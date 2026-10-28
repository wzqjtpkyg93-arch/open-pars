import asyncio
import hashlib
import json
import logging
import math
import os
import re
import secrets
import shlex
import sqlite3
import string
import threading
import time
import unicodedata
from collections import Counter
from contextlib import suppress
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
from email.utils import parsedate_to_datetime
from html import escape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qsl, unquote, urlencode, urljoin, urlsplit, urlunsplit
from zoneinfo import ZoneInfo

import httpx
from bs4 import BeautifulSoup
from dotenv import load_dotenv
from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.error import BadRequest, Forbidden, RetryAfter, TelegramError
from telegram.ext import Application, MessageHandler, CallbackQueryHandler, filters, ContextTypes

load_dotenv()
ADMIN_ID = int(os.getenv("ADMIN_ID", "1110325917"))
DATABASE = Path(os.getenv("DATABASE_PATH", "bot.sqlite3"))
DATA_DIR = Path(os.getenv("DATA_DIR", str(DATABASE.parent)))
PASSWORD_FILE = DATA_DIR / "passwords.txt"
BLOCKED_FILE = DATA_DIR / "blocked.txt"
DISPLAY_TZ = ZoneInfo(os.getenv("APP_TIMEZONE", "Europe/Moscow"))
USE_BROWSER = os.getenv("PROFILE_BROWSER", "1") == "1"
SUBSCRIPTIONS_ENABLED = os.getenv("SUBSCRIPTIONS_ENABLED", "0") == "1"
XROCKET_TESTNET = os.getenv("XROCKET_TESTNET", "0") == "1"
PLANS = {"d1": (24, "0.90", "1 день"), "d3": (72, "2.40", "3 дня"),
         "d7": (168, "4.90", "7 дней"), "d30": (720, "16.90", "30 дней")}
# Можно вернуть прежний темп, установив REQUEST_INTERVAL=2 в Environment.
REQUEST_INTERVAL = float(os.getenv("REQUEST_INTERVAL", "1.2"))
if not math.isfinite(REQUEST_INTERVAL) or not 1 <= REQUEST_INTERVAL <= 30:
    raise ValueError("REQUEST_INTERVAL: число от 1 до 30 секунд.")
COUNTRIES = "kw ae bh sa".split()
HOSTS = {"opensooq.com", "www.opensooq.com"} | {c + ".opensooq.com" for c in COUNTRIES}
METRICS = {"price", "views", "seller_views", "rating", "ratings", "reviews", "sold", "photos", "listings_count"}
MAX_PAGES, MAX_ADS, MAX_SEND = 20, 1000, 200
CDN = "https://opensooq-imagesv2.os-cdn.com/previews/700x0/"
log = logging.getLogger("opensooq")
EXCLUDED_WORDS = ["car", "cars", "auto", "autos", "kia", "gmc", "toyota", "nissan", "chevrolet", "ford", "bmw", "mercedes", "audi", "hyundai", "apartment", "flat", "real estate", "rent", "rental", "delivery", "service", "job", "vacancy", "سيارة", "سيارات", "شقة", "شقق", "عقار", "ايجار", "تأجير", "خدمة", "وظيفة"]
EXCLUDED_RE = re.compile(r"(?<!\w)(?:" + "|".join(re.escape(w) for w in EXCLUDED_WORDS) + r")(?!\w)", re.I)
# Коды приходят от OpenSooq для каждой карточки, независимо от языка заголовка.
EXCLUDED_CATEGORY_PREFIXES = (
    "autos", "vehicles", "cars", "realestate", "propertyfor", "propertiesfor",
    "services", "jobs", "jobopenings", "jobseekers", "employment",
)
TOPIC_FALLBACK_RE = re.compile(
    r"(?<!\w)(?:cars?\s+for\s+(?:sale|rent)|(?:apartment|flat|villa|room|warehouse)s?\s+for\s+(?:rent|sale)"
    r"|لل(?:ايجار|تاجير)|سيارات?|شقق?|عقارات?|فلل|فيلا|جيب|مستودعات?|وظائف|وظيفة|خدمات)(?!\w)", re.I)


def category_codes(value):
    if not isinstance(value, dict):
        return "", ""
    def first(keys):
        return next((value[k].strip() for k in keys if isinstance(value.get(k), str) and value[k].strip()), "")
    return (
        first(("cat1_code", "categoryReportingName", "category_reporting_name", "category_code", "cat_code")),
        first(("cat2_code", "subCategoryReportingName", "subcategory_reporting_name", "subcategory_code")),
    )


def excluded_topic(ad):
    """Классифицируем именно объявление, а не тип аккаунта продавца."""
    codes = [re.sub(r"[^a-z0-9]", "", str(ad.get(k) or "").lower())
             for k in ("category_code", "subcategory_code")]
    if codes[0]:
        return "category:" + codes[0] if codes[0].startswith(EXCLUDED_CATEGORY_PREFIXES) else ""
    # При известной разрешённой категории слова car/rent/service сами по себе
    # не должны скрывать игрушку, запчасть для электроники или мебель.
    if codes[1] and codes[1].startswith(EXCLUDED_CATEGORY_PREFIXES):
        return "category:" + codes[1]
    title = unicodedata.normalize("NFKC", str(ad.get("title") or ""))
    title = re.sub(r"[\u064b-\u065f\u0670ـ]", "", title)
    title = title.translate(str.maketrans({"أ": "ا", "إ": "ا", "آ": "ا"}))
    if EXCLUDED_RE.search(title) or TOPIC_FALLBACK_RE.search(title):
        return "title"
    return ""

class SourceError(Exception):
    pass

class RateLimit(SourceError):
    pass

def proxy_settings(value):
    value = value.strip()
    if not value:
        return None, None
    try:
        parsed = urlsplit(value)
        if (parsed.scheme not in {"http", "https"} or not parsed.hostname
                or not parsed.port or parsed.query or parsed.fragment
                or parsed.path not in {"", "/"}
                or any(char.isspace() for char in value)):
            raise ValueError()
        hostname = parsed.hostname
        if ":" in hostname:
            hostname = "[" + hostname + "]"
        browser = {"server": f"{parsed.scheme}://{hostname}:{parsed.port}"}
        if parsed.username is not None:
            browser["username"] = unquote(parsed.username)
        if parsed.password is not None:
            browser["password"] = unquote(parsed.password)
        return value, browser
    except ValueError:
        raise ValueError("OPENSOOQ_PROXY_URL: нужен HTTP URI вида http://USER:PASS@HOST:PORT.") from None

def error_text(error):
    text = str(error)
    value = os.getenv("OPENSOOQ_PROXY_URL", "").strip()
    if value:
        text = text.replace(value, "[proxy]")
        with suppress(ValueError):
            parsed = urlsplit(value)
            for secret in (parsed.password, parsed.username):
                if secret:
                    text = text.replace(secret, "[hidden]")
                    text = text.replace(unquote(secret), "[hidden]")
    return text

def safe_url(value, base=""):
    value = urljoin(base, str(value).strip())
    try:
        u = urlsplit(value)
        if (len(value) > 8192 or "\\" in value or any(ord(c) < 32 for c in value) or u.scheme not in {"http", "https"} or u.hostname not in HOSTS or u.username or u.password or u.port not in {None, 80, 443}):
            raise ValueError()
    except ValueError:
        raise ValueError("Нужна веб-ссылка на категорию OpenSooq.") from None
    return urlunsplit(("https", u.hostname, u.path or "/", u.query, ""))

def photo_url(value, base=CDN):
    if not isinstance(value, str) or not value: return ""
    if value.startswith("//"):
        value = "https:" + value
    if not value.startswith(("https://", "http://", "//")):
        value = urljoin(base.replace("{size}", "700x0"), value)
        if value.lower().endswith((".jpg", ".jpeg", ".png")): value += ".webp"
    u = urlsplit(value)
    if (u.scheme not in {"http", "https"} or not u.hostname or not (u.hostname.endswith(".os-cdn.com") or u.hostname in HOSTS) or u.username or u.password or u.port not in {None, 80, 443}): return ""
    return urlunsplit(("https", u.hostname, u.path, u.query, ""))

def number(value):
    if value is None or isinstance(value, bool): return None
    if isinstance(value, (int, float)):
        if value >= 0 and math.isfinite(value): return float(value)
        return None
    text = "".join(str(unicodedata.digit(c)) if c.isdecimal() else c for c in str(value))
    text = text.replace("٬", "").replace("٫", ".").replace(",", "").replace("\u200f", "").replace("\u200e", "")
    text = re.sub(r"(?<=\d)\s+(?=\d)", "", text)
    match = re.search(r"(\d+(?:\.\d+)?)(?:\s*(k|m|b|ألف|الف|مليون)(?!\w))?", text, re.I)
    if not match or text.lstrip().startswith("-"): return None
    scales = {"k": 1000, "m": 1000000, "b": 1000000000, "ألف": 1000, "الف": 1000, "مليون": 1000000}
    result = float(match[1]) * scales.get((match[2] or "").lower(), 1)
    return result if math.isfinite(result) else None

def count(value):
    result = number(value)
    return round(result) if result is not None else None

def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values(): yield from walk(child)
    elif isinstance(value, list):
        for child in value: yield from walk(child)

def props(soup):
    tag = soup.find("script", id="__NEXT_DATA__")
    if not tag: return {}
    try: return json.loads(tag.string or tag.get_text())["props"]["pageProps"]
    except (ValueError, KeyError, TypeError): raise SourceError("Изменились данные страницы OpenSooq.") from None

def flight(soup):
    chunks, result = [], []
    for tag in soup.find_all("script", src=False):
        text = tag.string or tag.get_text()
        for match in re.finditer(r"(?:self\.)?__next_f\.push\(", text):
            try:
                data, _ = json.JSONDecoder().raw_decode(text[match.end():])
                if (isinstance(data, list) and len(data) > 1 and data[0] == 1 and isinstance(data[1], str)): chunks.append(data[1])
            except ValueError: pass
    for line in "".join(chunks).splitlines():
        key, separator, value = line.partition(":")
        if (separator and re.fullmatch(r"[0-9a-fA-F]+", key) and value[:1] in {"{", "["}):
            with suppress(ValueError): result.append(json.loads(value))
    return result

def parse_profile(raw, expected_id):
    """Счётчики профиля; listings_count — общее число Live Listings."""
    soup = BeautifulSoup(raw, "html.parser")
    result = {key: None for key in (
        "rating", "ratings", "reviews", "seller_views", "sold", "listings_count"
    )}

    def put(key, value, convert=count):
        # 0 — известное значение, а не отсутствие данных.
        if result[key] is None and value is not None:
            result[key] = convert(value)

    documents = []
    with suppress(SourceError):
        documents.append(props(soup))
    documents.extend(flight(soup))

    # В текущем HTML профиль находится в userInfo.member / data.info.member.
    # Поиск member также поддерживает эти блоки внутри Next.js Flight.
    members = []
    for obj in walk(documents):
        member = obj.get("member")
        if isinstance(member, dict) and any(key in member for key in (
            "views_count", "views", "posts_count", "member_info", "rating"
        )):
            members.append(member)

    expected_id = str(expected_id).strip() if expected_id is not None else ""
    if expected_id:
        matching = [m for m in members if str(m.get("id")) == expected_id]
        without_id = [m for m in members if m.get("id") is None]
        if matching:
            members = matching
        elif without_id:
            members = without_id
        elif members:
            # Не подставляем статистику другого продавца после редиректа.
            raise SourceError("Открыт профиль другого продавца.")

    for member in members:
        put("seller_views", member.get("views_count"))
        put("seller_views", member.get("views"))
        # posts_count не считаем подтверждённым числом активных объявлений.
        # Для listings_count ниже читается видимая вкладка Live Listings.
        rating = member.get("rating")
        if isinstance(rating, dict):
            put("rating", rating.get("average_rating"), number)
            put("ratings", rating.get("number_of_rating"))
            put("reviews", rating.get("number_of_reviews"))
        info = member.get("member_info")
        if isinstance(info, dict):
            put("sold", info.get("sold_listings_count"))

    # Резервный разбор видимого HTML: английский и арабский интерфейсы.
    for tag in soup(["script", "style", "template", "noscript"]):
        tag.decompose()

    def clean_text(value):
        value = unicodedata.normalize("NFKC", value)
        value = re.sub(r"[\u064b-\u065f\u0670\u200e\u200f\u061c]", "", value)
        return re.sub(r"\s+", " ", value).strip()

    numeric = r"\d[\d.,٬٫]*(?: \d{3})*(?:\s*(?:[kmb]|ألف|الف|مليون))?"
    view_label = r"(?:Views?|مشاهدة|مشاهدات|المشاهدات)"
    follower_label = r"(?:Followers?|المتابعون|المتابعين|متابعون|متابعين|متابع)"

    if result["seller_views"] is None:
        # Views и Followers должны находиться в одном небольшом блоке.
        # Так просмотры отдельного объявления не попадут в seller_views.
        for node in soup.find_all(string=re.compile(view_label, re.I)):
            parent = node.parent
            for _ in range(3):
                if parent is None:
                    break
                text = clean_text(parent.get_text(" ", strip=True))
                if len(text) > 350:
                    break
                match = re.search(rf"({numeric})\s*{view_label}\b", text, re.I)
                if match and re.search(follower_label, text, re.I):
                    put("seller_views", match.group(1))
                    if result["seller_views"] is not None:
                        break
                parent = parent.parent
            if result["seller_views"] is not None:
                break

    tab_labels = {
        "listings_count": r"(?:Live\s+Listings?|(?:الإعلانات|الاعلانات)\s+(?:الفعاله|الفعالة|النشطة))",
        "sold": r"(?:Sold\s+Listings?|(?:الإعلانات|الاعلانات)\s+المباعة)",
    }
    for tab in soup.select("li, a, button, [role='tab']"):
        text = clean_text(tab.get_text(" ", strip=True))
        if len(text) > 150:
            continue
        for key, label in tab_labels.items():
            if result[key] is None:
                match = re.fullmatch(rf"{label}\s*[（(]\s*({numeric})\s*[)）]", text, re.I)
                if match:
                    put(key, match.group(1))

    page_text = clean_text(soup.get_text(" ", strip=True))
    if result["reviews"] is None:
        match = re.search(r"(?:\(|^|\s)(\d+)\s*(?:reviews?|تقييمات|مراجعات)", page_text, re.I)
        if match:
            put("reviews", match.group(1))
    if result["rating"] is None:
        match = re.search(r"(\d[.٫]\d+)\s*(?:★|stars?|نجوم)", page_text, re.I)
        if match:
            put("rating", match.group(1), number)

    # Не считаем len(listings.items): это только одна страница объявлений.
    # Если счётчик недоступен, оставляем None, чтобы карточка показала «нет данных».
    return result

def update_filters(current, text):
    result = dict(current)
    for pair in shlex.split(text):
        key, separator, value = pair.partition("=")
        metric, _, bound = key.rpartition("_")
        if not separator or (key not in {"keywords", "exclude", "currency", "unknown"} and not (metric in METRICS and bound in {"min", "max"})):
            raise ValueError(f"Неизвестный фильтр: {pair[:60]}")
        if value.lower() in {"off", "none"}: result.pop(key, None)
        elif key in {"keywords", "exclude"}:
            if (len(value) > 500 or not any(x.strip() for x in value.split(","))): raise ValueError("Укажите слова через запятую.")
            result[key] = value
        elif key == "currency":
            if not re.fullmatch("[A-Za-z]{3}", value): raise ValueError("Валюта: код из 3 букв.")
            result[key] = value.upper()
        elif key == "unknown":
            if value not in {"include", "exclude"}: raise ValueError("unknown: только include или exclude.")
            result[key] = value
        else:
            number_value = float(value.replace(",", "."))
            if (not math.isfinite(number_value) or number_value < 0 or (metric == "rating" and number_value > 5)): raise ValueError("Числа должны быть неотрицательными.")
            if (metric not in {"price", "rating"} and not number_value.is_integer()): raise ValueError("Счётчики должны быть целыми.")
            result[key] = number_value
    for metric in METRICS:
        if result.get(metric + "_min", 0) > result.get(metric + "_max", math.inf): raise ValueError(f"{metric}_min больше {metric}_max.")
    return result

def matches(ad, rules):
    text = (ad["title"] + "\n" + ad.get("description", "")).casefold()
    def terms(name): return [value.strip().casefold() for value in rules.get(name, "").split(",") if value.strip()]
    if terms("keywords") and not any(value in text for value in terms("keywords")): return False, set()
    if any(value in text for value in terms("exclude")): return False, set()
    missing = set()
    accepted = True
    if rules.get("currency"):
        if not ad.get("currency"): missing.add("currency")
        elif ad["currency"] != rules["currency"]: accepted = False
    for metric in METRICS:
        low, high = rules.get(metric + "_min"), rules.get(metric + "_max")
        if low is None and high is None: continue
        value = ad.get(metric)
        if value is None: missing.add(metric)
        elif ((low is not None and value < low) or (high is not None and value > high)): accepted = False
    allow_missing = not missing or rules.get("unknown") == "include"
    return accepted and allow_missing, missing

def save_user_password(user_id, password):
    data = {}
    if os.path.exists(PASSWORD_FILE):
        with open(PASSWORD_FILE, "r") as f:
            for line in f:
                if ":" in line:
                    uid, pwd = line.strip().split(":", 1)
                    data[uid] = pwd
    data[str(user_id)] = password
    with open(PASSWORD_FILE, "w") as f:
        for uid, pwd in data.items():
            f.write(f"{uid}:{pwd}\n")

def remove_user_password(user_id):
    if not PASSWORD_FILE.exists():
        return
    lines = PASSWORD_FILE.read_text(encoding="utf-8").splitlines()
    remaining = [line for line in lines if line.split(":", 1)[0] != str(user_id)]
    PASSWORD_FILE.write_text("".join(line + "\n" for line in remaining), encoding="utf-8")


def check_user_password(user_id, password):
    if not os.path.exists(PASSWORD_FILE): return False
    with open(PASSWORD_FILE, "r") as f:
        for line in f:
            if ":" in line:
                uid, pwd = line.strip().split(":", 1)
                if uid == str(user_id) and pwd == password: return True
    return False

def is_blocked(user_id):
    if not os.path.exists(BLOCKED_FILE): return False
    with open(BLOCKED_FILE, "r") as f: return str(user_id) in [line.strip() for line in f]

def block_user(user_id):
    if not is_blocked(user_id):
        with open(BLOCKED_FILE, "a") as f: f.write(f"{user_id}\n")

def unblock_user(user_id):
    if os.path.exists(BLOCKED_FILE):
        with open(BLOCKED_FILE, "r") as f: lines = f.readlines()
        with open(BLOCKED_FILE, "w") as f:
            for line in lines:
                if line.strip() != str(user_id): f.write(line)


def plain(value):
    if isinstance(value, dict):
        for key in ("content", "text", "value"):
            if key in value:
                return plain(value[key])
        return ""
    if isinstance(value, list):
        return "\n".join(filter(None, (plain(v) for v in value)))
    return "" if value is None else str(value).strip()


def publication(value):
    """Дата без времени остаётся датой: время публикации не выдумываем."""
    text = plain(value)
    if not text:
        return ""
    for fmt in ("%d-%m-%Y", "%d/%m/%Y", "%Y-%m-%d"):
        try:
            return datetime.strptime(text, fmt).strftime("%d.%m.%Y")
        except ValueError:
            pass
    try:
        dt = datetime.fromisoformat(text.replace("Z", "+00:00"))
        if dt.tzinfo is not None:
            dt = dt.astimezone(DISPLAY_TZ)
            return dt.strftime("%d.%m.%Y %H:%M %Z")
        return dt.strftime("%d.%m.%Y %H:%M") + " (часовой пояс не указан)"
    except ValueError:
        return text[:100]


def relative_label(value):
    text = plain(value).split("•", 1)[0].strip()
    if text.lower() in {"today", "yesterday", "just now"}:
        return {"today": "Сегодня", "yesterday": "Вчера", "just now": "Только что"}[text.lower()]
    match = re.fullmatch(r"(\d+)\s*(minutes?|mins?|hours?|hrs?|days?)\s+ago", text, re.I)
    if match:
        unit = match[2].lower()
        label = "мин." if unit.startswith("m") else "ч." if unit.startswith("h") else "дн."
        return f"{match[1]} {label} назад"
    return text[:100]


def next_category_url(data, block, url):
    next_path = (data.get("seoPage") or {}).get("nextPageUrl")
    if next_path:
        return safe_url(next_path, url)
    # /en/find отдаёт meta.pages/current_page, но может не иметь SEO-ссылки.
    meta = block.get("meta") or {}
    if not isinstance(meta, dict) or not block.get("items"):
        return None
    current = count(meta.get("current_page"))
    pages = count(meta.get("pages"))
    if current is None or pages is None or not 1 <= current < pages:
        return None
    parsed = urlsplit(safe_url(url))
    query = [(key, value) for key, value in parse_qsl(parsed.query, keep_blank_values=True) if key != "page"]
    query.append(("page", str(current + 1)))
    return safe_url(urlunsplit((parsed.scheme, parsed.netloc, parsed.path, urlencode(query), "")))


def parse_category_dom(soup, url, documents):
    section = soup.select_one("section[data-testid='serp-results']")
    if section is None:
        raise SourceError("Не найдены данные категории OpenSooq.")
    metadata = {}
    for obj in walk(documents):
        listing = obj.get("listings")
        if isinstance(listing, dict) and isinstance(listing.get("items"), list):
            for item in listing["items"]:
                post = item.get("post") if isinstance(item, dict) else None
                if isinstance(post, dict) and post.get("id"):
                    metadata[str(post["id"])] = post
    ads, seen = [], set()
    cards = section.select("a.postListItemData[data-id1][href]")
    for node in cards:
        ad_id = str(node.get("data-id1", ""))
        heading = node.find(["h2", "h3"])
        if not ad_id.isdecimal() or heading is None or ad_id in seen:
            continue
        ad_url = safe_url(node["href"], url)
        if not re.search(r"/(?:search|lists)/" + re.escape(ad_id) + r"(?:/|$)", urlsplit(ad_url).path):
            continue
        seen.add(ad_id)
        post = metadata.get(ad_id, {})
        main_category, subcategory = category_codes(post)
        price_node = heading.find_previous_sibling("span")
        price_text = price_node.get_text(" ", strip=True) if price_node else ""
        currency_match = re.search(r"\b([A-Z]{3})\b", price_text)
        media = node.select_one("[data-testid='serp-listing-carousel'] img")
        image = photo_url(media.get("src", "")) if media else ""
        status = node.find("span", recursive=False)
        camera = node.select_one("svg[data-name='iconCamera2']")
        ad = dict.fromkeys(METRICS)
        ad.update(id=ad_id, url=ad_url, title=heading.get_text(" ", strip=True), description="",
            price=number(price_text) if currency_match else None,
            currency=currency_match[1] if currency_match else "",
            images=[image] if image else [],
            photos=count(camera.parent.get_text(" ", strip=True)) if camera else None,
            seller_id=str(post.get("member_id") or ""), seller_name="", seller_url="",
            category_code=main_category, subcategory_code=subcategory,
            location=", ".join(filter(None, [plain(post.get("neighborhoodName") or node.get("data-nhood")),
                                            plain(post.get("city_reporting") or node.get("data-city"))])),
            published="", posted_label=relative_label(status.get_text(" ", strip=True)) if status else "")
        ads.append(ad)
    if cards and not ads:
        raise SourceError("Новый формат карточек категории не удалось прочитать.")
    next_link = soup.select_one("a[aria-label='Go to next page'][href], a[rel~='next'][href], link[rel~='next'][href]")
    next_url = safe_url(next_link["href"], url) if next_link and ads else None
    if ads and not next_url:
        parsed = urlsplit(url)
        params = parse_qsl(parsed.query, keep_blank_values=True)
        current = int(dict(params).get("page", "1"))
        expected = sorted((key, value) for key, value in params if key != "page")
        for link in soup.find_all("a", href=True):
            candidate = urlsplit(urljoin(url, link["href"]))
            query = parse_qsl(candidate.query, keep_blank_values=True)
            if (candidate.hostname == parsed.hostname and candidate.path == parsed.path
                    and dict(query).get("page") == str(current + 1)
                    and sorted((key, value) for key, value in query if key != "page") == expected):
                next_url = safe_url(link["href"], url)
                break
    return ads, next_url


def parse_category(raw, url):
    soup = BeautifulSoup(raw, "html.parser")
    documents = []
    with suppress(SourceError):
        documents.append(props(soup))
    documents.extend(flight(soup))
    data = next((o for o in walk(documents) if isinstance(o.get("serpApiResponse"), dict)), None)
    block = data.get("serpApiResponse", {}).get("listings") if data else None
    if not isinstance(block, dict) or not isinstance(block.get("items"), list):
        return parse_category_dom(soup, url, documents)
    ads = []
    for row in block["items"]:
        if not isinstance(row, dict) or not row.get("id") or not row.get("title"):
            continue
        path = row.get("post_url") or f"/search/{row['id']}"
        if path.startswith("/search/"):
            locale = urlsplit(url).path.split("/")[1]
            path = "/" + (locale if locale in {"ar", "en"} else "en") + path
        image = photo_url(row.get("image_uri"))
        ad = dict.fromkeys(METRICS)
        main_category, subcategory = category_codes(row)
        ad.update(
            id=str(row["id"]), url=safe_url(path, url), title=plain(row["title"]),
            description=plain(row.get("masked_description")),
            price=number(row.get("price_amount")), currency=plain(row.get("price_currency_iso")),
            photos=count(row.get("image_count")), images=[image] if image else [],
            views=count(row.get("views_count")), seller_id=str(row.get("member_id") or ""),
            seller_name=plain(row.get("member_display_name")), seller_url="",
            rating=number(row.get("member_rating_avg")), ratings=count(row.get("member_rating_count")),
            category_code=main_category, subcategory_code=subcategory,
            location=", ".join(filter(None, [plain(row.get("nhood_label")), plain(row.get("city_label"))])),
            published=publication(row.get("inserted_date")), posted_label=relative_label(row.get("posted_at")),
        )
        username = plain(row.get("member_user_name"))
        if username:
            locale = "ar" if urlsplit(url).path.startswith("/ar/") else "en"
            ad["seller_url"] = safe_url(f"/{locale}/mid/{username}", url)
        ads.append(ad)
    if block["items"] and not ads:
        raise SourceError("Карточки категории имеют неизвестную структуру.")
    return ads, next_category_url(data, block, url)


def parse_listing(raw, ad):
    soup = BeautifulSoup(raw, "html.parser")
    documents = []
    with suppress(SourceError):
        documents.append(props(soup))
    documents.extend(flight(soup))
    data = None
    for obj in walk(documents):
        candidate = obj.get("listingData")
        if isinstance(candidate, dict) and str(candidate.get("commonInfo", {}).get("postId")) == ad["id"]:
            data = candidate
            break
    if data is None:
        raise SourceError("Не удалось прочитать данные объявления.")
    info = data["commonInfo"]
    # Только метаданные выбранного объявления: рекомендации других категорий
    # на этой же странице не участвуют в классификации.
    for metadata in walk(data.get("loggingData") or {}):
        main_category, subcategory = category_codes(metadata)
        if main_category:
            ad["category_code"] = main_category
            ad["subcategory_code"] = subcategory
            break
    owner = info.get("ownerData") or {}
    ad["title"] = plain(info.get("topTitle")) or ad["title"]
    ad["description"] = plain(info.get("description")) or ad.get("description", "")
    for target, key, convert in (
        ("seller_id", "id", str), ("seller_name", "fullName", plain),
        ("rating", "ratingAvg", number), ("ratings", "numberOfRatings", count),
    ):
        if owner.get(key) is not None:
            ad[target] = convert(owner[key])
    # Это неподтверждённый общий счётчик карточки. Не выдаём его за Live Listings.
    ad["seller_listings_hint"] = count(owner.get("numberOfListings"))
    if owner.get("memberLink"):
        ad["seller_url"] = safe_url(owner["memberLink"], ad["url"])
    locations = {}
    for section in (info.get("basicInfo") or {}).get("sections", []):
        for item in section.get("items", []):
            kind, value = item.get("key_type"), plain(item.get("value"))
            if kind == "ListingPostDate" and value:
                ad["published"] = publication(value)
            if kind in {"Neighborhood", "City"} and value:
                locations[kind] = value
    if locations:
        ad["location"] = ", ".join(dict.fromkeys(locations[k] for k in ("Neighborhood", "City") if k in locations))
    if not ad.get("published"):
        for key in ("datePublished", "publishedAt", "createdAt"):
            if info.get(key):
                ad["published"] = publication(info[key])
                break
    gallery = info.get("gallery") or {}
    base = (data.get("config") or {}).get("imagesBaseUrl") or CDN
    images = [photo_url(m.get("uri"), base) for m in gallery.get("media", [])
              if isinstance(m, dict) and str(m.get("mimeType", "")).startswith("image/")]
    ad["images"] = list(dict.fromkeys(filter(None, images))) or ad.get("images", [])
    if (gallery.get("chips") or {}).get("imagesCount") is not None:
        ad["photos"] = count(gallery["chips"]["imagesCount"])
    for key in ("viewsCount", "views_count", "postViewsCount"):
        if info.get(key) is not None:
            ad["views"] = count(info[key])
            break
    prices = ((data.get("listing") or {}).get("price") or {}).get("prices", [])
    if prices:
        ad["price"] = number(prices[0].get("price"))
        ad["currency"] = plain(prices[0].get("key") or prices[0].get("currencyLabel")) or ad.get("currency", "")
    return ad


class Reader:
    def __init__(self):
        self.proxy_url, self.browser_proxy = proxy_settings(os.getenv("OPENSOOQ_PROXY_URL", ""))
        self.http = httpx.AsyncClient(timeout=30, follow_redirects=False,
            proxy=self.proxy_url, trust_env=False,
            headers={"User-Agent": "OpenSooqTelegramBot/2.0", "Accept-Language": "en"})
        self.lock = asyncio.Lock()
        self.browser_lock = asyncio.Lock()
        self.last, self.pauses, self.cache = 0.0, {}, {}
        self.pw = self.browser = self.browser_context = None
        self.browser_failures = 0

    async def throttle(self):
        async with self.lock:
            await asyncio.sleep(max(0, self.last + REQUEST_INTERVAL - time.monotonic()))
            self.last = time.monotonic()

    def status_error(self, status, headers, host):
        if status == 429:
            retry = headers.get("retry-after", "300")
            try:
                delay = float(retry)
            except ValueError:
                try:
                    delay = parsedate_to_datetime(retry).timestamp() - time.time()
                except (ValueError, TypeError, OverflowError):
                    delay = 300
            self.pauses[host] = time.monotonic() + max(60, min(3600, delay))
            raise RateLimit("OpenSooq ограничил запросы: HTTP 429.")
        if status != 200:
            raise SourceError(f"OpenSooq вернул HTTP {status}.")

    @staticmethod
    def check_html(raw):
        if re.search(r"<title>\s*(?:Just a moment|Access Denied|Access Restricted|Attention Required)", raw[:20000], re.I):
            raise SourceError("OpenSooq показал проверку доступа.")

    async def get(self, url):
        url = safe_url(url)
        for _ in range(6):
            host = urlsplit(url).hostname
            if self.pauses.get(host, 0) > time.monotonic():
                raise RateLimit("Пауза после ограничения OpenSooq ещё не закончилась.")
            for attempt in range(3):
                await self.throttle()
                try:
                    async with self.http.stream("GET", url) as response:
                        body = bytearray()
                        async for chunk in response.aiter_bytes():
                            body.extend(chunk)
                            if len(body) > 8 * 1024 * 1024:
                                raise SourceError("Слишком большой ответ OpenSooq.")
                        raw = body.decode(response.encoding or "utf-8", errors="replace")
                    if response.status_code >= 500 and attempt < 2:
                        await asyncio.sleep(2 ** (attempt + 1))
                        continue
                    break
                except httpx.RequestError:
                    if attempt == 2:
                        raise SourceError("OpenSooq не ответил вовремя.") from None
                    await asyncio.sleep(2 ** (attempt + 1))
            if response.status_code in {301, 302, 303, 307, 308}:
                location = response.headers.get("location")
                if not location:
                    raise SourceError("Перенаправление без адреса.")
                url = safe_url(location, url)
                continue
            self.status_error(response.status_code, response.headers, host)
            self.check_html(raw)
            return raw, url
        raise SourceError("Слишком много перенаправлений.")

    async def browser_profile(self, url, seller_id):
        # Один браузер на процесс; страницы профилей обрабатываются по очереди.
        if not USE_BROWSER or self.browser_failures >= 3:
            raise SourceError("Браузерная загрузка профилей недоступна в этой проверке.")
        from playwright.async_api import async_playwright, TimeoutError as PlaywrightTimeout
        async with self.browser_lock:
            page = None
            try:
                if self.browser is None or not self.browser.is_connected():
                    if self.pw is None:
                        self.pw = await async_playwright().start()
                    launch_options = {"headless": True, "args": ["--disable-dev-shm-usage"]}
                    if self.browser_proxy is not None:
                        launch_options["proxy"] = self.browser_proxy
                    self.browser = await self.pw.chromium.launch(**launch_options)
                    self.browser_context = await self.browser.new_context(locale="en-US")
                    async def lightweight(route):
                        if route.request.resource_type in {"image", "media", "font"}:
                            await route.abort()
                        else:
                            await route.continue_()
                    await self.browser_context.route("**/*", lightweight)
                await self.throttle()
                page = await self.browser_context.new_page()
                try:
                    response = await page.goto(safe_url(url), timeout=25000, wait_until="domcontentloaded")
                except PlaywrightTimeout:
                    # При тайм-ауте DOM уже может содержать нужные данные.
                    response = None
                safe_url(page.url)
                if urlsplit(page.url).hostname != urlsplit(url).hostname:
                    raise SourceError("Профиль перенаправил на другую страну.")
                if response is not None:
                    self.status_error(response.status, response.headers, urlsplit(url).hostname)
                profile = None
                for attempt in range(4):
                    raw = await page.content()
                    self.check_html(raw)
                    profile = await asyncio.to_thread(parse_profile, raw, seller_id)
                    if all(profile.get(key) is not None for key in ("seller_views", "listings_count")):
                        log.info("[profile_browser] seller=%s views=%s live=%s", seller_id, profile["seller_views"], profile["listings_count"])
                        return profile
                    if attempt < 3:
                        await asyncio.sleep(1.5)
                if profile and any(v is not None for v in profile.values()):
                    self.browser_failures += 1
                    return profile
                raise SourceError("Статистика отсутствует в загруженном профиле.")
            except RateLimit:
                raise
            except Exception as exc:
                self.browser_failures += 1
                log.warning("[profile_browser] seller=%s error=%s", seller_id, error_text(exc)[:1200])
                if isinstance(exc, SourceError):
                    raise
                raise SourceError("Не удалось загрузить профиль браузером; подробности в логах.") from None
            finally:
                if page is not None:
                    with suppress(Exception):
                        await page.close()

    async def profile(self, url, seller_id):
        key = (url, seller_id)
        cached = self.cache.get(key)
        if cached and cached[0] > time.monotonic():
            return cached[1], cached[2]
        profile, problems = None, []
        try:
            raw, _ = await self.get(url)
            profile = await asyncio.to_thread(parse_profile, raw, seller_id)
            log.info("[profile_http] seller=%s views=%s live=%s", seller_id, profile.get("seller_views"), profile.get("listings_count"))
        except RateLimit:
            raise
        except (SourceError, ValueError) as exc:
            problems.append("HTTP: " + error_text(exc))
            log.warning("[profile_http] seller=%s error=%s", seller_id, error_text(exc)[:500])
        if profile is None or any(profile.get(key) is None for key in ("seller_views", "listings_count")):
            try:
                rendered = await self.browser_profile(url, seller_id)
                profile = profile or {}
                profile.update({k: v for k, v in rendered.items() if v is not None})
            except RateLimit:
                raise
            except (SourceError, ValueError, ImportError) as exc:
                problems.append("Браузер: " + error_text(exc))
        absent = [key for key in ("seller_views", "listings_count") if not profile or profile.get(key) is None]
        if absent:
            labels = {"seller_views": "просмотры", "listings_count": "активные объявления"}
            issue = "Недоступны " + ", ".join(labels[key] for key in absent) + ". " + ("; ".join(problems) or "Счётчики не найдены в профиле.")
        else:
            issue = ""
        ttl = 300 if not issue else 60
        self.cache[key] = (time.monotonic() + ttl, profile, issue)
        if len(self.cache) > 2000:
            self.cache = {k: v for k, v in self.cache.items() if v[0] > time.monotonic()}
            self.cache = dict(list(self.cache.items())[-1000:])
        return profile, issue

    async def enrich(self, ad, rules=None):
        if excluded_topic(ad):
            ad["_filtered_before_profile"] = True
            return ad, ""
        raw, final = await self.get(ad["url"])
        if urlsplit(final).hostname != urlsplit(ad["url"]).hostname:
            raise SourceError("Объявление перенаправило на другую страну.")
        ad["url"] = final
        ad = await asyncio.to_thread(parse_listing, raw, ad)
        if excluded_topic(ad):
            ad["_filtered_before_profile"] = True
            return ad, ""
        if rules:
            # Эти поля уже окончательны после загрузки объявления и не меняются
            # профилем. Неизвестное поле здесь не является причиной отказа.
            early_keys = {"keywords", "exclude", "currency"} | {
                metric + "_" + bound
                for metric in ("price", "photos", "views")
                for bound in ("min", "max")
            }
            early_rules = {k: v for k, v in rules.items() if k in early_keys}
            early_rules["unknown"] = "include"
            if not matches(ad, early_rules)[0]:
                ad["_filtered_before_profile"] = True
                return ad, ""
        if not ad.get("seller_url"):
            return ad, "В объявлении отсутствует ссылка на профиль продавца."
        profile, warning = await self.profile(ad["seller_url"], ad["seller_id"])
        if profile:
            # Доступные данные карточки сохраняются, даже если профиль закрыт.
            ad.update({k: v for k, v in profile.items() if v is not None})
        return ad, warning

    async def close(self):
        if self.browser is not None:
            with suppress(Exception):
                await self.browser.close()
        if self.pw is not None:
            with suppress(Exception):
                await self.pw.stop()
        await self.http.aclose()


def card(ad):
    def show(key):
        value = ad.get(key)
        if value is None:
            return "нет данных"
        return escape(f"{value:g}" if isinstance(value, float) else str(value))

    lines = [f"📦 <b>{escape(ad['title'][:100])}</b>"]
    price = f"{show('price')} {escape(ad.get('currency', ''))}".strip() if ad.get("price") is not None else "Цена не указана"
    lines.append(f"<b>{price}</b>")
    if ad.get("location"):
        lines.append("📍 " + escape(ad["location"]))
    if ad.get("published"):
        lines.append("📅 Опубликовано: " + escape(ad["published"]))
    if ad.get("posted_label"):
        lines.append("🕓 В выдаче: " + escape(ad["posted_label"]))
    desc = plain(ad.get("description"))
    if desc:
        if len(desc) > 260:
            desc = desc[:257].rstrip() + "…"
        lines.extend(["", f"<blockquote>{escape(desc)}</blockquote>"])
    lines.extend(["", "👤 <b>" + escape((ad.get("seller_name") or "Продавец")[:60]) + "</b>",
        f"👁 Просмотры профиля: <b>{show('seller_views')}</b>",
        f"📦 Активных объявлений: <b>{show('listings_count')}</b>"])
    if ad.get("listings_count") is None and ad.get("seller_listings_hint") is not None:
        lines.append(f"По карточке продавца: {show('seller_listings_hint')} объявлений — активность не подтверждена")
    rating = []
    if ad.get("rating") is not None:
        rating.append(f"⭐ Рейтинг: <b>{show('rating')}</b>")
    if ad.get("ratings") is not None:
        rating.append(f"Оценок: {show('ratings')}")
    if rating:
        lines.append(" · ".join(rating))
    if ad.get("reviews") is not None:
        lines.append(f"💬 Отзывов: {show('reviews')}")
    if ad.get("sold") is not None:
        lines.append(f"✅ Продано: {show('sold')}")
    footer = [f"ID {show('id')}"]
    if ad.get("photos") is not None:
        footer.append(f"Фото: {show('photos')}")
    lines.extend(["", " · ".join(footer)])
    return "\n".join(lines)


async def telegram_call(method, **kwargs):
    try:
        return await method(**kwargs)
    except RetryAfter as exc:
        delay = exc.retry_after.total_seconds() if hasattr(exc.retry_after, "total_seconds") else float(exc.retry_after)
        if delay > 60:
            raise
        await asyncio.sleep(delay + 1)
        return await method(**kwargs)


HELP_TEXT = """ℹ️ Команды
/sources — категории
/remove 1 — удалить категорию
/filters — текущие фильтры
/filters price_max=500 currency=AED
/filters keywords="iphone,samsung" exclude="broken,parts"
/filters seller_views_min=100 listings_count_max=10
/filters unknown=include — пропускать объявления с неизвестными счётчиками
/filters unknown=exclude — исключать их при активных ограничениях
/reset — сбросить фильтры
/check — проверить объявления
/restart — перезапустить проверку
/watch — регулярная проверка
/interval 15 — интервал 5–1440 минут
/pause — остановить проверку и мониторинг
/status — статус и последний отчёт
/saved — сохранённые поиски
/cancel — отменить ввод
/admin — пользователи и пароли (для владельца)
/revokepass ID — отозвать пароль и доступ (для владельца)
/testproxy — проверить просмотры и активные объявления через прокси
/id — ваш Telegram ID

seller_views — просмотры профиля продавца
listings_count — активные объявления продавца

Для добавления категории отправьте её ссылку.
Повторная проверка сохраняет историю уже отправленных объявлений.
"""






def report_text(stats, elapsed, outcome, warnings, missing):
    titles = {"complete": "✅ Поиск завершён", "partial": "⏹ Поиск завершён",
              "error": "❌ Поиск прерван", "stopped": "⏸ Поиск остановлен", "limit": "📦 Достигнут лимит поиска"}
    seconds = max(0, round(elapsed))
    duration = f"{seconds // 60} мин. {seconds % 60} сек." if seconds >= 60 else f"{seconds} сек."
    text = (f"<b>{titles[outcome]}</b>\n\n"
        f"Отправлено объявлений: <b>{stats['sent']}</b>\n"
        f"Уже отправлялись: <b>{stats['duplicates']}</b>\n"
        f"Время: <b>{duration}</b>\n\n"
        f"Страниц: {stats['pages']} · Карточек: {stats['found']}\n"
        f"Обработано новых: {stats['checked']}\n"
        f"Отсеяно фильтрами: {stats['filtered']} · Ошибок: {stats['errors']}")
    return text


class Service:
    def __init__(self, bot, allowed, path):
        self.bot, self.allowed = bot, set(allowed)
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(path)
        self.db.row_factory = sqlite3.Row
        self.db.executescript("""
            PRAGMA journal_mode=WAL;
            CREATE TABLE IF NOT EXISTS users(chat INTEGER PRIMARY KEY, urls TEXT NOT NULL DEFAULT '[]', rules TEXT NOT NULL DEFAULT '{}', enabled INTEGER NOT NULL DEFAULT 0, minutes INTEGER NOT NULL DEFAULT 15, next_check REAL NOT NULL DEFAULT 0, last TEXT NOT NULL DEFAULT '');
            CREATE TABLE IF NOT EXISTS delivered(chat INTEGER NOT NULL, key TEXT NOT NULL, PRIMARY KEY(chat,key));
            CREATE TABLE IF NOT EXISTS authorized(chat INTEGER PRIMARY KEY);
            CREATE TABLE IF NOT EXISTS revoked(chat INTEGER PRIMARY KEY);
            CREATE TABLE IF NOT EXISTS subscriptions(chat INTEGER PRIMARY KEY, until REAL NOT NULL);
            CREATE TABLE IF NOT EXISTS subscriptions_test(chat INTEGER PRIMARY KEY, until REAL NOT NULL);
            CREATE TABLE IF NOT EXISTS subscription_events(id TEXT PRIMARY KEY, chat INTEGER NOT NULL, hours REAL NOT NULL, actor INTEGER NOT NULL, created REAL NOT NULL);
            CREATE TABLE IF NOT EXISTS payment_orders(
                id TEXT PRIMARY KEY, chat INTEGER NOT NULL, plan TEXT NOT NULL, hours INTEGER NOT NULL,
                amount TEXT NOT NULL, currency TEXT NOT NULL, invoice TEXT NOT NULL DEFAULT '',
                link TEXT NOT NULL DEFAULT '', status TEXT NOT NULL DEFAULT 'pending', applied INTEGER NOT NULL DEFAULT 0,
                created REAL NOT NULL, checked REAL NOT NULL DEFAULT 0, network TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS saved_searches(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                chat INTEGER NOT NULL,
                name TEXT NOT NULL,
                config TEXT NOT NULL,
                created REAL NOT NULL,
                UNIQUE(chat, name)
            );
        """)
        self.db.commit()
        self.allowed.update(r["chat"] for r in self.db.execute("SELECT chat FROM authorized"))
        self.revoked = {r["chat"] for r in self.db.execute("SELECT chat FROM revoked") if r["chat"] != ADMIN_ID}
        self.allowed.difference_update(self.revoked)
        self.reader, self.tasks, self.lock = Reader(), {}, asyncio.Lock()
        self.closing = False
        self.subscription_table = "subscriptions_test" if XROCKET_TESTNET else "subscriptions"
        self.billing = Billing(self)

    def permitted(self, chat):
        if chat == ADMIN_ID:
            return True
        if SUBSCRIPTIONS_ENABLED:
            return (chat not in self.revoked and not is_blocked(chat) and self.access_until(chat) > time.time())
        return chat in self.allowed and chat not in self.revoked and not is_blocked(chat)

    def access_until(self, chat):
        row = self.db.execute("SELECT until FROM " + self.subscription_table + " WHERE chat=?", (chat,)).fetchone()
        return row["until"] if row else 0

    def add_time(self, chat, hours, actor, event):
        hours = float(hours)
        if not math.isfinite(hours) or not 0 < hours <= 8760:
            raise ValueError("Часы: число больше 0 и не больше 8760.")
        now = time.time()
        with self.db:
            if self.db.execute("SELECT 1 FROM subscription_events WHERE id=?", (event,)).fetchone():
                return self.access_until(chat)
            until = max(now, self.access_until(chat)) + hours * 3600
            self.db.execute("INSERT INTO " + self.subscription_table + " VALUES (?,?) ON CONFLICT(chat) DO UPDATE SET until=excluded.until", (chat, until))
            self.db.execute("INSERT INTO subscription_events VALUES (?,?,?,?,?)", (event, chat, hours, actor, now))
        return until

    def authorize(self, chat):
        self.allowed.add(chat)
        self.revoked.discard(chat)
        with self.db:
            self.db.execute("DELETE FROM revoked WHERE chat=?", (chat,))
            self.db.execute("INSERT OR IGNORE INTO authorized VALUES (?)", (chat,))

    async def revoke_access(self, chat):
        if chat == ADMIN_ID:
            raise ValueError("Нельзя отозвать доступ администратора.")
        remove_user_password(chat)
        self.allowed.discard(chat)
        self.revoked.add(chat)
        self.state(chat)
        with self.db:
            self.db.execute("DELETE FROM authorized WHERE chat=?", (chat,))
            self.db.execute("INSERT OR IGNORE INTO revoked VALUES (?)", (chat,))
            self.db.execute("UPDATE users SET enabled=0 WHERE chat=?", (chat,))
        await self.cancel_scan(chat)

    def state(self, chat):
        with self.db:
            self.db.execute("INSERT OR IGNORE INTO users(chat) VALUES (?)", (chat,))
        row = dict(self.db.execute("SELECT * FROM users WHERE chat=?", (chat,)).fetchone())
        row["urls"], row["rules"] = json.loads(row["urls"]), json.loads(row["rules"])
        return row

    def save(self, chat, **changes):
        if not changes or not changes.keys() <= {"urls", "rules", "enabled", "minutes", "next_check", "last"}:
            raise ValueError("Некорректные настройки.")
        values = [json.dumps(v, ensure_ascii=False) if k in {"urls", "rules"} else v for k, v in changes.items()]
        with self.db:
            self.db.execute("UPDATE users SET " + ",".join(k + "=?" for k in changes) + " WHERE chat=?", values + [chat])

    def trigger(self, chat):
        if self.closing or not self.permitted(chat) or not self.state(chat)["urls"]:
            return False
        if chat in self.tasks and not self.tasks[chat].done():
            return False
        self.save(chat, next_check=time.time() + self.state(chat)["minutes"] * 60)
        self.tasks[chat] = asyncio.create_task(self.scan(chat))
        return True

    async def tick(self, context):
        if SUBSCRIPTIONS_ENABLED:
            active = set(self.tasks) | {r["chat"] for r in self.db.execute("SELECT chat FROM users WHERE enabled=1")}
            for chat in active:
                if not self.permitted(chat):
                    self.save(chat, enabled=0)
                    await self.cancel_scan(chat)
        for row in list(self.db.execute("SELECT chat FROM users WHERE enabled=1 AND next_check<=?", (time.time(),))):
            self.trigger(row["chat"])

    async def cancel_scan(self, chat):
        task = self.tasks.get(chat)
        if task and not task.done():
            task.cancel()
            with suppress(asyncio.CancelledError):
                await task

    async def send(self, chat, ad):
        buttons = [[InlineKeyboardButton("🔗 Ссылка на товар", url=ad["url"])]]
        if ad.get("seller_url"):
            buttons.append([InlineKeyboardButton("👤 Профиль продавца", url=ad["seller_url"])])
        markup = InlineKeyboardMarkup(buttons)
        text = card(ad)
        size = len(BeautifulSoup(text, "html.parser").get_text().encode("utf-16-le")) // 2
        if ad.get("images"):
            try:
                if size <= 1024:
                    await telegram_call(self.bot.send_photo, chat_id=chat, photo=ad["images"][0], caption=text, parse_mode="HTML", reply_markup=markup)
                    return
                await telegram_call(self.bot.send_photo, chat_id=chat, photo=ad["images"][0],
                    caption=escape(ad["title"][:100]), parse_mode="HTML")
            except BadRequest as exc:
                log.warning("Не удалось отправить фото: %s", exc)
        await telegram_call(self.bot.send_message, chat_id=chat, text=text, parse_mode="HTML", reply_markup=markup)

    async def live_progress(self, message, stats):
        previous = ""
        while True:
            await asyncio.sleep(20)
            text = (
                "⏳ Проверка продолжается…\n"
                f"Страниц: {stats['pages']}\n"
                f"Обработано новых: {stats['checked']}\n"
                f"Отправлено: {stats['sent']}\n"
                f"Уже отправлялись: {stats['duplicates']}\n"
                f"Отсеяно: {stats['filtered']}\n"
                f"Ошибок: {stats['errors']}\n\n"
                "Итоговый отчёт появится после завершения.\nОстановка: /pause"
            )
            if text != previous:
                try:
                    await telegram_call(message.edit_text, text=text)
                    previous = text
                except TelegramError:
                    log.warning("[scan_progress] Не удалось обновить прогресс")

    async def scan(self, chat):
        stats, warnings, missing, seen = Counter(), {}, set(), set()
        outcome, started, stop = "complete", time.monotonic(), False
        report_allowed = True
        progress_task = None
        last_delivery = 0.0
        try:
            progress_message = await telegram_call(self.bot.send_message, chat_id=chat, text="🚀 Начинаю проверку объявлений…")
            if progress_message is not None:
                progress_task = asyncio.create_task(self.live_progress(progress_message, stats))
            async with self.lock:
                self.reader.browser_failures = 0
                for source in list(self.state(chat)["urls"]):
                    url, pages_seen = source, set()
                    for page_index in range(MAX_PAGES):
                        if stop or source not in self.state(chat)["urls"]:
                            break
                        if not self.permitted(chat):
                            outcome, stop = "stopped", True
                            break
                        if url in pages_seen:
                            warnings["Обнаружен повтор страницы категории."] = True
                            break
                        pages_seen.add(url)
                        try:
                            raw, final = await self.reader.get(url)
                            ads, next_url = await asyncio.to_thread(parse_category, raw, final)
                            stats["pages"] += 1
                            log.info("[scan_page] chat=%s page=%s cards=%s has_next=%s", chat, stats["pages"], len(ads), bool(next_url))
                        except RateLimit as exc:
                            warnings[str(exc)] = True
                            stats["errors"] += 1
                            outcome, stop = "partial", True
                            break
                        except (SourceError, ValueError) as exc:
                            warnings[str(exc)] = True
                            stats["errors"] += 1
                            outcome = "partial"
                            break
                        for ad in ads:
                            key = urlsplit(ad["url"]).hostname + ":" + ad["id"]
                            if key in seen:
                                continue
                            seen.add(key)
                            stats["found"] += 1
                            if self.db.execute("SELECT 1 FROM delivered WHERE chat=? AND key=?", (chat, key)).fetchone():
                                stats["duplicates"] += 1
                                continue
                            if stats["checked"] >= MAX_ADS or stats["sent"] >= MAX_SEND:
                                outcome, stop = "limit", True
                                break
                            if source not in self.state(chat)["urls"] or not self.permitted(chat):
                                break
                            stats["checked"] += 1
                            if excluded_topic(ad):
                                stats["filtered"] += 1
                                stats["topic_skipped"] += 1
                                continue
                            try:
                                rules = self.state(chat)["rules"]
                                ad, warning = await self.reader.enrich(ad, rules=rules)
                                if ad.pop("_filtered_before_profile", False):
                                    stats["filtered"] += 1
                                    continue
                                absent_profile = {k for k in ("seller_views", "listings_count") if ad.get(k) is None}
                                missing.update(absent_profile)
                                if absent_profile:
                                    stats["profiles"] += 1
                                if warning:
                                    warnings[warning] = True
                                accepted, absent = matches(ad, rules)
                                missing.update(absent)
                                if not accepted:
                                    stats["filtered"] += 1
                                    continue
                                # Загрузка следующей карточки занимает время сама;
                                # ждём только остаток интервала между отправками.
                                await asyncio.sleep(max(0, last_delivery + 1.1 - time.monotonic()))
                                if not self.permitted(chat):
                                    outcome, stop = "stopped", True
                                    break
                                await self.send(chat, ad)
                                with self.db:
                                    self.db.execute("INSERT OR IGNORE INTO delivered VALUES (?,?)", (chat, key))
                                stats["sent"] += 1
                                last_delivery = time.monotonic()
                            except Forbidden:
                                raise
                            except RateLimit as exc:
                                warnings[str(exc)] = True
                                stats["errors"] += 1
                                outcome, stop = "partial", True
                                break
                            except (SourceError, ValueError, TelegramError) as exc:
                                stats["errors"] += 1
                                warnings[str(exc)[:220]] = True
                                log.warning("Объявление %s: %s", ad["id"], type(exc).__name__)
                            except Exception:
                                stats["errors"] += 1
                                warnings[f"Объявление {ad['id']}: ошибка обработки; подробности в логах Render."] = True
                                log.exception("Ошибка обработки объявления %s", ad["id"])
                        if stop or not next_url:
                            break
                        if urlsplit(next_url).hostname != urlsplit(final).hostname:
                            warnings["Следующая страница ведёт на другую страну."] = True
                            outcome = "partial"
                            break
                        url = next_url
                        if page_index + 1 == MAX_PAGES:
                            outcome = "limit"
                    if stop:
                        break
        except asyncio.CancelledError:
            outcome = "stopped"
            raise
        except Forbidden:
            self.save(chat, enabled=0)
            report_allowed = False
        except Exception:
            outcome = "error"
            stats["errors"] += 1
            warnings["Ошибка проверки; подробности записаны в логах Render."] = True
            log.exception("Проверка прервана для chat=%s", chat)
        finally:
            if progress_task is not None:
                progress_task.cancel()
                with suppress(asyncio.CancelledError):
                    await progress_task
            if outcome == "complete" and warnings:
                outcome = "partial"
            for warning in warnings:
                log.warning("[scan_detail] chat=%s %s", chat, error_text(warning))
            if missing:
                log.warning("[scan_missing] chat=%s fields=%s", chat, ",".join(sorted(missing)))
            report = report_text(stats, time.monotonic() - started, outcome, warnings, missing)
            log.info("[scan_done] chat=%s outcome=%s pages=%s sent=%s duplicates=%s filtered=%s topic_skipped=%s errors=%s", chat, outcome, stats["pages"], stats["sent"], stats["duplicates"], stats["filtered"], stats["topic_skipped"], stats["errors"])
            with suppress(sqlite3.Error):
                self.save(chat, last=report, next_check=time.time() + self.state(chat)["minutes"] * 60)
            # Удаляем только собственную задачу, чтобы не затронуть новый запуск.
            if self.tasks.get(chat) is asyncio.current_task():
                self.tasks.pop(chat, None)
            if report_allowed and not self.closing:
                markup = InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔄 Перезапустить парсер", callback_data="restart_scan")],
                    [InlineKeyboardButton("🏠 Главное меню", callback_data="menu_home")],
                ])
                try:
                    await telegram_call(self.bot.send_message, chat_id=chat, text=report, parse_mode="HTML", reply_markup=markup)
                except Forbidden:
                    self.save(chat, enabled=0)
                except TelegramError:
                    log.exception("Не удалось доставить итоговый отчёт")

    async def close(self):
        self.closing = True
        tasks = list(self.tasks.values())
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        await self.reader.close()
        await self.billing.close()
        self.db.close()


async def handle_commands(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if not message or not message.text or not user or not chat or chat.type != "private":
        return
    service = context.application.bot_data["service"]
    text = message.text.strip()
    parts = text.split(maxsplit=1)
    if not parts:
        return
    command, argument = parts[0].split("@")[0].lower(), parts[1] if len(parts) > 1 else ""
    if is_blocked(user.id):
        await message.reply_text("⛔ Вы заблокированы.")
        return
    if command == "/id":
        await message.reply_text(f"Ваш Telegram ID: {user.id}")
        return
    try:
        if command in {"/admin", "/createpass", "/block", "/unblock"}:
            if user.id != ADMIN_ID:
                return
            if command == "/admin":
                await message.reply_text("👑 Админ-панель\n/createpass ID — создать пароль\n/block ID — заблокировать\n/unblock ID — разблокировать")
                return
            target = int(argument)
            if target <= 0:
                raise ValueError("Укажите положительный Telegram ID.")
            if command == "/createpass":
                password = "".join(secrets.choice(string.ascii_letters + string.digits) for _ in range(12))
                await service.revoke_access(target)
                save_user_password(target, password)
                await message.reply_text(f"Пароль для {target}: <code>{password}</code>", parse_mode="HTML")
            elif command == "/block":
                if target == ADMIN_ID:
                    raise ValueError("Нельзя заблокировать администратора.")
                block_user(target)
                service.state(target)
                service.save(target, enabled=0)
                await service.cancel_scan(target)
                await message.reply_text(f"Пользователь {target} заблокирован.")
            else:
                unblock_user(target)
                await message.reply_text(f"Пользователь {target} разблокирован.")
            return
        if not service.permitted(user.id):
            if check_user_password(user.id, text):
                service.authorize(user.id)
                await message.reply_text("✅ Доступ открыт. Отправьте ссылку на категорию.", reply_markup=get_main_menu())
            else:
                await message.reply_text("🔒 Бот приватный. Введите выданный пароль.")
            return
        state = service.state(chat.id)
        if command == "/start":
            await message.reply_text("👋 Отправьте ссылку на категорию OpenSooq или выберите действие.", reply_markup=get_main_menu())
        elif command == "/help":
            await message.reply_text(HELP_TEXT)
        elif command in {"/filters", "/set"}:
            if argument:
                state["rules"] = update_filters(state["rules"], argument)
                service.save(chat.id, rules=state["rules"])
            await message.reply_text(filters_text(state), parse_mode="HTML")
        elif command == "/reset":
            service.save(chat.id, rules={})
            await message.reply_text("✅ Фильтры сброшены.")
        elif command == "/testproxy":
            if not service.reader.proxy_url:
                await message.reply_text("Добавьте OPENSOOQ_PROXY_URL в Environment на Render и перезапустите сервис.")
                return
            await message.reply_text("Проверяю профиль chilltime Ali через настроенный прокси…")
            try:
                raw, _ = await service.reader.get("https://kw.opensooq.com/en/mid/member-103907011724500523077")
                profile = await asyncio.to_thread(parse_profile, raw, "39101505")
                def value(key):
                    item = profile.get(key)
                    return "нет данных" if item is None else str(item)
                await message.reply_text(
                    "Профиль загружен: HTTP 200.\n"
                    f"Просмотры: {value('seller_views')}\n"
                    f"Активных объявлений: {value('listings_count')}\n"
                    f"Продано: {value('sold')}\n"
                    f"Рейтинг: {value('rating')}\n"
                    f"Оценок: {value('ratings')}\n"
                    f"Отзывов: {value('reviews')}"
                )
            except (SourceError, ValueError) as exc:
                await message.reply_text("Проверка профиля: " + error_text(exc)[:700])
        elif command == "/sources":
            sources = "\n".join(f"{i}. {u}" for i, u in enumerate(state["urls"], 1))
            await message.reply_text((sources or "Категории не добавлены. Отправьте ссылку.")[:3900], disable_web_page_preview=True)
        elif command == "/remove":
            index = int(argument) - 1
            if not 0 <= index < len(state["urls"]):
                raise ValueError("Нет категории с таким номером. См. /sources.")
            state["urls"].pop(index)
            service.save(chat.id, urls=state["urls"])
            await message.reply_text("✅ Категория удалена.")
        elif command == "/interval":
            minutes = int(argument)
            if not 5 <= minutes <= 1440:
                raise ValueError("Интервал: 5–1440 минут.")
            service.save(chat.id, minutes=minutes, next_check=time.time() + minutes * 60)
            await message.reply_text(f"Интервал: {minutes} мин.")
        elif command in {"/pause", "/stop"}:
            service.save(chat.id, enabled=0)
            await service.cancel_scan(chat.id)
            await message.reply_text("⏸ Мониторинг остановлен.")
        elif command == "/status":
            active = chat.id in service.tasks and not service.tasks[chat.id].done()
            status = f"Мониторинг: {'включён' if state['enabled'] else 'выключен'}\nПроверка: {'выполняется' if active else 'не выполняется'}\nИнтервал: {state['minutes']} мин.\nКатегорий: {len(state['urls'])}\n\n"
            await message.reply_text(escape(status) + (state["last"] or "Проверок ещё не было."), parse_mode="HTML")
        elif command in {"/check", "/watch", "/restart", "/add"} or text.startswith(("https://", "http://")):
            if command == "/add" or text.startswith(("https://", "http://")):
                url = safe_url(argument if command == "/add" else text)
                if re.search(r"/(?:search|lists)/\d+", urlsplit(url).path):
                    raise ValueError("Нужна ссылка на категорию, а не на отдельное объявление.")
                if url not in state["urls"]:
                    if len(state["urls"]) >= 5:
                        raise ValueError("Максимум 5 категорий.")
                    state["urls"].append(url)
                    service.save(chat.id, urls=state["urls"])
            if not state["urls"]:
                raise ValueError("Сначала добавьте категорию.")
            if command == "/watch":
                service.save(chat.id, enabled=1)
            if command == "/restart":
                await service.cancel_scan(chat.id)
            started = service.trigger(chat.id)
            await message.reply_text("🚀 Проверка запущена." if started else "⏳ Проверка уже выполняется.")
        else:
            await message.reply_text("Отправьте ссылку на категорию или /help.")
    except ValueError as exc:
        await message.reply_text(str(exc)[:800] or "Проверьте параметры команды: /help.")




# Панель Telegram: категории, фильтры и сохранённые настройки поиска.
FILTER_LABELS = {
    "price": "Цена", "seller_views": "Просмотры продавца",
    "listings_count": "Активные объявления продавца", "rating": "Рейтинг продавца",
    "ratings": "Количество оценок", "reviews": "Отзывы", "sold": "Продано",
    "photos": "Количество фото", "views": "Просмотры объявления",
}
TEXT_LABELS = {"keywords": "Искать слова", "exclude": "Исключить слова", "currency": "Валюта"}
COUNTRY_LABELS = {"kw": "🇰🇼 Кувейт", "ae": "🇦🇪 ОАЭ", "bh": "🇧🇭 Бахрейн", "sa": "🇸🇦 Саудовская Аравия"}


def ui_keyboard(rows):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(label, callback_data=data) for label, data in row]
        for row in rows
    ])


def ui_number(value):
    return f"{value:g}" if isinstance(value, float) else str(value)


def ui_range(rules, metric):
    low, high = rules.get(metric + "_min"), rules.get(metric + "_max")
    if low is None and high is None:
        return "без ограничений"
    if low is not None and high is not None:
        return f"{ui_number(low)}–{ui_number(high)}"
    return "от " + ui_number(low) if low is not None else "до " + ui_number(high)


def ui_url(url):
    return escape(url if len(url) <= 180 else url[:177] + "…")


def metric_input(rules, metric, text):
    if metric not in FILTER_LABELS:
        raise ValueError("Неизвестный фильтр.")
    text = unicodedata.normalize("NFKC", text).strip()
    if text.lower() in {"off", "none"}:
        result = dict(rules)
        result.pop(metric + "_min", None)
        result.pop(metric + "_max", None)
        return result
    match = re.fullmatch(
        r"(?:от\s*)?(\d+(?:[.,]\d+)?)\s*(?:-|–|—|\.\.|до)\s*(\d+(?:[.,]\d+)?)", text, re.I)
    if match:
        return update_filters(rules, f"{metric}_min={match[1]} {metric}_max={match[2]}")
    if not re.fullmatch(r"\d+(?:[.,]\d+)?", text):
        raise ValueError("Введите диапазон, например 1-99999, либо одно число для максимума. Убрать ограничение: off.")
    return update_filters(rules, f"{metric}_max={text}")


def source_key(url):
    return hashlib.sha256(url.encode()).hexdigest()[:16]


def source_country(url):
    code = (urlsplit(url).hostname or "").split(".")[0]
    return COUNTRY_LABELS.get(code, "OpenSooq")


def checked_source(value):
    url = safe_url(value)
    if re.search(r"/(?:search|lists)/\d+", urlsplit(url).path):
        raise ValueError("Нужна ссылка на категорию или выдачу, а не на отдельное объявление.")
    return url


def get_main_menu():
    return ui_keyboard([
        [("🚀 Начать поиск", "menu_check")],
        [("🔗 Категории", "menu_sources"), ("⚙️ Фильтры", "menu_filters")],
        [("💾 Мои поиски", "ui:saved"), ("🌍 Страна", "ui:countries")],
        [("⏱ Мониторинг", "ui:monitor"), ("📊 Статус", "menu_status")],
        [("⏸ Остановить", "menu_stop"), ("❔ Помощь", "menu_help")],
        [("💳 Подписка", "bill:plans")],
    ])


def filters_text(state):
    rules = state["rules"]
    lines = ["⚙️ <b>Фильтры поиска</b>", "", "Нажмите на поле, чтобы изменить его.",
             "Цена сравнивается в валюте объявления; пересчёта валют нет.", ""]
    for metric, label in FILTER_LABELS.items():
        lines.append(f"{label}: <b>{escape(ui_range(rules, metric))}</b>")
    for field, label in TEXT_LABELS.items():
        lines.append(f"{label}: <b>{escape(str(rules.get(field) or 'не задано'))}</b>")
    lines.extend(["", "Неизвестные значения: " + (
        "разрешены при числовых ограничениях" if rules.get("unknown") == "include"
        else "исключаются при заданных ограничениях"),
        "Слова для поиска работают по принципу «хотя бы одно».",
        "Авто, недвижимость, услуги и вакансии исключаются по категории ещё до загрузки карточки. Если категория неизвестна — используется заголовок."])
    return "\n".join(lines)


def saved_rows(service, chat):
    return list(service.db.execute(
        "SELECT id,name,config FROM saved_searches WHERE chat=? ORDER BY id DESC", (chat,)))


def saved_row(service, chat, search_id):
    row = service.db.execute("SELECT * FROM saved_searches WHERE chat=? AND id=?", (chat, search_id)).fetchone()
    if row is None:
        raise ValueError("Этот сохранённый поиск уже удалён.")
    return row


def save_search(service, chat, name):
    name = " ".join(name.split())
    if not name or len(name) > 50 or name.startswith(("http://", "https://")):
        raise ValueError("Название: от 1 до 50 символов. Например: ОАЭ · телефоны.")
    state = service.state(chat)
    if not state["urls"]:
        raise ValueError("Сначала добавьте хотя бы одну категорию.")
    if len(saved_rows(service, chat)) >= 20:
        raise ValueError("Можно сохранить до 20 поисков. Удалите один из старых.")
    config = {key: state[key] for key in ("urls", "rules", "minutes")}
    try:
        with service.db:
            service.db.execute("INSERT INTO saved_searches(chat,name,config,created) VALUES (?,?,?,?)",
                (chat, name, json.dumps(config, ensure_ascii=False), time.time()))
    except sqlite3.IntegrityError:
        raise ValueError("Поиск с таким названием уже есть. Укажите другое название.") from None


async def load_search(service, chat, search_id):
    row = saved_row(service, chat, search_id)
    config = json.loads(row["config"])
    urls = [checked_source(url) for url in config["urls"]]
    if not 1 <= len(urls) <= 5:
        raise ValueError("Некорректные категории в сохранённом поиске.")
    minutes = int(config["minutes"])
    if not 5 <= minutes <= 1440:
        raise ValueError("Некорректный интервал в сохранённом поиске.")
    rules = dict(config["rules"])
    service.save(chat, enabled=0)
    await service.cancel_scan(chat)
    service.save(chat, urls=urls, rules=rules, minutes=minutes,
                 enabled=0, next_check=time.time() + minutes * 60)
    return row["name"]


async def show_panel(update, text, keyboard):
    options = dict(parse_mode="HTML", reply_markup=keyboard, disable_web_page_preview=True)
    query = update.callback_query
    if query and query.message:
        try:
            await query.message.edit_text(text, **options)
            return
        except BadRequest as exc:
            if "message is not modified" in str(exc).lower():
                return
    await update.effective_message.reply_text(text, **options)


async def panel(update, context, screen="home", notice=""):
    service = context.application.bot_data["service"]
    chat = update.effective_chat.id
    state = service.state(chat)
    back = [("‹ Главное меню", "menu_home")]
    if screen == "sources":
        lines = ["🔗 <b>Категории поиска</b>", "", "Каждую ссылку можно заменить или удалить."]
        rows = []
        for index, url in enumerate(state["urls"], 1):
            lines.append(f"\n<b>{index}. {source_country(url)}</b>\n{ui_url(url)}")
            key = source_key(url)
            rows.append([(f"✏️ Заменить №{index}", "ui:replace:" + key),
                         (f"🗑 Удалить №{index}", "ui:delete:" + key)])
        if not state["urls"]:
            lines.append("\nПока нет категорий. Добавьте ссылку или выберите страну.")
        rows.extend([[("＋ Добавить ссылку", "ui:add"), ("🌍 Выбрать страну", "ui:countries")], back])
        text, keyboard = "\n".join(lines), ui_keyboard(rows)
    elif screen == "filters":
        rows = [[(label, "ui:metric:" + key)] for key, label in FILTER_LABELS.items()]
        rows.extend([[("🔎 Искать слова", "ui:field:keywords"), ("🚫 Исключить слова", "ui:field:exclude")],
                     [("💱 Валюта", "ui:currency"), ("❔ Нет данных", "ui:unknown")],
                     [("↺ Сбросить фильтры", "ui:reset")], back])
        text, keyboard = filters_text(state), ui_keyboard(rows)
    elif screen == "saved":
        records = saved_rows(service, chat)
        text = ("💾 <b>Мои поиски</b>\n\n"
                "Сохраняются категории, фильтры и интервал.\n"
                "Загрузка заменяет текущие настройки и останавливает мониторинг.\n"
                "История отправленных объявлений общая и сохраняется.\n\n")
        text += f"Сохранено: <b>{len(records)}/20</b>" if records else "Пока нет сохранённых поисков."
        rows = [[(row["name"], f"ui:search:{row['id']}")] for row in records]
        rows.extend([[("＋ Сохранить текущий поиск", "ui:save")], back])
        keyboard = ui_keyboard(rows)
    elif screen == "monitor":
        text = ("⏱ <b>Мониторинг</b>\n\n"
                f"Состояние: {'🟢 включён' if state['enabled'] else '⚪ выключен'}\n"
                f"Интервал: <b>{state['minutes']} мин.</b>\n\n"
                "Регулярный поиск отправляет только ещё не доставленные объявления.")
        keyboard = ui_keyboard([[("🟢 Включить", "ui:watch"), ("⏸ Остановить", "menu_stop")],
            [(f"{n} мин.", f"ui:interval:{n}") for n in (5, 15, 30, 60)],
            [("Другой интервал", "ui:custom_interval")], back])
    elif screen == "status":
        active = chat in service.tasks and not service.tasks[chat].done()
        text = ("📊 <b>Статус</b>\n\n"
            f"Мониторинг: {'🟢 включён' if state['enabled'] else '⚪ выключен'}\n"
            f"Проверка: {'выполняется или ожидает очереди' if active else 'не выполняется'}\n"
            f"Категорий: {len(state['urls'])} · Интервал: {state['minutes']} мин.\n\n"
            + (state["last"] or "Проверок ещё не было."))
        keyboard = get_main_menu()
    else:
        active = chat in service.tasks and not service.tasks[chat].done()
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
import sys
import threading
import tempfile
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
    for key in ("BOT_TOKEN", "XROCKET_API_TOKEN"):
        secret = os.getenv(key, "").strip()
        if secret:
            text = text.replace(secret, "[hidden]")
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

def registration_date(value):
    """Только дата аккаунта из явно названного поля, без выдуманного дня."""
    text = unicodedata.normalize("NFKC", plain(value))
    text = "".join(str(unicodedata.digit(c)) if c.isdecimal() else c for c in text)
    for pattern, fmt in ((r"(?<!\d)\d{4}-\d{2}-\d{2}(?!\d)", "%Y-%m-%d"),
                         (r"(?<!\d)\d{2}-\d{2}-\d{4}(?!\d)", "%d-%m-%Y"),
                         (r"(?<!\d)\d{2}/\d{2}/\d{4}(?!\d)", "%d/%m/%Y"),
                         (r"(?<!\d)\d{2}\.\d{2}\.\d{4}(?!\d)", "%d.%m.%Y")):
        match = re.search(pattern, text)
        if match:
            with suppress(ValueError):
                return datetime.strptime(match[0], fmt).strftime("%d.%m.%Y")
    # Дата с названием месяца: поддерживаем лишь явные английские форматы.
    for fmt in ("%d %B %Y", "%d %b %Y", "%B %d, %Y", "%b %d, %Y", "%B %Y", "%b %Y"):
        candidate = re.sub(r"^(?:Member\s+Since|Joined|Registered)\s*:?\s*", "", text, flags=re.I).strip()
        with suppress(ValueError):
            parsed = datetime.strptime(candidate, fmt)
            return parsed.strftime("%m.%Y" if "%d" not in fmt else "%d.%m.%Y")
    if re.fullmatch(r"(?:Member\s+Since\s*:?\s*)?(?:19|20)\d{2}", text, re.I):
        return text[-4:]
    return ""


def seller_keys(ad):
    """ID и точная ссылка профиля; имя продавца не является идентификатором."""
    keys = []
    seller_id = str(ad.get("seller_id") or "").strip()
    if seller_id and seller_id != "0":
        keys.append(f"id:{seller_id}")
    if ad.get("seller_url"):
        with suppress(ValueError):
            profile = urlsplit(safe_url(ad["seller_url"], ad["url"]))
            keys.append(f"{profile.hostname}:url:{unquote(profile.path).rstrip('/')}")
    return keys


def rules_key(rules):
    normalized = {k: int(v) if isinstance(v, float) and v.is_integer() else v for k, v in rules.items()}
    return hashlib.sha256(json.dumps(normalized, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def recent_source(url):
    parsed = urlsplit(safe_url(url))
    query = [(k, v) for k, v in parse_qsl(parsed.query, keep_blank_values=True) if k not in {"page", "sort_code"}]
    query.append(("sort_code", "recent"))
    return safe_url(urlunsplit((parsed.scheme, parsed.netloc, parsed.path, urlencode(query), "")))


def parse_profile(raw, expected_id):
    """Счётчики профиля; listings_count — общее число Live Listings."""
    soup = BeautifulSoup(raw, "html.parser")
    result = {key: None for key in (
        "rating", "ratings", "reviews", "seller_views", "sold", "listings_count", "seller_registered"
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
            "views_count", "views", "posts_count", "member_info", "rating", "member_since"
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
        for field in ("member_since", "registration_date", "registered_at", "joined_at"):
            registered = registration_date(member.get(field))
            if registered and result["seller_registered"] is None:
                result["seller_registered"] = registered
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
    if result["seller_registered"] is None:
        match = re.search(r"(?:Member\s+Since|Joined|Registered|عضو\s+منذ|تاريخ\s+التسجيل|تاريخ\s+الانضمام)\s*:?\s*([^|•]{1,55})", page_text, re.I)
        if match:
            result["seller_registered"] = registration_date(match[1]) or None
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
    registered = registration_date(owner.get("member_since") or owner.get("memberSince") or owner.get("registrationDate"))
    if registered:
        ad["seller_registered"] = registered
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

    async def enrich(self, ad, rules=None, seller_seen=None):
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
        if seller_seen is not None and seller_seen(ad):
            ad["_seller_already_sent"] = True
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
        f"📦 Активных объявлений: <b>{show('listings_count')}</b>",
        "📅 Регистрация продавца: <b>" + escape(str(ad.get("seller_registered") or "нет данных")) + "</b>"])
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
/check — проверить ещё не просмотренные объявления
/deepcheck — пройти старые страницы, пропуская проверенные карточки
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
Повторная проверка пропускает уже проверенные карточки с теми же фильтрами.
От одного продавца отправляется одно объявление.
После двух страниц только со знакомыми карточками быстрый поиск останавливается.
/deepcheck продолжает поиск глубже: полезно, если свежая карточка попала ниже закреплённых.
"""






def report_text(stats, elapsed, outcome, warnings, missing):
    titles = {"complete": "✅ Поиск завершён", "partial": "⏹ Поиск завершён",
              "error": "❌ Поиск прерван", "stopped": "⏸ Поиск остановлен", "limit": "📦 Достигнут лимит поиска"}
    seconds = max(0, round(elapsed))
    duration = f"{seconds // 60} мин. {seconds % 60} сек." if seconds >= 60 else f"{seconds} сек."
    text = (f"<b>{titles[outcome]}</b>\n\n"
        f"Отправлено объявлений: <b>{stats['sent']}</b>\n"
        f"Уже отправлялись: <b>{stats['duplicates']}</b>\n"
        f"Проверены ранее: <b>{stats['previously_checked']}</b>\n"
        f"Повторы продавцов: <b>{stats['seller_duplicates']}</b>\n"
        f"Время: <b>{duration}</b>\n\n"
        f"Страниц: {stats['pages']} · Карточек: {stats['found']}\n"
        f"Проверено карточек: {stats['checked']}\n"
        f"Отсеяно фильтрами: {stats['filtered']} · Ошибок: {stats['errors']}")
    if stats["history_boundary"]:
        text += "\n\nСвежая часть выдачи проверена; дальше знакомые карточки. Глубокая проверка: /deepcheck."
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
            CREATE TABLE IF NOT EXISTS checked_ads(
                chat INTEGER NOT NULL, rules TEXT NOT NULL, key TEXT NOT NULL,
                PRIMARY KEY(chat,rules,key)
            );
            CREATE TABLE IF NOT EXISTS delivered_sellers(
                chat INTEGER NOT NULL, key TEXT NOT NULL, PRIMARY KEY(chat,key)
            );
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
        self.account_browser = PersistentOpenSooqBrowser()
        self.dialogues = SellerDialogues(self)
        self.account_login = AccountLogin(self)

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

    def seller_seen(self, chat, ad):
        return any(self.db.execute("SELECT 1 FROM delivered_sellers WHERE chat=? AND key=?", (chat, key)).fetchone()
                   for key in seller_keys(ad))

    def remember_seller(self, chat, ad):
        self.db.executemany("INSERT OR IGNORE INTO delivered_sellers VALUES (?,?)", [(chat, key) for key in seller_keys(ad)])

    def mark_checked(self, chat, signature, key):
        with self.db:
            self.db.execute("INSERT OR IGNORE INTO checked_ads VALUES (?,?,?)", (chat, signature, key))

    def trigger(self, chat, deep=False):
        if self.closing or not self.permitted(chat) or not self.state(chat)["urls"]:
            return False
        if chat in self.tasks and not self.tasks[chat].done():
            return False
        self.save(chat, next_check=time.time() + self.state(chat)["minutes"] * 60)
        self.tasks[chat] = asyncio.create_task(self.scan(chat, deep=deep))
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
        if chat == ADMIN_ID:
            token = self.dialogues.register(chat, ad)
            if token:
                buttons.append([InlineKeyboardButton("💬 Начать диалог", callback_data="talk:start:"+token)])
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
                f"Проверено карточек: {stats['checked']}\n"
                f"Отправлено: {stats['sent']}\n"
                f"Уже отправлялись: {stats['duplicates']}\n"
                f"Проверены ранее: {stats['previously_checked']}\n"
                f"Повторы продавцов: {stats['seller_duplicates']}\n"
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

    async def scan(self, chat, deep=False):
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
                    url, pages_seen = recent_source(source), set()
                    known_pages = 0
                    scan_rules = self.state(chat)["rules"]
                    signature = rules_key(scan_rules)
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
                        # Определяем границу по истории ДО обработки этой страницы.
                        page_known = bool(ads)
                        for candidate in ads:
                            candidate_key = urlsplit(candidate["url"]).hostname + ":" + candidate["id"]
                            known = (self.db.execute("SELECT 1 FROM delivered WHERE chat=? AND key=?", (chat, candidate_key)).fetchone()
                                     or self.db.execute("SELECT 1 FROM checked_ads WHERE chat=? AND rules=? AND key=?", (chat, signature, candidate_key)).fetchone()
                                     or self.seller_seen(chat, candidate))
                            if not known:
                                page_known = False
                                break
                        for ad in ads:
                            if self.state(chat)["rules"] != scan_rules:
                                warnings["Фильтры изменены во время проверки. Запустите поиск заново."] = True
                                outcome, stop = "partial", True
                                break
                            key = urlsplit(ad["url"]).hostname + ":" + ad["id"]
                            if key in seen:
                                continue
                            seen.add(key)
                            stats["found"] += 1
                            if self.db.execute("SELECT 1 FROM delivered WHERE chat=? AND key=?", (chat, key)).fetchone():
                                stats["duplicates"] += 1
                                with self.db:
                                    self.remember_seller(chat, ad)
                                continue
                            if self.seller_seen(chat, ad):
                                stats["seller_duplicates"] += 1
                                continue
                            if self.db.execute("SELECT 1 FROM checked_ads WHERE chat=? AND rules=? AND key=?", (chat, signature, key)).fetchone():
                                stats["previously_checked"] += 1
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
                                self.mark_checked(chat, signature, key)
                                continue
                            try:
                                rules = scan_rules
                                ad, warning = await self.reader.enrich(ad, rules=rules, seller_seen=lambda item: self.seller_seen(chat, item))
                                if self.state(chat)["rules"] != scan_rules:
                                    warnings["Фильтры изменены во время проверки. Запустите поиск заново."] = True
                                    outcome, stop = "partial", True
                                    break
                                if ad.pop("_seller_already_sent", False) or self.seller_seen(chat, ad):
                                    stats["seller_duplicates"] += 1
                                    self.mark_checked(chat, signature, key)
                                    continue
                                if ad.pop("_filtered_before_profile", False):
                                    stats["filtered"] += 1
                                    self.mark_checked(chat, signature, key)
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
                                    # Не закрепляем отказ из-за временно недоступных данных.
                                    if not absent and not warning:
                                        self.mark_checked(chat, signature, key)
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
                                    self.remember_seller(chat, ad)
                                    self.db.execute("INSERT OR IGNORE INTO checked_ads VALUES (?,?,?)", (chat, signature, key))
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
                        known_pages = known_pages + 1 if page_known else 0
                        if not deep and known_pages >= 2:
                            stats["history_boundary"] += 1
                            break
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
        await self.account_login.close()
        await self.dialogues.close()
        await self.account_browser.close()
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
        elif command in {"/check", "/deepcheck", "/watch", "/restart", "/add"} or text.startswith(("https://", "http://")):
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
            started = service.trigger(chat.id, deep=command == "/deepcheck")
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
                "Поиск начинается со свежих объявлений и пропускает уже проверенные карточки с теми же фильтрами. Один продавец — одно объявление. Глубокая проверка: /deepcheck.")
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
        countries = ", ".join(dict.fromkeys(source_country(url) for url in state["urls"])) or "не выбрана"
        text = ("🔎 <b>Панель поиска OpenSooq</b>\n\n"
            f"🌍 {countries}\n"
            f"🔗 Категорий: <b>{len(state['urls'])}/5</b>\n"
            f"⚙️ Настроек фильтров: <b>{len(state['rules'])}</b>\n"
            f"💾 Сохранённых поисков: <b>{len(saved_rows(service, chat))}</b>\n"
            f"⏱ Мониторинг: {'включён' if state['enabled'] else 'выключен'} · {state['minutes']} мин.\n"
            f"{'⏳ Поиск выполняется или ожидает очереди.' if active else 'Готов к запуску.'}\n\n"
            "Выберите действие ниже.")
        keyboard = get_main_menu()
    if screen == "home" and update.effective_user.id == ADMIN_ID:
        keyboard = InlineKeyboardMarkup(list(keyboard.inline_keyboard) + [[InlineKeyboardButton("👑 Пользователи", callback_data="ui:admin"), InlineKeyboardButton("💬 Диалоги",callback_data="talk:list")]])
    if notice:
        text = escape(notice) + "\n\n" + text
    await show_panel(update, text, keyboard)


async def ask_field(update, context, action, prompt, **payload):
    context.user_data["panel_form"] = dict(action=action, payload=payload, expires=time.time() + 600)
    await show_panel(update, prompt + "\n\nОтправьте ответ одним сообщением. Отмена: /cancel",
        ui_keyboard([[ ("Отмена", "ui:cancel") ]]))


async def handle(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, user, chat = update.effective_message, update.effective_user, update.effective_chat
    service = context.application.bot_data["service"]
    if not message or not message.text or not user or not chat or chat.type != "private":
        return
    command = message.text.strip().split(maxsplit=1)[0].split("@")[0].lower() if message.text.strip() else ""
    if command in {"/account","/account_off","/account_diag"}:
        if user.id!=ADMIN_ID:
            await message.reply_text("Подключение личного аккаунта доступно только владельцу.")
            return
        try:
            if command=="/account_diag":
                await message.reply_text(service.account_login.diagnostic_text())
                return
            if command=="/account":
                parts=message.text.strip().split()
                country=parts[1].lower() if len(parts)==2 else "sa"
                if len(parts)>2 or country not in COUNTRIES:
                    await message.reply_text("Выберите страну аккаунта: /account sa, /account kw, /account ae или /account bh. Без параметра — Саудовская Аравия.")
                    return
                origin=account_origin()
                if not os.getenv('PORT'):
                    raise ValueError('Включите Web Service с PORT на Render для страницы входа.')
                token=await service.account_login.issue(country)
                keyboard=InlineKeyboardMarkup([[InlineKeyboardButton('🔐 Войти в OpenSooq',url=origin+'/account#'+token)]])
                await message.reply_text("Страна входа: "+COUNTRY_LABELS[country]+"\n\n🔐 Личная страница управления на 15 минут. Браузер использует постоянный профиль. Активные диалоги поставлены на паузу. Сначала войдите через главную OpenSooq: кнопка «Вход / профиль», затем Login or Sign Up. После успешного входа откройте существующий чат и нажмите «Сохранить вход». Браузер входа и переписка используют OPENSOOQ_PROXY_URL, если он задан. Новый /account открывает главную; чаты автоматически не открываются. Ссылку не пересылайте. Коды в Telegram вводить не нужно.",reply_markup=keyboard)
            else:
                await disconnect_opensooq_account(service)
                await message.reply_text("⏸ Аккаунт отключён от автоответчика, активные диалоги остановлены. Парсер работает как раньше.")
        except (ValueError,OSError):
            await message.reply_text('Не удалось открыть подключение аккаунта. Проверьте HTTPS-адрес RENDER_EXTERNAL_URL, PORT и доступ на запись в DATA_DIR. Секреты в чат не присылайте.')
        return
    if command in {"/dialogs", "/chatstatus", "/dialog", "/stopdialogs"}:
        if user.id != ADMIN_ID:
            await message.reply_text("Переписка с личного аккаунта доступна только владельцу.")
            return
        if command == "/stopdialogs":
            dialogs=service.dialogues
            dialogs.cancelled.update(r['id'] for r in dialogs.db.execute('SELECT id FROM seller_dialogues WHERE chat=?',(ADMIN_ID,)))
            async with dialogs.lock:
                with dialogs.db:
                    dialogs.db.execute("UPDATE seller_dialogues SET state='paused',note='Остановлен владельцем' WHERE chat=? AND state IN ('queued','waiting','sending','approved')",(ADMIN_ID,))
            await message.reply_text("⏸ Автоответы во всех диалогах остановлены.")
        elif command == "/chatstatus":
            worker=service.dialogues.transport
            mode='постоянный профиль' if worker.profile_mode else 'прежний файл сессии или ещё не подключён'
            await message.reply_text("Переписка на Render: "+("настройки заданы; вход проверяется при запуске диалога." if worker.configured() else "не подключена.")+"\nРежим: "+mode+".\nПодключить аккаунт с телефона: /account. Отключить: /account_off. Для сохранения после перезапуска DATA_DIR должен находиться на постоянном диске Render. Коды и профиль в Telegram не присылайте.")
        elif command == "/dialog":
            try:
                url=safe_url(message.text.split(maxsplit=1)[1])
                match=re.fullmatch(r"/(?:en|ar)/(?:search|lists)/(\d+)(?:/.*)?",urlsplit(url).path)
                if not match:
                    raise ValueError("Нужна ссылка на конкретное объявление OpenSooq.")
                raw,final=await service.reader.get(url)
                ad=dict.fromkeys(METRICS)
                ad.update(id=match[1],url=final,title="",description="",seller_id="",seller_name="",seller_url="",images=[])
                ad=await asyncio.to_thread(parse_listing,raw,ad)
                token=service.dialogues.register(chat.id,ad)
                if not token:
                    raise ValueError("Не удалось подтвердить профиль продавца.")
                await message.reply_text("Начать сценарий по этому товару?\n"+ad['seller_name']+" · "+ad['title'],reply_markup=ui_keyboard([[('💬 Начать диалог','talk:start:'+token)]]))
            except (ValueError,IndexError,SourceError) as exc:
                await message.reply_text(str(exc)[:800] if not isinstance(exc,IndexError) else "Используйте /dialog ССЫЛКА_НА_ОБЪЯВЛЕНИЕ")
        else:
            await dialogue_panel(update,context)
        return
    if await billing_message(update, context):
        return
    if not service.permitted(user.id):
        await handle_commands(update, context)
        return
    text = message.text.strip()
    command = text.split(maxsplit=1)[0].split("@")[0].lower() if text else ""
    form = context.user_data.get("panel_form")
    if text.startswith("/"):
        context.user_data.pop("panel_form", None)
        if command in {"/admin", "/users", "/revokepass", "/revoke"}:
            if user.id != ADMIN_ID:
                await message.reply_text("Эта команда доступна только администратору.")
                return
            if command in {"/revokepass", "/revoke"}:
                try:
                    target = admin_target(text.split(maxsplit=1)[1])
                    await service.revoke_access(target)
                    await message.reply_text(f"🚫 Пароль и доступ пользователя {target} отозваны. Мониторинг остановлен.")
                except (ValueError, IndexError) as exc:
                    await message.reply_text(str(exc) if isinstance(exc, ValueError) else "Используйте /revokepass ID")
            else:
                await admin_panel(update, context)
            return
        if command in {"/start", "/cancel", "/sources", "/saved", "/status"}:
            await panel(update, context, {"/sources": "sources", "/saved": "saved", "/status": "status"}.get(command, "home"))
            return
        if command == "/filters" and len(text.split(maxsplit=1)) == 1:
            await panel(update, context, "filters")
            return
        await handle_commands(update, context)
        return
    if form:
        if form["expires"] < time.time():
            context.user_data.pop("panel_form", None)
            await panel(update, context, notice="Время ввода истекло. Выберите действие заново.")
            return
        action, payload = form["action"], form["payload"]
        state = service.state(chat.id)
        screen, notice = "home", "✅ Сохранено."
        try:
            if action in {"add", "replace"}:
                url = checked_source(text)
                urls = list(state["urls"])
                if action == "replace":
                    old = payload["url"]
                    if old not in urls:
                        raise ValueError("Категория уже изменена. Отмените ввод и откройте список заново.")
                    if url in urls and url != old:
                        raise ValueError("Такая категория уже есть.")
                    urls[urls.index(old)] = url
                else:
                    if url in urls:
                        raise ValueError("Эта категория уже добавлена.")
                    if len(urls) >= 5:
                        raise ValueError("Максимум 5 категорий. Сначала удалите одну.")
                    urls.append(url)
                service.save(chat.id, urls=urls)
                screen = "sources"
            elif action in {"filter", "range"}:
                if action == "range":
                    metric = payload["metric"]
                    rules = metric_input(state["rules"], metric, text)
                    notice = f"✅ {FILTER_LABELS[metric]}: {ui_range(rules, metric)}. Фильтр сохранён."
                else:
                    field = payload["field"]
                    metric, _, bound = field.rpartition("_")
                    range_text = re.fullmatch(r"(?:от\s*)?\d+(?:[.,]\d+)?\s*(?:-|–|—|\.\.|до)\s*\d+(?:[.,]\d+)?", text, re.I)
                    if metric in FILTER_LABELS and bound in {"min", "max"} and range_text:
                        rules = metric_input(state["rules"], metric, text)
                        notice = f"✅ {FILTER_LABELS[metric]}: {ui_range(rules, metric)}. Фильтр сохранён."
                    else:
                        rules = update_filters(state["rules"], field + "=" + shlex.quote(text))
                        label = TEXT_LABELS.get(field, FILTER_LABELS.get(metric, field))
                        display = ui_range(rules, metric) if metric in FILTER_LABELS else str(rules.get(field) or "не задано")
                        notice = f"✅ {label}: {display}. Фильтр сохранён."
                service.save(chat.id, rules=rules)
                screen = "filters"
            elif action == "save":
                save_search(service, chat.id, text)
                screen, notice = "saved", "💾 Поиск сохранён."
            elif action == "admin_target":
                if user.id != ADMIN_ID:
                    raise ValueError("Доступ закрыт.")
                target = admin_target(text)
                context.user_data.pop("panel_form", None)
                await admin_confirmation(update, context, payload["kind"], target)
                return
            elif action == "interval":
                minutes = int(text)
                if not 5 <= minutes <= 1440:
                    raise ValueError("Введите число от 5 до 1440.")
                service.save(chat.id, minutes=minutes, next_check=time.time() + minutes * 60)
                screen = "monitor"
            context.user_data.pop("panel_form", None)
            await panel(update, context, screen, notice)
        except ValueError as exc:
            await message.reply_text(str(exc)[:800] + "\nПопробуйте ещё раз или /cancel.")
        return
    if text.startswith(("http://", "https://")):
        try:
            url = checked_source(text)
            urls = service.state(chat.id)["urls"]
            if url in urls:
                await panel(update, context, "sources", "Эта категория уже есть.")
                return
            if len(urls) >= 5:
                raise ValueError("Максимум 5 категорий. Удалите одну или замените её.")
            service.save(chat.id, urls=urls + [url])
            await panel(update, context, "sources", "✅ Категория добавлена. Для запуска нажмите «Начать поиск».")
        except ValueError as exc:
            await message.reply_text(str(exc))
        return
    await panel(update, context)


async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query, user, chat = update.callback_query, update.effective_user, update.effective_chat
    service = context.application.bot_data["service"]
    if query and (query.data or "").startswith("talk:"):
        await dialogue_callback(update,context)
        return
    if query and user and chat and chat.type == "private" and (query.data or "").startswith("bill:"):
        await billing_callback(update, context)
        return
    if not query or not user or not chat or chat.type != "private" or not service.permitted(user.id):
        if query:
            await query.answer("Доступ закрыт.", show_alert=True)
        return
    await query.answer()
    context.user_data.pop("panel_form", None)
    data, state = query.data or "", service.state(chat.id)
    back = [("‹ Главное меню", "menu_home")]
    try:
        navigation = {"menu_home": "home", "menu_sources": "sources", "menu_filters": "filters",
                      "menu_status": "status", "ui:saved": "saved", "ui:monitor": "monitor", "ui:cancel": "home"}
        if data.startswith("ui:admin"):
            if user.id != ADMIN_ID:
                raise ValueError("Админ-панель доступна только владельцу.")
            await admin_callback(update, context, data)
        elif data in navigation:
            await panel(update, context, navigation[data])
        elif data in {"menu_check", "restart_scan", "ui:watch"}:
            if not state["urls"]:
                await panel(update, context, "sources", "Сначала добавьте категорию.")
                return
            if data == "restart_scan":
                await service.cancel_scan(chat.id)
            if data == "ui:watch":
                service.save(chat.id, enabled=1)
            started = service.trigger(chat.id)
            await panel(update, context, notice="🚀 Поиск запущен." if started else "⏳ Поиск уже выполняется.")
        elif data == "menu_stop":
            service.save(chat.id, enabled=0)
            await service.cancel_scan(chat.id)
            await panel(update, context, notice="⏸ Поиск и мониторинг остановлены.")
        elif data == "menu_help":
            await show_panel(update, HELP_TEXT + "\n/saved — сохранённые поиски\n/cancel — отменить ввод\n\nСсылки можно добавлять, заменять и удалять кнопками в разделе «Категории».\nОтправленная ссылка сохраняется; запуск выполняется кнопкой «Начать поиск».", get_main_menu())
        elif data == "ui:add":
            await ask_field(update, context, "add", "🔗 <b>Добавить категорию</b>\nОтправьте ссылку на категорию или выдачу OpenSooq.")
        elif data.startswith(("ui:replace:", "ui:delete:", "ui:delete_yes:")):
            key = data.rsplit(":", 1)[1]
            url = next((url for url in state["urls"] if source_key(url) == key), None)
            if url is None:
                raise ValueError("Эта категория уже изменена или удалена.")
            if data.startswith("ui:replace:"):
                await ask_field(update, context, "replace", "✏️ <b>Заменить категорию</b>\nТекущая ссылка:\n" + ui_url(url) + "\n\nОтправьте новую ссылку.", url=url)
            elif data.startswith("ui:delete_yes:"):
                service.save(chat.id, urls=[item for item in state["urls"] if item != url])
                if len(state["urls"]) == 1:
                    service.save(chat.id, enabled=0)
                    await service.cancel_scan(chat.id)
                await panel(update, context, "sources", "🗑 Категория удалена.")
            else:
                await show_panel(update, "🗑 <b>Удалить эту категорию?</b>\n\n" + ui_url(url),
                    ui_keyboard([[ ("Да, удалить", "ui:delete_yes:" + key) ], [("Отмена", "menu_sources")]]))
        elif data == "ui:countries":
            await show_panel(update, "🌍 <b>Выберите страну</b>\n\nБудет предложена общая выдача выбранной страны.",
                ui_keyboard([[(label, "ui:country:" + code)] for code, label in COUNTRY_LABELS.items()] + [back]))
        elif data.startswith("ui:country:"):
            code = data.rsplit(":", 1)[1]
            if code not in COUNTRY_LABELS:
                raise ValueError("Неизвестная страна.")
            await show_panel(update, f"🌍 <b>{COUNTRY_LABELS[code]}</b>\n\nЗаменить текущие категории общей выдачей этой страны?\nФильтры сохранятся — проверьте выбранную валюту.\nМониторинг будет остановлен. Сохраните текущий поиск заранее, если он нужен.",
                ui_keyboard([[("Заменить категории", "ui:country_yes:" + code)], [("Отмена", "menu_sources")]]))
        elif data.startswith("ui:country_yes:"):
            code = data.rsplit(":", 1)[1]
            if code not in COUNTRY_LABELS:
                raise ValueError("Неизвестная страна.")
            service.save(chat.id, enabled=0)
            await service.cancel_scan(chat.id)
            service.save(chat.id, urls=[f"https://{code}.opensooq.com/en/find?search=true&sort_code=recent"])
            await panel(update, context, "sources", "✅ Страна изменена. Проверьте фильтры и нажмите «Начать поиск».")
        elif data.startswith("ui:metric:"):
            metric = data.rsplit(":", 1)[1]
            if metric not in FILTER_LABELS:
                raise ValueError("Неизвестный фильтр.")
            context.user_data["panel_form"] = dict(action="range", payload={"metric": metric}, expires=time.time() + 600)
            await show_panel(update, f"⚙️ <b>{FILTER_LABELS[metric]}</b>\n\nСейчас: <b>{escape(ui_range(state['rules'], metric))}</b>\n\nОтправьте диапазон одним сообщением: <code>1-99999</code>.\nОдно число задаёт максимум.\nФильтр сохранится автоматически.\n\nТакже можно отдельно выбрать минимум или максимум кнопками ниже.\nСнять обе границы: <code>off</code>. Отмена: /cancel.", ui_keyboard([
                [("Минимум", "ui:field:" + metric + "_min"), ("Максимум", "ui:field:" + metric + "_max")],
                [("Убрать ограничение", "ui:clear:" + metric)], [("‹ Все фильтры", "menu_filters")]]))
        elif data.startswith("ui:field:"):
            field = data.rsplit(":", 1)[1]
            metric, _, bound = field.rpartition("_")
            if field in TEXT_LABELS:
                label = TEXT_LABELS[field]
                hint = "Слова через запятую, например: iphone,samsung." if field != "currency" else "Код из трёх букв, например AED."
            elif metric in FILTER_LABELS and bound in {"min", "max"}:
                label = FILTER_LABELS[metric] + (" — минимум" if bound == "min" else " — максимум")
                hint = "Одно число. Для снятия ограничения: off."
            else:
                raise ValueError("Неизвестное поле.")
            await ask_field(update, context, "filter", f"⚙️ <b>{label}</b>\n{hint}\nТекущее значение: {escape(str(state['rules'].get(field, 'не задано')))}\nДля удаления значения отправьте off.", field=field)
        elif data.startswith("ui:clear:"):
            metric = data.rsplit(":", 1)[1]
            if metric not in FILTER_LABELS:
                raise ValueError("Неизвестный фильтр.")
            rules = dict(state["rules"])
            rules.pop(metric + "_min", None)
            rules.pop(metric + "_max", None)
            service.save(chat.id, rules=rules)
            await panel(update, context, "filters", "✅ Ограничение снято.")
        elif data == "ui:currency":
            await show_panel(update, "💱 <b>Валюта цены</b>\n\nОбъявления с другой валютой будут исключаться. Пересчёта валют нет.", ui_keyboard([
                [(code, "ui:currency_set:" + code) for code in ("KWD", "AED", "SAR", "BHD")],
                [("Любая валюта", "ui:currency_set:off"), ("Другая", "ui:field:currency")], [("‹ Фильтры", "menu_filters")]]))
        elif data.startswith("ui:currency_set:"):
            rules = update_filters(state["rules"], "currency=" + data.rsplit(":", 1)[1])
            service.save(chat.id, rules=rules)
            await panel(update, context, "filters", "✅ Валюта сохранена.")
        elif data == "ui:unknown":
            await show_panel(update, "❔ <b>Если значение неизвестно</b>\n\nПример: задан минимум просмотров, но профиль недоступен.\n«Исключать» — такое объявление не отправляется.\n«Разрешать» — может отправиться, если остальные фильтры подходят.", ui_keyboard([
                [("Исключать", "ui:unknown_set:exclude"), ("Разрешать", "ui:unknown_set:include")], [("‹ Фильтры", "menu_filters")]]))
        elif data.startswith("ui:unknown_set:"):
            rules = update_filters(state["rules"], "unknown=" + data.rsplit(":", 1)[1])
            service.save(chat.id, rules=rules)
            await panel(update, context, "filters", "✅ Настройка сохранена.")
        elif data == "ui:reset":
            await show_panel(update, "↺ <b>Сбросить все пользовательские фильтры?</b>\nКатегории и сохранённые поиски останутся.", ui_keyboard([
                [("Сбросить", "ui:reset_yes"), ("Отмена", "menu_filters")]]))
        elif data == "ui:reset_yes":
            service.save(chat.id, rules={})
            await panel(update, context, "filters", "✅ Фильтры сброшены.")
        elif data == "ui:save":
            if not state["urls"]:
                raise ValueError("Сначала добавьте категорию.")
            await ask_field(update, context, "save", "💾 <b>Сохранить текущий поиск</b>\nВведите название, например: ОАЭ · телефоны.\nСохранятся категории, фильтры и интервал.")
        elif data.startswith(("ui:search:", "ui:load:", "ui:load_yes:", "ui:drop:", "ui:drop_yes:")):
            search_id = int(data.rsplit(":", 1)[1])
            row = saved_row(service, chat.id, search_id)
            if data.startswith("ui:load_yes:"):
                name = await load_search(service, chat.id, search_id)
                await panel(update, context, notice=f"✅ Загружен поиск «{name}». Для запуска нажмите «Начать поиск».")
            elif data.startswith("ui:drop_yes:"):
                with service.db:
                    service.db.execute("DELETE FROM saved_searches WHERE chat=? AND id=?", (chat.id, search_id))
                await panel(update, context, "saved", "🗑 Сохранённый поиск удалён. Текущие настройки не менялись.")
            elif data.startswith("ui:load:"):
                await show_panel(update, "💾 <b>Загрузить поиск «" + escape(row["name"]) + "»?</b>\n\nТекущие категории и фильтры будут заменены. Мониторинг остановится. История отправок сохранится.", ui_keyboard([
                    [("Загрузить", f"ui:load_yes:{search_id}"), ("Отмена", "ui:saved")]]))
            elif data.startswith("ui:drop:"):
                await show_panel(update, "🗑 Удалить сохранённый поиск «" + escape(row["name"]) + "»?", ui_keyboard([
                    [("Удалить", f"ui:drop_yes:{search_id}"), ("Отмена", "ui:saved")]]))
            else:
                config = json.loads(row["config"])
                detail = "💾 <b>" + escape(row["name"]) + "</b>\n\n"
                detail += "\n".join(ui_url(url) for url in config["urls"])
                detail += f"\n\nИнтервал: {config['minutes']} мин.\n\n" + filters_text(config)
                await show_panel(update, detail, ui_keyboard([
                    [("📂 Загрузить", f"ui:load:{search_id}"), ("🗑 Удалить", f"ui:drop:{search_id}")], [("‹ Мои поиски", "ui:saved")]]))
        elif data == "ui:custom_interval":
            await ask_field(update, context, "interval", "⏱ <b>Интервал мониторинга</b>\nВведите количество минут: от 5 до 1440.")
        elif data.startswith("ui:interval:"):
            minutes = int(data.rsplit(":", 1)[1])
            if not 5 <= minutes <= 1440:
                raise ValueError("Интервал: 5–1440 минут.")
            service.save(chat.id, minutes=minutes, next_check=time.time() + minutes * 60)
            await panel(update, context, "monitor", "✅ Интервал сохранён.")
        else:
            await panel(update, context)
    except ValueError as exc:
        await query.message.reply_text(str(exc)[:800], reply_markup=get_main_menu())



def admin_target(value):
    try:
        target = int(str(value).strip())
    except (ValueError, TypeError):
        raise ValueError("Укажите Telegram ID пользователя числом.") from None
    if target <= 0:
        raise ValueError("Telegram ID должен быть положительным.")
    if target == ADMIN_ID:
        raise ValueError("Доступ администратора изменять нельзя.")
    return target


async def admin_panel(update, context, page=0, notice=""):
    if update.effective_user.id != ADMIN_ID:
        raise ValueError("Доступ закрыт.")
    service = context.application.bot_data["service"]
    known = set(service.allowed) | set(service.revoked)
    for table in ("users", "authorized"):
        known.update(row["chat"] for row in service.db.execute("SELECT chat FROM " + table))
    users = sorted(target for target in known if target > 0 and target != ADMIN_ID)
    pages = max(1, (len(users) + 9) // 10)
    page = max(0, min(page, pages - 1))
    lines = ["👑 <b>Пользователи</b>", "", f"Известных пользователей: <b>{len(users)}</b>",
             "🟢 доступ открыт · 🚫 отозван · ⛔ заблокирован · ⚪ ожидает входа", ""]
    rows = []
    for target in users[page * 10:(page + 1) * 10]:
        badge = "⛔" if is_blocked(target) else "🚫" if target in service.revoked else "🟢" if service.permitted(target) else "⚪"
        lines.append(f"{badge} <code>{target}</code>")
        rows.append([(f"{badge} {target}", f"ui:admin:user:{target}")])
    navigation = []
    if page:
        navigation.append(("‹ Назад", f"ui:admin:page:{page-1}"))
    if page + 1 < pages:
        navigation.append(("Далее ›", f"ui:admin:page:{page+1}"))
    if navigation:
        rows.append(navigation)
    rows.extend([
        [("🎁 Добавить часы / бесплатный период", "bill:gift")],
        [("🔑 Выдать пароль", "ui:admin:choose:create"), ("🚫 Отозвать доступ", "ui:admin:choose:revoke")],
        [("⛔ Блокировать", "ui:admin:choose:block"), ("✅ Разблокировать", "ui:admin:choose:unblock")],
        [("‹ Главное меню", "menu_home")],
    ])
    text = "\n".join(lines)
    if notice:
        text = escape(notice) + "\n\n" + text
    await show_panel(update, text, ui_keyboard(rows))


async def admin_confirmation(update, context, kind, target):
    if update.effective_user.id != ADMIN_ID:
        raise ValueError("Доступ закрыт.")
    target = admin_target(target)
    descriptions = {
        "create": "Выдать новый пароль? Старый пароль и текущая авторизация будут отозваны, мониторинг остановится.",
        "revoke": "Отозвать пароль и доступ? Пользователь потеряет авторизацию, его мониторинг остановится. Для возврата доступа нужно выдать новый пароль.",
        "block": "Заблокировать пользователя и остановить его мониторинг?",
        "unblock": "Снять блокировку пользователя? Отозванный пароль этим действием не восстанавливается.",
    }
    if kind not in descriptions:
        raise ValueError("Неизвестное действие.")
    await show_panel(update, f"👤 <code>{target}</code>\n\n" + descriptions[kind], ui_keyboard([
        [("Подтвердить", f"ui:admin:apply:{kind}:{target}"), ("Отмена", "ui:admin")],
    ]))


async def admin_callback(update, context, data):
    if update.effective_user.id != ADMIN_ID:
        raise ValueError("Доступ закрыт.")
    service = context.application.bot_data["service"]
    parts = data.split(":")
    if data == "ui:admin":
        await admin_panel(update, context)
    elif len(parts) == 4 and parts[2] == "page":
        await admin_panel(update, context, int(parts[3]))
    elif len(parts) == 4 and parts[2] == "choose":
        kind = parts[3]
        if kind not in {"create", "revoke", "block", "unblock"}:
            raise ValueError("Неизвестное действие.")
        await ask_field(update, context, "admin_target", "👤 <b>Telegram ID пользователя</b>\nПопросите пользователя отправить боту /id и пришлите полученное число.", kind=kind)
    elif len(parts) == 4 and parts[2] == "user":
        target = admin_target(parts[3])
        state = service.state(target)
        status = "заблокирован" if is_blocked(target) else "доступ отозван" if target in service.revoked else "доступ открыт" if service.permitted(target) else "ожидает входа"
        await show_panel(update, f"👤 <b>Пользователь</b> <code>{target}</code>\n\nСтатус: {status}\nПодписка до: {access_date(service.access_until(target))}\nКатегорий: {len(state['urls'])}\nМониторинг: {'включён' if state['enabled'] else 'выключен'}", ui_keyboard([
            [("🎁 Добавить часы", f"bill:gift:{target}")],
            [("🔑 Новый пароль", f"ui:admin:confirm:create:{target}"), ("🚫 Отозвать", f"ui:admin:confirm:revoke:{target}")],
            [("⛔ Блокировать", f"ui:admin:confirm:block:{target}"), ("✅ Разблокировать", f"ui:admin:confirm:unblock:{target}")],
            [("‹ Пользователи", "ui:admin")],
        ]))
    elif len(parts) == 5 and parts[2] == "confirm":
        await admin_confirmation(update, context, parts[3], admin_target(parts[4]))
    elif len(parts) == 5 and parts[2] == "apply":
        kind, target = parts[3], admin_target(parts[4])
        if kind == "create":
            await service.revoke_access(target)
            password = "".join(secrets.choice(string.ascii_letters + string.digits) for _ in range(12))
            save_user_password(target, password)
            await update.callback_query.message.reply_text(
                f"🔑 Новый пароль для <code>{target}</code>:\n<code>{password}</code>\n\nПередайте пароль пользователю. Его старый доступ отозван.", parse_mode="HTML")
            notice = f"Пароль для {target} создан."
        elif kind == "revoke":
            await service.revoke_access(target)
            notice = f"🚫 Пароль и доступ пользователя {target} отозваны."
        elif kind == "block":
            block_user(target)
            service.state(target)
            service.save(target, enabled=0)
            await service.cancel_scan(target)
            notice = f"⛔ Пользователь {target} заблокирован."
        elif kind == "unblock":
            unblock_user(target)
            notice = f"✅ Блокировка пользователя {target} снята."
        else:
            raise ValueError("Неизвестное действие.")
        await admin_panel(update, context, notice=notice)
    else:
        raise ValueError("Кнопка устарела. Откройте админ-панель заново.")


def access_date(value):
    return datetime.fromtimestamp(value, DISPLAY_TZ).strftime('%d.%m.%Y %H:%M %Z') if value else 'нет активного периода'


class RocketError(ValueError):
    pass


class Billing:
    def __init__(self, service):
        self.service = service
        self.token = os.getenv('XROCKET_API_TOKEN', '').strip()
        self.network = 'testnet' if XROCKET_TESTNET else 'mainnet'
        self.base = 'https://pay.api.testnet.xrocket.exchange' if XROCKET_TESTNET else 'https://pay.api.xrocket.exchange'
        self.http = None
        self.lock, self.api_lock = asyncio.Lock(), asyncio.Lock()
        self.next_request = 0.0

    async def request(self, method, path, **kwargs):
        if not self.token:
            raise RocketError('Оплата ещё не настроена. Обратитесь к владельцу.')
        if self.http is None:
            self.http = httpx.AsyncClient(timeout=15, trust_env=False, follow_redirects=False,
                headers={'Authorization': 'Bearer ' + self.token, 'Accept': 'application/json'})
        async with self.api_lock:
            if self.next_request > time.monotonic() + 5:
                raise RocketError('Платёжный сервис просит подождать. Повторите проверку позже.')
            await asyncio.sleep(max(0, self.next_request - time.monotonic()))
            self.next_request = time.monotonic() + 0.6
            try:
                response = await self.http.request(method, self.base + path, **kwargs)
            except httpx.RequestError:
                raise RocketError('Нет ответа от xRocket. Счёт сохранён, повторите проверку позже.') from None
        if response.status_code == 429:
            try:
                delay = float(response.headers.get('Retry-After', '60'))
            except ValueError:
                delay = 60
            self.next_request = time.monotonic() + (max(1, min(3600, delay)) if math.isfinite(delay) else 60)
        if not 200 <= response.status_code < 300:
            log.warning('[xrocket] HTTP %s method=%s', response.status_code, method)
            raise RocketError(f'xRocket: HTTP {response.status_code}. Проверка доступна позже; владелец может посмотреть логи.')
        try:
            body = response.json()
        except ValueError:
            raise RocketError('Некорректный ответ xRocket.') from None
        if not isinstance(body, dict):
            raise RocketError('Некорректный формат ответа xRocket.')
        # Current Pay API; варианты оболочки допускаются только с полями счёта.
        for key in ('invoice', 'data'):
            if isinstance(body.get(key), dict) and 'id' in body[key]:
                body = body[key]
                break
        return body

    def validate(self, order, invoice):
        try:
            valid = (isinstance(invoice, dict) and bool(invoice.get('id'))
                and invoice.get('clientInvoiceId') == order['id']
                and invoice.get('priceCurrency') == order['currency']
                and Decimal(str(invoice.get('priceAmount'))) == Decimal(order['amount'])
                and (not order['invoice'] or str(invoice['id']) == order['invoice']))
        except (InvalidOperation, TypeError, ValueError):
            valid = False
        if not valid:
            raise RocketError('Счёт не прошёл проверку суммы, валюты или идентификатора. Доступ не изменён.')

    async def create(self, chat, plan):
        if not SUBSCRIPTIONS_ENABLED:
            raise RocketError('Покупка подписок пока выключена.')
        if not os.getenv('SUPPORT_USERNAME', '').strip():
            raise RocketError('Владелец ещё не настроил контакт поддержки.')
        if plan not in PLANS:
            raise RocketError('Тариф отсутствует.')
        async with self.lock:
            db = self.service.db
            row = db.execute("SELECT * FROM payment_orders WHERE chat=? AND plan=? AND network=? AND applied=0 AND status='pending' AND created>? ORDER BY created DESC LIMIT 1", (chat, plan, self.network, time.time()-1800)).fetchone()
            existing = row is not None
            if row is None:
                hours, amount, _ = PLANS[plan]
                order_id = secrets.token_hex(16)
                with db:
                    db.execute('INSERT INTO payment_orders(id,chat,plan,hours,amount,currency,created,network) VALUES (?,?,?,?,?,?,?,?)',
                        (order_id, chat, plan, hours, amount, 'USDT', time.time(), self.network))
                row = db.execute('SELECT * FROM payment_orders WHERE id=?', (order_id,)).fetchone()
            order = dict(row)
            if order['link']:
                return order
            invoice = None
            if existing:
                with suppress(RocketError):
                    invoice = await self.request('GET', '/api/v1/invoice', params={'clientInvoiceId': order['id']})
            if invoice is None:
                payload = dict(priceAmount=order['amount'], priceCurrency='USDT', payoutCurrency='USDT',
                    payCurrencies=['USDT'], numPayments=1, clientInvoiceId=order['id'], expiresIn=1800000,
                    description='OpenSooq parser: ' + PLANS[plan][2], customer={'telegramId': str(chat)},
                    isFeePaidByUser=False)
                try:
                    invoice = await self.request('POST', '/api/v1/invoices', json=payload)
                except RocketError:
                    invoice = await self.request('GET', '/api/v1/invoice', params={'clientInvoiceId': order['id']})
            self.validate(order, invoice)
            link = (invoice.get('links') or {}).get('telegramBotLink', '')
            parsed = urlsplit(link)
            if parsed.scheme != 'https' or parsed.hostname != 't.me' or parsed.username or parsed.password:
                raise RocketError('xRocket не вернул корректную ссылку на оплату.')
            with db:
                db.execute('UPDATE payment_orders SET invoice=?, link=? WHERE id=?', (str(invoice['id']), link, order['id']))
            return dict(db.execute('SELECT * FROM payment_orders WHERE id=?', (order['id'],)).fetchone())

    async def check(self, order_id, chat=None):
        async with self.lock:
            db = self.service.db
            row = db.execute('SELECT * FROM payment_orders WHERE id=? AND network=?', (order_id, self.network)).fetchone()
            if row is None or (chat is not None and row['chat'] != chat):
                raise RocketError('Счёт не найден для этого пользователя.')
            order = dict(row)
            if order['applied']:
                return 'paid', False
            if order['status'] in {'expired', 'cancelled'}:
                return order['status'], False
            with db:
                db.execute('UPDATE payment_orders SET checked=? WHERE id=?', (time.time(), order_id))
            invoice = await self.request('GET', '/api/v1/invoice', params={'clientInvoiceId': order_id})
            self.validate(order, invoice)
            status = invoice.get('status')
            if status == 'paid':
                # Одна транзакция: начисление и отметка счёта фиксируются вместе.
                with db:
                    fresh = db.execute('SELECT applied FROM payment_orders WHERE id=?', (order_id,)).fetchone()
                    if fresh['applied']:
                        return 'paid', False
                    now = time.time()
                    until = max(now, self.service.access_until(order['chat'])) + order['hours'] * 3600
                    db.execute('INSERT INTO ' + self.service.subscription_table + ' VALUES (?,?) ON CONFLICT(chat) DO UPDATE SET until=excluded.until', (order['chat'], until))
                    db.execute('INSERT INTO subscription_events VALUES (?,?,?,?,?)', ('pay:' + order_id, order['chat'], order['hours'], 0, now))
                    db.execute("UPDATE payment_orders SET applied=1,status='paid',invoice=? WHERE id=?", (str(invoice['id']), order_id))
                log.info('[subscription_paid] chat=%s plan=%s order=%s', order['chat'], order['plan'], order_id)
                with suppress(TelegramError):
                    await self.service.bot.send_message(chat_id=order['chat'], text='✅ Оплата подтверждена. Период начислен до ' + access_date(until) + '.\nОткройте /start. Настройки поиска сохранены. Если доступ отозван администратором, обратитесь в поддержку.')
                return 'paid', True
            if status in {'expired', 'cancelled'}:
                with db:
                    db.execute('UPDATE payment_orders SET status=? WHERE id=?', (status, order_id))
            # unknown / active / partially_paid никогда не открывают доступ.
            return str(status or 'unknown'), False

    async def poll(self, context):
        if not SUBSCRIPTIONS_ENABLED or not self.token or self.service.closing:
            return
        rows = list(self.service.db.execute("SELECT id FROM payment_orders WHERE applied=0 AND status='pending' AND network=? ORDER BY checked,created LIMIT 10", (self.network,)))
        for row in rows:
            try:
                await self.check(row['id'])
            except RocketError as exc:
                log.warning('[payment_check] order=%s error=%s', row['id'], type(exc).__name__)
        # Счета не удаляются по местным часам: поздний платёж сверяется с API.

    async def close(self):
        if self.http is not None:
            await self.http.aclose()


async def subscription_panel(update, context, notice=''):
    service = context.application.bot_data['service']
    user_id = update.effective_user.id
    service.state(user_id)
    status = '👑 Владелец: бесплатно и бессрочно.' if user_id == ADMIN_ID else 'Доступ до: ' + access_date(service.access_until(user_id))
    support = os.getenv('SUPPORT_USERNAME', '').strip().lstrip('@')
    text = '💳 <b>Подписка на парсер</b>\n\n' + escape(status) + '\n\n'
    if XROCKET_TESTNET:
        text += '🧪 <b>ТЕСТОВЫЙ РЕЖИМ: только тестовые средства.</b>\n\n'
    if notice:
        text += escape(notice) + '\n\n'
    text += 'Оплата в USDT через xRocket. Разовая покупка, без автоматического списания.\nПродление добавляется к оставшемуся сроку. 30 дней = 720 часов.\n\n'
    if support:
        text += 'Поддержка: @' + escape(support) + '\n'
    rows = [[(f'{label} · {amount} USDT', 'bill:buy:' + key)] for key, (_, amount, label) in PLANS.items()]
    pending = service.db.execute("SELECT id FROM payment_orders WHERE chat=? AND applied=0 AND status='pending' AND network=? ORDER BY created DESC LIMIT 1", (user_id, service.billing.network)).fetchone()
    if pending:
        rows.append([('🔄 Проверить последний счёт', 'bill:check:' + pending['id'])])
    if service.permitted(user_id):
        rows.append([('‹ Главное меню', 'menu_home')])
    await show_panel(update, text, ui_keyboard(rows))


async def billing_message(update, context):
    service = context.application.bot_data['service']
    text, user_id = update.effective_message.text.strip(), update.effective_user.id
    command = text.split(maxsplit=1)[0].split('@')[0].lower() if text else ''
    form = context.user_data.get('panel_form') or {}
    if command in {'/addhours', '/free'} or (form.get('action') == 'billing_gift' and not text.startswith('/')):
        if user_id != ADMIN_ID:
            await update.effective_message.reply_text('Только владелец может выдавать бесплатное время.')
            return True
        if form.get('action') == 'billing_gift' and not text.startswith('/'):
            if form.get('expires', 0) < time.time():
                context.user_data.pop('panel_form', None)
                await update.effective_message.reply_text('Время ввода истекло. Откройте админ-панель снова.')
                return True
            payload = form['payload']
            text = (str(payload['target']) + ' ' + text) if payload.get('target') else text
            argument = text
        else:
            argument = text.partition(' ')[2]
        try:
            target_text, hours_text = argument.split()
            target = admin_target(target_text)
            hours = float(hours_text.replace(',', '.'))
            if not math.isfinite(hours) or not 0 < hours <= 8760:
                raise ValueError('Часы: число больше 0 и не больше 8760.')
            nonce = secrets.token_hex(8)
            context.user_data['billing_grant'] = {'id': nonce, 'target': target, 'hours': hours, 'expires': time.time()+600}
            context.user_data.pop('panel_form', None)
            await show_panel(update, f'🎁 Выдать <b>{hours:g} ч.</b> пользователю <code>{target}</code>?\n\nВремя прибавится к оставшемуся сроку. Оплата не требуется.', ui_keyboard([[('Выдать время', 'bill:grant:' + nonce)], [('Отмена', 'bill:cancel')]]))
        except ValueError as exc:
            await update.effective_message.reply_text(str(exc) if len(argument.split()) == 2 else 'Используйте /addhours ID ЧАСЫ или /free ID ЧАСЫ. Например: /free 123456789 24')
        return True
    if command in {'/subscription', '/buy', '/paysupport'}:
        if is_blocked(user_id) or user_id in service.revoked:
            await update.effective_message.reply_text('Доступ отозван. Обратитесь к владельцу.')
        else:
            await subscription_panel(update, context)
        return True
    if SUBSCRIPTIONS_ENABLED and not service.permitted(user_id) and command != '/id':
        if is_blocked(user_id) or user_id in service.revoked:
            await update.effective_message.reply_text('Доступ отозван. Обратитесь к владельцу.')
        else:
            await subscription_panel(update, context, 'Для запуска поиска нужна активная подписка. Ваши настройки сохраняются.')
        return True
    return False


async def billing_callback(update, context):
    query, user_id = update.callback_query, update.effective_user.id
    service = context.application.bot_data['service']
    await query.answer()
    parts = (query.data or '').split(':')
    try:
        if parts[1] in {'gift', 'grant', 'cancel'}:
            if user_id != ADMIN_ID:
                raise ValueError('Только владелец может выдавать время.')
            if parts[1] == 'cancel':
                context.user_data.pop('billing_grant', None)
                context.user_data.pop('panel_form', None)
                await admin_panel(update, context)
            elif parts[1] == 'gift':
                target = admin_target(parts[2]) if len(parts) == 3 else None
                prompt = '🎁 Сколько часов выдать бесплатно?' if target else '🎁 Отправьте Telegram ID и число бесплатных часов через пробел. Например: 123456789 24'
                await ask_field(update, context, 'billing_gift', prompt, target=target)
            else:
                grant = context.user_data.get('billing_grant') or {}
                if len(parts) != 3 or grant.get('id') != parts[2] or grant.get('expires', 0) < time.time():
                    raise ValueError('Выдача уже выполнена или кнопка устарела.')
                until = service.add_time(grant['target'], grant['hours'], ADMIN_ID, 'gift:' + grant['id'])
                service.authorize(grant['target'])
                service.state(grant['target'])
                context.user_data.pop('billing_grant', None)
                await admin_panel(update, context, notice=f"Выдано {grant['hours']:g} ч. для {grant['target']}. Доступ до {access_date(until)}. Блокировка, если была, остаётся.")
            return
        if is_blocked(user_id) or user_id in service.revoked:
            raise ValueError('Доступ отозван. Обратитесь к владельцу.')
        if parts[1] == 'plans':
            await subscription_panel(update, context)
        elif parts[1] == 'buy' and len(parts) == 3:
            if user_id == ADMIN_ID:
                await subscription_panel(update, context, 'Тебе покупать подписку не нужно 😄')
                return
            order = await service.billing.create(user_id, parts[2])
            markup = InlineKeyboardMarkup([[InlineKeyboardButton('Оплатить в xRocket', url=order['link'])], [InlineKeyboardButton('🔄 Проверить оплату', callback_data='bill:check:' + order['id'])], [InlineKeyboardButton('‹ Тарифы', callback_data='bill:plans')]])
            await show_panel(update, f"💳 <b>Счёт xRocket</b>\n\n{escape(PLANS[order['plan']][2])}: <b>{order['amount']} USDT</b>\n\nОплатите и нажмите «Проверить оплату». Автопроверка тоже включена. Доступ выдаётся владельцу этого счёта в боте. Счёт действует 30 минут.", markup)
        elif parts[1] == 'check' and len(parts) == 3:
            state, _ = await service.billing.check(parts[2], user_id)
            notices = {'paid': '✅ Оплата подтверждена. Период уже начислен.', 'expired': 'Срок счёта истёк. Создайте новый.', 'cancelled': 'Счёт отменён.'}
            await subscription_panel(update, context, notices.get(state, 'Оплата пока не подтверждена полностью. Повторите проверку позже.'))
        else:
            raise ValueError('Кнопка устарела.')
    except (ValueError, IndexError) as exc:
        await query.message.reply_text(str(exc)[:500])


# Переписка с продавцами: один выбранный товар, один вопрос после нового ответа.
DIALOG_QUESTIONS = (
    "Hi! I'm interested in this item. Is it still available?",
    "Is everything in good condition?",
    "How long have you been using it?",
    "Why are you selling it?",
    "Do you still have the receipt?",
    "Is that your final price?",
)


def dialogue_answer(text, stage, answered):
    """Консервативный сценарий. Неясный ответ отдаём владельцу, не угадываем."""
    text = unicodedata.normalize('NFKC', text).casefold().strip()
    text = re.sub(r'\s+', ' ', text.replace('’', "'"))
    answered = set(answered)
    if re.search(r"\b(sold|not available|no longer available|already gone|stop messaging|do not contact|don't contact|leave me alone)\b|مباع|لا تراسل", text):
        return 'stopped', answered, None
    if not text or re.fullmatch(r'(hi|hello|hey|good morning|good evening|مرحبا|السلام عليكم)[.! ]*', text):
        return 'wait', answered, None
    # Вопрос продавца или предложение перевода/внешнего перехода требует человека.
    if re.search(r'https?://|\?|\b(pay|deposit|transfer|whatsapp|telegram|ignore previous|send money|delivery fee|you want|do you|are you|can you|will you)\b', text):
        return 'review', answered, None
    yes = bool(re.search(r'\b(yes|yeah|yep|sure|ok|okay|available|of course)\b|نعم|متوفر', text))
    no = bool(re.search(r"\b(no|nope|not|isn't|doesn't|don't|broken|damaged|faulty)\b|ليس|لا يوجد", text))
    if stage == 0 and re.fullmatch(r'(no|nope|sorry no)[.! ]*', text):
        return 'stopped', answered, None
    if re.search(r'\b(good|excellent|perfect|mint|working|brand new|like new)\b', text) and not no:
        answered.add(1)
    if re.search(r'\b\d+\s*(days?|weeks?|months?|years?|hrs?|hours?)\b|\b(never used|unused|brand new)\b', text):
        answered.add(2)
    if re.search(r'\b(because|moving|upgrad\w*|bought another|no longer need|need money)\b', text):
        answered.add(3)
    if re.search(r'\b(receipt|invoice|proof of purchase)\b', text):
        if yes or no or re.search(r'\b(have|lost|included|missing)\b', text):
            answered.add(4)
    if re.search(r'\b(price is firm|price is final|final price|no negotiation)\b', text):
        answered.add(5)
    if stage == 0 and yes and not no:
        answered.add(0)
    elif stage == 1 and yes and not no:
        answered.add(1)
    elif stage == 4 and (yes or no):
        answered.add(4)
    elif stage == 5 and (yes or no or re.search(r'\d|\b(final|firm|lowest|negotiable)\b', text)):
        answered.add(5)
    if stage not in answered:
        return 'review', answered, None
    next_stage = next((i for i in range(stage + 1, len(DIALOG_QUESTIONS)) if i not in answered), None)
    return ('complete' if next_stage is None else 'next'), answered, next_stage


class DialogueUnavailable(ValueError):
    pass


class PersistentOpenSooqBrowser:
    """Один выделенный профиль и один браузер для ручного входа и переписки."""
    def __init__(self, directory=None):
        self.directory=Path(directory) if directory is not None else DATA_DIR/'opensooq-browser-profile'
        self.lock=asyncio.Lock()
        self.pw=self.context=self.page=None
        self._file_lock=None
        self.on_blocked=None

    def _acquire_profile(self):
        import fcntl
        self.directory.mkdir(parents=True,exist_ok=True,mode=0o700)
        os.chmod(self.directory,0o700)
        fd=os.open(self.directory/'.bot-profile.lock',os.O_RDWR|os.O_CREAT,0o600)
        try:
            os.fchmod(fd,0o600)
            fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BaseException:
            os.close(fd)
            raise
        self._file_lock=fd

    def _release_profile(self):
        if self._file_lock is not None:
            fd,self._file_lock=self._file_lock,None
            os.close(fd)

    def _context_closed(self,context):
        if self.context is context:
            self.context=self.page=None

    async def _restrict_navigation(self,route):
        request=route.request
        if request.is_navigation_request():
            try:
                allowed=login_navigation_allowed(request.url,request.frame.parent_frame is None)
            except (ValueError,AttributeError):
                allowed=False
            if not allowed:
                if self.on_blocked is not None:
                    self.on_blocked(request)
                await route.abort()
                return
        await route.continue_()

    async def get_page(self):
        async with self.lock:
            if self.context is not None:
                if self.page is None or self.page.is_closed():
                    self.page=await self.context.new_page()
                    self.page.set_default_timeout(12000)
                return self.context,self.page
            # Завершаем оставшийся транспорт после неожиданного закрытия Chromium.
            await self._shutdown()
            try:
                self._acquire_profile()
            except BlockingIOError:
                raise DialogueUnavailable('Постоянный профиль уже используется другим процессом. Второй браузер не запущен; файлы блокировки не удаляются.') from None
            try:
                from playwright.async_api import async_playwright
                self.pw=await async_playwright().start()
                self.context=await self.pw.chromium.launch_persistent_context(
                    str(self.directory),**opensooq_browser_launch_options(),
                    viewport={'width':420,'height':820},locale='en-US',
                    accept_downloads=False,timeout=25000)
                self.context.on('close',self._context_closed)
                await self.context.route('**/*',self._restrict_navigation)
                pages=[page for page in self.context.pages if not page.is_closed()]
                self.page=pages[0] if pages else await self.context.new_page()
                self.page.set_default_timeout(12000)
                return self.context,self.page
            except asyncio.CancelledError:
                await self._shutdown()
                raise
            except Exception:
                await self._shutdown()
                raise DialogueUnavailable('Не удалось открыть постоянный браузер. Проверьте Chromium, память, доступ на запись в DATA_DIR и отсутствие второго процесса с тем же профилем.') from None

    async def _shutdown(self):
        context,pw=self.context,self.pw
        self.context=self.page=self.pw=None
        try:
            if context is not None:
                with suppress(Exception):
                    await asyncio.wait_for(context.close(),timeout=10)
        finally:
            try:
                if pw is not None:
                    with suppress(Exception):
                        await asyncio.wait_for(pw.stop(),timeout=10)
            finally:
                self._release_profile()

    async def close(self):
        async with self.lock:
            await self._shutdown()


def write_account_metadata(metadata):
    """Атомарный файл разрешения на автоответы; для постоянного режима без cookie."""
    DATA_DIR.mkdir(parents=True,exist_ok=True)
    path=DATA_DIR/'opensooq-chat.json'
    fd,temporary=tempfile.mkstemp(prefix='.opensooq-',suffix='.json',dir=DATA_DIR)
    try:
        os.fchmod(fd,0o600)
        with os.fdopen(fd,'w',encoding='utf-8') as stream:
            json.dump(metadata,stream)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary,path)
    finally:
        with suppress(FileNotFoundError):
            os.unlink(temporary)
    return path


def pause_account_automation(dialogs):
    """Вызывать под dialogs.lock: новый ручной вход требует нового Save."""
    dialogs.transport.disabled=True
    dialogs.transport.saved_enabled=False
    with dialogs.db:
        dialogs.db.execute("UPDATE seller_dialogues SET state='paused',note='Ручное управление аккаунтом; продолжение только после подтверждения владельца' WHERE chat=? AND state IN ('queued','waiting','sending','approved')",(ADMIN_ID,))
    metadata={}
    path=DATA_DIR/'opensooq-chat.json'
    if path.is_file():
        with suppress(ValueError,OSError,TypeError):
            value=json.loads(path.read_text(encoding='utf-8'))
            if isinstance(value,dict):
                metadata=value
    metadata['_opensooq_chat_enabled']=False
    write_account_metadata(metadata)


async def disconnect_opensooq_account(service):
    dialogs=service.dialogues
    dialogs.cancelled.update(row['id'] for row in dialogs.db.execute(
        'SELECT id FROM seller_dialogues WHERE chat=?',(ADMIN_ID,)))
    await service.account_login.close()
    async with dialogs.lock:
        try:
            # Сначала запрещаем автоответы на диске, затем закрываем браузер.
            pause_account_automation(dialogs)
        finally:
            await dialogs.transport.close()
            await service.account_browser.close()



class OpenSooqChatBrowser:
    """Обычный интерфейс сайта. Секрет сессии создаёт владелец вне чата Telegram."""
    def __init__(self, profile=None):
        self.pw = self.browser = self.context = self.page = None
        self.account = os.getenv('OPENSOOQ_CHAT_ACCOUNT_ID', '').strip()
        self.state_file = Path(os.getenv('OPENSOOQ_CHAT_STATE_FILE', '/etc/secrets/opensooq-chat.json'))
        self.profile=profile
        self.profile_mode=False
        self._using_profile=False
        self.saved_enabled=False
        self.disabled=False
        local=DATA_DIR/'opensooq-chat.json'
        if local.is_file():
            with suppress(ValueError,OSError,TypeError):
                meta=json.loads(local.read_text(encoding='utf-8'))
                self.state_file=local
                self.account=str(meta.get('_opensooq_account_id',''))
                self.saved_enabled=meta.get('_opensooq_chat_enabled') is True
                self.disabled=meta.get('_opensooq_chat_enabled') is False
                self.profile_mode=meta.get('_opensooq_profile_mode')=='persistent'
        self.blocked = False
        self.guard = lambda: True

    def configured(self):
        enabled=self.saved_enabled or os.getenv('OPENSOOQ_CHAT_ENABLED','0')=='1'
        if self.profile_mode:
            enabled=self.saved_enabled and self.profile is not None and self.profile.directory.is_dir()
        return (not self.disabled and enabled and self.state_file.is_file() and self.account.isdecimal())

    async def ready(self):
        if self.blocked:
            raise DialogueUnavailable('Чат остановлен после проверки доступа сайта. Нужен ручной вход.')
        if not self.configured():
            raise DialogueUnavailable('Аккаунт ещё не подключён. Откройте /account и войдите с телефона через личную страницу.')
        if self.page is not None and not self.page.is_closed():
            return
        if self.profile_mode:
            metadata=json.loads(self.state_file.read_text(encoding='utf-8'))
            if (metadata.get('_opensooq_account_id')!=self.account
                    or metadata.get('_opensooq_chat_enabled') is not True
                    or metadata.get('_opensooq_profile_mode')!='persistent'):
                raise DialogueUnavailable('Разрешение или привязка профиля изменились. Подтвердите вход через /account.')
            self.context,self.page=await self.profile.get_page()
            self._using_profile=True
            return
        from playwright.async_api import async_playwright
        self.pw = await async_playwright().start()
        try:
            self.browser = await self.pw.chromium.launch(**opensooq_browser_launch_options())
            state = json.loads(self.state_file.read_text(encoding='utf-8'))
            if state.get('_opensooq_account_id') != self.account:
                raise DialogueUnavailable('Файл сессии не привязан к указанному аккаунту. Создайте его через --chat-login.')
            state = {key:state[key] for key in ('cookies','origins') if key in state}
            self.context = await self.browser.new_context(storage_state=state, locale='en-US')
            self.page = await self.context.new_page()
            self.page.set_default_timeout(12000)
        except Exception:
            await self.close()
            raise DialogueUnavailable('Не удалось запустить браузер переписки. Проверьте файл сессии и установку Chromium.') from None

    async def goto(self, url):
        await self.ready()
        parsed = urlsplit(url)
        if parsed.scheme != 'https' or parsed.hostname not in HOSTS | {'my.opensooq.com'}:
            raise DialogueUnavailable('Некорректный адрес диалога.')
        await self.page.goto(url, wait_until='domcontentloaded', timeout=30000)
        title = await self.page.title()
        if re.search(r'just a moment|access denied|access restricted|verify.*human', title, re.I):
            self.blocked = True
            raise DialogueUnavailable('OpenSooq показал проверку доступа. Автоматическая переписка остановлена.')
        if urlsplit(self.page.url).hostname not in HOSTS | {'my.opensooq.com'}:
            raise DialogueUnavailable('OpenSooq перенаправил на вход. Обновите сессию вручную.')

    async def room(self, url, ad):
        parsed = urlsplit(url)
        query = dict(parse_qsl(parsed.query))
        match = re.fullmatch(r'(\d+)-(\d+)-(\d+)', query.get('selectedRoom', ''))
        if (parsed.hostname != 'my.opensooq.com' or parsed.path != '/chats'
                or not match or match[1] != str(ad['id']) or match[3] != self.account
                or (str(ad.get('seller_id') or '').isdecimal() and match[2] != str(ad['seller_id']))):
            raise DialogueUnavailable('Диалог не совпадает с объявлением, продавцом или подключённым аккаунтом.')
        await self.goto(url)
        textarea = self.page.get_by_placeholder('Message Text...', exact=True)
        await textarea.wait_for(state='visible')
        # Проверяем ссылку объявления именно в заголовке открытого диалога.
        header_links = self.page.locator('main a[href*="/search/"]')
        links = await header_links.evaluate_all('(els) => els.map(el => el.href)')
        if not any(urlsplit(h).path.rstrip('/').endswith('/search/' + str(ad['id'])) for h in links):
            raise DialogueUnavailable('Не удалось подтвердить товар в заголовке чата.')
        return self.page.url

    async def locate(self, ad):
        await self.goto('https://my.opensooq.com/chats')
        search = self.page.get_by_role('textbox', name='Search', exact=True)
        await search.wait_for(state='visible')
        await self.page.locator('li').first.wait_for(state='visible')
        if not ad.get('seller_name') or not ad.get('title'):
            raise DialogueUnavailable('Для начала диалога нужны имя продавца и заголовок товара.')
        await search.fill(ad['seller_name'])
        rows = self.page.locator('li').filter(has_text=ad['seller_name']).filter(has_text=ad['title'])
        # Поиск списка асинхронный; ждём стабилизации списка, а не повторяем отправку.
        await asyncio.sleep(1)
        count_rows = await rows.count()
        if count_rows > 1:
            raise DialogueUnavailable('Найдено несколько похожих чатов. Нужна ручная проверка получателя.')
        if count_rows == 0:
            return ''
        await rows.click()
        await self.page.get_by_placeholder('Message Text...', exact=True).wait_for(state='visible')
        return await self.room(self.page.url, ad)

    async def messages(self):
        rows = await self.page.locator('[id^="msg-"]').evaluate_all('''els => els.map(el => ({
            id: el.id, classes: el.className,
            text: Array.from(el.querySelectorAll('p')).map(p => p.innerText).join('\\n')
        }))''')
        messages = []
        for item in rows:
            match = re.fullmatch(r'msg-(\d+)', item['id'])
            classes = str(item['classes']).split()
            if not match:
                continue
            direction = 'out' if 'tw-justify-end' in classes else 'in' if 'tw-justify-start' in classes else 'unknown'
            messages.append({'id': int(match[1]), 'direction': direction, 'text': item['text'].strip()})
        return sorted(messages, key=lambda m: m['id'])

    async def send(self, text, after):
        # Только заранее заданные вопросы; произвольный текст продавца не исполняется.
        if text not in DIALOG_QUESTIONS:
            raise DialogueUnavailable('Вопрос отсутствует в согласованном сценарии.')
        box = self.page.get_by_placeholder('Message Text...', exact=True)
        await box.fill(text)
        send = self.page.locator('button').filter(has=self.page.locator('svg[data-icon="paper-plane"]'))
        if await send.count() != 1:
            raise DialogueUnavailable('Не удалось однозначно найти кнопку отправки.')
        if not self.guard():
            raise DialogueUnavailable('Диалог остановлен владельцем.')
        await send.click()
        for _ in range(4):
            for message in await self.messages():
                if message['id'] > after and message['direction'] == 'out' and message['text'] == text:
                    return message['id']
            await asyncio.sleep(.5)
        raise DialogueUnavailable('Результат отправки пока неизвестен. Повторная отправка автоматически не выполняется.')

    async def first(self, ad):
        await self.goto(ad['url'])
        if urlsplit(self.page.url).path.rstrip('/') != urlsplit(ad['url']).path.rstrip('/'):
            raise DialogueUnavailable('Объявление перенаправило на другую страницу.')
        # Проверяем продавца по точной ссылке профиля из карточки парсера.
        profiles = await self.page.locator('a[href*="/mid/"]').evaluate_all('(els) => els.map(el => el.href)')
        expected = urlsplit(safe_url(ad['seller_url'], ad['url']))
        if not any(urlsplit(u).hostname == expected.hostname and unquote(urlsplit(u).path).rstrip('/') == unquote(expected.path).rstrip('/') for u in profiles):
            raise DialogueUnavailable('Профиль продавца в объявлении изменился. Отправка остановлена.')
        box = self.page.get_by_placeholder('Message...', exact=True)
        await box.wait_for(state='visible')
        await box.fill(DIALOG_QUESTIONS[0])
        if not self.guard():
            raise DialogueUnavailable('Диалог остановлен владельцем.')
        await self.page.get_by_role('button', name='Send Message', exact=True).click()
        for _ in range(30):
            if not await box.input_value():
                break
            await asyncio.sleep(.5)
        else:
            raise DialogueUnavailable('Форма не подтвердила первую отправку. Проверьте историю вручную, автоматического повтора нет.')
        room_url = await self.locate(ad)
        if not room_url:
            raise DialogueUnavailable('Первая отправка не подтверждена в истории. Нужна ручная проверка; повтор запрещён.')
        messages = await self.messages()
        outgoing = [m for m in messages if m['direction'] == 'out' and m['text'] == DIALOG_QUESTIONS[0]]
        if not outgoing:
            raise DialogueUnavailable('Первая отправка не подтверждена. Проверьте чат вручную.')
        return room_url, outgoing[-1]['id']

    async def close(self):
        if self._using_profile:
            self.pw=self.browser=self.context=self.page=None
            self._using_profile=False
            return
        if self.context is not None:
            with suppress(Exception):
                await self.context.close()
        if self.browser is not None:
            with suppress(Exception):
                await self.browser.close()
        if self.pw is not None:
            with suppress(Exception):
                await self.pw.stop()
        self.pw = self.browser = self.context = self.page = None


class SellerDialogues:
    def __init__(self, service):
        self.service, self.db = service, service.db
        self.transport = OpenSooqChatBrowser(getattr(service,'account_browser',None))
        self.lock = asyncio.Lock()
        self.cancelled = set()
        self.db.executescript('''
            CREATE TABLE IF NOT EXISTS dialogue_ads(
                token TEXT PRIMARY KEY, chat INTEGER NOT NULL, ad_key TEXT NOT NULL,
                seller TEXT NOT NULL, data TEXT NOT NULL, UNIQUE(chat,ad_key));
            CREATE TABLE IF NOT EXISTS dialogue_events(
                dialogue TEXT NOT NULL, message_id INTEGER NOT NULL, direction TEXT NOT NULL,
                text TEXT NOT NULL, observed REAL NOT NULL, PRIMARY KEY(dialogue,message_id));
            CREATE TABLE IF NOT EXISTS seller_dialogues(
                id TEXT PRIMARY KEY, chat INTEGER NOT NULL, seller TEXT NOT NULL UNIQUE,
                ad TEXT NOT NULL, room TEXT NOT NULL DEFAULT '', state TEXT NOT NULL DEFAULT 'queued',
                stage INTEGER NOT NULL DEFAULT -1, cursor INTEGER NOT NULL DEFAULT 0,
                answered TEXT NOT NULL DEFAULT '[]', pending_stage INTEGER, pending_text TEXT NOT NULL DEFAULT '',
                pending_after INTEGER NOT NULL DEFAULT 0, updated REAL NOT NULL, note TEXT NOT NULL DEFAULT '');
        ''')
        self.db.commit()

    def register(self, chat, ad):
        if chat != ADMIN_ID:
            return ''
        seller = next(iter(seller_keys(ad)), '')
        if not seller or not ad.get('seller_url') or not ad.get('seller_name'):
            return ''
        key = urlsplit(ad['url']).hostname + ':' + str(ad['id'])
        with self.db:
            self.db.execute('INSERT OR IGNORE INTO dialogue_ads VALUES (?,?,?,?,?)',
                (secrets.token_hex(8), chat, key, seller, json.dumps(ad, ensure_ascii=False)))
        return self.db.execute('SELECT token FROM dialogue_ads WHERE chat=? AND ad_key=?', (chat,key)).fetchone()['token']

    def row(self, token):
        row = self.db.execute('SELECT * FROM seller_dialogues WHERE id=? AND chat=?', (token,ADMIN_ID)).fetchone()
        if row is None:
            raise ValueError('Диалог не найден.')
        return dict(row)

    def start(self, token):
        ad = self.db.execute('SELECT * FROM dialogue_ads WHERE token=? AND chat=?', (token,ADMIN_ID)).fetchone()
        if ad is None:
            raise ValueError('Карточка не найдена. Откройте /dialogs.')
        existing = self.db.execute('SELECT id FROM seller_dialogues WHERE seller=?', (ad['seller'],)).fetchone()
        if existing:
            return existing['id']
        if not self.transport.configured():
            raise DialogueUnavailable('Для переписки подключите аккаунт: /account. Вход в браузере ChatGPT не подключает Render автоматически.')
        with self.db:
            self.db.execute('INSERT INTO seller_dialogues(id,chat,seller,ad,updated) VALUES (?,?,?,?,?)',
                (token, ADMIN_ID, ad['seller'], ad['data'], time.time()))
        return token

    def save(self, token, **values):
        permitted = {'room','state','stage','cursor','answered','pending_stage','pending_text','pending_after','note'}
        if not values or not values.keys() <= permitted:
            raise ValueError('Некорректное состояние диалога.')
        if 'answered' in values:
            values['answered'] = json.dumps(sorted(set(values['answered'])))
        values['updated'] = time.time()
        with self.db:
            self.db.execute('UPDATE seller_dialogues SET '+','.join(k+'=?' for k in values)+' WHERE id=? AND chat=?',
                list(values.values())+[token,ADMIN_ID])

    async def notify(self, row, text):
        ad = json.loads(row['ad'])
        markup = ui_keyboard([[('⏸ Остановить диалог','talk:pause:'+row['id']), ('📋 Статус','talk:status:'+row['id'])]])
        with suppress(TelegramError):
            await self.service.bot.send_message(chat_id=ADMIN_ID,
                text=('💬 '+ad.get('seller_name','Продавец')+' · '+ad.get('title','Товар')+'\n\n'+text)[:3900], reply_markup=markup)

    def record(self, token, messages):
        with self.db:
            self.db.executemany('INSERT OR IGNORE INTO dialogue_events VALUES (?,?,?,?,?)',
                [(token,m['id'],m['direction'],m['text'][:3000],time.time()) for m in messages])

    async def update(self, row):
        token, ad = row['id'], json.loads(row['ad'])
        if row['state'] == 'queued':
            room = await self.transport.locate(ad)
            if room:
                messages = await self.transport.messages()
                self.record(token,messages)
                outgoing = [m for m in messages if m['direction']=='out']
                if len(outgoing) == 1 and outgoing[0]['text'] == DIALOG_QUESTIONS[0]:
                    self.save(token, room=room,state='waiting',stage=0,cursor=outgoing[0]['id'])
                    await self.notify(row, 'Найден уже начатый диалог. Первое сообщение повторно не отправлено.')
                elif not messages:
                    self.save(token,room=room,state='sending',pending_stage=0,pending_text=DIALOG_QUESTIONS[0],pending_after=0)
                    message_id = await self.transport.send(DIALOG_QUESTIONS[0],0)
                    self.save(token,state='waiting',stage=0,cursor=message_id,pending_text='',pending_stage=None)
                else:
                    self.save(token,room=room,state='review',note='В чате есть более ранняя переписка. Нужна ручная проверка.')
                    await self.notify(row, 'Уже есть переписка. Автоматический сценарий не запущен, чтобы не вмешиваться в разговор.')
            else:
                # Фиксируем попытку ДО внешнего действия. После сбоя не повторяем её.
                self.save(token,state='sending',pending_stage=0,pending_text=DIALOG_QUESTIONS[0],pending_after=0)
                room, message_id = await self.transport.first(ad)
                self.save(token,room=room,state='waiting',stage=0,cursor=message_id,pending_text='',pending_stage=None)
                await self.notify(row,'Отправлено: '+DIALOG_QUESTIONS[0])
            return
        if not row['room']:
            self.save(token,state='review',note='Результат первой отправки неизвестен. Проверьте сайт вручную.')
            await self.notify(row,'Нужна ручная проверка первой отправки. Автоматического повтора нет.')
            return
        await self.transport.room(row['room'],ad)
        messages = await self.transport.messages()
        self.record(token,messages)
        if row['state'] == 'approved':
            if any(m['id']>row['pending_after'] for m in messages):
                self.save(token,state='review',cursor=max(m['id'] for m in messages),pending_text='',pending_stage=None,note='После подтверждения пришло новое сообщение. Откройте чат перед ответом.')
                await self.notify(row,'Подтверждённый вопрос не отправлен: в диалоге появились новые сообщения.')
                return
            self.save(token,state='sending')
            message_id = await self.transport.send(row['pending_text'],row['pending_after'])
            self.save(token,state='waiting',stage=row['pending_stage'],cursor=message_id,pending_text='',pending_stage=None)
            await self.notify(row,'Отправлено после вашего подтверждения: '+DIALOG_QUESTIONS[row['pending_stage']])
            return
        if row['state'] == 'sending':
            sent = [m for m in messages if m['direction']=='out' and m['id']>row['pending_after'] and m['text']==row['pending_text']]
            if sent:
                self.save(token,state='waiting',stage=row['pending_stage'],cursor=sent[-1]['id'],pending_text='',pending_stage=None)
                await self.notify(row,'Отправка подтверждена по истории чата. Вопрос не дублировался.')
            else:
                self.save(token,state='review',note='Не удалось подтвердить предыдущую отправку. Повтор автоматически не выполняется.')
                await self.notify(row,'Не удалось подтвердить отправку. Проверьте чат вручную; вопрос повторно не отправлен.')
            return
        fresh = [m for m in messages if m['id']>row['cursor']]
        if not fresh:
            self.save(token,note='Ожидаем новый ответ продавца.')
            return
        if any(m['direction']!='in' for m in fresh):
            self.save(token,state='review',note='В чате появился ручной ответ или неизвестный тип сообщения.')
            await self.notify(row,'Автоматическая переписка приостановлена: ручной ответ или неизвестный тип сообщения.')
            return
        reply = '\n'.join(m['text'] for m in fresh)
        if not reply.strip():
            self.save(token,state='review',note='Ответ содержит вложение без распознанного текста.')
            await self.notify(row,'Продавец прислал вложение. Нужен ручной просмотр.')
            return
        decision, answered, next_stage = dialogue_answer(reply,row['stage'],json.loads(row['answered']))
        cursor = max(m['id'] for m in fresh)
        self.save(token,cursor=cursor,answered=answered)
        await self.notify(row,'Продавец: '+reply[:2200])
        if decision == 'wait':
            return
        if decision in {'stopped','review','complete'}:
            notes={'stopped':'Продавец сообщил о продаже или попросил остановиться.',
                   'review':'Неоднозначный ответ. Нужен ответ человека.', 'complete':'Все вопросы заданы. Сделка автоматически не заключается.'}
            self.save(token,state=decision,note=notes[decision])
            await self.notify(row,notes[decision])
            return
        question = DIALOG_QUESTIONS[next_stage]
        self.save(token,state='sending',pending_stage=next_stage,pending_text=question,pending_after=cursor,answered=answered)
        message_id = await self.transport.send(question,cursor)
        self.save(token,state='waiting',stage=next_stage,cursor=message_id,pending_text='',pending_stage=None)
        await self.notify(row,'Отправлено: '+question)

    async def poll(self, context):
        await self.service.account_login.expire()
        if self.service.account_login.active:
            return
        if self.service.closing or self.lock.locked() or not self.transport.configured():
            return
        async with self.lock:
            rows = list(self.db.execute("SELECT * FROM seller_dialogues WHERE chat=? AND state IN ('queued','waiting','sending','approved') ORDER BY updated LIMIT 5",(ADMIN_ID,)))
            for db_row in rows:
                row = dict(db_row)
                self.transport.guard = lambda token=row['id']: token not in self.cancelled and not self.service.closing and not self.service.account_login.active
                try:
                    await self.update(row)
                except Exception as exc:
                    # Не выводим URL сессии/содержимое storage_state в логи.
                    log.warning('[seller_dialogue] id=%s type=%s',row['id'],type(exc).__name__)
                    if row['id'] in self.cancelled:
                        self.save(row['id'],state='paused',note='Остановлен владельцем.')
                        continue
                    self.save(row['id'],state='review',note='Проверка или отправка не завершена. Нужен ручной просмотр.')
                    await self.notify(row,'Переписка приостановлена: '+(str(exc)[:500] if isinstance(exc,DialogueUnavailable) else 'сайт не ответил или изменился интерфейс. Проверьте диалог вручную.'))

    async def close(self):
        async with self.lock:
            await self.transport.close()


async def dialogue_panel(update, context, token=''):
    if update.effective_user.id != ADMIN_ID:
        raise ValueError('Переписка с личного аккаунта доступна только владельцу.')
    dialogs = context.application.bot_data['service'].dialogues
    if token:
        row = dialogs.row(token)
        ad = json.loads(row['ad'])
        statuses={'queued':'в очереди','waiting':'ожидаем ответ','sending':'проверяем отправку','approved':'вопрос подтверждён владельцем','paused':'остановлен владельцем','review':'нужна ручная проверка','stopped':'остановлен','complete':'вопросы завершены'}
        text = f"💬 <b>{escape(ad['seller_name'])}</b>\n{escape(ad['title'])}\n\nСостояние: {statuses.get(row['state'],row['state'])}\n"
        if row['stage']>=0:
            text += '\nПоследний вопрос: '+escape(DIALOG_QUESTIONS[row['stage']])+'\n'
        text += '\n'+escape(row['note'])
        rows = [[('⏸ Остановить','talk:pause:'+token)]]
        if row['state']=='review' and row['stage']==-1 and not row['pending_text']:
            rows.append([('Повторить подключение без отправки','talk:retry:'+token)])
        if row['state'] in {'review','paused'} and row['room'] and 0 <= row['stage'] < len(DIALOG_QUESTIONS)-1 and not row['pending_text']:
            rows.append([('Следующий вопрос с подтверждением', 'talk:next:'+token)])
        keyboard = ui_keyboard(rows+[[('‹ Диалоги','talk:list')]])
        if row['room']:
            keyboard = InlineKeyboardMarkup(list(keyboard.inline_keyboard)+[[InlineKeyboardButton('✍️ Открыть чат',url=row['room'])]])
    else:
        rows = list(dialogs.db.execute('SELECT id,ad,state FROM seller_dialogues WHERE chat=? ORDER BY updated DESC LIMIT 20',(ADMIN_ID,)))
        text = '💬 <b>Диалоги с продавцами</b>\n\nЗапуск — кнопкой у выбранного объявления. Один продавец — один диалог. Неясный ответ передаётся владельцу.\n\n'
        text += 'Аккаунт на Render: '+('настройки заданы; вход проверяется при запуске диалога.' if dialogs.transport.configured() else 'не подключён. /chatstatus')
        keyboard = ui_keyboard([[(json.loads(r['ad'])['seller_name']+' · '+r['state'],'talk:status:'+r['id'])] for r in rows]+[[('⏸ Остановить все','talk:pause_all')],[('‹ Главное меню','menu_home')]])
    await show_panel(update,text,keyboard)


async def dialogue_callback(update, context):
    query, user, chat = update.callback_query, update.effective_user, update.effective_chat
    if not user or user.id != ADMIN_ID or not chat or chat.type != 'private':
        await query.answer('Переписка с личного аккаунта доступна только владельцу.',show_alert=True)
        return
    await query.answer()
    dialogs = context.application.bot_data['service'].dialogues
    parts = (query.data or '').split(':')
    try:
        if parts[1] == 'start' and len(parts)==3:
            async with dialogs.lock:
                token = dialogs.start(parts[2])
            await dialogue_panel(update,context,token)
        elif parts[1]=='next' and len(parts)==3:
            row = dialogs.row(parts[2])
            if row['state'] not in {'review','paused'} or row['pending_text'] or not row['room'] or not 0 <= row['stage'] < len(DIALOG_QUESTIONS)-1:
                raise ValueError('Сначала проверьте историю чата. Неизвестную отправку повторять нельзя.')
            stage = row['stage']+1
            await show_panel(update,'Отправить следующий вопрос после вашего просмотра переписки?\n\n'+escape(DIALOG_QUESTIONS[stage]),
                ui_keyboard([[('Да, отправить',f"talk:approve:{row['id']}:{stage}:{row['cursor']}")],[('Отмена','talk:status:'+row['id'])]]))
        elif parts[1]=='approve' and len(parts)==5:
            async with dialogs.lock:
                row=dialogs.row(parts[2])
                stage,cursor=int(parts[3]),int(parts[4])
                if row['state'] not in {'review','paused'} or row['pending_text'] or not row['room'] or stage!=row['stage']+1 or cursor!=row['cursor'] or not 0<=stage<len(DIALOG_QUESTIONS):
                    raise ValueError('Подтверждение устарело. Откройте статус диалога.')
                dialogs.cancelled.discard(row['id'])
                dialogs.save(row['id'],state='approved',pending_stage=stage,pending_text=DIALOG_QUESTIONS[stage],pending_after=cursor)
            await dialogue_panel(update,context,row['id'])
        elif parts[1]=='pause' and len(parts)==3:
            dialogs.row(parts[2])
            dialogs.cancelled.add(parts[2])
            async with dialogs.lock:
                dialogs.row(parts[2])
                dialogs.save(parts[2],state='paused',note='Остановлен владельцем. Автоответы отключены.')
            await dialogue_panel(update,context,parts[2])
        elif parts[1]=='pause_all':
            dialogs.cancelled.update(r['id'] for r in dialogs.db.execute('SELECT id FROM seller_dialogues WHERE chat=?',(ADMIN_ID,)))
            async with dialogs.lock:
                with dialogs.db:
                    dialogs.db.execute("UPDATE seller_dialogues SET state='paused',note='Остановлен владельцем' WHERE chat=? AND state IN ('queued','waiting','sending','approved')",(ADMIN_ID,))
            await dialogue_panel(update,context)
        elif parts[1]=='status' and len(parts)==3:
            await dialogue_panel(update,context,parts[2])
        else:
            await dialogue_panel(update,context)
    except ValueError as exc:
        await query.message.reply_text(str(exc)[:1000])


async def local_chat_login():
    """Запускается владельцем на его компьютере, не в Telegram и не в ChatGPT."""
    from playwright.async_api import async_playwright
    target = Path(os.getenv('OPENSOOQ_CHAT_STATE_FILE','opensooq-chat.json')).expanduser()
    async with async_playwright() as pw:
        browser = await pw.chromium.launch(headless=False)
        context = await browser.new_context()
        page = await context.new_page()
        await page.goto('https://my.opensooq.com/chats',wait_until='domcontentloaded')
        print('Войдите в существующий аккаунт вручную в открывшемся браузере и откройте любой существующий диалог. Затем вернитесь сюда и нажмите Enter. Не присылайте файл сессии в чат и не добавляйте его в GitHub.')
        await asyncio.to_thread(input)
        if urlsplit(page.url).hostname != 'my.opensooq.com' or not await page.get_by_role('button',name='My Profile',exact=True).is_visible():
            await browser.close()
            raise SystemExit('Вход не подтверждён. Файл сессии не сохранён.')
        selected = dict(parse_qsl(urlsplit(page.url).query)).get('selectedRoom','')
        match = re.fullmatch(r'\d+-\d+-(\d+)',selected)
        if not match:
            await browser.close()
            raise SystemExit('Откройте любой существующий диалог перед нажатием Enter. Файл не сохранён: ID аккаунта не подтверждён.')
        target.parent.mkdir(parents=True,exist_ok=True)
        state = await context.storage_state()
        state['_opensooq_account_id'] = match[1]
        fd=os.open(target,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)
        os.fchmod(fd,0o600)
        with os.fdopen(fd,'w',encoding='utf-8') as file:
            json.dump(state,file)
        os.chmod(target,0o600)
        print('Сессия сохранена локально. На Render добавьте её как Secret File, не как файл репозитория.')
        print('OPENSOOQ_CHAT_ACCOUNT_ID='+match[1])
        await browser.close()



ACCOUNT_PAGE = r'''<!doctype html>
<html lang="ru"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Подключить OpenSooq</title>
<style>
body{margin:0;background:#10141e;color:#f7f7fb;font:16px system-ui}
main{max-width:480px;margin:auto;padding:14px}button,input{font:inherit;border-radius:10px;padding:12px;border:1px solid #506077}
button{background:#1264eb;color:white;margin:4px 2px}button:disabled{opacity:.5}
input{box-sizing:border-box;width:100%;background:#202a3b;color:white}
canvas{display:block;width:100%;max-width:420px;margin:auto;background:white;border-radius:8px}
#status{white-space:pre-wrap;font-size:14px}small{display:block;margin:12px 0;color:#c4ccdb}
</style>
<main><h2>Вход в OpenSooq</h2>
<p>Начните с кнопки «Вход / профиль»: она открывает главную OpenSooq и штатную форму Login or Sign Up. Завершите вход на экране ниже. После подтверждения входа откройте «Чаты», выберите существующий диалог и нажмите «Сохранить вход».</p>
<small>Личная ссылка даёт управление постоянным браузером. Закрытие страницы не удаляет его профиль; отключение бота: /account_off. Не пересылайте её. Пароль и код вводите здесь, не в Telegram. Сообщения об отправке команды не подтверждают вход в аккаунт.</small>
<button id="login">Вход / профиль</button><button id="chats">После входа: открыть чаты</button><button id="save">Сохранить вход</button>
<button id="close">Закрыть страницу входа</button>
<p id="status" role="status" aria-live="polite">Подключаем браузер…</p>
<canvas id="screen" width="420" height="820"></canvas>
<p>Нажмите нужное поле на экране. Введите его полное значение ниже и нажмите «Заменить поле». Предыдущее значение выбранного поля будет заменено.</p>
<input id="entry" type="password" autocomplete="off" autocapitalize="none" autocorrect="off" spellcheck="false" placeholder="Номер, пароль или код — для выбранного поля">
<button id="type">Заменить поле</button><button id="enter">Enter / Далее</button>
<button id="backspace">Удалить символ</button><button id="tab">Следующее поле</button>
<button id="up">↑</button><button id="down">↓</button><button id="refresh">Обновить экран</button>
<small>Страница действует 15 минут. При просьбе сайта подождать прекратите попытки. Расширенный отчёт v18 в боте: /account_diag. Он не содержит значений полей и не повторяет вход.</small></main>
<script>
'use strict';
const token=location.hash.slice(1);
history.replaceState(null,'','/account');
const status=document.querySelector('#status'),canvas=document.querySelector('#screen'),entry=document.querySelector('#entry');
let ended=false,shown=false,refreshing=false,actionPending=false,screenPromise=Promise.resolve();
function notice(s){status.textContent=s}
function controls(){
 document.querySelectorAll('button').forEach(b=>b.disabled=ended||actionPending);
 entry.disabled=ended||actionPending;
 canvas.style.pointerEvents=ended||actionPending?'none':'auto';
 canvas.setAttribute('aria-busy',String(actionPending));
}
function finish(){ended=true;entry.value='';canvas.getContext('2d').clearRect(0,0,canvas.width,canvas.height);controls()}
async function request(path,body){
 const controller=new AbortController(),timer=setTimeout(()=>controller.abort(),45000);
 try{
  const r=await fetch(path,{method:body?'POST':'GET',headers:{Authorization:'Bearer '+token,...(body?{'Content-Type':'application/json'}:{})},body:body?JSON.stringify(body):undefined,cache:'no-store',referrerPolicy:'no-referrer',signal:controller.signal});
  if(!r.ok){let m='Ошибка подключения';try{m=(await r.json()).error||m}catch{}if(r.status===401)finish();throw Error(m)}
  return r;
 }catch(e){
  if(e.name==='AbortError')throw Error('Сервер не ответил вовремя. Команда могла выполниться — сначала проверьте экран. Автоматического повтора нет.');
  throw e;
 }finally{clearTimeout(timer)}
}
async function shot(){
 if(ended||actionPending||refreshing)return;
 refreshing=true;
 screenPromise=(async()=>{
  let url;
  try{
   const r=await request('/account-api/screen'),blob=await r.blob();
   url=URL.createObjectURL(blob);const img=new Image();
   await new Promise((resolve,reject)=>{img.onload=resolve;img.onerror=reject;img.src=url});
   if(ended)return;
   canvas.width=img.naturalWidth;canvas.height=img.naturalHeight;canvas.getContext('2d').drawImage(img,0,0);
   if(!shown){if(!actionPending)notice('Браузер готов. Вход выполняете вы.');shown=true}
  }catch(e){notice(e.message)}finally{if(url)URL.revokeObjectURL(url);refreshing=false}
 })();
 await screenPromise;
}
async function act(body){
 if(ended||actionPending)return false;
 // Действие ожидает уже начатый снимок; снимок не отбрасывает нажатие.
 actionPending=true;controls();notice('Выполняю выбранное действие…');
 let ok=false;
 try{
  await screenPromise;
  if(ended)return false;
  const data=await(await request('/account-api/action',body)).json();
  ok=true;notice(data.message||'Действие выполнено. Проверьте результат на экране.');
  if(body.action==='text')entry.value='';
  if(data.finished)finish();
 }catch(e){notice(e.message)}finally{actionPending=false;controls()}
 if(!ended)await shot();
 return ok;
}
canvas.addEventListener('click',e=>{const r=canvas.getBoundingClientRect();act({action:'click',x:(e.clientX-r.left)*canvas.width/r.width,y:(e.clientY-r.top)*canvas.height/r.height})});
document.querySelector('#type').onclick=()=>{if(!ended&&!actionPending&&entry.value)act({action:'text',text:entry.value})};
for(const [id,key] of [['enter','Enter'],['backspace','Backspace'],['tab','Tab']])document.querySelector('#'+id).onclick=()=>act({action:'key',key});
document.querySelector('#up').onclick=()=>act({action:'scroll',dy:-500});document.querySelector('#down').onclick=()=>act({action:'scroll',dy:500});
document.querySelector('#refresh').onclick=()=>shot();
for(const id of ['login','chats','save','close'])document.querySelector('#'+id).onclick=()=>act({action:id});
if(!token){finish();notice('Ссылка без кода доступа. Получите новую через /account.')}else{shot();setInterval(shot,2500)}
</script></html>
'''


def login_navigation_allowed(url, top_frame):
    """Разрешаем штатные окна reCAPTCHA, не произвольные внешние страницы."""
    parsed=urlsplit(url)
    host=parsed.hostname or ''
    if parsed.scheme not in {'http','https'} or parsed.username or parsed.password:
        return False
    if host=='opensooq.com' or host.endswith('.opensooq.com'):
        return True
    return (not top_frame and parsed.scheme=='https'
            and host in {'www.google.com','recaptcha.google.com','www.recaptcha.net','recaptcha.net'}
            and parsed.port in {None,443} and parsed.path.startswith('/recaptcha/'))


def opensooq_browser_launch_options():
    """Use the same configured static proxy for OpenSooq login and chat.

    A proxy failure propagates to the caller; there is no direct retry/fallback.
    Telegram and billing clients keep their existing network configuration.
    """
    _, browser_proxy = proxy_settings(os.getenv('OPENSOOQ_PROXY_URL', ''))
    options = {'headless': True, 'args': ['--disable-dev-shm-usage']}
    if browser_proxy is not None:
        options['proxy'] = browser_proxy
    return options


def login_error_labels(document):
    """Return fixed labels only; never retain or render server-provided strings."""
    known = {
        'unauthorized': 'auth_unspecified',
        'unauthenticated': 'auth_unspecified',
        'authentication failed': 'auth_unspecified',
        'invalid credentials': 'credentials_rejected',
        'invalid login credentials': 'credentials_rejected',
        'incorrect credentials': 'credentials_rejected',
        'invalid password': 'password_rejected',
        'incorrect password': 'password_rejected',
        'wrong password': 'password_rejected',
        'captcha verification failed': 'captcha_rejected',
        'recaptcha verification failed': 'captcha_rejected',
        'invalid captcha': 'captcha_rejected',
        'invalid recaptcha': 'captcha_rejected',
        'captcha failed': 'captcha_rejected',
        'captcha validation failed': 'captcha_rejected',
        'recaptcha validation failed': 'captcha_rejected',
        'too many requests': 'wait',
        'too many attempts': 'wait',
        'too many login attempts': 'wait',
        'rate limit exceeded': 'wait',
        'please wait before trying again': 'wait',
        'please wait before trying again or contact us': 'wait',
        'session expired': 'session_rejected',
        'invalid session': 'session_rejected',
        'csrf token mismatch': 'session_rejected',
        'invalid csrf token': 'session_rejected',
        'csrf verification failed': 'session_rejected',
        'invalid otp': 'otp_rejected',
        'incorrect otp': 'otp_rejected',
        'otp expired': 'otp_rejected',
        'invalid verification code': 'otp_rejected',
        'bad request': 'request_rejected',
        'validation error': 'request_rejected',
        'validation failed': 'request_rejected',
        'access denied': 'access_rejected',
        'access restricted': 'access_rejected',
        'account blocked': 'account_rejected',
        'account suspended': 'account_rejected',
        'account disabled': 'account_rejected',
    }
    # Some API error codes join words with underscores/hyphens or camelCase.
    # Match an entire known code. Do not infer reasons from arbitrary substrings.
    compact = {re.sub(r'[^a-z]', '', key): value for key, value in known.items()}
    permitted = {'error', 'errors', 'message', 'messages', 'detail', 'details',
                 'description', 'code', 'errorcode', 'errormessage', 'reason', 'data'}
    stack = [(document, 0)]
    result = set()
    visited = 0
    while stack and visited < 80:
        value, depth = stack.pop()
        visited += 1
        if isinstance(value, str):
            if not 0 < len(value) <= 180:
                continue
            text = value.casefold().strip().rstrip('.!')
            normalized = re.sub(r'[_\-\s]+', ' ', text)
            label = known.get(normalized)
            if label is None and re.fullmatch(r'[a-zA-Z_\-]+', value):
                label = compact.get(re.sub(r'[^a-z]', '', text))
            if label:
                result.add(label)
        elif depth < 5 and isinstance(value, dict):
            for key, child in list(value.items())[:30]:
                if isinstance(key, str) and re.sub(r'[_\-]', '', key.casefold()) in permitted:
                    stack.append((child, depth + 1))
        elif depth < 5 and isinstance(value, list):
            stack.extend((child, depth + 1) for child in value[:20])
    return result


def login_blocked_destination(url):
    """Classify a destination without persisting its hostname, path or query."""
    try:
        parsed = urlsplit(url)
        host = parsed.hostname or ''
    except ValueError:
        return 'некорректный адрес'
    if host in {'www.google.com', 'recaptcha.google.com', 'www.recaptcha.net', 'recaptcha.net'}:
        return 'Google / reCAPTCHA'
    if host == 'gstatic.com' or host.endswith('.gstatic.com'):
        return 'Google static'
    if any(host == base or host.endswith('.' + base) for base in
           ('doubleclick.net', 'googlesyndication.com', 'googleadservices.com')):
        return 'рекламный домен'
    if host == 'opensooq.com' or host.endswith('.opensooq.com'):
        return 'OpenSooq'
    return 'другой внешний адрес'


LOGIN_ERROR_LABELS = {
    'auth_unspecified': 'отказ авторизации без уточнения причины',
    'credentials_rejected': 'сервис сообщил: данные входа отклонены',
    'password_rejected': 'сервис сообщил: пароль отклонён',
    'captcha_rejected': 'сервис сообщил: проверка CAPTCHA отклонена',
    'wait': 'сервис просит подождать',
    'session_rejected': 'сервис сообщил: ошибка сессии или CSRF',
    'otp_rejected': 'сервис сообщил: код подтверждения отклонён или истёк',
    'request_rejected': 'запрос отклонён без конкретной причины',
    'access_rejected': 'сервис ограничил доступ; основание не указано',
    'account_rejected': 'сервис сообщил об ограничении аккаунта',
}


class AccountLogin:
    def __init__(self, service):
        self.service=service
        self.token=''
        self.expires=0
        self.active=False
        self.lock=asyncio.Lock()
        self.pw=self.browser=self.context=self.page=None
        self.country='sa'
        self.diag_flags=set()
        self.diag_http=Counter()
        self.diag_failures=Counter()
        self.diag_exists=False
        self.last_diag_check=0.0
        self.diag_routes={}
        self.diag_salt=secrets.token_hex(16)
        self.diag_pending={}
        self.diag_events=[]
        self.diag_blocked=0
        self.diag_action=0
        self.diag_action_label='открытие страницы'
        self._observed_page=None
        self.diag_error_details=[]
        self.diag_inspect_tasks=set()
        self.diag_inspected=0
        self.diag_generation=0
        self.diag_blocked_kinds=Counter()
        self._account_entry_pending=False

    def diagnostic_text(self):
        if not self.diag_exists:
            return 'Диагностика пуста. /account_diag не открывает сайт и не повторяет вход. Старые попытки этой версией не наблюдались.'
        lines=['Диагностика входа v18',
               'Страна: '+COUNTRY_LABELS.get(self.country,self.country),
               'Доступ к странице: '+('активен' if self.active and time.monotonic()<self.expires else 'закрыт или истёк'),
               'Браузер входа: постоянный профиль. '+('Настроен общий прокси OPENSOOQ_PROXY_URL; прямого повтора при его ошибке нет.' if self.service.reader.browser_proxy is not None else 'Прямое соединение: OPENSOOQ_PROXY_URL не задан.')]
        flags={'captcha_failed':'На странице: reCAPTCHA verification failed.',
               'unauthorized':'На странице: Unauthorized. Точная причина не раскрыта.',
               'wait':'Сайт просит подождать перед повторным входом.',
               'browser_error':'Не удалось открыть браузер входа.'}
        lines.extend(flags[k] for k in sorted(self.diag_flags) if k in flags)
        if self.diag_events:
            lines.append('Последние запросы авторизации и ошибки:')
            for action, label, route, group, method, resource, result in self.diag_events[-4:]:
                lines.append(f'Действие {action} ({label}): {method} / {resource} / {group} / маршрут {route} → {result}')
            lines.append('Группа маршрута определяется по его названию. HTTP 200 сам по себе не подтверждает вход; чужой HTTP 401 не доказывает отказ входа.')
        else:
            lines.append('Запросов авторизации или ошибок пока не зафиксировано.')
        if self.diag_error_details:
            lines.append('Разбор уже полученных ошибок (без новых запросов):')
            for action, route, status, description in self.diag_error_details:
                lines.append(f'Действие {action}, маршрут {route}, HTTP {status}: {description}.')
            lines.append('Это сообщение сервиса, а не независимая проверка пароля или CAPTCHA. Если причина не раскрыта, она остаётся неизвестной.')
        if self.diag_blocked:
            lines.append(f'Ограничитель нашей страницы запретил переходов: {self.diag_blocked}.')
        for (frame_kind,destination),amount in sorted(self.diag_blocked_kinds.items()):
            lines.append(f'Запрещено: {frame_kind} / {destination} × {amount}')
        for (provider,status),amount in sorted(self.diag_http.items()):
            lines.append(f'{provider}: HTTP {status} × {amount}')
        for (provider,reason),amount in sorted(self.diag_failures.items()):
            lines.append(f'{provider}: {reason} × {amount}')
        lines.append('JSON-ошибки входа распознаются в памяти по списку известных сообщений. В отчёте только готовые категории; исходный текст ответа, значения полей, заголовки, cookie и URL не сохраняются. Действие у запроса означает время его начала, не доказанную причину. Новый /account очищает отчёт.')
        return '\n'.join(lines)[:3900]

    @staticmethod
    def diagnostic_provider(url):
        try:
            parsed=urlsplit(url)
            host=parsed.hostname or ''
        except ValueError:
            return ''
        if host=='opensooq.com' or host.endswith('.opensooq.com'):
            return 'OpenSooq'
        if host in {'www.google.com','recaptcha.google.com','www.recaptcha.net','recaptcha.net','www.gstatic.com'} and parsed.path.startswith('/recaptcha/'):
            return 'reCAPTCHA'
        return ''

    def request_metadata(self, request):
        provider=self.diagnostic_provider(request.url)
        if not provider:
            return None
        parsed=urlsplit(request.url)
        # Соль и хеш нужны только для сопоставления одного маршрута в памяти.
        # Телефон, query, исходный путь и URL в журнал не попадают.
        identity=hashlib.sha256((self.diag_salt+'|'+str(parsed.hostname)+'|'+parsed.path).encode()).hexdigest()
        if identity not in self.diag_routes and len(self.diag_routes)<80:
            self.diag_routes[identity]=len(self.diag_routes)+1
        route=self.diag_routes.get(identity,0)
        group='reCAPTCHA' if provider=='reCAPTCHA' else 'другой'
        segments=re.split(r'[^a-z]+',parsed.path.casefold())
        if provider=='OpenSooq' and any(s in {'login','signin','auth','authenticate','authentication','authorization','session','sessions','token','password','otp','verify','verification'} for s in segments):
            group='авторизация*'
        method=request.method if request.method in {'GET','POST','PUT','PATCH','DELETE','HEAD','OPTIONS'} else 'OTHER'
        resource=request.resource_type if request.resource_type in {'document','xhr','fetch','script','image','stylesheet','font','other'} else 'other'
        return (self.diag_action,self.diag_action_label,route,group,method,resource,provider)

    def request_seen(self, request):
        metadata=self.request_metadata(request)
        if metadata is not None and len(self.diag_pending)<500:
            self.diag_pending[id(request)]=metadata

    def request_finished(self, request):
        self.diag_pending.pop(id(request),None)

    def add_diagnostic_event(self, metadata, result):
        self.diag_events.append((*metadata[:6],result))
        del self.diag_events[:-40]

    def response_seen(self, response):
        metadata=self.diag_pending.get(id(response.request)) or self.request_metadata(response.request)
        if metadata is None:
            return
        status=int(response.status)
        if not 100<=status<=599:
            return
        self.diag_http[(metadata[6],status)]+=1
        if status>=400 or (metadata[3]=='авторизация*' and metadata[5] in {'xhr','fetch','document'}):
            self.add_diagnostic_event(metadata,'HTTP '+str(status))
        self.inspect_login_error(response, metadata, status)

    def inspect_login_error(self, response, metadata, status):
        # Process only failed OpenSooq login-like fetches, at most 20 per viewer.
        # No extra HTTP request is sent: response.body() reads the existing reply.
        if (metadata[6] != 'OpenSooq' or metadata[3] != 'авторизация*'
                or metadata[5] not in {'fetch', 'xhr'} or not 400 <= status < 500
                or self.diag_inspected >= 20 or len(self.diag_inspect_tasks) >= 4):
            return
        self.diag_inspected += 1
        generation = self.diag_generation
        task = asyncio.create_task(self.read_login_error(response, metadata, status, generation))
        self.diag_inspect_tasks.add(task)
        task.add_done_callback(self.diag_inspect_tasks.discard)

    async def read_login_error(self, response, metadata, status, generation):
        labels = set()
        detail = 'JSON с уточнением не получен'
        try:
            headers = response.headers
            kind = headers.get('content-type', '').partition(';')[0].strip().lower()
            if kind == 'application/json' or (kind.startswith('application/') and kind.endswith('+json')):
                declared = headers.get('content-length')
                if declared is not None and (not declared.isdecimal() or int(declared) > 32768):
                    detail = 'разбор пропущен: размер ответа'
                else:
                    raw = await asyncio.wait_for(response.body(), timeout=2)
                    if len(raw) <= 32768:
                        # JSON is parsed in memory only. Never stringify or log it.
                        document = json.loads(raw)
                        labels = login_error_labels(document)
                        detail = 'известного сообщения об ошибке нет'
                    else:
                        detail = 'разбор пропущен: размер ответа'
        except asyncio.CancelledError:
            raise
        except Exception:
            # Exception text may contain credentials or browser request details.
            detail = 'ответ не удалось безопасно разобрать'
        if generation != self.diag_generation:
            return
        descriptions = [LOGIN_ERROR_LABELS[key] for key in sorted(labels)]
        self.diag_error_details.append((metadata[0], metadata[2], status,
                                        '; '.join(descriptions[:2]) if descriptions else detail))
        del self.diag_error_details[:-4]
        if 'wait' in labels:
            self.diag_flags.add('wait')

    async def cancel_diagnostic_reads(self):
        self.diag_generation += 1
        tasks = tuple(self.diag_inspect_tasks)
        for task in tasks:
            task.cancel()
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)
        self.diag_inspect_tasks.clear()

    def request_failed(self, request):
        metadata=self.diag_pending.pop(id(request),None) or self.request_metadata(request)
        if metadata is None:
            return
        # ERR_ABORTED бывает обычной отменой при навигации; не называем это блокировкой.
        reason='отменён' if request.failure=='net::ERR_ABORTED' else 'сетевая ошибка'
        self.diag_failures[(metadata[6],reason)]+=1
        if metadata[3]=='авторизация*':
            self.add_diagnostic_event(metadata,reason)

    async def collect_flags(self, force=False):
        if self.page is None or (not force and time.monotonic()-self.last_diag_check<3):
            return
        self.last_diag_check=time.monotonic()
        for frame in self.page.frames[:30]:
            try:
                host=urlsplit(frame.url).hostname or ''
            except ValueError:
                continue
            if host!='opensooq.com' and not host.endswith('.opensooq.com'):
                continue
            for key,pattern in [('captcha_failed',r'^recaptcha verification failed$'),
                                ('unauthorized',r'^unauthorized$'),
                                ('wait',r'^please wait before trying again(?: or contact us)?$')]:
                with suppress(Exception):
                    for candidate in (await frame.get_by_text(re.compile(pattern,re.I)).all())[:8]:
                        if await candidate.is_visible():
                            self.diag_flags.add(key)
                            break

    async def replace_focused_field(self, value):
        # Смотрим только на фокус и редактируемость. Значения полей не читаем.
        candidates=[]
        for frame in self.page.frames[:30]:
            try:
                host=urlsplit(frame.url).hostname or ''
            except ValueError:
                continue
            if host!='opensooq.com' and not host.endswith('.opensooq.com'):
                continue
            for item in (await frame.locator('input:focus, textarea:focus, [contenteditable="true"]:focus').all())[:3]:
                if (await item.is_visible() and await item.is_editable()
                        and await item.evaluate('(el) => el.ownerDocument.hasFocus()')):
                    candidates.append(item)
        if len(candidates)!=1:
            raise ValueError('Сначала нажмите нужное поле OpenSooq на экране, затем снова нажмите «Заменить поле». Текст не введён.')
        await candidates[0].fill(value,timeout=5000)

    async def issue(self,country='sa'):
        if country not in COUNTRIES:
            raise ValueError('Неизвестная страна аккаунта.')
        async with self.lock:
            await self._close()
            self.country=country
            self.diag_flags.clear();self.diag_http.clear();self.diag_failures.clear()
            self.diag_routes.clear();self.diag_pending.clear();self.diag_events.clear()
            self.diag_error_details.clear();self.diag_blocked_kinds.clear()
            self.diag_inspected=0
            self._account_entry_pending=True
            self.diag_salt=secrets.token_hex(16)
            self.diag_blocked=0;self.diag_action=0;self.diag_action_label='открытие страницы' 
            self.diag_exists=True
            self.last_diag_check=0.0
            self.token=secrets.token_urlsafe(32)
            self.expires=time.monotonic()+900
            self.active=True
            dialogs=getattr(self.service,'dialogues',None)
            if dialogs is not None:
                dialogs.cancelled.update(row['id'] for row in dialogs.db.execute(
                    'SELECT id FROM seller_dialogues WHERE chat=?',(ADMIN_ID,)))
                async with dialogs.lock:
                    try:
                        pause_account_automation(dialogs)
                        await dialogs.transport.close()
                    except BaseException:
                        await self._close()
                        raise
            return self.token

    def authorized(self, value):
        try:
            return (self.active and time.monotonic()<self.expires and bool(self.token)
                    and isinstance(value,str) and secrets.compare_digest(value,'Bearer '+self.token))
        except (TypeError,ValueError):return False

    def blocked_navigation(self, request):
        self.diag_blocked+=1
        try:
            frame_kind='основное окно' if request.frame.parent_frame is None else 'встроенное окно'
        except Exception:
            frame_kind='окно не определено'
        destination=login_blocked_destination(request.url)
        self.diag_blocked_kinds[(frame_kind,destination)]+=1

    def _listeners(self):
        return (('request',self.request_seen),('requestfinished',self.request_finished),
                ('response',self.response_seen),('requestfailed',self.request_failed))

    async def _open(self):
        if self.page is not None and not self.page.is_closed():
            return
        try:
            manager=self.service.account_browser
            self.context,self.page=await manager.get_page()
            manager.on_blocked=self.blocked_navigation
            self._observed_page=self.page
            for event,callback in self._listeners():
                self.page.on(event,callback)
            current=urlsplit(self.page.url)
            requested_host=self.country+'.opensooq.com'
            current_host=current.hostname or ''
            # Новый /account начинает с главной выбранной страны.
            # Профиль и заданный прокси сохраняются; чаты сами не открываются.
            if (self._account_entry_pending or not login_navigation_allowed(self.page.url,True)
                    or (current_host in {c+'.opensooq.com' for c in COUNTRIES}
                        and current_host!=requested_host)):
                await self.page.goto('https://'+requested_host+'/en',wait_until='domcontentloaded',timeout=30000)
            self._account_entry_pending=False
        except asyncio.CancelledError:
            await self._close()
            raise
        except Exception as error:
            self.diag_flags.add('browser_error')
            await self._close()
            if isinstance(error,DialogueUnavailable):
                raise
            raise DialogueUnavailable('Не удалось показать постоянный браузер. Проверьте DATA_DIR, Chromium и память Render.') from None

    async def screen(self, authorization):
        async with self.lock:
            if not self.authorized(authorization):raise PermissionError()
            await self._open()
            await self.collect_flags()
            return await self.page.screenshot(type='png')

    async def action(self, authorization, data):
        async with self.lock:
            if not self.authorized(authorization):raise PermissionError()
            await self._open()
            action=data.get('action')
            labels={'click':'нажатие','text':'замена поля','key':'клавиша',
                    'scroll':'прокрутка','login':'вход через главную','chats':'открытие чатов','save':'сохранение','close':'закрытие'}
            if action not in labels:
                raise ValueError('Действие не поддерживается.')
            self.diag_action+=1
            self.diag_action_label=labels[action]
            if action=='key' and data.get('key') in {'Enter','Backspace','Tab'}:
                self.diag_action_label+=' '+data['key']
            if action=='click':
                x,y=data.get('x'),data.get('y')
                if isinstance(x,bool) or isinstance(y,bool) or not isinstance(x,(int,float)) or not isinstance(y,(int,float)) or not math.isfinite(x) or not math.isfinite(y) or not 0<=x<420 or not 0<=y<820:
                    raise ValueError('Нажмите внутри экрана браузера.')
                await self.page.mouse.click(x,y)
            elif action=='text':
                value=data.get('text')
                if not isinstance(value,str) or not 1<=len(value)<=200:
                    raise ValueError('Введите от 1 до 200 символов.')
                await self.replace_focused_field(value)
            elif action=='key':
                if data.get('key') not in {'Enter','Backspace','Tab'}:raise ValueError('Клавиша не поддерживается.')
                await self.page.keyboard.press(data['key'])
            elif action=='scroll':
                dy=data.get('dy')
                if type(dy) is not int or dy not in {-500,500}:raise ValueError('Некорректная прокрутка.')
                await self.page.mouse.wheel(0,dy)
            elif action=='login':
                await self.page.goto('https://'+self.country+'.opensooq.com/en',wait_until='domcontentloaded',timeout=30000)
                # Open the site's own login form; never submit credentials here.
                login=self.page.get_by_role('button',name='Login or Sign Up',exact=True)
                if await login.count()==1 and await login.is_visible():
                    await login.click()
            elif action=='chats':
                await self.page.goto('https://my.opensooq.com/chats',wait_until='domcontentloaded',timeout=30000)
            elif action=='save':
                return await self._save()
            elif action=='close':
                await self._close()
                return {'finished':True,'message':'Доступ по ссылке закрыт. Профиль браузера сохранён; остановленные диалоги остаются на паузе.'}
            else:raise ValueError('Действие не поддерживается.')
            await self.collect_flags(force=True)
            message=('Значение выбранного поля заменено.' if action=='text' else
                     'Действие выполнено. Проверьте результат на экране — это не подтверждение входа.')
            return {'message':message}

    async def _save(self):
        url=urlsplit(self.page.url)
        room=dict(parse_qsl(url.query)).get('selectedRoom','')
        match=re.fullmatch(r'\d+-\d+-(\d+)',room)
        if url.scheme!='https' or url.hostname!='my.opensooq.com' or url.path!='/chats' or not match:
            raise ValueError('Откройте «Чаты» и выберите существующий диалог, затем сохраните вход.')
        if not await self.page.get_by_role('button',name='My Profile',exact=True).is_visible():
            raise ValueError('Вход не подтверждён. Завершите вход на сайте.')
        if not await self.page.get_by_placeholder('Message Text...',exact=True).is_visible():
            raise ValueError('Дождитесь загрузки выбранного диалога.')
        # Браузерные данные остаются в профиле. Файл ниже хранит только
        # подтверждённый аккаунт и явное разрешение владельца на автоответы.
        path=write_account_metadata({'_opensooq_account_id':match[1],
            '_opensooq_chat_enabled':True,'_opensooq_profile_mode':'persistent',
            '_opensooq_profile_version':1})
        dialogs=self.service.dialogues
        async with dialogs.lock:
            await dialogs.transport.close()
            dialogs.transport.state_file=path
            dialogs.transport.account=match[1]
            dialogs.transport.saved_enabled=True
            dialogs.transport.disabled=False
            dialogs.transport.blocked=False
            dialogs.transport.profile_mode=True
        await self._close()
        with suppress(TelegramError):
            await self.service.bot.send_message(chat_id=ADMIN_ID,text='✅ Вход подтверждён. Переписка использует тот же постоянный профиль браузера. Диалоги, остановленные при открытии /account, остаются на паузе. Запуск — кнопкой у выбранного объявления. /chatstatus — состояние, /account_off — отключение.')
        return {'finished':True,'message':'Вход подтверждён, профиль сохранён. Браузер остаётся доступен боту; прежние диалоги на паузе.'}

    async def _close(self):
        # Отзываем только доступ по ссылке. Общий браузер и его профиль остаются.
        page=self._observed_page
        if page is not None:
            for event,callback in self._listeners():
                with suppress(Exception):
                    page.remove_listener(event,callback)
        manager=getattr(self.service,'account_browser',None)
        if manager is not None and manager.on_blocked==self.blocked_navigation:
            manager.on_blocked=None
        self._observed_page=None
        self.context=self.browser=self.pw=self.page=None
        await self.cancel_diagnostic_reads()
        self.diag_pending.clear()
        self.active=False;self.token='';self.expires=0

    async def expire(self):
        if self.active and time.monotonic()>=self.expires:
            async with self.lock:
                if self.active and time.monotonic()>=self.expires:
                    await self._close()

    async def close(self):
        async with self.lock:await self._close()


def account_origin():
    raw=os.getenv('RENDER_EXTERNAL_URL','').strip()
    parsed=urlsplit(raw)
    if parsed.scheme!='https' or not parsed.hostname or parsed.username or parsed.password or parsed.query or parsed.fragment or parsed.path not in {'','/'}:
        raise ValueError('Не найден HTTPS-адрес сервиса. Задайте RENDER_EXTERNAL_URL адресом вашего сервиса Render без пути и параметров.')
    return raw.rstrip('/')


def make_http_handler(service, loop):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self,*args):pass
        def respond(self,status,body,kind='application/json; charset=utf-8'):
            if not isinstance(body,bytes):body=json.dumps(body,ensure_ascii=False).encode()
            self.send_response(status)
            self.send_header('Content-Type',kind)
            self.send_header('Content-Length',str(len(body)))
            self.send_header('Cache-Control','no-store, max-age=0')
            self.send_header('Referrer-Policy','no-referrer')
            self.send_header('X-Content-Type-Options','nosniff')
            self.send_header('X-Frame-Options','DENY')
            self.send_header('Content-Security-Policy',"default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; connect-src 'self'; img-src blob:; frame-ancestors 'none'; base-uri 'none'; form-action 'none'")
            self.end_headers()
            with suppress(BrokenPipeError,ConnectionResetError):self.wfile.write(body)
        def api(self,post=False):
            manager=service.account_login
            authorization=self.headers.get('Authorization','')
            if not manager.authorized(authorization):
                self.respond(401,{'error':'Доступ истёк или ссылка неверна. Получите новую через /account.'});return
            if post:
                try:
                    if self.headers.get('Origin')!=account_origin():
                        self.respond(403,{'error':'Источник запроса не разрешён.'});return
                    size=int(self.headers.get('Content-Length','0'))
                    if not 0<size<=8192:raise ValueError()
                    if self.headers.get('Content-Type','').split(';')[0]!='application/json':raise ValueError()
                    data=json.loads(self.rfile.read(size))
                    if not isinstance(data,dict):raise ValueError()
                except (ValueError,TypeError):
                    self.respond(400,{'error':'Некорректный запрос.'});return
                coroutine=manager.action(authorization,data)
            else:coroutine=manager.screen(authorization)
            future=asyncio.run_coroutine_threadsafe(coroutine,loop)
            try:
                result=future.result(timeout=40)
                self.respond(200,result,'application/json; charset=utf-8' if post else 'image/png')
            except PermissionError:self.respond(401,{'error':'Доступ истёк. Получите новую ссылку.'})
            except (ValueError,DialogueUnavailable) as exc:self.respond(400,{'error':str(exc)[:600]})
            except Exception:
                future.cancel()
                # Никаких содержимых полей, cookie, токенов и исключений браузера в ответе/логе.
                self.respond(503,{'error':'Браузер не ответил. Откройте новую ссылку через /account.'})
        def do_GET(self):
            if self.path in {'/','/healthz'}:self.respond(200,b'ok','text/plain')
            elif self.path=='/account':self.respond(200,ACCOUNT_PAGE.encode(),'text/html; charset=utf-8')
            elif self.path=='/account-api/screen':self.api()
            else:self.respond(404,{'error':'Не найдено.'})
        def do_POST(self):
            if self.path=='/account-api/action':self.api(post=True)
            else:self.respond(404,{'error':'Не найдено.'})
    return Handler



def build_app(token, allowed, database):
    async def setup(app):
        if SUBSCRIPTIONS_ENABLED and not os.getenv("ADMIN_ID", "").strip():
            raise RuntimeError("Для подписок явно задайте ADMIN_ID владельца в Environment.")
        service = Service(app.bot, allowed, database)
        app.bot_data["service"] = service
        log.info("[startup] database=%s data_dir=%s browser=%s proxy=%s", Path(database).resolve(), DATA_DIR.resolve(), USE_BROWSER, bool(service.reader.proxy_url))
        if os.getenv("PORT"):
            server = ThreadingHTTPServer(("0.0.0.0", int(os.environ["PORT"])), make_http_handler(service,asyncio.get_running_loop()))
            server.daemon_threads=True
            threading.Thread(target=server.serve_forever, daemon=True).start()
            app.bot_data["health_server"] = server
        if app.job_queue is None:
            raise RuntimeError('Установите python-telegram-bot с дополнением [job-queue].')
        app.job_queue.run_repeating(service.tick, interval=15, first=5)
        app.job_queue.run_repeating(service.billing.poll, interval=30, first=10)
        app.job_queue.run_repeating(service.dialogues.poll, interval=30, first=15)
        try:
            await app.bot.set_my_commands([
                BotCommand("start", "Меню"), BotCommand("check", "Проверить объявления"),
                BotCommand("restart", "Перезапустить проверку"), BotCommand("pause", "Остановить"),
                BotCommand("status", "Статус и отчёт"), BotCommand("help", "Справка"), BotCommand("id", "Мой ID"),
                BotCommand("testproxy", "Проверить прокси и просмотры"),
                BotCommand("saved", "Сохранённые поиски"), BotCommand("cancel", "Отменить ввод"),
                BotCommand("subscription", "Подписка и оплата"),
            ])
        except TelegramError as exc:
            # Список команд — оформление меню; временная ошибка этого вызова
            # не должна останавливать уже инициализированный парсер.
            log.warning("[startup_commands] %s", error_text(exc))
    async def cleanup(app):
        server = app.bot_data.pop("health_server", None)
        if server:
            await asyncio.to_thread(server.shutdown)
            server.server_close()
        service = app.bot_data.pop("service", None)
        if service:
            await service.close()
    async def on_error(update, context):
        error = context.error
        log.error("Ошибка обработчика: %s", type(error).__name__, exc_info=(type(error), error, error.__traceback__))
    app = (Application.builder().token(token).concurrent_updates(False)
           .post_init(setup).post_stop(cleanup).post_shutdown(cleanup).build())
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.TEXT, handle))
    app.add_handler(CallbackQueryHandler(button_handler))
    app.add_error_handler(on_error)
    return app


class StartupCheckError(Exception):
    def __init__(self, code, message):
        self.code = code
        super().__init__(message)


def check_startup(network=True, client=None):
    """Без polling, платежей и записи в БД. Безопасно для Pre-Deploy Command."""
    token = os.getenv("BOT_TOKEN", "").strip()
    if not re.fullmatch(r"[0-9]+:[A-Za-z0-9_-]+", token):
        raise StartupCheckError(11, "BOT_TOKEN_FORMAT: нужен токен Telegram от BotFather, а не ключ xRocket.")
    if ADMIN_ID <= 0 or (SUBSCRIPTIONS_ENABLED and not os.getenv("ADMIN_ID", "").strip()):
        raise StartupCheckError(12, "ADMIN_ID: укажите положительный числовой Telegram ID владельца.")
    try:
        {int(v.strip()) for v in os.getenv("ALLOWED_TELEGRAM_IDS", "").split(",") if v.strip()}
        proxy_settings(os.getenv("OPENSOOQ_PROXY_URL", ""))
        if os.getenv("PORT") and not 0 <= int(os.environ["PORT"]) <= 65535:
            raise ValueError()
    except ValueError:
        raise StartupCheckError(13, "CONFIG: проверьте формат ALLOWED_TELEGRAM_IDS, PORT и OPENSOOQ_PROXY_URL.") from None
    if SUBSCRIPTIONS_ENABLED:
        if not os.getenv("XROCKET_API_TOKEN", "").strip():
            raise StartupCheckError(14, "XROCKET_API_TOKEN: ключ отсутствует при включённых подписках.")
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{4,31}", os.getenv("SUPPORT_USERNAME", "").strip().lstrip("@")):
            raise StartupCheckError(15, "SUPPORT_USERNAME: нужен Telegram username поддержки, без ссылки.")
    print("[startup_check] CONFIG_OK", flush=True)
    if not network:
        return

    owned = client is None
    if owned:
        client = httpx.Client(timeout=httpx.Timeout(15, connect=10), trust_env=False, follow_redirects=False)
    try:
        # Единственный запрос к Telegram — getMe. Второй getUpdates не запускается.
        try:
            response = client.get("https://api.telegram.org/bot" + token + "/getMe")
        except httpx.RequestError:
            raise StartupCheckError(22, "TELEGRAM_NETWORK: нет соединения с api.telegram.org из нового контейнера.") from None
        if response.status_code in {401, 404}:
            raise StartupCheckError(21, "TELEGRAM_AUTH: Telegram отверг BOT_TOKEN. Проверьте его у BotFather.")
        if response.status_code != 200:
            raise StartupCheckError(23, f"TELEGRAM_HTTP: HTTP {response.status_code} при getMe.")
        try:
            if response.json().get("ok") is not True:
                raise ValueError()
        except (ValueError, AttributeError):
            raise StartupCheckError(23, "TELEGRAM_RESPONSE: некорректный ответ getMe.") from None
        print("[startup_check] TELEGRAM_OK", flush=True)

        if SUBSCRIPTIONS_ENABLED:
            base = "https://pay.api.testnet.xrocket.exchange" if XROCKET_TESTNET else "https://pay.api.xrocket.exchange"
            try:
                # Только сведения о приложении; счетов, переводов и списаний нет.
                response = client.get(base + "/api/v1/app-info", headers={
                    "Authorization": "Bearer " + os.getenv("XROCKET_API_TOKEN", "").strip()})
            except httpx.RequestError:
                raise StartupCheckError(32, "XROCKET_NETWORK: нет соединения с xRocket Pay API.") from None
            if response.status_code in {401, 403}:
                raise StartupCheckError(31, "XROCKET_AUTH: проверьте Current Pay API Token и соответствие XROCKET_TESTNET выбранному приложению.")
            if response.status_code != 200:
                raise StartupCheckError(33, f"XROCKET_HTTP: HTTP {response.status_code} при чтении сведений о приложении.")
            print("[startup_check] XROCKET_OK", flush=True)
        print("[startup_check] CHECK_COMPLETE", flush=True)
    finally:
        if owned:
            client.close()


class SecretFormatter(logging.Formatter):
    def format(self, record):
        return error_text(super().format(record))


def main():
    handler = logging.StreamHandler()
    handler.setFormatter(SecretFormatter("%(asctime)s %(levelname)s %(message)s"))
    logging.basicConfig(level=logging.INFO, handlers=[handler], force=True)
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("httpcore").setLevel(logging.WARNING)
    if "--chat-login" in sys.argv:
        asyncio.run(local_chat_login())
        return 0
    if "--check-startup" in sys.argv:
        try:
            check_startup()
            return 0
        except StartupCheckError as exc:
            print(f"[startup_check_failed] EXIT={exc.code} {error_text(exc)}", flush=True)
            return exc.code
    token = os.getenv("BOT_TOKEN", "").strip()
    if not token:
        raise SystemExit("Задайте BOT_TOKEN в Environment на Render.")
    allowed = {ADMIN_ID} | {int(v.strip()) for v in os.getenv("ALLOWED_TELEGRAM_IDS", "").split(",") if v.strip()}
    log.info("[boot_v18] Создание Telegram Application")
    app = build_app(token, allowed, DATABASE)
    try:
        app.run_polling(allowed_updates=["message", "callback_query"], bootstrap_retries=3)
    except Exception:
        log.exception("[startup_failed] Бот остановился при запуске")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
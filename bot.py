import asyncio
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
from datetime import datetime
from email.utils import parsedate_to_datetime
from html import escape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urljoin, urlsplit, urlunsplit
from zoneinfo import ZoneInfo

import httpx

from bs4 import BeautifulSoup
from dotenv import load_dotenv

from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Update,
)

from telegram.error import (
    BadRequest,
    Forbidden,
    RetryAfter,
    TelegramError,
)

from telegram.ext import (
    Application,
    MessageHandler,
    CallbackQueryHandler,
    filters,
    ContextTypes,
)


load_dotenv()

ADMIN_ID = int(os.getenv("ADMIN_ID", "1110325917"))

DATABASE = Path(
    os.getenv("DATABASE_PATH", "bot.sqlite3")
)

DATA_DIR = Path(
    os.getenv("DATA_DIR", str(DATABASE.parent))
)

PASSWORD_FILE = DATA_DIR / "passwords.txt"
BLOCKED_FILE = DATA_DIR / "blocked.txt"

DISPLAY_TZ = ZoneInfo(
    os.getenv("APP_TIMEZONE", "Europe/Moscow")
)

USE_BROWSER = os.getenv("PROFILE_BROWSER", "1") == "1"

COUNTRIES = "kw ae bh sa".split()

HOSTS = {
    "opensooq.com",
    "www.opensooq.com",
} | {
    country + ".opensooq.com"
    for country in COUNTRIES
}

METRICS = {
    "price",
    "views",
    "seller_views",
    "rating",
    "ratings",
    "reviews",
    "sold",
    "photos",
    "listings_count",
}

MAX_PAGES = 20
MAX_ADS = 1000
MAX_SEND = 200

CDN = "https://opensooq-imagesv2.os-cdn.com/previews/700x0/"

log = logging.getLogger("opensooq")

EXCLUDED_WORDS = [
    "car",
    "cars",
    "auto",
    "autos",
    "kia",
    "gmc",
    "toyota",
    "nissan",
    "chevrolet",
    "ford",
    "bmw",
    "mercedes",
    "audi",
    "hyundai",
    "apartment",
    "flat",
    "real estate",
    "rent",
    "rental",
    "delivery",
    "service",
    "job",
    "vacancy",
    "سيارة",
    "سيارات",
    "شقة",
    "شقق",
    "عقار",
    "ايجار",
    "تأجير",
    "خدمة",
    "وظيفة",
]

EXCLUDED_RE = re.compile(
    r"(?<!\w)(?:"
    + "|".join(re.escape(word) for word in EXCLUDED_WORDS)
    + r")(?!\w)",
    re.I,
)


class SourceError(Exception):
    pass


class RateLimit(SourceError):
    pass


def safe_url(value, base=""):
    value = urljoin(base, str(value).strip())

    try:
        parsed = urlsplit(value)

        if (
            len(value) > 8192
            or "\\" in value
            or any(ord(char) < 32 for char in value)
            or parsed.scheme not in {"http", "https"}
            or parsed.hostname not in HOSTS
            or parsed.username
            or parsed.password
            or parsed.port not in {None, 80, 443}
        ):
            raise ValueError()

    except ValueError:
        raise ValueError(
            "Нужна веб-ссылка на категорию OpenSooq."
        ) from None

    return urlunsplit(
        (
            "https",
            parsed.hostname,
            parsed.path or "/",
            parsed.query,
            "",
        )
    )


def photo_url(value, base=CDN):
    if not isinstance(value, str) or not value:
        return ""

    if value.startswith("//"):
        value = "https:" + value

    if not value.startswith(("https://", "http://", "//")):
        value = urljoin(
            base.replace("{size}", "700x0"),
            value,
        )

        if value.lower().endswith((".jpg", ".jpeg", ".png")):
            value += ".webp"

    parsed = urlsplit(value)

    if (
        parsed.scheme not in {"http", "https"}
        or not parsed.hostname
        or not (
            parsed.hostname.endswith(".os-cdn.com")
            or parsed.hostname in HOSTS
        )
        or parsed.username
        or parsed.password
        or parsed.port not in {None, 80, 443}
    ):
        return ""

    return urlunsplit(
        (
            "https",
            parsed.hostname,
            parsed.path,
            parsed.query,
            "",
        )
    )


def number(value):
    if value is None or isinstance(value, bool):
        return None

    if isinstance(value, (int, float)):
        if value >= 0 and math.isfinite(value):
            return float(value)

        return None

    text = "".join(
        str(unicodedata.digit(char))
        if char.isdecimal()
        else char
        for char in str(value)
    )

    text = (
        text.replace("٬", "")
        .replace("٫", ".")
        .replace(",", "")
        .replace("\u200f", "")
        .replace("\u200e", "")
    )

    text = re.sub(
        r"(?<=\d)\s+(?=\d)",
        "",
        text,
    )

    match = re.search(
        r"(\d+(?:\.\d+)?)(?:\s*(k|m|b|ألف|الف|مليون)(?!\w))?",
        text,
        re.I,
    )

    if not match or text.lstrip().startswith("-"):
        return None

    scales = {
        "k": 1000,
        "m": 1000000,
        "b": 1000000000,
        "ألف": 1000,
        "الف": 1000,
        "مليون": 1000000,
    }

    result = float(match[1]) * scales.get(
        (match[2] or "").lower(),
        1,
    )

    return result if math.isfinite(result) else None


def count(value):
    result = number(value)
    return round(result) if result is not None else None


def walk(value):
    if isinstance(value, dict):
        yield value

        for child in value.values():
            yield from walk(child)

    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def props(soup):
    tag = soup.find("script", id="__NEXT_DATA__")

    if not tag:
        return {}

    try:
        return json.loads(
            tag.string or tag.get_text()
        )["props"]["pageProps"]

    except (ValueError, KeyError, TypeError):
        raise SourceError(
            "Изменились данные страницы OpenSooq."
        ) from None


def flight(soup):
    chunks = []
    result = []

    for tag in soup.find_all("script", src=False):
        text = tag.string or tag.get_text()

        for match in re.finditer(
            r"(?:self\.)?__next_f\.push\(",
            text,
        ):
            try:
                data, _ = json.JSONDecoder().raw_decode(
                    text[match.end():]
                )

                if (
                    isinstance(data, list)
                    and len(data) > 1
                    and data[0] == 1
                    and isinstance(data[1], str)
                ):
                    chunks.append(data[1])

            except ValueError:
                pass

    for line in "".join(chunks).splitlines():
        key, separator, value = line.partition(":")

        if (
            separator
            and re.fullmatch(r"[0-9a-fA-F]+", key)
            and value[:1] in {"{", "["}
        ):
            with suppress(ValueError):
                result.append(json.loads(value))

    return result


def parse_profile(raw, expected_id):
    soup = BeautifulSoup(raw, "html.parser")

    result = {
        "rating": None,
        "ratings": None,
        "reviews": None,
        "seller_views": None,
        "sold": None,
        "listings_count": None,
    }

    def put(key, value, convert=count):
        if result[key] is None and value is not None:
            result[key] = convert(value)

    documents = []

    with suppress(SourceError):
        documents.append(props(soup))

    documents.extend(flight(soup))

    members = []

    for obj in walk(documents):
        member = obj.get("member")

        if isinstance(member, dict) and any(
            key in member
            for key in (
                "views_count",
                "views",
                "posts_count",
                "member_info",
                "rating",
            )
        ):
            members.append(member)

    expected_id = (
        str(expected_id).strip()
        if expected_id is not None
        else ""
    )

    if expected_id:
        matching = [
            member
            for member in members
            if str(member.get("id")) == expected_id
        ]

        without_id = [
            member
            for member in members
            if member.get("id") is None
        ]

        if matching:
            members = matching

        elif without_id:
            members = without_id

        elif members:
            raise SourceError(
                "Открыт профиль другого продавца."
            )

    for member in members:
        put("seller_views", member.get("views_count"))
        put("seller_views", member.get("views"))
        put("listings_count", member.get("posts_count"))

        rating = member.get("rating")

        if isinstance(rating, dict):
            put(
                "rating",
                rating.get("average_rating"),
                number,
            )
            put(
                "ratings",
                rating.get("number_of_rating"),
            )
            put(
                "reviews",
                rating.get("number_of_reviews"),
            )

        info = member.get("member_info")

        if isinstance(info, dict):
            put(
                "sold",
                info.get("sold_listings_count"),
            )

    for tag in soup(
        ["script", "style", "template", "noscript"]
    ):
        tag.decompose()

    def clean_text(value):
        value = unicodedata.normalize("NFKC", value)

        value = re.sub(
            r"[\u064b-\u065f\u0670\u200e\u200f\u061c]",
            "",
            value,
        )

        return re.sub(r"\s+", " ", value).strip()

    numeric = (
        r"\d[\d.,٬٫]*(?: \d{3})*"
        r"(?:\s*(?:[kmb]|ألف|الف|مليون))?"
    )

    view_label = r"(?:Views?|مشاهدة|مشاهدات|المشاهدات)"

    follower_label = (
        r"(?:Followers?|المتابعون|المتابعين|"
        r"متابعون|متابعين|متابع)"
    )

    if result["seller_views"] is None:
        for node in soup.find_all(
            string=re.compile(view_label, re.I)
        ):
            parent = node.parent

            for _ in range(3):
                if parent is None:
                    break

                text = clean_text(
                    parent.get_text(" ", strip=True)
                )

                if len(text) > 350:
                    break

                match = re.search(
                    rf"({numeric})\s*{view_label}\b",
                    text,
                    re.I,
                )

                if match and re.search(
                    follower_label,
                    text,
                    re.I,
                ):
                    put(
                        "seller_views",
                        match.group(1),
                    )

                    if result["seller_views"] is not None:
                        break

                parent = parent.parent

            if result["seller_views"] is not None:
                break

    tab_labels = {
        "listings_count": (
            r"(?:Live\s+Listings?|"
            r"(?:الإعلانات|الاعلانات)\s+"
            r"(?:الفعاله|الفعالة|النشطة))"
        ),
        "sold": (
            r"(?:Sold\s+Listings?|"
            r"(?:الإعلانات|الاعلانات)\s+المباعة)"
        ),
    }

    for tab in soup.select(
        "li, a, button, [role='tab']"
    ):
        text = clean_text(
            tab.get_text(" ", strip=True)
        )

        if len(text) > 150:
            continue

        for key, label in tab_labels.items():
            if result[key] is not None:
                continue

            match = re.fullmatch(
                rf"{label}\s*[（(]\s*({numeric})\s*[)）]",
                text,
                re.I,
            )

            if match:
                put(key, match.group(1))

    page_text = clean_text(
        soup.get_text(" ", strip=True)
    )

    if result["reviews"] is None:
        match = re.search(
            r"(?:\(|^|\s)(\d+)\s*"
            r"(?:reviews?|تقييمات|مراجعات)",
            page_text,
            re.I,
        )

        if match:
            put("reviews", match.group(1))

    if result["rating"] is None:
        match = re.search(
            r"(\d[.٫]\d+)\s*(?:★|stars?|نجوم)",
            page_text,
            re.I,
        )

        if match:
            put(
                "rating",
                match.group(1),
                number,
            )

    return result


def update_filters(current, text):
    result = dict(current)

    for pair in shlex.split(text):
        key, separator, value = pair.partition("=")
        metric, _, bound = key.rpartition("_")

        if (
            not separator
            or (
                key not in {
                    "keywords",
                    "exclude",
                    "currency",
                    "unknown",
                }
                and not (
                    metric in METRICS
                    and bound in {"min", "max"}
                )
            )
        ):
            raise ValueError(
                f"Неизвестный фильтр: {pair[:60]}"
            )

        if value.lower() in {"off", "none"}:
            result.pop(key, None)

        elif key in {"keywords", "exclude"}:
            if (
                len(value) > 500
                or not any(
                    item.strip()
                    for item in value.split(",")
                )
            ):
                raise ValueError(
                    "Укажите слова через запятую."
                )

            result[key] = value

        elif key == "currency":
            if not re.fullmatch(
                "[A-Za-z]{3}",
                value,
            ):
                raise ValueError(
                    "Валюта: код из 3 букв."
                )

            result[key] = value.upper()

        elif key == "unknown":
            if value not in {"include", "exclude"}:
                raise ValueError(
                    "unknown: только include или exclude."
                )

            result[key] = value

        else:
            number_value = float(
                value.replace(",", ".")
            )

            if (
                not math.isfinite(number_value)
                or number_value < 0
                or (
                    metric == "rating"
                    and number_value > 5
                )
            ):
                raise ValueError(
                    "Числа должны быть неотрицательными."
                )

            if (
                metric not in {"price", "rating"}
                and not number_value.is_integer()
            ):
                raise ValueError(
                    "Счётчики должны быть целыми."
                )

            result[key] = number_value

    for metric in METRICS:
        if (
            result.get(metric + "_min", 0)
            > result.get(metric + "_max", math.inf)
        ):
            raise ValueError(
                f"{metric}_min больше {metric}_max."
            )

    return result


def matches(ad, rules):
    text = (
        ad["title"]
        + "\n"
        + ad.get("description", "")
    ).casefold()

    def terms(name):
        return [
            value.strip().casefold()
            for value in rules.get(name, "").split(",")
            if value.strip()
        ]

    if terms("keywords") and not any(
        value in text
        for value in terms("keywords")
    ):
        return False, set()

    if any(
        value in text
        for value in terms("exclude")
    ):
        return False, set()

    missing = set()
    accepted = True

    if rules.get("currency"):
        if not ad.get("currency"):
            missing.add("currency")

        elif ad["currency"] != rules["currency"]:
            accepted = False

    for metric in METRICS:
        low = rules.get(metric + "_min")
        high = rules.get(metric + "_max")

        if low is None and high is None:
            continue

        value = ad.get(metric)

        if value is None:
            missing.add(metric)

        elif (
            (low is not None and value < low)
            or (high is not None and value > high)
        ):
            accepted = False

    allow_missing = (
        not missing
        or rules.get("unknown") == "include"
    )

    return accepted and allow_missing, missing


def save_user_password(user_id, password):
    data = {}

    if PASSWORD_FILE.exists():
        with open(PASSWORD_FILE, "r") as file:
            for line in file:
                if ":" in line:
                    uid, pwd = line.strip().split(":", 1)
                    data[uid] = pwd

    data[str(user_id)] = password

    with open(PASSWORD_FILE, "w") as file:
        for uid, pwd in data.items():
            file.write(f"{uid}:{pwd}\n")


def check_user_password(user_id, password):
    if not PASSWORD_FILE.exists():
        return False

    with open(PASSWORD_FILE, "r") as file:
        for line in file:
            if ":" in line:
                uid, pwd = line.strip().split(":", 1)

                if (
                    uid == str(user_id)
                    and pwd == password
                ):
                    return True

    return False


def is_blocked(user_id):
    if not BLOCKED_FILE.exists():
        return False

    with open(BLOCKED_FILE, "r") as file:
        return str(user_id) in [
            line.strip()
            for line in file
        ]


def block_user(user_id):
    if not is_blocked(user_id):
        with open(BLOCKED_FILE, "a") as file:
            file.write(f"{user_id}\n")


def unblock_user(user_id):
    if BLOCKED_FILE.exists():
        with open(BLOCKED_FILE, "r") as file:
            lines = file.readlines()

        with open(BLOCKED_FILE, "w") as file:
            for line in lines:
                if line.strip() != str(user_id):
                    file.write(line)


def plain(value):
    if isinstance(value, dict):
        for key in ("content", "text", "value"):
            if key in value:
                return plain(value[key])

        return ""

    if isinstance(value, list):
        return "\n".join(
            filter(
                None,
                (plain(item) for item in value),
            )
        )

    return "" if value is None else str(value).strip()


def publication(value):
    text = plain(value)

    if not text:
        return ""

    for fmt in (
        "%d-%m-%Y",
        "%d/%m/%Y",
        "%Y-%m-%d",
    ):
        try:
            return datetime.strptime(
                text,
                fmt,
            ).strftime("%d.%m.%Y")

        except ValueError:
            pass

    try:
        parsed = datetime.fromisoformat(
            text.replace("Z", "+00:00")
        )

        if parsed.tzinfo is not None:
            parsed = parsed.astimezone(DISPLAY_TZ)

            return parsed.strftime(
                "%d.%m.%Y %H:%M %Z"
            )

        return (
            parsed.strftime("%d.%m.%Y %H:%M")
            + " (часовой пояс не указан)"
        )

    except ValueError:
        return text[:100]


def relative_label(value):
    text = plain(value).split("•", 1)[0].strip()

    translations = {
        "today": "Сегодня",
        "yesterday": "Вчера",
        "just now": "Только что",
    }

    if text.lower() in translations:
        return translations[text.lower()]

    match = re.fullmatch(
        r"(\d+)\s*(minutes?|mins?|hours?|hrs?|days?)\s+ago",
        text,
        re.I,
    )

    if match:
        unit = match[2].lower()

        if unit.startswith("m"):
            label = "мин."
        elif unit.startswith("h"):
            label = "ч."
        else:
            label = "дн."

        return f"{match[1]} {label} назад"

    return text[:100]


def parse_category(raw, url):
    soup = BeautifulSoup(raw, "html.parser")
    documents = []

    with suppress(SourceError):
        documents.append(props(soup))

    documents.extend(flight(soup))

    data = next(
        (
            obj
            for obj in walk(documents)
            if isinstance(
                obj.get("serpApiResponse"),
                dict,
            )
        ),
        None,
    )

    block = (
        data.get("serpApiResponse", {}).get("listings")
        if data
        else None
    )

    if (
        not isinstance(block, dict)
        or not isinstance(block.get("items"), list)
    ):
        raise SourceError(
            "Не найдены данные категории OpenSooq."
        )

    ads = []

    for row in block["items"]:
        if (
            not isinstance(row, dict)
            or not row.get("id")
            or not row.get("title")
        ):
            continue

        path = row.get("post_url") or f"/search/{row['id']}"

        if path.startswith("/search/"):
            locale = urlsplit(url).path.split("/")[1]

            path = (
                "/"
                + (
                    locale
                    if locale in {"ar", "en"}
                    else "en"
                )
                + path
            )

        image = photo_url(row.get("image_uri"))
        ad = dict.fromkeys(METRICS)

        ad.update(
            id=str(row["id"]),
            url=safe_url(path, url),
            title=plain(row["title"]),
            description=plain(row.get("masked_description")),
            price=number(row.get("price_amount")),
            currency=plain(row.get("price_currency_iso")),
            photos=count(row.get("image_count")),
            images=[image] if image else [],
            views=count(row.get("views_count")),
            seller_id=str(row.get("member_id") or ""),
            seller_name=plain(row.get("member_display_name")),
            seller_url="",
            rating=number(row.get("member_rating_avg")),
            ratings=count(row.get("member_rating_count")),
            location=", ".join(
                filter(
                    None,
                    [
                        plain(row.get("nhood_label")),
                        plain(row.get("city_label")),
                    ],
                )
            ),
            published=publication(row.get("inserted_date")),
            posted_label=relative_label(row.get("posted_at")),
        )

        username = plain(row.get("member_user_name"))

        if username:
            locale = (
                "ar"
                if urlsplit(url).path.startswith("/ar/")
                else "en"
            )

            ad["seller_url"] = safe_url(
                f"/{locale}/mid/{username}",
                url,
            )

        ads.append(ad)

    if block["items"] and not ads:
        raise SourceError(
            "Карточки категории имеют неизвестную структуру."
        )

    next_path = data.get(
        "seoPage", {}
    ).get("nextPageUrl")

    next_url = (
        safe_url(next_path, url)
        if next_path
        else None
    )

    return ads, next_url


def parse_listing(raw, ad):
    soup = BeautifulSoup(raw, "html.parser")
    documents = []

    with suppress(SourceError):
        documents.append(props(soup))

    documents.extend(flight(soup))

    data = None

    for obj in walk(documents):
        candidate = obj.get("listingData")

        if (
            isinstance(candidate, dict)
            and str(
                candidate.get(
                    "commonInfo", {}
                ).get("postId")
            ) == ad["id"]
        ):
            data = candidate
            break

    if data is None:
        raise SourceError(
            "Не удалось прочитать данные объявления."
        )

    info = data["commonInfo"]
    owner = info.get("ownerData") or {}

    ad["title"] = (
        plain(info.get("topTitle"))
        or ad["title"]
    )

    ad["description"] = (
        plain(info.get("description"))
        or ad.get("description", "")
    )

    for target, key, convert in (
        ("seller_id", "id", str),
        ("seller_name", "fullName", plain),
        ("rating", "ratingAvg", number),
        ("ratings", "numberOfRatings", count),
        ("listings_count", "numberOfListings", count),
    ):
        if owner.get(key) is not None:
            ad[target] = convert(owner[key])

    if owner.get("memberLink"):
        ad["seller_url"] = safe_url(
            owner["memberLink"],
            ad["url"],
        )

    locations = {}

    for section in (
        info.get("basicInfo") or {}
    ).get("sections", []):
        for item in section.get("items", []):
            kind = item.get("key_type")
            value = plain(item.get("value"))

            if kind == "ListingPostDate" and value:
                ad["published"] = publication(value)

            if kind in {"Neighborhood", "City"} and value:
                locations[kind] = value

    if locations:
        ad["location"] = ", ".join(
            dict.fromkeys(
                locations[key]
                for key in ("Neighborhood", "City")
                if key in locations
            )
        )

    if not ad.get("published"):
        for key in (
            "datePublished",
            "publishedAt",
            "createdAt",
        ):
            if info.get(key):
                ad["published"] = publication(info[key])
                break

    gallery = info.get("gallery") or {}

    base = (
        data.get("config") or {}
    ).get("imagesBaseUrl") or CDN

    images = [
        photo_url(media.get("uri"), base)
        for media in gallery.get("media", [])
        if (
            isinstance(media, dict)
            and str(
                media.get("mimeType", "")
            ).startswith("image/")
        )
    ]

    ad["images"] = (
        list(
            dict.fromkeys(
                filter(None, images)
            )
        )
        or ad.get("images", [])
    )

    if (
        gallery.get("chips") or {}
    ).get("imagesCount") is not None:
        ad["photos"] = count(
            gallery["chips"]["imagesCount"]
        )

    for key in (
        "viewsCount",
        "views_count",
        "postViewsCount",
    ):
        if info.get(key) is not None:
            ad["views"] = count(info[key])
            break

    prices = (
        (
            data.get("listing") or {}
        ).get("price") or {}
    ).get("prices", [])

    if prices:
        ad["price"] = number(
            prices[0].get("price")
        )

        ad["currency"] = (
            plain(
                prices[0].get("key")
                or prices[0].get("currencyLabel")
            )
            or ad.get("currency", "")
        )

    return ad


class Reader:
    def __init__(self):
        self.http = httpx.AsyncClient(
            timeout=30,
            follow_redirects=False,
            headers={
                "User-Agent": "OpenSooqTelegramBot/2.0",
                "Accept-Language": "en",
            },
        )

        self.lock = asyncio.Lock()
        self.browser_lock = asyncio.Lock()

        self.last = 0.0
        self.pauses = {}
        self.cache = {}

        self.pw = None
        self.browser = None
        self.browser_context = None
        self.browser_failures = 0

    async def throttle(self):
        async with self.lock:
            await asyncio.sleep(
                max(
                    0,
                    self.last + 2 - time.monotonic(),
                )
            )

            self.last = time.monotonic()

    def status_error(self, status, headers, host):
        if status == 429:
            retry = headers.get("retry-after", "300")

            try:
                delay = float(retry)

            except ValueError:
                try:
                    delay = (
                        parsedate_to_datetime(
                            retry
                        ).timestamp()
                        - time.time()
                    )

                except (
                    ValueError,
                    TypeError,
                    OverflowError,
                ):
                    delay = 300

            self.pauses[host] = (
                time.monotonic()
                + max(60, min(3600, delay))
            )

            raise RateLimit(
                "OpenSooq ограничил запросы: HTTP 429."
            )

        if status != 200:
            raise SourceError(
                f"OpenSooq вернул HTTP {status}."
            )

    @staticmethod
    def check_html(raw):
        if re.search(
            r"<title>\s*(?:Just a moment|Access Denied|Attention Required)",
            raw[:20000],
            re.I,
        ):
            raise SourceError(
                "OpenSooq показал проверку доступа."
            )

    async def get(self, url):
        url = safe_url(url)

        for _ in range(6):
            host = urlsplit(url).hostname

            if self.pauses.get(host, 0) > time.monotonic():
                raise RateLimit(
                    "Пауза после ограничения OpenSooq "
                    "ещё не закончилась."
                )

            for attempt in range(3):
                await self.throttle()

                try:
                    async with self.http.stream(
                        "GET",
                        url,
                    ) as response:
                        body = bytearray()

                        async for chunk in response.aiter_bytes():
                            body.extend(chunk)

                            if len(body) > 8 * 1024 * 1024:
                                raise SourceError(
                                    "Слишком большой ответ OpenSooq."
                                )

                        raw = body.decode(
                            response.encoding or "utf-8",
                            errors="replace",
                        )

                    if (
                        response.status_code >= 500
                        and attempt < 2
                    ):
                        await asyncio.sleep(
                            2 ** (attempt + 1)
                        )
                        continue

                    break

                except httpx.RequestError:
                    if attempt == 2:
                        raise SourceError(
                            "OpenSooq не ответил вовремя."
                        ) from None

                    await asyncio.sleep(
                        2 ** (attempt + 1)
                    )

            if response.status_code in {
                301, 302, 303, 307, 308
            }:
                location = response.headers.get(
                    "location"
                )

                if not location:
                    raise SourceError(
                        "Перенаправление без адреса."
                    )

                url = safe_url(location, url)
                continue

            self.status_error(
                response.status_code,
                response.headers,
                host,
            )

            self.check_html(raw)

            return raw, url

        raise SourceError(
            "Слишком много перенаправлений."
        )

    async def browser_profile(self, url, seller_id):
        if not USE_BROWSER or self.browser_failures >= 3:
            raise SourceError(
                "Браузерная загрузка профилей "
                "недоступна в этой проверке."
            )

        from playwright.async_api import (
            async_playwright,
            TimeoutError as PlaywrightTimeout,
        )

        async with self.browser_lock:
            page = None

            try:
                if (
                    self.browser is None
                    or not self.browser.is_connected()
                ):
                    if self.pw is None:
                        self.pw = await async_playwright().start()

                    self.browser = await self.pw.chromium.launch(
                        headless=True,
                        args=["--disable-dev-shm-usage"],
                    )

                    self.browser_context = (
                        await self.browser.new_context(
                            locale="en-US"
                        )
                    )

                    async def lightweight(route):
                        if route.request.resource_type in {
                            "image",
                            "media",
                            "font",
                        }:
                            await route.abort()

                        else:
                            await route.continue_()

                    await self.browser_context.route(
                        "**/*",
                        lightweight,
                    )

                await self.throttle()

                page = await self.browser_context.new_page()

                try:
                    response = await page.goto(
                        safe_url(url),
                        timeout=25000,
                        wait_until="domcontentloaded",
                    )

                except PlaywrightTimeout:
                    # DOM может содержать данные и после тайм-аута.
                    response = None

                safe_url(page.url)

                if (
                    urlsplit(page.url).hostname
                    != urlsplit(url).hostname
                ):
                    raise SourceError(
                        "Профиль перенаправил на другую страну."
                    )

                if response is not None:
                    self.status_error(
                        response.status,
                        response.headers,
                        urlsplit(url).hostname,
                    )

                profile = None

                for attempt in range(4):
                    raw = await page.content()
                    self.check_html(raw)

                    profile = await asyncio.to_thread(
                        parse_profile,
                        raw,
                        seller_id,
                    )

                    if profile["seller_views"] is not None:
                        return profile

                    if attempt < 3:
                        await asyncio.sleep(1.5)

                if profile and any(
                    value is not None
                    for value in profile.values()
                ):
                    self.browser_failures += 1
                    return profile

                raise SourceError(
                    "Статистика отсутствует "
                    "в загруженном профиле."
                )

            except RateLimit:
                raise

            except Exception as exc:
                self.browser_failures += 1

                if isinstance(exc, SourceError):
                    raise

                log.warning(
                    "Браузер профиля: %s",
                    str(exc)[:1200],
                )

                raise SourceError(
                    "Не удалось загрузить профиль браузером; "
                    "подробности в логах."
                ) from None

            finally:
                if page is not None:
                    with suppress(Exception):
                        await page.close()

    async def profile(self, url, seller_id):
        key = (url, seller_id)
        cached = self.cache.get(key)

        if cached and cached[0] > time.monotonic():
            return cached[1], cached[2]

        profile = None
        issue = ""

        try:
            raw, _ = await self.get(url)

            profile = await asyncio.to_thread(
                parse_profile,
                raw,
                seller_id,
            )

        except RateLimit:
            raise

        except (SourceError, ValueError) as exc:
            issue = str(exc)

        if (
            profile is None
            or profile["seller_views"] is None
        ):
            try:
                rendered = await self.browser_profile(
                    url,
                    seller_id,
                )

                profile = profile or {}

                profile.update({
                    key: value
                    for key, value in rendered.items()
                    if value is not None
                })

            except RateLimit:
                raise

            except (
                SourceError,
                ValueError,
                ImportError,
            ) as exc:
                issue = issue or str(exc)

        if (
            profile
            and profile.get("seller_views") is not None
        ):
            issue = ""

        else:
            issue = (
                "Просмотры профиля недоступны: "
                + (
                    issue
                    or "счётчик не найден."
                )
            )

        ttl = 300 if not issue else 60

        self.cache[key] = (
            time.monotonic() + ttl,
            profile,
            issue,
        )

        if len(self.cache) > 2000:
            self.cache = {
                key: value
                for key, value in self.cache.items()
                if value[0] > time.monotonic()
            }

            self.cache = dict(
                list(self.cache.items())[-1000:]
            )

        return profile, issue

    async def enrich(self, ad):
        raw, final = await self.get(ad["url"])

        if (
            urlsplit(final).hostname
            != urlsplit(ad["url"]).hostname
        ):
            raise SourceError(
                "Объявление перенаправило на другую страну."
            )

        ad["url"] = final

        ad = await asyncio.to_thread(
            parse_listing,
            raw,
            ad,
        )

        if not ad.get("seller_url"):
            return (
                ad,
                "В объявлении отсутствует "
                "ссылка на профиль продавца.",
            )

        profile, warning = await self.profile(
            ad["seller_url"],
            ad["seller_id"],
        )

        if profile:
            ad.update({
                key: value
                for key, value in profile.items()
                if value is not None
            })

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

        return escape(
            f"{value:g}"
            if isinstance(value, float)
            else str(value)
        )

    description = (
        plain(ad.get("description"))
        or "Без описания"
    )

    if len(description) > 400:
        description = description[:397] + "..."

    timing = escape(
        ad.get("published")
        or ad.get("posted_label")
        or "нет данных"
    )

    extra_time = ""

    if ad.get("published") and ad.get("posted_label"):
        extra_time = (
            "• <b>Время в выдаче:</b> "
            f"{escape(ad['posted_label'])}\n"
        )

    seller = (
        ad.get("seller_name")
        or "Неизвестен"
    )[:60]

    return (
        f"<b>Объявление №{show('id')}</b>\n\n"
        f"📦 <b>{escape(ad['title'][:100])}</b>\n"
        f"🏷 <b>Цена:</b> {show('price')} "
        f"{escape(ad.get('currency', ''))}\n"
        f"📍 <b>Локация:</b> "
        f"{escape(ad.get('location') or 'Не указана')}\n"
        f"🕓 <b>Опубликовано:</b> {timing}\n"
        f"{extra_time}\n"
        f"📖 <b>Описание:</b>\n"
        f"<blockquote>{escape(description)}</blockquote>\n\n"
        f"💼 <b>Продавец:</b> {escape(seller)}\n\n"
        f"• <b>Фото:</b> {show('photos')}\n"
        f"• <b>Рейтинг:</b> {show('rating')} "
        f"(оценок: {show('ratings')})\n"
        f"• <b>Отзывов:</b> {show('reviews')}\n"
        f"• <b>Продано:</b> {show('sold')}\n"
        f"• <b>Просмотры профиля:</b> {show('seller_views')}\n"
        f"• <b>Активных объявлений:</b> {show('listings_count')}"
    )


async def telegram_call(method, **kwargs):
    try:
        return await method(**kwargs)

    except RetryAfter as exc:
        delay = (
            exc.retry_after.total_seconds()
            if hasattr(
                exc.retry_after,
                "total_seconds",
            )
            else float(exc.retry_after)
        )

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
/id — ваш Telegram ID

seller_views — просмотры профиля продавца
listings_count — активные объявления продавца

Для добавления категории отправьте её ссылку.
Повторная проверка сохраняет историю уже отправленных объявлений.
"""


def get_main_menu():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(
                "📊 Мои фильтры",
                callback_data="menu_filters",
            ),
            InlineKeyboardButton(
                "🔗 Категории",
                callback_data="menu_sources",
            ),
        ],
        [
            InlineKeyboardButton(
                "🚀 Начать парсинг",
                callback_data="menu_check",
            )
        ],
        [
            InlineKeyboardButton(
                "⚙️ Помощь",
                callback_data="menu_help",
            )
        ],
    ])


def filters_text(state):
    text = "\n".join(
        f"{key}={value}"
        for key, value in state["rules"].items()
    ) or "не заданы"

    return (
        "⚙️ <b>Текущие фильтры:</b>\n<pre>"
        + escape(text)
        + "</pre>\nИзменение: <code>/filters ...</code>"
    )


def report_text(
    stats,
    elapsed,
    outcome,
    warnings,
    missing,
):
    titles = {
        "complete": "✅ Проверка завершена",
        "partial": "⚠️ Проверка завершена с замечаниями",
        "error": "❌ Проверка прервана",
        "stopped": "⏸ Проверка остановлена",
        "limit": "⚠️ Достигнут лимит проверки",
    }

    text = (
        f"<b>{titles[outcome]}</b>\n\n"
        f"📄 Загружено страниц: {stats['pages']}\n"
        f"🔎 Найдено карточек: {stats['found']}\n"
        f"👀 Обработано новых: {stats['checked']}\n"
        f"✅ Отправлено объявлений: {stats['sent']}\n"
        f"🔄 Уже отправлялись: {stats['duplicates']}\n"
        f"🚫 Отсеяно фильтрами: {stats['filtered']}\n"
        f"⚠️ Ошибок: {stats['errors']}\n"
        f"👤 Карточек с неполной статистикой продавца: "
        f"{stats['profiles']}\n"
        f"⏱ Время: {round(elapsed)} сек."
    )

    if missing:
        names = {
            "seller_views": "просмотры профиля",
            "listings_count": "активные объявления",
        }

        text += (
            "\n\nНедоступные значения: "
            + escape(
                ", ".join(
                    names.get(key, key)
                    for key in sorted(missing)
                )
            )
        )

    if warnings:
        text += (
            "\n\n<b>Замечания:</b>\n"
            + "\n".join(
                "• " + escape(warning[:220])
                for warning in list(warnings)[:4]
            )
        )

    return text


class Service:
    def __init__(self, bot, allowed, path):
        self.bot = bot
        self.allowed = set(allowed)

        Path(path).parent.mkdir(
            parents=True,
            exist_ok=True,
        )

        DATA_DIR.mkdir(
            parents=True,
            exist_ok=True,
        )

        self.db = sqlite3.connect(path)
        self.db.row_factory = sqlite3.Row

        self.db.executescript("""
            PRAGMA journal_mode=WAL;

            CREATE TABLE IF NOT EXISTS users(
                chat INTEGER PRIMARY KEY,
                urls TEXT NOT NULL DEFAULT '[]',
                rules TEXT NOT NULL DEFAULT '{}',
                enabled INTEGER NOT NULL DEFAULT 0,
                minutes INTEGER NOT NULL DEFAULT 15,
                next_check REAL NOT NULL DEFAULT 0,
                last TEXT NOT NULL DEFAULT ''
            );

            CREATE TABLE IF NOT EXISTS delivered(
                chat INTEGER NOT NULL,
                key TEXT NOT NULL,
                PRIMARY KEY(chat, key)
            );

            CREATE TABLE IF NOT EXISTS authorized(
                chat INTEGER PRIMARY KEY
            );
        """)

        self.db.commit()

        self.allowed.update(
            row["chat"]
            for row in self.db.execute(
                "SELECT chat FROM authorized"
            )
        )

        self.reader = Reader()
        self.tasks = {}
        self.lock = asyncio.Lock()
        self.closing = False

    def permitted(self, chat):
        return (
            chat in self.allowed
            and not is_blocked(chat)
        )

    def authorize(self, chat):
        self.allowed.add(chat)

        with self.db:
            self.db.execute(
                "INSERT OR IGNORE INTO authorized VALUES (?)",
                (chat,),
            )

    def state(self, chat):
        with self.db:
            self.db.execute(
                "INSERT OR IGNORE INTO users(chat) VALUES (?)",
                (chat,),
            )

        row = dict(
            self.db.execute(
                "SELECT * FROM users WHERE chat=?",
                (chat,),
            ).fetchone()
        )

        row["urls"] = json.loads(row["urls"])
        row["rules"] = json.loads(row["rules"])

        return row

    def save(self, chat, **changes):
        allowed_fields = {
            "urls",
            "rules",
            "enabled",
            "minutes",
            "next_check",
            "last",
        }

        if (
            not changes
            or not changes.keys() <= allowed_fields
        ):
            raise ValueError(
                "Некорректные настройки."
            )

        values = [
            json.dumps(value, ensure_ascii=False)
            if key in {"urls", "rules"}
            else value
            for key, value in changes.items()
        ]

        with self.db:
            self.db.execute(
                "UPDATE users SET "
                + ",".join(
                    key + "=?"
                    for key in changes
                )
                + " WHERE chat=?",
                values + [chat],
            )

    def trigger(self, chat):
        if (
            self.closing
            or not self.permitted(chat)
            or not self.state(chat)["urls"]
        ):
            return False

        if (
            chat in self.tasks
            and not self.tasks[chat].done()
        ):
            return False

        self.save(
            chat,
            next_check=(
                time.time()
                + self.state(chat)["minutes"] * 60
            ),
        )

        self.tasks[chat] = asyncio.create_task(
            self.scan(chat)
        )

        return True

    async def tick(self, context):
        rows = list(
            self.db.execute(
                "SELECT chat FROM users "
                "WHERE enabled=1 AND next_check<=?",
                (time.time(),),
            )
        )

        for row in rows:
            self.trigger(row["chat"])

    async def cancel_scan(self, chat):
        task = self.tasks.get(chat)

        if task and not task.done():
            task.cancel()

            with suppress(asyncio.CancelledError):
                await task

    async def send(self, chat, ad):
        buttons = [[
            InlineKeyboardButton(
                "🔗 Ссылка на товар",
                url=ad["url"],
            )
        ]]

        if ad.get("seller_url"):
            buttons.append([
                InlineKeyboardButton(
                    "👤 Профиль продавца",
                    url=ad["seller_url"],
                )
            ])

        markup = InlineKeyboardMarkup(buttons)
        text = card(ad)

        size = len(
            BeautifulSoup(
                text,
                "html.parser",
            ).get_text().encode("utf-16-le")
        ) // 2

        if ad.get("images"):
            try:
                if size <= 1024:
                    await telegram_call(
                        self.bot.send_photo,
                        chat_id=chat,
                        photo=ad["images"][0],
                        caption=text,
                        parse_mode="HTML",
                        reply_markup=markup,
                    )
                    return

                await telegram_call(
                    self.bot.send_photo,
                    chat_id=chat,
                    photo=ad["images"][0],
                    caption=escape(ad["title"][:100]),
                    parse_mode="HTML",
                )

            except BadRequest as exc:
                log.warning(
                    "Не удалось отправить фото: %s",
                    exc,
                )

        await telegram_call(
            self.bot.send_message,
            chat_id=chat,
            text=text,
            parse_mode="HTML",
            reply_markup=markup,
        )

    async def scan(self, chat):
        stats = Counter()
        warnings = {}
        missing = set()
        seen = set()

        outcome = "complete"
        started = time.monotonic()
        stop = False
        report_allowed = True

        try:
            await telegram_call(
                self.bot.send_message,
                chat_id=chat,
                text="🚀 Начинаю проверку объявлений…",
            )

            async with self.lock:
                self.reader.browser_failures = 0

                for source in list(
                    self.state(chat)["urls"]
                ):
                    url = source
                    pages_seen = set()

                    for page_index in range(MAX_PAGES):
                        if (
                            stop
                            or source not in self.state(chat)["urls"]
                        ):
                            break

                        if not self.permitted(chat):
                            outcome = "stopped"
                            stop = True
                            break

                        if url in pages_seen:
                            warnings[
                                "Обнаружен повтор страницы категории."
                            ] = True
                            break

                        pages_seen.add(url)

                        try:
                            raw, final = await self.reader.get(url)

                            ads, next_url = await asyncio.to_thread(
                                parse_category,
                                raw,
                                final,
                            )

                            stats["pages"] += 1

                        except RateLimit as exc:
                            warnings[str(exc)] = True
                            stats["errors"] += 1
                            outcome = "partial"
                            stop = True
                            break

                        except (SourceError, ValueError) as exc:
                            warnings[str(exc)] = True
                            stats["errors"] += 1
                            outcome = "partial"
                            break

                        for ad in ads:
                            key = (
                                urlsplit(ad["url"]).hostname
                                + ":"
                                + ad["id"]
                            )

                            if key in seen:
                                continue

                            seen.add(key)
                            stats["found"] += 1

                            delivered = self.db.execute(
                                "SELECT 1 FROM delivered "
                                "WHERE chat=? AND key=?",
                                (chat, key),
                            ).fetchone()

                            if delivered:
                                stats["duplicates"] += 1
                                continue

                            if (
                                stats["checked"] >= MAX_ADS
                                or stats["sent"] >= MAX_SEND
                            ):
                                outcome = "limit"
                                stop = True
                                break

                            if (
                                source not in self.state(chat)["urls"]
                                or not self.permitted(chat)
                            ):
                                break

                            stats["checked"] += 1

                            if EXCLUDED_RE.search(ad["title"]):
                                stats["filtered"] += 1
                                continue

                            try:
                                ad, warning = await self.reader.enrich(ad)

                                absent_profile = {
                                    key
                                    for key in (
                                        "seller_views",
                                        "listings_count",
                                    )
                                    if ad.get(key) is None
                                }

                                missing.update(absent_profile)

                                if absent_profile:
                                    stats["profiles"] += 1

                                if warning:
                                    warnings[warning] = True

                                accepted, absent = matches(
                                    ad,
                                    self.state(chat)["rules"],
                                )

                                missing.update(absent)

                                if not accepted:
                                    stats["filtered"] += 1
                                    continue

                                await self.send(chat, ad)

                                with self.db:
                                    self.db.execute(
                                        "INSERT OR IGNORE "
                                        "INTO delivered VALUES (?,?)",
                                        (chat, key),
                                    )

                                stats["sent"] += 1
                                await asyncio.sleep(1.1)

                            except Forbidden:
                                raise

                            except RateLimit as exc:
                                warnings[str(exc)] = True
                                stats["errors"] += 1
                                outcome = "partial"
                                stop = True
                                break

                            except (
                                SourceError,
                                ValueError,
                                TelegramError,
                            ) as exc:
                                stats["errors"] += 1
                                warnings[str(exc)[:220]] = True

                                log.warning(
                                    "Объявление %s: %s",
                                    ad["id"],
                                    type(exc).__name__,
                                )

                            except Exception:
                                stats["errors"] += 1

                                warnings[
                                    "Ошибка обработки объявления; "
                                    "подробности в логах."
                                ] = True

                                log.exception(
                                    "Ошибка обработки объявления %s",
                                    ad["id"],
                                )

                        if stop or not next_url:
                            break

                        if (
                            urlsplit(next_url).hostname
                            != urlsplit(final).hostname
                        ):
                            warnings[
                                "Следующая страница "
                                "ведёт на другую страну."
                            ] = True

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

            warnings[
                "Ошибка проверки; подробности "
                "записаны в логах Render."
            ] = True

            log.exception(
                "Проверка прервана для chat=%s",
                chat,
            )

        finally:
            if outcome == "complete" and warnings:
                outcome = "partial"

            report = report_text(
                stats,
                time.monotonic() - started,
                outcome,
                warnings,
                missing,
            )

            with suppress(sqlite3.Error):
                self.save(
                    chat,
                    last=report,
                    next_check=(
                        time.time()
                        + self.state(chat)["minutes"] * 60
                    ),
                )

            if self.tasks.get(chat) is asyncio.current_task():
                self.tasks.pop(chat, None)

            if report_allowed and not self.closing:
                markup = InlineKeyboardMarkup([
                    [
                        InlineKeyboardButton(
                            "🔄 Перезапустить парсер",
                            callback_data="restart_scan",
                        )
                    ],
                    [
                        InlineKeyboardButton(
                            "🏠 Главное меню",
                            callback_data="menu_home",
                        )
                    ],
                ])

                try:
                    await telegram_call(
                        self.bot.send_message,
                        chat_id=chat,
                        text=report,
                        parse_mode="HTML",
                        reply_markup=markup,
                    )

                except Forbidden:
                    self.save(chat, enabled=0)

                except TelegramError:
                    log.exception(
                        "Не удалось доставить итоговый отчёт"
                    )

    async def close(self):
        self.closing = True
        tasks = list(self.tasks.values())

        for task in tasks:
            task.cancel()

        await asyncio.gather(
            *tasks,
            return_exceptions=True,
        )

        await self.reader.close()
        self.db.close()


async def handle(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
):
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat

    if (
        not message
        or not message.text
        or not user
        or not chat
        or chat.type != "private"
    ):
        return

    service = context.application.bot_data["service"]
    text = message.text.strip()
    parts = text.split(maxsplit=1)

    if not parts:
        return

    command = parts[0].split("@")[0].lower()
    argument = parts[1] if len(parts) > 1 else ""

    if is_blocked(user.id):
        await message.reply_text(
            "⛔ Вы заблокированы."
        )
        return

    if command == "/id":
        await message.reply_text(
            f"Ваш Telegram ID: {user.id}"
        )
        return

    try:
        if command in {
            "/admin",
            "/createpass",
            "/block",
            "/unblock",
        }:
            if user.id != ADMIN_ID:
                return

            if command == "/admin":
                await message.reply_text(
                    "👑 Админ-панель\n"
                    "/createpass ID — создать пароль\n"
                    "/block ID — заблокировать\n"
                    "/unblock ID — разблокировать"
                )
                return

            target = int(argument)

            if target <= 0:
                raise ValueError(
                    "Укажите положительный Telegram ID."
                )

            if command == "/createpass":
                password = "".join(
                    secrets.choice(
                        string.ascii_letters + string.digits
                    )
                    for _ in range(12)
                )

                save_user_password(
                    target,
                    password,
                )

                await message.reply_text(
                    f"Пароль для {target}: "
                    f"<code>{password}</code>",
                    parse_mode="HTML",
                )

            elif command == "/block":
                if target == ADMIN_ID:
                    raise ValueError(
                        "Нельзя заблокировать администратора."
                    )

                block_user(target)

                service.state(target)
                service.save(target, enabled=0)

                await service.cancel_scan(target)

                await message.reply_text(
                    f"Пользователь {target} заблокирован."
                )

            else:
                unblock_user(target)

                await message.reply_text(
                    f"Пользователь {target} разблокирован."
                )

            return

        if not service.permitted(user.id):
            if check_user_password(user.id, text):
                service.authorize(user.id)

                await message.reply_text(
                    "✅ Доступ открыт. "
                    "Отправьте ссылку на категорию.",
                    reply_markup=get_main_menu(),
                )

            else:
                await message.reply_text(
                    "🔒 Бот приватный. "
                    "Введите выданный пароль."
                )

            return

        state = service.state(chat.id)

        if command == "/start":
            await message.reply_text(
                "👋 Отправьте ссылку на категорию "
                "OpenSooq или выберите действие.",
                reply_markup=get_main_menu(),
            )

        elif command == "/help":
            await message.reply_text(HELP_TEXT)

        elif command in {"/filters", "/set"}:
            if argument:
                state["rules"] = update_filters(
                    state["rules"],
                    argument,
                )

                service.save(
                    chat.id,
                    rules=state["rules"],
                )

            await message.reply_text(
                filters_text(state),
                parse_mode="HTML",
            )

        elif command == "/reset":
            service.save(chat.id, rules={})

            await message.reply_text(
                "✅ Фильтры сброшены."
            )

        elif command == "/sources":
            sources = "\n".join(
                f"{index}. {url}"
                for index, url in enumerate(
                    state["urls"],
                    1,
                )
            )

            await message.reply_text(
                (
                    sources
                    or "Категории не добавлены. "
                    "Отправьте ссылку."
                )[:3900],
                disable_web_page_preview=True,
            )

        elif command == "/remove":
            index = int(argument) - 1

            if not 0 <= index < len(state["urls"]):
                raise ValueError(
                    "Нет категории с таким номером. "
                    "См. /sources."
                )

            state["urls"].pop(index)

            service.save(
                chat.id,
                urls=state["urls"],
            )

            await message.reply_text(
                "✅ Категория удалена."
            )

        elif command == "/interval":
            minutes = int(argument)

            if not 5 <= minutes <= 1440:
                raise ValueError(
                    "Интервал: 5–1440 минут."
                )

            service.save(
                chat.id,
                minutes=minutes,
                next_check=time.time() + minutes * 60,
            )

            await message.reply_text(
                f"Интервал: {minutes} мин."
            )

        elif command in {"/pause", "/stop"}:
            service.save(chat.id, enabled=0)

            await service.cancel_scan(chat.id)

            await message.reply_text(
                "⏸ Мониторинг остановлен."
            )

        elif command == "/status":
            active = (
                chat.id in service.tasks
                and not service.tasks[chat.id].done()
            )

            status = (
                f"Мониторинг: "
                f"{'включён' if state['enabled'] else 'выключен'}\n"
                f"Проверка: "
                f"{'выполняется' if active else 'не выполняется'}\n"
                f"Интервал: {state['minutes']} мин.\n"
                f"Категорий: {len(state['urls'])}\n\n"
            )

            await message.reply_text(
                escape(status)
                + (
                    state["last"]
                    or "Проверок ещё не было."
                ),
                parse_mode="HTML",
            )

        elif (
            command in {
                "/check",
                "/watch",
                "/restart",
                "/add",
            }
            or text.startswith(("https://", "http://"))
        ):
            if (
                command == "/add"
                or text.startswith(("https://", "http://"))
            ):
                url = safe_url(
                    argument
                    if command == "/add"
                    else text
                )

                if re.search(
                    r"/(?:search|lists)/\d+",
                    urlsplit(url).path,
                ):
                    raise ValueError(
                        "Нужна ссылка на категорию, "
                        "а не на отдельное объявление."
                    )

                if url not in state["urls"]:
                    if len(state["urls"]) >= 5:
                        raise ValueError(
                            "Максимум 5 категорий."
                        )

                    state["urls"].append(url)

                    service.save(
                        chat.id,
                        urls=state["urls"],
                    )

            if not state["urls"]:
                raise ValueError(
                    "Сначала добавьте категорию."
                )

            if command == "/watch":
                service.save(chat.id, enabled=1)

            if command == "/restart":
                await service.cancel_scan(chat.id)

            started = service.trigger(chat.id)

            await message.reply_text(
                "🚀 Проверка запущена."
                if started
                else "⏳ Проверка уже выполняется."
            )

        else:
            await message.reply_text(
                "Отправьте ссылку на категорию или /help."
            )

    except ValueError as exc:
        await message.reply_text(
            str(exc)[:800]
            or "Проверьте параметры команды: /help."
        )


async def button_handler(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
):
    query = update.callback_query
    user = update.effective_user
    chat = update.effective_chat

    service = context.application.bot_data["service"]

    if (
        not query
        or not user
        or not chat
        or chat.type != "private"
        or not service.permitted(user.id)
    ):
        if query:
            await query.answer(
                "Доступ закрыт.",
                show_alert=True,
            )

        return

    await query.answer()

    state = service.state(chat.id)
    data = query.data

    if data in {"menu_check", "restart_scan"}:
        if not state["urls"]:
            await query.message.reply_text(
                "Сначала добавьте категорию.",
                reply_markup=get_main_menu(),
            )
            return

        if data == "restart_scan":
            await service.cancel_scan(chat.id)

        started = service.trigger(chat.id)

        await query.message.reply_text(
            "🚀 Проверка запущена."
            if started
            else "⏳ Проверка уже выполняется."
        )

    elif data == "menu_filters":
        await query.message.reply_text(
            filters_text(state),
            parse_mode="HTML",
            reply_markup=get_main_menu(),
        )

    elif data == "menu_sources":
        text = "\n".join(
            f"{index}. {url}"
            for index, url in enumerate(
                state["urls"],
                1,
            )
        ) or "Категории не добавлены. Отправьте ссылку."

        await query.message.reply_text(
            text[:3900],
            disable_web_page_preview=True,
            reply_markup=get_main_menu(),
        )

    elif data == "menu_help":
        await query.message.reply_text(
            HELP_TEXT,
            reply_markup=get_main_menu(),
        )

    else:
        await query.message.reply_text(
            "Выберите действие:",
            reply_markup=get_main_menu(),
        )


def build_app(token, allowed, database):
    async def setup(app):
        service = Service(
            app.bot,
            allowed,
            database,
        )

        app.bot_data["service"] = service

        if os.getenv("PORT"):
            class HealthHandler(BaseHTTPRequestHandler):
                def do_GET(self):
                    self.send_response(
                        200
                        if self.path in {"/", "/healthz"}
                        else 404
                    )

                    self.end_headers()
                    self.wfile.write(b"ok")

                def log_message(self, *args):
                    pass

            server = ThreadingHTTPServer(
                (
                    "0.0.0.0",
                    int(os.environ["PORT"]),
                ),
                HealthHandler,
            )

            threading.Thread(
                target=server.serve_forever,
                daemon=True,
            ).start()

            app.bot_data["health_server"] = server

        if app.job_queue is None:
            raise RuntimeError(
                "Установите python-telegram-bot "
                "с дополнением [job-queue]."
            )

        app.job_queue.run_repeating(
            service.tick,
            interval=15,
            first=5,
        )

        await app.bot.set_my_commands([
            BotCommand("start", "Меню"),
            BotCommand("check", "Проверить объявления"),
            BotCommand("restart", "Перезапустить проверку"),
            BotCommand("pause", "Остановить"),
            BotCommand("status", "Статус и отчёт"),
            BotCommand("help", "Справка"),
            BotCommand("id", "Мой ID"),
        ])

    async def cleanup(app):
        server = app.bot_data.pop(
            "health_server",
            None,
        )

        if server:
            await asyncio.to_thread(
                server.shutdown
            )

            server.server_close()

        service = app.bot_data.pop(
            "service",
            None,
        )

        if service:
            await service.close()

    async def on_error(update, context):
        error = context.error

        log.error(
            "Ошибка обработчика: %s",
            type(error).__name__,
            exc_info=(
                type(error),
                error,
                error.__traceback__,
            ),
        )

    app = (
        Application.builder()
        .token(token)
        .concurrent_updates(False)
        .post_init(setup)
        .post_stop(cleanup)
        .post_shutdown(cleanup)
        .build()
    )

    app.add_handler(
        MessageHandler(
            filters.ChatType.PRIVATE & filters.TEXT,
            handle,
        )
    )

    app.add_handler(
        CallbackQueryHandler(button_handler)
    )

    app.add_error_handler(on_error)

    return app


if __name__ == "__main__":
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(message)s",
    )

    logging.getLogger("httpx").setLevel(
        logging.WARNING
    )

    logging.getLogger("httpcore").setLevel(
        logging.WARNING
    )

    token = os.getenv("BOT_TOKEN", "").strip()

    if not token:
        raise SystemExit(
            "Задайте BOT_TOKEN в Environment на Render."
        )

    allowed = {ADMIN_ID} | {
        int(value.strip())
        for value in os.getenv(
            "ALLOWED_TELEGRAM_IDS",
            "",
        ).split(",")
        if value.strip()
    }

    build_app(
        token,
        allowed,
        DATABASE,
    ).run_polling(
        allowed_updates=[
            "message",
            "callback_query",
        ]
    )
from __future__ import annotations
import asyncio
import base64
from io import BytesIO
import hashlib
import hmac
import json
import logging
import math
import os
import re
import secrets
import signal
import shlex
import shutil
import socket
import sqlite3
import string
import sys
import tempfile
import time
import unicodedata
from collections import Counter
from contextlib import suppress
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
from email.utils import parsedate_to_datetime
from html import escape
from pathlib import Path
from urllib.parse import parse_qsl, unquote, urlencode, urljoin, urlsplit, urlunsplit
from zoneinfo import ZoneInfo
import httpx
from bs4 import BeautifulSoup
from dotenv import load_dotenv
from telegram import BotCommand, BotCommandScopeChat, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Update
from telegram.error import BadRequest, Forbidden, RetryAfter, TelegramError
from telegram.ext import Application, MessageHandler, CallbackQueryHandler, filters, ContextTypes
load_dotenv()
ADMIN_ID = int(os.getenv('ADMIN_ID', '1110325917'))
DATABASE = Path(os.getenv('DATABASE_PATH', '/var/data/bot.sqlite3' if os.getenv('RENDER') == 'true' else 'bot.sqlite3'))
DATA_DIR = Path(os.getenv('DATA_DIR', str(DATABASE.parent)))
PASSWORD_FILE = DATA_DIR / 'passwords.json'
BLOCKED_FILE = DATA_DIR / 'blocked.txt'
DISPLAY_TZ = ZoneInfo(os.getenv('APP_TIMEZONE', 'Europe/Moscow'))
USE_BROWSER = os.getenv('PROFILE_BROWSER', '1') == '1'
SUBSCRIPTIONS_ENABLED = False
REQUEST_INTERVAL = float(os.getenv('REQUEST_INTERVAL', '1.0'))
if not math.isfinite(REQUEST_INTERVAL) or not 1 <= REQUEST_INTERVAL <= 30:
    raise ValueError('REQUEST_INTERVAL: число от 1 до 30 секунд.')
COUNTRIES = 'kw ae bh sa jo'.split()
HOSTS = {'opensooq.com', 'www.opensooq.com'} | {c + '.opensooq.com' for c in COUNTRIES}
MAX_PAGES, MAX_ADS, MAX_SEND = (20, 1000, 200)
CDN = 'https://opensooq-imagesv2.os-cdn.com/previews/700x0/'
log = logging.getLogger('opensooq')
EXCLUDED_WORDS = ['car', 'cars', 'auto', 'autos', 'kia', 'gmc', 'toyota', 'nissan', 'chevrolet', 'ford', 'bmw', 'mercedes', 'audi', 'hyundai', 'apartment', 'flat', 'real estate', 'rent', 'rental', 'delivery', 'service', 'job', 'vacancy', 'سيارة', 'سيارات', 'شقة', 'شقق', 'عقار', 'ايجار', 'تأجير', 'خدمة', 'وظيفة']
EXCLUDED_RE = re.compile('(?<!\\w)(?:' + '|'.join((re.escape(w) for w in EXCLUDED_WORDS)) + ')(?!\\w)', re.I)
EXCLUDED_CATEGORY_PREFIXES = ('autos', 'vehicles', 'cars', 'realestate', 'propertyfor', 'propertiesfor', 'services', 'jobs', 'jobopenings', 'jobseekers', 'employment')
TOPIC_FALLBACK_RE = re.compile('(?<!\\w)(?:cars?\\s+for\\s+(?:sale|rent)|(?:apartment|flat|villa|room|warehouse)s?\\s+for\\s+(?:rent|sale)|لل(?:ايجار|تاجير)|سيارات?|شقق?|عقارات?|فلل|فيلا|جيب|مستودعات?|وظائف|وظيفة|خدمات)(?!\\w)', re.I)
FILTER_LABELS = {'price': 'Цена', 'seller_views': 'Просмотры продавца', 'listings_count': 'Активные объявления продавца', 'rating': 'Рейтинг продавца', 'ratings': 'Количество оценок', 'reviews': 'Отзывы', 'sold': 'Продано', 'photos': 'Количество фото', 'views': 'Просмотры объявления'}
METRICS = frozenset(FILTER_LABELS)
TEXT_LABELS = {'keywords': 'Искать слова', 'exclude': 'Исключить слова', 'currency': 'Валюта'}
COUNTRY_LABELS = {'kw': '🇰🇼 Кувейт', 'ae': '🇦🇪 ОАЭ', 'bh': '🇧🇭 Бахрейн', 'sa': '🇸🇦 Саудовская Аравия', 'jo': '🇯🇴 Иордания'}
SECRET_ENV_KEYS = ('BOT_TOKEN', 'OPENSOOQ_PROXY_URL')
SECRET_RE = re.compile('(?:bot\\d+:[A-Za-z0-9_-]+|Bearer\\s+\\S+|https?://[^\\s/@]+:[^\\s/@]+@[^\\s]+)')

def category_codes(value):
    if not isinstance(value, dict):
        return ('', '')

    def first(keys):
        return next((value[k].strip() for k in keys if isinstance(value.get(k), str) and value[k].strip()), '')
    res = [first(('cat1_code', 'categoryReportingName', 'category_reporting_name', 'category_code', 'cat_code')), first(('cat2_code', 'subCategoryReportingName', 'subcategory_reporting_name', 'subcategory_code'))]
    return (res[0], res[1]) if len(res) >= 2 else ('', '')

def excluded_topic(ad):
    codes = [re.sub('[^a-z0-9]', '', str(ad.get(k) or '').lower()) for k in ('category_code', 'subcategory_code')]
    if codes[0].startswith(EXCLUDED_CATEGORY_PREFIXES):
        return 'category:' + codes[0]
    if codes[0] in {'mobiletablet', 'electronics', 'fashionandkids', 'homeandfurniture', 'businessindustrial'}:
        return ''
    if codes[1].startswith(EXCLUDED_CATEGORY_PREFIXES):
        return 'category:' + codes[1]
    title = unicodedata.normalize('NFKC', str(ad.get('title') or ''))
    title = re.sub('[\\u064b-\\u065f\\u0670ـ]', '', title)
    title = title.translate(str.maketrans({'أ': 'ا', 'إ': 'ا', 'آ': 'ا'}))
    if EXCLUDED_RE.search(title) or TOPIC_FALLBACK_RE.search(title):
        return 'title'
    return ''

class SourceError(Exception):

    def __init__(self, message, *, reason='', status=None):
        super().__init__(message)
        self.reason, self.status = (reason, status)

class RateLimit(SourceError):
    pass

def proxy_settings(value):
    value = value.strip()
    if not value:
        return (None, None)
    try:
        parsed = urlsplit(value)
        if parsed.scheme not in {'http', 'https'} or not parsed.hostname or (not parsed.port) or parsed.query or parsed.fragment or (parsed.path not in {'', '/'}) or any((char.isspace() for char in value)):
            raise ValueError()
        hostname = parsed.hostname
        if ':' in hostname:
            hostname = '[' + hostname + ']'
        browser = {'server': f'{parsed.scheme}://{hostname}:{parsed.port}'}
        if parsed.username is not None:
            browser['username'] = unquote(parsed.username)
        if parsed.password is not None:
            browser['password'] = unquote(parsed.password)
        return (value, browser)
    except ValueError:
        raise ValueError('OPENSOOQ_PROXY_URL: нужен HTTP URI вида http://USER:PASS@HOST:PORT.') from None

def load_proxy_config():
    """Saved runtime choices override initial environment configuration."""
    path = DATA_DIR / 'proxies.json'
    try:
        config = json.loads(path.read_text(encoding='utf-8'))
    except FileNotFoundError:
        return None
    except (ValueError, OSError):
        raise ValueError('Не удалось прочитать сохранённые прокси в DATA_DIR/proxies.json.') from None
    try:
        pool = config['pool']
        active = config['active']
        if not isinstance(pool, list) or not 1 <= len(pool) <= 11 or type(active) is not int or (not 0 <= active < len(pool)):
            raise ValueError()
        parsed = [proxy_settings(value)[0] for value in pool]
        if not all(parsed) or len(set(parsed)) != len(parsed):
            raise ValueError()
    except (ValueError, TypeError, KeyError, AttributeError):
        raise ValueError('Некорректные сохранённые настройки прокси. Проверьте DATA_DIR/proxies.json.') from None
    return (parsed, active)

def save_proxy_config(pool, active):
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(dir=DATA_DIR, prefix='.proxies-')
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as stream:
            json.dump({'pool': pool, 'active': active}, stream)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, DATA_DIR / 'proxies.json')
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)

def proxy_label(uri):
    if not uri:
        return 'Прямое соединение'
    parsed = urlsplit(uri)
    return f'{parsed.hostname}:{parsed.port}'

def error_text(error):
    text = str(error)
    for key in SECRET_ENV_KEYS:
        secret = os.getenv(key, '').strip()
        if secret:
            text = text.replace(secret, '[hidden]')
    with suppress(ValueError):
        parsed = urlsplit(os.getenv('OPENSOOQ_PROXY_URL', ''))
        for secret in (parsed.password, parsed.username):
            if secret:
                text = text.replace(secret, '[hidden]').replace(unquote(secret), '[hidden]')
    return SECRET_RE.sub('[hidden]', text)

def safe_url(value, base=''):
    value = urljoin(base, str(value).strip())
    try:
        u = urlsplit(value)
        if len(value) > 8192 or '\\' in value or any((ord(c) < 32 for c in value)) or (u.scheme not in {'http', 'https'}) or (u.hostname not in HOSTS) or u.username or u.password or (u.port not in {None, 80, 443}):
            raise ValueError()
    except ValueError:
        raise ValueError('Нужна веб-ссылка на категорию OpenSooq.') from None
    return urlunsplit(('https', u.hostname, u.path or '/', u.query, ''))

def photo_url(value, base=CDN):
    if not isinstance(value, str) or not value:
        return ''
    if value.startswith('//'):
        value = 'https:' + value
    if not value.startswith(('https://', 'http://', '//')):
        value = urljoin(base.replace('{size}', '700x0'), value)
        if value.lower().endswith(('.jpg', '.jpeg', '.png')):
            value += '.webp'
    u = urlsplit(value)
    if u.scheme not in {'http', 'https'} or not u.hostname or (not (u.hostname.endswith('.os-cdn.com') or u.hostname in HOSTS)) or u.username or u.password or (u.port not in {None, 80, 443}):
        return ''
    return urlunsplit(('https', u.hostname, u.path, u.query, ''))

def number(value):
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        if value >= 0 and math.isfinite(value):
            return float(value)
        return None
    text = ''.join((str(unicodedata.digit(c)) if c.isdecimal() else c for c in str(value)))
    text = text.replace('٬', '').replace('٫', '.').replace(',', '').replace('\u200f', '').replace('\u200e', '')
    text = re.sub('(?<=\\d)\\s+(?=\\d)', '', text)
    match = re.search('(\\d+(?:\\.\\d+)?)(?:\\s*(k|m|b|ألف|الف|مليون)(?!\\w))?', text, re.I)
    if not match or text.lstrip().startswith('-'):
        return None
    scales = {'k': 1000, 'm': 1000000, 'b': 1000000000, 'ألف': 1000, 'الف': 1000, 'مليون': 1000000}
    result = float(match[1]) * scales.get((match[2] or '').lower(), 1)
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
    tag = soup.find('script', id='__NEXT_DATA__')
    if not tag:
        return {}
    try:
        return json.loads(tag.string or tag.get_text())['props']['pageProps']
    except (ValueError, KeyError, TypeError):
        raise SourceError('Изменились данные страницы OpenSooq.') from None

def flight(soup):
    chunks, result = ([], [])
    for tag in soup.find_all('script', src=False):
        text = tag.string or tag.get_text()
        for match in re.finditer('(?:self\\.)?__next_f\\.push\\(', text):
            try:
                data, _ = json.JSONDecoder().raw_decode(text[match.end():])
                if isinstance(data, list) and len(data) > 1 and (data[0] == 1) and isinstance(data[1], str):
                    chunks.append(data[1])
            except ValueError:
                pass
    for line in ''.join(chunks).splitlines():
        key, separator, value = line.partition(':')
        if separator and re.fullmatch('[0-9a-fA-F]+', key) and (value[:1] in {'{', '['}):
            with suppress(ValueError):
                result.append(json.loads(value))
    return result

def plain(value):
    if isinstance(value, dict):
        for key in ('content', 'text', 'value'):
            if key in value:
                return plain(value[key])
        return ''
    if isinstance(value, list):
        return '\n'.join(filter(None, (plain(v) for v in value)))
    return '' if value is None else str(value).strip()

def registration_date(value):
    text = unicodedata.normalize('NFKC', plain(value))
    text = ''.join((str(unicodedata.digit(c)) if c.isdecimal() else c for c in text))
    for pattern, fmt in (('(?<!\\d)\\d{4}-\\d{2}-\\d{2}(?!\\d)', '%Y-%m-%d'), ('(?<!\\d)\\d{2}-\\d{2}-\\d{4}(?!\\d)', '%d-%m-%Y'), ('(?<!\\d)\\d{2}/\\d{2}/\\d{4}(?!\\d)', '%d/%m/%Y'), ('(?<!\\d)\\d{2}\\.\\d{2}\\.\\d{4}(?!\\d)', '%d.%m.%Y')):
        match = re.search(pattern, text)
        if match:
            with suppress(ValueError):
                return datetime.strptime(match[0], fmt).strftime('%d.%m.%Y')
    for fmt in ('%d %B %Y', '%d %b %Y', '%B %d, %Y', '%b %d, %Y', '%B %Y', '%b %Y'):
        candidate = re.sub('^(?:Member\\s+Since|Joined|Registered)\\s*:?\\s*', '', text, flags=re.I).strip()
        with suppress(ValueError):
            parsed = datetime.strptime(candidate, fmt)
            return parsed.strftime('%m.%Y' if '%d' not in fmt else '%d.%m.%Y')
    if re.fullmatch('(?:Member\\s+Since\\s*:?\\s*)?(?:19|20)\\d{2}', text, re.I):
        return text[-4:]
    return ''

def seller_keys(ad):
    keys = []
    seller_id = str(ad.get('seller_id') or '').strip()
    if seller_id and seller_id != '0':
        keys.append(f'id:{seller_id}')
    if ad.get('seller_url'):
        with suppress(ValueError):
            profile = urlsplit(safe_url(ad['seller_url'], ad['url']))
            keys.append(f"{profile.hostname}:url:{unquote(profile.path).rstrip('/')}")
    return keys

def rules_key(rules):
    normalized = {k: int(v) if isinstance(v, float) and v.is_integer() else v for k, v in rules.items()}
    return hashlib.sha256(('filter-v2:' + json.dumps(normalized, sort_keys=True, ensure_ascii=False)).encode()).hexdigest()

def recent_source(url):
    parsed = urlsplit(safe_url(url))
    query = [(k, v) for k, v in parse_qsl(parsed.query, keep_blank_values=True) if k not in {'page', 'sort_code'}]
    query.append(('sort_code', 'recent'))
    return safe_url(urlunsplit((parsed.scheme, parsed.netloc, parsed.path, urlencode(query), '')))

def parse_profile(raw, expected_id):
    soup = BeautifulSoup(raw, 'html.parser')
    result = {key: None for key in ('rating', 'ratings', 'reviews', 'seller_views', 'sold', 'listings_count', 'seller_registered')}

    def put(key, value, convert=count):
        if result[key] is None and value is not None:
            result[key] = convert(value)
    documents = []
    with suppress(SourceError):
        documents.append(props(soup))
    documents.extend(flight(soup))
    members = []
    for obj in walk(documents):
        member = obj.get('member')
        if isinstance(member, dict) and any((key in member for key in ('views_count', 'views', 'posts_count', 'member_info', 'rating', 'member_since'))):
            members.append(member)
    expected_id = str(expected_id).strip() if expected_id is not None else ''
    if expected_id:
        matching = [m for m in members if str(m.get('id')) == expected_id]
        without_id = [m for m in members if m.get('id') is None]
        if matching:
            members = matching
        elif without_id:
            members = without_id
        elif members:
            raise SourceError('Открыт профиль другого продавца.')
    for member in members:
        for field in ('member_since', 'registration_date', 'registered_at', 'joined_at'):
            registered = registration_date(member.get(field))
            if registered and result['seller_registered'] is None:
                result['seller_registered'] = registered
        put('seller_views', member.get('views_count'))
        put('seller_views', member.get('views'))
        rating = member.get('rating')
        if isinstance(rating, dict):
            put('rating', rating.get('average_rating'), number)
            put('ratings', rating.get('number_of_rating'))
            put('reviews', rating.get('number_of_reviews'))
        info = member.get('member_info')
        if isinstance(info, dict):
            put('sold', info.get('sold_listings_count'))
    for tag in soup(['script', 'style', 'template', 'noscript']):
        tag.decompose()

    def clean_text(value):
        value = unicodedata.normalize('NFKC', value)
        value = re.sub('[\\u064b-\\u065f\\u0670\\u200e\\u200f\\u061c]', '', value)
        return re.sub('\\s+', ' ', value).strip()
    numeric = '\\d[\\d.,٬٫]*(?: \\d{3})*(?:\\s*(?:[kmb]|ألف|الف|مليون))?'
    view_label = '(?:Views?|مشاهدة|مشاهدات|المشاهدات)'
    follower_label = '(?:Followers?|المتابعون|المتابعين|متابعون|متابعين|متابع)'
    if result['seller_views'] is None:
        for node in soup.find_all(string=re.compile(view_label, re.I)):
            parent = node.parent
            for _ in range(3):
                if parent is None:
                    break
                text = clean_text(parent.get_text(' ', strip=True))
                if len(text) > 350:
                    break
                match = re.search(f'({numeric})\\s*{view_label}\\b', text, re.I)
                if match and re.search(follower_label, text, re.I):
                    put('seller_views', match.group(1))
                    if result['seller_views'] is not None:
                        break
                if not match and re.search(follower_label, text, re.I):
                    match = re.search(f'\\b{view_label}\\s*:\\s*({numeric})(?![\\w.,٬٫])', text, re.I)
                    if match:
                        put('seller_views', match.group(1))
                        if result['seller_views'] is not None:
                            break
                parent = parent.parent
            if result['seller_views'] is not None:
                break
    tab_labels = {'listings_count': '(?:Live\\s+Listings?|(?:الإعلانات|الاعلانات)\\s+(?:الفعاله|الفعالة|النشطة))', 'sold': '(?:Sold\\s+Listings?|(?:الإعلانات|الاعلانات)\\s+المباعة)'}
    for tab in soup.select("li, a, button, [role='tab']"):
        text = clean_text(tab.get_text(' ', strip=True))
        if len(text) > 150:
            continue
        for key, label in tab_labels.items():
            if result[key] is None:
                match = re.fullmatch(f'{label}\\s*[（(]\\s*({numeric})\\s*[)）]', text, re.I)
                if match:
                    put(key, match.group(1))
    page_text = clean_text(soup.get_text(' ', strip=True))
    if result['seller_registered'] is None:
        match = re.search('(?:Member\\s+Since|Joined|Registered|عضو\\s+منذ|تاريخ\\s+التسجيل|تاريخ\\s+الانضمام)\\s*:?\\s*([^|•]{1,55})', page_text, re.I)
        if match:
            result['seller_registered'] = registration_date(match[1]) or None
    if result['reviews'] is None:
        match = re.search('(?:\\(|^|\\s)(\\d+)\\s*(?:reviews?|تقييمات|مراجعات)', page_text, re.I)
        if match:
            put('reviews', match.group(1))
    if result['rating'] is None:
        match = re.search('(\\d[.٫]\\d+)\\s*(?:★|stars?|نجوم)', page_text, re.I)
        if match:
            put('rating', match.group(1), number)
    return result

def update_filters(current, text):
    result = dict(current)
    for pair in shlex.split(text):
        key, separator, value = pair.partition('=')
        metric, _, bound = key.rpartition('_')
        if not separator or (key not in {'keywords', 'exclude', 'currency', 'unknown'} and (not (metric in METRICS and bound in {'min', 'max'}))):
            raise ValueError(f'Неизвестный фильтр: {pair[:60]}')
        if value.lower() in {'off', 'none'}:
            result.pop(key, None)
        elif key in {'keywords', 'exclude'}:
            if len(value) > 500 or not any((x.strip() for x in value.split(','))):
                raise ValueError('Укажите слова через запятую.')
            result[key] = value
        elif key == 'currency':
            if not re.fullmatch('[A-Za-z]{3}', value):
                raise ValueError('Валюта: код из 3 букв.')
            result[key] = value.upper()
        elif key == 'unknown':
            if value not in {'include', 'exclude'}:
                raise ValueError('unknown: только include или exclude.')
            result[key] = value
        else:
            number_value = float(value.replace(',', '.'))
            if not math.isfinite(number_value) or number_value < 0 or (metric == 'rating' and number_value > 5):
                raise ValueError('Числа должны быть неотрицательными.')
            if metric not in {'price', 'rating'} and (not number_value.is_integer()):
                raise ValueError('Счётчики должны быть целыми.')
            result[key] = number_value
    for metric in METRICS:
        if result.get(metric + '_min', 0) > result.get(metric + '_max', math.inf):
            raise ValueError(f'{metric}_min больше {metric}_max.')
    return result

def matches(ad, rules):
    text = (ad['title'] + '\n' + ad.get('description', '')).casefold()

    def terms(name):
        return [v.strip().casefold() for v in rules.get(name, '').split(',') if v.strip()]
    if terms('keywords') and (not any((v in text for v in terms('keywords')))):
        return (False, set())
    if any((v in text for v in terms('exclude'))):
        return (False, set())
    missing = set()
    accepted = True
    if rules.get('currency'):
        if not ad.get('currency'):
            missing.add('currency')
        elif ad['currency'] != rules['currency']:
            accepted = False
    for metric in METRICS:
        low, high = (rules.get(metric + '_min'), rules.get(metric + '_max'))
        if low is None and high is None:
            continue
        value = ad.get(metric)
        if value is None:
            missing.add(metric)
        elif low is not None and value < low or (high is not None and value > high):
            accepted = False
    allow_missing = not missing or rules.get('unknown') == 'include'
    return (accepted and allow_missing, missing)

def _load_passwords():
    try:
        return json.loads(PASSWORD_FILE.read_text(encoding='utf-8'))
    except (FileNotFoundError, ValueError):
        return {}

def _save_passwords(data):
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=DATA_DIR, prefix='.pw-')
    try:
        os.fchmod(fd, 384)
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            json.dump(data, f)
        os.replace(tmp, PASSWORD_FILE)
    finally:
        with suppress(FileNotFoundError):
            os.unlink(tmp)

def save_user_password(user_id, password):
    data = _load_passwords()
    data[str(user_id)] = password
    _save_passwords(data)

def remove_user_password(user_id):
    data = _load_passwords()
    data.pop(str(user_id), None)
    _save_passwords(data)

def check_user_password(user_id, password):
    return hmac.compare_digest(_load_passwords().get(str(user_id), ''), password)

def _blocked_set():
    if not BLOCKED_FILE.exists():
        return set()
    return {line.strip() for line in BLOCKED_FILE.read_text(encoding='utf-8').splitlines() if line.strip()}

def is_blocked(user_id):
    return str(user_id) in _blocked_set()

def block_user(user_id):
    if not is_blocked(user_id):
        with open(BLOCKED_FILE, 'a', encoding='utf-8') as f:
            f.write(f'{user_id}\n')

def unblock_user(user_id):
    lines = _blocked_set() - {str(user_id)}
    BLOCKED_FILE.write_text(''.join((f'{u}\n' for u in sorted(lines))), encoding='utf-8')

def publication(value):
    text = plain(value)
    if not text:
        return ''
    for fmt in ('%d-%m-%Y', '%d/%m/%Y', '%Y-%m-%d'):
        try:
            return datetime.strptime(text, fmt).strftime('%d.%m.%Y')
        except ValueError:
            pass
    try:
        dt = datetime.fromisoformat(text.replace('Z', '+00:00'))
        if dt.tzinfo is not None:
            dt = dt.astimezone(DISPLAY_TZ)
            return dt.strftime('%d.%m.%Y %H:%M %Z')
        return dt.strftime('%d.%m.%Y %H:%M') + ' (часовой пояс не указан)'
    except ValueError:
        return text[:100]

def relative_label(value):
    text = plain(value).split('•', 1)[0].strip()
    if text.lower() in {'today', 'yesterday', 'just now'}:
        return {'today': 'Сегодня', 'yesterday': 'Вчера', 'just now': 'Только что'}[text.lower()]
    match = re.fullmatch('(\\d+)\\s*(minutes?|mins?|hours?|hrs?|days?)\\s+ago', text, re.I)
    if match:
        unit = match[2].lower()
        label = 'мин.' if unit.startswith('m') else 'ч.' if unit.startswith('h') else 'дн.'
        return f'{match[1]} {label} назад'
    return text[:100]

def next_category_url(data, block, url):
    next_path = (data.get('seoPage') or {}).get('nextPageUrl')
    if next_path:
        return safe_url(next_path, url)
    meta = block.get('meta') or {}
    if not isinstance(meta, dict) or not block.get('items'):
        return None
    current = count(meta.get('current_page'))
    pages = count(meta.get('pages'))
    if current is None or pages is None or (not 1 <= current < pages):
        return None
    parsed = urlsplit(safe_url(url))
    query = [(key, value) for key, value in parse_qsl(parsed.query, keep_blank_values=True) if key != 'page']
    query.append(('page', str(current + 1)))
    return safe_url(urlunsplit((parsed.scheme, parsed.netloc, parsed.path, urlencode(query), '')))

def parse_category_dom(soup, url, documents):
    section = soup.select_one("section[data-testid='serp-results']")
    if section is None:
        raise SourceError('Не найдены данные категории OpenSooq.')
    metadata = {}
    for obj in walk(documents):
        listing = obj.get('listings')
        if isinstance(listing, dict) and isinstance(listing.get('items'), list):
            for item in listing['items']:
                post = item.get('post') if isinstance(item, dict) else None
                if isinstance(post, dict) and post.get('id'):
                    metadata[str(post['id'])] = post
    ads, seen = ([], set())
    cards = section.select('a.postListItemData[data-id1][href]')
    for node in cards:
        ad_id = str(node.get('data-id1', ''))
        heading = node.find(['h2', 'h3'])
        if not ad_id.isdecimal() or heading is None or ad_id in seen:
            continue
        ad_url = safe_url(node['href'], url)
        if not re.search('/(?:search|lists)/' + re.escape(ad_id) + '(?:/|$)', urlsplit(ad_url).path):
            continue
        seen.add(ad_id)
        post = metadata.get(ad_id, {})
        cat_data = category_codes(post)
        main_category, subcategory = (cat_data[0], cat_data[1])
        price_node = heading.find_previous_sibling('span')
        price_text = price_node.get_text(' ', strip=True) if price_node else ''
        currency_match = re.search('\\b([A-Z]{3})\\b', price_text)
        media = node.select_one("[data-testid='serp-listing-carousel'] img")
        image = photo_url(media.get('src', '')) if media else ''
        status = node.find('span', recursive=False)
        camera = node.select_one("svg[data-name='iconCamera2']")
        ad = dict.fromkeys(METRICS)
        ad.update(id=ad_id, url=ad_url, title=heading.get_text(' ', strip=True), description='', price=number(price_text) if currency_match else None, currency=currency_match[1] if currency_match else '', images=[image] if image else [], photos=count(camera.parent.get_text(' ', strip=True)) if camera else None, seller_id=str(post.get('member_id') or ''), seller_name='', seller_url='', category_code=main_category, subcategory_code=subcategory, location=', '.join(filter(None, [plain(post.get('neighborhoodName') or node.get('data-nhood')), plain(post.get('city_reporting') or node.get('data-city'))])), published='', posted_label=relative_label(status.get_text(' ', strip=True)) if status else '')
        ads.append(ad)
    if cards and (not ads):
        raise SourceError('Новый формат объявлений категории не удалось прочитать.')
    next_link = soup.select_one("a[aria-label='Go to next page'][href], a[rel~='next'][href], link[rel~='next'][href]")
    next_url = safe_url(next_link['href'], url) if next_link and ads else None
    if ads and (not next_url):
        parsed = urlsplit(url)
        params = parse_qsl(parsed.query, keep_blank_values=True)
        try:
            current = int(dict(params).get('page', '1'))
        except ValueError:
            return (ads, None)
        expected = sorted(((key, value) for key, value in params if key != 'page'))
        for link in soup.find_all('a', href=True):
            candidate = urlsplit(urljoin(url, link['href']))
            query = parse_qsl(candidate.query, keep_blank_values=True)
            if candidate.hostname == parsed.hostname and candidate.path == parsed.path and (dict(query).get('page') == str(current + 1)) and (sorted(((key, value) for key, value in query if key != 'page')) == expected):
                next_url = safe_url(link['href'], url)
                break
    return (ads, next_url)

def parse_category(raw, url):
    soup = BeautifulSoup(raw, 'html.parser')
    documents = []
    with suppress(SourceError):
        documents.append(props(soup))
    documents.extend(flight(soup))
    data = next((o for o in walk(documents) if isinstance(o.get('serpApiResponse'), dict)), None)
    block = data.get('serpApiResponse', {}).get('listings') if data else None
    if not isinstance(block, dict) or not isinstance(block.get('items'), list):
        return parse_category_dom(soup, url, documents)
    ads = []
    for row in block['items']:
        if not isinstance(row, dict) or not row.get('id') or (not row.get('title')):
            continue
        path = row.get('post_url') or f"/search/{row['id']}"
        if path.startswith('/search/'):
            locale = urlsplit(url).path.split('/')[1]
            path = '/' + (locale if locale in {'ar', 'en'} else 'en') + path
        image = photo_url(row.get('image_uri'))
        ad = dict.fromkeys(METRICS)
        cat_data = category_codes(row)
        main_category, subcategory = (cat_data[0], cat_data[1])
        ad.update(id=str(row['id']), url=safe_url(path, url), title=plain(row['title']), description=plain(row.get('masked_description')), price=number(row.get('price_amount')), currency=plain(row.get('price_currency_iso')).upper(), photos=count(row.get('image_count')), images=[image] if image else [], views=count(row.get('views_count')), seller_id=str(row.get('member_id') or ''), seller_name=plain(row.get('member_display_name')), seller_url='', rating=number(row.get('member_rating_avg')), ratings=count(row.get('member_rating_count')), category_code=main_category, subcategory_code=subcategory, location=', '.join(filter(None, [plain(row.get('nhood_label')), plain(row.get('city_label'))])), published=publication(row.get('inserted_date')), posted_label=relative_label(row.get('posted_at')))
        username = plain(row.get('member_user_name'))
        if username:
            locale = 'ar' if urlsplit(url).path.startswith('/ar/') else 'en'
            ad['seller_url'] = safe_url(f'/{locale}/mid/{username}', url)
        ads.append(ad)
    if block['items'] and (not ads):
        raise SourceError('Объявления категории имеют неизвестную структуру.')
    return (ads, next_category_url(data, block, url))

def parse_listing(raw, ad):
    soup = BeautifulSoup(raw, 'html.parser')
    documents = []
    with suppress(SourceError):
        documents.append(props(soup))
    documents.extend(flight(soup))
    data = None
    for obj in walk(documents):
        candidate = obj.get('listingData')
        if isinstance(candidate, dict) and str(candidate.get('commonInfo', {}).get('postId')) == ad['id']:
            data = candidate
            break
    if data is None:
        raise SourceError('Не удалось прочитать данные объявления.')
    info = data['commonInfo']
    for metadata in walk(data.get('loggingData') or {}):
        cat_data = category_codes(metadata)
        main_category, subcategory = (cat_data[0], cat_data[1])
        if main_category:
            ad['category_code'] = main_category
            ad['subcategory_code'] = subcategory
            break
    owner = info.get('ownerData') or {}
    ad['title'] = plain(info.get('topTitle')) or ad['title']
    ad['description'] = plain(info.get('description')) or ad.get('description', '')
    for target, key, convert in (('seller_id', 'id', str), ('seller_name', 'fullName', plain), ('rating', 'ratingAvg', number), ('ratings', 'numberOfRatings', count)):
        if owner.get(key) is not None:
            ad[target] = convert(owner[key])
    registered = registration_date(owner.get('member_since') or owner.get('memberSince') or owner.get('registrationDate'))
    if registered:
        ad['seller_registered'] = registered
    ad['seller_listings_hint'] = count(owner.get('numberOfListings'))
    if owner.get('memberLink'):
        ad['seller_url'] = safe_url(owner['memberLink'], ad['url'])
    locations = {}
    for section in (info.get('basicInfo') or {}).get('sections', []):
        for item in section.get('items', []):
            kind, value = (item.get('key_type'), plain(item.get('value')))
            if kind == 'ListingPostDate' and value:
                ad['published'] = publication(value)
            if kind in {'Neighborhood', 'City'} and value:
                locations[kind] = value
    if locations:
        ad['location'] = ', '.join(dict.fromkeys((locations[k] for k in ('Neighborhood', 'City') if k in locations)))
    if not ad.get('published'):
        for key in ('datePublished', 'publishedAt', 'createdAt'):
            if info.get(key):
                ad['published'] = publication(info[key])
                break
    gallery = info.get('gallery') or {}
    base = (data.get('config') or {}).get('imagesBaseUrl') or CDN
    images = [photo_url(m.get('uri'), base) for m in gallery.get('media', []) if isinstance(m, dict) and str(m.get('mimeType', '')).startswith('image/')]
    ad['images'] = list(dict.fromkeys(filter(None, images))) or ad.get('images', [])
    if (gallery.get('chips') or {}).get('imagesCount') is not None:
        ad['photos'] = count(gallery['chips']['imagesCount'])
    for key in ('viewsCount', 'views_count', 'postViewsCount'):
        if info.get(key) is not None:
            ad['views'] = count(info[key])
            break
    prices = ((data.get('listing') or {}).get('price') or {}).get('prices', [])
    if prices:
        price = number(prices[0].get('price'))
        if price is not None:
            ad['price'] = price
        currency = plain(prices[0].get('key') or prices[0].get('currencyLabel')).upper()
        if re.fullmatch('[A-Z]{3}', currency):
            ad['currency'] = currency
    return ad

class Reader:

    def __init__(self):
        saved = load_proxy_config()
        if saved:
            self.proxy_pool, self.proxy_index = saved
        else:
            primary, _ = proxy_settings(os.getenv('OPENSOOQ_PROXY_URL', ''))
            backup_file = Path(os.getenv('OPENSOOQ_PROXY_BACKUPS_FILE', '/etc/secrets/opensooq-proxies.txt'))
            try:
                lines = backup_file.read_text(encoding='utf-8').splitlines()
            except FileNotFoundError:
                lines = []
            backups = [proxy_settings(line)[0] for line in lines if line.strip() and (not line.lstrip().startswith('#'))]
            if backups and (not primary):
                raise ValueError('Для запасных прокси задайте основной OPENSOOQ_PROXY_URL.')
            self.proxy_pool = list(dict.fromkeys([primary, *backups]))
            self.proxy_index = 0
        if len(self.proxy_pool) > 11:
            raise ValueError('Можно сохранить основной и до 10 резервных прокси.')
        self.proxy_url, self.browser_proxy = proxy_settings(self.proxy_pool[self.proxy_index] or '')
        self.proxy_clients = [self._http_client(proxy) for proxy in self.proxy_pool]
        self.http = self.proxy_clients[self.proxy_index]
        self.on_proxy_switch = None
        self.browser_fetch = None
        self.browser_hosts = {}
        self.request_lock = asyncio.Lock()
        self.lock = asyncio.Lock()
        self.browser_lock = asyncio.Lock()
        self.last, self.pauses, self.cache = (0.0, {}, {})
        self.pw = self.browser = self.browser_context = None
        self.browser_failures = 0

    @staticmethod
    def _http_client(proxy):
        return httpx.AsyncClient(timeout=30, follow_redirects=False, proxy=proxy, trust_env=False, headers={'User-Agent': 'OpenSooqTelegramBot/2.0', 'Accept-Language': 'en'})

    async def _next_proxy(self):
        if self.proxy_index + 1 == len(self.proxy_clients):
            return False
        self.proxy_index += 1
        self.http = self.proxy_clients[self.proxy_index]
        self.proxy_url, self.browser_proxy = proxy_settings(self.proxy_pool[self.proxy_index])
        await self.reset_profile_browser()
        log.warning('[proxy] HTTP-запросы парсера переключены на прокси №%s', self.proxy_index + 1)
        if self.on_proxy_switch:
            await self.on_proxy_switch(self.proxy_index + 1)
        return True

    async def reset_profile_browser(self):
        async with self.browser_lock:
            if self.browser is not None:
                with suppress(Exception):
                    await self.browser.close()
            self.browser = self.browser_context = None
            self.browser_failures = 0
            self.cache.clear()
            self.browser_hosts.clear()

    async def configure_proxies(self, action, value=''):
        async with self.request_lock:
            pool, active = (list(self.proxy_pool), self.proxy_index)
            if action in {'new', 'add'}:
                uri, _ = proxy_settings(value)
                if not uri:
                    raise ValueError('Пришлите HTTP-прокси: http://ЛОГИН:ПАРОЛЬ@СЕРВЕР:ПОРТ')
                if action == 'new':
                    pool = [uri] + [p for p in pool[1:] if p and p != uri]
                    active = 0
                elif uri not in pool:
                    if not pool[0]:
                        raise ValueError('Сначала задайте основной прокси: /newproxy.')
                    if len(pool) >= 11:
                        raise ValueError('Можно сохранить основной и до 10 резервных прокси.')
                    pool.append(uri)
            elif action == 'next':
                if len(pool) < 2:
                    raise ValueError('Резервных прокси пока нет. Добавьте через /addproxy.')
                active = (active + 1) % len(pool)
            elif action == 'delete':
                try:
                    index = int(value) - 1
                except ValueError:
                    raise ValueError('Используйте /delproxy НОМЕР из /proxies.') from None
                if index <= 0 or index >= len(pool):
                    raise ValueError('Удалять можно только резервные прокси из /proxies.')
                if index == active:
                    raise ValueError('Этот прокси сейчас активен. Сначала /nextproxy.')
                pool.pop(index)
                active -= index < active
            else:
                raise ValueError('Неизвестное действие с прокси.')
            changed = pool[active] != self.proxy_pool[self.proxy_index]
            clients = []
            try:
                for proxy in pool:
                    clients.append(self._http_client(proxy))
                save_proxy_config(pool, active)
            except BaseException:
                for client in clients:
                    await client.aclose()
                raise
            old_clients = self.proxy_clients
            self.proxy_pool, self.proxy_index, self.proxy_clients = (pool, active, clients)
            self.http = clients[active]
            self.proxy_url, self.browser_proxy = proxy_settings(pool[active])
            if changed:
                await self.reset_profile_browser()
            for client in old_clients:
                with suppress(Exception):
                    await client.aclose()
            return changed

    async def throttle(self):
        async with self.lock:
            await asyncio.sleep(max(0, self.last + REQUEST_INTERVAL - time.monotonic()))
            self.last = time.monotonic()

    def status_error(self, status, headers, host):
        action = str(headers.get('x-amzn-waf-action', '')).lower()
        if action in {'challenge', 'captcha'}:
            raise SourceError(f'OpenSooq: HTTP {status}, AWS WAF {action}. Страница объявлений не получена.', reason='waf_' + action, status=status)
        if status == 202:
            raise SourceError('OpenSooq вернул HTTP 202. Страница объявлений не получена; проверка защиты не подтверждена заголовком.', reason='http202', status=status)
        if status == 429:
            retry = headers.get('retry-after', '300')
            try:
                delay = float(retry)
            except ValueError:
                try:
                    delay = parsedate_to_datetime(retry).timestamp() - time.time()
                except (ValueError, TypeError, OverflowError, AttributeError):
                    delay = 300
            self.pauses[host] = time.monotonic() + max(60, min(3600, delay))
            raise RateLimit('OpenSooq ограничил запросы: HTTP 429.', reason='rate_limit', status=429)
        if status != 200:
            raise SourceError(f'OpenSooq вернул HTTP {status}.', reason='http_error', status=status)

    @staticmethod
    def check_html(raw):
        if re.search('<title>\\s*(?:Just a moment|Access Denied|Access Restricted|Attention Required)', raw[:20000], re.I):
            raise SourceError('OpenSooq показал проверку доступа.', reason='access_check')

    async def get(self, url):
        url = safe_url(url)
        host = urlsplit(url).hostname
        async with self.request_lock:
            if self.pauses.get(host, 0) > time.monotonic():
                raise RateLimit('Пауза после ограничения OpenSooq ещё не закончилась.', reason='rate_limit_pause')
            if self.browser_fetch is None:
                return await self._get(url)
            while True:
                try:
                    result = await self.browser_fetch(url)
                    self.browser_hosts[host] = time.monotonic() + 300
                    return result
                except SourceError as exc:
                    if exc.reason == 'proxy_connection' and await self._next_proxy():
                        continue
                    raise

    async def _get(self, url):
        url = safe_url(url)
        for _ in range(6):
            host = urlsplit(url).hostname
            if self.pauses.get(host, 0) > time.monotonic():
                raise RateLimit('Пауза после ограничения OpenSooq ещё не закончилась.', reason='rate_limit_pause')
            response = None
            attempt = 0
            while attempt < 3:
                await self.throttle()
                try:
                    async with self.http.stream('GET', url) as response:
                        body = bytearray()
                        async for chunk in response.aiter_bytes():
                            body.extend(chunk)
                            if len(body) > 8 * 1024 * 1024:
                                raise SourceError('Слишком большой ответ OpenSooq.')
                        raw = body.decode(response.encoding or 'utf-8', errors='replace')
                    if response.status_code == 407 and await self._next_proxy():
                        attempt = 0
                        continue
                    if response.status_code >= 500 and attempt < 2:
                        await asyncio.sleep(2 ** (attempt + 1))
                        attempt += 1
                        continue
                    break
                except httpx.RequestError as exc:
                    if self.proxy_url and isinstance(exc, (httpx.ProxyError, httpx.ConnectError, httpx.ConnectTimeout, httpx.ReadTimeout, httpx.ReadError)):
                        if await self._next_proxy():
                            attempt = 0
                            continue
                    if attempt == 2:
                        raise SourceError('OpenSooq не ответил вовремя.', reason='network') from None
                    await asyncio.sleep(2 ** (attempt + 1))
                    attempt += 1
            if response is None:
                raise SourceError('Нет ответа OpenSooq.')
            if response.status_code in {301, 302, 303, 307, 308}:
                location = response.headers.get('location')
                if not location:
                    raise SourceError('Перенаправление без адреса.')
                url = safe_url(location, url)
                continue
            self.status_error(response.status_code, response.headers, host)
            self.check_html(raw)
            return (raw, url)
        raise SourceError('Слишком много перенаправлений.')

    async def browser_profile(self, url, seller_id):
        if not USE_BROWSER or self.browser_failures >= 3:
            raise SourceError('Браузерная загрузка профилей недоступна.')
        from playwright.async_api import async_playwright, TimeoutError as PlaywrightTimeout
        async with self.browser_lock:
            page = None
            try:
                if self.browser is None or not self.browser.is_connected():
                    if self.pw is None:
                        self.pw = await async_playwright().start()
                    launch_options = {'headless': True, 'args': ['--disable-dev-shm-usage']}
                    if self.browser_proxy is not None:
                        launch_options['proxy'] = self.browser_proxy
                    self.browser = await self.pw.chromium.launch(**launch_options)
                    self.browser_context = await self.browser.new_context(locale='en-US')

                    async def lightweight(route):
                        if route.request.resource_type in {'image', 'media', 'font'}:
                            await route.abort()
                        else:
                            await route.continue_()
                    await self.browser_context.route('**/*', lightweight)
                await self.throttle()
                page = await self.browser_context.new_page()
                try:
                    response = await page.goto(safe_url(url), timeout=25000, wait_until='domcontentloaded')
                except PlaywrightTimeout:
                    response = None
                safe_url(page.url)
                if urlsplit(page.url).hostname != urlsplit(url).hostname:
                    raise SourceError('Профиль перенаправил на другую страну.')
                if response is not None:
                    self.status_error(response.status, response.headers, urlsplit(url).hostname)
                profile = None
                for attempt in range(4):
                    raw = await page.content()
                    self.check_html(raw)
                    profile = await asyncio.to_thread(parse_profile, raw, seller_id)
                    if all((profile.get(key) is not None for key in ('seller_views', 'listings_count'))):
                        self.browser_failures = 0
                        return profile
                    if attempt < 3:
                        await asyncio.sleep(1.0)
                if profile and any((v is not None for v in profile.values())):
                    self.browser_failures = 0
                    return profile
                raise SourceError('Статистика отсутствует в загруженном профиле.')
            except RateLimit:
                raise
            except Exception as exc:
                self.browser_failures += 1
                log.warning('[profile_browser] seller=%s error=%s', seller_id, error_text(exc)[:1200])
                if isinstance(exc, SourceError):
                    raise
                raise SourceError('Не удалось загрузить профиль браузером.') from None
            finally:
                if page is not None:
                    with suppress(Exception):
                        await page.close()

    async def profile(self, url, seller_id):
        key = (url, seller_id)
        cached = self.cache.get(key)
        if cached and cached[0] > time.monotonic():
            return (cached[1], cached[2])
        profile, problems = (None, [])
        try:
            raw, _ = await self.get(url)
            profile = await asyncio.to_thread(parse_profile, raw, seller_id)
        except RateLimit:
            raise
        except (SourceError, ValueError) as exc:
            problems.append('HTTP: ' + error_text(exc))
        if getattr(self, 'browser_fetch', None) is None and (profile is None or any((profile.get(key) is None for key in ('seller_views', 'listings_count')))):
            try:
                rendered = await self.browser_profile(url, seller_id)
                profile = profile or {}
                profile.update({k: v for k, v in rendered.items() if v is not None})
            except RateLimit:
                raise
            except (SourceError, ValueError, ImportError) as exc:
                problems.append('Браузер: ' + error_text(exc))
        absent = [key for key in ('seller_views', 'listings_count') if not profile or profile.get(key) is None]
        if absent:
            labels = {'seller_views': 'просмотры', 'listings_count': 'активные объявления'}
            issue = 'Недоступны ' + ', '.join((labels[key] for key in absent)) + '. ' + ('; '.join(problems) or 'Счётчики не найдены в профиле.')
        else:
            issue = ''
        ttl = 300 if not issue else 60
        self.cache[key] = (time.monotonic() + ttl, profile, issue)
        if len(self.cache) > 2000:
            self.cache = {k: v for k, v in self.cache.items() if v[0] > time.monotonic()}
            self.cache = dict(list(self.cache.items())[-1000:])
        return (profile, issue)

    async def enrich(self, ad, rules=None, seller_seen=None):
        if excluded_topic(ad):
            ad['_filtered_before_profile'] = 'topic'
            return (ad, '')
        if rules:
            summary_rules = {k: v for k, v in rules.items() if k in {'price_min', 'price_max', 'currency'}}
            summary_rules['unknown'] = 'include'
            if not matches(ad, summary_rules)[0]:
                ad['_filtered_before_profile'] = 'rules'
                return (ad, '')
        raw, final = await self.get(ad['url'])
        if urlsplit(final).hostname != urlsplit(ad['url']).hostname:
            raise SourceError('Объявление перенаправило на другую страну.')
        ad['url'] = final
        ad = await asyncio.to_thread(parse_listing, raw, ad)
        if excluded_topic(ad):
            ad['_filtered_before_profile'] = 'topic'
            return (ad, '')
        if rules:
            early_keys = {'keywords', 'exclude', 'currency'} | {metric + '_' + bound for metric in ('price', 'photos', 'views') for bound in ('min', 'max')}
            early_rules = {k: v for k, v in rules.items() if k in early_keys}
            early_rules['unknown'] = 'include'
            if not matches(ad, early_rules)[0]:
                ad['_filtered_before_profile'] = 'rules'
                return (ad, '')
        if seller_seen is not None and seller_seen(ad):
            ad['_seller_already_sent'] = True
            return (ad, '')
        if not ad.get('seller_url'):
            return (ad, 'В объявлении отсутствует ссылка на профиль продавца.')
        profile, warning = await self.profile(ad['seller_url'], ad['seller_id'])
        if profile:
            ad.update({k: v for k, v in profile.items() if v is not None})
        return (ad, warning)

    async def close(self):
        if self.browser is not None:
            with suppress(Exception):
                await self.browser.close()
        if self.pw is not None:
            with suppress(Exception):
                await self.pw.stop()
        for client in dict.fromkeys([self.http, *self.proxy_clients]):
            await client.aclose()

def _show(ad, key):
    value = ad.get(key)
    if value is None:
        return 'нет данных'
    return escape(f'{value:g}' if isinstance(value, float) else str(value))

def card(ad):
    lines = [f"📦 <b>{escape(ad['title'][:100])}</b>"]
    price = f"{_show(ad, 'price')} {escape(ad.get('currency', ''))}".strip() if ad.get('price') is not None else 'Цена не указана'
    lines.append(f'<b>{price}</b>')
    if ad.get('location'):
        lines.append('📍 ' + escape(ad['location']))
    if ad.get('published'):
        lines.append('📅 Опубликовано: ' + escape(ad['published']))
    if ad.get('posted_label'):
        lines.append('🕓 В выдаче: ' + escape(ad['posted_label']))
    desc = plain(ad.get('description'))
    if desc:
        if len(desc) > 260:
            desc = desc[:257].rstrip() + '…'
        lines.extend(['', f'<blockquote>{escape(desc)}</blockquote>'])
    lines.extend(['', '👤 <b>' + escape((ad.get('seller_name') or 'Продавец')[:60]) + '</b>', f"👁 Просмотры профиля: <b>{_show(ad, 'seller_views')}</b>", f"📦 Активных объявлений: <b>{_show(ad, 'listings_count')}</b>", '📅 Регистрация продавца: <b>' + escape(str(ad.get('seller_registered') or 'нет данных')) + '</b>'])
    if ad.get('listings_count') is None and ad.get('seller_listings_hint') is not None:
        lines.append(f"В профиле продавца: {_show(ad, 'seller_listings_hint')} объявлений — активность не подтверждена")
    rating = []
    if ad.get('rating') is not None:
        rating.append(f"⭐ Рейтинг: <b>{_show(ad, 'rating')}</b>")
    if ad.get('ratings') is not None:
        rating.append(f"Оценок: {_show(ad, 'ratings')}")
    if rating:
        lines.append(' · '.join(rating))
    if ad.get('reviews') is not None:
        lines.append(f"💬 Отзывов: {_show(ad, 'reviews')}")
    if ad.get('sold') is not None:
        lines.append(f"✅ Продано: {_show(ad, 'sold')}")
    footer = [f"ID {_show(ad, 'id')}"]
    if ad.get('photos') is not None:
        footer.append(f"Фото: {_show(ad, 'photos')}")
    lines.extend(['', ' · '.join(footer)])
    return '\n'.join(lines)

async def telegram_call(method, **kwargs):
    try:
        return await method(**kwargs)
    except RetryAfter as exc:
        delay = exc.retry_after.total_seconds() if hasattr(exc.retry_after, 'total_seconds') else float(exc.retry_after)
        if delay > 60:
            raise
        await asyncio.sleep(delay + 1)
        return await method(**kwargs)
HELP_TEXT = 'ℹ️ Поиск объявлений\n/start — меню\n/check — поиск\n/pause — остановить\n/testsource — проверить выдачу\n/version — версия\n/saved — сохранённые поиски\n/id — мой ID\nФильтры и страны настраиваются кнопками меню.'

def help_text(user_id):
    return HELP_TEXT

def public_browser_url(url):
    url = safe_url(url)
    parsed = urlsplit(url)
    segments = {segment.casefold() for segment in parsed.path.split('/') if segment}
    if parsed.hostname not in {code + '.opensooq.com' for code in COUNTRIES} or not re.match('^/(?:en|ar)(?:/|$)', parsed.path) or segments & {'login', 'signin', 'sign-in', 'register', 'signup', 'account', 'accounts', 'chats', 'chat', 'messages', 'inbox', 'settings', 'payment', 'payments', 'checkout', 'logout'} or any((key.lower() in {'selectedroom', 'token', 'redirect', 'redirect_uri', 'next', 'returnurl'} for key, _ in parse_qsl(parsed.query))):
        raise SourceError('Нужна публичная выдача, объявление или профиль продавца.', reason='browser_public_only')
    return url

def source_failure_text(exc):
    reason = getattr(exc, 'reason', '')
    labels = {'waf_challenge': 'Сайт запросил AWS WAF Challenge. Страница выдачи не получена.', 'waf_captcha': 'Сайт запросил CAPTCHA. Страница выдачи не получена.', 'http202': 'HTTP 202: сайт не вернул обычную страницу выдачи. Защита сайта пока не подтверждена.', 'access_check': 'Сайт показал страницу проверки доступа вместо объявлений.', 'rate_limit': 'HTTP 429: сайт ограничил частоту запросов. Дождитесь окончания паузы.', 'rate_limit_pause': 'Действует пауза после ограничения запросов сайтом.', 'network': 'Не удалось получить ответ через текущее соединение.', 'browser_timeout': 'Chrome не успел загрузить страницу. Повторите /testsource.', 'browser_network': 'Не удалось загрузить страницу в Chrome. Повторите /testsource и проверьте лог [parser_browser].', 'country_redirect': 'Сайт перенаправил Chrome в другую страну. Выдача не использована.', 'browser_redirect': 'Chrome перенаправлен на другую страницу. Выдача не использована.', 'browser_public_only': 'Для браузерного поиска выберите страну через меню «Страны»: её публичную выдачу /en/find.', 'browser_render_timeout': 'Chrome не получил готовые данные объявлений. Проверьте доступ сайта через /testsource.', 'proxy_connection': 'Chrome не смог подключиться через прокси. Проверьте /proxies и /newproxy.'}
    if reason in labels:
        return labels[reason]
    status = getattr(exc, 'status', None)
    if status is None:
        match = re.search('HTTP\\s+(\\d{3})', str(exc))
        status = int(match[1]) if match else None
    if status == 403:
        return 'HTTP 403: сайт отказал в доступе к странице выдачи.'
    if status == 407:
        return 'HTTP 407: прокси отклонил авторизацию.'
    if isinstance(status, int):
        return f'HTTP {status}: страница выдачи не получена.'
    if isinstance(exc, (TimeoutError, httpx.RequestError)):
        return 'Истекло время ожидания ответа через текущее соединение.'
    if isinstance(exc, ValueError):
        return 'Ссылка или настройки поиска некорректны.'
    return 'Не удалось загрузить или прочитать страницу выдачи. Подробности — в логах сервиса.'

async def test_source_message(update, context):
    service = context.application.bot_data['service']
    chat = update.effective_chat.id
    urls = active_sources(service.state(chat))
    message = update.effective_message
    if not urls:
        await message.reply_text('Нет активных категорий. Выберите страну и категорию поиска.')
        return
    await message.reply_text('🔎 Проверяю страницы текущего поиска через активное соединение…')
    for source in urls:
        try:
            async with asyncio.timeout(60):
                raw, final = await service.reader.get(recent_source(source))
                ads, _ = await asyncio.to_thread(parse_category, raw, final)
            mode = 'Chrome' if service.reader.browser_hosts.get(urlsplit(final).hostname, 0) > time.monotonic() else 'HTTP'
            result = f'✅ Страница загружена: HTTP 200 ({mode}). Прочитано объявлений: {len(ads)}.'
        except (SourceError, ValueError, TimeoutError) as exc:
            result = '⚠️ ' + source_failure_text(exc)
            log.warning('[source_test] chat=%s host=%s %s', chat, urlsplit(source).hostname, error_text(exc))
        await message.reply_text(source_country(source) + '\n' + source + '\n\n' + result)

def report_text(stats, elapsed, outcome):
    titles = {'complete': '✅ Поиск завершён', 'partial': '⚠️ Поиск завершён с замечаниями', 'error': '❌ Поиск прерван', 'stopped': '⏸ Поиск остановлен', 'limit': '📦 Достигнут лимит поиска'}
    seconds = max(0, round(elapsed))
    duration = f'{seconds // 60} мин. {seconds % 60} сек.' if seconds >= 60 else f'{seconds} сек.'
    text = f"<b>{titles[outcome]}</b>\n\nОтправлено объявлений: <b>{stats['sent']}</b>\nУже отправлялись: <b>{stats['duplicates']}</b>\nПроверены ранее: <b>{stats['previously_checked']}</b>\nПовторы продавцов: <b>{stats['seller_duplicates']}</b>\nВремя: <b>{duration}</b>\n\nСтраниц: {stats['pages']} · Объявлений: {stats['found']}\nПроверено объявлений: {stats['checked']}\nОтсеяно фильтрами: {stats['filtered']} · Ошибок: {stats['errors']}"
    if stats['filtered']:
        text += f"\nТематика: {stats['filtered_topic']} · Настройки: {stats['filtered_rules']} · Нет данных для фильтра: {stats['filtered_missing']}"
    if stats['history_boundary']:
        text += '\n\nСвежая часть выдачи проверена; дальше знакомые объявления. Глубокая проверка: /deepcheck.'
    return text

def public_document_ready(raw, url):
    path = urlsplit(url).path
    if re.search('/(?:search|lists)/\\d+', path) or '/mid/' in path:
        soup = BeautifulSoup(raw, 'html.parser')
        node = soup.select_one('script#__NEXT_DATA__')
        if node is not None:
            try:
                data = json.loads(node.string or node.get_text())
                return bool(data.get('props', {}).get('pageProps'))
            except (ValueError, TypeError, AttributeError):
                return False
        return bool(flight(soup))
    try:
        parse_category(raw, url)
        return True
    except (SourceError, ValueError, KeyError, TypeError):
        return False

async def read_rendered_document(page, reader, url, *, render_timeout=18, settle=0.5):
    from playwright.async_api import TimeoutError as PlaywrightTimeout
    latest = {'response': None, 'at': 0.0}

    def observe(response):
        try:
            if response.request.resource_type == 'document' and response.frame == page.main_frame:
                latest['response'] = response
                latest['at'] = time.monotonic()
        except (AttributeError, ValueError):
            return
    page.on('response', observe)
    try:
        try:
            response = await page.goto(url, wait_until='domcontentloaded', timeout=25000)
            if latest['response'] is None and response is not None:
                latest.update(response=response, at=time.monotonic())
        except PlaywrightTimeout:
            pass
        deadline = time.monotonic() + render_timeout
        while True:
            response = latest['response']
            if response is not None:
                status = response.status
                action = str(response.headers.get('x-amzn-waf-action', '')).lower()
                if action == 'captcha' or status not in {200, 202}:
                    reader.status_error(status, response.headers, urlsplit(url).hostname)
                if status == 200 and action not in {'challenge', 'captcha'} and (time.monotonic() - latest['at'] >= settle):
                    final = public_browser_url(page.url)
                    if urlsplit(final).hostname != urlsplit(url).hostname:
                        raise SourceError('Страница перенаправила Chrome в другую страну.', reason='country_redirect')
                    requested_path = urlsplit(url).path.rstrip('/')
                    final_path = urlsplit(final).path.rstrip('/')
                    requested_ad = re.search('/(?:search|lists)/(\\d+)', requested_path)
                    final_ad = re.search('/(?:search|lists)/(\\d+)', final_path)
                    same = requested_ad is not None and final_ad is not None and (requested_ad[1] == final_ad[1]) or requested_path == final_path
                    if not same:
                        raise SourceError('Chrome перенаправлен на другую страницу.', reason='browser_redirect')
                    try:
                        raw = await page.content()
                    except Exception:
                        if time.monotonic() >= deadline:
                            raise
                    else:
                        if len(raw.encode('utf-8')) > 8 * 1024 * 1024:
                            raise SourceError('Слишком большой ответ OpenSooq.')
                        reader.check_html(raw)
                        if await asyncio.to_thread(public_document_ready, raw, final):
                            return (raw, final)
            if time.monotonic() >= deadline:
                if response is not None:
                    reader.status_error(response.status, response.headers, urlsplit(url).hostname)
                raise SourceError('Chrome не получил готовые данные объявлений за отведённое время.', reason='browser_render_timeout')
            await asyncio.sleep(0.25)
    finally:
        page.remove_listener('response', observe)

class Service:

    def __init__(self, bot, allowed, path):
        self.bot, self.allowed = (bot, set(allowed))
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(path)
        self.db.row_factory = sqlite3.Row
        self.db.executescript("\n            PRAGMA journal_mode=WAL;\n            CREATE TABLE IF NOT EXISTS users(chat INTEGER PRIMARY KEY, urls TEXT NOT NULL DEFAULT '[]', rules TEXT NOT NULL DEFAULT '{}', enabled INTEGER NOT NULL DEFAULT 0, minutes INTEGER NOT NULL DEFAULT 15, next_check REAL NOT NULL DEFAULT 0, last TEXT NOT NULL DEFAULT '');\n            CREATE TABLE IF NOT EXISTS delivered(chat INTEGER NOT NULL, key TEXT NOT NULL, PRIMARY KEY(chat,key));\n            CREATE TABLE IF NOT EXISTS checked_ads(\n                chat INTEGER NOT NULL, rules TEXT NOT NULL, key TEXT NOT NULL,\n                PRIMARY KEY(chat,rules,key)\n            );\n            CREATE TABLE IF NOT EXISTS delivered_sellers(\n                chat INTEGER NOT NULL, key TEXT NOT NULL, PRIMARY KEY(chat,key)\n            );\n            CREATE TABLE IF NOT EXISTS authorized(chat INTEGER PRIMARY KEY);\n            CREATE TABLE IF NOT EXISTS revoked(chat INTEGER PRIMARY KEY);\n            CREATE TABLE IF NOT EXISTS subscriptions(chat INTEGER PRIMARY KEY, until REAL NOT NULL);\n            CREATE TABLE IF NOT EXISTS subscriptions_test(chat INTEGER PRIMARY KEY, until REAL NOT NULL);\n            CREATE TABLE IF NOT EXISTS subscription_events(id TEXT PRIMARY KEY, chat INTEGER NOT NULL, hours REAL NOT NULL, actor INTEGER NOT NULL, created REAL NOT NULL);\n            CREATE TABLE IF NOT EXISTS payment_orders(\n                id TEXT PRIMARY KEY, chat INTEGER NOT NULL, plan TEXT NOT NULL, hours INTEGER NOT NULL,\n                amount TEXT NOT NULL, currency TEXT NOT NULL, invoice TEXT NOT NULL DEFAULT '',\n                link TEXT NOT NULL DEFAULT '', status TEXT NOT NULL DEFAULT 'pending', applied INTEGER NOT NULL DEFAULT 0,\n                created REAL NOT NULL, checked REAL NOT NULL DEFAULT 0, network TEXT NOT NULL\n            );\n            CREATE TABLE IF NOT EXISTS saved_searches(\n                id INTEGER PRIMARY KEY AUTOINCREMENT,\n                chat INTEGER NOT NULL,\n                name TEXT NOT NULL,\n                config TEXT NOT NULL,\n                created REAL NOT NULL,\n                UNIQUE(chat, name)\n            );\n        ")
        columns = {row['name'] for row in self.db.execute('PRAGMA table_info(users)')}
        if 'disabled_countries' not in columns:
            self.db.execute("ALTER TABLE users ADD COLUMN disabled_countries TEXT NOT NULL DEFAULT '[]'")
        if 'country_mode' not in columns:
            self.db.execute("ALTER TABLE users ADD COLUMN country_mode TEXT NOT NULL DEFAULT 'single'")
        if 'selected_country' not in columns:
            self.db.execute("ALTER TABLE users ADD COLUMN selected_country TEXT NOT NULL DEFAULT ''")
        self.db.commit()
        self.allowed.update((r['chat'] for r in self.db.execute('SELECT chat FROM authorized')))
        self.revoked = {r['chat'] for r in self.db.execute('SELECT chat FROM revoked') if r['chat'] != ADMIN_ID}
        self.allowed.difference_update(self.revoked)
        self.reader, self.tasks, self.lock = (Reader(), {}, asyncio.Lock())
        self.reader.on_proxy_switch = self.notify_proxy_switch
        self.closing = False
        self.public_browser = PublicChromeBrowser()
        self.browser_lock = asyncio.Lock()
        self.reader.browser_fetch = self.fetch_public_page
        if getattr(self.reader, 'proxy_url', None):
            os.environ['OPENSOOQ_PROXY_URL'] = self.reader.proxy_url

    async def fetch_public_page(self, url):
        url = public_browser_url(url)
        async with self.browser_lock:
            page = None
            try:
                async with asyncio.timeout(55):
                    context, _ = await self.public_browser.get_page()
                    page = await context.new_page()
                    page.set_default_timeout(12000)
                    await self.reader.throttle()
                    return await read_rendered_document(page, self.reader, url)
            except (SourceError, ValueError):
                raise
            except TimeoutError:
                raise SourceError('Chrome не успел загрузить страницу.', reason='browser_timeout') from None
            except Exception as exc:
                code = str(exc)
                reason = 'proxy_connection' if any((marker in code for marker in ('ERR_PROXY_CONNECTION_FAILED', 'ERR_TUNNEL_CONNECTION_FAILED', 'ERR_INVALID_AUTH_CREDENTIALS', 'ERR_PROXY_AUTH_UNSUPPORTED'))) else 'browser_network'
                log.warning('[parser_browser] host=%s error=%s reason=%s', urlsplit(url).hostname, type(exc).__name__, reason)
                raise SourceError('Не удалось загрузить страницу в Chrome.', reason=reason) from None
            finally:
                if page is not None:
                    with suppress(Exception):
                        await page.close()

    async def change_proxy(self, action, value=''):
        changed = await self.reader.configure_proxies(action, value)
        os.environ['OPENSOOQ_PROXY_URL'] = self.reader.proxy_url
        if changed:
            async with self.browser_lock:
                await self.public_browser.close()

    async def notify_proxy_switch(self, number):
        os.environ['OPENSOOQ_PROXY_URL'] = self.reader.proxy_url
        try:
            save_proxy_config(self.reader.proxy_pool, self.reader.proxy_index)
        except OSError:
            log.error('[proxy] Не удалось сохранить переключение прокси на диск.')
        async with self.browser_lock:
            await self.public_browser.close()
        with suppress(TelegramError):
            await self.bot.send_message(chat_id=ADMIN_ID, text=f'🔄 Парсер переключился на прокси №{number}.')

    def permitted(self, chat):
        if chat == ADMIN_ID:
            return True
        return chat in self.allowed and chat not in self.revoked and (not is_blocked(chat))

    def authorize(self, chat):
        self.allowed.add(chat)
        self.revoked.discard(chat)
        with self.db:
            self.db.execute('DELETE FROM revoked WHERE chat=?', (chat,))
            self.db.execute('INSERT OR IGNORE INTO authorized VALUES (?)', (chat,))

    async def revoke_access(self, chat):
        if chat == ADMIN_ID:
            raise ValueError('Нельзя отозвать доступ администратора.')
        remove_user_password(chat)
        self.allowed.discard(chat)
        self.revoked.add(chat)
        self.state(chat)
        with self.db:
            self.db.execute('DELETE FROM authorized WHERE chat=?', (chat,))
            self.db.execute('INSERT OR IGNORE INTO revoked VALUES (?)', (chat,))
            self.db.execute('UPDATE users SET enabled=0 WHERE chat=?', (chat,))
        await self.cancel_scan(chat)

    def state(self, chat):
        with self.db:
            self.db.execute('INSERT OR IGNORE INTO users(chat) VALUES (?)', (chat,))
        row = dict(self.db.execute('SELECT * FROM users WHERE chat=?', (chat,)).fetchone())
        try:
            urls = json.loads(row.get('urls', '[]'))
            row['urls'] = [u for u in urls if isinstance(u, str)] if isinstance(urls, list) else []
        except Exception:
            row['urls'] = []
        try:
            rules = json.loads(row.get('rules', '{}'))
            row['rules'] = rules if isinstance(rules, dict) else {}
        except Exception:
            row['rules'] = {}
        try:
            disabled = json.loads(row.get('disabled_countries', '[]'))
            row['disabled_countries'] = list(dict.fromkeys((code for code in disabled if code in COUNTRIES))) if isinstance(disabled, list) else []
        except (ValueError, TypeError):
            row['disabled_countries'] = []
        row['country_mode'] = 'all' if row.get('country_mode') == 'all' else 'single'
        selected = row.get('selected_country', '')
        if selected not in COUNTRIES:
            selected = next((country_code(url) for url in row['urls'] if country_code(url) in COUNTRIES and country_code(url) not in row['disabled_countries']), '')
        row['selected_country'] = selected
        return row

    def save(self, chat, **changes):
        if not changes or not changes.keys() <= {'urls', 'rules', 'enabled', 'minutes', 'next_check', 'last', 'disabled_countries', 'country_mode', 'selected_country'}:
            raise ValueError('Некорректные настройки.')
        values = [json.dumps(v, ensure_ascii=False) if k in {'urls', 'rules', 'disabled_countries'} else v for k, v in changes.items()]
        with self.db:
            self.db.execute('UPDATE users SET ' + ','.join((k + '=?' for k in changes)) + ' WHERE chat=?', values + [chat])

    def seller_seen(self, chat, ad):
        return any((self.db.execute('SELECT 1 FROM delivered_sellers WHERE chat=? AND key=?', (chat, key)).fetchone() for key in seller_keys(ad)))

    def remember_seller(self, chat, ad):
        self.db.executemany('INSERT OR IGNORE INTO delivered_sellers VALUES (?,?)', [(chat, key) for key in seller_keys(ad)])

    def mark_checked(self, chat, signature, key):
        with self.db:
            self.db.execute('INSERT OR IGNORE INTO checked_ads VALUES (?,?,?)', (chat, signature, key))

    def trigger(self, chat, deep=False):
        if self.closing or not self.permitted(chat) or (not active_sources(self.state(chat))):
            return False
        if chat in self.tasks and (not self.tasks[chat].done()):
            return False
        self.save(chat, next_check=time.time() + self.state(chat)['minutes'] * 60)
        self.tasks[chat] = asyncio.create_task(self.scan(chat, deep=deep))
        return True

    async def tick(self, context):
        for row in list(self.db.execute('SELECT chat FROM users WHERE enabled=1 AND next_check<=?', (time.time(),))):
            self.trigger(row['chat'])

    async def cancel_scan(self, chat):
        task = self.tasks.get(chat)
        if task and (not task.done()):
            task.cancel()
            with suppress(asyncio.CancelledError):
                await task

    async def send(self, chat, ad):
        buttons = [[InlineKeyboardButton('🔗 Ссылка на товар', url=ad['url'])]]
        if ad.get('seller_url'):
            buttons.append([InlineKeyboardButton('👤 Профиль продавца', url=ad['seller_url'])])
        markup = InlineKeyboardMarkup(buttons)
        text = card(ad)
        size = len(BeautifulSoup(text, 'html.parser').get_text().encode('utf-16-le')) // 2
        if ad.get('images'):
            try:
                if size <= 1024:
                    await telegram_call(self.bot.send_photo, chat_id=chat, photo=ad['images'][0], caption=text, parse_mode='HTML', reply_markup=markup)
                    return
                await telegram_call(self.bot.send_photo, chat_id=chat, photo=ad['images'][0], caption=escape(ad['title'][:100]), parse_mode='HTML')
            except BadRequest as exc:
                log.warning('Не удалось отправить фото: %s', exc)
        await telegram_call(self.bot.send_message, chat_id=chat, text=text, parse_mode='HTML', reply_markup=markup)

    async def live_progress(self, message, stats):
        previous = ''
        while True:
            await asyncio.sleep(20)
            text = f"⏳ Проверка продолжается…\nСтраниц: {stats['pages']}\nПроверено объявлений: {stats['checked']}\nОтправлено: {stats['sent']}\nУже отправлялись: {stats['duplicates']}\nПроверены ранее: {stats['previously_checked']}\nПовторы продавцов: {stats['seller_duplicates']}\nОтсеяно: {stats['filtered']}\nОшибок: {stats['errors']}\n\nИтоговый отчёт появится после завершения.\nОстановка: /pause"
            if text != previous:
                try:
                    await telegram_call(message.edit_text, text=text)
                    previous = text
                except TelegramError:
                    log.warning('[scan_progress] Не удалось обновить прогресс')

    async def scan(self, chat, deep=False):
        stats, warnings, seen = (Counter(), {}, set())
        failure_reasons = []
        outcome, started, stop = ('complete', time.monotonic(), False)
        report_allowed = True
        progress_task = None
        last_delivery = 0.0
        try:
            progress_message = await telegram_call(self.bot.send_message, chat_id=chat, text='🚀 Начинаю проверку объявлений…')
            if progress_message is not None:
                progress_task = asyncio.create_task(self.live_progress(progress_message, stats))
            async with self.lock:
                self.reader.browser_failures = 0
                for source in active_sources(self.state(chat)):
                    if not isinstance(source, str):
                        continue
                    try:
                        url = recent_source(source)
                    except ValueError:
                        warnings['Сохранённая ссылка на категорию некорректна.'] = True
                        failure_reasons.append('Сохранённая ссылка на категорию некорректна.')
                        stats['errors'] += 1
                        outcome = 'partial'
                        continue
                    pages_seen = set()
                    known_pages = 0
                    scan_rules = self.state(chat)['rules']
                    signature = rules_key(scan_rules)
                    for page_index in range(MAX_PAGES):
                        if stop or source not in active_sources(self.state(chat)):
                            break
                        if not self.permitted(chat):
                            outcome, stop = ('stopped', True)
                            break
                        if url in pages_seen:
                            warnings['Обнаружен повтор страницы категории.'] = True
                            break
                        pages_seen.add(url)
                        try:
                            raw, final = await self.reader.get(url)
                            ads, next_url = await asyncio.to_thread(parse_category, raw, final)
                            stats['pages'] += 1
                        except RateLimit as exc:
                            failure_reasons.append(source_failure_text(exc))
                            warnings[str(exc)] = True
                            stats['errors'] += 1
                            outcome, stop = ('partial', True)
                            break
                        except (SourceError, ValueError) as exc:
                            failure_reasons.append(source_failure_text(exc))
                            warnings[str(exc)] = True
                            stats['errors'] += 1
                            outcome = 'partial'
                            break
                        page_known = bool(ads)
                        for candidate in ads:
                            candidate_key = urlsplit(candidate['url']).hostname + ':' + candidate['id']
                            known = self.db.execute('SELECT 1 FROM delivered WHERE chat=? AND key=?', (chat, candidate_key)).fetchone() or self.db.execute('SELECT 1 FROM checked_ads WHERE chat=? AND rules=? AND key=?', (chat, signature, candidate_key)).fetchone() or self.seller_seen(chat, candidate)
                            if not known:
                                page_known = False
                                break
                        for ad in ads:
                            if self.state(chat)['rules'] != scan_rules:
                                warnings['Фильтры изменены во время проверки. Запустите поиск заново.'] = True
                                outcome, stop = ('partial', True)
                                break
                            key = urlsplit(ad['url']).hostname + ':' + ad['id']
                            if key in seen:
                                continue
                            seen.add(key)
                            stats['found'] += 1
                            if self.db.execute('SELECT 1 FROM delivered WHERE chat=? AND key=?', (chat, key)).fetchone():
                                stats['duplicates'] += 1
                                with self.db:
                                    self.remember_seller(chat, ad)
                                continue
                            if self.seller_seen(chat, ad):
                                stats['seller_duplicates'] += 1
                                continue
                            if self.db.execute('SELECT 1 FROM checked_ads WHERE chat=? AND rules=? AND key=?', (chat, signature, key)).fetchone():
                                stats['previously_checked'] += 1
                                continue
                            if stats['checked'] >= MAX_ADS or stats['sent'] >= MAX_SEND:
                                outcome, stop = ('limit', True)
                                break
                            if source not in active_sources(self.state(chat)) or not self.permitted(chat):
                                break
                            stats['checked'] += 1
                            if excluded_topic(ad):
                                stats['filtered'] += 1
                                stats['filtered_topic'] += 1
                                self.mark_checked(chat, signature, key)
                                continue
                            try:
                                rules = scan_rules
                                ad, warning = await self.reader.enrich(ad, rules=rules, seller_seen=lambda item: self.seller_seen(chat, item))
                                if self.state(chat)['rules'] != scan_rules:
                                    warnings['Фильтры изменены во время проверки. Запустите поиск заново.'] = True
                                    outcome, stop = ('partial', True)
                                    break
                                if ad.pop('_seller_already_sent', False) or self.seller_seen(chat, ad):
                                    stats['seller_duplicates'] += 1
                                    self.mark_checked(chat, signature, key)
                                    continue
                                rejection = ad.pop('_filtered_before_profile', False)
                                if rejection:
                                    stats['filtered'] += 1
                                    stats['filtered_topic' if rejection == 'topic' else 'filtered_rules'] += 1
                                    self.mark_checked(chat, signature, key)
                                    continue
                                if warning:
                                    warnings[warning] = True
                                accepted, absent = matches(ad, rules)
                                if not accepted:
                                    stats['filtered'] += 1
                                    if absent and rules.get('unknown') != 'include':
                                        stats['filtered_missing'] += 1
                                    else:
                                        stats['filtered_rules'] += 1
                                    if not absent and (not warning):
                                        self.mark_checked(chat, signature, key)
                                    continue
                                await asyncio.sleep(max(0, last_delivery + 1.1 - time.monotonic()))
                                if not self.permitted(chat):
                                    outcome, stop = ('stopped', True)
                                    break
                                await self.send(chat, ad)
                                with self.db:
                                    self.db.execute('INSERT OR IGNORE INTO delivered VALUES (?,?)', (chat, key))
                                    self.remember_seller(chat, ad)
                                    self.db.execute('INSERT OR IGNORE INTO checked_ads VALUES (?,?,?)', (chat, signature, key))
                                stats['sent'] += 1
                                last_delivery = time.monotonic()
                            except Forbidden:
                                raise
                            except RateLimit as exc:
                                warnings[str(exc)] = True
                                stats['errors'] += 1
                                outcome, stop = ('partial', True)
                                break
                            except (SourceError, ValueError, TelegramError) as exc:
                                stats['errors'] += 1
                                warnings[str(exc)[:220]] = True
                                log.warning('Объявление %s: %s', ad['id'], type(exc).__name__)
                            except Exception:
                                stats['errors'] += 1
                                warnings[f"Объявление {ad['id']}: ошибка обработки; подробности в логах Render."] = True
                                log.exception('Ошибка обработки объявления %s', ad['id'])
                        known_pages = known_pages + 1 if page_known else 0
                        if not deep and known_pages >= 2:
                            stats['history_boundary'] += 1
                            break
                        if stop or not next_url:
                            break
                        if urlsplit(next_url).hostname != urlsplit(final).hostname:
                            warnings['Следующая страница ведёт на другую страну.'] = True
                            outcome = 'partial'
                            break
                        url = next_url
                        if page_index + 1 == MAX_PAGES:
                            outcome = 'limit'
                    if stop:
                        break
        except asyncio.CancelledError:
            outcome = 'stopped'
            raise
        except Forbidden:
            self.save(chat, enabled=0)
            report_allowed = False
        except Exception:
            outcome = 'error'
            stats['errors'] += 1
            warnings['Ошибка проверки; подробности записаны в логах Render.'] = True
            log.exception('Проверка прервана для chat=%s', chat)
        finally:
            if progress_task is not None:
                progress_task.cancel()
                with suppress(asyncio.CancelledError):
                    await progress_task
            if outcome == 'complete' and warnings:
                outcome = 'partial'
            if stats['errors'] and (not stats['pages']) and (outcome not in {'stopped'}):
                outcome = 'error'
            for warning in warnings:
                log.warning('[scan_detail] chat=%s %s', chat, error_text(warning))
            report = report_text(stats, time.monotonic() - started, outcome)
            if failure_reasons:
                report += '\n\n<b>Причина:</b>\n' + '\n'.join((escape(reason) for reason in dict.fromkeys(failure_reasons)))[:1200]
            elif stats['errors'] and (not stats['pages']):
                report += '\n\nСтраница поиска не получена. Проверьте выдачу командой /testsource.'
            with suppress(sqlite3.Error):
                self.save(chat, last=report, next_check=time.time() + self.state(chat)['minutes'] * 60)
            if self.tasks.get(chat) is asyncio.current_task():
                self.tasks.pop(chat, None)
            if report_allowed and (not self.closing):
                markup = InlineKeyboardMarkup([*([[InlineKeyboardButton('🔎 Проверить страницу поиска', callback_data='ui:testsource')]] if stats['errors'] else []), [InlineKeyboardButton('🔄 Перезапустить парсер', callback_data='restart_scan')], [InlineKeyboardButton('🏠 Главное меню', callback_data='menu_home')]])
                try:
                    await telegram_call(self.bot.send_message, chat_id=chat, text=report, parse_mode='HTML', reply_markup=markup)
                except Forbidden:
                    self.save(chat, enabled=0)
                except TelegramError:
                    log.exception('Не удалось доставить итоговый отчёт')

    async def close(self):
        self.closing = True
        tasks = list(self.tasks.values())
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        try:
            await self.reader.close()
            async with self.browser_lock:
                await self.public_browser.close()
        finally:
            self.db.close()

class BrowserUnavailable(ValueError):
    pass

class RemoteChromeDesktop:
    width, height = (1000, 900)
    VNC_READY_SECONDS = 25
    HOLD_DISPLAY = "import json,os,sys; print(json.dumps({'display':os.environ['DISPLAY'],'authority':os.environ['XAUTHORITY']}),flush=True); sys.stdin.buffer.read(1)"
    ERROR_PATTERNS = {'X_SERVER_FAILED': 'xvfb failed to start', 'X_AUTH_REJECTED': 'authorization required|authorization failed|invalid mit-magic-cookie|no protocol specified', 'X_DISPLAY_UNAVAILABLE': 'xopendisplay failed|unable to open display|cannot open display', 'X_LISTEN_FAILED': 'cannot establish any listening sockets|failed to open listener', 'X_KEYBOARD_FAILED': 'failed to activate virtual core keyboard|failed to compile keymap', 'TEMP_WRITE_FAILED': 'permission denied|read-only file system|no space left on device', 'VNC_BIND_FAILED': 'address already in use|unable to bind|failed to bind', 'OPTION_REJECTED': 'unrecognized option|unknown option|invalid option'}

    def __init__(self):
        self.lock = asyncio.Lock()
        self.processes, self._monitors = ([], [])
        self.display, self.port, self.environment = ('', None, {})
        self.issue, self.flags, self.progress = ('', set(), set())
        self._temporary = None
        self._startup_log = None

    @property
    def running(self):
        return len(self.processes) == 2 and all((p.returncode is None for p in self.processes))

    async def _observe_errors(self, stream):
        tail = ''
        while (chunk := (await stream.read(2048))):
            tail = (tail + chunk.decode('utf-8', errors='replace'))[-4096:]
            for label, pattern in {'X_DISPLAY_OPENED': 'Using X display', 'FRAMEBUFFER_READY': 'Read initial data from X display into framebuffer', 'VNC_LISTENING': 'Listening for VNC connections on TCP port'}.items():
                if re.search(pattern, tail, re.I):
                    self.progress.add(label)
            for code, pattern in self.ERROR_PATTERNS.items():
                if re.search(pattern, tail, re.I):
                    self.flags.add(code)

    def _consume_startup_log(self):
        if self._startup_log is not None:
            try:
                with self._startup_log.open('rb') as stream:
                    stream.seek(0, 2)
                    stream.seek(max(0, stream.tell() - 8192))
                    text = stream.read(8192).decode('utf-8', errors='replace')
                for code, pattern in self.ERROR_PATTERNS.items():
                    if re.search(pattern, text, re.I):
                        self.flags.add(code)
            except OSError:
                pass
            with suppress(OSError):
                self._startup_log.unlink()
            self._startup_log = None

    async def _exit_code(self, process):
        try:
            return str(await asyncio.wait_for(process.wait(), 1))
        except asyncio.TimeoutError:
            return 'UNKNOWN'

    async def start(self):
        async with self.lock:
            if self.running:
                return
            await self._stop()
            self.issue, self.flags, self.progress = ('DEPENDENCIES', set(), set())
            if any((shutil.which(name) is None for name in ('xvfb-run', 'Xvfb', 'xauth', 'x11vnc'))):
                raise BrowserUnavailable('Не найдены программы удалённого экрана (DEPENDENCIES).')
            try:
                self.issue = 'XVFB_START'
                self._temporary = tempfile.TemporaryDirectory(prefix='opensooq-xvfb-')
                self._startup_log = Path(self._temporary.name) / 'startup.log'
                self._startup_log.touch(mode=384)
                process = await asyncio.create_subprocess_exec('xvfb-run', '--auto-servernum', '--error-file=' + str(self._startup_log), '--server-args=-screen 0 1000x900x24 -nolisten tcp -noreset', sys.executable, '-u', '-c', self.HOLD_DISPLAY, stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE, start_new_session=True)
                self.processes.append(process)
                self._monitors.append(asyncio.create_task(self._observe_errors(process.stderr)))
                try:
                    ready = await asyncio.wait_for(process.stdout.readline(), 12)
                except asyncio.TimeoutError:
                    self.issue = 'XVFB_TIMEOUT'
                    raise
                if not ready:
                    self.issue = 'XVFB_EXIT_' + await self._exit_code(process)
                    raise RuntimeError('X display wrapper exited')
                self.issue = 'XVFB_REPLY'
                if len(ready) > 8192:
                    raise ValueError('Invalid display reply')
                reply = json.loads(ready)
                if not isinstance(reply, dict):
                    raise ValueError('Invalid display reply')
                display, authority = (reply.get('display'), reply.get('authority'))
                if not isinstance(display, str) or not re.fullmatch(':\\d+(?:\\.\\d+)?', display) or (not isinstance(authority, str)) or (not Path(authority).is_file()):
                    raise ValueError('Invalid display reply')
                self.display = display
                self.environment = {'DISPLAY': display, 'XAUTHORITY': authority}
                self._consume_startup_log()
                self.issue = 'VNC_START'
                with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as listener:
                    listener.bind(('127.0.0.1', 0))
                    self.port = listener.getsockname()[1]
                process = await asyncio.create_subprocess_exec('x11vnc', '-norc', '-display', display, '-auth', authority, '-nolookup', '-listen', '127.0.0.1', '-allow', '127.0.0.1', '-rfbport', str(self.port), '-rfbportv6', '-1', '-no6', '-nopw', '-forever', '-shared', '-noxdamage', '-noxrecord', '-nosel', '-noshm', stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE)
                self.processes.append(process)
                self._monitors.append(asyncio.create_task(self._observe_errors(process.stderr)))
                await self._wait_for_vnc()
                self.issue = ''
                return
            except BaseException:
                await self._stop()
                raise

    async def _wait_for_vnc(self):
        deadline = time.monotonic() + self.VNC_READY_SECONDS
        writer = None
        connected = False
        try:
            while True:
                for index, prefix in ((0, 'XVFB_EXIT_'), (1, 'VNC_EXIT_')):
                    if self.processes[index].returncode is not None:
                        self.issue = prefix + str(self.processes[index].returncode)
                        raise RuntimeError('Desktop process exited')
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    self.issue = 'VNC_GREETING_TIMEOUT' if connected else 'VNC_PORT_TIMEOUT'
                    raise RuntimeError('VNC readiness timed out')
                self.issue = 'VNC_WAIT_PORT'
                try:
                    reader, writer = await asyncio.wait_for(asyncio.open_connection('127.0.0.1', self.port), min(1, remaining))
                except (OSError, asyncio.TimeoutError):
                    await asyncio.sleep(min(0.2, max(0, deadline - time.monotonic())))
                    continue
                connected = True
                self.progress.add('VNC_TCP_CONNECTED')
                self.issue = 'VNC_WAIT_GREETING'
                try:
                    greeting = await asyncio.wait_for(reader.readexactly(12), max(0.001, deadline - time.monotonic()))
                except asyncio.TimeoutError:
                    self.issue = 'VNC_GREETING_TIMEOUT'
                    raise RuntimeError('VNC greeting timed out') from None
                except (OSError, asyncio.IncompleteReadError):
                    self.issue = 'VNC_GREETING_CLOSED'
                    raise RuntimeError('VNC closed before greeting') from None
                if not re.fullmatch(b'RFB \\d{3}\\.\\d{3}\\n', greeting):
                    self.issue = 'VNC_PROTOCOL'
                    raise RuntimeError('Invalid VNC greeting')
                self.progress.add('VNC_RFB_READY')
                return
        finally:
            if writer is not None:
                writer.close()
                with suppress(Exception):
                    await asyncio.wait_for(writer.wait_closed(), 1)

    async def _stop(self):
        for index in range(len(self.processes) - 1, -1, -1):
            process = self.processes[index]
            if process.returncode is None:
                if index == 0 and process.stdin is not None:
                    process.stdin.close()
                else:
                    with suppress(ProcessLookupError):
                        process.terminate()
                try:
                    await asyncio.wait_for(process.wait(), 4)
                except asyncio.TimeoutError:
                    if index == 0:
                        with suppress(ProcessLookupError):
                            os.killpg(process.pid, signal.SIGTERM)
                    else:
                        with suppress(ProcessLookupError):
                            process.terminate()
                    try:
                        await asyncio.wait_for(process.wait(), 2)
                    except asyncio.TimeoutError:
                        if index == 0:
                            with suppress(ProcessLookupError):
                                os.killpg(process.pid, signal.SIGKILL)
                        else:
                            with suppress(ProcessLookupError):
                                process.kill()
                        await process.wait()
        self.processes.clear()
        for task in self._monitors:
            try:
                await asyncio.wait_for(task, 0.5)
            except (asyncio.TimeoutError, asyncio.CancelledError):
                pass
        self._monitors.clear()
        self._consume_startup_log()
        if self._temporary is not None:
            self._temporary.cleanup()
            self._temporary = None
        self.display, self.port, self.environment = ('', None, {})

    async def close(self):
        async with self.lock:
            await self._stop()

async def check_desktop():
    desktop = RemoteChromeDesktop()
    try:
        await desktop.start()
        print('[desktop_check] XVFB_VNC_OK', flush=True)
        return 0
    except Exception:
        print('[desktop_check_failed] ' + (desktop.issue or 'UNKNOWN') + (' ' + ','.join(sorted(desktop.flags)) if desktop.flags else ''), flush=True)
        return 44
    finally:
        await desktop.close()

def opensooq_browser_launch_options():
    _, browser_proxy = proxy_settings(os.getenv('OPENSOOQ_PROXY_URL', ''))
    options = {'headless': True, 'args': ['--disable-dev-shm-usage']}
    if browser_proxy is not None:
        options['proxy'] = browser_proxy
    return options

def public_navigation_allowed(url, top_frame):
    parsed = urlsplit(url)
    host = parsed.hostname or ''
    if parsed.scheme not in {'http', 'https'} or parsed.username or parsed.password:
        return False
    if host == 'opensooq.com' or host.endswith('.opensooq.com'):
        return True
    return not top_frame and parsed.scheme == 'https' and (host in {'www.google.com', 'recaptcha.google.com', 'www.recaptcha.net', 'recaptcha.net'}) and (parsed.port in {None, 443}) and parsed.path.startswith('/recaptcha/')

class PublicChromeBrowser:

    def __init__(self, directory=None):
        self.directory = Path(directory) if directory is not None else DATA_DIR / 'opensooq-public-profile'
        self.lock = asyncio.Lock()
        self.pw = self.context = self.page = None
        self._file_lock = None
        self.desktop = RemoteChromeDesktop()
        self.startup_stage, self.startup_issue = ('idle', '')
        self.on_blocked = None

    def _acquire_profile(self):
        import fcntl
        self.directory.mkdir(parents=True, exist_ok=True, mode=448)
        os.chmod(self.directory, 448)
        fd = os.open(self.directory / '.bot-profile.lock', os.O_RDWR | os.O_CREAT, 384)
        try:
            os.fchmod(fd, 384)
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BaseException:
            os.close(fd)
            raise
        self._file_lock = fd

    def _release_profile(self):
        if self._file_lock is not None:
            fd, self._file_lock = (self._file_lock, None)
            os.close(fd)

    def _context_closed(self, context):
        if self.context is context:
            self.context = self.page = None

    async def _restrict_navigation(self, route):
        request = route.request
        if request.is_navigation_request():
            try:
                allowed = public_navigation_allowed(request.url, request.frame.parent_frame is None)
            except (ValueError, AttributeError):
                allowed = False
            if not allowed:
                if self.on_blocked is not None:
                    self.on_blocked(request)
                await route.abort()
                return
        await route.continue_()

    async def get_page(self):
        async with self.lock:
            if self.context is not None and self.desktop.running:
                if self.page is None or self.page.is_closed():
                    self.page = await self.context.new_page()
                    self.page.set_default_timeout(12000)
                self.startup_stage, self.startup_issue = ('ready', '')
                return (self.context, self.page)
            await self._shutdown()
            try:
                self._acquire_profile()
            except BlockingIOError:
                raise BrowserUnavailable('Постоянный профиль уже используется другим процессом.') from None
            try:
                self.startup_stage = 'display'
                await self.desktop.start()
                self.startup_stage = 'chrome'
                from playwright.async_api import async_playwright
                self.pw = await async_playwright().start()
                launch_options = opensooq_browser_launch_options()
                launch_options.update(headless=False, channel='chrome', env={**os.environ, **self.desktop.environment}, no_viewport=True, args=['--disable-dev-shm-usage', '--window-position=0,0', '--window-size=1000,900'])
                self.context = await self.pw.chromium.launch_persistent_context(str(self.directory), **launch_options, locale='en-US', accept_downloads=False, timeout=30000)
                self.context.on('close', self._context_closed)
                await self.context.route('**/*', self._restrict_navigation)
                pages = [page for page in self.context.pages if not page.is_closed()]
                self.page = pages[0] if pages else await self.context.new_page()
                self.page.set_default_timeout(12000)
                self.startup_stage, self.startup_issue = ('ready', '')
                return (self.context, self.page)
            except asyncio.CancelledError:
                await self._shutdown()
                raise
            except Exception as error:
                code = getattr(self.desktop, 'issue', '') or type(error).__name__ if self.startup_stage == 'display' else type(error).__name__
                self.startup_issue = self.startup_stage + ':' + code
                await self._shutdown()
                label = 'экран' if self.startup_stage == 'display' else 'Chrome'
                raise BrowserUnavailable('Не удалось запустить ' + label + ' (' + code + ').') from None

    async def _shutdown(self):
        context, pw = (self.context, self.pw)
        self.context = self.page = self.pw = None
        try:
            if context is not None:
                with suppress(Exception):
                    await asyncio.wait_for(context.close(), timeout=10)
        finally:
            try:
                if pw is not None:
                    with suppress(Exception):
                        await asyncio.wait_for(pw.stop(), timeout=10)
            finally:
                try:
                    await self.desktop.close()
                finally:
                    self._release_profile()

    async def close(self):
        async with self.lock:
            await self._shutdown()

def access_date(value):
    return datetime.fromtimestamp(value, DISPLAY_TZ).strftime('%d.%m.%Y %H:%M %Z') if value else 'нет активного периода'

def admin_target(value):
    try:
        target = int(str(value).strip())
    except (ValueError, TypeError):
        raise ValueError('Укажите Telegram ID пользователя числом.') from None
    if target <= 0:
        raise ValueError('Telegram ID должен быть положительным.')
    if target == ADMIN_ID:
        raise ValueError('Доступ администратора изменять нельзя.')
    return target

async def admin_panel(update, context, page=0, notice=''):
    if update.effective_user.id != ADMIN_ID:
        raise ValueError('Доступ закрыт.')
    service = context.application.bot_data['service']
    known = set(service.allowed) | set(service.revoked)
    for table in ('users', 'authorized'):
        known.update((row['chat'] for row in service.db.execute('SELECT chat FROM ' + table)))
    users = sorted((target for target in known if target > 0 and target != ADMIN_ID))
    pages = max(1, (len(users) + 9) // 10)
    page = max(0, min(page, pages - 1))
    lines = ['👑 <b>Пользователи</b>', '', f'Известных пользователей: <b>{len(users)}</b>', '🟢 доступ открыт · 🚫 отозван · ⛔ заблокирован · ⚪ ожидает входа', '']
    rows = []
    for target in users[page * 10:(page + 1) * 10]:
        badge = '⛔' if is_blocked(target) else '🚫' if target in service.revoked else '🟢' if service.permitted(target) else '⚪'
        lines.append(f'{badge} <code>{target}</code>')
        rows.append([(f'{badge} {target}', f'ui:admin:user:{target}')])
    navigation = []
    if page:
        navigation.append(('‹ Назад', f'ui:admin:page:{page - 1}'))
    if page + 1 < pages:
        navigation.append(('Далее ›', f'ui:admin:page:{page + 1}'))
    if navigation:
        rows.append(navigation)
    rows.extend([[('🔑 Выдать пароль', 'ui:admin:choose:create'), ('🚫 Отозвать доступ', 'ui:admin:choose:revoke')], [('⛔ Блокировать', 'ui:admin:choose:block'), ('✅ Разблокировать', 'ui:admin:choose:unblock')], [('‹ Главное меню', 'menu_home')]])
    text = '\n'.join(lines)
    if notice:
        text = escape(notice) + '\n\n' + text
    await show_panel(update, text, ui_keyboard(rows))

async def admin_confirmation(update, context, kind, target):
    if update.effective_user.id != ADMIN_ID:
        raise ValueError('Доступ закрыт.')
    target = admin_target(target)
    descriptions = {'create': 'Выдать новый пароль? Старый пароль и текущая авторизация будут отозваны, мониторинг остановится.', 'revoke': 'Отозвать пароль и доступ? Пользователь потеряет авторизацию, его мониторинг остановится.', 'block': 'Заблокировать пользователя и остановить его мониторинг?', 'unblock': 'Снять блокировку пользователя? Отозванный пароль этим действием не восстанавливается.'}
    if kind not in descriptions:
        raise ValueError('Неизвестное действие.')
    await show_panel(update, f'👤 <code>{target}</code>\n\n' + descriptions[kind], ui_keyboard([[('Подтвердить', f'ui:admin:apply:{kind}:{target}'), ('Отмена', 'ui:admin')]]))

async def admin_callback(update, context, data):
    if update.effective_user.id != ADMIN_ID:
        raise ValueError('Доступ закрыт.')
    service = context.application.bot_data['service']
    parts = data.split(':')
    if data == 'ui:admin':
        await admin_panel(update, context)
    elif len(parts) == 4 and parts[2] == 'page':
        await admin_panel(update, context, int(parts[3]))
    elif len(parts) == 4 and parts[2] == 'choose':
        kind = parts[3]
        if kind not in {'create', 'revoke', 'block', 'unblock'}:
            raise ValueError('Неизвестное действие.')
        await ask_field(update, context, 'admin_target', '👤 <b>Telegram ID пользователя</b>\nПопросите пользователя отправить боту /id и пришлите полученное число.', kind=kind)
    elif len(parts) == 4 and parts[2] == 'user':
        target = admin_target(parts[3])
        state = service.state(target)
        status = 'заблокирован' if is_blocked(target) else 'доступ отозван' if target in service.revoked else 'доступ открыт' if service.permitted(target) else 'ожидает входа'
        await show_panel(update, f"👤 <b>Пользователь</b> <code>{target}</code>\n\nСтатус: {status}\nКатегорий: {len(state['urls'])}\nМониторинг: {('включён' if state['enabled'] else 'выключен')}", ui_keyboard([[('🔑 Новый пароль', f'ui:admin:confirm:create:{target}'), ('🚫 Отозвать', f'ui:admin:confirm:revoke:{target}')], [('⛔ Блокировать', f'ui:admin:confirm:block:{target}'), ('✅ Разблокировать', f'ui:admin:confirm:unblock:{target}')], [('‹ Пользователи', 'ui:admin')]]))
    elif len(parts) == 5 and parts[2] == 'confirm':
        await admin_confirmation(update, context, parts[3], admin_target(parts[4]))
    elif len(parts) == 5 and parts[2] == 'apply':
        kind, target = (parts[3], admin_target(parts[4]))
        if kind == 'create':
            await service.revoke_access(target)
            password = ''.join((secrets.choice(string.ascii_letters + string.digits) for _ in range(12)))
            save_user_password(target, password)
            await update.callback_query.message.reply_text(f'🔑 Новый пароль для <code>{target}</code>:\n<code>{password}</code>\n\nПередайте пароль пользователю. Его старый доступ отозван.', parse_mode='HTML')
            notice = f'Пароль для {target} создан.'
        elif kind == 'revoke':
            await service.revoke_access(target)
            notice = f'🚫 Пароль и доступ пользователя {target} отозваны.'
        elif kind == 'block':
            block_user(target)
            service.state(target)
            service.save(target, enabled=0)
            await service.cancel_scan(target)
            notice = f'⛔ Пользователь {target} заблокирован.'
        elif kind == 'unblock':
            unblock_user(target)
            notice = f'✅ Блокировка пользователя {target} снята.'
        else:
            raise ValueError('Неизвестное действие.')
        await admin_panel(update, context, notice=notice)
    else:
        raise ValueError('Кнопка устарела. Откройте админ-панель заново.')

async def handle_commands(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, user, chat = (update.effective_message, update.effective_user, update.effective_chat)
    if not message or not message.text or (not user) or (not chat) or (chat.type != 'private'):
        return
    service = context.application.bot_data['service']
    text = message.text.strip()
    parts = text.split(maxsplit=1)
    if not parts:
        return
    command, argument = (parts[0].split('@')[0].lower(), parts[1] if len(parts) > 1 else '')
    if is_blocked(user.id):
        await message.reply_text('⛔ Вы заблокированы.')
        return
    if command == '/id':
        await message.reply_text(f'Ваш Telegram ID: {user.id}')
        return
    try:
        if command in {'/admin', '/createpass', '/block', '/unblock'}:
            if user.id != ADMIN_ID:
                return
            if command == '/admin':
                await message.reply_text('👑 Админ-панель\n/createpass ID — создать пароль\n/block ID — заблокировать\n/unblock ID — разблокировать')
                return
            target = int(argument)
            if target <= 0:
                raise ValueError('Укажите положительный Telegram ID.')
            if command == '/createpass':
                password = ''.join((secrets.choice(string.ascii_letters + string.digits) for _ in range(12)))
                await service.revoke_access(target)
                save_user_password(target, password)
                await message.reply_text(f'Пароль для {target}: <code>{password}</code>', parse_mode='HTML')
            elif command == '/block':
                if target == ADMIN_ID:
                    raise ValueError('Нельзя заблокировать администратора.')
                block_user(target)
                service.state(target)
                service.save(target, enabled=0)
                await service.cancel_scan(target)
                await message.reply_text(f'Пользователь {target} заблокирован.')
            else:
                unblock_user(target)
                await message.reply_text(f'Пользователь {target} разблокирован.')
            return
        if not service.permitted(user.id):
            if check_user_password(user.id, text):
                service.authorize(user.id)
                await message.reply_text('✅ Доступ открыт. Отправьте ссылку на категорию.', reply_markup=get_main_menu())
            else:
                await message.reply_text('🔒 Бот приватный. Введите выданный пароль.')
            return
        state = service.state(chat.id)
        if command == '/start':
            await message.reply_text('👋 Отправьте ссылку на категорию OpenSooq или выберите действие.', reply_markup=get_main_menu())
        elif command == '/help':
            await message.reply_text(help_text(user.id))
        elif command in {'/filters', '/set'}:
            if argument:
                state['rules'] = update_filters(state['rules'], argument)
                service.save(chat.id, rules=state['rules'])
            await message.reply_text(filters_text(state), parse_mode='HTML')
        elif command == '/reset':
            service.save(chat.id, rules={})
            await message.reply_text('✅ Фильтры сброшены.')
        elif command == '/testsource':
            await test_source_message(update, context)
        elif command == '/testproxy':
            if not service.reader.proxy_url:
                await message.reply_text('Добавьте OPENSOOQ_PROXY_URL в Environment на Render и перезапустите сервис.')
                return
            await message.reply_text('Проверяю профиль chilltime Ali через настроенный прокси…')
            try:
                raw, _ = await service.reader.get('https://kw.opensooq.com/en/mid/member-103907011724500523077')
                profile = await asyncio.to_thread(parse_profile, raw, '39101505')

                def value(key):
                    item = profile.get(key)
                    return 'нет данных' if item is None else str(item)
                await message.reply_text(f"Профиль загружен: HTTP 200.\nПросмотры: {value('seller_views')}\nАктивных объявлений: {value('listings_count')}\nПродано: {value('sold')}\nРейтинг: {value('rating')}\nОценок: {value('ratings')}\nОтзывов: {value('reviews')}")
            except (SourceError, ValueError) as exc:
                await message.reply_text('Проверка профиля: ' + error_text(exc)[:700])
        elif command == '/sources':
            sources = '\n'.join((f'{i}. {u}' for i, u in enumerate(state['urls'], 1)))
            await message.reply_text((sources or 'Категории не добавлены. Отправьте ссылку.')[:3900], disable_web_page_preview=True)
        elif command == '/remove':
            index = int(argument) - 1
            if not 0 <= index < len(state['urls']):
                raise ValueError('Нет категории с таким номером. См. /sources.')
            state['urls'].pop(index)
            service.save(chat.id, urls=state['urls'])
            await message.reply_text('✅ Категория удалена.')
        elif command == '/interval':
            minutes = int(argument)
            if not 5 <= minutes <= 1440:
                raise ValueError('Интервал: 5–1440 минут.')
            service.save(chat.id, minutes=minutes, next_check=time.time() + minutes * 60)
            await message.reply_text(f'Интервал: {minutes} мин.')
        elif command in {'/pause', '/stop'}:
            service.save(chat.id, enabled=0)
            await service.cancel_scan(chat.id)
            await message.reply_text('⏸ Мониторинг остановлен.')
        elif command == '/status':
            active = chat.id in service.tasks and (not service.tasks[chat.id].done())
            status = f"Мониторинг: {('включён' if state['enabled'] else 'выключен')}\nПроверка: {('выполняется' if active else 'не выполняется')}\nИнтервал: {state['minutes']} мин.\nКатегорий: {len(state['urls'])}\n\n"
            await message.reply_text(escape(status) + (state['last'] or 'Проверок ещё не было.'), parse_mode='HTML')
        elif command in {'/check', '/deepcheck', '/watch', '/restart', '/add'} or text.startswith(('https://', 'http://')):
            if command == '/add' or text.startswith(('https://', 'http://')):
                url = safe_url(argument if command == '/add' else text)
                if re.search('/(?:search|lists)/\\d+', urlsplit(url).path):
                    raise ValueError('Нужна ссылка на категорию, а не на отдельное объявление.')
                if url not in state['urls']:
                    if len(state['urls']) >= 5:
                        raise ValueError('Максимум 5 категорий.')
                    state['urls'].append(url)
                    service.save(chat.id, urls=state['urls'])
            if not active_sources(state):
                raise ValueError('Добавьте категорию и включите её страну в меню «Страны».')
            if command == '/watch':
                service.save(chat.id, enabled=1)
            if command == '/restart':
                await service.cancel_scan(chat.id)
            started = service.trigger(chat.id, deep=command == '/deepcheck')
            await message.reply_text('🚀 Проверка запущена.' if started else '⏳ Проверка уже выполняется.')
        else:
            await message.reply_text('Отправьте ссылку на категорию или /help.')
    except ValueError as exc:
        await message.reply_text(str(exc)[:800] or 'Проверьте параметры команды: /help.')

def ui_keyboard(rows):
    return InlineKeyboardMarkup([[InlineKeyboardButton(label, callback_data=data) for label, data in row] for row in rows])

def ui_number(value):
    return f'{value:g}' if isinstance(value, float) else str(value)

def ui_range(rules, metric):
    low, high = (rules.get(metric + '_min'), rules.get(metric + '_max'))
    if low is None and high is None:
        return 'без ограничений'
    if low is not None and high is not None:
        return f'{ui_number(low)}–{ui_number(high)}'
    return 'от ' + ui_number(low) if low is not None else 'до ' + ui_number(high)

def ui_url(url):
    return escape(url if len(url) <= 180 else url[:177] + '…')

def metric_input(rules, metric, text):
    if metric not in FILTER_LABELS:
        raise ValueError('Неизвестный фильтр.')
    text = unicodedata.normalize('NFKC', text).strip()
    if text.lower() in {'off', 'none'}:
        result = dict(rules)
        result.pop(metric + '_min', None)
        result.pop(metric + '_max', None)
        return result
    match = re.fullmatch('(?:от\\s*)?(\\d+(?:[.,]\\d+)?)\\s*(?:-|–|—|\\.\\.|до)\\s*(\\d+(?:[.,]\\d+)?)', text, re.I)
    if match:
        return update_filters(rules, f'{metric}_min={match[1]} {metric}_max={match[2]}')
    if not re.fullmatch('\\d+(?:[.,]\\d+)?', text):
        raise ValueError('Введите диапазон, например 1-99999, либо одно число для максимума. Убрать ограничение: off.')
    return update_filters(rules, f'{metric}_max={text}')

def source_key(url):
    return hashlib.sha256(url.encode()).hexdigest()[:16]

def country_code(url):
    return (urlsplit(url).hostname or '').split('.')[0]

def active_sources(state):
    disabled = set(state.get('disabled_countries', []))
    urls = [url for url in state['urls'] if isinstance(url, str) and country_code(url) not in disabled]
    if state.get('country_mode', 'single') == 'all':
        return urls
    selected = state.get('selected_country') or (country_code(urls[0]) if urls else '')
    return [url for url in urls if country_code(url) == selected]

async def country_panel(update, context, notice='', code=None):
    service = context.application.bot_data['service']
    state = service.state(update.effective_chat.id)
    disabled = set(state.get('disabled_countries', []))
    present = {country_code(url) for url in state['urls'] if isinstance(url, str)}
    mode = state.get('country_mode', 'single')
    selected = state.get('selected_country') or next((country_code(url) for url in active_sources(state)), '')
    mode_text = '🌐 Все включённые страны' if mode == 'all' else '🎯 Одна страна: ' + COUNTRY_LABELS.get(selected, 'выберите ниже')
    if code is not None:
        if code not in COUNTRY_LABELS:
            raise ValueError('Неизвестная страна.')
        enabled = code in present and code not in disabled
        status = '🟢 Включена' if enabled else '⏸ Отключена' if code in present else 'Ещё не добавлена'
        text = f'<b>{COUNTRY_LABELS[code]}</b>\n\n{mode_text}\n{status}\n\n«Искать только здесь» выбирает одну страну.\nОбщий поиск запускается только в режиме «Все включённые страны».\nФильтры общие; пересчёта валют нет.'
        rows = [[('🎯 Искать только здесь', 'ui:country_select:' + code)], [('⏸ Отключить' if enabled else '＋ Включить страну', f'ui:country_toggle:{code}:' + ('off' if enabled else 'on'))], [('📂 Категории', 'menu_sources')], [('‹ Все страны', 'ui:countries')]]
    else:
        text = '🌍 <b>Страны поиска</b>\n\n' + mode_text + '\n\nВыберите страну и нажмите «Искать только здесь».\nДля общего поиска включите отдельный режим ниже.'
        rows = [[(('🎯 ' if mode == 'single' and item == selected and (item not in disabled) else '🟢 ' if item in present and item not in disabled else '⏸ ' if item in present else '＋ ') + label, 'ui:country:' + item)] for item, label in COUNTRY_LABELS.items()]
        rows.extend([[('✓ Одна страна' if mode == 'single' else '🎯 Одна страна', 'ui:country_mode:single')], [('✓ Все включённые страны' if mode == 'all' else '🌐 Все включённые страны', 'ui:country_mode:all')], [('‹ Главное меню', 'menu_home')]])
    if notice:
        text = escape(notice) + '\n\n' + text
    await show_panel(update, text, ui_keyboard(rows))

def source_country(url):
    code = (urlsplit(url).hostname or '').split('.')[0]
    return COUNTRY_LABELS.get(code, 'OpenSooq')

def checked_source(value):
    url = safe_url(value)
    if re.search('/(?:search|lists)/\\d+', urlsplit(url).path):
        raise ValueError('Нужна ссылка на категорию или выдачу, а не на отдельное объявление.')
    return url

def get_main_menu():
    rows = [[('🔎 Найти объявления', 'menu_check')], [('🌍 Страны', 'ui:countries'), ('📂 Категории', 'menu_sources')], [('⚙️ Фильтры', 'menu_filters'), ('💾 Поиски', 'ui:saved')], [('⏱ Мониторинг', 'ui:monitor'), ('📊 Результаты', 'menu_status')], [('⏸ Остановить', 'menu_stop'), ('❔ Помощь', 'menu_help')]]
    return ui_keyboard(rows)

def filters_text(state):
    rules = state['rules']
    lines = ['⚙️ <b>Фильтры поиска</b>', '', 'Нажмите на поле, чтобы изменить его.', 'Цена сравнивается в валюте объявления; пересчёта валют нет.', '']
    for metric, label in FILTER_LABELS.items():
        lines.append(f'{label}: <b>{escape(ui_range(rules, metric))}</b>')
    for field, label in TEXT_LABELS.items():
        lines.append(f"{label}: <b>{escape(str(rules.get(field) or 'не задано'))}</b>")
    lines.extend(['', 'Неизвестные значения: ' + ('разрешены при числовых ограничениях' if rules.get('unknown') == 'include' else 'исключаются при заданных ограничениях'), 'Слова для поиска работают по принципу «хотя бы одно».', 'Авто, недвижимость, услуги и вакансии исключаются по категории.'])
    return '\n'.join(lines)

def saved_rows(service, chat):
    return list(service.db.execute('SELECT id,name,config FROM saved_searches WHERE chat=? ORDER BY id DESC', (chat,)))

def saved_row(service, chat, search_id):
    row = service.db.execute('SELECT * FROM saved_searches WHERE chat=? AND id=?', (chat, search_id)).fetchone()
    if row is None:
        raise ValueError('Этот сохранённый поиск уже удалён.')
    return row

def save_search(service, chat, name):
    name = ' '.join(name.split())
    if not name or len(name) > 50 or name.startswith(('http://', 'https://')):
        raise ValueError('Название: от 1 до 50 символов.')
    state = service.state(chat)
    if not state['urls']:
        raise ValueError('Сначала добавьте хотя бы одну категорию.')
    if len(saved_rows(service, chat)) >= 20:
        raise ValueError('Можно сохранить до 20 поисков. Удалите один из старых.')
    config = {key: state[key] for key in ('urls', 'rules', 'minutes', 'disabled_countries', 'country_mode', 'selected_country')}
    try:
        with service.db:
            service.db.execute('INSERT INTO saved_searches(chat,name,config,created) VALUES (?,?,?,?)', (chat, name, json.dumps(config, ensure_ascii=False), time.time()))
    except sqlite3.IntegrityError:
        raise ValueError('Поиск с таким названием уже есть.') from None

async def load_search(service, chat, search_id):
    row = saved_row(service, chat, search_id)
    config = json.loads(row['config'])
    urls = [checked_source(url) for url in config['urls']]
    if not 1 <= len(urls) <= 5:
        raise ValueError('Некорректные категории в сохранённом поиске.')
    minutes = int(config['minutes'])
    if not 5 <= minutes <= 1440:
        raise ValueError('Некорректный интервал в сохранённом поиске.')
    rules = dict(config['rules'])
    service.save(chat, enabled=0)
    await service.cancel_scan(chat)
    service.save(chat, urls=urls, rules=rules, minutes=minutes, disabled_countries=[code for code in config.get('disabled_countries', []) if code in COUNTRIES], country_mode='all' if config.get('country_mode') == 'all' else 'single', selected_country=config.get('selected_country', '') if config.get('selected_country', '') in COUNTRIES else '', enabled=0, next_check=time.time() + minutes * 60)
    return row['name']



def home_banner_file():
    stream = BytesIO(base64.b64decode(HOME_BANNER_BASE64))
    stream.name = 'search-menu.jpg'
    return stream

def remember_banner(cache, message):
    photos = getattr(message, 'photo', None)
    if isinstance(photos, (list, tuple)) and photos:
        cache['home_banner_file_id'] = photos[-1].file_id

async def show_home_banner(update, context, text, keyboard):
    cache = context.application.bot_data if context is not None else {}
    query = update.callback_query
    message = query.message if query and query.message else update.effective_message
    cached = cache.get('home_banner_file_id')
    if query and query.message:
        choices = [cached, None] if cached else [None]
        for file_id in choices:
            try:
                result = await message.edit_media(
                    media=InputMediaPhoto(media=file_id or home_banner_file(), caption=text, parse_mode='HTML'),
                    reply_markup=keyboard)
                remember_banner(cache, result)
                return
            except BadRequest as exc:
                if 'message is not modified' in str(exc).lower():
                    return
                cache.pop('home_banner_file_id', None)
            except Forbidden:
                raise
            except TelegramError:
                break
    try:
        result = await message.reply_photo(photo=cache.get('home_banner_file_id') or home_banner_file(),
                                           caption=text, parse_mode='HTML', reply_markup=keyboard)
        remember_banner(cache, result)
        if query and query.message:
            with suppress(TelegramError):
                await query.message.edit_reply_markup(reply_markup=None)
    except Forbidden:
        raise
    except TelegramError as exc:
        log.warning('[menu_banner] %s', error_text(exc))
        await show_panel(update, text, keyboard)

async def show_panel(update, text, keyboard, *, banner=False, context=None):
    if banner:
        await show_home_banner(update, context, text, keyboard)
        return
    options = dict(parse_mode='HTML', reply_markup=keyboard, disable_web_page_preview=True)
    query = update.callback_query
    if query and query.message:
        try:
            if getattr(query.message, 'photo', None):
                visible = BeautifulSoup(text, 'html.parser').get_text()
                if len(visible.encode('utf-16-le')) // 2 <= 1024:
                    await query.message.edit_caption(caption=text, parse_mode='HTML', reply_markup=keyboard)
                    return
                await query.message.edit_reply_markup(reply_markup=None)
            else:
                await query.message.edit_text(text, **options)
                return
        except BadRequest as exc:
            if 'message is not modified' in str(exc).lower():
                return
        await query.message.reply_text(text, **options)
        return
    await update.effective_message.reply_text(text, **options)

async def panel(update, context, screen='home', notice=''):
    service = context.application.bot_data['service']
    chat = update.effective_chat.id
    state = service.state(chat)
    back = [('‹ Главное меню', 'menu_home')]
    if screen == 'sources':
        lines = ['🔗 <b>Категории поиска</b>', '', 'Каждую ссылку можно заменить или удалить.']
        rows = []
        for index, url in enumerate(state['urls'], 1):
            if not isinstance(url, str):
                continue
            status = ' · отключена' if country_code(url) in state.get('disabled_countries', []) else ''
            lines.append(f'\n<b>{index}. {source_country(url)}{status}</b>\n{ui_url(url)}')
            key = source_key(url)
            rows.append([(f'✏️ Заменить №{index}', 'ui:replace:' + key), (f'🗑 Удалить №{index}', 'ui:delete:' + key)])
        if not state['urls']:
            lines.append('\nПока нет категорий. Добавьте ссылку или выберите страну.')
        rows.extend([[('＋ Добавить ссылку', 'ui:add'), ('🌍 Выбрать страну', 'ui:countries')], back])
        text, keyboard = ('\n'.join(lines), ui_keyboard(rows))
    elif screen == 'filters':
        rows = []
        for key, label in FILTER_LABELS.items():
            rows.append([(label, 'ui:metric:' + key)])
        rows.extend([[('🔎 Искать слова', 'ui:field:keywords'), ('🚫 Исключить слова', 'ui:field:exclude')], [('💱 Валюта', 'ui:currency'), ('❔ Нет данных', 'ui:unknown')], [('↺ Сбросить фильтры', 'ui:reset')], back])
        text, keyboard = (filters_text(state), ui_keyboard(rows))
    elif screen == 'saved':
        records = saved_rows(service, chat)
        text = '💾 <b>Мои поиски</b>\n\nСохраняются категории, включённые страны, фильтры и интервал.\nЗагрузка заменяет текущие настройки и останавливает мониторинг.\n\n'
        text += f'Сохранено: <b>{len(records)}/20</b>' if records else 'Пока нет сохранённых поисков.'
        rows = [[(row['name'], f"ui:search:{row['id']}")] for row in records]
        rows.extend([[('＋ Сохранить текущий поиск', 'ui:save')], back])
        keyboard = ui_keyboard(rows)
    elif screen == 'monitor':
        text = f"⏱ <b>Мониторинг</b>\n\nСостояние: {('🟢 включён' if state['enabled'] else '⚪ выключен')}\nИнтервал: <b>{state['minutes']} мин.</b>\n\nПоиск начинается со свежих объявлений и пропускает уже проверенные объявления."
        keyboard = ui_keyboard([[('🟢 Включить', 'ui:watch'), ('⏸ Остановить', 'menu_stop')], [(f'{n} мин.', f'ui:interval:{n}') for n in (5, 15, 30, 60)], [('Другой интервал', 'ui:custom_interval')], back])
    elif screen == 'status':
        active = chat in service.tasks and (not service.tasks[chat].done())
        text = f"📊 <b>Статус</b>\n\nМониторинг: {('🟢 включён' if state['enabled'] else '⚪ выключен')}\nПроверка: {('выполняется или ожидает очереди' if active else 'не выполняется')}\nАктивных категорий: {len(active_sources(state))} из {len(state['urls'])} · Интервал: {state['minutes']} мин.\n\n" + ('Последний отчёт:\n' + state['last'] if state['last'] else 'Проверок ещё не было.')
        keyboard = get_main_menu()
    else:
        active = chat in service.tasks and (not service.tasks[chat].done())
        countries = ', '.join(dict.fromkeys((source_country(url) for url in active_sources(state)))) or 'нет включённых стран'
        search_status = '⏳ Выполняется или ожидает очереди' if active else 'Готов к поиску'
        watch_status = '🟢 Включён' if state['enabled'] else '⚪ Выключен'
        mode = '🌐 Поиск по включённым странам' if state.get('country_mode') == 'all' else '🎯 Поиск по одной стране'
        text = (f'<b>{mode}</b>\n{escape(countries)}\n\n'
                f'🔎 {search_status}\n'
                f"⏱ Мониторинг: {'включён' if state['enabled'] else 'выключен'} · {state['minutes']} мин.\n"
                f"📂 Категории: {len(active_sources(state))} · 💾 Поиски: {len(saved_rows(service, chat))}")
        keyboard = get_main_menu()
    if screen == 'home' and update.effective_user.id == ADMIN_ID:
        rows = list(keyboard.inline_keyboard)
        rows.append([InlineKeyboardButton('🌐 Прокси', callback_data='ui:proxies'), InlineKeyboardButton('👑 Пользователи', callback_data='ui:admin')])
        keyboard = InlineKeyboardMarkup(rows)
    if notice:
        text = escape(notice) + '\n\n' + text
    if screen == 'home':
        await show_panel(update, text, keyboard, banner=True, context=context)
    else:
        await show_panel(update, text, keyboard)

async def ask_field(update, context, action, prompt, **payload):
    context.user_data['panel_form'] = dict(action=action, payload=payload, expires=time.time() + 600)
    await show_panel(update, prompt + '\n\nОтправьте ответ одним сообщением. Отмена: /cancel', ui_keyboard([[('Отмена', 'ui:cancel')]]))

async def proxy_management_message(update, context):
    message, user, chat = (update.effective_message, update.effective_user, update.effective_chat)
    if not message or not message.text or (not user) or (not chat):
        return False
    text = message.text.strip()
    parts = text.split(maxsplit=1)
    command = parts[0].split('@')[0].lower() if parts else ''
    actions = {'/newproxy': 'new', '/addproxy': 'add', '/nextproxy': 'next', '/delproxy': 'delete'}
    pending = context.user_data.get('proxy_form')
    is_command = command in actions or command == '/proxies'
    if text.startswith('/') and (not is_command):
        context.user_data.pop('proxy_form', None)
        return False
    if not is_command and (not pending):
        return False
    if user.id != ADMIN_ID or chat.id != ADMIN_ID or chat.type != 'private':
        context.user_data.pop('proxy_form', None)
        await message.reply_text('Управление прокси доступно только владельцу.')
        return True
    service = context.application.bot_data['service']
    if command == '/proxies':
        context.user_data.pop('proxy_form', None)
        reader = service.reader
        lines = ['🌐 Прокси', '']
        for index, uri in enumerate(reader.proxy_pool):
            label = 'Основной' if index == 0 else 'Резервный'
            active = ' · активен' if index == reader.proxy_index else ''
            lines.append(f'{index + 1}. {label}: {proxy_label(uri)}{active}')
        lines.append('\n/newproxy — заменить основной\n/addproxy — добавить резервный\n/nextproxy — переключиться\n/delproxy НОМЕР — удалить резервный')
        await message.reply_text('\n'.join(lines))
        return True
    if is_command:
        context.user_data.pop('proxy_form', None)
        action, value = (actions[command], parts[1] if len(parts) == 2 else '')
        if action in {'new', 'add'} and (not value):
            context.user_data['proxy_form'] = {'action': action, 'expires': time.time() + 600}
            context.user_data.pop('panel_form', None)
            await message.reply_text('Пришлите HTTP-прокси одним сообщением:\nhttp://ЛОГИН:ПАРОЛЬ@СЕРВЕР:ПОРТ\nОтмена: /cancel')
            return True
    else:
        if pending['expires'] < time.time():
            context.user_data.pop('proxy_form', None)
            await message.reply_text('Время ввода истекло. Повторите /newproxy или /addproxy.')
            return True
        action, value = (pending['action'], text)
    try:
        await service.change_proxy(action, value)
    except (ValueError, OSError) as exc:
        label = str(exc) if isinstance(exc, ValueError) else 'Не удалось сохранить прокси. Проверьте постоянный диск и DATA_DIR.'
        await message.reply_text(label)
        return True
    context.user_data.pop('proxy_form', None)
    if action in {'new', 'add'}:
        with suppress(TelegramError):
            await message.delete()
    await message.reply_text('✅ Настройки прокси сохранены и применены без деплоя. Проверка: /testproxy. Список: /proxies.')
    return True

async def handle(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message, user, chat = (update.effective_message, update.effective_user, update.effective_chat)
    service = context.application.bot_data['service']
    if not message or not message.text or (not user) or (not chat) or (chat.type != 'private'):
        return
    if await proxy_management_message(update, context):
        return
    command = message.text.strip().split(maxsplit=1)[0].split('@')[0].lower() if message.text.strip() else ''
    if command in {'/account', '/account_off', '/account_diag', '/account_end', '/dialogs', '/dialog', '/chatstatus', '/stopdialogs', '/phrases'}:
        await message.reply_text('В этой версии оставлен публичный парсер. Вход в OpenSooq и диалоги отключены. Используйте /testsource и /check.')
        return
    if command == '/version':
        await message.reply_text('Версия v39.1 · Поиск объявлений · Chrome')
        return
    if not service.permitted(user.id):
        await handle_commands(update, context)
        return
    text = message.text.strip()
    command = text.split(maxsplit=1)[0].split('@')[0].lower() if text else ''
    form = context.user_data.get('panel_form')
    if text.startswith('/'):
        context.user_data.pop('panel_form', None)
        if command in {'/admin', '/users', '/revokepass', '/revoke'}:
            if user.id != ADMIN_ID:
                await message.reply_text('Эта команда доступна только администратору.')
                return
            if command in {'/revokepass', '/revoke'}:
                try:
                    target = admin_target(text.split(maxsplit=1)[1])
                    await service.revoke_access(target)
                    await message.reply_text(f'🚫 Пароль и доступ пользователя {target} отозваны. Мониторинг остановлен.')
                except (ValueError, IndexError) as exc:
                    await message.reply_text(str(exc) if isinstance(exc, ValueError) else 'Используйте /revokepass ID')
            else:
                await admin_panel(update, context)
            return
        if command in {'/start', '/cancel', '/sources', '/saved', '/status'}:
            await panel(update, context, {'/sources': 'sources', '/saved': 'saved', '/status': 'status'}.get(command, 'home'))
            return
        if command == '/filters' and len(text.split(maxsplit=1)) == 1:
            await panel(update, context, 'filters')
            return
        await handle_commands(update, context)
        return
    if form:
        if form['expires'] < time.time():
            context.user_data.pop('panel_form', None)
            await panel(update, context, notice='Время ввода истекло. Выберите действие заново.')
            return
        action, payload = (form['action'], form['payload'])
        state = service.state(chat.id)
        screen, notice = ('home', '✅ Сохранено.')
        try:
            if action in {'add', 'replace'}:
                url = checked_source(text)
                urls = list(state['urls'])
                if action == 'replace':
                    old = payload['url']
                    if old not in urls:
                        raise ValueError('Категория уже изменена. Отмените ввод и откройте список заново.')
                    if url in urls and url != old:
                        raise ValueError('Такая категория уже есть.')
                    urls[urls.index(old)] = url
                else:
                    if url in urls:
                        raise ValueError('Эта категория уже добавлена.')
                    if len(urls) >= 5:
                        raise ValueError('Максимум 5 категорий. Сначала удалите одну.')
                    urls.append(url)
                service.save(chat.id, urls=urls)
                screen = 'sources'
            elif action in {'filter', 'range'}:
                if action == 'range':
                    metric = payload['metric']
                    rules = metric_input(state['rules'], metric, text)
                    notice = f'✅ {FILTER_LABELS[metric]}: {ui_range(rules, metric)}. Фильтр сохранён.'
                else:
                    field = payload['field']
                    metric, _, bound = field.rpartition('_')
                    range_text = re.fullmatch('(?:от\\s*)?\\d+(?:[.,]\\d+)?\\s*(?:-|–|—|\\.\\.|до)\\s*\\d+(?:[.,]\\d+)?', text, re.I)
                    if metric in FILTER_LABELS and bound in {'min', 'max'} and range_text:
                        rules = metric_input(state['rules'], metric, text)
                        notice = f'✅ {FILTER_LABELS[metric]}: {ui_range(rules, metric)}. Фильтр сохранён.'
                    else:
                        rules = update_filters(state['rules'], field + '=' + shlex.quote(text))
                        label = TEXT_LABELS.get(field, FILTER_LABELS.get(metric, field))
                        display = ui_range(rules, metric) if metric in FILTER_LABELS else str(rules.get(field) or 'не задано')
                        notice = f'✅ {label}: {display}. Фильтр сохранён.'
                service.save(chat.id, rules=rules)
                screen = 'filters'
            elif action == 'save':
                save_search(service, chat.id, text)
                screen, notice = ('saved', '💾 Поиск сохранён.')
            elif action == 'admin_target':
                if user.id != ADMIN_ID:
                    raise ValueError('Доступ закрыт.')
                target = admin_target(text)
                context.user_data.pop('panel_form', None)
                await admin_confirmation(update, context, payload['kind'], target)
                return
            elif action == 'interval':
                minutes = int(text)
                if not 5 <= minutes <= 1440:
                    raise ValueError('Введите число от 5 до 1440.')
                service.save(chat.id, minutes=minutes, next_check=time.time() + minutes * 60)
                screen = 'monitor'
            context.user_data.pop('panel_form', None)
            await panel(update, context, screen, notice)
        except ValueError as exc:
            await message.reply_text(str(exc)[:800] + '\nПопробуйте ещё раз или /cancel.')
        return
    if text.startswith(('http://', 'https://')):
        try:
            url = checked_source(text)
            urls = service.state(chat.id)['urls']
            if url in urls:
                await panel(update, context, 'sources', 'Эта категория уже есть.')
                return
            if len(urls) >= 5:
                raise ValueError('Максимум 5 категорий. Удалите одну или замените её.')
            service.save(chat.id, urls=urls + [url])
            await panel(update, context, 'sources', '✅ Категория добавлена. Для запуска нажмите «Начать поиск».')
        except ValueError as exc:
            await message.reply_text(str(exc))
        return
    await panel(update, context)

async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query, user, chat = (update.callback_query, update.effective_user, update.effective_chat)
    service = context.application.bot_data['service']
    if query and (query.data or '').startswith(('talk:', 'bill:')):
        await query.answer('Эта функция удалена. Откройте /start.', show_alert=True)
        return
    if not query or not user or (not chat) or (chat.type != 'private') or (not service.permitted(user.id)):
        if query:
            await query.answer('Доступ закрыт.', show_alert=True)
        return
    await query.answer()
    context.user_data.pop('panel_form', None)
    data, state = (query.data or '', service.state(chat.id))
    try:
        if data == 'ui:proxies':
            if user.id != ADMIN_ID:
                await query.message.reply_text('Управление прокси доступно только владельцу.')
                return
            reader = service.reader
            lines = ['🌐 Прокси', '']
            for index, uri in enumerate(reader.proxy_pool):
                active = ' · активен' if index == reader.proxy_index else ''
                lines.append(f'{index + 1}. {proxy_label(uri)}{active}')
            lines.append('\n/newproxy — заменить основной\n/addproxy — добавить резервный\n/nextproxy — переключиться\n/delproxy НОМЕР — удалить резервный')
            await query.message.reply_text('\n'.join(lines))
            return
        navigation = {'menu_home': 'home', 'menu_sources': 'sources', 'menu_filters': 'filters', 'menu_status': 'status', 'ui:saved': 'saved', 'ui:monitor': 'monitor', 'ui:cancel': 'home'}
        if data == 'ui:testsource':
            await test_source_message(update, context)
            return
        if data.startswith('ui:admin'):
            if user.id != ADMIN_ID:
                raise ValueError('Админ-панель доступна только владельцу.')
            await admin_callback(update, context, data)
        elif data in navigation:
            await panel(update, context, navigation[data])
        elif data in {'menu_check', 'restart_scan', 'ui:watch'}:
            if not active_sources(state):
                await country_panel(update, context, 'Добавьте или включите страну для поиска.')
                return
            if data == 'restart_scan':
                await service.cancel_scan(chat.id)
            if data == 'ui:watch':
                service.save(chat.id, enabled=1)
            started = service.trigger(chat.id)
            await panel(update, context, notice='🚀 Поиск запущен.' if started else '⏳ Поиск уже выполняется.')
        elif data == 'menu_stop':
            service.save(chat.id, enabled=0)
            await service.cancel_scan(chat.id)
            await panel(update, context, notice='⏸ Поиск и мониторинг остановлены.')
        elif data == 'menu_help':
            await show_panel(update, help_text(user.id) + '\n/saved — сохранённые поиски\n/cancel — отменить ввод\n\nОтправленная ссылка сохраняется; запуск выполняется кнопкой «Начать поиск».', get_main_menu())
        elif data == 'ui:add':
            await ask_field(update, context, 'add', '🔗 <b>Добавить категорию</b>\nОтправьте ссылку на категорию или выдачу OpenSooq.')
        elif data.startswith(('ui:replace:', 'ui:delete:', 'ui:delete_yes:')):
            key = data.rsplit(':', 1)[1]
            url = next((url for url in state['urls'] if source_key(url) == key), None)
            if url is None:
                raise ValueError('Эта категория уже изменена или удалена.')
            if data.startswith('ui:replace:'):
                await ask_field(update, context, 'replace', '✏️ <b>Заменить категорию</b>\nТекущая ссылка:\n' + ui_url(url) + '\n\nОтправьте новую ссылку.', url=url)
            elif data.startswith('ui:delete_yes:'):
                service.save(chat.id, urls=[item for item in state['urls'] if item != url])
                if len(state['urls']) == 1:
                    service.save(chat.id, enabled=0)
                    await service.cancel_scan(chat.id)
                await panel(update, context, 'sources', '🗑 Категория удалена.')
            else:
                await show_panel(update, '🗑 <b>Удалить эту категорию?</b>\n\n' + ui_url(url), ui_keyboard([[('Да, удалить', 'ui:delete_yes:' + key)], [('Отмена', 'menu_sources')]]))
        elif data == 'ui:countries':
            await country_panel(update, context)
        elif data.startswith('ui:country:'):
            await country_panel(update, context, code=data.rsplit(':', 1)[1])
        elif data.startswith('ui:country_mode:'):
            mode = data.rsplit(':', 1)[1]
            if mode not in {'single', 'all'}:
                raise ValueError('Неизвестный режим поиска.')
            service.save(chat.id, country_mode=mode, selected_country=state.get('selected_country', ''))
            await service.cancel_scan(chat.id)
            if not active_sources(service.state(chat.id)):
                service.save(chat.id, enabled=0)
            elif state['enabled']:
                service.save(chat.id, next_check=time.time())
            await country_panel(update, context, '✅ Режим поиска сохранён.')
        elif data.startswith('ui:country_select:'):
            code = data.rsplit(':', 1)[1]
            if code not in COUNTRY_LABELS:
                raise ValueError('Неизвестная страна.')
            urls = list(state['urls'])
            if not any((country_code(url) == code for url in urls)):
                if len(urls) >= 5:
                    raise ValueError('Максимум 5 категорий. Сначала удалите ненужную категорию.')
                urls.append(f'https://{code}.opensooq.com/en/find?search=true&sort_code=recent')
            service.save(chat.id, urls=urls, country_mode='single', selected_country=code, disabled_countries=[item for item in state.get('disabled_countries', []) if item != code])
            await service.cancel_scan(chat.id)
            if state['enabled']:
                service.save(chat.id, next_check=time.time())
            await panel(update, context, notice='🎯 Выбрана только ' + COUNTRY_LABELS[code] + '. Нажмите «Найти объявления».')
        elif data.startswith('ui:country_toggle:'):
            _, _, code, action = data.split(':')
            if code not in COUNTRY_LABELS or action not in {'on', 'off'}:
                raise ValueError('Неизвестная страна или действие.')
            urls = list(state['urls'])
            disabled = set(state.get('disabled_countries', []))
            if action == 'on':
                if not any((country_code(url) == code for url in urls)):
                    if len(urls) >= 5:
                        raise ValueError('Максимум 5 категорий. Удалите ненужную категорию перед добавлением страны.')
                    urls.append(f'https://{code}.opensooq.com/en/find?search=true&sort_code=recent')
                disabled.discard(code)
            else:
                disabled.add(code)
            selected = state.get('selected_country', '')
            if action == 'on' and state.get('country_mode', 'single') == 'single':
                selected = code
            service.save(chat.id, urls=urls, disabled_countries=sorted(disabled), selected_country=selected)
            await service.cancel_scan(chat.id)
            if not active_sources(service.state(chat.id)):
                service.save(chat.id, enabled=0)
            elif state['enabled']:
                service.save(chat.id, next_check=time.time())
            notice = '✅ Страна включена. Режим поиска указан ниже.' if action == 'on' else '⏸ Страна отключена. Её категории сохранены для повторного включения.'
            await country_panel(update, context, notice, code=code)
        elif data.startswith('ui:country_yes:'):
            code = data.rsplit(':', 1)[1]
            if code not in COUNTRY_LABELS:
                raise ValueError('Неизвестная страна.')
            service.save(chat.id, enabled=0)
            await service.cancel_scan(chat.id)
            service.save(chat.id, urls=[f'https://{code}.opensooq.com/en/find?search=true&sort_code=recent'], disabled_countries=[item for item in state.get('disabled_countries', []) if item != code], country_mode='single', selected_country=code)
            await panel(update, context, 'sources', '✅ Страна изменена. Проверьте фильтры и нажмите «Начать поиск».')
        elif data.startswith('ui:metric:'):
            metric = data.rsplit(':', 1)[1]
            if metric not in FILTER_LABELS:
                raise ValueError('Неизвестный фильтр.')
            context.user_data['panel_form'] = dict(action='range', payload={'metric': metric}, expires=time.time() + 600)
            await show_panel(update, f"⚙️ <b>{FILTER_LABELS[metric]}</b>\n\nСейчас: <b>{escape(ui_range(state['rules'], metric))}</b>\n\nОтправьте диапазон одним сообщением: <code>1-99999</code>.\nОдно число задаёт максимум.\nСнять обе границы: <code>off</code>. Отмена: /cancel.", ui_keyboard([[('Минимум', 'ui:field:' + metric + '_min'), ('Максимум', 'ui:field:' + metric + '_max')], [('Убрать ограничение', 'ui:clear:' + metric)], [('‹ Все фильтры', 'menu_filters')]]))
        elif data.startswith('ui:field:'):
            field = data.rsplit(':', 1)[1]
            metric, _, bound = field.rpartition('_')
            if field in TEXT_LABELS:
                label = TEXT_LABELS[field]
                hint = 'Слова через запятую, например: iphone,samsung.' if field != 'currency' else 'Код из трёх букв, например AED.'
            elif metric in FILTER_LABELS and bound in {'min', 'max'}:
                label = FILTER_LABELS[metric] + (' — минимум' if bound == 'min' else ' — максимум')
                hint = 'Одно число. Для снятия ограничения: off.'
            else:
                raise ValueError('Неизвестное поле.')
            await ask_field(update, context, 'filter', f"⚙️ <b>{label}</b>\n{hint}\nТекущее значение: {escape(str(state['rules'].get(field, 'не задано')))}\nДля удаления значения отправьте off.", field=field)
        elif data.startswith('ui:clear:'):
            metric = data.rsplit(':', 1)[1]
            if metric not in FILTER_LABELS:
                raise ValueError('Неизвестный фильтр.')
            rules = dict(state['rules'])
            rules.pop(metric + '_min', None)
            rules.pop(metric + '_max', None)
            service.save(chat.id, rules=rules)
            await panel(update, context, 'filters', '✅ Ограничение снято.')
        elif data == 'ui:currency':
            await show_panel(update, '💱 <b>Валюта цены</b>\n\nОбъявления с другой валютой будут исключаться. Пересчёта валют нет.', ui_keyboard([[(code, 'ui:currency_set:' + code) for code in ('KWD', 'AED', 'SAR', 'BHD', 'JOD')], [('Любая валюта', 'ui:currency_set:off'), ('Другая', 'ui:field:currency')], [('‹ Фильтры', 'menu_filters')]]))
        elif data.startswith('ui:currency_set:'):
            rules = update_filters(state['rules'], 'currency=' + data.rsplit(':', 1)[1])
            service.save(chat.id, rules=rules)
            await panel(update, context, 'filters', '✅ Валюта сохранена.')
        elif data == 'ui:unknown':
            await show_panel(update, '❔ <b>Если значение неизвестно</b>\n\nПример: задан минимум просмотров, но профиль недоступен.\n«Исключать» — такое объявление не отправляется.\n«Разрешать» — может отправиться, если остальные фильтры подходят.', ui_keyboard([[('Исключать', 'ui:unknown_set:exclude'), ('Разрешать', 'ui:unknown_set:include')], [('‹ Фильтры', 'menu_filters')]]))
        elif data.startswith('ui:unknown_set:'):
            rules = update_filters(state['rules'], 'unknown=' + data.rsplit(':', 1)[1])
            service.save(chat.id, rules=rules)
            await panel(update, context, 'filters', '✅ Настройка сохранена.')
        elif data == 'ui:reset':
            await show_panel(update, '↺ <b>Сбросить все пользовательские фильтры?</b>\nКатегории и сохранённые поиски останутся.', ui_keyboard([[('Сбросить', 'ui:reset_yes'), ('Отмена', 'menu_filters')]]))
        elif data == 'ui:reset_yes':
            service.save(chat.id, rules={})
            await panel(update, context, 'filters', '✅ Фильтры сброшены.')
        elif data == 'ui:save':
            if not state['urls']:
                raise ValueError('Сначала добавьте категорию.')
            await ask_field(update, context, 'save', '💾 <b>Сохранить текущий поиск</b>\nВведите название, например: ОАЭ · телефоны.\nСохранятся категории, включённые страны, фильтры и интервал.')
        elif data.startswith(('ui:search:', 'ui:load:', 'ui:load_yes:', 'ui:drop:', 'ui:drop_yes:')):
            search_id = int(data.rsplit(':', 1)[1])
            row = saved_row(service, chat.id, search_id)
            if data.startswith('ui:load_yes:'):
                name = await load_search(service, chat.id, search_id)
                await panel(update, context, notice=f'✅ Загружен поиск «{name}». Для запуска нажмите «Начать поиск».')
            elif data.startswith('ui:drop_yes:'):
                with service.db:
                    service.db.execute('DELETE FROM saved_searches WHERE chat=? AND id=?', (chat.id, search_id))
                await panel(update, context, 'saved', '🗑 Сохранённый поиск удалён. Текущие настройки не менялись.')
            elif data.startswith('ui:load:'):
                await show_panel(update, '💾 <b>Загрузить поиск «' + escape(row['name']) + '»?</b>\n\nТекущие категории и фильтры будут заменены. Мониторинг остановится. История отправок сохранится.', ui_keyboard([[('Загрузить', f'ui:load_yes:{search_id}'), ('Отмена', 'ui:saved')]]))
            elif data.startswith('ui:drop:'):
                await show_panel(update, '🗑 Удалить сохранённый поиск «' + escape(row['name']) + '»?', ui_keyboard([[('Удалить', f'ui:drop_yes:{search_id}'), ('Отмена', 'ui:saved')]]))
            else:
                config = json.loads(row['config'])
                detail = '💾 <b>' + escape(row['name']) + '</b>\n\n'
                detail += '\n'.join((ui_url(url) for url in config['urls']))
                detail += f"\n\nИнтервал: {config['minutes']} мин.\n\n" + filters_text(config)
                await show_panel(update, detail, ui_keyboard([[('📂 Загрузить', f'ui:load:{search_id}'), ('🗑 Удалить', f'ui:drop:{search_id}')], [('‹ Мои поиски', 'ui:saved')]]))
        elif data == 'ui:custom_interval':
            await ask_field(update, context, 'interval', '⏱ <b>Интервал мониторинга</b>\nВведите количество минут: от 5 до 1440.')
        elif data.startswith('ui:interval:'):
            minutes = int(data.rsplit(':', 1)[1])
            if not 5 <= minutes <= 1440:
                raise ValueError('Интервал: 5–1440 минут.')
            service.save(chat.id, minutes=minutes, next_check=time.time() + minutes * 60)
            await panel(update, context, 'monitor', '✅ Интервал сохранён.')
        else:
            await panel(update, context)
    except ValueError as exc:
        await query.message.reply_text(str(exc)[:800], reply_markup=get_main_menu())

class HealthServer:

    def __init__(self):
        self.runner = None

    async def start(self, port):
        from aiohttp import web

        async def health(request):
            return web.json_response({'status': 'ok', 'version': 'parser-v39'})
        app = web.Application()
        app.router.add_get('/healthz', health)
        app.router.add_get('/', health)
        self.runner = web.AppRunner(app)
        await self.runner.setup()
        await web.TCPSite(self.runner, '0.0.0.0', port).start()

    async def close(self):
        if self.runner is not None:
            await self.runner.cleanup()
            self.runner = None

def build_app(token, allowed, database):

    async def setup(app):
        service = Service(app.bot, allowed, database)
        app.bot_data['service'] = service
        log.info('[startup] parser-v39 database=%s data_dir=%s transport=Chrome', Path(database).resolve(), DATA_DIR.resolve())
        if os.getenv('PORT'):
            server = HealthServer()
            await server.start(int(os.environ['PORT']))
            app.bot_data['health_server'] = server
        if app.job_queue is None:
            raise RuntimeError('Установите python-telegram-bot[job-queue].')
        app.job_queue.run_repeating(service.tick, interval=15, first=5)
        commands = [BotCommand('start', 'Меню'), BotCommand('check', 'Найти объявления'), BotCommand('pause', 'Остановить поиск'), BotCommand('status', 'Результаты'), BotCommand('testsource', 'Проверить выдачу'), BotCommand('saved', 'Мои поиски'), BotCommand('version', 'Версия парсера'), BotCommand('help', 'Справка'), BotCommand('id', 'Мой ID')]
        try:
            await app.bot.set_my_commands(commands)
            await app.bot.set_my_commands(commands + [BotCommand('proxies', 'Прокси'), BotCommand('newproxy', 'Сменить основной прокси'), BotCommand('addproxy', 'Добавить резервный'), BotCommand('nextproxy', 'Переключить прокси'), BotCommand('users', 'Пользователи')], scope=BotCommandScopeChat(chat_id=ADMIN_ID))
        except TelegramError as exc:
            log.warning('[startup_commands] %s', error_text(exc))

    async def cleanup(app):
        server = app.bot_data.pop('health_server', None)
        if server:
            await server.close()
        service = app.bot_data.pop('service', None)
        if service:
            await service.close()

    async def on_error(update, context):
        error = context.error
        log.error('Ошибка обработчика: %s', type(error).__name__, exc_info=(type(error), error, error.__traceback__))
    app = Application.builder().token(token).concurrent_updates(False).post_init(setup).post_stop(cleanup).post_shutdown(cleanup).build()
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.TEXT, handle))
    app.add_handler(CallbackQueryHandler(button_handler))
    app.add_error_handler(on_error)
    return app

class StartupCheckError(Exception):

    def __init__(self, code, message):
        self.code = code
        super().__init__(message)

def check_startup(network=True, client=None):
    token = os.getenv('BOT_TOKEN', '').strip()
    if not re.fullmatch('[0-9]+:[A-Za-z0-9_-]+', token):
        raise StartupCheckError(11, 'BOT_TOKEN_FORMAT: нужен токен Telegram от BotFather.')
    if ADMIN_ID <= 0 or (SUBSCRIPTIONS_ENABLED and (not os.getenv('ADMIN_ID', '').strip())):
        raise StartupCheckError(12, 'ADMIN_ID: укажите положительный числовой Telegram ID владельца.')
    try:
        {int(v.strip()) for v in os.getenv('ALLOWED_TELEGRAM_IDS', '').split(',') if v.strip()}
        saved_proxy = load_proxy_config()
        if saved_proxy is None:
            proxy_settings(os.getenv('OPENSOOQ_PROXY_URL', ''))
        if os.getenv('PORT') and (not 0 <= int(os.environ['PORT']) <= 65535):
            raise ValueError()
    except ValueError:
        raise StartupCheckError(13, 'CONFIG: проверьте формат ALLOWED_TELEGRAM_IDS, PORT и OPENSOOQ_PROXY_URL.') from None
    print('[startup_check] CONFIG_OK', flush=True)
    if not network:
        return
    owned = client is None
    if owned:
        client = httpx.Client(timeout=httpx.Timeout(15, connect=10), trust_env=False, follow_redirects=False)
    try:
        try:
            response = client.get('https://api.telegram.org/bot' + token + '/getMe')
        except httpx.RequestError:
            raise StartupCheckError(22, 'TELEGRAM_NETWORK: нет соединения с api.telegram.org.') from None
        if response.status_code in {401, 404}:
            raise StartupCheckError(21, 'TELEGRAM_AUTH: Telegram отверг BOT_TOKEN.')
        if response.status_code != 200:
            raise StartupCheckError(23, f'TELEGRAM_HTTP: HTTP {response.status_code} при getMe.')
        try:
            if response.json().get('ok') is not True:
                raise ValueError()
        except (ValueError, AttributeError):
            raise StartupCheckError(23, 'TELEGRAM_RESPONSE: некорректный ответ getMe.') from None
        print('[startup_check] TELEGRAM_OK', flush=True)
        print('[startup_check] CHECK_COMPLETE', flush=True)
    finally:
        if owned:
            client.close()

class SecretFormatter(logging.Formatter):

    def format(self, record):
        return error_text(super().format(record))

def main():
    handler = logging.StreamHandler()
    handler.setFormatter(SecretFormatter('%(asctime)s %(levelname)s %(message)s'))
    logging.basicConfig(level=logging.INFO, handlers=[handler], force=True)
    logging.getLogger('httpx').setLevel(logging.WARNING)
    logging.getLogger('httpcore').setLevel(logging.WARNING)
    if '--check-desktop' in sys.argv:
        return asyncio.run(check_desktop())
    if '--check-startup' in sys.argv:
        try:
            check_startup()
            return 0
        except StartupCheckError as exc:
            print(f'[startup_check_failed] EXIT={exc.code} {error_text(exc)}', flush=True)
            return exc.code
    token = os.getenv('BOT_TOKEN', '').strip()
    if not token:
        raise SystemExit('Задайте BOT_TOKEN в Environment на Render.')
    allowed = {ADMIN_ID} | {int(v.strip()) for v in os.getenv('ALLOWED_TELEGRAM_IDS', '').split(',') if v.strip()}
    log.info('[boot_v39_1_menu_banner] Создание Telegram Application')
    app = build_app(token, allowed, DATABASE)
    try:
        app.run_polling(allowed_updates=['message', 'callback_query'], bootstrap_retries=3)
    except Exception:
        log.exception('[startup_failed] Бот остановился при запуске')
        return 1
    return 0


# Встроенный баннер меню. Служебные данные изображения.
HOME_BANNER_BASE64 = (
    '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'
    'g8hhGfzlVfbsk4lxtuXjm0hbNOuZ7N3n6Lt3T9ht+gdGW+w2tsN2+1xERY6cdEjG8fEnJPiagF/LtymMRI+S4VAADqo8BVm3'
    'sp9XCRyKsVQW2baI3sf0HcdSI3VagnrVAsrKushQOXSPqtpyr5d9X6uXnGnC2Vyx6ZG1ROodXwtB2ZfrGntHYRISlXsyZx4L'
    'PjucUjxKq5ylwI7kRNzh8GVHDqPqnv8ADxrBa5TjzlxcfcU8848lS3FnKlklRJPiTk05KYdtkpyK8gpjz0bhB5BZHsn9xrPU'
    'qEVMt3mujb27XUJdnPkZIB+60dDBLup2ioAhIWoVekW3u3Be4w2Vr5hIHGqV2aRt/U60LHFDK/sIrqXQMBtsuSVYyOArlbVq'
    '4Kkjgu7yepYrfPiVUOsGbtb4bjbEGSrKTv7nsYHXJPEDypv2VaN0/qq5y4+u5V0hNerrTAEeOpcVpakkIUst5UkBWDgDjjia'
    '6ofsx1FFdhqjl5l4bpB/jUeh7DNSWV5T1pXGeZJyGn1hKh8ayWu1BTaRAlbL7ZLKzwXvIHcuaLNsv1HlqG3ZWZKYU4PuSF29'
    'x4PbpxuBaR7bKgAccOfSrUt2wvT6dms+fd2bnbtbypz0iK1CjHs4zGcIacQpW6QcFWAokAgZPGrgj6G2glY3IdtjqAx2q3kk'
    'geHAmnaJsZvN0VvXy/Eo6txUYH7R4n4AVY7a9Q6wsjdi2bIOI5Lj236OvbLMhDtnmQ5TAC1sOMkNupJxvtK5cyMpz4irt2CI'
    'ctmpXrXMSC0d1eByCuo/57qvO6aKtGmbIuOz20iQ8jcbVIcJDY+sE8hUG07ZY9qvsVxpOMKSnPU8ckn51hr3nPNc0hdSztW0'
    '2hzXErpqKE+o7qB0zwrkX0htM3fUl6dft7LjzMLdbDKBnKlE5IHwArrWI4G4Ge4VW5/9pyXt38oQcnvBNZhV5oteNVmsqWM1'
    'AdFxHqPZbqGzPwmZVrlOSXAlS3uwK40Le44J5OO444HBPLiadtebGLIxZtJT9I/hu93gdom8tSIKypbuQptYQPZ7LmggKzyP'
    'WuyNQ6AtuvYaC89KjPIGN1lzCQe8JORVfHYFqW0uLcsd/iSE9GpjZaV8xkV1Lbarg3QSstfZ1vVMVHkdXv7rlLT2xvUE+5Rb'
    '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'
    '2WyuDzl2R/4sAq+4mlSPSB2GXdOZr8J3e5iTZVL+eWzXll/LN4/9VR+2aV/LV8f9VT/lD/CnNzwHvvUOa5Pn8bx4/wDUr01k'
    '659G27pUhyPpDB/prFuH5hsGo5Lsno33BSlRxodpZHNMuTFP+iRivO4a2dH/AFUf5Q/wrInXBx7UNRPeHf8AhSmvw9+KBR2H'
    'PRrO7wT6NC70lbF9h+pMNoXZJaEneShjWDqSk+AcURWRGwbR1tcL9pe1PFOOC7fqWK/w8O0Qa4HOtWle9CV/lB/Csjet0NnK'
    'I76P0XcUwa3A+Sg6hsrVlZve1/0IXaF82QQnipKNSa8abPMO2yFM+1Ckk1Bn9jVrtlzenI1xPbkOAJP4W0s8gADkB2bhxXOs'
    'faU9HOW3J6D4OinmPtxvMdO63dLqkDp2mR99PFWH9v1URQ2adXNPY5w9WuXQkGA7Z21txtcaJkb5BIksz4qvLi2oCkT37urH'
    'Zz9HSh/931AEZ+DraaotO3q4rGJK0Sh/95iNrPz50Tm2SDJH98WeEo96G1Nn/RNGOr7BQLfZv5j3PYfVoVyfhC8sJUpyzJeA'
    '+lBukOQD5AOA/ZS7Xr5dpnoel2i+MNYKVn1EucD+gVVRzm0bT8kHfta2z3tvq/eDWunV9hUrKHJjHksH9wpY6uhA8Cpi12cd'
    'KjvFh+q6utm23TUJ1Lj1xkRknAWJMN5rh8UdKq70kn9G7RbO1qOyX+0v6gtiNx1pEhIclR+7BwSpBOR4EjuqsE63hBIS1f56'
    'B3FR/cqkL1U2/nGoAsdzyd7/AFgaTaj26j34Jv2XaVB0ax/pH/ZbGyDW/q7DlhlvDDYLkValch9JH7x8atUXrfHsne8jmqhT'
    'cmXfek2eR4ORmv6tGl6Bk71ptDmerSC2fmhQpOqycwpU9j9HCyrPaCPSVbyb0UnmRWpfn2L1aJMN/CkOJIx8KrVl+Gk5TBmN'
    'f/hri8nHwUVCnRqXEWnBuF8jnuWhiQPtSg/bURWaNVN2wro/LDuwkf8AsApFs21Y6uwqtMt0ql2lfqxJPvIHuH9nh8Klc6cL'
    'hCkRXDlt9tTavIgiqutlmjW66SLhB1CntJKAhxqZbVpQccjltasGpZGbui0ksyLBL/NauCmV/svISPtq0XNI71l/YW0Kbc6J'
    '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'
    'dlOrVTevHRZp1u//AM69sJjveoza+zUfxjzpKlbwyT400fy6Vj8in/J/8aj95m/hC4Ou/QB3UjwrQxUqdqzCMQzWa+5TXnxD'
    'xbvhk5ffvUt/ly4OTSP8n/xpY14sfzSf2P8AjUP3aLd51P4alwWMcpdpD/EU3ia2XKlNNLQkIUoBXsY4deOalDqy24tOeRxV'
    'QNrLTiVjmkg1aYc9YiRJCTkONAE+KeH3YrJc0WsILV6rk5tevetqNuHS5sHu09VsiRjrWeHcnYUpiSyrDzDiXEHxByPupvAJ'
    'zR4KRWeAvRY3Jg2mW5qLql6VHGIlxQmW1jkN7iR8Kh2e6rD1c2bjphh/GXba72ZP+LVxHyOarzGa6Vq7FTAO7JfN+UlqKF+9'
    'zdH9Id+v/KUWedOGn2u2vUNHPK6b8YzT/oZrt9U29OM/jB94q2qYpuPUubsunzl7RZxc31Vk6kk9pf7gRyDu4PJIA/dTYHDW'
    'xOSX5sl3nvuqV81GsAZV3Vx2xC+vva4vJ60baipaU/WUB9tQLWbvbalnnuWR99WLEjlUlr9MH7aq++udteJq+9w1ps86h7F5'
    'fldiZYsad7vQH7ptAoYpQFDFdOV84hIxVsWb8Ro+3tjmt9az8EJH8aqnHSrjgxMaftCAP5tavmrH+zWG+dDWhe05E0C+vWcN'
    'zR6haoJoZPjW8mGe6lCH3iufjC+iC0eVG9aq3dKw09XJKz8gkfuquasfaMnsLVaGfrFa8eaj/Cq5rp2X8Kesr5fywy2mWcGt'
    'HlP1RVMtlre/rO3q6NrCvkQf3VDanOylONS9p9RpavklRqy5MUnLn8nafObToN/zBSlTinXHFnmtRV8zmiycVtoindHDpRiI'
    'e6uNiC+y/CvWsyvcWFHpk/YaqCYrflvq71n76uh2L2cd5Z4bqFH7DVKOHLiz3qJ+2t9gZLivCcuWOpsoMO8uPokYoJJQoEcC'
    'DkGlCiror55posrkhyTgOKyE5IGMUTLC33UNNIUtxZCUpSMlRPQVlt9vlXKUiLDYcffcOEobGSatrT2lmtHs+sP7j9+UMDHF'
    'EQeHev7qz1q7aLevgu/sbYdzterOYYPmcfQcTwHjATc1b4+jdNzYzrUd+5yWwZanG0rDIHFLScjgepI8BVYA54/dU81q4Y1u'
    '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'
    '5yyv9io8z/nK1NuWtE/Dt/pXXI2o3l0Hc1U+sHulpV++i/l/qJz3b7MV4hwH91cdqRukgpx8MUEOrbOULUk/mqIpfCu3PUm7'
    'Yt2fNbN8v+q69d1vqI5zeJp/WH8K0nNc6hAIN4l48x/CuVk3Oc37k2SnyeUP31mTqO7t+7c5f+VJqPwdT8y0M5Q2Lfmth4N+'
    'wXSj+uL8rIN3lY/SH8KjN41fdJjaoy7g842r3wccfDgKpVOrL4n/AOkn1DuVg/urejaxmI4PttvDvA3TS+EqDfK3UuUWzXZC'
    'ng68I+klS+42i2agARdIyXDyD4GFp+I41Er1sVuKUGRYX03Bk8QyohLvwPJX2GnOPquK9+UQ40fHiKfbTrBNsc7SLJSUnipt'
    'YylXmKbKlejp4Kq/2dsjbDS58YvzDJ3fx7wVRM62TLXKciTor0aU37zTyChafga1wiu0LPqLSG0aO1adRW+FLVjdQxLO6tP/'
    'AILwwpJ8M/A0x6u9DpU9tydoK6l08/wXdiEODwS8Bg/rAeddGjeNfk7Ir5ntPk9WsHSOk3iFyals9KBQRmphqLZ9qHRlxVb9'
    'Q2iZbJYPBElspC/FKuSh4gmi07oO+ayuaLZYLVMuc9fJmK0VkeJxwSPEkCtHOCVzxZOLMe5Q3dNZ4dvk3GS3Ghx3ZElzghpp'
    'BUpXkBxrqvSvoYXCGhE3Xl0bgMj2jb7esOvnwU57if1d41ILvftE7OIjlo07AjReGFojnffdPe68cn4Z+AqireNZkMyt2y+T'
    '9W/dJOFm8rnqybGLm8kP3p5NvZ5llOFO/Hon7T4VMbdZLXp4FFtYSlXIvq9paviaF41qm4LKnn0obHutNj2R/H41HntYMN5D'
    'bTjh8eArnvfXra6cF9KsLHY2xwCyMX5jme7h3AK1bDrW9WxhMSNc5DLCSShCSMJzz5in9OvtR/8A67ljyUkfurnt3Wk4/kUM'
    'tfDeNa69aXw8PX1J/RQkfuqAtKp0MLVU5RbLBOKliPHCPrBXSje0HUo5X6dn9MfwrMNoep//ANfXD4Of8K5bc1Venc5ucn4L'
    'x91ajl2nv/lJ0pfm6r+NSFnU3uWJ/KTZ34Lae0NH3XWB2lanbHHUdwT5v4rEdrmoWM72rpqPOYB++uSy4tZ9palfpKJo0tBX'
    'JOT4DNSFo4avKzO5Q2zvltG+X/VdYK25Xpke1riUP/fawj0g7o2fa13N+EomuXm4TyvdYX57lZDDdQMr3Gx+etKfvNSFv/nK'
    'g7azCJFowf7f0XTq/SUuDQP/AMtrmr9Faz+6tVXpQXJPLVV7X5FVc1YjI/LXCGjw7YH7qUmRZW/yl3Y8koWr91TFrO8rBU21'
    'SbrSpD/aPuujV+lNeU53NQX5X6+PvNa6vSq1GM9nd78o+L4Fc/JvOmmect9z9Fg/vIpX8rtOM+7HnunwQlP3k1Y2z6z4lc+r'
    'yjoN0ZT7mt/VX0fSr1h/N3O8n9KUP4VhX6VGv3chu5XEeJkn+FUYNoNnZB7KyPrPe4+kfcKwnafuZ7Cyxkd286o/cBVzbMby'
    'fE/dc2rynb+FjP6Gf9VeZ9I/ai+PxV5uI8nlH91IO2/azLzi/wBwTnvfUP31RK9q134hqJAQPFtSvvVWq5tQ1ErO4/Hb/Qjp'
    '/fVgtGjVYX8pqx+VrR/tb9lfatoe1qZne1XJQD9aSr/jSm7xtMm8Hdavpz0Clrrnh3aNqd3h+FnkDubCU/cK0ndYX9/O/erg'
    'Qe59Q+41MWtPeFldyhvDo+OwALptFs14/wC09rmWAfqsn95rbbst3A/v/aFNbHXJZR/rGuS3rtPkZ7abJc/TeUfvNahySSTk'
    '+PGn8NS/KFSdu35/xneJXY3qOnGATcdpUrA5/wDSUdH+qkmtiPeNkcIZn64mScdPwo8vPwbRXGPy+VDj3mmKFMfhHgqztm/P'
    '+M7+o/dduo2h+j1FwJM+4SSP6MzV/vFF/bm9G2IrKrDfpmOiWneP7T4riP40KfMU/wAo8FA7VvjrWd/Ufuu3HvSJ9HBhGGNm'
    'l8kK/PIR9peNMc70k9ieD6nsZkud3bXPc+4muP6UKfNM4BQ/aV4f8Z/9R+66RufpH6DdChb9jVua7lPXd5X2AVD7htzgyCTF'
    '2f6ej5+s9JXj/wCIKp7nRijm2cAj9oXZ/wAV39R+6sCRtbnvFXZ2KwsA/UYcOP2nDTY9tEvDxOG4Lf6EcD99RICjFGBvBL42'
    '5OtV3ifun5zWd5cz/fSU/oNJFYDqi8K53F8fonFNWKAFPC3gl8RXOrz4lOCr9dF+9cZZ/wDNNa658t335Uhf6Tqj++sAFGE+'
    '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'
    'SSRik9aFChCMUAeNChTQv//Z'
)

if __name__ == '__main__':
    raise SystemExit(main())
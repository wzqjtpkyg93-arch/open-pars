from __future__ import annotations
import asyncio
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
from telegram import BotCommand, BotCommandScopeChat, InlineKeyboardButton, InlineKeyboardMarkup, Update
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
HELP_TEXT = 'ℹ️ Публичный парсер v39\n/start — меню\n/check — поиск\n/pause — остановить\n/testsource — проверить выдачу\n/version — версия\n/saved — сохранённые поиски\n/id — мой ID\nФильтры и страны настраиваются кнопками меню.'

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
    rows = [[('🔎 Найти объявления', 'menu_check')], [('🌍 Страны', 'ui:countries'), ('📂 Категории', 'menu_sources')], [('⚙️ Фильтры поиска', 'menu_filters'), ('💾 Мои поиски', 'ui:saved')], [('⏱ Мониторинг', 'ui:monitor'), ('📊 Результаты', 'menu_status')], [('⏸ Остановить поиск', 'menu_stop'), ('❔ Помощь', 'menu_help')]]
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

async def show_panel(update, text, keyboard):
    options = dict(parse_mode='HTML', reply_markup=keyboard, disable_web_page_preview=True)
    query = update.callback_query
    if query and query.message:
        try:
            await query.message.edit_text(text, **options)
            return
        except BadRequest as exc:
            if 'message is not modified' in str(exc).lower():
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
        text = '<b>ParsSTAFF v39 · Публичный парсер</b>\n' + 'Поиск свежих объявлений без входа в аккаунт\n\n' + ('🌐 Все включённые страны\n' if state.get('country_mode') == 'all' else '🎯 Поиск по одной стране\n') + f"🌍 <b>{escape(countries)}</b>\nАктивных категорий: {len(active_sources(state))} из {len(state['urls'])} · Сохранённых поисков: {len(saved_rows(service, chat))}\n\n<b>Поиск</b> · {search_status}\n<b>Мониторинг</b> · {watch_status} · {state['minutes']} мин.\n\n" + 'Настройте фильтры и начните поиск.'
        keyboard = get_main_menu()
    if screen == 'home' and update.effective_user.id == ADMIN_ID:
        rows = list(keyboard.inline_keyboard)
        rows.append([InlineKeyboardButton('🌐 Прокси', callback_data='ui:proxies'), InlineKeyboardButton('👑 Пользователи', callback_data='ui:admin')])
        keyboard = InlineKeyboardMarkup(rows)
    if notice:
        text = escape(notice) + '\n\n' + text
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
        await message.reply_text('ParsSTAFF v39 · публичный парсер · отдельный профиль Chrome · вход в OpenSooq не используется.')
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
    log.info('[boot_v39_parser_only] Создание Telegram Application')
    app = build_app(token, allowed, DATABASE)
    try:
        app.run_polling(allowed_updates=['message', 'callback_query'], bootstrap_retries=3)
    except Exception:
        log.exception('[startup_failed] Бот остановился при запуске')
        return 1
    return 0
if __name__ == '__main__':
    raise SystemExit(main())
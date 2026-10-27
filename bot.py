import os
import re
import asyncio
from telegram import Update
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes
from playwright.async_api import async_playwright
import requests
from bs4 import BeautifulSoup

# --- НАСТРОЙКИ ---
TOKEN = os.environ.get("TOKEN")
ADMIN_ID = 1110325917
# Пароль для доступа (можешь поменять)
PASSWORD = "МойСекретныйПароль123"
# Список авторизованных пользователей
AUTHORIZED_USERS = set()

# --- ФУНКЦИЯ ПАРСИНГА ЧЕРЕЗ PLAYWRIGHT ---
async def get_views_from_profile(profile_url):
    if not profile_url:
        return "Ссылка на профиль не найдена."
    
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        page = await browser.new_page()
        try:
            # Заходим на страницу профиля
            await page.goto(profile_url, timeout=30000)
            # Ждем 3 секунды, пока JS подгрузит цифры
            await page.wait_for_timeout(3000) 
            
            content = await page.content()
            soup = BeautifulSoup(content, "html.parser")
            text = soup.get_text(" ", strip=True)
            
            # Ищем просмотры (поддерживает форматы 55.6K, 1.2M, 720 и т.д.)
            match = re.search(r"([\d.,٬٫]+\s*[kKmM]?)\s*(?:Views|مشاهدة|مشاهدات)", text, re.I)
            if match:
                return match.group(1).strip()
            
            # Если не нашли в тексте, ищем в скрытом JSON
            if '"views_count"' in content:
                json_match = re.search(r'"views_count"\s*:\s*(\d+)', content)
                if json_match:
                    return json_str_format(json_match.group(1))
                    
            return "Просмотры не найдены на странице."
            
        except Exception as e:
            return f"Ошибка при загрузке профиля: {e}"
        finally:
            await browser.close()

def json_str_format(num_str):
    num = int(num_str)
    if num >= 1000000:
        return f"{num/1000000:.1f}M"
    elif num >= 1000:
        return f"{num/1000:.1f}K"
    return str(num)

# --- ФУНКЦИЯ ПОИСКА ССЫЛКИ НА ПРОФИЛЬ В ОБЪЯВЛЕНИИ ---
def find_profile_url(listing_url):
    try:
        headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/120.0.0.0"}
        r = requests.get(listing_url, headers=headers, timeout=15)
        soup = BeautifulSoup(r.text, "html.parser")
        
        # Ищем ссылку на профиль в HTML
        for a in soup.find_all('a', href=True):
            if '/profile/' in a['href'] or '/member/' in a['href']:
                url = a['href']
                if not url.startswith('http'):
                    # Добавляем домен, если ссылка относительная
                    base_domain = re.match(r'(https?://[^/]+)', listing_url)
                    if base_domain:
                        url = base_domain.group(1) + url
                return url
        return None
    except Exception as e:
        return None

# --- ЛОГИКА БОТА ---
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id in AUTHORIZED_USERS:
        await update.message.reply_text("✅ Ты уже авторизован! Отправь ссылку на объявление OpenSooq.")
    else:
        await update.message.reply_text("🔒 Введи пароль для доступа к парсеру:")

async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    
    # Проверка пароля
    if user_id not in AUTHORIZED_USERS:
        if text == PASSWORD:
            AUTHORIZED_USERS.add(user_id)
            await update.message.reply_text("✅ Пароль верный! Теперь отправь ссылку на объявление OpenSooq.")
            try:
                await context.bot.send_message(chat_id=ADMIN_ID, text=f"🚨 Новый юзер авторизовался: {user_id}")
            except: pass
        else:
            await update.message.reply_text("❌ Неверный пароль.")
        return

    # Проверка, что это ссылка
    if "opensooq.com" not in text and "opn.so" not in text:
        await update.message.reply_text("⚠️ Пожалуйста, отправь ссылку на объявление OpenSooq (начинается с https://).")
        return

    msg = await update.message.reply_text("🔎 Ищу профиль продавца...")
    
    # Ищем ссылку на профиль
    profile_url = await asyncio.to_thread(find_profile_url, text)
    
    if not profile_url:
        await msg.edit_text("❌ Не удалось найти ссылку на профиль продавца в этом объявлении.")
        return
        
    await msg.edit_text("⏳ Загружаю страницу профиля (это займет пару секунд)...")
    
    # Парсим просмотры через Playwright
    views = await get_views_from_profile(profile_url)
    
    # Отправляем результат
    await msg.edit_text(
        f"👤 **Профиль продавца:**\n{profile_url}\n\n"
        f"👁 **Просмотры профиля:** {views}",
        parse_mode="Markdown",
        disable_web_page_preview=True
    )

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "🤖 Я бот-парсер просмотров OpenSooq.\n\n"
        "1. Введи пароль (если еще не авторизован).\n"
        "2. Отправь ссылку на любое объявление OpenSooq.\n"
        "3. Я найду профиль продавца и покажу, сколько у него просмотров."
    )

def main():
    if not TOKEN:
        print("ОШИБКА: Не задан TOKEN в переменных окружения!")
        return
        
    app = Application.builder().token(TOKEN).build()
    
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    
    print("✅ ПАРСЕР ЗАПУЩЕН (ожидание сообщений)")
    app.run_polling()

if __name__ == "__main__":
    main()
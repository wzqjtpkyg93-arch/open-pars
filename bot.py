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
PASSWORD = "МойСекретныйПароль123"
AUTHORIZED_USERS = set()

# --- ПАРСИНГ ПРОСМОТРОВ ---
async def get_views_from_profile(profile_url):
    if not profile_url:
        return "Ссылка на профиль не найдена."
    
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
        )
        page = await context.new_page()
        try:
            await page.goto(profile_url, timeout=40000, wait_until="networkidle")
            await page.wait_for_timeout(3000)
            
            content = await page.content()
            soup = BeautifulSoup(content, "html.parser")
            text = soup.get_text(" ", strip=True)
            
            # Поиск в тексте
            match = re.search(r"([\d.,٬٫]+\s*[kKmM]?)\s*(?:Views|مشاهدة|مشاهدات)", text, re.I)
            if match:
                return match.group(1).strip()
            
            # Поиск в JSON
            if '"views_count"' in content:
                json_match = re.search(r'"views_count"\s*:\s*(\d+)', content)
                if json_match: return json_match.group(1)
                
            if '"views"' in content:
                json_match = re.search(r'"views"\s*:\s*"(\d+)"', content)
                if json_match: return json_match.group(1)
                
            await page.screenshot(path="debug_profile.png")
            return "Не найдено (возможно капча)"
            
        except Exception as e:
            return f"Ошибка загрузки: {str(e)[:20]}"
        finally:
            await browser.close()

# --- ПОИСК ССЫЛКИ НА ПРОФИЛЬ В ОБЪЯВЛЕНИИ ---
def find_profile_url(listing_url):
    try:
        headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/120.0.0.0"}
        r = requests.get(listing_url, headers=headers, timeout=15)
        soup = BeautifulSoup(r.text, "html.parser")
        for a in soup.find_all('a', href=True):
            if '/profile/' in a['href'] or '/member/' in a['href']:
                url = a['href']
                if not url.startswith('http'):
                    base = re.match(r'(https?://[^/]+)', listing_url)
                    if base: url = base.group(1) + url
                return url
        return None
    except Exception:
        return None

# --- ЛОГИКА БОТА ---
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id in AUTHORIZED_USERS:
        await update.message.reply_text("✅ Ты уже авторизован! Отправь ссылку на объявление OpenSooq.")
    else:
        await update.message.reply_text("🔒 Введи пароль для доступа:")

async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    
    if user_id not in AUTHORIZED_USERS:
        if text == PASSWORD:
            AUTHORIZED_USERS.add(user_id)
            await update.message.reply_text("✅ Пароль верный! Теперь отправь ссылку на конкретное объявление.")
            try: await context.bot.send_message(chat_id=ADMIN_ID, text=f"🚨 Новый юзер: {user_id}")
            except: pass
        else:
            await update.message.reply_text("❌ Неверный пароль.")
        return

    if "opensooq.com" not in text and "opn.so" not in text:
        await update.message.reply_text("⚠️ Отправь ссылку на конкретное объявление OpenSooq.")
        return

    # Проверка, что это не страница поиска
    if "/find" in text or "/search?" in text:
        await update.message.reply_text("⚠️ Это страница поиска. Открой конкретный товар и скопируй ссылку на него.")
        return

    msg = await update.message.reply_text("🔎 Ищу профиль продавца...")
    profile_url = await asyncio.to_thread(find_profile_url, text)
    
    if not profile_url:
        await msg.edit_text("❌ Не удалось найти ссылку на профиль в объявлении.")
        return
        
    await msg.edit_text("⏳ Загружаю профиль (это займет пару секунд)...")
    views = await get_views_from_profile(profile_url)
    
    await msg.edit_text(
        f"👤 **Профиль:**\n{profile_url}\n\n"
        f"👁 **Просмотры:** {views}",
        parse_mode="Markdown",
        disable_web_page_preview=True
    )

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Отправь ссылку на конкретное объявление OpenSooq, и я покажу просмотры продавца.")

def main():
    if not TOKEN:
        print("ОШИБКА: Не задан TOKEN!")
        return
    app = Application.builder().token(TOKEN).build()
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    print("✅ ПАРСЕР ЗАПУЩЕН")
    app.run_polling()

if __name__ == "__main__":
    main()
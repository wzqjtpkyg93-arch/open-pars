import os
import re
import asyncio
from telegram import Update
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes
from playwright.async_api import async_playwright
import requests
from bs4 import BeautifulSoup

TOKEN = os.environ.get("TOKEN")
ADMIN_ID = 1110325917
PASSWORD = "МойСекретныйПароль123"
AUTHORIZED_USERS = set()

async def get_links_from_category(category_url):
    """Открывает категорию и собирает ссылки на товары"""
    links = []
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
        )
        page = await context.new_page()
        try:
            await page.goto(category_url, timeout=40000, wait_until="domcontentloaded")
            await page.wait_for_timeout(5000) # Ждем загрузки JS
            
            # Прокручиваем страницу, чтобы подгрузились объявления
            for _ in range(3):
                await page.mouse.wheel(0, 1500)
                await page.wait_for_timeout(1000)

            content = await page.content()
            soup = BeautifulSoup(content, "html.parser")
            
            # Ищем ссылки на объявления (обычно содержат /search/ или /item/)
            for a in soup.find_all('a', href=True):
                href = a['href']
                if '/search/' in href or '/item/' in href:
                    if href.startswith('/'):
                        href = "https://kw.opensooq.com" + href
                    if href not in links and "opensooq.com" in href:
                        links.append(href)
                        
        except Exception as e:
            print(f"Ошибка категории: {e}")
        finally:
            await browser.close()
    return list(set(links))[:10] # Берем первые 10 штук

async def get_views_from_listing(listing_url):
    """Заходит в объявление, находит профиль и парсит просмотры"""
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
        )
        page = await context.new_page()
        try:
            await page.goto(listing_url, timeout=30000, wait_until="domcontentloaded")
            await page.wait_for_timeout(2000)
            
            content = await page.content()
            soup = BeautifulSoup(content, "html.parser")
            
            # Ищем ссылку на профиль в объявлении
            profile_url = None
            for a in soup.find_all('a', href=True):
                if '/profile/' in a['href'] or '/member/' in a['href']:
                    profile_url = a['href']
                    if not profile_url.startswith('http'):
                        profile_url = "https://kw.opensooq.com" + profile_url
                    break
            
            if not profile_url:
                return None, "Профиль не найден"
                
            # Заходим в профиль
            await page.goto(profile_url, timeout=30000, wait_until="domcontentloaded")
            await page.wait_for_timeout(3000)
            
            content = await page.content()
            soup = BeautifulSoup(content, "html.parser")
            text = soup.get_text(" ", strip=True)
            
            match = re.search(r"([\d.,٬٫]+\s*[kKmM]?)\s*(?:Views|مشاهدة|مشاهدات)", text, re.I)
            if match:
                return match.group(1).strip(), profile_url
                
            if '"views_count"' in content:
                json_match = re.search(r'"views_count"\s*:\s*(\d+)', content)
                if json_match: return json_match.group(1), profile_url
                
            return "Не найдено", profile_url
            
        except Exception as e:
            return f"Ошибка: {str(e)[:15]}", None
        finally:
            await browser.close()

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id in AUTHORIZED_USERS:
        await update.message.reply_text("✅ Отправь ссылку на категорию (поиск) OpenSooq.")
    else:
        await update.message.reply_text("🔒 Введи пароль:")

async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    
    if user_id not in AUTHORIZED_USERS:
        if text == PASSWORD:
            AUTHORIZED_USERS.add(user_id)
            await update.message.reply_text("✅ Пароль верный! Отправь ссылку на категорию.")
        else:
            await update.message.reply_text("❌ Неверный пароль.")
        return

    if "opensooq.com" not in text and "opn.so" not in text:
        await update.message.reply_text("⚠️ Отправь ссылку на категорию OpenSooq.")
        return

    msg = await update.message.reply_text("🔎 Ищу объявления в категории (это займет время)...")
    
    links = await get_links_from_category(text)
    
    if not links:
        await msg.edit_text("❌ Не удалось найти объявления. Возможно, сайт блокирует запрос.")
        return
        
    await msg.edit_text(f"Найдено {len(links)} объявлений. Проверяю профили...")
    
    results = []
    for i, link in enumerate(links):
        views, profile_url = await get_views_from_listing(link)
        if profile_url:
            results.append(f"Товар: {link}\nПрофиль: {profile_url}\nПросмотры: {views}\n")
        else:
            results.append(f"Товар: {link}\nНе удалось получить профиль.\n")
            
        if i % 3 == 0:
            await msg.edit_text(f"Обработано {i+1} из {len(links)}...")

    final_text = "\n---\n".join(results)
    if len(final_text) > 4000:
        final_text = final_text[:4000] + "..."
        
    await msg.edit_text(f"✅ Результаты:\n\n{final_text}", disable_web_page_preview=True)

def main():
    if not TOKEN: return
    app = Application.builder().token(TOKEN).build()
    app.add_handler(CommandHandler("start", start))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    print("✅ ПАРСЕР КАТЕГОРИЙ ЗАПУЩЕН")
    app.run_polling()

if __name__ == "__main__":
    main()
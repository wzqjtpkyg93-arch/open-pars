FROM python:3.11-slim

# Устанавливаем системные библиотеки, которые нужны браузеру
RUN apt-get update && apt-get install -y \
    wget gnupg curl libnss3 libatk-bridge2.0-0 libxkbcommon0 libgtk-3-0 libasound2 \
    && rm -rf /var/lib/apt/lists/*

# Копируем файлы и ставим зависимости Python
COPY requirements.txt .
RUN pip install -r requirements.txt

# Устанавливаем сам браузер Chromium для Playwright
RUN playwright install chromium

# Копируем код бота
COPY . .

# Запускаем бота
CMD ["python", "bot.py"]
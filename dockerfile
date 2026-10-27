FROM python:3.12-slim-bookworm

# Устанавливаем системные зависимости для Playwright
RUN apt-get update && apt-get install -y \
    wget \
    curl \
    git \
    libnss3 \
    libatk-bridge2.0-0 \
    libxkbcommon0 \
    libgtk-3-0 \
    libasound2 \
    && rm -rf /var/lib/apt/lists/*

# Переменные окружения
ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PLAYWRIGHT_BROWSERS_PATH=/opt/pw-browsers \
    DATABASE_PATH=/var/data/bot.sqlite3 \
    DATA_DIR=/var/data \
    TZ=Asia/Kuwait \
    PROFILE_BROWSER=1

WORKDIR /app

COPY requirements.txt .

# Устанавливаем библиотеки Python и браузер Chromium
RUN pip install --no-cache-dir -r requirements.txt \
    && python -m playwright install chromium \
    && playwright install-deps chromium

COPY bot.py .

CMD ["python", "-u", "bot.py"]
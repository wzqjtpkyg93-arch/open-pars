FROM python:3.12-slim-bookworm

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PLAYWRIGHT_BROWSERS_PATH=/opt/pw-browsers \
    DATABASE_PATH=/var/data/bot.sqlite3 \
    DATA_DIR=/var/data \
    APP_TIMEZONE=Europe/Moscow \
    PROFILE_BROWSER=1

WORKDIR /app

COPY requirements.txt .

RUN pip install --no-cache-dir -r requirements.txt \
    && python -m playwright install --with-deps chromium webkit

COPY bot.py .

CMD ["python", "-u", "bot.py"]
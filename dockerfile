FROM python:3.12-slim-bookworm

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PLAYWRIGHT_BROWSERS_PATH=/opt/pw-browsers \
    DATABASE_PATH=/var/data/bot.sqlite3 \
    DATA_DIR=/var/data \
    APP_TIMEZONE=Europe/Moscow \
    PROFILE_BROWSER=1

WORKDIR /app

RUN apt-get update \
    && apt-get install -y --no-install-recommends xvfb xauth x11vnc curl ca-certificates fonts-dejavu-core \
    && rm -rf /var/lib/apt/lists/*

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt "aiohttp==3.14.5" \
    && pip install --no-cache-dir "playwright==1.64.1" \
    && python -m playwright install --with-deps chromium chrome

RUN mkdir -p /opt/novnc \
    && curl --fail --location --retry 3 https://codeload.github.com/novnc/noVNC/tar.gz/refs/tags/v1.6.0 -o /tmp/novnc.tar.gz \
    && python -c "import hashlib; assert hashlib.sha256(open('/tmp/novnc.tar.gz','rb').read()).hexdigest() == '5066103959ef4e9b10f37e5a148627360dd8414e4cf8a7db92bdbd022e728aaa'" \
    && tar -xzf /tmp/novnc.tar.gz --strip-components=1 -C /opt/novnc \
    && rm /tmp/novnc.tar.gz

COPY bot.py .

CMD ["python", "-u", "bot.py"]
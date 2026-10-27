FROM mcr.microsoft.com/playwright/python:v1.49.0-noble

WORKDIR /app

# Прописываем токен напрямую в контейнер
ENV TOKEN=8816022011:AAGQHE3PVnngi33K8MxxO5DKzPL2BK7Ldlg

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

CMD ["python", "bot.py"]
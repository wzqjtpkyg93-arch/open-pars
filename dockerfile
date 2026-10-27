# Используем официальный образ Playwright для Python
FROM mcr.microsoft.com/playwright/python:v1.49.0-noble

# Устанавливаем рабочую директорию
WORKDIR /app

# Копируем файлы зависимостей
COPY requirements.txt .

# Устанавливаем Python-библиотеки
RUN pip install --no-cache-dir -r requirements.txt

# Копируем код бота
COPY . .

# Запускаем бота
CMD ["python", "bot.py"]
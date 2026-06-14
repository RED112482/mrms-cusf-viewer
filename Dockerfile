FROM python:3.11-slim

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    MPLBACKEND=Agg \
    MRMS_CACHE_DIR=/tmp/mrms_unit_streamflow_cache \
    PORT=8080

WORKDIR /app

# Minimal runtime libraries commonly needed by rasterio/Pillow wheels.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        libexpat1 \
        libjpeg62-turbo \
        zlib1g \
        libcurl4 \
    && rm -rf /var/lib/apt/lists/*

COPY requirements.txt .
RUN python -m pip install --upgrade pip \
    && pip install --no-cache-dir -r requirements.txt

COPY app.py .

EXPOSE 8080

CMD gunicorn -w ${WEB_CONCURRENCY:-2} -k gthread --threads ${WEB_THREADS:-4} --timeout ${WEB_TIMEOUT:-180} --bind 0.0.0.0:${PORT} app:app

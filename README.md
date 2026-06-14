# MRMS CUSF Viewer

NOAA/NWS experimental viewer — unofficial development tool. Not an operational NWS/NCEP product.  
Author: Kevin Gilmore

This is a Flask-based MRMS viewer that renders MRMS/FLASH/QPE/reflectivity GRIB2 data into Leaflet image overlays and supports synchronized 1-, 2-, and 4-panel viewing, point readouts, loops, area averages, and valid-at-time warning/advisory overlays.

## Why this needs a real web service

This is not a static GitHub Pages app. The backend downloads MRMS files, decompresses GRIB2 data, uses rasterio/numpy/Pillow to render PNGs, and serves API endpoints such as `/api/render.png`, `/api/value`, `/api/archive/list`, and `/api/alerts`.

Use GitHub to store the code, then deploy the app as a Docker web service on Render, Railway, Cloud Run, Fly.io, a VPS, or similar.

## Local run with Docker

```bash
docker build -t mrms-cusf-viewer .
docker run --rm -p 8080:8080 mrms-cusf-viewer
```

Open:

```text
http://localhost:8080/viewer
```

## Local run without Docker

```bash
python -m venv .venv
# Windows PowerShell:
.venv\Scripts\Activate.ps1
# macOS/Linux:
# source .venv/bin/activate

python -m pip install --upgrade pip
python -m pip install -r requirements.txt
python app.py
```

Open:

```text
http://localhost:8080/viewer
```

## Render deployment

1. Push these files to a GitHub repository.
2. In Render, create a new Web Service from the GitHub repository.
3. Select Docker runtime.
4. Use the included `Dockerfile` or `render.yaml`.
5. Health check path: `/healthz`.
6. Open the public Render URL, then `/viewer`.

Recommended environment variables:

```text
MRMS_CACHE_DIR=/tmp/mrms_unit_streamflow_cache
ENABLE_BACKGROUND_ARCHIVE=0
WEB_CONCURRENCY=2
WEB_THREADS=4
WEB_TIMEOUT=180
```

For a paid Render plan with a persistent disk, you can change:

```text
MRMS_CACHE_DIR=/var/data/mrms_unit_streamflow_cache
MRMS_ARCHIVE_DIR=/var/data/mrms_unit_streamflow_cache/archive
```

## Operational notes

- The cache is safe to be temporary for live viewing. If the container restarts, it will rebuild as users request data.
- A persistent disk is only needed if you want captured archive files to survive restarts.
- Public usage can increase load quickly because every render, loop frame, and point readout hits the backend.
- Keep `ENABLE_BACKGROUND_ARCHIVE=0` for public hosting unless persistent storage and hosting costs are planned.
- Consider disabling deep alert text checks by default if IEM/AFOS rate limits become a problem.

## Main endpoints

```text
/ or /viewer       Main viewer
/healthz          Health check
/api/metadata     App/product metadata
/api/render.png   Rendered MRMS overlay PNG
/api/value        Point value lookup
/api/alerts       Valid-at-time alerts
```

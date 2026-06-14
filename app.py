import csv
import gzip
import concurrent.futures
import hashlib
import io
import json
import math
import os
import re
import shutil
import tempfile
import threading
import time
import xml.etree.ElementTree as ET
from collections import OrderedDict
from datetime import datetime, timedelta, timezone
from urllib.parse import urljoin

import matplotlib
matplotlib.use("Agg")

import numpy as np
import requests
import rasterio
from PIL import Image
from flask import Flask, Response, jsonify, request, send_file
from flask_cors import CORS
from matplotlib.colors import LinearSegmentedColormap, Normalize
from matplotlib.path import Path as MplPath
from rasterio.enums import Resampling
from rasterio.transform import from_bounds
from rasterio.warp import reproject, transform as rio_transform
from rasterio.windows import Window
from rasterio.windows import from_bounds as window_from_bounds


app = Flask(__name__)
CORS(app)

APP_USER_AGENT = os.environ.get("APP_USER_AGENT", "MRMSUnitStreamflowViewer/1.0 KevinGilmore")
DEFAULT_PRODUCT = "CREST"

APP_TITLE = "MRMS CUSF Viewer"
APP_AUTHOR = "Kevin Gilmore"
APP_DISCLAIMER = (
    "NOAA/NWS experimental viewer — unofficial development tool. "
    "Not an operational NWS/NCEP product. Author: Kevin Gilmore."
)

CACHE_DIR = os.environ.get(
    "MRMS_CACHE_DIR",
    os.path.join(tempfile.gettempdir(), "mrms_unit_streamflow_cache"),
)
ARCHIVE_DIR = os.environ.get("MRMS_ARCHIVE_DIR", os.path.join(CACHE_DIR, "archive"))
os.makedirs(CACHE_DIR, exist_ok=True)
os.makedirs(ARCHIVE_DIR, exist_ok=True)

ENABLE_BACKGROUND_ARCHIVE = os.environ.get("ENABLE_BACKGROUND_ARCHIVE", "0").strip().lower() in ("1", "true", "yes", "on")
ARCHIVE_INTERVAL_SECONDS = int(os.environ.get("ARCHIVE_INTERVAL_SECONDS", str(10 * 60)))

MRMS_TIME_STEP_MINUTES = 10
ARCHIVE_LOOKBACK_HOURS = 24
ARCHIVE_LOOKBACK_MINUTES = ARCHIVE_LOOKBACK_HOURS * 60
# Some radar mosaics update around every 2 minutes, so keep enough remote
# directory entries to cover a full 24-hour picker/loop window for both radar
# and 10-minute FLASH/QPE products.
ARCHIVE_REMOTE_LIST_LIMIT = int((ARCHIVE_LOOKBACK_MINUTES / 2) + 80)

CACHE_TTL_SECONDS = 10 * 60

REMOTE_LIST_CACHE = {}
REMOTE_LIST_TTL_SECONDS = 5 * 60

RENDER_CACHE_TTL_SECONDS = 10 * 60
RENDER_STYLE_VERSION = "20260613_crest_coverage_delta_v1"

# Prevent duplicate concurrent downloads/renders when multiple panels request the
# same MRMS file or image at nearly the same time. This preserves output values
# and only avoids repeated work.
DOWNLOAD_LOCKS = {}
RENDER_LOCKS = {}
LOCKS_GUARD = threading.RLock()
TIME_WINDOW_DOWNLOAD_WORKERS = 6

MAX_CACHE = OrderedDict()
MAX_CACHE_TTL_SECONDS = 10 * 60
MAX_CACHE_MAX_ITEMS = 240

ALERT_CACHE = OrderedDict()
ALERT_CACHE_TTL_SECONDS = 5 * 60
ALERT_CACHE_MAX_ITEMS = 160

FFS_TEXT_CACHE = OrderedDict()
FFS_TEXT_CACHE_TTL_SECONDS = 20 * 60
FFS_TEXT_CACHE_MAX_ITEMS = 160
FFS_TEXT_CACHE_LOCK = threading.RLock()

AFOS_TEXT_CACHE = OrderedDict()
AFOS_TEXT_CACHE_TTL_SECONDS = 30 * 60
AFOS_TEXT_FAILURE_TTL_SECONDS = 8 * 60
AFOS_TEXT_CACHE_MAX_ITEMS = 320
AFOS_TEXT_TIMEOUT_SECONDS = 8
AFOS_TEXT_LIMIT = 300

M3S_PER_KM2_TO_CFS_PER_SQMI = 35.314666721 / 0.38610215855

PRODUCTS = {
    "CREST": {
        "display": "CREST Max Unit Streamflow",
        "directory": "https://mrms.ncep.noaa.gov/2D/FLASH/CREST_MAXUNITSTREAMFLOW/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/FLASH/CREST_MAXUNITSTREAMFLOW/MRMS_FLASH_CREST_MAXUNITSTREAMFLOW.latest.grib2.gz",
        "file_prefix": "MRMS_FLASH_CREST_MAXUNITSTREAMFLOW_00.00_",
        "step_minutes": 10,
    },
    "SAC": {
        "display": "SAC Max Unit Streamflow",
        "directory": "https://mrms.ncep.noaa.gov/2D/FLASH/SAC_MAXUNITSTREAMFLOW/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/FLASH/SAC_MAXUNITSTREAMFLOW/MRMS_FLASH_SAC_MAXUNITSTREAMFLOW.latest.grib2.gz",
        "file_prefix": "MRMS_FLASH_SAC_MAXUNITSTREAMFLOW_00.00_",
        "step_minutes": 10,
    },
    "HP": {
        "display": "HP Max Unit Streamflow",
        "directory": "https://mrms.ncep.noaa.gov/2D/FLASH/HP_MAXUNITSTREAMFLOW/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/FLASH/HP_MAXUNITSTREAMFLOW/MRMS_FLASH_HP_MAXUNITSTREAMFLOW.latest.grib2.gz",
        "file_prefix": "MRMS_FLASH_HP_MAXUNITSTREAMFLOW_00.00_",
        "step_minutes": 10,
    },
    "PRECIPRATE": {
        "display": "MRMS Instantaneous Rain Rate",
        "directory": "https://mrms.ncep.noaa.gov/2D/PrecipRate/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/PrecipRate/MRMS_PrecipRate.latest.grib2.gz",
        "file_prefix": "MRMS_PrecipRate_00.00_",
        "step_minutes": 2,
    },
    "QPE1H": {
        "display": "MRMS One-Hour Precipitation",
        "directory": "https://mrms.ncep.noaa.gov/2D/RadarOnly_QPE_01H/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/RadarOnly_QPE_01H/MRMS_RadarOnly_QPE_01H.latest.grib2.gz",
        "file_prefix": "MRMS_RadarOnly_QPE_01H_00.00_",
        "step_minutes": 10,
    },
    "QPE15M": {
        "display": "MRMS Fifteen-Minute Precipitation",
        "directory": "https://mrms.ncep.noaa.gov/2D/RadarOnly_QPE_15M/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/RadarOnly_QPE_15M/MRMS_RadarOnly_QPE_15M.latest.grib2.gz",
        "file_prefix": "MRMS_RadarOnly_QPE_15M_00.00_",
        "step_minutes": 15,
    },
    "QPE6H": {
        "display": "MRMS Six-Hour Precipitation",
        "directory": "https://mrms.ncep.noaa.gov/2D/RadarOnly_QPE_06H/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/RadarOnly_QPE_06H/MRMS_RadarOnly_QPE_06H.latest.grib2.gz",
        "file_prefix": "MRMS_RadarOnly_QPE_06H_00.00_",
        "step_minutes": 60,
    },
    "RALA": {
        "display": "MRMS Reflectivity At Lowest Altitude (RALA)",
        "directory": "https://mrms.ncep.noaa.gov/2D/ReflectivityAtLowestAltitude/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/ReflectivityAtLowestAltitude/MRMS_ReflectivityAtLowestAltitude.latest.grib2.gz",
        "file_prefix": "MRMS_ReflectivityAtLowestAltitude_00.50_",
        "step_minutes": 2,
    },
    "REFLQC": {
        "display": "MRMS Merged Reflectivity QC Mosaic",
        "directory": "https://mrms.ncep.noaa.gov/2D/MergedReflectivityQC/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/MergedReflectivityQC/MRMS_MergedReflectivityQC.latest.grib2.gz",
        "file_prefix": "MRMS_MergedReflectivityQC_00.50_",
        "step_minutes": 2,
    },
    "REFLCOMP": {
        "display": "MRMS Composite Reflectivity QC",
        "directory": "https://mrms.ncep.noaa.gov/2D/MergedReflectivityQCComposite/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/MergedReflectivityQCComposite/MRMS_MergedReflectivityQCComposite.latest.grib2.gz",
        "file_prefix": "MRMS_MergedReflectivityQCComposite_00.50_",
        "step_minutes": 2,
    },
    "REFL10C": {
        "display": "MRMS Reflectivity at -10°C",
        "directory": "https://mrms.ncep.noaa.gov/2D/Reflectivity_-10C/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/Reflectivity_-10C/MRMS_Reflectivity_-10C.latest.grib2.gz",
        "file_prefix": "MRMS_Reflectivity_-10C_00.50_",
        "step_minutes": 2,
    },
}

MM_TO_IN = 1.0 / 25.4

COLOR_MAX = 2000.0
# CREST/FLASH unit-streamflow palette matched to the supplied legend image.
# The near-duplicate stop pairs preserve the hard breaks visible at 100, 200,
# 400, 600, and 1000 cfs/mi^2.
COLOR_STOPS = [
    (0.0,     "#000000"),
    (100.0,   "#fefefe"),
    (100.01,  "#fefe00"),
    (200.0,   "#999900"),
    (200.01,  "#ff6346"),
    (400.0,   "#ffa500"),
    (400.01,  "#f08080"),
    (600.0,   "#800000"),
    (600.01,  "#800080"),
    (1000.0,  "#fe00fe"),
    (1000.01, "#0000ff"),
    (2000.0,  "#000080"),
]

STREAMFLOW_CMAP = LinearSegmentedColormap.from_list(
    "ff_unit_streamflow",
    [(v / COLOR_MAX, c) for v, c in COLOR_STOPS],
    N=256,
)

STREAMFLOW_NORM = Normalize(vmin=0.0, vmax=COLOR_MAX, clip=True)

DIFF_ABS_MAX = 200.0
DIFF_CMAP = LinearSegmentedColormap.from_list(
    "ff_unit_streamflow_diff",
    [
        (0.00, "#000000"),  # -200: strong decrease
        (0.25, "#00ffff"),  # -100: cyan
        (0.39, "#0096ff"),  # -44: brighter lower-end decrease
        (0.47, "#0033ff"),  # -12: blue compacted closer to zero
        (0.50, "#000000"),  # zero: black
        (0.53, "#ff0000"),  # +12: red compacted closer to zero
        (0.61, "#ff4bff"),  # +44: bright lower-end increase
        (0.75, "#ff00ff"),  # +100: magenta
        (1.00, "#000000"),  # +200: strong increase
    ],
    N=256,
)
DIFF_NORM = Normalize(vmin=-DIFF_ABS_MAX, vmax=DIFF_ABS_MAX, clip=True)

MRMS_QPE_COLOR_STOPS_IN = [
    (0.00, "#000000"),
    (0.01, "#04e9e7"),
    (0.10, "#019ff4"),
    (0.25, "#0300f4"),
    (0.50, "#02fd02"),
    (0.75, "#01c501"),
    (1.00, "#008e00"),
    (1.50, "#fdf802"),
    (2.00, "#e5bc00"),
    (3.00, "#fd9500"),
    (4.00, "#fd0000"),
    (6.00, "#d40000"),
    (8.00, "#bc0000"),
    (10.00, "#f800fd"),
    (12.00, "#9854c6"),
    (16.00, "#fdfdfd"),
]
MRMS_QPE_MAX_IN = 16.0
MRMS_QPE_CMAP = LinearSegmentedColormap.from_list(
    "mrms_qpe",
    [(v / MRMS_QPE_MAX_IN, c) for v, c in MRMS_QPE_COLOR_STOPS_IN],
    N=256,
)
MRMS_QPE_NORM = Normalize(vmin=0.0, vmax=MRMS_QPE_MAX_IN, clip=True)

QPE_DIFF_ABS_MAX_IN = 4.0
MRMS_QPE_DIFF_CMAP = LinearSegmentedColormap.from_list(
    "mrms_qpe_diff_30m",
    [
        (0.00, "#000000"),  # -4.00 in: strong decrease
        (0.25, "#00ffff"),  # -2.00 in: cyan
        (0.39, "#0096ff"),  # lower-end decrease contrast
        (0.47, "#0033ff"),  # blue compacted closer to zero
        (0.50, "#000000"),  # zero: black
        (0.53, "#ff0000"),  # red compacted closer to zero
        (0.61, "#ff4bff"),  # lower-end increase contrast
        (0.75, "#ff00ff"),  # +2.00 in: magenta
        (1.00, "#000000"),  # +4.00 in: strong increase
    ],
    N=256,
)
MRMS_QPE_DIFF_NORM = Normalize(vmin=-QPE_DIFF_ABS_MAX_IN, vmax=QPE_DIFF_ABS_MAX_IN, clip=True)

# Instantaneous rain-rate palette matched to the user-supplied reference legend.
MRMS_RAINRATE_COLOR_STOPS_INHR = [
    (0.00, "#000000"),
    (0.01, "#202020"),
    (0.99, "#d0d0d0"),
    (1.00, "#0515ff"),
    (2.00, "#1bf0ff"),
    (3.00, "#47e987"),
    (4.00, "#f88cf8"),
    (5.00, "#ffd703"),
    (6.00, "#ff9302"),
    (8.00, "#ff0101"),
    (10.00, "#ffc0c0"),
    (12.00, "#ffffff"),
]
MRMS_RAINRATE_MAX_INHR = 12.0
MRMS_RAINRATE_CMAP = LinearSegmentedColormap.from_list(
    "mrms_rainrate",
    [(v / MRMS_RAINRATE_MAX_INHR, c) for v, c in MRMS_RAINRATE_COLOR_STOPS_INHR],
    N=256,
)
MRMS_RAINRATE_NORM = Normalize(vmin=0.0, vmax=MRMS_RAINRATE_MAX_INHR, clip=True)

# RALA / reflectivity palette matched to the user-supplied reference legend.
MRMS_REFL_COLOR_STOPS_DBZ = [
    (-30.0, "#080608"),
    (-25.0, "#16041d"),
    (-20.0, "#2a0536"),
    (-15.0, "#3c0c4c"),
    (-10.0, "#3a2441"),
    (-5.0, "#474747"),
    (0.0, "#828788"),
    (5.0, "#a8acb0"),
    (10.0, "#3f5c93"),
    (15.0, "#5ba5c0"),
    (20.0, "#2cbc54"),
    (25.0, "#0fa20f"),
    (30.0, "#107b0c"),
    (35.0, "#497e03"),
    (40.0, "#e3ca05"),
    (45.0, "#e09f04"),
    (50.0, "#e50402"),
    (55.0, "#b50301"),
    (60.0, "#b14a68"),
    (65.0, "#e506e5"),
    (70.0, "#9677e3"),
    (75.0, "#4706e4"),
    (80.0, "#0103e3"),
]
MRMS_REFL_MIN_DBZ = -30.0
MRMS_REFL_MAX_DBZ = 80.0
MRMS_REFL_CMAP = LinearSegmentedColormap.from_list(
    "mrms_reflectivity",
    [((v - MRMS_REFL_MIN_DBZ) / (MRMS_REFL_MAX_DBZ - MRMS_REFL_MIN_DBZ), c) for v, c in MRMS_REFL_COLOR_STOPS_DBZ],
    N=256,
)
MRMS_REFL_NORM = Normalize(vmin=MRMS_REFL_MIN_DBZ, vmax=MRMS_REFL_MAX_DBZ, clip=True)


PARAMETERS = {
    "CREST": {
        "display": "CREST Max Unit Streamflow",
        "kind": "raw",
        "product": "CREST",
        "units": "cfs/mi^2",
        "native_units": "m^3/s/km^2",
        "style": "streamflow",
    },
    "SAC": {
        "display": "SAC Max Unit Streamflow",
        "kind": "raw",
        "product": "SAC",
        "units": "cfs/mi^2",
        "native_units": "m^3/s/km^2",
        "style": "streamflow",
    },
    "HP": {
        "display": "HP Max Unit Streamflow",
        "kind": "raw",
        "product": "HP",
        "units": "cfs/mi^2",
        "native_units": "m^3/s/km^2",
        "style": "streamflow",
    },
    "RAINRATE": {
        "display": "MRMS Instantaneous Rain Rate",
        "kind": "raw",
        "product": "PRECIPRATE",
        "units": "in/hr",
        "native_units": "mm/hr",
        "style": "rainrate",
    },
    "RAINRATE_MAX_30M": {
        "display": "MRMS 30-Min Max Instantaneous Rain Rate",
        "kind": "derived_max",
        "product": "PRECIPRATE",
        "units": "in/hr",
        "native_units": "mm/hr",
        "style": "rainrate",
        "description": "Pixel-wise maximum MRMS instantaneous rain rate observed during the latest/selected 30-minute window",
    },
    "QPE1H": {
        "display": "MRMS One-Hour Precipitation",
        "kind": "raw",
        "product": "QPE1H",
        "units": "in",
        "native_units": "mm",
        "style": "qpe",
    },
    "QPE1H_DIFF_30M": {
        "display": "MRMS One-Hour QPE Δ 30 min",
        "kind": "difference",
        "product": "QPE1H",
        "units": "in",
        "native_units": "mm",
        "style": "qpe_difference",
        "description": "Current/selected rolling 1-hour QPE minus rolling 1-hour QPE 30 minutes earlier",
    },
    "QPE30M": {
        "display": "MRMS Past 30-Minute Precipitation",
        "kind": "derived_sum",
        "product": "QPE15M",
        "units": "in",
        "native_units": "mm",
        "style": "qpe",
        "description": "Current/selected RadarOnly QPE 15M plus the previous 15M file ending 15 minutes earlier",
    },
    "QPE6H": {
        "display": "MRMS Six-Hour Precipitation",
        "kind": "raw",
        "product": "QPE6H",
        "units": "in",
        "native_units": "mm",
        "style": "qpe",
    },
    "RALA": {
        "display": "MRMS Reflectivity At Lowest Altitude (RALA)",
        "kind": "raw",
        "product": "RALA",
        "units": "dBZ",
        "native_units": "dBZ",
        "style": "reflectivity",
    },
    "REFLQC": {
        "display": "MRMS Merged Reflectivity QC Mosaic",
        "kind": "raw",
        "product": "REFLQC",
        "units": "dBZ",
        "native_units": "dBZ",
        "style": "reflectivity",
    },
    "REFLCOMP": {
        "display": "MRMS Composite Reflectivity QC",
        "kind": "raw",
        "product": "REFLCOMP",
        "units": "dBZ",
        "native_units": "dBZ",
        "style": "reflectivity",
    },
    "REFL10C": {
        "display": "MRMS Reflectivity at -10°C",
        "kind": "raw",
        "product": "REFL10C",
        "units": "dBZ",
        "native_units": "dBZ",
        "style": "reflectivity",
    },
    "CREST_DIFF_10M": {
        "display": "CREST Δ 10 min",
        "kind": "difference",
        "units": "cfs/mi^2",
        "description": "Current/selected CREST minus previous CREST update 10 minutes earlier",
    },
    "HP_MINUS_CREST": {
        "display": "HP − CREST Difference",
        "kind": "difference",
        "units": "cfs/mi^2",
        "description": "HP Max Unit Streamflow minus regular CREST Max Unit Streamflow",
    },
}


def parameter_info(param, fallback_product=None):
    param = (param or fallback_product or DEFAULT_PRODUCT).upper()

    if param in PRODUCTS and param not in PARAMETERS:
        return param, {
            "display": PRODUCTS[param]["display"],
            "kind": "raw",
            "product": param,
            "units": "cfs/mi^2",
            "native_units": "m^3/s/km^2",
            "style": "streamflow",
        }

    if param not in PARAMETERS:
        raise ValueError(f"Unknown parameter '{param}'. Valid options: {', '.join(PARAMETERS.keys())}")

    return param, PARAMETERS[param]


VIEWER_HTML = r"""
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>MRMS CUSF Viewer — NOAA/NWS Experimental</title>

  <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css">

  <style>
    html, body {
      height: 100%;
      width: 100%;
      margin: 0;
      padding: 0;
      background: #000;
      font-family: Arial, sans-serif;
      overflow: hidden;
    }

    #mapGrid {
      position: absolute;
      top: 26px;
      bottom: 26px;
      left: 332px;
      right: 0;
      display: grid;
      gap: 2px;
      background: #111;
      transition: left 0.18s ease;
    }

    body.sidebar-collapsed #mapGrid {
      left: 42px;
    }

    #mapGrid.layout-1 {
      grid-template-columns: 1fr;
      grid-template-rows: 1fr;
    }

    #mapGrid.layout-2 {
      grid-template-columns: 1fr 1fr;
      grid-template-rows: 1fr;
    }

    #mapGrid.layout-4 {
      grid-template-columns: 1fr 1fr;
      grid-template-rows: 1fr 1fr;
    }

    #mapGrid.layout-1 .mapPane:not(:first-child),
    #mapGrid.layout-2 .mapPane:nth-child(n+3) {
      display: none;
    }

    .mapPane {
      position: relative;
      min-width: 0;
      min-height: 0;
      height: 100%;
      border-left: 1px solid #222;
      border-right: 1px solid #222;
      overflow: hidden;
      background: #000;
    }

    .panelMap {
      position: absolute;
      top: 28px;
      left: 0;
      right: 0;
      bottom: 0;
      height: auto;
      width: auto;
      background: #000;
    }

    .panelTitle {
      position: absolute;
      top: 36px;
      right: 10px;
      z-index: 9998;
      background: rgba(0,0,0,0.72);
      color: #fff;
      padding: 4px 7px;
      border: 1px solid #999;
      border-radius: 4px;
      font-size: 12px;
      font-weight: bold;
      pointer-events: none;
      text-align: right;
      line-height: 1.25;
    }

    .panelLegend {
      position: absolute;
      top: 0;
      left: 0;
      right: 0;
      height: 28px;
      z-index: 9999;
      background: rgba(0,0,0,0.90);
      border-bottom: 1px solid #111;
      pointer-events: none;
    }

    .panelLegendBar {
      position: absolute;
      left: 6px;
      right: 6px;
      top: 4px;
      height: 12px;
      border: 1px solid #111;
    }

    .panelLegendTicks {
      position: absolute;
      left: 6px;
      right: 6px;
      top: 16px;
      height: 10px;
    }

    .panelTick {
      position: absolute;
      top: 0;
      transform: translateX(-50%);
      color: white;
      text-shadow: 1px 1px 2px #000, -1px -1px 2px #000;
      font-weight: bold;
      font-size: 10px;
      line-height: 10px;
      white-space: nowrap;
    }

    #controls {
      position: absolute;
      top: 0;
      bottom: 0;
      left: 0;
      z-index: 10000;
      width: 332px;
      background: rgba(10,10,10,0.96);
      color: white;
      box-shadow: 0 2px 8px rgba(0,0,0,0.65);
      font-size: 12px;
      border-right: 1px solid #555;
      overflow: hidden;
      display: flex;
      flex-direction: column;
      transition: width 0.18s ease;
    }

    body.sidebar-collapsed #controls {
      width: 42px;
    }

    #controlsHeader {
      display: flex;
      align-items: center;
      justify-content: space-between;
      padding: 8px 8px 8px 10px;
      border-bottom: 1px solid #444;
      min-height: 34px;
      box-sizing: border-box;
      background: rgba(18,18,18,0.98);
    }

    #controlsHeaderTitle {
      font-size: 13px;
      font-weight: bold;
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
      margin-right: 8px;
    }

    #sidebarToggle {
      margin-top: 0;
      min-width: 24px;
      width: 24px;
      height: 24px;
      padding: 0;
      line-height: 22px;
      text-align: center;
      font-size: 14px;
      font-weight: bold;
      flex: 0 0 auto;
    }

    #controlsContent {
      padding: 10px 12px;
      overflow-y: auto;
      overflow-x: hidden;
      flex: 1 1 auto;
    }

    body.sidebar-collapsed #controlsContent,
    body.sidebar-collapsed #controlsHeaderTitle {
      display: none;
    }

    #controls b { font-size: 14px; }

    label {
      display: inline-block;
      margin-top: 8px;
      font-weight: bold;
    }

    select, button, input {
      margin-top: 4px;
      font-size: 12px;
      background: #222;
      color: white;
      border: 1px solid #777;
      border-radius: 3px;
      padding: 3px;
      max-width: 100%;
      box-sizing: border-box;
    }

    select.panelParam {
      width: 100%;
      max-width: 100%;
      box-sizing: border-box;
    }

    .panelRow {
      margin-top: 6px;
    }

    .panelRow.hiddenPanelControl {
      display: none;
    }

    .loop-controls {
      margin-top: 8px;
      padding: 7px;
      border: 1px solid #333;
      border-radius: 4px;
      background: rgba(255,255,255,0.04);
    }

    .loop-controls select {
      width: auto;
      margin-right: 4px;
    }

    button {
      cursor: pointer;
      padding: 4px 8px;
    }

    button:hover { background: #333; }

    #status {
      margin-top: 8px;
      font-size: 11px;
      color: #ddd;
      line-height: 1.35;
      max-width: 100%;
    }

    .experimental-banner {
      margin-top: 8px;
      padding: 7px 8px;
      border: 1px solid #f0c85a;
      border-radius: 4px;
      background: rgba(240, 200, 90, 0.10);
      color: #ffe8a3;
      font-size: 11px;
      line-height: 1.35;
      font-weight: bold;
    }

    .small-note {
      color: #aaa;
      font-size: 11px;
      margin-top: 5px;
      line-height: 1.35;
    }

    .leaflet-popup-content {
      font-size: 13px;
      line-height: 1.35;
    }

    .leaflet-container { background: #000; }

    .alert-key {
      font-size: 11px;
      line-height: 1.35;
      margin-top: 5px;
      color: #ddd;
    }

    .color-chip {
      display: inline-block;
      width: 12px;
      height: 9px;
      margin-right: 4px;
      border: 1px solid #999;
    }

    .alert-tooltip {
      background: rgba(0,0,0,0.78);
      color: white;
      border: 1px solid #ccc;
      font-size: 11px;
      font-weight: bold;
      padding: 2px 4px;
      white-space: nowrap;
    }

    .max-tooltip {
      background: rgba(0,0,0,0.82);
      color: #ffffff;
      border: 2px solid #ffffff;
      font-size: 12px;
      font-weight: bold;
      padding: 3px 5px;
      white-space: nowrap;
    }

    .hover-value-tooltip {
      background: rgba(0,0,0,0.86);
      color: #ffffff;
      border: 1px solid #ffffff;
      font-size: 12px;
      font-weight: bold;
      padding: 3px 5px;
      white-space: nowrap;
      pointer-events: none;
    }


    .click-readout-popup .leaflet-popup-content-wrapper {
      background: rgba(0,0,0,0.94);
      color: #ffffff;
      border: 1px solid #ffffff;
      border-radius: 4px;
      box-shadow: 0 0 8px rgba(255,255,255,0.25);
      font-size: 12px;
      font-weight: bold;
    }

    .click-readout-popup .leaflet-popup-content {
      color: #ffffff;
      margin: 8px 10px;
      line-height: 1.4;
    }

    .click-readout-popup .leaflet-popup-tip {
      background: rgba(0,0,0,0.94);
      border: 1px solid #ffffff;
    }

    .click-readout-popup .leaflet-popup-close-button {
      color: #ffffff !important;
      font-weight: bold;
    }

    .click-readout-pulse-marker {
      background: transparent;
      border: none;
    }

    .click-readout-pulse-ring {
      width: 22px;
      height: 22px;
      border: 2px solid #ffffff;
      border-radius: 50%;
      box-shadow: 0 0 7px rgba(255,255,255,0.95);
      animation: click-readout-pulse 1.15s ease-out infinite;
    }

    @keyframes click-readout-pulse {
      0% { opacity: 1.0; transform: scale(0.58); }
      65% { opacity: 0.38; transform: scale(1.12); }
      100% { opacity: 0.08; transform: scale(1.35); }
    }

    .area-avg-pulse-shape {
      stroke: #ffffff !important;
      animation: area-avg-outline-pulse 1.15s ease-in-out infinite;
      filter: drop-shadow(0 0 4px rgba(255,255,255,0.95));
    }

    @keyframes area-avg-outline-pulse {
      0% { stroke-opacity: 0.55; stroke-width: 2.2px; }
      50% { stroke-opacity: 1.0; stroke-width: 5.2px; }
      100% { stroke-opacity: 0.55; stroke-width: 2.2px; }
    }

    .area-avg-popup .leaflet-popup-content-wrapper {
      background: rgba(0,0,0,0.88);
      color: #ffffff;
      border: 1px solid #ffffff;
      font-size: 12px;
      font-weight: bold;
    }

    .area-avg-popup .leaflet-popup-tip {
      background: rgba(0,0,0,0.88);
    }

    .mode-indicator {
      display: inline-flex;
      align-items: center;
      gap: 5px;
      margin-left: 6px;
      font-size: 11px;
      font-weight: bold;
      vertical-align: middle;
      white-space: nowrap;
    }

    .mode-dot {
      width: 9px;
      height: 9px;
      border-radius: 50%;
      display: inline-block;
      animation: pulse-mode 1.1s infinite;
    }

    .mode-live { color: #ffb3b3; }
    .mode-live .mode-dot {
      background: #ff0000;
      box-shadow: 0 0 7px rgba(255, 0, 0, 0.85);
    }

    .mode-archive { color: #b7d8ff; }
    .mode-archive .mode-dot {
      background: #1e90ff;
      box-shadow: 0 0 7px rgba(30, 144, 255, 0.85);
    }

    #validTimeReadout {
      margin-top: 5px;
      color: #ddd;
      font-size: 11px;
      line-height: 1.3;
    }

    .timeButtonActive {
      border-color: #ffffff;
      box-shadow: 0 0 5px rgba(255,255,255,0.45);
    }

    @keyframes pulse-mode {
      0% { opacity: 0.30; transform: scale(0.9); }
      50% { opacity: 1.0; transform: scale(1.15); }
      100% { opacity: 0.30; transform: scale(0.9); }
    }
  </style>
</head>

<body>

  <div id="controls">
    <div id="controlsHeader">
      <div id="controlsHeaderTitle">MRMS Panel Controls</div>
      <button id="sidebarToggle" onclick="toggleSidebar()" title="Collapse controls">&#171;</button>
    </div>
    <div id="controlsContent">
    <b>MRMS CUSF Viewer</b><br>
    Synchronized MRMS viewer. Units depend on the selected element.
    <div class="experimental-banner">
      NOAA/NWS experimental viewer — unofficial development tool. Not an operational NWS/NCEP product.<br>
      Author: Kevin Gilmore
    </div>

    <br>

    <label>Panel Layout</label><br>
    <select id="panelLayout" onchange="layoutChanged()">
      <option value="1">1 panel</option>
      <option value="2" selected>2 panels</option>
      <option value="4">4 panels</option>
    </select>

    <br>

    <label>Panel Elements</label><br>
    <div id="panelControl-left" class="panelRow">Panel 1:
    <select id="leftParam" class="panelParam" onchange="panelParamChanged('left')">
      <option value="CREST">CREST Max Unit Streamflow</option>
      <option value="SAC">SAC Max Unit Streamflow</option>
      <option value="HP">HP Max Unit Streamflow</option>
      <option value="RAINRATE">MRMS Instantaneous Rain Rate</option>
      <option value="RAINRATE_MAX_30M">MRMS 30-Min Max Instantaneous Rain Rate</option>
      <option value="QPE1H">MRMS One-Hour Precipitation</option>
      <option value="QPE1H_DIFF_30M">MRMS One-Hour QPE Δ 30 min</option>
      <option value="QPE30M">MRMS Past 30-Minute Precipitation</option>
      <option value="QPE6H">MRMS Six-Hour Precipitation</option>
      <option value="RALA">MRMS Reflectivity At Lowest Altitude (RALA)</option>
      <option value="REFLQC">MRMS Merged Reflectivity QC Mosaic</option>
      <option value="REFLCOMP">MRMS Composite Reflectivity QC</option>
      <option value="REFL10C">MRMS Reflectivity at -10°C</option>
      <option value="CREST_DIFF_10M">CREST Δ 10 min</option>
      <option value="HP_MINUS_CREST">HP − CREST Difference</option>
    </select></div>
    <div id="panelControl-right" class="panelRow">Panel 2:
    <select id="rightParam" class="panelParam" onchange="panelParamChanged('right')">
      <option value="CREST">CREST Max Unit Streamflow</option>
      <option value="SAC">SAC Max Unit Streamflow</option>
      <option value="HP">HP Max Unit Streamflow</option>
      <option value="RAINRATE">MRMS Instantaneous Rain Rate</option>
      <option value="RAINRATE_MAX_30M">MRMS 30-Min Max Instantaneous Rain Rate</option>
      <option value="QPE1H">MRMS One-Hour Precipitation</option>
      <option value="QPE1H_DIFF_30M">MRMS One-Hour QPE Δ 30 min</option>
      <option value="QPE30M">MRMS Past 30-Minute Precipitation</option>
      <option value="QPE6H">MRMS Six-Hour Precipitation</option>
      <option value="RALA">MRMS Reflectivity At Lowest Altitude (RALA)</option>
      <option value="REFLQC">MRMS Merged Reflectivity QC Mosaic</option>
      <option value="REFLCOMP">MRMS Composite Reflectivity QC</option>
      <option value="REFL10C">MRMS Reflectivity at -10°C</option>
      <option value="CREST_DIFF_10M">CREST Δ 10 min</option>
      <option value="HP_MINUS_CREST">HP − CREST Difference</option>
    </select></div>
    <div id="panelControl-lowerLeft" class="panelRow">Panel 3:
    <select id="lowerLeftParam" class="panelParam" onchange="panelParamChanged('lowerLeft')">
      <option value="CREST">CREST Max Unit Streamflow</option>
      <option value="SAC">SAC Max Unit Streamflow</option>
      <option value="HP">HP Max Unit Streamflow</option>
      <option value="RAINRATE">MRMS Instantaneous Rain Rate</option>
      <option value="RAINRATE_MAX_30M">MRMS 30-Min Max Instantaneous Rain Rate</option>
      <option value="QPE1H">MRMS One-Hour Precipitation</option>
      <option value="QPE1H_DIFF_30M">MRMS One-Hour QPE Δ 30 min</option>
      <option value="QPE30M">MRMS Past 30-Minute Precipitation</option>
      <option value="QPE6H">MRMS Six-Hour Precipitation</option>
      <option value="RALA">MRMS Reflectivity At Lowest Altitude (RALA)</option>
      <option value="REFLQC">MRMS Merged Reflectivity QC Mosaic</option>
      <option value="REFLCOMP">MRMS Composite Reflectivity QC</option>
      <option value="REFL10C">MRMS Reflectivity at -10°C</option>
      <option value="CREST_DIFF_10M">CREST Δ 10 min</option>
      <option value="HP_MINUS_CREST">HP − CREST Difference</option>
    </select></div>
    <div id="panelControl-lowerRight" class="panelRow">Panel 4:
    <select id="lowerRightParam" class="panelParam" onchange="panelParamChanged('lowerRight')">
      <option value="CREST">CREST Max Unit Streamflow</option>
      <option value="SAC">SAC Max Unit Streamflow</option>
      <option value="HP">HP Max Unit Streamflow</option>
      <option value="RAINRATE">MRMS Instantaneous Rain Rate</option>
      <option value="RAINRATE_MAX_30M">MRMS 30-Min Max Instantaneous Rain Rate</option>
      <option value="QPE1H">MRMS One-Hour Precipitation</option>
      <option value="QPE1H_DIFF_30M">MRMS One-Hour QPE Δ 30 min</option>
      <option value="QPE30M">MRMS Past 30-Minute Precipitation</option>
      <option value="QPE6H">MRMS Six-Hour Precipitation</option>
      <option value="RALA">MRMS Reflectivity At Lowest Altitude (RALA)</option>
      <option value="REFLQC">MRMS Merged Reflectivity QC Mosaic</option>
      <option value="REFLCOMP">MRMS Composite Reflectivity QC</option>
      <option value="REFL10C">MRMS Reflectivity at -10°C</option>
      <option value="CREST_DIFF_10M">CREST Δ 10 min</option>
      <option value="HP_MINUS_CREST">HP − CREST Difference</option>
    </select></div>

    <br>

    <label>Time Mode
      <span id="modeIndicator" class="mode-indicator mode-live">
        <span class="mode-dot"></span><span id="modeText">LIVE</span> <span id="modeTimeText"></span>
      </span>
    </label><br>
    <input id="timeMode" type="hidden" value="latest">
    <button id="liveButton" onclick="goLive()">Go LIVE / Latest</button>
    <button id="archiveButton" onclick="goArchiveMode()">Archive Mode</button>
    <div id="validTimeReadout">Valid: loading latest Z...</div>

    <br>

    <label>Archive Base Time, UTC/Z</label><br>
    <input id="archiveTime" type="text" placeholder="YYYYMMDD-HHMMSSZ" autocomplete="off" style="width: 150px;">
    <button onclick="loadArchiveList()">List Recent</button>

    <br>

    <select id="archiveList" style="width: 100%; box-sizing: border-box;">
      <option value="">Recent MRMS archive times will appear here</option>
    </select>

    <br>

    <label>Time Trend Slider</label><br>
    <input id="timeOffset" type="range" min="-1440" max="0" step="10" value="0" style="width: 250px;" oninput="timelineChanged(false)">
    <span id="timeOffsetLabel">Current Z</span>

    <div class="loop-controls">
      <label style="margin-top:0;">Loop</label><br>
      Frames:
      <select id="loopFrames">
        <option value="6">6</option>
        <option value="12" selected>12</option>
        <option value="18">18</option>
        <option value="24">24</option>
      </select>
      Skip:
      <select id="loopSkip">
        <option value="1" selected>every file</option>
        <option value="2">every other file</option>
        <option value="3">every 3rd file</option>
        <option value="5">every 5th file</option>
      </select>
      Speed:
      <select id="loopDelay">
        <option value="140">fast</option>
        <option value="220" selected>smooth</option>
        <option value="350">slower</option>
      </select><br>
      <button onclick="startLoop()">Preload / Play Loop</button>
      <button onclick="stopLoop(true)">Stop Loop</button>
      <div class="small-note">Loop preloads all frames first, then swaps already-loaded images so animation is complete and less glitchy. Best with one radar element or a 2-panel comparison.</div>
    </div>

    <br>

    <label>Overlays</label><br>
    <input id="showAlerts" type="checkbox" checked onchange="refreshAllAlerts()">
    Valid-at-time FFW / FFS / Flood Advisory outlines<br>

    <input id="showAlertLabels" type="checkbox" checked onchange="refreshAllAlerts()">
    Show warning number + status labels<br>

    <input id="deepAlertText" type="checkbox" checked onchange="refreshAllAlerts()">
    Deep FFW/FFS text status check for CONSIDERABLE/EMERGENCY<br>

    <input id="showHoverReadout" type="checkbox" onchange="toggleHoverReadouts()">
    Hover value readout<br>
    <button onclick="clearAllClickReadouts()" style="margin-top:4px;">Clear all panel readouts</button><br>


    <input id="enableAreaAvg" type="checkbox" onchange="toggleAreaAverageTool()">
    Area average free-draw tool<br>
    <button onclick="finishAreaAveragePolygon()" style="margin-top:4px;">Finish Area</button>
    <button onclick="clearAreaAverage()" style="margin-top:4px;">Clear Area Average</button>
    <div class="small-note">When enabled, click points on any panel to draw any shape. Double-click or use Finish Area to close it. The same shape mirrors to all visible panels and computes the average for each selected element.</div>

    <input id="autoRender" type="checkbox" checked>
    Auto re-render after pan/zoom<br>

    <input id="fastRender" type="checkbox" checked onchange="fastRenderChanged()">
    Fast render mode — lower display resolution, same source data/readouts

    <div class="alert-key">
      <span class="color-chip" style="background:#00ff00"></span>FFW base<br>
      <span class="color-chip" style="background:#90ee90"></span>Flood Advisory<br>
      <span class="color-chip" style="background:#006400"></span>Considerable FFW / latest FFS<br>
      <span class="color-chip" style="background:#ff00ff"></span>Flash Flood Emergency<br>
    </div>

    <label>Overlay opacity</label><br>
    <input id="opacity" type="range" min="0" max="100" value="100" oninput="setOverlayOpacity()">

    <br><br>

    <button onclick="refreshAllLayers(false)">Refresh View</button>
    <button onclick="refreshAllLayers(true)">Render Current View</button>
    <button onclick="captureNow()">Capture Latest</button>

    <div id="status">Loading...</div>

    <div class="small-note">
      Panel layout and element selections are saved in this browser until changed. All visible maps pan/zoom together. Click any panel to open matching readouts in every visible panel; use Clear all panel readouts or Esc to remove them. Hover readout is optional to reduce requests while panning.
    </div>
    </div>
  </div>

  <div id="mapGrid" class="layout-2">
    <div class="mapPane">
      <div class="panelLegend"><div id="leftLegendBar" class="panelLegendBar"></div><div id="leftLegendTicks" class="panelLegendTicks"></div></div>
      <div id="mapLeft" class="panelMap"></div>
      <div id="leftTitle" class="panelTitle">Panel 1</div>
    </div>
    <div class="mapPane">
      <div class="panelLegend"><div id="rightLegendBar" class="panelLegendBar"></div><div id="rightLegendTicks" class="panelLegendTicks"></div></div>
      <div id="mapRight" class="panelMap"></div>
      <div id="rightTitle" class="panelTitle">Panel 2</div>
    </div>
    <div class="mapPane">
      <div class="panelLegend"><div id="lowerLeftLegendBar" class="panelLegendBar"></div><div id="lowerLeftLegendTicks" class="panelLegendTicks"></div></div>
      <div id="mapLowerLeft" class="panelMap"></div>
      <div id="lowerLeftTitle" class="panelTitle">Panel 3</div>
    </div>
    <div class="mapPane">
      <div class="panelLegend"><div id="lowerRightLegendBar" class="panelLegendBar"></div><div id="lowerRightLegendTicks" class="panelLegendTicks"></div></div>
      <div id="mapLowerRight" class="panelMap"></div>
      <div id="lowerRightTitle" class="panelTitle">Panel 4</div>
    </div>
  </div>


  <script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
  <script src="https://unpkg.com/esri-leaflet@3.0.14/dist/esri-leaflet.js"></script>

  <script>
    const domains = {
      LIX: {
        west: -91.95, south: 27.85, east: -88.25, north: 31.45,
        center: [30.25, -90.10], zoom: 8
      },
      MOB: {
        west: -89.55, south: 28.25, east: -85.85, north: 31.85,
        center: [30.75, -87.75], zoom: 8
      },
      LCH: {
        west: -94.45, south: 28.75, east: -91.05, north: 31.55,
        center: [30.32, -93.02], zoom: 8
      },
      JAX: {
        west: -83.55, south: 28.70, east: -80.30, north: 31.65,
        center: [30.40, -81.85], zoom: 8
      },
      GULF: {
        west: -94.50, south: 27.00, east: -84.50, north: 33.00,
        center: [30.25, -89.20], zoom: 7
      }
    };

    // Hard-coded startup/domain view. Change this value to MOB, LCH, JAX,
    // or GULF, or edit the bounds/center/zoom in the domains object above.
    const DEFAULT_VIEW_DOMAIN = "LIX";

    const ARCHIVE_LOOKBACK_MINUTES = 24 * 60;
    const ARCHIVE_LOOKAHEAD_MINUTES = 60;

    const parameterInfo = {
      CREST: {
        label: "CREST Max Unit Streamflow",
        shortLabel: "CREST",
        product: "CREST",
        units: "cfs/mi²",
        isDifference: false
      },
      SAC: {
        label: "SAC Max Unit Streamflow",
        shortLabel: "SAC",
        product: "SAC",
        units: "cfs/mi²",
        isDifference: false
      },
      HP: {
        label: "HP Max Unit Streamflow",
        shortLabel: "HP",
        product: "HP",
        units: "cfs/mi²",
        nativeUnits: "m³/s/km²",
        isDifference: false
      },
      RAINRATE: {
        label: "MRMS Instantaneous Rain Rate",
        shortLabel: "RainRate",
        product: "PRECIPRATE",
        units: "in/hr",
        nativeUnits: "mm/hr",
        isDifference: false
      },
      RAINRATE_MAX_30M: {
        label: "MRMS 30-Min Max Instantaneous Rain Rate",
        shortLabel: "Max RR 30m",
        product: "PRECIPRATE",
        units: "in/hr",
        nativeUnits: "mm/hr",
        isDifference: false
      },
      QPE1H: {
        label: "MRMS One-Hour Precipitation",
        shortLabel: "QPE 1h",
        product: "QPE1H",
        units: "in",
        nativeUnits: "mm",
        isDifference: false
      },
      QPE1H_DIFF_30M: {
        label: "MRMS One-Hour QPE Δ 30 min",
        shortLabel: "QPE 1h Δ30m",
        product: "QPE1H",
        units: "in",
        nativeUnits: "mm",
        isDifference: true,
        isQpeDifference: true
      },
      QPE30M: {
        label: "MRMS Past 30-Minute Precipitation",
        shortLabel: "QPE 30m",
        product: "QPE15M",
        units: "in",
        nativeUnits: "mm",
        isDifference: false
      },
      QPE6H: {
        label: "MRMS Six-Hour Precipitation",
        shortLabel: "QPE 6h",
        product: "QPE6H",
        units: "in",
        nativeUnits: "mm",
        isDifference: false
      },
      RALA: {
        label: "MRMS Reflectivity At Lowest Altitude (RALA)",
        shortLabel: "RALA",
        product: "RALA",
        units: "dBZ",
        nativeUnits: "dBZ",
        isDifference: false
      },
      REFLQC: {
        label: "MRMS Merged Reflectivity QC Mosaic",
        shortLabel: "Refl QC",
        product: "REFLQC",
        units: "dBZ",
        nativeUnits: "dBZ",
        isDifference: false
      },
      REFLCOMP: {
        label: "MRMS Composite Reflectivity QC",
        shortLabel: "Comp Refl",
        product: "REFLCOMP",
        units: "dBZ",
        nativeUnits: "dBZ",
        isDifference: false
      },
      REFL10C: {
        label: "MRMS Reflectivity at -10°C",
        shortLabel: "Refl -10°C",
        product: "REFL10C",
        units: "dBZ",
        nativeUnits: "dBZ",
        isDifference: false
      },
      CREST_DIFF_10M: {
        label: "CREST Δ 10 min",
        shortLabel: "CREST Δ10m",
        product: "CREST",
        units: "cfs/mi²",
        isDifference: true
      },
      HP_MINUS_CREST: {
        label: "HP − CREST Difference",
        shortLabel: "HP−CREST",
        product: "HP",
        units: "cfs/mi²",
        isDifference: true
      }
    };

    const panels = {};
    const PANEL_KEYS = ["left", "right", "lowerLeft", "lowerRight"];
    const PANEL_LABELS = {
      left: "PANEL 1",
      right: "PANEL 2",
      lowerLeft: "PANEL 3",
      lowerRight: "PANEL 4"
    };
    let mapSyncLock = false;
    let autoRenderTimer = null;
    let timelineTimer = null;
    let alertRefreshTimer = null;
    let alertFetchSerial = 0;
    let alertCacheKey = "";
    let alertCacheData = null;
    let suppressAutoRenderUntil = 0;
    let isLooping = false;
    let loopTimer = null;
    let loopFrames = [];
    let loopIndex = 0;
    let loopBaseBounds = null;
    let areaAvgEnabled = false;
    let areaAvgDrawing = null;
    let areaAvgVertices = [];
    let areaAvgSourcePanelKey = null;
    let areaAvgSerial = 0;
    let areaAvgPulseTimer = null;
    let areaAvgPulseStart = 0;
    let liveLatestToken = "";
    let liveLatestLabel = "";

    const censusBase = "https://tigerweb.geo.census.gov/arcgis/rest/services/TIGERweb/State_County/MapServer";

    function savedParam(key, fallback) {
      const value = window.localStorage.getItem(`mrms.viewer.${key}Param`);
      if (value && parameterInfo[value]) {
        return value;
      }
      return fallback;
    }

    function savedSidebarCollapsed() {
      return window.localStorage.getItem("mrms.viewer.sidebarCollapsed") === "1";
    }

    function savedLayoutCount() {
      const raw = window.localStorage.getItem("mrms.viewer.panelLayout");
      const n = Number(raw || "2");
      return [1, 2, 4].includes(n) ? n : 2;
    }

    function selectedLayoutCount() {
      const el = document.getElementById("panelLayout");
      const n = Number((el && el.value) || savedLayoutCount() || 2);
      return [1, 2, 4].includes(n) ? n : 2;
    }

    function savedFastRenderEnabled() {
      const raw = window.localStorage.getItem("mrms.viewer.fastRender");
      return raw === null ? true : raw === "1";
    }

    function fastRenderEnabled() {
      const el = document.getElementById("fastRender");
      return !el || !!el.checked;
    }

    function fastRenderChanged() {
      window.localStorage.setItem("mrms.viewer.fastRender", fastRenderEnabled() ? "1" : "0");
      forEachPanel(function (key, panel) { panel.lastRenderKey = ""; });
      refreshAllLayers(true);
    }

    function activePanelKeys() {
      return PANEL_KEYS.slice(0, selectedLayoutCount());
    }

    function forEachPanel(callback) {
      for (const key of PANEL_KEYS) {
        if (panels[key]) callback(key, panels[key]);
      }
    }

    function forEachActivePanel(callback) {
      for (const key of activePanelKeys()) {
        if (panels[key]) callback(key, panels[key]);
      }
    }

    function invalidateAllPanelSizes() {
      forEachPanel(function (key, panel) {
        try { panel.map.invalidateSize(); } catch (e) {}
      });
    }

    function selectedArchiveProduct() {
      const keys = activePanelKeys();
      const firstParam = selectedParam(keys[0] || "left");
      return rawProductForParam(firstParam || "CREST") || "CREST";
    }

    function setSidebarCollapsed(collapsed, persist=true) {
      document.body.classList.toggle("sidebar-collapsed", !!collapsed);

      const btn = document.getElementById("sidebarToggle");
      if (btn) {
        btn.innerHTML = collapsed ? "&#187;" : "&#171;";
        btn.title = collapsed ? "Expand controls" : "Collapse controls";
      }

      if (persist) {
        window.localStorage.setItem("mrms.viewer.sidebarCollapsed", collapsed ? "1" : "0");
      }

      setTimeout(function () {
        invalidateAllPanelSizes();
      }, 220);
    }

    function toggleSidebar() {
      setSidebarCollapsed(!document.body.classList.contains("sidebar-collapsed"));
    }

    function updateLiveIndicator() {
      const mode = document.getElementById("timeMode").value;
      const offset = Number(document.getElementById("timeOffset").value);
      const indicator = document.getElementById("modeIndicator");
      const modeText = document.getElementById("modeText");
      const timeText = document.getElementById("modeTimeText");
      const readout = document.getElementById("validTimeReadout");
      const liveBtn = document.getElementById("liveButton");
      const archiveBtn = document.getElementById("archiveButton");

      if (!indicator || !modeText || !timeText || !readout) return;

      const token = selectedEffectiveToken() || liveLatestToken || currentRoundedToken();
      const label = token ? tokenToIsoZ(token) : "No valid Z time selected";

      indicator.classList.remove("mode-live", "mode-archive");
      liveBtn && liveBtn.classList.remove("timeButtonActive");
      archiveBtn && archiveBtn.classList.remove("timeButtonActive");

      if (mode === "latest" && offset === 0) {
        indicator.classList.add("mode-live");
        modeText.textContent = "LIVE";
        timeText.textContent = label;
        readout.innerHTML = `Valid: <b>${label}</b>`;
        liveBtn && liveBtn.classList.add("timeButtonActive");
      } else if (mode === "latest") {
        indicator.classList.add("mode-live");
        modeText.textContent = "LIVE OFFSET";
        timeText.textContent = label;
        readout.innerHTML = `Valid: <b>${label}</b> from live anchor ${tokenToIsoZ(liveLatestToken || currentRoundedToken())}`;
        liveBtn && liveBtn.classList.add("timeButtonActive");
      } else {
        indicator.classList.add("mode-archive");
        modeText.textContent = "ARCHIVE";
        timeText.textContent = label;
        readout.innerHTML = `Archive valid: <b>${label}</b>`;
        archiveBtn && archiveBtn.classList.add("timeButtonActive");
      }
    }

    async function updateLiveLatestToken(silent=false) {
      try {
        const product = selectedArchiveProduct();
        const resp = await fetch(`/api/archive/list?product=${encodeURIComponent(product)}&cacheBust=${Date.now()}`);
        const data = await resp.json();
        if (resp.ok && data.times && data.times.length > 0) {
          liveLatestToken = data.times[0].token || "";
          liveLatestLabel = data.times[0].label || "";
          updateTimelineLabel();
          updateLiveIndicator();
          return liveLatestToken;
        }
      } catch (err) {
        if (!silent) {
          document.getElementById("status").innerHTML = `LIVE latest lookup failed: ${err}`;
        }
      }
      updateTimelineLabel();
      updateLiveIndicator();
      return liveLatestToken;
    }

    async function goLive() {
      document.getElementById("timeMode").value = "latest";
      document.getElementById("timeOffset").value = 0;
      await updateLiveLatestToken(false);
      updateTimelineControls();
      refreshAllLayers(true);
    }

    function goArchiveMode() {
      document.getElementById("timeMode").value = "archive";
      const list = document.getElementById("archiveList");
      if (!list.value && list.options.length > 0 && list.options[0].value) {
        list.value = list.options[0].value;
      }
      updateTimelineControls();
      refreshAllLayers(true);
    }

    function makeMap(divId) {
      const m = L.map(divId, {
        preferCanvas: true,
        zoomControl: true
      }).setView(domains[DEFAULT_VIEW_DOMAIN].center, domains[DEFAULT_VIEW_DOMAIN].zoom);

      L.tileLayer("https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png", {
        maxZoom: 15,
        attribution: "© OpenStreetMap © CARTO"
      }).addTo(m);

      return m;
    }

    function addBoundaryLayers(panel) {
      panel.countiesLayer = L.esri.featureLayer({
        url: censusBase + "/1",
        simplifyFactor: 0.4,
        precision: 5,
        style: function () {
          return {
            color: "#a8a8a8",
            weight: 0.7,
            opacity: 0.75,
            fillOpacity: 0
          };
        }
      }).addTo(panel.map);

      panel.statesLayer = L.esri.featureLayer({
        url: censusBase + "/0",
        simplifyFactor: 0.4,
        precision: 5,
        style: function () {
          return {
            color: "#ffffff",
            weight: 1.8,
            opacity: 0.95,
            fillOpacity: 0
          };
        }
      }).addTo(panel.map);

      panel.marineZonesLayer = L.esri.featureLayer({
        url: "https://services9-nocdn.arcgis.com/RHVPKKiFTONKtxq3/ArcGIS/rest/services/NWS_Watches_Warnings_v1/FeatureServer/5",
        simplifyFactor: 0.4,
        precision: 5,
        style: function () {
          return {
            color: "#ffff00",
            weight: 1.3,
            opacity: 0.90,
            fillOpacity: 0
          };
        }
      }).addTo(panel.map);
    }

    function initPanel(key, divId, titleId, defaultParam) {
      const panel = {
        key: key,
        map: makeMap(divId),
        titleEl: document.getElementById(titleId),
        legendBarEl: document.getElementById(`${key}LegendBar`),
        legendTicksEl: document.getElementById(`${key}LegendTicks`),
        streamflowOverlay: null,
        loopOverlay: null,
        alertsGroup: L.layerGroup(),
        maxMarkerGroup: L.layerGroup(),
        areaAvgGroup: L.layerGroup(),
        areaAvgPopup: null,
        clickReadoutGroup: L.layerGroup(),
        clickReadoutPopup: null,
        clickReadoutSerial: 0,
        hoverTooltip: null,
        hoverTimer: null,
        hoverRequestSerial: 0,
        renderRequestSerial: 0,
        alertsRequestSerial: 0,
        maxRequestSerial: 0
      };

      addBoundaryLayers(panel);
      panels[key] = panel;

      panel.map.on("moveend", function () {
        syncMapsFrom(key);
      });

      panel.map.on("zoomend", function () {
        syncMapsFrom(key);
      });

      panel.map.on("click", function (e) {
        handleMapClick(key, e);
      });

      panel.map.on("dblclick", function (e) {
        handleAreaAverageDoubleClick(key, e);
      });

      panel.map.on("mousemove", function (e) {
        handleAreaAverageMouseMove(key, e);
        handleHoverMove(key, e);
      });

      panel.map.on("mouseout", function () {
        clearHoverReadout(key);
      });

      panel.map.on("mousedown", function (e) {
        handleAreaAverageMouseDown(key, e);
      });

      panel.map.on("mouseup", function (e) {
        handleAreaAverageMouseUp(key, e);
      });

      return panel;
    }

    function selectedParam(panelKey) {
      return document.getElementById(`${panelKey}Param`).value;
    }

    function selectedParamInfo(panelKey) {
      return parameterInfo[selectedParam(panelKey)] || parameterInfo.CREST;
    }

    function rawProductForParam(param) {
      return (parameterInfo[param] || parameterInfo.CREST).product;
    }

    function panelParamChanged(panelKey) {
      const param = selectedParam(panelKey);
      window.localStorage.setItem(`mrms.viewer.${panelKey}Param`, param);
      updatePanelTitles();
      if (isLooping) {
        stopLoop(false);
      }
      if (activePanelKeys().includes(panelKey)) {
        updateLiveLatestToken(true);
        refreshPanelLayer(panelKey, true);
      }
    }

    function applyLayout(refresh=true) {
      const count = selectedLayoutCount();
      const grid = document.getElementById("mapGrid");
      grid.classList.remove("layout-1", "layout-2", "layout-4");
      grid.classList.add(`layout-${count}`);
      window.localStorage.setItem("mrms.viewer.panelLayout", String(count));

      for (const key of PANEL_KEYS) {
        const row = document.getElementById(`panelControl-${key}`);
        if (row) row.classList.toggle("hiddenPanelControl", !activePanelKeys().includes(key));
      }

      updatePanelTitles();
      setTimeout(function () {
        invalidateAllPanelSizes();
        bringAllBoundariesToFront();
      }, 120);

      if (refresh) {
        if (isLooping) stopLoop(false);
        if (!isLooping) refreshAllLayers(true);
      }
    }

    function layoutChanged() {
      applyLayout(true);
    }

    const STREAMFLOW_LEGEND_MAX = 2000.0;
    const STREAMFLOW_LEGEND_STOPS = [
      {value: 0.0, color: "#000000"},
      {value: 100.0, color: "#fefefe"},
      {value: 100.0, color: "#fefe00"},
      {value: 200.0, color: "#999900"},
      {value: 200.0, color: "#ff6346"},
      {value: 400.0, color: "#ffa500"},
      {value: 400.0, color: "#f08080"},
      {value: 600.0, color: "#800000"},
      {value: 600.0, color: "#800080"},
      {value: 1000.0, color: "#fe00fe"},
      {value: 1000.0, color: "#0000ff"},
      {value: 2000.0, color: "#000080"}
    ];

    function pctFromLegendValue(value, maxValue) {
      const pct = Math.max(0, Math.min(100, (Number(value) / Number(maxValue)) * 100));
      return `${Number(pct.toFixed(4))}%`;
    }

    function gradientFromValueStops(stops, maxValue) {
      return "linear-gradient(to right, " + stops.map(function (stop) {
        return `${stop.color} ${pctFromLegendValue(stop.value, maxValue)}`;
      }).join(", ") + ")";
    }

    function legendSpecForParamInfo(p) {
      if (p.isQpeDifference) {
        return {
          background: "linear-gradient(to right, #000000 0%, #00ffff 25%, #0096ff 39%, #0033ff 47%, #000000 50%, #ff0000 53%, #ff4bff 61%, #ff00ff 75%, #000000 100%)",
          ticks: [
            {left:"0%", text:"−4"},
            {left:"25%", text:"−2"},
            {left:"50%", text:"0"},
            {left:"75%", text:"+2"},
            {left:"100%", text:"+4"}
          ]
        };
      }
      if (p.isDifference) {
        return {
          background: "linear-gradient(to right, #000000 0%, #00ffff 25%, #0096ff 39%, #0033ff 47%, #000000 50%, #ff0000 53%, #ff4bff 61%, #ff00ff 75%, #000000 100%)",
          ticks: [
            {left:"2%", text:"−200"},
            {left:"50%", text:"0"},
            {left:"98%", text:"+200"}
          ]
        };
      }
      if ((p.units || "") === "in/hr") {
        return {
          background: "linear-gradient(to right, #000000 0%, #202020 0.08%, #d0d0d0 8.25%, #0515ff 8.33%, #1bf0ff 16.67%, #47e987 25%, #f88cf8 33.33%, #ffd703 41.67%, #ff9302 50%, #ff0101 66.67%, #ffc0c0 83.33%, #ffffff 100%)",
          ticks: [
            {left:"0%", text:"0"},
            {left:"8.33%", text:"1"},
            {left:"16.67%", text:"2"},
            {left:"25%", text:"3"},
            {left:"33.33%", text:"4"},
            {left:"41.67%", text:"5"},
            {left:"50%", text:"6"},
            {left:"66.67%", text:"8"},
            {left:"100%", text:"12"}
          ]
        };
      }
      if ((p.units || "").includes("dBZ")) {
        return {
          background: "linear-gradient(to right, #080608 0%, #16041d 4.5%, #2a0536 9.1%, #3c0c4c 13.6%, #3a2441 18.2%, #474747 22.7%, #828788 27.3%, #a8acb0 31.8%, #3f5c93 36.4%, #5ba5c0 40.9%, #2cbc54 45.5%, #0fa20f 50%, #107b0c 54.5%, #497e03 59.1%, #e3ca05 63.6%, #e09f04 68.2%, #e50402 72.7%, #b50301 77.3%, #b14a68 81.8%, #e506e5 86.4%, #9677e3 90.9%, #4706e4 95.5%, #0103e3 100%)",
          ticks: [
            {left:"0%", text:"-30"},
            {left:"18%", text:"-10"},
            {left:"27%", text:"0"},
            {left:"45%", text:"20"},
            {left:"64%", text:"40"},
            {left:"82%", text:"60"},
            {left:"100%", text:"80"}
          ]
        };
      }
      if ((p.units || "").includes("in")) {
        return {
          background: "linear-gradient(to right, #000000 0%, #04e9e7 1%, #019ff4 6%, #0300f4 14%, #02fd02 25%, #01c501 38%, #008e00 50%, #fdf802 63%, #e5bc00 75%, #fd9500 82%, #fd0000 88%, #d40000 94%, #f800fd 98%, #fdfdfd 100%)",
          ticks: [
            {left:"6%", text:"0.1"},
            {left:"25%", text:"0.5"},
            {left:"50%", text:"1"},
            {left:"75%", text:"2"},
            {left:"88%", text:"4"},
            {left:"98%", text:"10"},
            {left:"100%", text:"16"}
          ]
        };
      }
      return {
        background: gradientFromValueStops(STREAMFLOW_LEGEND_STOPS, STREAMFLOW_LEGEND_MAX),
        ticks: [
          {left:"0%", text:"0"},
          {left:"10%", text:"200"},
          {left:"20%", text:"400"},
          {left:"30%", text:"600"},
          {left:"50%", text:"1000"},
          {left:"100%", text:"2000"}
        ]
      };
    }

    function setPanelLegend(panelKey, spec) {
      const panel = panels[panelKey];
      if (!panel || !panel.legendBarEl || !panel.legendTicksEl) return;
      panel.legendBarEl.style.background = spec.background;
      panel.legendTicksEl.innerHTML = "";
      for (const tick of spec.ticks) {
        const div = document.createElement("div");
        div.className = "panelTick";
        div.style.left = tick.left;
        div.textContent = tick.text;
        panel.legendTicksEl.appendChild(div);
      }
    }

    function updateAllPanelLegends() {
      forEachPanel(function (key) {
        const p = selectedParamInfo(key);
        setPanelLegend(key, legendSpecForParamInfo(p));
      });
    }

    function updatePanelTitles() {
      forEachPanel(function (key, panel) {
        const p = selectedParamInfo(key);
        panel.titleEl.innerHTML = `${PANEL_LABELS[key]}<br>${p.shortLabel}`;
      });
      updateAllPanelLegends();
    }

    function utcNowText() {
      return new Date().toISOString().replace(".000Z", "Z");
    }

    function selectedDomain() {
      return DEFAULT_VIEW_DOMAIN;
    }

    function primaryMap() {
      return panels.left.map;
    }

    function getDomainBounds(useCurrentMapView, panelKey) {
      const m = panelKey ? panels[panelKey].map : primaryMap();

      if (useCurrentMapView) {
        const b = m.getBounds();
        return {
          west: b.getWest(),
          south: b.getSouth(),
          east: b.getEast(),
          north: b.getNorth(),
          center: m.getCenter(),
          zoom: m.getZoom()
        };
      }

      return domains[selectedDomain()];
    }

    function getRenderWidth(panelKey) {
      const size = panels[panelKey].map.getSize();
      const layout = selectedLayoutCount();
      const fast = fastRenderEnabled();
      const dpr = fast ? Math.min(window.devicePixelRatio || 1, 1.0) : (window.devicePixelRatio || 1);
      const cap = fast
        ? (layout === 4 ? 820 : (layout === 2 ? 1050 : 1350))
        : (layout === 4 ? 1150 : (layout === 2 ? 1400 : 1700));
      const floor = fast ? 420 : 520;
      return Math.min(cap, Math.max(floor, Math.round(size.x * dpr)));
    }

    function bringPanelBoundariesToFront(panelKey) {
      const panel = panels[panelKey];
      try { panel.countiesLayer.bringToFront(); } catch (e) {}
      try { panel.statesLayer.bringToFront(); } catch (e) {}
      try { panel.marineZonesLayer.bringToFront(); } catch (e) {}
      try { panel.alertsGroup.bringToFront(); } catch (e) {}
      try { panel.maxMarkerGroup.bringToFront(); } catch (e) {}
    }

    function bringAllBoundariesToFront() {
      forEachActivePanel(function (key) {
        bringPanelBoundariesToFront(key);
      });
    }

    function clearPanelAlerts(panelKey) {
      const panel = panels[panelKey];
      panel.alertsRequestSerial += 1;
      try {
        panel.alertsGroup.clearLayers();
        if (panel.map.hasLayer(panel.alertsGroup)) {
          panel.map.removeLayer(panel.alertsGroup);
        }
      } catch (e) {}
    }

    function clearPanelMaxMarker(panelKey) {
      const panel = panels[panelKey];
      panel.maxRequestSerial += 1;
      try {
        panel.maxMarkerGroup.clearLayers();
        if (panel.map.hasLayer(panel.maxMarkerGroup)) {
          panel.map.removeLayer(panel.maxMarkerGroup);
        }
      } catch (e) {}
    }

    function formatValue(value, signed=false) {
      if (value === null || value === undefined || !Number.isFinite(Number(value))) {
        return "";
      }

      const n = Math.round(Number(value));
      const prefix = signed && n > 0 ? "+" : "";
      return `${prefix}${n.toLocaleString()}`;
    }

    function signedValueHtml(value, units="cfs/mi²") {
      const n = Number(value);
      const sign = n > 0 ? "+" : "";
      const digits = String(units || "").includes("in") ? 2 : 0;
      return `<b>${sign}${n.toLocaleString(undefined, {minimumFractionDigits: digits, maximumFractionDigits: digits})} ${units}</b>`;
    }

    function parseUtcInputToToken(value) {
      if (!value) return "";
      let s = String(value).trim().toUpperCase();
      s = s.replace(/UTC/g, "Z").replace(/\s+/g, " ").replace(/Z$/, "");

      let m = s.match(/^(\d{8})[-_ ]?(\d{2})(\d{2})(\d{2})?$/);
      if (m) {
        return `${m[1]}-${m[2]}${m[3]}${m[4] || "00"}`;
      }

      m = s.match(/^(\d{4})-(\d{2})-(\d{2})[ T](\d{2}):?(\d{2})(?::?(\d{2}))?$/);
      if (m) {
        return `${m[1]}${m[2]}${m[3]}-${m[4]}${m[5]}${m[6] || "00"}`;
      }

      return "";
    }

    function selectedBaseArchiveToken() {
      const listValue = document.getElementById("archiveList").value;
      if (listValue) {
        return listValue;
      }

      return parseUtcInputToToken(document.getElementById("archiveTime").value);
    }

    function currentRoundedToken() {
      const now = new Date();
      const rounded = new Date(Math.floor(now.getTime() / (10 * 60 * 1000)) * (10 * 60 * 1000));

      const yyyy = rounded.getUTCFullYear().toString().padStart(4, "0");
      const mm = (rounded.getUTCMonth() + 1).toString().padStart(2, "0");
      const dd = rounded.getUTCDate().toString().padStart(2, "0");
      const hh = rounded.getUTCHours().toString().padStart(2, "0");
      const mi = rounded.getUTCMinutes().toString().padStart(2, "0");

      return `${yyyy}${mm}${dd}-${hh}${mi}00`;
    }

    function tokenToDate(token) {
      if (!token || !/^\d{8}-\d{6}$/.test(token)) {
        return null;
      }

      const y = Number(token.slice(0, 4));
      const m = Number(token.slice(4, 6)) - 1;
      const d = Number(token.slice(6, 8));
      const h = Number(token.slice(9, 11));
      const mi = Number(token.slice(11, 13));
      const s = Number(token.slice(13, 15));

      return new Date(Date.UTC(y, m, d, h, mi, s));
    }

    function dateToToken(d) {
      const yyyy = d.getUTCFullYear().toString().padStart(4, "0");
      const mm = (d.getUTCMonth() + 1).toString().padStart(2, "0");
      const dd = d.getUTCDate().toString().padStart(2, "0");
      const hh = d.getUTCHours().toString().padStart(2, "0");
      const mi = d.getUTCMinutes().toString().padStart(2, "0");
      const ss = d.getUTCSeconds().toString().padStart(2, "0");

      return `${yyyy}${mm}${dd}-${hh}${mi}${ss}`;
    }

    function addMinutesToToken(token, minutes) {
      const d = tokenToDate(token);
      if (!d) {
        return "";
      }

      return dateToToken(new Date(d.getTime() + minutes * 60 * 1000));
    }

    function tokenToIsoZ(token) {
      const d = tokenToDate(token);
      if (!d) {
        return "";
      }

      return d.toISOString().replace(".000Z", "Z");
    }

    function selectedEffectiveToken() {
      const mode = document.getElementById("timeMode").value;
      const offset = Number(document.getElementById("timeOffset").value);

      if (mode === "latest") {
        const liveToken = liveLatestToken || currentRoundedToken();
        if (offset === 0) {
          return liveLatestToken || "";
        }

        return addMinutesToToken(liveToken, offset);
      }

      const baseToken = selectedBaseArchiveToken();
      if (!baseToken) {
        return "";
      }

      return addMinutesToToken(baseToken, offset);
    }

    function selectedTimeLabel() {
      const mode = document.getElementById("timeMode").value;
      const offset = Number(document.getElementById("timeOffset").value);
      const token = selectedEffectiveToken();

      if (mode === "latest" && offset === 0) {
        return `LIVE ${tokenToIsoZ(liveLatestToken || currentRoundedToken())}`;
      }

      if (token) {
        return tokenToIsoZ(token);
      }

      return "No valid Z time selected";
    }

    function selectedTimeStepMinutes() {
      const key = activePanelKeys()[0] || "left";
      const product = rawProductForParam(selectedParam(key));
      if (["RALA", "REFLQC", "REFLCOMP", "REFL10C", "PRECIPRATE"].includes(product)) return 2;
      if (product === "QPE15M") return 15;
      if (product === "QPE6H") return 60;
      return 10;
    }

    function updateTimelineControls() {
      const mode = document.getElementById("timeMode").value;
      const slider = document.getElementById("timeOffset");
      slider.step = selectedTimeStepMinutes();

      if (mode === "archive") {
        slider.min = -ARCHIVE_LOOKBACK_MINUTES;
        slider.max = ARCHIVE_LOOKAHEAD_MINUTES;
      } else {
        slider.min = -ARCHIVE_LOOKBACK_MINUTES;
        slider.max = 0;
        if (Number(slider.value) > 0) {
          slider.value = 0;
        }
      }

      updateTimelineLabel();
      updateLiveIndicator();
    }

    function updateTimelineLabel() {
      const mode = document.getElementById("timeMode").value;
      const offset = Number(document.getElementById("timeOffset").value);
      const label = document.getElementById("timeOffsetLabel");

      if (mode === "latest") {
        if (offset === 0) {
          label.textContent = `LIVE ${tokenToIsoZ(liveLatestToken || currentRoundedToken())}`;
        } else {
          label.textContent = `${offset} min → ${selectedTimeLabel()}`;
        }
      } else {
        const sign = offset > 0 ? "+" : "";
        label.textContent = `${sign}${offset} min → ${selectedTimeLabel()}`;
      }
    }

    function timelineChanged(immediate) {
      updateTimelineLabel();
      updateLiveIndicator();
      clearTimeout(timelineTimer);

      const delay = immediate ? 0 : 350;

      timelineTimer = setTimeout(function () {
        refreshAllLayers(true);
      }, delay);
    }

    function setDefaultArchiveInputUTC() {
      const now = new Date();
      const ms = now.getTime();
      const rounded = new Date(Math.floor(ms / (10 * 60 * 1000)) * (10 * 60 * 1000));

      const yyyy = rounded.getUTCFullYear().toString().padStart(4, "0");
      const mm = (rounded.getUTCMonth() + 1).toString().padStart(2, "0");
      const dd = rounded.getUTCDate().toString().padStart(2, "0");
      const hh = rounded.getUTCHours().toString().padStart(2, "0");
      const mi = rounded.getUTCMinutes().toString().padStart(2, "0");

      document.getElementById("archiveTime").value = `${yyyy}${mm}${dd}-${hh}${mi}00Z`;
    }

    function setOverlayOpacity() {
      const opacity = Number(document.getElementById("opacity").value) / 100.0;
      forEachPanel(function (key, panel) {
        const overlay = panel.streamflowOverlay;
        if (overlay) {
          overlay.setOpacity(opacity);
        }
        if (panel.loopOverlay) {
          panel.loopOverlay.setOpacity(opacity);
        }
      });
    }

    async function loadArchiveList() {
      const status = document.getElementById("status");
      const product = selectedArchiveProduct();
      status.innerHTML = `Loading recent MRMS archive list for ${product} for the last 24 hours...`;

      try {
        const resp = await fetch(`/api/archive/list?product=${encodeURIComponent(product)}&cacheBust=${Date.now()}`);
        const data = await resp.json();

        const sel = document.getElementById("archiveList");
        sel.innerHTML = "";

        if (!resp.ok) {
          const opt = document.createElement("option");
          opt.value = "";
          opt.textContent = "Archive list error";
          sel.appendChild(opt);
          status.innerHTML = `<b>Archive list error:</b> ${data.error || "unknown"}`;
          return;
        }

        if (!data.times || data.times.length === 0) {
          const opt = document.createElement("option");
          opt.value = "";
          opt.textContent = "No MRMS archive files found";
          sel.appendChild(opt);
          status.innerHTML = "No MRMS archive files found.";
          return;
        }

        for (const item of data.times) {
          const opt = document.createElement("option");
          opt.value = item.token;
          opt.textContent = item.label;
          sel.appendChild(opt);
        }

        if (data.times[0] && data.times[0].token) {
          liveLatestToken = data.times[0].token;
          liveLatestLabel = data.times[0].label || "";
          if (!document.getElementById("archiveTime").value) {
            document.getElementById("archiveTime").value = `${liveLatestToken}Z`;
          }
        }

        status.innerHTML = `Loaded ${data.times.length} recent MRMS archive times from the last 24 hours. All times UTC/Z.`;
        updateTimelineLabel();
        updateLiveIndicator();

      } catch (err) {
        document.getElementById("status").innerHTML = `Archive list failed: ${err}`;
      }
    }

    async function captureNow() {
      const status = document.getElementById("status");
      status.innerHTML = `Capturing latest CREST/SAC/HP into local archive...`;

      const products = Array.from(new Set(activePanelKeys().map(function (key) {
        return rawProductForParam(selectedParam(key));
      }).filter(Boolean)));
      const results = [];

      for (const product of products) {
        try {
          const resp = await fetch(`/api/archive/capture?product=${encodeURIComponent(product)}&cacheBust=${Date.now()}`);
          const data = await resp.json();
          if (!resp.ok) {
            results.push(`${product}: failed (${data.error || "unknown"})`);
          } else {
            results.push(`${product}: ${data.token}Z`);
          }
        } catch (err) {
          results.push(`${product}: failed (${err})`);
        }
      }

      status.innerHTML = `Capture complete:<br>${results.join("<br>")}`;
      await loadArchiveList();
    }

    function alertCategory(feature) {
      const p = feature.properties || {};
      const event = (p.event || "").toLowerCase();
      const tag = (p.flash_flood_tag || "").toLowerCase();
      const blob = Object.values(p).join(" ").toLowerCase();

      if (tag === "emergency" || blob.includes("flash flood emergency")) {
        return "emergency";
      }

      if (tag === "considerable" || (event.includes("flash flood warning") && blob.includes("considerable"))) {
        return "considerable";
      }

      if (event.includes("flood advisory")) {
        return "advisory";
      }

      return "ffw";
    }

    function alertStatusText(feature) {
      const p = feature.properties || {};
      const cat = alertCategory(feature);
      const event = (p.event || "").toLowerCase();

      if (cat === "emergency") {
        return "EMERGENCY";
      }

      if (cat === "considerable") {
        return "CONSIDERABLE";
      }

      if (event.includes("flood advisory")) {
        return "ADVISORY";
      }

      if (event.includes("flash flood warning")) {
        return "BASE";
      }

      return "";
    }

    function alertLabelText(feature) {
      const p = feature.properties || {};
      if (p.display_label) {
        return p.display_label;
      }
      const vtec = p.vtec_id || p.VTEC_ID || p.vtec || p.warning_number || "";
      const status = p.status_text || alertStatusText(feature);
      const productLabel = p.product_label || p.product_code || p.event || "Alert";
      const code = String(p.product_code || "").toUpperCase();

      const m = String(vtec).match(/\b(FF|FA)\.([A-Z])\.(\d{4})\b/);
      if (m) {
        let prefix = `${m[1]}.${m[2]}`;
        if (code === "FFS" || code === "FFW+FFS" || p.ffs_detected || prefix === "FF.W") {
          prefix = "FF.W";
        }
        return `${status ? status + " " : ""}${prefix} ${m[3]}`.trim();
      }

      return `${status ? status + " " : ""}${productLabel}`.trim();
    }

    function alertStyle(feature) {
      const p = feature.properties || {};
      const cat = alertCategory(feature);
      const code = p.product_code || "";

      if (cat === "emergency") {
        return { color: "#ff00ff", weight: 5.5, opacity: 1.0, fill: false, fillOpacity: 0.0 };
      }

      if (cat === "considerable") {
        return { color: "#006400", weight: (code === "FFS" || code === "FFW+FFS") ? 5.5 : 4.5, opacity: 1.0, fill: false, fillOpacity: 0.0 };
      }

      if (cat === "advisory") {
        return { color: "#90ee90", weight: 2.8, opacity: 1.0, fill: false, fillOpacity: 0.0 };
      }

      if (code === "FFS" || code === "FFW+FFS") {
        return { color: "#00ff00", weight: 4.2, opacity: 1.0, fill: false, fillOpacity: 0.0 };
      }

      return { color: "#00ff00", weight: 3.2, opacity: 1.0, fill: false, fillOpacity: 0.0 };
    }

    function zText(t) {
      if (!t) {
        return "";
      }

      const s = String(t);
      if (s.endsWith("Z") || s.includes("UTC")) {
        return s;
      }

      return `${s}Z`;
    }

    function onEachAlert(feature, layer) {
      const p = feature.properties || {};
      const event = p.event || "Alert";
      const headline = p.headline || p.name || event;
      const office = p.wfo || p.WFO || p.senderName || "";
      const issue = p.issue_utc || p.issue || p.ISSUE || p.sent || "";
      const expire = p.vtec_end_utc || p.expire || p.EXPIRE || p.expires || "";
      const vtec = p.vtec_id || p.VTEC_ID || p.vtec || p.warning_number || "";
      const productLabel = p.product_label || p.product_code || event;
      const displayLabel = alertLabelText(feature);
      const statusText = p.status_text || alertStatusText(feature);
      const cat = alertCategory(feature);

      let tag = "";
      if (cat === "emergency") {
        tag = "Flash Flood Emergency";
      } else if (cat === "considerable") {
        tag = "Considerable";
      } else if (statusText) {
        tag = statusText;
      }

      layer.on("add", function () {
        const code = p.product_code || "";
        const tag = p.flash_flood_tag || "";

        if (code === "FFS" || code === "FFW+FFS" || tag === "considerable" || tag === "emergency") {
          try { layer.bringToFront(); } catch (e) {}
        }
      });

      const showLabels = document.getElementById("showAlertLabels").checked;

      layer.bindTooltip(displayLabel, {
        permanent: showLabels,
        sticky: !showLabels,
        direction: showLabels ? "center" : "top",
        className: "alert-tooltip"
      });

      layer.bindPopup(
        `<b>${productLabel}</b>${tag ? " — <b>" + tag + "</b>" : ""}<br>` +
        `${displayLabel ? "Label: <b>" + displayLabel + "</b><br>" : ""}` +
        `${vtec ? "VTEC: <b>" + vtec + "</b><br>" : ""}` +
        `${headline}<br>` +
        `${office ? "Office: " + office + "<br>" : ""}` +
        `${issue ? "Issued/Statement: " + zText(issue) + "<br>" : ""}` +
        `${expire ? "VTEC End: " + zText(expire) + "<br>" : ""}` +
        `${p.ffs_detected ? "<b>Latest active FFS detected</b><br>" : ""}` +
        `<span style="font-size:11px;color:#555;">Valid-at-time outline layer</span>`
      );
    }

    function clearAllAlerts() {
      forEachPanel(function (key) {
        clearPanelAlerts(key);
      });
    }

    function buildAlertRequestKey() {
      const token = selectedEffectiveToken() || "latest";
      const b = primaryMap().getBounds();
      const deep = document.getElementById("deepAlertText").checked ? "1" : "0";
      return JSON.stringify({
        token: token,
        deep: deep,
        west: Math.round(b.getWest() * 20) / 20,
        south: Math.round(b.getSouth() * 20) / 20,
        east: Math.round(b.getEast() * 20) / 20,
        north: Math.round(b.getNorth() * 20) / 20
      });
    }

    function applyAlertGeoJsonToPanel(panelKey, data) {
      const panel = panels[panelKey];
      panel.alertsRequestSerial += 1;
      panel.alertsGroup.clearLayers();

      if (panel.map.hasLayer(panel.alertsGroup)) {
        panel.map.removeLayer(panel.alertsGroup);
      }

      if (!document.getElementById("showAlerts").checked || !data) {
        return;
      }

      panel.alertsGroup = L.layerGroup().addTo(panel.map);

      const layer = L.geoJSON(data, {
        style: alertStyle,
        onEachFeature: onEachAlert
      });

      panel.alertsGroup.addLayer(layer);
      bringPanelBoundariesToFront(panelKey);
    }

    function applyAlertGeoJsonToBothPanels(data) {
      forEachPanel(function (key) {
        if (activePanelKeys().includes(key)) {
          applyAlertGeoJsonToPanel(key, data);
        } else {
          clearPanelAlerts(key);
        }
      });
    }

    async function refreshAlertsNow() {
      clearTimeout(alertRefreshTimer);

      if (!document.getElementById("showAlerts").checked) {
        alertCacheKey = "";
        alertCacheData = null;
        clearAllAlerts();
        return;
      }

      const requestKey = buildAlertRequestKey();
      if (requestKey === alertCacheKey && alertCacheData) {
        applyAlertGeoJsonToBothPanels(alertCacheData);
        return;
      }

      const thisRequest = ++alertFetchSerial;
      const token = selectedEffectiveToken();
      const b = primaryMap().getBounds();
      const deep = document.getElementById("deepAlertText").checked ? "1" : "0";

      let url =
        `/api/alerts` +
        `?west=${b.getWest()}&south=${b.getSouth()}&east=${b.getEast()}&north=${b.getNorth()}` +
        `&deep=${deep}` +
        `&cacheBust=${Date.now()}`;

      if (token) {
        url += `&time=${encodeURIComponent(token)}`;
      }

      try {
        const resp = await fetch(url);
        const data = await resp.json();

        if (thisRequest !== alertFetchSerial) {
          return;
        }

        if (!document.getElementById("showAlerts").checked) {
          clearAllAlerts();
          return;
        }

        if (!resp.ok) {
          console.log("Alerts error", data);
          return;
        }

        alertCacheKey = requestKey;
        alertCacheData = data;
        applyAlertGeoJsonToBothPanels(data);

      } catch (err) {
        if (thisRequest === alertFetchSerial) {
          console.log("Alert refresh failed", err);
        }
      }
    }

    function refreshAllAlerts() {
      clearTimeout(alertRefreshTimer);
      alertRefreshTimer = setTimeout(refreshAlertsNow, 180);
    }

    async function refreshPanelMaxMarker(panelKey) {
      const panel = panels[panelKey];
      const thisRequest = ++panel.maxRequestSerial;

      panel.maxMarkerGroup.clearLayers();

      if (panel.map.hasLayer(panel.maxMarkerGroup)) {
        panel.map.removeLayer(panel.maxMarkerGroup);
      }

      const showMaxEl = document.getElementById("showMaxPixel");
      const show = !!(showMaxEl && showMaxEl.checked);

      if (!show) {
        return;
      }

      panel.maxMarkerGroup = L.layerGroup().addTo(panel.map);

      const param = selectedParam(panelKey);
      const product = rawProductForParam(param);
      const token = selectedEffectiveToken();
      const b = panel.map.getBounds();
      const width = getRenderWidth(panelKey);

      let url =
        `/api/max` +
        `?param=${encodeURIComponent(param)}` +
        `&product=${encodeURIComponent(product)}` +
        `&west=${b.getWest()}&south=${b.getSouth()}&east=${b.getEast()}&north=${b.getNorth()}` +
        `&width=${width}` +
        `&cacheBust=${Date.now()}`;

      if (token) {
        url += `&time=${encodeURIComponent(token)}`;
      }

      try {
        const resp = await fetch(url);
        const data = await resp.json();

        if (thisRequest !== panel.maxRequestSerial) {
          return;
        }

        const showMaxElAfterFetch = document.getElementById("showMaxPixel");
        if (!(showMaxElAfterFetch && showMaxElAfterFetch.checked)) {
          clearPanelMaxMarker(panelKey);
          return;
        }

        if (!resp.ok || !data.found) {
          return;
        }

        const info = parameterInfo[param] || parameterInfo.CREST;
        const latlng = [data.lat, data.lon];
        const signed = !!info.isDifference;
        const units = data.display_units || info.units;
        const maxDv = data.display_value ?? data.value_cfs_per_smi;
        const maxDigits = String(units || "").includes("in") ? 2 : (String(units || "").includes("dBZ") ? 1 : 0);
        const maxSign = signed && Number(maxDv) > 0 ? "+" : "";
        const valueText = `${maxSign}${Number(maxDv).toLocaleString(undefined, {minimumFractionDigits: maxDigits, maximumFractionDigits: maxDigits})} ${units}`;
        const labelPrefix = signed ? "EXTREME" : "MAX";

        const circleOuter = L.circleMarker(latlng, {
          radius: 16,
          color: "#ffffff",
          weight: 4,
          opacity: 1.0,
          fill: false,
          interactive: true
        });

        const circleInner = L.circleMarker(latlng, {
          radius: 8,
          color: "#000000",
          weight: 2,
          opacity: 1.0,
          fill: false,
          interactive: true
        });

        const popupHtml =
          `<b>${info.label} ${signed ? "largest difference" : "max in current view"}</b><br>` +
          `<b>${valueText}</b><br>` +
          `${data.native_value !== null && data.native_value !== undefined ? Number(data.native_value).toFixed(2) + " " + (data.native_units || info.nativeUnits || "") + "<br>" : ""}` +
          `Lat/Lon: ${data.lat.toFixed(4)}, ${data.lon.toFixed(4)}<br>` +
          `<span style="font-size:11px;color:#555;">Valid: ${data.file_time_utc || selectedTimeLabel()}</span>`;

        circleOuter.bindTooltip(`${labelPrefix} ${valueText}`, {
          permanent: true,
          direction: "top",
          offset: [0, -12],
          className: "max-tooltip"
        });

        circleOuter.bindPopup(popupHtml);
        circleInner.bindPopup(popupHtml);

        panel.maxMarkerGroup.addLayer(circleOuter);
        panel.maxMarkerGroup.addLayer(circleInner);
        bringPanelBoundariesToFront(panelKey);

      } catch (err) {
        if (thisRequest === panel.maxRequestSerial) {
          console.log("Max marker refresh failed", err);
        }
      }
    }

    function refreshAllMaxMarkers() {
      forEachPanel(function (key) {
        if (activePanelKeys().includes(key)) {
          refreshPanelMaxMarker(key);
        } else {
          clearPanelMaxMarker(key);
        }
      });
    }

    function refreshPanelLayer(panelKey, useCurrentMapView) {
      const panel = panels[panelKey];
      const thisRenderRequest = ++panel.renderRequestSerial;
      const param = selectedParam(panelKey);
      const product = rawProductForParam(param);
      const info = parameterInfo[param] || parameterInfo.CREST;
      const d = getDomainBounds(useCurrentMapView, panelKey);
      const opacity = Number(document.getElementById("opacity").value) / 100.0;
      const token = selectedEffectiveToken();
      const width = getRenderWidth(panelKey);
      const renderKey = JSON.stringify({
        param: param,
        product: product,
        token: token || "",
        west: Number(d.west).toFixed(5),
        south: Number(d.south).toFixed(5),
        east: Number(d.east).toFixed(5),
        north: Number(d.north).toFixed(5),
        width: width
      });

      if (panel.lastRenderKey === renderKey && panel.streamflowOverlay) {
        document.getElementById("status").innerHTML =
          `<b>${info.label}</b> already current<br>` +
          `Valid: ${selectedTimeLabel()}<br>` +
          `No re-render needed.`;
        bringPanelBoundariesToFront(panelKey);
        return;
      }

      let url =
        `/api/render.png?param=${encodeURIComponent(param)}` +
        `&product=${encodeURIComponent(product)}` +
        `&west=${d.west}&south=${d.south}&east=${d.east}&north=${d.north}` +
        `&width=${width}` +
        `&cacheBust=${Date.now()}`;

      if (token) {
        url += `&time=${encodeURIComponent(token)}`;
      }

      const bounds = [
        [d.south, d.west],
        [d.north, d.east]
      ];

      const previousOverlay = panel.streamflowOverlay;

      document.getElementById("status").innerHTML =
        `Rendering ${info.label} ${selectedTimeLabel()}...<br>` +
        `Panel: ${panelKey.toUpperCase()} | Width: ${width}px`;

      const nextOverlay = L.imageOverlay(url, bounds, {
        opacity: opacity,
        interactive: false
      });

      nextOverlay.on("load", function () {
        if (thisRenderRequest !== panel.renderRequestSerial) {
          try { panel.map.removeLayer(nextOverlay); } catch (e) {}
          return;
        }

        if (previousOverlay && previousOverlay !== nextOverlay && panel.map.hasLayer(previousOverlay)) {
          panel.map.removeLayer(previousOverlay);
        }

        panel.streamflowOverlay = nextOverlay;
        panel.lastRenderKey = renderKey;

        document.getElementById("status").innerHTML =
          `<b>${info.label}</b> loaded<br>` +
          `Valid: ${selectedTimeLabel()}<br>` +
          `Rendered: ${utcNowText()}<br>` +
          `Click any panel for all visible panel values.`;

        bringPanelBoundariesToFront(panelKey);
        refreshAllAlerts();
        refreshPanelMaxMarker(panelKey);
      });

      nextOverlay.on("error", function () {
        if (thisRenderRequest !== panel.renderRequestSerial) {
          return;
        }
        try {
          const el = nextOverlay.getElement && nextOverlay.getElement();
          if (el) el.style.display = "none";
          if (panel.map.hasLayer(nextOverlay)) panel.map.removeLayer(nextOverlay);
        } catch (e) {}

        document.getElementById("status").innerHTML =
          `<b>Error loading ${info.label}</b><br>` +
          `Check the terminal output for details. Previous panel layer was left in place if available.`;
      });

      nextOverlay.addTo(panel.map);

      if (!useCurrentMapView) {
        suppressAutoRenderUntil = Date.now() + 1200;
        mapSyncLock = true;
        forEachActivePanel(function (key, panel) {
          panel.map.setView(d.center, d.zoom, { animate: false });
        });
        setTimeout(function () { mapSyncLock = false; }, 0);
      }

      bringPanelBoundariesToFront(panelKey);
    }

    function refreshAllLayers(useCurrentMapView) {
      if (isLooping) {
        stopLoop(false);
      }
      forEachPanel(function (key) {
        if (activePanelKeys().includes(key)) {
          refreshPanelLayer(key, useCurrentMapView);
        } else {
          clearPanelMaxMarker(key);
          clearPanelAlerts(key);
        }
      });
    }

    function scheduleAutoRender() {
      if (!document.getElementById("autoRender").checked) {
        refreshAllAlerts();
        refreshAllMaxMarkers();
          return;
      }

      if (Date.now() < suppressAutoRenderUntil) {
        refreshAllAlerts();
        refreshAllMaxMarkers();
          return;
      }

      clearTimeout(autoRenderTimer);
      autoRenderTimer = setTimeout(function () {
        refreshAllLayers(true);
      }, 900);
    }

    function syncMapsFrom(panelKey) {
      if (mapSyncLock) {
        return;
      }

      if (isLooping) {
        stopLoop(false);
      }

      const source = panels[panelKey].map;
      mapSyncLock = true;
      forEachActivePanel(function (key, panel) {
        if (key !== panelKey) {
          panel.map.setView(source.getCenter(), source.getZoom(), { animate: false });
        }
      });
      setTimeout(function () {
        mapSyncLock = false;
      }, 0);

      scheduleAutoRender();
    }

    function toggleHoverReadouts() {
      if (!document.getElementById("showHoverReadout").checked) {
        forEachPanel(function (key) { clearHoverReadout(key); });
      }
    }

    function clearHoverReadout(panelKey) {
      const panel = panels[panelKey];
      if (!panel) return;
      panel.hoverRequestSerial += 1;
      if (panel.hoverTimer) {
        clearTimeout(panel.hoverTimer);
        panel.hoverTimer = null;
      }
      if (panel.hoverTooltip && panel.map.hasLayer(panel.hoverTooltip)) {
        panel.map.removeLayer(panel.hoverTooltip);
      }
    }

    function formatHoverValue(data, info, signed) {
      const dv = data.display_value ?? data.value_cfs_per_smi;
      if (dv === null || dv === undefined || !Number.isFinite(Number(dv))) {
        return "No valid grid value";
      }
      const units = data.display_units || info.units || "";
      const digits = units.includes("in") ? 2 : 0;
      const sign = signed && Number(dv) > 0 ? "+" : "";
      return `${sign}${Number(dv).toLocaleString(undefined, {maximumFractionDigits: digits})} ${units}`;
    }

    function formatAreaAverageValue(value, units, signed=false) {
      if (value === null || value === undefined || !Number.isFinite(Number(value))) {
        return "No valid pixels";
      }
      let digits = 0;
      if ((units || "").includes("in") || (units || "").includes("dBZ")) digits = 2;
      const sign = signed && Number(value) > 0 ? "+" : "";
      return `${sign}${Number(value).toLocaleString(undefined, {minimumFractionDigits: digits, maximumFractionDigits: digits})} ${units || ""}`.trim();
    }

    function makeAreaEstimateHtml(data, units, signed=false) {
      if (!data || !data.found) return "";
      const low = data.estimate_low;
      const high = data.estimate_high;
      if (!Number.isFinite(Number(low)) || !Number.isFinite(Number(high))) return "";
      return `<span style="color:#ff6b6b;">${formatAreaAverageValue(low, units, signed)} to ${formatAreaAverageValue(high, units, signed)} range estimate</span><br>`;
    }

    function formatCoveragePercent(value) {
      const n = Number(value);
      if (!Number.isFinite(n)) return "0%";
      if (n > 0 && n < 1) return `${n.toFixed(1)}%`;
      if (n < 10 && Math.abs(n - Math.round(n)) > 0.05) return `${n.toFixed(1)}%`;
      return `${Math.round(n)}%`;
    }

    function previousCoveragePoint(data) {
      const points = data && data.trend && Array.isArray(data.trend.points) ? data.trend.points : [];
      const candidates = points
        .filter(p => p && p.found && Number(p.minutes_ago || 0) > 0 && Array.isArray(p.coverage_thresholds))
        .sort((a, b) => Number(a.minutes_ago || 0) - Number(b.minutes_ago || 0));
      return candidates.length ? candidates[0] : null;
    }

    function coveragePercentLookup(items, threshold) {
      if (!Array.isArray(items)) return null;
      const target = Number(threshold);
      for (const item of items) {
        if (Math.abs(Number(item.threshold) - target) < 0.001) {
          const pct = Number(item.percent);
          return Number.isFinite(pct) ? pct : null;
        }
      }
      return null;
    }

    function formatCoverageDelta(value) {
      const n = Math.abs(Number(value));
      if (!Number.isFinite(n)) return "0%";
      if (n > 0 && n < 0.1) return `${n.toFixed(2)}%`;
      if (n < 1) return `${n.toFixed(1)}%`;
      return `${Math.round(n)}%`;
    }

    function makeCoverageDeltaHtml(item, prevPoint) {
      const current = Number(item && item.percent);
      const threshold = Number(item && item.threshold);
      if (!Number.isFinite(current) || !Number.isFinite(threshold) || current <= 0) return "";
      const prev = prevPoint ? coveragePercentLookup(prevPoint.coverage_thresholds, threshold) : null;
      if (prev === null || prev <= 0) {
        return ` <span style="color:#dddddd;font-size:11px;white-space:nowrap;">(1st frame crossing &gt;${threshold.toLocaleString(undefined, {maximumFractionDigits:0})})</span>`;
      }
      const delta = current - prev;
      if (Math.abs(delta) < 0.05) {
        return ` <span style="color:#bbbbbb;font-size:11px;white-space:nowrap;">→ ${formatCoverageDelta(delta)} Δ10m</span>`;
      }
      if (delta > 0) {
        return ` <span style="color:#ff4b4b;font-size:11px;font-weight:900;white-space:nowrap;">↑ ${formatCoverageDelta(delta)} Δ10m</span>`;
      }
      return ` <span style="color:#4bb3ff;font-size:11px;font-weight:900;white-space:nowrap;">↓ ${formatCoverageDelta(delta)} Δ10m</span>`;
    }

    function makeStreamflowCoverageHtml(data, param, units) {
      if (!data || !data.found || String(param || "").toUpperCase() !== "CREST") return "";
      const items = Array.isArray(data.coverage_thresholds) ? data.coverage_thresholds : [];
      if (!items.length || !Number.isFinite(Number(data.max))) return "";
      const maxText = formatAreaAverageValue(data.max, units, false);
      const prevPoint = previousCoveragePoint(data);
      const parts = items.map(item => {
        const threshold = Number(item.threshold || 0).toLocaleString(undefined, {maximumFractionDigits: 0});
        return `<div style="white-space:nowrap;">Area &gt;${threshold} = ${formatCoveragePercent(item.percent)}${makeCoverageDeltaHtml(item, prevPoint)}</div>`;
      });
      return `<div style="margin:2px 0 4px 0;padding:3px 5px;border:1px solid #777;background:rgba(255,255,255,0.05);line-height:1.35;">` +
             `<span style="font-size:14px;font-weight:900;">Max=${maxText}</span><br>` +
             `<span style="font-size:12px;color:#f2f2f2;">${parts.join("")}</span>` +
             `</div>`;
    }

    function compactTrendThreshold(units, data=null, signed=false) {
      const unitText = String(units || "");
      const param = String((data && data.param) || "").toUpperCase();

      if (unitText.includes("in")) return signed ? 0.01 : 0.02;
      if (unitText.includes("dBZ")) return 0.5;
      if (param === "CREST_DIFF_10M" || param === "HP_MINUS_CREST") return 0.5;
      return 1.0;
    }

    function trendTowardZeroMode(data, signed=false) {
      // Retained for compatibility, but signed-difference trend badges now use
      // the actual trend direction (up = worse, down = better), not distance
      // from zero.
      return false;
    }

    function makeAreaTrendSparklineHtml(data, units, signed=false) {
      if (!data || !data.trend || !Array.isArray(data.trend.points)) return "";
      const pts = data.trend.points
        .filter(p => p && p.found && Number.isFinite(Number(p.mean)))
        .map(p => ({
          minutesAgo: Number(p.minutes_ago || 0),
          mean: Number(p.mean),
          label: p.label || ""
        }));
      if (pts.length < 2) return "";

      pts.sort((a, b) => b.minutesAgo - a.minutesAgo); // oldest -> newest
      const first = pts[0].mean;
      const last = pts[pts.length - 1].mean;
      const delta = last - first;
      const eps = compactTrendThreshold(units, data, signed);
      const towardZeroMode = trendTowardZeroMode(data, signed);

      // For signed-difference / rate-of-change products, use the actual trend
      // direction of the area-average or point values:
      //   -50 → -25 → 0 = WORSE   (trending up)
      //   +50 → +25 → 0 = BETTER  (trending down)
      //   0 → +25 → +50 = WORSE   (trending up)
      //   0 → -25 → -50 = BETTER  (trending down)
      // So the badge logic should simply follow the sign of newest-oldest.
      const trendScore = delta;

      let color = "#9a9a9a";
      let label = "30m SAME";
      let arrow = "→";
      if (Math.abs(trendScore) > eps) {
        if (trendScore > 0) {
          color = "#ff4b4b";
          label = "30m WORSE";
          arrow = "↗";
        } else {
          color = "#4bb3ff";
          label = "30m BETTER";
          arrow = "↘";
        }
      }

      const values = pts.map(p => p.mean);
      let vmin = Math.min(...values);
      let vmax = Math.max(...values);
      if (!Number.isFinite(vmin) || !Number.isFinite(vmax)) return "";
      if (Math.abs(vmax - vmin) < 1e-9) {
        vmin -= 1;
        vmax += 1;
      }

      const w = 86;
      const h = 28;
      const padX = 6;
      const padY = 5;
      const xStep = pts.length > 1 ? (w - 2 * padX) / (pts.length - 1) : 0;
      const coords = pts.map((p, i) => {
        const x = padX + i * xStep;
        const y = h - padY - ((p.mean - vmin) / (vmax - vmin)) * (h - 2 * padY);
        return {x, y, p};
      });
      const pointText = coords.map(c => `${c.x.toFixed(1)},${c.y.toFixed(1)}`).join(" ");
      const dotHtml = coords.map(c => `<circle cx="${c.x.toFixed(1)}" cy="${c.y.toFixed(1)}" r="2.4" fill="${color}" stroke="#ffffff" stroke-width="0.7"></circle>`).join("");
      const titleText = pts.map(p => `${p.minutesAgo}m ago: ${formatAreaAverageValue(p.mean, units, signed)}`).join(" | ");
      const zeroLine = `<line x1="${padX}" y1="${h - padY}" x2="${w - padX}" y2="${h - padY}" stroke="#444" stroke-width="1"></line>`;

      const trendTitle = titleText;

      return `
        <div style="display:flex;align-items:center;gap:6px;margin:3px 0 4px 0;">
          <svg width="${w}" height="${h}" viewBox="0 0 ${w} ${h}" style="border:1px solid #777;background:#050505;flex:0 0 auto;">
            <title>${trendTitle}</title>
            ${zeroLine}
            <polyline points="${pointText}" fill="none" stroke="${color}" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"></polyline>
            ${dotHtml}
          </svg>
          <span style="color:${color};font-weight:900;font-size:13px;white-space:nowrap;">${arrow} ${label}</span>
        </div>`;
    }

    function makeThreatTrendHtml(param, meanValue) {
      const v = Number(meanValue);
      if (!Number.isFinite(v)) return "";
      if (param === "CREST_DIFF_10M") {
        if (v > 0.5) {
          return `<span style="color:#ff4b4b;font-size:15px;font-weight:900;">CURRENT Δ: THREAT INCREASING</span><br>`;
        }
        if (v < -0.5) {
          return `<span style="color:#4bb3ff;font-size:15px;font-weight:900;">CURRENT Δ: THREAT DECREASING</span><br>`;
        }
        return `<span style="color:#dddddd;font-size:14px;font-weight:800;">CURRENT Δ: NEAR STEADY</span><br>`;
      }
      if (param === "QPE1H_DIFF_30M") {
        if (v > 0.01) {
          return `<span style="color:#ff4b4b;font-size:15px;font-weight:900;">CURRENT Δ: 1-HOUR INTENSITY INCREASING</span><br>`;
        }
        if (v < -0.01) {
          return `<span style="color:#4bb3ff;font-size:15px;font-weight:900;">CURRENT Δ: 1-HOUR INTENSITY DECREASING</span><br>`;
        }
        return `<span style="color:#dddddd;font-size:14px;font-weight:800;">CURRENT Δ: 1-HOUR INTENSITY NEAR STEADY</span><br>`;
      }
      return "";
    }

    function toggleAreaAverageTool() {
      const checkbox = document.getElementById("enableAreaAvg");
      areaAvgEnabled = !!(checkbox && checkbox.checked);
      if (areaAvgEnabled) {
        clearHoverReadout("left");
        clearHoverReadout("right");
        clearHoverReadout("lowerLeft");
        clearHoverReadout("lowerRight");
      } else {
        stopAreaAveragePulse();
        areaAvgDrawing = null;
        areaAvgVertices = [];
        areaAvgSourcePanelKey = null;
      }
      forEachPanel(function (key, panel) {
        const container = panel.map.getContainer();
        if (areaAvgEnabled) {
          try { panel.map.dragging.disable(); } catch (e) {}
          try { panel.map.doubleClickZoom.disable(); } catch (e) {}
          container.style.cursor = "crosshair";
        } else {
          try { panel.map.dragging.enable(); } catch (e) {}
          try { panel.map.doubleClickZoom.enable(); } catch (e) {}
          container.style.cursor = "";
        }
      });
    }

    function clearAreaAverage() {
      stopAreaAveragePulse();
      areaAvgSerial += 1;
      areaAvgDrawing = null;
      areaAvgVertices = [];
      areaAvgSourcePanelKey = null;
      forEachPanel(function (key, panel) {
        try { panel.areaAvgGroup.clearLayers(); } catch (e) {}
        try {
          if (panel.map.hasLayer(panel.areaAvgGroup)) panel.map.removeLayer(panel.areaAvgGroup);
        } catch (e) {}
        try {
          if (panel.areaAvgPopup) panel.map.closePopup(panel.areaAvgPopup);
        } catch (e) {}
        panel.areaAvgPopup = null;
      });
    }

    function stopAreaAveragePulse() {
      if (areaAvgPulseTimer) {
        clearInterval(areaAvgPulseTimer);
        areaAvgPulseTimer = null;
      }
    }

    function startAreaAveragePulse() {
      if (areaAvgPulseTimer) return;
      areaAvgPulseStart = Date.now();
      areaAvgPulseTimer = setInterval(function () {
        const phase = ((Date.now() - areaAvgPulseStart) % 1150) / 1150.0;
        const wave = 0.5 - 0.5 * Math.cos(phase * Math.PI * 2.0);
        forEachActivePanel(function (key, panel) {
          try {
            panel.areaAvgGroup.eachLayer(function (layer) {
              if (!layer || !layer._areaAvgPulseLayer || !layer.setStyle) return;
              if (layer._areaAvgPulseHalo) {
                layer.setStyle({
                  weight: 4.0 + wave * 8.0,
                  opacity: 0.72 - wave * 0.57,
                  fillOpacity: 0.0
                });
              } else {
                layer.setStyle({
                  weight: 2.2 + wave * 1.6,
                  opacity: 0.78 + wave * 0.22,
                  fillOpacity: 0.045 + wave * 0.075
                });
              }
            });
          } catch (e) {}
        });
      }, 70);
    }

    function areaAveragePopupLatLng(vertices, map) {
      try {
        const bounds = L.latLngBounds(vertices);
        const topLat = bounds.getNorth();
        const latSpan = Math.max(Math.abs(bounds.getNorth() - bounds.getSouth()), 0.0001);
        const topBand = Math.max(latSpan * 0.08, 0.00005);
        const topVertices = vertices.filter(v => Math.abs(v.lat - topLat) <= topBand);
        const anchorLng = topVertices.length
          ? topVertices.reduce((sum, v) => sum + v.lng, 0.0) / topVertices.length
          : bounds.getCenter().lng;

        // Put the popup anchor right on the north/top edge of the drawn polygon.
        // Leaflet's popup tip points to this anchor, so the arrow touches the
        // polygon while the popup body stays above it instead of overlapping.
        return L.latLng(topLat, anchorLng);
      } catch (e) {
        const plainVertices = vertices.map(v => ({lat: v.lat, lon: v.lng}));
        const center = plainVertices.reduce((acc, v) => ({lat: acc.lat + v.lat / plainVertices.length, lon: acc.lon + v.lon / plainVertices.length}), {lat:0, lon:0});
        return L.latLng(center.lat, center.lon);
      }
    }

    function drawAreaAverageShape(vertices, finalized=false) {
      if (!Array.isArray(vertices) || vertices.length === 0) return;
      if (!finalized) stopAreaAveragePulse();
      forEachActivePanel(function (key, panel) {
        if (!panel.map.hasLayer(panel.areaAvgGroup)) {
          panel.areaAvgGroup.addTo(panel.map);
        }
        panel.areaAvgGroup.clearLayers();
        if (vertices.length >= 3 && finalized) {
          const polygon = L.polygon(vertices, {
            color: "#ffffff",
            weight: 2.2,
            opacity: 0.95,
            fill: true,
            fillColor: "#ffffff",
            fillOpacity: 0.075,
            interactive: false,
            className: "area-avg-pulse-shape"
          });
          polygon._areaAvgPulseLayer = true;

          const pulseHalo = L.polygon(vertices, {
            color: "#ffffff",
            weight: 6.0,
            opacity: 0.35,
            fill: false,
            interactive: false,
            className: "area-avg-pulse-shape"
          });
          pulseHalo._areaAvgPulseLayer = true;
          pulseHalo._areaAvgPulseHalo = true;

          panel.areaAvgGroup.addLayer(polygon);
          panel.areaAvgGroup.addLayer(pulseHalo);
          try {
            const el = polygon.getElement && polygon.getElement();
            if (el) el.classList.add("area-avg-pulse-shape");
            const haloEl = pulseHalo.getElement && pulseHalo.getElement();
            if (haloEl) haloEl.classList.add("area-avg-pulse-shape");
          } catch (e) {}
        } else {
          const polyline = L.polyline(vertices, {
            color: "#ffffff",
            weight: 2.5,
            opacity: 1.0,
            dashArray: finalized ? null : "5,5",
            interactive: false
          });
          panel.areaAvgGroup.addLayer(polyline);
          for (const latlng of vertices) {
            panel.areaAvgGroup.addLayer(L.circleMarker(latlng, {
              radius: 4, color: "#ffffff", weight: 2, fill: true, fillColor: "#000000", fillOpacity: 0.8, interactive: false
            }));
          }
        }
        bringPanelBoundariesToFront(key);
      });
      if (finalized && vertices.length >= 3) startAreaAveragePulse();
    }

    function handleAreaAverageMouseDown(panelKey, e) {
      return;
    }

    function handleAreaAverageMouseMove(panelKey, e) {
      if (!areaAvgEnabled || !areaAvgDrawing || areaAvgSourcePanelKey !== panelKey || !e.latlng) return;
      const preview = areaAvgVertices.concat([e.latlng]);
      drawAreaAverageShape(preview, false);
    }

    function handleAreaAverageMouseUp(panelKey, e) {
      return;
    }

    function handleAreaAverageDoubleClick(panelKey, e) {
      if (!areaAvgEnabled || areaAvgSourcePanelKey !== panelKey || areaAvgVertices.length < 3) return;
      if (e && e.originalEvent) {
        L.DomEvent.preventDefault(e.originalEvent);
        L.DomEvent.stopPropagation(e.originalEvent);
      }
      finishAreaAveragePolygon();
    }

    function handleAreaAverageMapClick(panelKey, e) {
      if (!areaAvgEnabled || !activePanelKeys().includes(panelKey) || !e.latlng) return false;
      if (e.originalEvent) {
        L.DomEvent.preventDefault(e.originalEvent);
        L.DomEvent.stopPropagation(e.originalEvent);
      }
      if (!areaAvgDrawing || areaAvgSourcePanelKey !== panelKey) {
        clearAreaAverage();
        areaAvgDrawing = { mode: "polygon" };
        areaAvgVertices = [];
        areaAvgSourcePanelKey = panelKey;
      }
      areaAvgVertices.push(e.latlng);
      drawAreaAverageShape(areaAvgVertices, false);
      return true;
    }

    function finishAreaAveragePolygon() {
      if (!areaAvgEnabled || areaAvgVertices.length < 3) return;
      const vertices = areaAvgVertices.slice();
      areaAvgDrawing = null;
      finalizeAreaAveragePolygon(vertices);
    }

    async function finalizeAreaAveragePolygon(vertices) {
      const serial = ++areaAvgSerial;
      drawAreaAverageShape(vertices, true);
      const token = selectedEffectiveToken();
      const plainVertices = vertices.map(v => ({lat: v.lat, lon: v.lng}));

      forEachActivePanel(async function (key, panel) {
        const param = selectedParam(key);
        const product = rawProductForParam(param);
        const info = selectedParamInfo(key);
        const loadingHtml = `<b>${info.shortLabel} area average</b><br>Computing...`;
        try {
          if (panel.areaAvgPopup) panel.map.closePopup(panel.areaAvgPopup);
          panel.areaAvgPopup = L.popup({
              autoClose: false,
              closeOnClick: false,
              className: "area-avg-popup",
              autoPan: true,
              autoPanPadding: [18, 18],
              offset: [0, 0]
            })
            .setLatLng(areaAveragePopupLatLng(vertices, panel.map))
            .setContent(loadingHtml)
            .openOn(panel.map);
        } catch (e) {}

        try {
          const resp = await fetch(`/api/area_average_polygon_trend`, {
            method: 'POST',
            headers: {'Content-Type': 'application/json'},
            body: JSON.stringify({param, product, time: token || "", vertices: plainVertices, samples: 3, step_minutes: 10})
          });
          const data = await resp.json();
          if (serial !== areaAvgSerial) return;
          const units = data.display_units || info.units || "";
          const signed = !!info.isDifference;
          const meanText = resp.ok && data.found ? formatAreaAverageValue(data.mean, units, signed) : "No valid pixels";
          const minText = resp.ok && data.found ? formatAreaAverageValue(data.min, units, signed) : "";
          const maxText = resp.ok && data.found ? formatAreaAverageValue(data.max, units, signed) : "";
          const isCrestStreamflow = String(param || "").toUpperCase() === "CREST";
          const html =
            `<b>${info.shortLabel} area average</b><br>` +
            `${data.found ? makeThreatTrendHtml(param, data.mean) : ""}` +
            `${data.found ? makeAreaTrendSparklineHtml(data, units, signed) : ""}` +
            `${data.found ? makeStreamflowCoverageHtml(data, param, units) : ""}` +
            `<span style="font-size:16px;">${meanText}</span><br>` +
            `${data.found && !isCrestStreamflow ? `Min/Max: ${minText} / ${maxText}<br>` : ""}` +
            `${data.found ? makeAreaEstimateHtml(data, units, signed) : ""}`;
          if (panel.areaAvgPopup) panel.areaAvgPopup.setContent(html).openOn(panel.map);
          drawAreaAverageShape(vertices, true);
        } catch (err) {
          if (serial !== areaAvgSerial) return;
          if (panel.areaAvgPopup) panel.areaAvgPopup.setContent(`<b>${info.shortLabel} area average</b><br>Average query failed.`).openOn(panel.map);
        }
      });
    }

    function handleHoverMove(panelKey, e) {
      if (areaAvgEnabled) return;
      const show = document.getElementById("showHoverReadout").checked;
      const panel = panels[panelKey];
      if (!show || !panel) return;

      const param = selectedParam(panelKey);
      const info = parameterInfo[param] || parameterInfo.CREST;
      const signed = !!info.isDifference;
      const token = selectedEffectiveToken();
      const lat = e.latlng.lat;
      const lon = e.latlng.lng;

      if (!panel.hoverTooltip) {
        panel.hoverTooltip = L.tooltip({
          permanent: false,
          direction: "top",
          offset: [12, -10],
          opacity: 0.96,
          className: "hover-value-tooltip"
        });
      }

      panel.hoverTooltip
        .setLatLng(e.latlng)
        .setContent(`${info.shortLabel}: loading...`)
        .addTo(panel.map);

      if (panel.hoverTimer) {
        clearTimeout(panel.hoverTimer);
      }

      const thisRequest = ++panel.hoverRequestSerial;
      panel.hoverTimer = setTimeout(async function () {
        let url =
          `/api/value?param=${encodeURIComponent(param)}` +
          `&product=${encodeURIComponent(rawProductForParam(param))}` +
          `&lat=${lat}&lon=${lon}` +
          `&cacheBust=${Date.now()}`;

        if (token) {
          url += `&time=${encodeURIComponent(token)}`;
        }

        try {
          const resp = await fetch(url);
          const data = await resp.json();

          if (thisRequest !== panel.hoverRequestSerial || !document.getElementById("showHoverReadout").checked) {
            return;
          }

          const valueText = resp.ok ? formatHoverValue(data, info, signed) : "Value error";
          panel.hoverTooltip
            .setLatLng(e.latlng)
            .setContent(`${info.shortLabel}: ${valueText}`)
            .addTo(panel.map);
        } catch (err) {
          if (thisRequest === panel.hoverRequestSerial && panel.hoverTooltip) {
            panel.hoverTooltip
              .setLatLng(e.latlng)
              .setContent(`${info.shortLabel}: value lookup failed`)
              .addTo(panel.map);
          }
        }
      }, 220);
    }

    function digitsForDisplayUnits(units) {
      units = String(units || "");
      if (units.includes("in")) return 2;
      if (units.includes("dBZ")) return 1;
      return 0;
    }

    function formatClickValueHtml(data, info, signed) {
      const dv = data.display_value ?? data.value_cfs_per_smi;
      if (dv === null || dv === undefined || !Number.isFinite(Number(dv))) {
        return "No valid grid value";
      }
      const units = data.display_units || info.units || "";
      const digits = digitsForDisplayUnits(units);
      const sign = signed && Number(dv) > 0 ? "+" : "";
      return `<b>${sign}${Number(dv).toLocaleString(undefined, {minimumFractionDigits: digits, maximumFractionDigits: digits})} ${units}</b>`;
    }

    function cleanValidTimeText(text) {
      if (!text) return "";
      const s = String(text);
      const m = s.match(/(\d{4}-\d{2}-\d{2})[ T](\d{2}:\d{2})(?::(\d{2}))?Z?/);
      if (m) {
        return `${m[1]} ${m[2]}:${m[3] || "00"}Z`;
      }
      return s
        .replace(/\s*-\s*(remote|local)Z?\s*$/i, "")
        .replace(/\b(remote|local)Z?\b/ig, "")
        .trim();
    }

    function clearPanelClickReadout(panelKey) {
      const panel = panels[panelKey];
      if (!panel) return;
      panel.clickReadoutSerial += 1;
      try {
        if (panel.clickReadoutPopup) {
          panel.map.closePopup(panel.clickReadoutPopup);
          if (panel.map.hasLayer(panel.clickReadoutPopup)) panel.map.removeLayer(panel.clickReadoutPopup);
        }
      } catch (e) {}
      panel.clickReadoutPopup = null;
      try {
        panel.clickReadoutGroup.clearLayers();
        if (panel.map.hasLayer(panel.clickReadoutGroup)) {
          panel.map.removeLayer(panel.clickReadoutGroup);
        }
      } catch (e) {}
    }

    function clearAllClickReadouts() {
      forEachPanel(function (key) {
        clearPanelClickReadout(key);
      });
    }

    function addClickReadoutPulse(panelKey, latlng) {
      const panel = panels[panelKey];
      if (!panel) return;
      try {
        panel.clickReadoutGroup.clearLayers();
        if (!panel.map.hasLayer(panel.clickReadoutGroup)) {
          panel.clickReadoutGroup.addTo(panel.map);
        }
        const pulseIcon = L.divIcon({
          className: "click-readout-pulse-marker",
          html: '<div class="click-readout-pulse-ring"></div>',
          iconSize: [26, 26],
          iconAnchor: [13, 13]
        });
        panel.clickReadoutGroup.addLayer(L.marker(latlng, {
          icon: pulseIcon,
          interactive: false,
          keyboard: false
        }));
        bringPanelBoundariesToFront(panelKey);
      } catch (e) {}
    }

    async function fetchClickedValueForPanel(panelKey, lat, lon, token) {
      const param = selectedParam(panelKey);
      const product = rawProductForParam(param);
      const info = parameterInfo[param] || parameterInfo.CREST;
      const signed = !!info.isDifference;
      const panelLabel = PANEL_LABELS[panelKey] || panelKey.toUpperCase();

      let url =
        `/api/value?param=${encodeURIComponent(param)}` +
        `&product=${encodeURIComponent(product)}` +
        `&lat=${lat}&lon=${lon}` +
        `&cacheBust=${Date.now()}`;

      if (token) {
        url += `&time=${encodeURIComponent(token)}`;
      }

      try {
        // Point readouts use the trend endpoint so each clicked location gets the
        // same compact 3-sample / 30-minute trend graphic as polygon averages.
        url =
          `/api/value_trend?param=${encodeURIComponent(param)}` +
          `&product=${encodeURIComponent(product)}` +
          `&lat=${lat}&lon=${lon}` +
          `&samples=3&step_minutes=10` +
          `&cacheBust=${Date.now()}`;

        if (token) {
          url += `&time=${encodeURIComponent(token)}`;
        }

        const resp = await fetch(url);
        const data = await resp.json();
        const units = data.display_units || info.units || "";
        const valueHtml = resp.ok ? formatClickValueHtml(data, info, signed) : "Value error";
        const threatHtml = (resp.ok && signed) ? makeThreatTrendHtml(param, data.display_value ?? data.value_cfs_per_smi) : "";
        const trendHtml = resp.ok ? makeAreaTrendSparklineHtml(data, units, signed) : "";
        const validText = cleanValidTimeText(resp.ok ? data.file_time_utc : "");
        const validHtml = validText ? `<br>Valid: ${validText}` : "";

        return (
          `<b>${panelLabel} — ${info.shortLabel}</b><br><br>` +
          `${threatHtml}` +
          `${trendHtml}` +
          `<span style="font-size:16px;">${valueHtml}</span>` +
          `${validHtml}`
        );
      } catch (err) {
        return (
          `<b>${panelLabel} — ${info.shortLabel}</b><br><br>` +
          `Value query failed`
        );
      }
    }

    async function handleMapClick(panelKey, e) {
      if (areaAvgEnabled) {
        handleAreaAverageMapClick(panelKey, e);
        return;
      }
      if (areaAvgDrawing) return;

      const token = selectedEffectiveToken();
      const lat = e.latlng.lat;
      const lon = e.latlng.lng;
      const latlng = [lat, lon];
      const keys = activePanelKeys();

      clearAllClickReadouts();

      for (const key of keys) {
        const panel = panels[key];
        if (!panel) continue;

        const info = selectedParamInfo(key);
        const thisClick = ++panel.clickReadoutSerial;
        addClickReadoutPulse(key, latlng);

        const popup = L.popup({
          maxWidth: 270,
          className: "click-readout-popup",
          closeOnClick: false,
          autoClose: false
        })
          .setLatLng(latlng)
          .setContent(
            `<b>${PANEL_LABELS[key] || key.toUpperCase()} — ${info.shortLabel}</b><br><br>` +
            `Loading value...`
          );

        panel.clickReadoutPopup = popup;
        popup.openOn(panel.map);

        fetchClickedValueForPanel(key, lat, lon, token)
          .then(function (html) {
            if (thisClick !== panel.clickReadoutSerial || panel.clickReadoutPopup !== popup) return;
            popup.setContent(html);
          })
          .catch(function () {
            if (thisClick !== panel.clickReadoutSerial || panel.clickReadoutPopup !== popup) return;
            popup.setContent(
              `<b>${PANEL_LABELS[key] || key.toUpperCase()} — ${info.shortLabel}</b><br><br>` +
              `Value query failed.`
            );
          });
      }
    }

    function loopBoundsFromPrimaryMap() {
      const b = primaryMap().getBounds();
      return {
        west: b.getWest(),
        south: b.getSouth(),
        east: b.getEast(),
        north: b.getNorth()
      };
    }

    function buildRenderUrlForPanelToken(panelKey, token, bounds, cacheKey) {
      const param = selectedParam(panelKey);
      const product = rawProductForParam(param);
      const width = getRenderWidth(panelKey);
      let url =
        `/api/render.png?param=${encodeURIComponent(param)}` +
        `&product=${encodeURIComponent(product)}` +
        `&west=${bounds.west}&south=${bounds.south}&east=${bounds.east}&north=${bounds.north}` +
        `&width=${width}` +
        `&cacheBust=${cacheKey || "loop"}`;
      if (token) {
        url += `&time=${encodeURIComponent(token)}`;
      }
      return url;
    }

    function preloadImage(url) {
      return new Promise(function (resolve) {
        const img = new Image();
        img.onload = function () { resolve({ ok: true, url: url }); };
        img.onerror = function () { resolve({ ok: false, url: url }); };
        img.src = url;
      });
    }

    async function selectLoopTokens(product, frameCount, skip) {
      const resp = await fetch(`/api/archive/list?product=${encodeURIComponent(product)}&cacheBust=${Date.now()}`);
      const data = await resp.json();
      if (!resp.ok || !data.times || !data.times.length) {
        throw new Error(data.error || `No archive/list times available for ${product}`);
      }

      const selectedToken = selectedEffectiveToken();
      let items = data.times;
      if (selectedToken) {
        items = items.filter(function (item) { return item.token <= selectedToken; });
        if (!items.length) items = data.times;
      }

      const picked = [];
      for (let i = 0; i < items.length && picked.length < frameCount; i += skip) {
        picked.push(items[i].token);
      }

      return picked.reverse();
    }

    async function startLoop() {
      stopLoop(false);
      const status = document.getElementById("status");
      const keys = activePanelKeys();
      const frameCount = Number(document.getElementById("loopFrames").value || 12);
      const skip = Math.max(1, Number(document.getElementById("loopSkip").value || 1));
      const product = selectedArchiveProduct();
      const bounds = loopBoundsFromPrimaryMap();
      const cacheKey = `loop-${Date.now()}`;

      loopBaseBounds = bounds;
      suppressAutoRenderUntil = Date.now() + 999999;
      status.innerHTML = `Building ${frameCount}-frame loop from ${product}. Preloading images first...`;

      try {
        const tokens = await selectLoopTokens(product, frameCount, skip);
        if (!tokens.length) throw new Error("No valid loop times were found.");

        const preloadJobs = [];
        loopFrames = tokens.map(function (token) {
          const frame = { token: token, urls: {} };
          for (const key of keys) {
            const url = buildRenderUrlForPanelToken(key, token, bounds, cacheKey);
            frame.urls[key] = url;
            preloadJobs.push(preloadImage(url));
          }
          return frame;
        });

        const results = await Promise.all(preloadJobs);
        const failed = results.filter(function (r) { return !r.ok; }).length;
        if (failed >= results.length) {
          throw new Error("All loop frame image loads failed. Check terminal/server output.");
        }

        isLooping = true;
        loopIndex = 0;
        showLoopFrame(0);
        const delay = Number(document.getElementById("loopDelay").value || 220);
        loopTimer = setInterval(function () {
          loopIndex = (loopIndex + 1) % loopFrames.length;
          showLoopFrame(loopIndex);
        }, delay);

        status.innerHTML = `Loop playing: ${loopFrames.length} frames, ${keys.length} panel(s), ${product}. ${failed ? failed + " frame-panel image(s) failed and were skipped by the browser." : "All images preloaded."}`;
      } catch (err) {
        suppressAutoRenderUntil = 0;
        status.innerHTML = `<b>Loop failed:</b> ${err.message || err}`;
      }
    }

    function showLoopFrame(index) {
      const frame = loopFrames[index];
      if (!frame || !loopBaseBounds) return;
      const opacity = Number(document.getElementById("opacity").value) / 100.0;
      const bounds = [[loopBaseBounds.south, loopBaseBounds.west], [loopBaseBounds.north, loopBaseBounds.east]];
      for (const key of activePanelKeys()) {
        const panel = panels[key];
        const url = frame.urls[key];
        if (!panel || !url) continue;

        if (panel.loopOverlay && panel.map.hasLayer(panel.loopOverlay)) {
          panel.map.removeLayer(panel.loopOverlay);
        }

        if (panel.streamflowOverlay && panel.map.hasLayer(panel.streamflowOverlay)) {
          panel.map.removeLayer(panel.streamflowOverlay);
        }

        panel.loopOverlay = L.imageOverlay(url, bounds, {
          opacity: opacity,
          interactive: false
        }).addTo(panel.map);

        const info = selectedParamInfo(key);
        panel.titleEl.innerHTML = `${PANEL_LABELS[key]}<br>${info.shortLabel}<br>${tokenToIsoZ(frame.token)}`;
        bringPanelBoundariesToFront(key);
      }
      updateLiveIndicator();
    }

    function stopLoop(refresh=true) {
      if (loopTimer) {
        clearInterval(loopTimer);
        loopTimer = null;
      }
      isLooping = false;
      suppressAutoRenderUntil = 0;
      forEachPanel(function (key, panel) {
        if (panel.loopOverlay && panel.map.hasLayer(panel.loopOverlay)) {
          panel.map.removeLayer(panel.loopOverlay);
        }
        panel.loopOverlay = null;
      });
      loopFrames = [];
      loopIndex = 0;
      updatePanelTitles();
      if (refresh) {
        refreshAllLayers(true);
      }
    }

    document.getElementById("archiveList").addEventListener("change", function () {
      goArchiveMode();
    });

    document.getElementById("timeMode").addEventListener("change", function () {
      updateTimelineControls();
      refreshAllLayers(true);
    });

    document.getElementById("archiveTime").addEventListener("change", function () {
      goArchiveMode();
    });

    document.addEventListener("keydown", function (e) {
      if (e.key === "Escape") {
        clearAllClickReadouts();
      }
    });

    function initializeViewer() {
      setSidebarCollapsed(savedSidebarCollapsed(), false);
      const fastRenderCheckbox = document.getElementById("fastRender");
      if (fastRenderCheckbox) fastRenderCheckbox.checked = savedFastRenderEnabled();

      initPanel("left", "mapLeft", "leftTitle", "CREST");
      initPanel("right", "mapRight", "rightTitle", "CREST_DIFF_10M");
      initPanel("lowerLeft", "mapLowerLeft", "lowerLeftTitle", "RAINRATE");
      initPanel("lowerRight", "mapLowerRight", "lowerRightTitle", "RALA");

      document.getElementById("panelLayout").value = savedLayoutCount();
      document.getElementById("leftParam").value = savedParam("left", "CREST");
      document.getElementById("rightParam").value = savedParam("right", "CREST_DIFF_10M");
      document.getElementById("lowerLeftParam").value = savedParam("lowerLeft", "RAINRATE");
      document.getElementById("lowerRightParam").value = savedParam("lowerRight", "RALA");

      applyLayout(false);
      setDefaultArchiveInputUTC();
      updateTimelineControls();
      updatePanelTitles();
      updateLiveIndicator();

      setTimeout(async function () {
        invalidateAllPanelSizes();
        await loadArchiveList();
        await updateLiveLatestToken(true);
        refreshAllLayers(false);
      }, 150);
    }

    initializeViewer();

    setInterval(async function () {
      if (document.getElementById("timeMode").value === "latest") {
        await updateLiveLatestToken(true);
        updateTimelineLabel();
        updateLiveIndicator();
        if (!isLooping) refreshAllLayers(true);
      }
    }, 10 * 60 * 1000);
  </script>
</body>
</html>
"""



def keyed_lock(lock_store, key):
    key = str(key)
    with LOCKS_GUARD:
        lock = lock_store.get(key)
        if lock is None:
            lock = threading.RLock()
            lock_store[key] = lock
        return lock


def requests_get(url, **kwargs):
    headers = kwargs.pop("headers", {})
    headers.setdefault("User-Agent", APP_USER_AGENT)
    return requests.get(url, headers=headers, **kwargs)


def now_utc():
    return datetime.now(timezone.utc)


def now_utc_iso():
    return now_utc().isoformat(timespec="seconds").replace("+00:00", "Z")


def ascii_header_value(value):
    text = "" if value is None else str(value)
    replacements = {
        "—": "-",
        "–": "-",
        "−": "-",
        "Δ": "Delta ",
        "²": "^2",
        "³": "^3",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return text.encode("latin-1", "replace").decode("latin-1")


def product_info(product):
    product = (product or DEFAULT_PRODUCT).upper()
    if product not in PRODUCTS:
        raise ValueError(f"Unknown product '{product}'. Valid options: {', '.join(PRODUCTS.keys())}")
    return product, PRODUCTS[product]


def parse_mrms_token(filename):
    match = re.search(r"_(\d{8}-\d{6})\.grib2\.gz$", filename)
    if not match:
        return None
    return match.group(1)


def token_to_datetime(token):
    return datetime.strptime(token, "%Y%m%d-%H%M%S").replace(tzinfo=timezone.utc)


def token_to_label(token):
    dt = token_to_datetime(token)
    return dt.strftime("%Y-%m-%d %H:%M:%SZ")


def datetime_to_iem_at(dt):
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%MZ")


def cache_paths_for_url(product, url):
    key = hashlib.md5(f"{product}_{url}".encode("utf-8")).hexdigest()
    gz_path = os.path.join(CACHE_DIR, f"{product}_{key}.grib2.gz")
    grib_path = os.path.join(CACHE_DIR, f"{product}_{key}.grib2")
    meta_path = os.path.join(CACHE_DIR, f"{product}_{key}.json")
    return gz_path, grib_path, meta_path


def archive_product_dir(product):
    product_dir = os.path.join(ARCHIVE_DIR, product)
    os.makedirs(product_dir, exist_ok=True)
    return product_dir


def archive_paths(product, token):
    product_dir = archive_product_dir(product)
    grib_path = os.path.join(product_dir, f"{product}_{token}.grib2")
    meta_path = os.path.join(product_dir, f"{product}_{token}.json")
    return grib_path, meta_path


def write_json(path, payload):
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)
    except Exception:
        pass


def read_json(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def download_and_unzip_url(product, url, force=False):
    gz_path, grib_path, meta_path = cache_paths_for_url(product, url)

    # Single-flight each remote file so simultaneous panel requests do not
    # download/decompress the same GRIB twice.
    lock = keyed_lock(DOWNLOAD_LOCKS, grib_path)
    with lock:
        if (
            not force
            and os.path.exists(grib_path)
            and time.time() - os.path.getmtime(grib_path) < CACHE_TTL_SECONDS
        ):
            return grib_path, read_json(meta_path)

        r = requests_get(url, timeout=90)
        r.raise_for_status()

        tmp_gz = f"{gz_path}.tmp"
        tmp_grib = f"{grib_path}.tmp"

        with open(tmp_gz, "wb") as f:
            f.write(r.content)

        with gzip.open(tmp_gz, "rb") as src, open(tmp_grib, "wb") as dst:
            dst.write(src.read())

        os.replace(tmp_gz, gz_path)
        os.replace(tmp_grib, grib_path)

        token = parse_mrms_token(os.path.basename(url))

        meta = {
            "product": product,
            "url": url,
            "token": token,
            "downloaded_utc": now_utc_iso(),
            "last_modified": r.headers.get("Last-Modified", ""),
            "content_length": r.headers.get("Content-Length", ""),
        }
        write_json(meta_path, meta)

        return grib_path, meta


def list_remote_files(product, limit=250):
    product, info = product_info(product)
    now = time.time()

    cached = REMOTE_LIST_CACHE.get(product)

    if cached and now - cached["time"] < REMOTE_LIST_TTL_SECONDS:
        return cached["items"][:limit]

    directory = info["directory"]
    prefix = info["file_prefix"]

    r = requests_get(directory, timeout=60)
    r.raise_for_status()

    pattern = rf"({re.escape(prefix)}\d{{8}}-\d{{6}}\.grib2\.gz)"
    filenames = sorted(set(re.findall(pattern, r.text)))

    items = []
    for filename in filenames:
        token = parse_mrms_token(filename)
        if not token:
            continue

        items.append({
            "product": product,
            "token": token,
            "filename": filename,
            "url": urljoin(directory, filename),
            "label": f"{token_to_label(token)} - remote",
        })

    items.sort(key=lambda x: x["token"], reverse=True)

    REMOTE_LIST_CACHE[product] = {
        "time": now,
        "items": items,
    }

    return items[:limit]


def nearest_remote_item(product, requested_token, limit=2000):
    product, _ = product_info(product)
    remote_items = list_remote_files(product, limit=limit)

    if not remote_items:
        return None, None

    if not requested_token:
        return remote_items[0], 0.0

    requested_dt = token_to_datetime(requested_token)
    best_item = None
    best_delta = None

    for item in remote_items:
        item_dt = token_to_datetime(item["token"])
        delta = abs((item_dt - requested_dt).total_seconds())

        if best_delta is None or delta < best_delta:
            best_delta = delta
            best_item = item

    return best_item, best_delta


def annotate_snapped_item(item, requested_token, delta_seconds):
    if not item:
        return item

    item = dict(item)

    if requested_token and item.get("token") != requested_token:
        try:
            requested_label = token_to_label(requested_token)
        except Exception:
            requested_label = str(requested_token)

        minutes = int(round(float(delta_seconds or 0.0) / 60.0))
        item["requested_token"] = requested_token
        item["snapped_from_requested"] = True
        item["delta_seconds_from_requested"] = float(delta_seconds or 0.0)
        item["label"] = f"{token_to_label(item['token'])} - nearest available to requested {requested_label} ({minutes} min off)"

    return item


def choose_remote_file(product, requested_token=None):
    product, info = product_info(product)

    if requested_token:
        try:
            best_item, best_delta = nearest_remote_item(product, requested_token, limit=2000)
        except Exception:
            best_item, best_delta = None, None

        if best_item:
            # Do not synthesize exact archive URLs. MRMS files roll off the server, and
            # exact stale URLs produce 404s. Use the nearest file that the directory
            # currently advertises and clearly label when we had to snap.
            return annotate_snapped_item(best_item, requested_token, best_delta)

        # Last resort: latest endpoint. This avoids a hard 404 and keeps the viewer usable.
        return {
            "product": product,
            "token": None,
            "filename": "latest",
            "url": info["latest_url"],
            "label": f"Latest/current Z - requested {requested_token} unavailable",
            "requested_token": requested_token,
            "snapped_from_requested": True,
        }

    try:
        remote_items = list_remote_files(product, limit=1)
        if remote_items:
            return remote_items[0]
    except Exception:
        pass

    return {
        "product": product,
        "token": None,
        "filename": "latest",
        "url": info["latest_url"],
        "label": "Latest/current Z",
    }


def get_grib_for_product_time(product, requested_token=None):
    product, _ = product_info(product)

    if requested_token:
        local_grib, local_meta = archive_paths(product, requested_token)
        if os.path.exists(local_grib):
            meta = read_json(local_meta)
            meta["source"] = "local_archive"
            return local_grib, meta

    item = choose_remote_file(product, requested_token)

    try:
        grib_path, meta = download_and_unzip_url(product, item["url"])
    except requests.HTTPError as e:
        status_code = getattr(e.response, "status_code", None)
        if requested_token and status_code == 404:
            REMOTE_LIST_CACHE.pop(product, None)
            item = choose_remote_file(product, requested_token)
            grib_path, meta = download_and_unzip_url(product, item["url"])
        else:
            raise

    meta.update({
        "token": item.get("token"),
        "label": item.get("label"),
        "source": "remote_ncep",
        "requested_token": item.get("requested_token", requested_token),
        "snapped_from_requested": bool(item.get("snapped_from_requested", False)),
        "delta_seconds_from_requested": item.get("delta_seconds_from_requested"),
    })

    return grib_path, meta


def capture_latest_to_archive(product):
    product, _ = product_info(product)
    item = choose_remote_file(product, requested_token=None)

    if not item.get("token"):
        grib_path, _ = download_and_unzip_url(product, item["url"], force=True)
        token = now_utc().strftime("%Y%m%d-%H%M%S")
    else:
        grib_path, _ = download_and_unzip_url(product, item["url"], force=False)
        token = item["token"]

    archive_grib, archive_meta = archive_paths(product, token)

    if not os.path.exists(archive_grib):
        shutil.copy2(grib_path, archive_grib)

    payload = {
        "product": product,
        "token": token,
        "label": token_to_label(token) if re.match(r"^\d{8}-\d{6}$", token) else token,
        "source_url": item["url"],
        "captured_utc": now_utc_iso(),
    }
    write_json(archive_meta, payload)

    return payload


def list_local_archive(product):
    product, _ = product_info(product)
    product_dir = archive_product_dir(product)

    items = []
    for name in os.listdir(product_dir):
        if not name.endswith(".grib2"):
            continue

        match = re.match(rf"{re.escape(product)}_(\d{{8}}-\d{{6}})\.grib2$", name)
        if not match:
            continue

        token = match.group(1)
        items.append({
            "product": product,
            "token": token,
            "label": f"{token_to_label(token)} - local",
            "source": "local",
        })

    items.sort(key=lambda x: x["token"], reverse=True)
    return items


def clean_mrms_array(arr, nodata=None):
    arr = arr.astype(np.float32)

    if nodata is not None:
        arr[arr == nodata] = np.nan

    arr[arr <= -900] = np.nan
    arr[~np.isfinite(arr)] = np.nan

    return arr


def clamp_window(win, src):
    col_off = max(0, int(np.floor(win.col_off)))
    row_off = max(0, int(np.floor(win.row_off)))

    col_end = min(src.width, int(np.ceil(win.col_off + win.width)))
    row_end = min(src.height, int(np.ceil(win.row_off + win.height)))

    width = max(1, col_end - col_off)
    height = max(1, row_end - row_off)

    return Window(col_off, row_off, width, height)


def source_window_for_bbox(src, west, south, east, north, pad_pixels=12):
    src_crs = src.crs if src.crs else "EPSG:4326"

    src_west = west
    src_east = east

    if src.bounds.left >= 0 and src.bounds.right > 180:
        if src_west < 0:
            src_west += 360.0
        if src_east < 0:
            src_east += 360.0

    if str(src_crs).upper() not in ("EPSG:4326", "OGC:CRS84"):
        xs, ys = rio_transform(
            "EPSG:4326",
            src_crs,
            [src_west, src_east],
            [south, north],
        )

        left = min(xs)
        right = max(xs)
        bottom = min(ys)
        top = max(ys)
    else:
        left = min(src_west, src_east)
        right = max(src_west, src_east)
        bottom = min(south, north)
        top = max(south, north)

    win = window_from_bounds(
        left,
        bottom,
        right,
        top,
        transform=src.transform,
    )

    win = Window(
        win.col_off - pad_pixels,
        win.row_off - pad_pixels,
        win.width + 2 * pad_pixels,
        win.height + 2 * pad_pixels,
    )

    return clamp_window(win, src)


def render_cache_paths(product, grib_path, west, south, east, north, width):
    grib_mtime = os.path.getmtime(grib_path)

    key_text = json.dumps({
        "product": product,
        "grib_path": grib_path,
        "grib_mtime": grib_mtime,
        "west": round(west, 5),
        "south": round(south, 5),
        "east": round(east, 5),
        "north": round(north, 5),
        "width": int(width),
        "palette_version": RENDER_STYLE_VERSION,
        "zero_values_transparent": True,
    }, sort_keys=True)

    key = hashlib.md5(key_text.encode("utf-8")).hexdigest()

    png_path = os.path.join(CACHE_DIR, f"render_{key}.png")
    meta_path = os.path.join(CACHE_DIR, f"render_{key}.json")

    return png_path, meta_path


def render_png(grib_path, product, west, south, east, north, width):
    width = int(width)
    width = max(800, min(width, 2600))

    cached_png, cached_meta = render_cache_paths(
        product,
        grib_path,
        west,
        south,
        east,
        north,
        width,
    )

    if (
        os.path.exists(cached_png)
        and os.path.exists(cached_meta)
        and time.time() - os.path.getmtime(cached_png) < RENDER_CACHE_TTL_SECONDS
    ):
        return cached_png, read_json(cached_meta)

    xs, ys = rio_transform(
        "EPSG:4326",
        "EPSG:3857",
        [west, east],
        [south, north],
    )

    x0, x1 = min(xs), max(xs)
    y0, y1 = min(ys), max(ys)

    aspect = abs((y1 - y0) / max((x1 - x0), 1.0))
    height = int(width * aspect)
    height = max(450, min(height, 2200))

    dst = np.full((height, width), np.nan, dtype=np.float32)
    dst_transform = from_bounds(x0, y0, x1, y1, width, height)

    with rasterio.open(grib_path) as src:
        src_crs = src.crs if src.crs else "EPSG:4326"

        win = source_window_for_bbox(src, west, south, east, north, pad_pixels=16)

        fill_value = src.nodata if src.nodata is not None else -9999.0

        src_arr = src.read(
            1,
            window=win,
            boundless=False,
            fill_value=fill_value,
        ).astype(np.float32)

        src_arr = clean_mrms_array(src_arr, src.nodata)
        src_transform = src.window_transform(win)

        reproject(
            source=src_arr,
            destination=dst,
            src_transform=src_transform,
            src_crs=src_crs,
            dst_transform=dst_transform,
            dst_crs="EPSG:3857",
            src_nodata=np.nan,
            dst_nodata=np.nan,
            resampling=Resampling.nearest,
        )

    dst_cfs = dst * M3S_PER_KM2_TO_CFS_PER_SQMI
    dst_cfs[dst_cfs < 0] = np.nan

    rgba = STREAMFLOW_CMAP(STREAMFLOW_NORM(dst_cfs))

    rgba[..., 3] = 1.0
    rgba[~np.isfinite(dst_cfs), 3] = 0.0
    rgba[np.isfinite(dst_cfs) & (dst_cfs <= 0.0), 3] = 0.0

    rgba_u8 = np.clip(rgba * 255, 0, 255).astype(np.uint8)
    img = Image.fromarray(rgba_u8, mode="RGBA")
    img.save(cached_png, compress_level=1)

    finite = dst_cfs[np.isfinite(dst_cfs)]

    meta = {
        "product": product,
        "units": "cfs/mi^2",
        "west": west,
        "south": south,
        "east": east,
        "north": north,
        "width": width,
        "height": height,
        "source_windowed": True,
        "png_saved_with": "Pillow compress_level=1",
        "max_cfs_per_smi": float(np.nanmax(finite)) if finite.size else None,
        "generated_utc": now_utc_iso(),
    }

    write_json(cached_meta, meta)

    return cached_png, meta


def token_add_minutes(token, minutes):
    return (token_to_datetime(token) + timedelta(minutes=minutes)).strftime("%Y%m%d-%H%M%S")


def choose_remote_file_strict(product, requested_token, tolerance_seconds=6 * 60):
    product, info = product_info(product)

    if not requested_token:
        return choose_remote_file(product, requested_token=None)

    try:
        best_item, best_delta = nearest_remote_item(product, requested_token, limit=2000)
    except Exception:
        best_item, best_delta = None, None

    if best_item:
        item = annotate_snapped_item(best_item, requested_token, best_delta)
        if best_delta is not None and best_delta > tolerance_seconds:
            item["outside_strict_tolerance"] = True
        return item

    return {
        "product": product,
        "token": None,
        "filename": "latest",
        "url": info["latest_url"],
        "label": f"Latest/current Z - requested {requested_token} unavailable",
        "requested_token": requested_token,
        "snapped_from_requested": True,
        "outside_strict_tolerance": True,
    }


def get_grib_for_product_time_strict(product, requested_token=None, tolerance_seconds=6 * 60):
    product, _ = product_info(product)

    if requested_token:
        local_grib, local_meta = archive_paths(product, requested_token)
        if os.path.exists(local_grib):
            meta = read_json(local_meta)
            meta["source"] = "local_archive"
            return local_grib, meta

    item = choose_remote_file_strict(product, requested_token, tolerance_seconds=tolerance_seconds)

    try:
        grib_path, meta = download_and_unzip_url(product, item["url"])
    except requests.HTTPError as e:
        status_code = getattr(e.response, "status_code", None)
        if requested_token and status_code == 404:
            REMOTE_LIST_CACHE.pop(product, None)
            item = choose_remote_file_strict(product, requested_token, tolerance_seconds=tolerance_seconds)
            grib_path, meta = download_and_unzip_url(product, item["url"])
        else:
            raise

    meta.update({
        "token": item.get("token"),
        "label": item.get("label"),
        "source": "remote_ncep",
        "requested_token": item.get("requested_token", requested_token),
        "snapped_from_requested": bool(item.get("snapped_from_requested", False)),
        "delta_seconds_from_requested": item.get("delta_seconds_from_requested"),
        "outside_strict_tolerance": bool(item.get("outside_strict_tolerance", False)),
    })

    return grib_path, meta


def get_time_window_gribs(product, requested_token=None, window_minutes=30, step_minutes=None, tolerance_seconds=None):
    """Return unique GRIB files covering a trailing time window.

    Faster path: determine all target frames from the cached MRMS directory
    listing, then download/decompress the needed files in parallel. This keeps
    the same scientific meaning as the previous frame-by-frame lookup, but
    avoids many serial network waits for products like 30-min max rain rate.
    """
    product, info = product_info(product)
    step_minutes = int(step_minutes or info.get("step_minutes") or MRMS_TIME_STEP_MINUTES)
    step_minutes = max(1, step_minutes)
    window_minutes = max(0, int(window_minutes))
    tolerance_seconds = float(tolerance_seconds if tolerance_seconds is not None else max(90, step_minutes * 60 * 1.5))

    curr_path, curr_meta = get_grib_for_product_time(product, requested_token)
    current_token = curr_meta.get("token") or requested_token
    if not current_token:
        raise ValueError(f"Could not determine the current {product} token for the trailing {window_minutes}-minute window.")

    requested_tokens = [token_add_minutes(current_token, -minute_offset) for minute_offset in range(0, window_minutes + 1, step_minutes)]
    target_dts = [(token, token_to_datetime(token)) for token in requested_tokens]

    paths_by_token = {}
    metas_by_token = {}
    seen_paths = set()

    def add_source(token, path, meta, allow_outside=False):
        if not path:
            return
        if meta.get("outside_strict_tolerance") and not allow_outside:
            return
        key = (os.path.abspath(path), meta.get("token") or meta.get("requested_token") or token or "")
        if key in seen_paths:
            return
        seen_paths.add(key)
        paths_by_token[token] = path
        metas_by_token[token] = meta

    add_source(current_token, curr_path, curr_meta, allow_outside=True)

    # Build a local/remote source list without downloading anything yet.
    jobs = []
    jobs_seen_urls = set()
    remote_items = []
    try:
        # The directory list is cached for REMOTE_LIST_TTL_SECONDS, so this is
        # usually a memory lookup after the first request.
        remote_items = list_remote_files(product, limit=2500)
    except Exception as e:
        print(f"[{product} trailing window directory-list fallback] {e}")

    for target_token, target_dt in target_dts:
        if target_token == current_token:
            continue

        local_grib, local_meta_path = archive_paths(product, target_token)
        if os.path.exists(local_grib):
            meta = read_json(local_meta_path)
            meta["source"] = "local_archive"
            add_source(target_token, local_grib, meta, allow_outside=True)
            continue

        item = None
        best_delta = None

        if remote_items:
            for candidate in remote_items:
                try:
                    delta = abs((token_to_datetime(candidate["token"]) - target_dt).total_seconds())
                except Exception:
                    continue
                if best_delta is None or delta < best_delta:
                    best_delta = delta
                    item = candidate
        else:
            try:
                item, best_delta = nearest_remote_item(product, target_token, limit=2000)
            except Exception:
                item, best_delta = None, None

        if not item or best_delta is None or best_delta > tolerance_seconds:
            continue

        item = annotate_snapped_item(item, target_token, best_delta)
        url = item.get("url")
        if not url or url in jobs_seen_urls:
            continue
        jobs_seen_urls.add(url)
        jobs.append((target_token, item))

    def download_job(job):
        target_token, item = job
        path, meta = download_and_unzip_url(product, item["url"])
        meta.update({
            "token": item.get("token"),
            "label": item.get("label"),
            "source": "remote_ncep",
            "requested_token": item.get("requested_token", target_token),
            "snapped_from_requested": bool(item.get("snapped_from_requested", False)),
            "delta_seconds_from_requested": item.get("delta_seconds_from_requested"),
            "outside_strict_tolerance": bool(item.get("outside_strict_tolerance", False)),
        })
        return target_token, path, meta

    if jobs:
        workers = max(1, min(TIME_WINDOW_DOWNLOAD_WORKERS, len(jobs)))
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
            future_map = {executor.submit(download_job, job): job for job in jobs}
            for fut in concurrent.futures.as_completed(future_map):
                target_token, item = future_map[fut]
                try:
                    token, path, meta = fut.result()
                    add_source(token, path, meta, allow_outside=False)
                except Exception as e:
                    print(f"[{product} trailing window fetch skipped] {target_token}: {e}")

    # Return newest-to-oldest, matching the previous function where metas[0]
    # represented the current/ending frame.
    ordered = []
    for token in requested_tokens:
        path = paths_by_token.get(token)
        meta = metas_by_token.get(token)
        if path and meta:
            ordered.append((token, path, meta))

    if not ordered:
        raise ValueError(f"No usable {product} files found for the trailing {window_minutes}-minute window.")

    paths = [item[1] for item in ordered]
    metas = [item[2] for item in ordered]
    return current_token, paths, metas

def webmercator_grid(west, south, east, north, width):
    width = int(width)
    width = max(500, min(width, 2600))

    xs, ys = rio_transform(
        "EPSG:4326",
        "EPSG:3857",
        [west, east],
        [south, north],
    )

    x0, x1 = min(xs), max(xs)
    y0, y1 = min(ys), max(ys)

    aspect = abs((y1 - y0) / max((x1 - x0), 1.0))
    height = int(width * aspect)
    height = max(300, min(height, 2200))

    dst_transform = from_bounds(x0, y0, x1, y1, width, height)
    return width, height, dst_transform, (x0, y0, x1, y1)


def read_grib_to_webmercator_grid(grib_path, west, south, east, north, width, height, dst_transform):
    dst = np.full((height, width), np.nan, dtype=np.float32)

    with rasterio.open(grib_path) as src:
        src_crs = src.crs if src.crs else "EPSG:4326"
        win = source_window_for_bbox(src, west, south, east, north, pad_pixels=16)
        fill_value = src.nodata if src.nodata is not None else -9999.0

        src_arr = src.read(
            1,
            window=win,
            boundless=False,
            fill_value=fill_value,
        ).astype(np.float32)

        src_arr = clean_mrms_array(src_arr, src.nodata)
        src_transform = src.window_transform(win)

        reproject(
            source=src_arr,
            destination=dst,
            src_transform=src_transform,
            src_crs=src_crs,
            dst_transform=dst_transform,
            dst_crs="EPSG:3857",
            src_nodata=np.nan,
            dst_nodata=np.nan,
            resampling=Resampling.nearest,
        )

    return dst


def render_param_cache_paths(param, product, grib_paths, west, south, east, north, width, extra=None):
    path_info = []
    for path in grib_paths:
        path_info.append({
            "path": path,
            "mtime": os.path.getmtime(path) if os.path.exists(path) else None,
        })

    key_text = json.dumps({
        "param": param,
        "product": product,
        "grib_paths": path_info,
        "west": round(west, 5),
        "south": round(south, 5),
        "east": round(east, 5),
        "north": round(north, 5),
        "width": int(width),
        "extra": extra or {},
    }, sort_keys=True)

    key = hashlib.md5(key_text.encode("utf-8")).hexdigest()
    png_path = os.path.join(CACHE_DIR, f"render_param_{key}.png")
    meta_path = os.path.join(CACHE_DIR, f"render_param_{key}.json")
    return png_path, meta_path


def apply_zero_transparency(rgba, arr, *, signed=False, eps=1.0e-6):
    """Make true zero values transparent while preserving valid nonzero data.

For signed difference products, use a tiny absolute-value tolerance so
subtraction/reprojection roundoff does not leave salt-and-pepper zero pixels.
For accumulation/rate/streamflow products, all values <= 0 are transparent.
    """
    finite = np.isfinite(arr)
    rgba[~finite, 3] = 0.0
    if signed:
        rgba[finite & (np.abs(arr) <= eps), 3] = 0.0
    else:
        rgba[finite & (arr <= 0.0), 3] = 0.0
    return rgba


def colorize_streamflow_cfs(arr_cfs):
    arr = arr_cfs.copy()
    arr[arr < 0] = np.nan
    rgba = STREAMFLOW_CMAP(STREAMFLOW_NORM(arr))
    rgba[..., 3] = 1.0
    rgba = apply_zero_transparency(rgba, arr, signed=False)
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def colorize_difference_cfs(diff_cfs):
    arr = diff_cfs.copy()
    rgba = DIFF_CMAP(DIFF_NORM(arr))
    rgba[..., 3] = 0.88
    rgba = apply_zero_transparency(rgba, arr, signed=True)
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def file_time_from_meta(meta, fallback="Latest/current Z"):
    file_time = meta.get("label") or meta.get("last_modified", "") or fallback
    text = str(file_time)
    if text and not text.endswith("Z") and "UTC" not in text and "requested" not in text:
        text = f"{text}Z"
    return text




def convert_native_value_to_display(raw_value, pinfo):
    if raw_value is None:
        return None
    style = pinfo.get("style", "streamflow")
    if style == "streamflow":
        return float(raw_value) * M3S_PER_KM2_TO_CFS_PER_SQMI
    if style in ("qpe", "rainrate"):
        return float(raw_value) * MM_TO_IN
    return float(raw_value)


def convert_native_array_to_display(raw_arr, pinfo):
    style = pinfo.get("style", "streamflow")
    arr = raw_arr.astype(np.float32).copy()
    if style == "streamflow":
        arr = arr * M3S_PER_KM2_TO_CFS_PER_SQMI
        arr[arr < 0] = np.nan
    elif style in ("qpe", "rainrate"):
        arr = arr * MM_TO_IN
        arr[arr < 0] = np.nan
    return arr


def colorize_mrms_qpe(arr_in):
    arr = arr_in.copy()
    arr[arr < 0] = np.nan
    rgba = MRMS_QPE_CMAP(MRMS_QPE_NORM(arr))
    rgba[..., 3] = 0.92
    rgba = apply_zero_transparency(rgba, arr, signed=False)
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def colorize_mrms_qpe_difference(diff_in):
    arr = diff_in.astype(np.float32).copy()
    rgba = MRMS_QPE_DIFF_CMAP(MRMS_QPE_DIFF_NORM(arr))
    rgba[..., 3] = 0.90
    rgba = apply_zero_transparency(rgba, arr, signed=True)
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def colorize_mrms_rainrate(arr_inhr):
    arr = arr_inhr.copy()
    arr[arr < 0] = np.nan
    rgba = MRMS_RAINRATE_CMAP(MRMS_RAINRATE_NORM(arr))
    rgba[..., 3] = 0.92
    rgba = apply_zero_transparency(rgba, arr, signed=False)
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def colorize_mrms_reflectivity(arr_dbz):
    arr = arr_dbz.astype(np.float32).copy()
    rgba = MRMS_REFL_CMAP(MRMS_REFL_NORM(arr))
    rgba[..., 3] = 0.95
    rgba[~np.isfinite(arr), 3] = 0.0
    rgba[np.isfinite(arr) & (arr < 5.0), 3] = 0.0
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def resolve_parameter_sources(param, product, requested_token):
    param, pinfo = parameter_info(param, fallback_product=product)

    if pinfo["kind"] == "raw":
        raw_product = pinfo.get("product") or product or param
        raw_product, _ = product_info(raw_product)
        grib_path, meta = get_grib_for_product_time(raw_product, requested_token)
        return {
            "param": param,
            "product": raw_product,
            "kind": "raw",
            "display": pinfo["display"],
            "units": pinfo.get("units", ""),
            "native_units": pinfo.get("native_units", ""),
            "style": pinfo.get("style", "streamflow"),
            "grib_paths": [grib_path],
            "metas": [meta],
            "file_time_utc": file_time_from_meta(meta),
            "component_times": {raw_product: file_time_from_meta(meta)},
        }

    if param == "CREST_DIFF_10M":
        curr_path, curr_meta = get_grib_for_product_time("CREST", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current CREST token for the 10-minute difference.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("CREST", prev_token, tolerance_seconds=6 * 60)
        return {
            "param": param,
            "product": "CREST",
            "kind": "difference",
            "display": pinfo["display"],
            "grib_paths": [curr_path, prev_path],
            "metas": [curr_meta, prev_meta],
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {
                "current_crest": file_time_from_meta(curr_meta),
                "previous_crest": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
        }

    if param == "RAINRATE_MAX_30M":
        current_token, paths, metas = get_time_window_gribs(
            "PRECIPRATE",
            requested_token=requested_token,
            window_minutes=30,
            step_minutes=2,
            tolerance_seconds=3 * 60,
        )
        return {
            "param": param,
            "product": "RAINRATE_MAX_30M",
            "kind": "derived_max",
            "display": pinfo["display"],
            "units": pinfo.get("units", "in/hr"),
            "native_units": pinfo.get("native_units", "mm/hr"),
            "style": pinfo.get("style", "rainrate"),
            "grib_paths": paths,
            "metas": metas,
            "file_time_utc": f"max of {len(paths)} PrecipRate frames ending {file_time_from_meta(metas[0])}",
            "component_times": {
                "window_minutes": 30,
                "frame_count": len(paths),
                "current_token": current_token,
                "frames": [file_time_from_meta(meta) for meta in metas],
            },
        }

    if param == "QPE1H_DIFF_30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE1H", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current QPE1H token for the 30-minute difference.")
        prev_token = token_add_minutes(current_token, -30)
        prev_path, prev_meta = get_grib_for_product_time_strict("QPE1H", prev_token, tolerance_seconds=8 * 60)
        return {
            "param": param,
            "product": "QPE1H",
            "kind": "difference",
            "display": pinfo["display"],
            "units": pinfo.get("units", "in"),
            "native_units": pinfo.get("native_units", "mm"),
            "style": pinfo.get("style", "qpe_difference"),
            "grib_paths": [curr_path, prev_path],
            "metas": [curr_meta, prev_meta],
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {
                "current_qpe1h": file_time_from_meta(curr_meta),
                "previous_qpe1h_30m": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
        }

    if param == "QPE30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE15M", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current QPE15M token for the 30-minute total.")
        prev_token = token_add_minutes(current_token, -15)
        prev_path, prev_meta = get_grib_for_product_time_strict("QPE15M", prev_token, tolerance_seconds=8 * 60)
        return {
            "param": param,
            "product": "QPE30M",
            "kind": "derived_sum",
            "display": pinfo["display"],
            "units": pinfo.get("units", "in"),
            "native_units": pinfo.get("native_units", "mm"),
            "style": pinfo.get("style", "qpe"),
            "grib_paths": [curr_path, prev_path],
            "metas": [curr_meta, prev_meta],
            "file_time_utc": f"{file_time_from_meta(prev_meta)} plus {file_time_from_meta(curr_meta)}",
            "component_times": {
                "current_qpe15m": file_time_from_meta(curr_meta),
                "previous_qpe15m": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
        }

    if param == "HP_MINUS_CREST":
        hp_path, hp_meta = get_grib_for_product_time("HP", requested_token)
        crest_path, crest_meta = get_grib_for_product_time("CREST", requested_token)
        return {
            "param": param,
            "product": "HP_MINUS_CREST",
            "kind": "difference",
            "display": pinfo["display"],
            "grib_paths": [hp_path, crest_path],
            "metas": [hp_meta, crest_meta],
            "file_time_utc": f"HP {file_time_from_meta(hp_meta)} minus CREST {file_time_from_meta(crest_meta)}",
            "component_times": {
                "hp": file_time_from_meta(hp_meta),
                "crest": file_time_from_meta(crest_meta),
            },
        }

    raise ValueError(f"Unsupported parameter '{param}'")

def compute_parameter_array(param, product, requested_token, west, south, east, north, width):
    param, pinfo = parameter_info(param, fallback_product=product)
    width, height, dst_transform, merc_bounds = webmercator_grid(west, south, east, north, width)

    if pinfo["kind"] == "raw":
        raw_product = pinfo.get("product") or product or param
        raw_product, _ = product_info(raw_product)
        grib_path, meta = get_grib_for_product_time(raw_product, requested_token)
        raw = read_grib_to_webmercator_grid(grib_path, west, south, east, north, width, height, dst_transform)
        arr_display = convert_native_array_to_display(raw, pinfo)
        return {
            "param": param,
            "product": raw_product,
            "kind": "raw",
            "display": pinfo["display"],
            "units": pinfo.get("units", ""),
            "native_units": pinfo.get("native_units", ""),
            "style": pinfo.get("style", "streamflow"),
            "arr_cfs": arr_display,
            "arr_m3s_per_km2": raw,
            "width": width,
            "height": height,
            "dst_transform": dst_transform,
            "merc_bounds": merc_bounds,
            "grib_paths": [grib_path],
            "meta": meta,
            "file_time_utc": file_time_from_meta(meta),
            "component_times": {raw_product: file_time_from_meta(meta)},
        }

    if param == "CREST_DIFF_10M":
        curr_path, curr_meta = get_grib_for_product_time("CREST", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current CREST token for the 10-minute difference.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("CREST", prev_token, tolerance_seconds=6 * 60)

        curr = read_grib_to_webmercator_grid(curr_path, west, south, east, north, width, height, dst_transform)
        prev = read_grib_to_webmercator_grid(prev_path, west, south, east, north, width, height, dst_transform)
        diff_raw = curr - prev
        diff_cfs = diff_raw * M3S_PER_KM2_TO_CFS_PER_SQMI

        return {
            "param": param,
            "product": "CREST",
            "kind": "difference",
            "display": pinfo["display"],
            "units": pinfo.get("units", "cfs/mi^2"),
            "native_units": "m^3/s/km^2",
            "arr_cfs": diff_cfs,
            "arr_m3s_per_km2": diff_raw,
            "width": width,
            "height": height,
            "dst_transform": dst_transform,
            "merc_bounds": merc_bounds,
            "grib_paths": [curr_path, prev_path],
            "meta": curr_meta,
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {
                "current_crest": file_time_from_meta(curr_meta),
                "previous_crest": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
        }

    if param == "RAINRATE_MAX_30M":
        current_token, paths, metas = get_time_window_gribs(
            "PRECIPRATE",
            requested_token=requested_token,
            window_minutes=30,
            step_minutes=2,
            tolerance_seconds=3 * 60,
        )

        max_raw = None
        for frame_path in paths:
            frame = read_grib_to_webmercator_grid(frame_path, west, south, east, north, width, height, dst_transform)
            max_raw = frame if max_raw is None else np.fmax(max_raw, frame)

        max_inhr = max_raw * MM_TO_IN
        max_inhr[max_inhr < 0] = np.nan

        return {
            "param": param,
            "product": "RAINRATE_MAX_30M",
            "kind": "derived_max",
            "display": pinfo["display"],
            "units": pinfo.get("units", "in/hr"),
            "native_units": pinfo.get("native_units", "mm/hr"),
            "style": pinfo.get("style", "rainrate"),
            "arr_cfs": max_inhr,
            "arr_m3s_per_km2": max_raw,
            "width": width,
            "height": height,
            "dst_transform": dst_transform,
            "merc_bounds": merc_bounds,
            "grib_paths": paths,
            "meta": metas[0],
            "file_time_utc": f"max of {len(paths)} PrecipRate frames ending {file_time_from_meta(metas[0])}",
            "component_times": {
                "window_minutes": 30,
                "frame_count": len(paths),
                "current_token": current_token,
                "frames": [file_time_from_meta(meta) for meta in metas],
            },
        }

    if param == "QPE1H_DIFF_30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE1H", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current QPE1H token for the 30-minute difference.")
        prev_token = token_add_minutes(current_token, -30)
        prev_path, prev_meta = get_grib_for_product_time_strict("QPE1H", prev_token, tolerance_seconds=8 * 60)

        curr = read_grib_to_webmercator_grid(curr_path, west, south, east, north, width, height, dst_transform)
        prev = read_grib_to_webmercator_grid(prev_path, west, south, east, north, width, height, dst_transform)
        diff_raw = curr - prev
        diff_in = diff_raw * MM_TO_IN

        return {
            "param": param,
            "product": "QPE1H",
            "kind": "difference",
            "display": pinfo["display"],
            "units": pinfo.get("units", "in"),
            "native_units": pinfo.get("native_units", "mm"),
            "style": pinfo.get("style", "qpe_difference"),
            "arr_cfs": diff_in,
            "arr_m3s_per_km2": diff_raw,
            "width": width,
            "height": height,
            "dst_transform": dst_transform,
            "merc_bounds": merc_bounds,
            "grib_paths": [curr_path, prev_path],
            "meta": curr_meta,
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {
                "current_qpe1h": file_time_from_meta(curr_meta),
                "previous_qpe1h_30m": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
        }

    if param == "QPE30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE15M", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current QPE15M token for the 30-minute total.")
        prev_token = token_add_minutes(current_token, -15)
        prev_path, prev_meta = get_grib_for_product_time_strict("QPE15M", prev_token, tolerance_seconds=8 * 60)

        curr = read_grib_to_webmercator_grid(curr_path, west, south, east, north, width, height, dst_transform)
        prev = read_grib_to_webmercator_grid(prev_path, west, south, east, north, width, height, dst_transform)
        total_raw = curr + prev
        total_in = total_raw * MM_TO_IN
        total_in[total_in < 0] = np.nan

        return {
            "param": param,
            "product": "QPE30M",
            "kind": "derived_sum",
            "display": pinfo["display"],
            "units": pinfo.get("units", "in"),
            "native_units": pinfo.get("native_units", "mm"),
            "style": pinfo.get("style", "qpe"),
            "arr_cfs": total_in,
            "arr_m3s_per_km2": total_raw,
            "width": width,
            "height": height,
            "dst_transform": dst_transform,
            "merc_bounds": merc_bounds,
            "grib_paths": [curr_path, prev_path],
            "meta": curr_meta,
            "file_time_utc": f"{file_time_from_meta(prev_meta)} plus {file_time_from_meta(curr_meta)}",
            "component_times": {
                "current_qpe15m": file_time_from_meta(curr_meta),
                "previous_qpe15m": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
        }

    if param == "HP_MINUS_CREST":
        hp_path, hp_meta = get_grib_for_product_time("HP", requested_token)
        crest_path, crest_meta = get_grib_for_product_time("CREST", requested_token)

        hp = read_grib_to_webmercator_grid(hp_path, west, south, east, north, width, height, dst_transform)
        crest = read_grib_to_webmercator_grid(crest_path, west, south, east, north, width, height, dst_transform)
        diff_raw = hp - crest
        diff_cfs = diff_raw * M3S_PER_KM2_TO_CFS_PER_SQMI

        return {
            "param": param,
            "product": "HP_MINUS_CREST",
            "kind": "difference",
            "display": pinfo["display"],
            "units": pinfo.get("units", "cfs/mi^2"),
            "native_units": "m^3/s/km^2",
            "arr_cfs": diff_cfs,
            "arr_m3s_per_km2": diff_raw,
            "width": width,
            "height": height,
            "dst_transform": dst_transform,
            "merc_bounds": merc_bounds,
            "grib_paths": [hp_path, crest_path],
            "meta": hp_meta,
            "file_time_utc": f"HP {file_time_from_meta(hp_meta)} minus CREST {file_time_from_meta(crest_meta)}",
            "component_times": {
                "hp": file_time_from_meta(hp_meta),
                "crest": file_time_from_meta(crest_meta),
            },
        }

    raise ValueError(f"Unsupported parameter '{param}'")


def render_parameter_png(param, product, requested_token, west, south, east, north, width):
    param, pinfo = parameter_info(param, fallback_product=product)
    width = int(width)

    # Resolve source files before reading/reprojecting so a cached PNG can return immediately.
    sources = resolve_parameter_sources(param, product, requested_token)
    cache_width = max(500, min(width, 2600))

    cached_png, cached_meta = render_param_cache_paths(
        param,
        sources.get("product") or product,
        sources["grib_paths"],
        west,
        south,
        east,
        north,
        cache_width,
        extra={
            "kind": sources["kind"],
            "style": sources.get("style", pinfo.get("style", "")),
            "palette_version": RENDER_STYLE_VERSION,
            "component_times": sources.get("component_times", {}),
        },
    )

    if (
        os.path.exists(cached_png)
        and os.path.exists(cached_meta)
        and time.time() - os.path.getmtime(cached_png) < RENDER_CACHE_TTL_SECONDS
    ):
        return cached_png, read_json(cached_meta)

    # Single-flight each rendered image so simultaneous panel/browser requests do
    # not do the same reprojection/colorization twice.
    render_lock = keyed_lock(RENDER_LOCKS, cached_png)
    with render_lock:
        if (
            os.path.exists(cached_png)
            and os.path.exists(cached_meta)
            and time.time() - os.path.getmtime(cached_png) < RENDER_CACHE_TTL_SECONDS
        ):
            return cached_png, read_json(cached_meta)

        data = compute_parameter_array(param, product, requested_token, west, south, east, north, width)
        arr_cfs = data["arr_cfs"]

        if data.get("style") == "qpe_difference":
            rgba_u8 = colorize_mrms_qpe_difference(arr_cfs)
        elif data["kind"] == "difference":
            rgba_u8 = colorize_difference_cfs(arr_cfs)
        elif data.get("style") == "rainrate":
            rgba_u8 = colorize_mrms_rainrate(arr_cfs)
        elif data.get("style") == "qpe":
            rgba_u8 = colorize_mrms_qpe(arr_cfs)
        elif data.get("style") == "reflectivity":
            rgba_u8 = colorize_mrms_reflectivity(arr_cfs)
        else:
            rgba_u8 = colorize_streamflow_cfs(arr_cfs)

        img = Image.fromarray(rgba_u8, mode="RGBA")
        img.save(cached_png, compress_level=1)

        finite = arr_cfs[np.isfinite(arr_cfs)]

        meta = {
            "param": param,
            "product": data.get("product") or product,
            "display": data["display"],
            "kind": data["kind"],
            "units": data.get("units", pinfo.get("units", "")),
            "west": west,
            "south": south,
            "east": east,
            "north": north,
            "width": data["width"],
            "height": data["height"],
            "source_windowed": True,
            "png_saved_with": "Pillow compress_level=1",
            "max_cfs_per_smi": float(np.nanmax(finite)) if finite.size and pinfo.get("style") == "streamflow" else None,
            "min_cfs_per_smi": float(np.nanmin(finite)) if finite.size and pinfo.get("style") == "streamflow" else None,
            "max_display_value": float(np.nanmax(finite)) if finite.size else None,
            "min_display_value": float(np.nanmin(finite)) if finite.size else None,
            "file_time_utc": data.get("file_time_utc", ""),
            "native_units": data.get("native_units", ""),
            "component_times": data.get("component_times", {}),
            "generated_utc": now_utc_iso(),
        }

        write_json(cached_meta, meta)
        return cached_png, meta

def sample_parameter_value(param, product, requested_token, lat, lon):
    param, pinfo = parameter_info(param, fallback_product=product)

    if pinfo["kind"] == "raw":
        raw_product = pinfo.get("product") or product or param
        grib_path, meta = get_grib_for_product_time(raw_product, requested_token)
        native_val = sample_native_value(grib_path, lat, lon)
        if native_val is None:
            return None, file_time_from_meta(meta)
        return {
            "native_value": native_val,
            "display_value": convert_native_value_to_display(native_val, pinfo),
            "native_units": pinfo.get("native_units", ""),
            "display_units": pinfo.get("units", ""),
            "value_m3s_per_km2": native_val,
            "value_cfs_per_smi": convert_native_value_to_display(native_val, pinfo),
        }, file_time_from_meta(meta)

    if param == "CREST_DIFF_10M":
        curr_path, curr_meta = get_grib_for_product_time("CREST", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine current CREST token for 10-minute difference.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("CREST", prev_token, tolerance_seconds=6 * 60)
        curr_val = sample_native_value(curr_path, lat, lon)
        prev_val = sample_native_value(prev_path, lat, lon)

        if curr_val is None or prev_val is None:
            return None, f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}"

        diff_m3s = curr_val - prev_val
        dv = diff_m3s * M3S_PER_KM2_TO_CFS_PER_SQMI
        return {
            "value_m3s_per_km2": diff_m3s,
            "value_cfs_per_smi": dv,
            "display_value": dv,
            "display_units": pinfo.get("units", "cfs/mi^2"),
            "native_value": diff_m3s,
            "native_units": "m^3/s/km^2",
        }, f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}"

    if param == "RAINRATE_MAX_30M":
        current_token, paths, metas = get_time_window_gribs(
            "PRECIPRATE",
            requested_token=requested_token,
            window_minutes=30,
            step_minutes=2,
            tolerance_seconds=3 * 60,
        )
        vals = []
        for frame_path in paths:
            val = sample_native_value(frame_path, lat, lon)
            if val is not None and np.isfinite(val):
                vals.append(float(val))

        if not vals:
            return None, f"max of {len(paths)} PrecipRate frames ending {file_time_from_meta(metas[0])}"

        max_mmhr = max(vals)
        if max_mmhr < 0:
            return None, f"max of {len(paths)} PrecipRate frames ending {file_time_from_meta(metas[0])}"

        dv = max_mmhr * MM_TO_IN
        return {
            "value_m3s_per_km2": max_mmhr,
            "value_cfs_per_smi": dv,
            "display_value": dv,
            "display_units": pinfo.get("units", "in/hr"),
            "native_value": max_mmhr,
            "native_units": pinfo.get("native_units", "mm/hr"),
        }, f"max of {len(paths)} PrecipRate frames ending {file_time_from_meta(metas[0])}"

    if param == "QPE1H_DIFF_30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE1H", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine current QPE1H token for 30-minute difference.")
        prev_token = token_add_minutes(current_token, -30)
        prev_path, prev_meta = get_grib_for_product_time_strict("QPE1H", prev_token, tolerance_seconds=8 * 60)
        curr_val = sample_native_value(curr_path, lat, lon)
        prev_val = sample_native_value(prev_path, lat, lon)

        if curr_val is None or prev_val is None:
            return None, f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}"

        diff_mm = curr_val - prev_val
        dv = diff_mm * MM_TO_IN
        return {
            "value_m3s_per_km2": diff_mm,
            "value_cfs_per_smi": dv,
            "display_value": dv,
            "display_units": pinfo.get("units", "in"),
            "native_value": diff_mm,
            "native_units": pinfo.get("native_units", "mm"),
        }, f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}"

    if param == "QPE30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE15M", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine current QPE15M token for 30-minute total.")
        prev_token = token_add_minutes(current_token, -15)
        prev_path, prev_meta = get_grib_for_product_time_strict("QPE15M", prev_token, tolerance_seconds=8 * 60)
        curr_val = sample_native_value(curr_path, lat, lon)
        prev_val = sample_native_value(prev_path, lat, lon)

        if curr_val is None or prev_val is None:
            return None, f"{file_time_from_meta(prev_meta)} plus {file_time_from_meta(curr_meta)}"

        total_mm = curr_val + prev_val
        if total_mm < 0:
            return None, f"{file_time_from_meta(prev_meta)} plus {file_time_from_meta(curr_meta)}"
        dv = total_mm * MM_TO_IN
        return {
            "value_m3s_per_km2": total_mm,
            "value_cfs_per_smi": dv,
            "display_value": dv,
            "display_units": pinfo.get("units", "in"),
            "native_value": total_mm,
            "native_units": pinfo.get("native_units", "mm"),
        }, f"{file_time_from_meta(prev_meta)} plus {file_time_from_meta(curr_meta)}"

    if param == "HP_MINUS_CREST":
        hp_path, hp_meta = get_grib_for_product_time("HP", requested_token)
        crest_path, crest_meta = get_grib_for_product_time("CREST", requested_token)
        hp_val = sample_native_value(hp_path, lat, lon)
        crest_val = sample_native_value(crest_path, lat, lon)

        if hp_val is None or crest_val is None:
            return None, f"HP {file_time_from_meta(hp_meta)} minus CREST {file_time_from_meta(crest_meta)}"

        diff_m3s = hp_val - crest_val
        dv = diff_m3s * M3S_PER_KM2_TO_CFS_PER_SQMI
        return {
            "value_m3s_per_km2": diff_m3s,
            "value_cfs_per_smi": dv,
            "display_value": dv,
            "display_units": pinfo.get("units", "cfs/mi^2"),
            "native_value": diff_m3s,
            "native_units": "m^3/s/km^2",
        }, f"HP {file_time_from_meta(hp_meta)} minus CREST {file_time_from_meta(crest_meta)}"

    raise ValueError(f"Unsupported parameter '{param}'")


def pixel_latlon_from_webmercator_transform(dst_transform, row, col):
    x, y = dst_transform * (col + 0.5, row + 0.5)
    lons, lats = rio_transform("EPSG:3857", "EPSG:4326", [x], [y])
    return float(lats[0]), float(lons[0])


def find_extreme_value_for_parameter(param, product, requested_token, west, south, east, north, width, min_cfs=0.0):
    param, pinfo = parameter_info(param, fallback_product=product)

    if pinfo["kind"] == "raw":
        raw_product = pinfo.get("product") or product or param
        grib_path, meta = get_grib_for_product_time(raw_product, requested_token)
        value = find_max_value_in_bbox(grib_path, raw_product, west, south, east, north, pinfo, min_threshold=min_cfs)
        return value, file_time_from_meta(meta), "max"

    data = compute_parameter_array(param, product, requested_token, west, south, east, north, width)
    arr_cfs = data["arr_cfs"]
    arr_raw = data["arr_m3s_per_km2"]

    finite_mask = np.isfinite(arr_cfs)
    if min_cfs > 0:
        finite_mask &= np.abs(arr_cfs) >= min_cfs

    if not np.any(finite_mask):
        return None, data.get("file_time_utc", ""), "extreme"

    work = np.where(finite_mask, np.abs(arr_cfs), np.nan)
    row, col = np.unravel_index(np.nanargmax(work), work.shape)
    lat, lon = pixel_latlon_from_webmercator_transform(data["dst_transform"], int(row), int(col))

    native_val = float(arr_raw[row, col]) if np.isfinite(arr_raw[row, col]) else None
    display_val = float(arr_cfs[row, col])
    value = {
        "lat": lat,
        "lon": lon,
        "value_m3s_per_km2": native_val,
        "value_cfs_per_smi": display_val,
        "display_value": display_val,
        "display_units": pinfo.get("units", "cfs/mi^2"),
        "native_value": native_val,
        "native_units": pinfo.get("native_units", "m^3/s/km^2"),
        "source_row": int(row),
        "source_col": int(col),
    }

    return value, data.get("file_time_utc", ""), "extreme"


def circle_bbox_from_radius(lat, lon, radius_m):
    radius_m = max(1.0, float(radius_m))
    lat = float(lat)
    lon = float(lon)
    dlat = radius_m / 111320.0
    coslat = max(0.15, abs(math.cos(math.radians(lat))))
    dlon = radius_m / (111320.0 * coslat)
    return lon - dlon, lat - dlat, lon + dlon, lat + dlat


def streamflow_area_coverage_breakdown(vals):
    vals = np.asarray(vals, dtype=np.float64)
    vals = vals[np.isfinite(vals)]
    if vals.size == 0:
        return []

    vmax = float(np.nanmax(vals))
    top_threshold = int(math.floor((vmax - 1.0e-9) / 100.0) * 100)
    thresholds = []
    for threshold in range(top_threshold, max(top_threshold - 300, 0), -100):
        if threshold >= 100:
            count = int(np.count_nonzero(vals > float(threshold)))
            pct = 100.0 * count / float(vals.size)
            thresholds.append({
                "threshold": float(threshold),
                "percent": float(pct),
                "count": count,
                "total": int(vals.size),
            })
    return thresholds[:3]


def summarize_area_average_values(vals, param, product, pinfo, data, extra=None):
    extra = extra or {}
    if vals is None or vals.size == 0:
        payload = {
            "found": False,
            "param": param,
            "product": data.get("product") or product,
            "display": data.get("display", pinfo.get("display", param)),
            "display_units": pinfo.get("units", ""),
            "native_units": data.get("native_units", pinfo.get("native_units", "")),
            "file_time_utc": data.get("file_time_utc", ""),
            "count": 0,
        }
        payload.update(extra)
        return payload

    vals = vals.astype(np.float64)
    vmin = float(np.nanmin(vals))
    vmax = float(np.nanmax(vals))
    est_low = vmin + (vmax - vmin) / 3.0
    est_high = vmin + 2.0 * (vmax - vmin) / 3.0
    payload = {
        "found": True,
        "param": param,
        "product": data.get("product") or product,
        "display": data.get("display", pinfo.get("display", param)),
        "display_units": pinfo.get("units", ""),
        "native_units": data.get("native_units", pinfo.get("native_units", "")),
        "file_time_utc": data.get("file_time_utc", ""),
        "mean": float(np.nanmean(vals)),
        "median": float(np.nanmedian(vals)),
        "min": vmin,
        "max": vmax,
        "estimate_low": float(est_low),
        "estimate_high": float(est_high),
        "count": int(vals.size),
    }
    if str(param).upper() == "CREST" and pinfo.get("style") == "streamflow":
        payload["coverage_thresholds"] = streamflow_area_coverage_breakdown(vals)
    payload.update(extra)
    return payload


def area_average_for_parameter(param, product, requested_token, lat, lon, radius_m):
    param, pinfo = parameter_info(param, fallback_product=product)
    west, south, east, north = circle_bbox_from_radius(lat, lon, radius_m)

    width = int(max(320, min(1000, (float(radius_m) * 2.0) / 250.0)))
    data = compute_parameter_array(param, product, requested_token, west, south, east, north, width)
    arr = data["arr_cfs"]

    cx, cy = rio_transform("EPSG:4326", "EPSG:3857", [float(lon)], [float(lat)])
    cx = float(cx[0])
    cy = float(cy[0])

    transform = data["dst_transform"]
    rows = np.arange(data["height"], dtype=np.float64) + 0.5
    cols = np.arange(data["width"], dtype=np.float64) + 0.5
    xs = transform.c + cols * transform.a
    ys = transform.f + rows * transform.e

    dx2 = (xs[None, :] - cx) ** 2
    dy2 = (ys[:, None] - cy) ** 2
    mask = (dx2 + dy2) <= float(radius_m) ** 2
    finite = mask & np.isfinite(arr)
    vals = arr[finite] if np.any(finite) else np.array([], dtype=np.float64)
    return summarize_area_average_values(vals, param, product, pinfo, data, {
        "radius_m": float(radius_m),
        "lat": float(lat),
        "lon": float(lon),
        "west": west,
        "south": south,
        "east": east,
        "north": north,
    })


def area_average_for_polygon(param, product, requested_token, vertices):
    if not vertices or len(vertices) < 3:
        raise ValueError("At least 3 vertices are required")

    lats = [float(v["lat"]) for v in vertices]
    lons = [float(v["lon"]) for v in vertices]
    west, east = min(lons), max(lons)
    south, north = min(lats), max(lats)
    param, pinfo = parameter_info(param, fallback_product=product)

    vx, vy = rio_transform("EPSG:4326", "EPSG:3857", lons, lats)
    path = MplPath(np.column_stack([vx, vy]), closed=True)
    width = int(max(320, min(1200, max((east - west) * 111320.0, (north - south) * 111320.0) / 250.0)))
    data = compute_parameter_array(param, product, requested_token, west, south, east, north, width)
    arr = data["arr_cfs"]
    transform = data["dst_transform"]
    rows = np.arange(data["height"], dtype=np.float64) + 0.5
    cols = np.arange(data["width"], dtype=np.float64) + 0.5
    xs = transform.c + cols * transform.a
    ys = transform.f + rows * transform.e
    grid_x, grid_y = np.meshgrid(xs, ys)
    points = np.column_stack([grid_x.ravel(), grid_y.ravel()])
    mask = path.contains_points(points, radius=1e-9).reshape(arr.shape)
    finite = mask & np.isfinite(arr)
    vals = arr[finite] if np.any(finite) else np.array([], dtype=np.float64)
    return summarize_area_average_values(vals, param, product, pinfo, data, {
        "vertices": vertices,
        "west": west,
        "south": south,
        "east": east,
        "north": north,
    })


def normalize_lon_for_src(src, lon):
    left = float(src.bounds.left)
    right = float(src.bounds.right)

    if left >= 0 and right > 180 and lon < 0:
        return lon + 360.0

    if right <= 180 and lon > 180:
        return lon - 360.0

    return lon


def sample_native_value(grib_path, lat, lon):
    with rasterio.open(grib_path) as src:
        src_crs = src.crs if src.crs else "EPSG:4326"

        sample_lon = normalize_lon_for_src(src, lon)
        x = sample_lon
        y = lat

        if str(src_crs).upper() not in ("EPSG:4326", "OGC:CRS84"):
            xs, ys = rio_transform("EPSG:4326", src_crs, [sample_lon], [lat])
            x = xs[0]
            y = ys[0]

        row, col = src.index(x, y)

        if row < 0 or col < 0 or row >= src.height or col >= src.width:
            return None

        val = src.read(1, window=Window(col, row, 1, 1)).astype(np.float32)[0, 0]

        if src.nodata is not None and val == src.nodata:
            return None

        if not np.isfinite(val) or val <= -900:
            return None

        return float(val)


def sample_value(grib_path, lat, lon):
    raw_cms = sample_native_value(grib_path, lat, lon)
    if raw_cms is None:
        return None

    cfs_smi = raw_cms * M3S_PER_KM2_TO_CFS_PER_SQMI

    if cfs_smi < 0:
        return None

    return {
        "value_m3s_per_km2": raw_cms,
        "value_cfs_per_smi": cfs_smi,
    }


def max_cache_key(product, grib_path, west, south, east, north):
    grib_mtime = os.path.getmtime(grib_path)

    return hashlib.md5(json.dumps({
        "product": product,
        "grib_path": grib_path,
        "grib_mtime": grib_mtime,
        "west": round(float(west), 5),
        "south": round(float(south), 5),
        "east": round(float(east), 5),
        "north": round(float(north), 5),
    }, sort_keys=True).encode("utf-8")).hexdigest()


def find_max_value_in_bbox(grib_path, product, west, south, east, north, pinfo, min_threshold=0.0):
    key = max_cache_key(product, grib_path, west, south, east, north)
    now = time.time()

    cached = MAX_CACHE.get(key)
    if cached and now - cached["time"] < MAX_CACHE_TTL_SECONDS:
        return cached["value"]

    with rasterio.open(grib_path) as src:
        src_crs = src.crs if src.crs else "EPSG:4326"
        win = source_window_for_bbox(src, west, south, east, north, pad_pixels=0)
        fill_value = src.nodata if src.nodata is not None else -9999.0

        arr = src.read(
            1,
            window=win,
            boundless=False,
            fill_value=fill_value,
        ).astype(np.float32)

        arr = clean_mrms_array(arr, src.nodata)
        arr_display = convert_native_array_to_display(arr, pinfo)
        arr_display[np.abs(arr_display) <= min_threshold] = np.nan

        if not np.any(np.isfinite(arr_display)):
            result = None
        else:
            rel_row, rel_col = np.unravel_index(np.nanargmax(arr_display), arr_display.shape)
            max_display = float(arr_display[rel_row, rel_col])
            raw_native = float(arr[rel_row, rel_col])

            src_row = int(win.row_off) + int(rel_row)
            src_col = int(win.col_off) + int(rel_col)
            x, y = src.xy(src_row, src_col)

            if str(src_crs).upper() not in ("EPSG:4326", "OGC:CRS84"):
                lons, lats = rio_transform(src_crs, "EPSG:4326", [x], [y])
                lon = float(lons[0])
                lat = float(lats[0])
            else:
                lon = float(x)
                lat = float(y)

            if lon > 180:
                lon -= 360.0

            result = {
                "lat": lat,
                "lon": lon,
                "value_m3s_per_km2": raw_native,
                "value_cfs_per_smi": max_display,
                "display_value": max_display,
                "display_units": pinfo.get("units", "cfs/mi^2"),
                "native_value": raw_native,
                "native_units": pinfo.get("native_units", "m^3/s/km^2"),
                "source_row": src_row,
                "source_col": src_col,
            }

    MAX_CACHE[key] = {
        "time": now,
        "value": result,
    }

    while len(MAX_CACHE) > MAX_CACHE_MAX_ITEMS:
        MAX_CACHE.popitem(last=False)

    return result


def geom_coord_bounds(geom):
    coords = []

    def walk(obj):
        if isinstance(obj, (list, tuple)):
            if len(obj) >= 2 and isinstance(obj[0], (int, float)) and isinstance(obj[1], (int, float)):
                coords.append((float(obj[0]), float(obj[1])))
            else:
                for item in obj:
                    walk(item)

    if not geom:
        return None

    walk(geom.get("coordinates", []))

    if not coords:
        return None

    xs = [c[0] for c in coords]
    ys = [c[1] for c in coords]

    return min(xs), min(ys), max(xs), max(ys)


def bbox_intersects(a, b):
    if not a or not b:
        return True

    aw, as_, ae, an = a
    bw, bs, be, bn = b

    return not (ae < bw or aw > be or an < bs or as_ > bn)


def bbox_overlap_fraction(a, b):
    if not a or not b or not bbox_intersects(a, b):
        return 0.0

    aw, as_, ae, an = a
    bw, bs, be, bn = b

    overlap_w = max(0.0, min(ae, be) - max(aw, bw))
    overlap_h = max(0.0, min(an, bn) - max(as_, bs))
    overlap_area = overlap_w * overlap_h

    area_a = max(0.0, (ae - aw) * (an - as_))
    area_b = max(0.0, (be - bw) * (bn - bs))
    denom = max(min(area_a, area_b), 1.0e-9)

    return overlap_area / denom


def filter_geojson_by_bbox(features, west, south, east, north):
    bbox = (west, south, east, north)
    out = []

    for feature in features:
        geom = feature.get("geometry")
        gb = geom_coord_bounds(geom)
        if bbox_intersects(gb, bbox):
            out.append(feature)

    return out


def parse_kml_coordinates(coord_text):
    points = []

    for part in coord_text.replace("\n", " ").replace("\t", " ").split():
        bits = part.split(",")
        if len(bits) < 2:
            continue

        try:
            lon = float(bits[0])
            lat = float(bits[1])
            points.append([lon, lat])
        except ValueError:
            continue

    return points


def get_child_text_anyns(elem, tag_name):
    for child in elem.iter():
        if child.tag.endswith("}" + tag_name) or child.tag == tag_name:
            if child.text:
                return child.text.strip()
    return ""


def parse_kml_polygon(poly_elem):
    rings = []

    for lr in poly_elem.iter():
        if not (lr.tag.endswith("}LinearRing") or lr.tag == "LinearRing"):
            continue

        coord_text = get_child_text_anyns(lr, "coordinates")
        ring = parse_kml_coordinates(coord_text)

        if ring:
            rings.append(ring)

    if not rings:
        return None

    return rings


def prop_ci(props, *names):
    lookup = {str(k).lower(): v for k, v in props.items()}

    for name in names:
        val = lookup.get(str(name).lower())
        if val not in (None, ""):
            return val

    return ""


def normalize_etn(etn):
    if etn in (None, ""):
        return ""

    text = str(etn).strip()

    match = re.search(r"\d+", text)
    if not match:
        return ""

    return f"{int(match.group(0)):04d}"


def clean_wfo(wfo):
    if not wfo:
        return ""

    text = str(wfo).upper().strip()
    text = re.sub(r"[^A-Z]", "", text)

    if len(text) == 4 and text.startswith("K"):
        text = text[1:]

    if len(text) >= 3:
        return text[-3:]

    return text


def parse_vtec_time(value):
    text = str(value).strip().upper()

    if text == "000000T0000Z":
        return None

    match = re.match(r"^(\d{6})T(\d{4})Z$", text)
    if match:
        yymmdd = match.group(1)
        hhmm = match.group(2)
        yy = int(yymmdd[:2])
        year = 2000 + yy if yy < 70 else 1900 + yy
        month = int(yymmdd[2:4])
        day = int(yymmdd[4:6])
        hour = int(hhmm[:2])
        minute = int(hhmm[2:4])
        return datetime(year, month, day, hour, minute, tzinfo=timezone.utc)

    match = re.match(r"^(\d{8})T(\d{4})Z$", text)
    if match:
        yyyymmdd = match.group(1)
        hhmm = match.group(2)
        year = int(yyyymmdd[:4])
        month = int(yyyymmdd[4:6])
        day = int(yyyymmdd[6:8])
        hour = int(hhmm[:2])
        minute = int(hhmm[2:4])
        return datetime(year, month, day, hour, minute, tzinfo=timezone.utc)

    return None


def parse_iso_z(value):
    if not value:
        return None

    text = str(value).strip()
    try:
        return datetime.fromisoformat(text.replace("Z", "+00:00")).astimezone(timezone.utc)
    except Exception:
        return None


def shift_month(year, month, offset):
    month_zero = month - 1 + offset
    return year + month_zero // 12, month_zero % 12 + 1


def infer_issue_time_from_segment(segment, anchor_dt):
    header = re.search(
        r"^[A-Z]{4}\d{2}\s+K[A-Z]{3}\s+(?P<stamp>\d{6})\s*$",
        segment,
        re.MULTILINE,
    )

    if not header:
        return None

    stamp = header.group("stamp")
    day = int(stamp[:2])
    hour = int(stamp[2:4])
    minute = int(stamp[4:6])

    candidates = []
    for offset in [-1, 0, 1]:
        year, month = shift_month(anchor_dt.year, anchor_dt.month, offset)
        try:
            dt = datetime(year, month, day, hour, minute, tzinfo=timezone.utc)
            candidates.append(dt)
        except ValueError:
            continue

    if not candidates:
        return None

    valid_candidates = [dt for dt in candidates if dt <= anchor_dt + timedelta(minutes=5)]
    if valid_candidates:
        return max(valid_candidates)

    return min(candidates, key=lambda dt: abs((dt - anchor_dt).total_seconds()))


def iso_z(dt):
    if not dt:
        return ""
    return dt.astimezone(timezone.utc).isoformat(timespec="minutes").replace("+00:00", "Z")


def loose_vtec_from_text(blob, default_phen="", default_sig=""):
    text = str(blob or "").upper()

    # Normal compact VTEC forms: FF.W.0021, FA.Y.0007, FF-W-0021, etc.
    match = re.search(r"\b(?P<phen>FF|FA)[\.\s_:/-]*(?P<sig>[WYS])[\.\s_:/-]*(?P<etn>\d{1,4})\b", text)
    if match:
        return {
            "phen": match.group("phen"),
            "sig": match.group("sig"),
            "etn": f"{int(match.group('etn')):04d}",
        }

    # Some IEM/DBF fields carry only an ETN near a key name. Use this only when
    # the caller supplied a known phenomena/significance from the product query.
    if default_phen and default_sig:
        match = re.search(r"\b(?:ETN|EVENT\s*ID|EVENTID|EVENT_ID|WARNING\s*NUMBER|WARNING_NUMBER|WFO_EVENT|GID|UGC_EVENT)\D{0,30}(?P<etn>\d{1,4})\b", text)
        if match:
            return {
                "phen": str(default_phen).upper(),
                "sig": str(default_sig).upper(),
                "etn": f"{int(match.group('etn')):04d}",
            }

    return None


def make_vtec_info(props, text_blob=""):
    blob = " ".join([text_blob, " ".join(str(v) for v in props.values())])

    full = re.search(
        r"/O\.(?P<action>[A-Z]{3})\.K(?P<wfo>[A-Z]{3})\.(?P<phen>FF|FA)\.(?P<sig>[A-Z])\.(?P<etn>\d{4})\.(?P<begin>\d{6,8}T\d{4}Z|000000T0000Z)-(?P<end>\d{6,8}T\d{4}Z|000000T0000Z)/",
        blob,
        re.IGNORECASE,
    )

    if full:
        phen = full.group("phen").upper()
        sig = full.group("sig").upper()
        etn = full.group("etn")
        wfo = clean_wfo(full.group("wfo"))
        begin_dt = parse_vtec_time(full.group("begin"))
        end_dt = parse_vtec_time(full.group("end"))

        return {
            "vtec_id": f"{phen}.{sig}.{etn}",
            "wfo": wfo,
            "phen": phen,
            "sig": sig,
            "etn": etn,
            "action": full.group("action").upper(),
            "vtec_begin_utc": iso_z(begin_dt),
            "vtec_end_utc": iso_z(end_dt),
        }

    match = re.search(r"\b(?P<phen>FF|FA)\.(?P<sig>[A-Z])\.(?P<etn>\d{4})\b", blob, re.IGNORECASE)
    if match:
        phen = match.group("phen").upper()
        sig = match.group("sig").upper()
        etn = match.group("etn")
        wfo = clean_wfo(prop_ci(props, "wfo", "WFO", "office", "OFFICE", "ugc_wfo", "UGC_WFO"))
        return {
            "vtec_id": f"{phen}.{sig}.{etn}",
            "wfo": wfo,
            "phen": phen,
            "sig": sig,
            "etn": etn,
            "action": "",
            "vtec_begin_utc": "",
            "vtec_end_utc": "",
        }

    loose = loose_vtec_from_text(blob)
    if loose:
        phen = loose["phen"]
        sig = loose["sig"]
        etn = loose["etn"]
        wfo = clean_wfo(prop_ci(props, "wfo", "WFO", "office", "OFFICE", "ugc_wfo", "UGC_WFO"))
        return {
            "vtec_id": f"{phen}.{sig}.{etn}",
            "wfo": wfo,
            "phen": phen,
            "sig": sig,
            "etn": etn,
            "action": "",
            "vtec_begin_utc": "",
            "vtec_end_utc": "",
        }

    phen = str(prop_ci(props, "phenomena", "PHENOMENA", "phenom", "PHENOM", "phen")).upper().strip()
    sig = str(prop_ci(props, "significance", "SIGNIFICANCE", "sig", "SIG")).upper().strip()
    etn = normalize_etn(prop_ci(props, "etn", "ETN", "eventid", "EVENTID", "event_id", "eventID"))
    wfo = clean_wfo(prop_ci(props, "wfo", "WFO", "office", "OFFICE", "ugc_wfo", "UGC_WFO"))

    if phen and sig and etn:
        return {
            "vtec_id": f"{phen}.{sig}.{etn}",
            "wfo": wfo,
            "phen": phen,
            "sig": sig,
            "etn": etn,
            "action": "",
            "vtec_begin_utc": "",
            "vtec_end_utc": "",
        }

    return {
        "vtec_id": "",
        "wfo": wfo,
        "phen": phen,
        "sig": sig,
        "etn": etn,
        "action": "",
        "vtec_begin_utc": "",
        "vtec_end_utc": "",
    }


def tag_rank(tag):
    if tag == "emergency":
        return 3
    if tag == "considerable":
        return 2
    return 0


def feature_valid_at_time(feature, valid_dt):
    props = feature.get("properties", {})

    begin_dt = parse_iso_z(props.get("vtec_begin_utc", ""))
    end_dt = parse_iso_z(props.get("vtec_end_utc", ""))

    if begin_dt and valid_dt < begin_dt - timedelta(minutes=1):
        return False

    if end_dt and valid_dt > end_dt + timedelta(minutes=1):
        return False

    action = str(props.get("action", "")).upper()
    if action in ("CAN", "EXP"):
        return False

    return True



def classify_flash_flood_tag_from_text(text):
    blob = str(text or "").lower()
    compact = re.sub(r"[^a-z0-9]+", " ", blob)

    # Flash Flood Emergency can be explicit, or encoded through the damage threat line.
    if (
        "flash flood emergency" in blob
        or "flash flood emergency" in compact
        or "flash flood...emergency" in blob
        or "flash flood damage threat...catastrophic" in blob
        or "flash flood damage threat catastrophic" in blob
        or "flash flood damage threat catastrophic" in compact
        or "damage threat...catastrophic" in blob
        or "damage threat catastrophic" in blob
        or "damage threat catastrophic" in compact
        or "catastrophic" in blob
        or "particularly dangerous situation" in blob
    ):
        return "emergency"

    if (
        "flash flood damage threat...considerable" in blob
        or "flash flood damage threat considerable" in blob
        or "flash flood damage threat considerable" in compact
        or "damage threat...considerable" in blob
        or "damage threat considerable" in blob
        or "damage threat considerable" in compact
        or "considerable" in blob
    ):
        return "considerable"

    return ""



def collect_element_text_and_attributes(elem, max_chars=20000):
    parts = []

    def add(value):
        if value is None:
            return
        text = str(value).strip()
        if text:
            parts.append(text)

    for node in elem.iter():
        add(node.text)
        for key, val in getattr(node, "attrib", {}).items():
            add(key)
            add(val)
        add(node.tail)

    text = " ".join(parts)
    if len(text) > max_chars:
        text = text[:max_chars]
    return text

def parse_kml_to_geojson(kml_text, requested_product_hint=""):
    root = ET.fromstring(kml_text)
    features = []

    placemarks = [
        elem for elem in root.iter()
        if elem.tag.endswith("}Placemark") or elem.tag == "Placemark"
    ]

    for pm in placemarks:
        name = get_child_text_anyns(pm, "name")
        description = get_child_text_anyns(pm, "description")

        props = {
            "name": name,
            "headline": name,
            "description": description,
            "source": "IEM VTEC valid-at-time polygon lookup",
        }

        for attr_key, attr_val in pm.attrib.items():
            props[f"placemark_{attr_key}"] = attr_val

        for data in pm.iter():
            if data.tag.endswith("}Data") or data.tag == "Data":
                key = data.attrib.get("name")
                val = get_child_text_anyns(data, "value")
                if key:
                    props[key] = val

            if data.tag.endswith("}SimpleData") or data.tag == "SimpleData":
                key = data.attrib.get("name")
                val = data.text.strip() if data.text else ""
                if key:
                    props[key] = val

        all_pm_text = collect_element_text_and_attributes(pm)
        text_blob_raw = f"{name} {description} {' '.join(str(v) for v in props.values())} {all_pm_text}"
        text_blob = text_blob_raw.lower()
        vtec_info = make_vtec_info(props, text_blob_raw)

        props.update(vtec_info)
        phen = vtec_info.get("phen", "").upper()
        sig = vtec_info.get("sig", "").upper()

        if phen == "FF" and sig == "W":
            props["event"] = "Flash Flood Warning"
            props["product_code"] = "FFW"
            props["product_label"] = "FFW"
        elif phen == "FA" and sig == "Y":
            props["event"] = "Flood Advisory"
            props["product_code"] = "FA.Y"
            props["product_label"] = "Flood Advisory"
        elif "flash flood warning" in text_blob:
            props["event"] = "Flash Flood Warning"
            props["product_code"] = "FFW"
            props["product_label"] = "FFW"
        elif "flood advisory" in text_blob:
            props["event"] = "Flood Advisory"
            props["product_code"] = "FA.Y"
            props["product_label"] = "Flood Advisory"
        else:
            continue

        if requested_product_hint:
            props["requested_product_hint"] = requested_product_hint

        props["flash_flood_tag"] = classify_flash_flood_tag_from_text(text_blob_raw)

        polygons = []

        for poly in pm.iter():
            if poly.tag.endswith("}Polygon") or poly.tag == "Polygon":
                parsed = parse_kml_polygon(poly)
                if parsed:
                    polygons.append(parsed)

        if not polygons:
            continue

        if len(polygons) == 1:
            geom = {
                "type": "Polygon",
                "coordinates": polygons[0],
            }
        else:
            geom = {
                "type": "MultiPolygon",
                "coordinates": polygons,
            }

        vtec_id = props.get("vtec_id", "")
        props["display_label"] = f"{props['product_label']} {vtec_id}".strip()

        features.append({
            "type": "Feature",
            "geometry": geom,
            "properties": props,
        })

    return {
        "type": "FeatureCollection",
        "features": features,
        "source": "IEM VTEC valid-at-time polygon lookup",
    }


def request_iem_common(valid_dt, phen, sig, accept="kml", limit1=False, addsvs=False, timeout=30):
    at = datetime_to_iem_at(valid_dt)

    url = "https://mesonet.agron.iastate.edu/cgi-bin/request/gis/watchwarn.py"

    params = {
        "accept": accept,
        "at": at,
        "timeopt": "2",
        "limitps": "1",
        "phenomena": phen,
        "significance": sig,
        # Full KML generally carries richer ExtendedData/VTEC metadata. The
        # simple KML can leave labels generic, which causes lost FF.W/FA.Y numbers.
        "simple": "no" if str(accept).lower() == "kml" else "yes",
    }

    if limit1:
        params["limit1"] = "1"

    if addsvs:
        params["addsvs"] = "1"

    r = requests_get(url, params=params, timeout=timeout)
    r.raise_for_status()

    return r.text


def request_iem_kml(valid_dt, phen, sig, limit1=False, addsvs=False):
    return request_iem_common(valid_dt, phen, sig, accept="kml", limit1=limit1, addsvs=addsvs, timeout=30)


def request_iem_csv(valid_dt, phen, sig, limit1=False, addsvs=False):
    return request_iem_common(valid_dt, phen, sig, accept="csv", limit1=limit1, addsvs=addsvs, timeout=30)


def parse_iem_csv_rows(csv_text):
    text = (csv_text or "").strip()
    if not text:
        return []

    try:
        reader = csv.DictReader(io.StringIO(text))
        rows = []
        for row in reader:
            cleaned = {}
            for key, val in (row or {}).items():
                if key is None:
                    continue
                clean_key = str(key).strip()
                if not clean_key:
                    continue
                cleaned[clean_key] = "" if val is None else str(val).strip()
            if cleaned:
                rows.append(cleaned)
        return rows
    except Exception:
        return []



def csv_row_geometry_bounds(row):
    """Best-effort bbox extraction from IEM CSV rows.

    Some IEM CSV variants expose WKT/geometry fields. Matching by geometry is
    much safer than assuming the CSV row order matches the KML Placemark order.
    """
    if not row:
        return None

    geometry_keys = (
        "geom", "geometry", "the_geom", "wkt", "wkb_geometry", "shape",
        "polygon", "coordinates", "latlon", "lat_lon", "lat...lon",
    )

    for key, value in row.items():
        key_lc = str(key).strip().lower()
        text = str(value or "").strip()
        if not text:
            continue

        if key_lc not in geometry_keys and "polygon" not in text.lower() and "coordinates" not in text.lower():
            continue

        # WKT-style: POLYGON((-90.1 30.2, -90.2 30.3, ...))
        pairs = re.findall(r"(-?\d+(?:\.\d+)?)\s+(-?\d+(?:\.\d+)?)", text)
        coords = []
        for x_s, y_s in pairs:
            try:
                x = float(x_s)
                y = float(y_s)
            except ValueError:
                continue
            if -180.0 <= x <= 360.0 and -90.0 <= y <= 90.0:
                if x > 180.0:
                    x -= 360.0
                coords.append((x, y))

        if coords:
            xs = [c[0] for c in coords]
            ys = [c[1] for c in coords]
            return min(xs), min(ys), max(xs), max(ys)

        # JSON/GeoJSON-ish fallback.
        try:
            obj = json.loads(text)
        except Exception:
            obj = None

        if obj is not None:
            coords = []

            def walk(v):
                if isinstance(v, (list, tuple)):
                    if len(v) >= 2 and isinstance(v[0], (int, float)) and isinstance(v[1], (int, float)):
                        x = float(v[0])
                        y = float(v[1])
                        if -180.0 <= x <= 360.0 and -90.0 <= y <= 90.0:
                            if x > 180.0:
                                x -= 360.0
                            coords.append((x, y))
                    else:
                        for item in v:
                            walk(item)
                elif isinstance(v, dict):
                    for item in v.values():
                        walk(item)

            walk(obj)
            if coords:
                xs = [c[0] for c in coords]
                ys = [c[1] for c in coords]
                return min(xs), min(ys), max(xs), max(ys)

    return None


def row_event_matches_feature(row, feature, default_phen, default_sig):
    props = feature.get("properties", {})
    row_blob = " ".join(str(v) for v in row.values()).lower()
    event = str(props.get("event", "")).lower()
    row_phen = str(prop_ci(row, "phen", "phenomena", "PHENOMENA", "phenom", "PHENOM", "phensig")).upper()
    row_sig = str(prop_ci(row, "sig", "significance", "SIGNIFICANCE", "SIG", "phensig")).upper()

    if row_phen and row_sig:
        if "flash flood warning" in event and not ("FF" in row_phen and "W" in row_sig):
            return False
        if "flood advisory" in event and not ("FA" in row_phen and "Y" in row_sig):
            return False

    if "flash flood warning" in event:
        return ("flash" in row_blob and "warning" in row_blob) or default_phen == "FF"
    if "flood advisory" in event:
        return ("flood" in row_blob and "advis" in row_blob) or default_phen == "FA"

    return True


def copy_vtec_row_fields_to_feature(feature, row, default_phen, default_sig):
    props = feature.get("properties", {})

    for key, val in row.items():
        if val in (None, ""):
            continue
        # Do not overwrite rich KML/AFOS fields with CSV values unless the field
        # is missing. This keeps text-derived CONSIDERABLE/EMERGENCY tags intact.
        props.setdefault(key, val)
        props.setdefault(str(key).lower(), val)

    blob = " ".join(str(v) for v in list(props.values()) + list(row.values()))
    vtec_info = make_vtec_info(props, blob)

    phen = (vtec_info.get("phen") or default_phen or "").upper()
    sig = (vtec_info.get("sig") or default_sig or "").upper()
    etn = vtec_info.get("etn") or normalize_etn(prop_ci(
        props,
        "etn", "ETN", "eventid", "EVENTID", "event_id", "EVENT_ID", "eventID", "event", "EVENT", "gid", "GID", "id", "ID",
    ))
    wfo = vtec_info.get("wfo") or clean_wfo(prop_ci(props, "wfo", "WFO", "office", "OFFICE"))

    if phen and sig and etn:
        props["phen"] = phen
        props["sig"] = sig
        props["etn"] = etn
        props["vtec_id"] = f"{phen}.{sig}.{etn}"
        props["warning_number"] = props["vtec_id"]
    if wfo:
        props["wfo"] = wfo

    feature["properties"] = props
    return feature

def merge_iem_csv_rows_into_features(features, csv_rows, default_phen, default_sig):
    if not features or not csv_rows:
        return features

    row_infos = []
    for idx, row in enumerate(csv_rows):
        info = make_vtec_info(row, " ".join(str(v) for v in row.values()))
        if not info.get("vtec_id") and not normalize_etn(prop_ci(row, "etn", "ETN", "eventid", "EVENTID", "event_id", "EVENT_ID", "eventID")):
            continue
        row_infos.append({
            "idx": idx,
            "row": row,
            "bbox": csv_row_geometry_bounds(row),
            "vtec_id": info.get("vtec_id", ""),
        })

    used_rows = set()

    for feature in features:
        props = feature.get("properties", {})
        if derive_alert_vtec_id(props):
            continue

        fb = geom_coord_bounds(feature.get("geometry"))
        if not fb:
            continue

        best = None
        best_score = 0.0

        for item in row_infos:
            if item["idx"] in used_rows:
                continue
            row = item["row"]
            rb = item.get("bbox")
            if not rb:
                continue
            if not row_event_matches_feature(row, feature, default_phen, default_sig):
                continue
            score = bbox_overlap_fraction(fb, rb)
            if score > best_score:
                best = item
                best_score = score

        # Require a meaningful geometry overlap. This avoids the previous bad
        # behavior where CONSIDERABLE tags/numbers drifted onto adjacent warnings.
        if best and best_score >= 0.25:
            copy_vtec_row_fields_to_feature(feature, best["row"], default_phen, default_sig)
            used_rows.add(best["idx"])

    return features


def enrich_features_with_iem_csv(valid_dt, features, phen, sig, limit1=False, addsvs=False):
    if not features:
        return features

    # First keep anything the KML itself gave us. Full KML often has ETN/WFO.
    if all(derive_alert_vtec_id(f.get("properties", {})) for f in features):
        return features

    try:
        csv_text = request_iem_csv(valid_dt, phen=phen, sig=sig, limit1=limit1, addsvs=addsvs)
        rows = parse_iem_csv_rows(csv_text)
        return merge_iem_csv_rows_into_features(features, rows, phen, sig)
    except Exception as e:
        print(f"[IEM {phen}.{sig} geometry-safe CSV metadata fetch error] {e}")
        return features


def feature_point_count(feature):
    count = 0

    def walk(obj):
        nonlocal count
        if isinstance(obj, (list, tuple)):
            if len(obj) >= 2 and isinstance(obj[0], (int, float)) and isinstance(obj[1], (int, float)):
                count += 1
            else:
                for item in obj:
                    walk(item)

    geom = feature.get("geometry", {})
    walk(geom.get("coordinates", []))
    return count


def is_county_like_flood_advisory(feature):
    props = feature.get("properties", {})
    if props.get("event") != "Flood Advisory":
        return False

    points = feature_point_count(feature)
    gb = geom_coord_bounds(feature.get("geometry"))

    if points >= 45:
        return True

    if gb:
        west, south, east, north = gb
        area = abs((east - west) * (north - south))
        if area > 1.8 and points >= 25:
            return True

    blob = " ".join(str(v) for v in props.values()).lower()
    if "county" in blob or "parish" in blob:
        if points >= 25:
            return True

    return False


def dedupe_features(features):
    seen = set()
    out = []

    for feature in features:
        props = feature.get("properties", {})
        geom = feature.get("geometry", {})
        key_text = json.dumps({
            "vtec": props.get("vtec_id", ""),
            "code": props.get("product_code", ""),
            "tag": props.get("flash_flood_tag", ""),
            "geom": geom,
        }, sort_keys=True)

        key = hashlib.md5(key_text.encode("utf-8")).hexdigest()

        if key in seen:
            continue

        seen.add(key)
        out.append(feature)

    return out


WFO_HINT_BBOXES = {
    "LIX": (-91.95, 27.85, -88.25, 31.45),
    "MOB": (-89.55, 28.25, -85.85, 31.85),
    "LCH": (-94.45, 28.75, -91.05, 31.55),
    "JAX": (-83.55, 28.70, -80.30, 31.65),
    # Broader SE/Gulf offices so panned archive views can pull the
    # matching AFOS FFW/FFS text products. This is important because the
    # IEM polygon KML can omit the actual VTEC/impact tag even though the
    # original warning text contains FF.W/FF.S + CATASTROPHIC/CONSIDERABLE.
    "HUN": (-88.60, 33.00, -84.40, 36.00),
    "BMX": (-88.80, 31.60, -84.60, 34.80),
    "FFC": (-86.80, 30.00, -80.50, 35.20),
    "MEG": (-91.80, 33.50, -87.00, 37.20),
    "OHX": (-88.10, 34.60, -84.00, 37.40),
    "MRX": (-85.80, 34.60, -81.60, 37.20),
    "JAN": (-92.70, 30.00, -88.00, 35.20),
    "SHV": (-95.20, 31.00, -91.00, 34.80),
    "LZK": (-94.80, 33.00, -89.20, 36.80),
    "TAE": (-86.70, 28.70, -82.00, 32.80),
    "CHS": (-82.80, 30.80, -78.50, 34.20),
    "CAE": (-83.00, 32.50, -79.00, 35.50),
    "GSP": (-84.80, 33.80, -80.00, 36.80),
    # Kentucky / Ohio Valley offices. Important for panned views: IEM polygons
    # can have generic or missing WFO metadata, so these bbox hints ensure the
    # AFOS FFW/FFS text chain is fetched and FF.S upgrades can promote the
    # original FF.W ETN to CONSIDERABLE/EMERGENCY.
    "JKL": (-85.80, 36.20, -81.70, 39.10),
    "LMK": (-88.00, 36.00, -84.00, 39.60),
    "PAH": (-90.80, 36.20, -86.00, 39.30),
    "ILN": (-85.80, 37.50, -82.00, 40.90),
    "RLX": (-83.80, 37.00, -79.00, 40.60),
    "IND": (-88.30, 38.50, -84.40, 41.80),
}


def guess_wfos_for_bbox(west, south, east, north):
    bbox = (west, south, east, north)
    wfos = set()

    for wfo, wbbox in WFO_HINT_BBOXES.items():
        if bbox_intersects(bbox, wbbox):
            wfos.add(wfo)

    return sorted(wfos)


def nws_latlon_to_decimal(value, is_lon=False):
    """
    NWS LAT...LON polygon points are usually hundredths of degrees.
    Example:
      3031 -> 30.31N
      9012 -> 90.12W
    """
    text = str(value).strip()

    if not text.isdigit():
        return None

    dec = int(text) / 100.0

    if is_lon:
        dec = -abs(dec)

    return dec


def parse_latlon_polygon_from_text(text):
    match = re.search(
        r"LAT\.\.\.LON\s+(.*?)(?:\n\s*\n|\n&&|\n\$\$|$)",
        text,
        re.IGNORECASE | re.DOTALL,
    )

    if not match:
        return None

    block = match.group(1)
    pairs = re.findall(r"\b(\d{4,5})\s+(\d{4,5})\b", block)

    coords = []

    for lat_s, lon_s in pairs:
        lat = nws_latlon_to_decimal(lat_s, is_lon=False)
        lon = nws_latlon_to_decimal(lon_s, is_lon=True)

        if lat is None or lon is None:
            continue

        coords.append([lon, lat])

    if len(coords) < 3:
        return None

    if coords[0] != coords[-1]:
        coords.append(coords[0])

    return {
        "type": "Polygon",
        "coordinates": [coords],
    }


def find_product_segment(text, match, next_start=None):
    before = text[:match.start()]
    headers = list(re.finditer(r"^[A-Z]{4}\d{2}\s+K[A-Z]{3}\s+\d{6}\s*$", before, re.MULTILINE))
    start = headers[-1].start() if headers else max(0, text.rfind("\n\n", 0, match.start()))

    end_candidates = []

    after_dollar = text.find("\n$$", match.end())
    if after_dollar != -1:
        end_candidates.append(after_dollar)

    after_header = re.search(r"^[A-Z]{4}\d{2}\s+K[A-Z]{3}\s+\d{6}\s*$", text[match.end():], re.MULTILINE)
    if after_header:
        end_candidates.append(match.end() + after_header.start())

    if next_start:
        end_candidates.append(next_start)

    end = min(end_candidates) if end_candidates else min(len(text), match.end() + 15000)
    return text[start:end]


def parse_ffs_products_from_text(text, valid_dt):
    """
    Parse FFS text and keep the highest valid impact tag for each FF.W event.

    Important behavior:
      - A later plain FFS should not downgrade a prior valid Emergency/Considerable tag.
      - A later CAN/EXP should suppress the warning/statement.
      - The top FFS polygon, if one exists, is returned as a separate feature so it plots above the base FFW.
    """
    grouped = {}

    vtec_pattern = re.compile(
        r"/O\.(?P<action>[A-Z]{3})\.K(?P<wfo>[A-Z]{3})\.(?P<phen>FF)\.(?P<sig>W)\.(?P<etn>\d{4})\.(?P<begin>\d{6,8}T\d{4}Z|000000T0000Z)-(?P<end>\d{6,8}T\d{4}Z|000000T0000Z)/",
        re.IGNORECASE,
    )

    matches = list(vtec_pattern.finditer(text))

    for idx, match in enumerate(matches):
        next_start = matches[idx + 1].start() if idx + 1 < len(matches) else None
        segment = find_product_segment(text, match, next_start=next_start)
        segment_lc = segment.lower()

        wfo = clean_wfo(match.group("wfo"))
        vtec_id = f"{match.group('phen').upper()}.{match.group('sig').upper()}.{match.group('etn')}"
        action = match.group("action").upper()
        begin_dt = parse_vtec_time(match.group("begin"))
        end_dt = parse_vtec_time(match.group("end"))
        issue_dt = infer_issue_time_from_segment(segment, valid_dt)

        if issue_dt and issue_dt > valid_dt + timedelta(minutes=1):
            continue

        if begin_dt and valid_dt < begin_dt - timedelta(minutes=1):
            continue

        tag = classify_flash_flood_tag_from_text(segment)

        geom = parse_latlon_polygon_from_text(segment)
        issue_for_sort = issue_dt or datetime(1900, 1, 1, tzinfo=timezone.utc)
        key = (wfo, vtec_id)

        label_status = "EMERGENCY" if tag == "emergency" else "CONSIDERABLE" if tag == "considerable" else "BASE"
        feature = None

        if geom is not None and action not in ("CAN", "EXP"):
            feature = {
                "type": "Feature",
                "geometry": geom,
                "properties": {
                    "event": "Flash Flood Warning",
                    "product_code": "FFW+FFS",
                    "product_label": "FFW",
                    "display_label": f"{label_status} FF.W {vtec_id.split('.')[-1]}",
                    "headline": f"Latest valid Flash Flood Statement upgrade for {vtec_id} {label_status}",
                    "wfo": wfo,
                    "vtec_id": vtec_id,
                    "phen": "FF",
                    "sig": "W",
                    "etn": vtec_id.split(".")[-1],
                    "action": action,
                    "flash_flood_tag": tag,
                    "ffs_detected": True,
                    "statement_status": label_status,
                    "issue_utc": iso_z(issue_dt),
                    "vtec_begin_utc": iso_z(begin_dt),
                    "vtec_end_utc": iso_z(end_dt),
                    "source": "IEM AFOS FFS text highest valid LAT...LON polygon",
                },
            }

        grouped.setdefault(key, []).append({
            "wfo": wfo,
            "vtec_id": vtec_id,
            "tag": tag,
            "action": action,
            "issue_dt": issue_for_sort,
            "begin_dt": begin_dt,
            "end_dt": end_dt,
            "feature": feature,
            "segment_lc": segment_lc,
        })

    out_tags = {}
    out_features = []

    for key, candidates in grouped.items():
        candidates.sort(key=lambda c: c["issue_dt"])

        # Latest action controls cancellation/expiration suppression.
        latest = candidates[-1]
        suppress = False
        if latest.get("action") in ("CAN", "EXP"):
            suppress = True

        latest_end = latest.get("end_dt")
        if latest_end and valid_dt > latest_end + timedelta(minutes=1):
            suppress = True

        active_candidates = []
        for c in candidates:
            end_dt = c.get("end_dt")
            if c.get("action") in ("CAN", "EXP"):
                continue
            if end_dt and valid_dt > end_dt + timedelta(minutes=1):
                continue
            active_candidates.append(c)

        # Keep the highest tag observed in active FFS products. This prevents a later
        # routine FFS from downgrading a prior Emergency/Considerable upgrade.
        if active_candidates:
            best_tag_candidate = max(active_candidates, key=lambda c: (tag_rank(c.get("tag", "")), c["issue_dt"]))
        else:
            best_tag_candidate = latest

        best_feature_candidates = [c for c in active_candidates if c.get("feature") is not None]
        if best_feature_candidates:
            best_feature_candidate = max(best_feature_candidates, key=lambda c: (tag_rank(c.get("tag", "")), c["issue_dt"]))
        else:
            best_feature_candidate = None

        best_tag = best_tag_candidate.get("tag", "") if best_tag_candidate else ""
        best_end = latest.get("end_dt") or (best_tag_candidate.get("end_dt") if best_tag_candidate else None)
        best_issue = latest.get("issue_dt") or (best_tag_candidate.get("issue_dt") if best_tag_candidate else None)

        out_tags[key] = {
            "wfo": latest.get("wfo"),
            "vtec_id": latest.get("vtec_id"),
            "tag": best_tag,
            "action": latest.get("action"),
            "ffs_detected": not suppress,
            "suppress": suppress,
            "issue_dt": best_issue,
            "begin_dt": latest.get("begin_dt"),
            "end_dt": best_end,
            "statement_status": "EMERGENCY" if best_tag == "emergency" else "CONSIDERABLE" if best_tag == "considerable" else "BASE",
            "source_product": "FFS",
        }

        if not suppress and best_feature_candidate and best_feature_candidate.get("feature"):
            feature = best_feature_candidate["feature"]
            props = feature.get("properties", {})
            props["flash_flood_tag"] = best_tag
            props["statement_status"] = out_tags[key]["statement_status"]
            props["display_label"] = f"{props['statement_status']} FF.W {props.get('etn', latest.get('vtec_id', '').split('.')[-1])}"
            feature["properties"] = props
            out_features.append(feature)

    return out_tags, out_features


def parse_ffw_products_from_text(text, valid_dt):
    """
    Parse original FFW text products. This catches NEW Flash Flood Emergencies
    where the emergency tag lives in the product body / damage threat line rather
    than the IEM polygon KML attributes. It also returns text-derived polygons so
    the visible map label can always include FF.W #### when the KML layer only
    says generic FFW BASE.
    """
    grouped = {}

    vtec_pattern = re.compile(
        r"/O\.(?P<action>[A-Z]{3})\.K(?P<wfo>[A-Z]{3})\.(?P<phen>FF)\.(?P<sig>W)\.(?P<etn>\d{4})\.(?P<begin>\d{6,8}T\d{4}Z|000000T0000Z)-(?P<end>\d{6,8}T\d{4}Z|000000T0000Z)/",
        re.IGNORECASE,
    )

    matches = list(vtec_pattern.finditer(text or ""))

    for idx, match in enumerate(matches):
        next_start = matches[idx + 1].start() if idx + 1 < len(matches) else None
        segment = find_product_segment(text, match, next_start=next_start)

        wfo = clean_wfo(match.group("wfo"))
        etn = match.group("etn")
        vtec_id = f"{match.group('phen').upper()}.{match.group('sig').upper()}.{etn}"
        action = match.group("action").upper()
        begin_dt = parse_vtec_time(match.group("begin"))
        end_dt = parse_vtec_time(match.group("end"))
        issue_dt = infer_issue_time_from_segment(segment, valid_dt)

        if issue_dt and issue_dt > valid_dt + timedelta(minutes=1):
            continue
        if begin_dt and valid_dt < begin_dt - timedelta(minutes=1):
            continue

        tag = classify_flash_flood_tag_from_text(segment)
        status = "EMERGENCY" if tag == "emergency" else "CONSIDERABLE" if tag == "considerable" else "BASE"
        geom = parse_latlon_polygon_from_text(segment)
        issue_for_sort = issue_dt or datetime(1900, 1, 1, tzinfo=timezone.utc)
        key = (wfo, vtec_id)

        feature = None
        if geom is not None and action not in ("CAN", "EXP"):
            feature = {
                "type": "Feature",
                "geometry": geom,
                "properties": {
                    "event": "Flash Flood Warning",
                    "product_code": "FFW",
                    "product_label": "FFW",
                    "display_label": f"{status} FF.W {etn}",
                    "headline": f"Valid Flash Flood Warning for {vtec_id} {status}",
                    "wfo": wfo,
                    "vtec_id": vtec_id,
                    "warning_number": vtec_id,
                    "phen": "FF",
                    "sig": "W",
                    "etn": etn,
                    "action": action,
                    "flash_flood_tag": tag,
                    "statement_status": status,
                    "issue_utc": iso_z(issue_dt),
                    "vtec_begin_utc": iso_z(begin_dt),
                    "vtec_end_utc": iso_z(end_dt),
                    "source": "IEM AFOS FFW text valid LAT...LON polygon",
                    "source_product": "FFW",
                },
            }

        grouped.setdefault(key, []).append({
            "wfo": wfo,
            "vtec_id": vtec_id,
            "tag": tag,
            "action": action,
            "issue_dt": issue_for_sort,
            "begin_dt": begin_dt,
            "end_dt": end_dt,
            "source_product": "FFW",
            "feature": feature,
        })

    out_tags = {}
    out_features = []

    for key, candidates in grouped.items():
        candidates.sort(key=lambda c: c["issue_dt"])
        latest = candidates[-1]

        suppress = False
        if latest.get("action") in ("CAN", "EXP"):
            suppress = True

        latest_end = latest.get("end_dt")
        if latest_end and valid_dt > latest_end + timedelta(minutes=1):
            suppress = True

        active_candidates = []
        for c in candidates:
            end_dt = c.get("end_dt")
            if c.get("action") in ("CAN", "EXP"):
                continue
            if end_dt and valid_dt > end_dt + timedelta(minutes=1):
                continue
            active_candidates.append(c)

        if active_candidates:
            best = max(active_candidates, key=lambda c: (tag_rank(c.get("tag", "")), c["issue_dt"]))
        else:
            best = latest

        best_tag = best.get("tag", "")
        best_status = "EMERGENCY" if best_tag == "emergency" else "CONSIDERABLE" if best_tag == "considerable" else "BASE"

        out_tags[key] = {
            "wfo": latest.get("wfo"),
            "vtec_id": latest.get("vtec_id"),
            "tag": best_tag,
            "action": latest.get("action"),
            "ffs_detected": False,
            "suppress": suppress,
            "issue_dt": latest.get("issue_dt"),
            "begin_dt": latest.get("begin_dt"),
            "end_dt": latest.get("end_dt"),
            "statement_status": best_status,
            "source_product": "FFW",
        }

        # Plot the best text-derived polygon too. This is the fallback that fixes
        # generic permanent labels such as "FFW BASE" from polygon-only KML.
        if not suppress and best.get("feature"):
            feature = best["feature"]
            props = feature.get("properties", {})
            props["flash_flood_tag"] = best_tag
            props["statement_status"] = best_status
            props["display_label"] = f"{best_status} FF.W {props.get('etn', latest.get('vtec_id', '').split('.')[-1])}"
            feature["properties"] = props
            out_features.append(feature)

    return out_tags, out_features

def merge_flash_flood_text_tag(existing, incoming):
    if existing is None:
        return incoming

    # Cancellation/expiration from either product suppresses the matching event.
    if incoming.get("suppress"):
        if not existing.get("issue_dt") or incoming.get("issue_dt") >= existing.get("issue_dt"):
            return incoming
        existing["suppress"] = True
        return existing

    if existing.get("suppress"):
        return existing

    old_tag = existing.get("tag", "")
    new_tag = incoming.get("tag", "")

    # Highest tier always wins, even if a later routine statement has no tag.
    if tag_rank(new_tag) > tag_rank(old_tag):
        existing["tag"] = new_tag
        existing["statement_status"] = incoming.get("statement_status")
        existing["source_product"] = incoming.get("source_product", existing.get("source_product"))
    elif tag_rank(new_tag) == tag_rank(old_tag):
        # Prefer FFS labels when it is a real statement/upgrade and not lower-tier.
        if incoming.get("source_product") == "FFS":
            existing["source_product"] = "FFS"
            existing["ffs_detected"] = True
            existing["statement_status"] = incoming.get("statement_status", existing.get("statement_status"))

    if incoming.get("end_dt"):
        existing["end_dt"] = incoming.get("end_dt")
    if incoming.get("issue_dt") and (not existing.get("issue_dt") or incoming.get("issue_dt") > existing.get("issue_dt")):
        existing["issue_dt"] = incoming.get("issue_dt")

    return existing



def quantize_alert_bbox(west, south, east, north, step=0.25):
    return (
        math.floor(float(west) / step) * step,
        math.floor(float(south) / step) * step,
        math.ceil(float(east) / step) * step,
        math.ceil(float(north) / step) * step,
    )


def trim_cache(cache, max_items):
    while len(cache) > max_items:
        try:
            cache.popitem(last=False)
        except TypeError:
            cache.pop(next(iter(cache)))


def fetch_afos_text_cached(pil, sdate, edate):
    cache_key = json.dumps({"pil": pil, "sdate": sdate, "edate": edate}, sort_keys=True)
    now = time.time()
    cached = AFOS_TEXT_CACHE.get(cache_key)

    if cached:
        ttl = AFOS_TEXT_FAILURE_TTL_SECONDS if cached.get("failed") else AFOS_TEXT_CACHE_TTL_SECONDS
        if now - cached.get("time", 0) < ttl:
            return cached.get("text", "")

    url = "https://mesonet.agron.iastate.edu/cgi-bin/afos/retrieve.py"
    params = {
        "pil": pil,
        "fmt": "text",
        "sdate": sdate,
        "edate": edate,
        "limit": str(AFOS_TEXT_LIMIT),
    }

    try:
        r = requests_get(url, params=params, timeout=AFOS_TEXT_TIMEOUT_SECONDS)
        r.raise_for_status()
        text = r.text or ""
        AFOS_TEXT_CACHE[cache_key] = {
            "time": now,
            "failed": False,
            "text": text,
        }
        trim_cache(AFOS_TEXT_CACHE, AFOS_TEXT_CACHE_MAX_ITEMS)
        return text
    except Exception as e:
        AFOS_TEXT_CACHE[cache_key] = {
            "time": now,
            "failed": True,
            "text": "",
            "error": str(e),
        }
        trim_cache(AFOS_TEXT_CACHE, AFOS_TEXT_CACHE_MAX_ITEMS)
        print(f"[AFOS text fetch skipped/cached] {pil}: {e}")
        return ""


def fetch_ffs_products(valid_dt, wfos):
    valid_dt = valid_dt.astimezone(timezone.utc)
    wfos = sorted(set(clean_wfo(w) for w in wfos if clean_wfo(w)))

    if not wfos:
        return {}, []

    sdate = (valid_dt - timedelta(hours=36)).strftime("%Y-%m-%dT%H:%MZ")
    edate = (valid_dt + timedelta(minutes=1)).strftime("%Y-%m-%dT%H:%MZ")

    cache_key = json.dumps({
        "sdate": sdate,
        "edate": edate,
        "wfos": wfos,
        "include": ["FFW", "FFS"],
        "classifier": "catastrophic_damage_threat_enabled_v6_ky_wfo_hints_etn_promotion_clean_area_popup",
        "afos_timeout": AFOS_TEXT_TIMEOUT_SECONDS,
        "afos_limit": AFOS_TEXT_LIMIT,
    }, sort_keys=True)

    now = time.time()

    with FFS_TEXT_CACHE_LOCK:
        cached = FFS_TEXT_CACHE.get(cache_key)
        if cached and now - cached["time"] < FFS_TEXT_CACHE_TTL_SECONDS:
            return cached["tags"], cached["features"]

        all_tags = {}
        all_features = []

        for wfo in wfos:
            # Original FFW text catches NEW emergencies such as:
            # FLASH FLOOD DAMAGE THREAT...CATASTROPHIC
            for pil_prefix in ("FFW", "FFS"):
                pil = f"{pil_prefix}{wfo}"
                product_text = fetch_afos_text_cached(pil, sdate, edate)

                if not product_text:
                    continue

                if pil_prefix == "FFW":
                    tags, features = parse_ffw_products_from_text(product_text, valid_dt)
                else:
                    tags, features = parse_ffs_products_from_text(product_text, valid_dt)

                for key, incoming in tags.items():
                    incoming["source_product"] = pil_prefix
                    if pil_prefix == "FFS":
                        incoming["ffs_detected"] = not incoming.get("suppress", False)
                    all_tags[key] = merge_flash_flood_text_tag(all_tags.get(key), incoming)

                all_features.extend(features)

        FFS_TEXT_CACHE[cache_key] = {
            "time": now,
            "tags": all_tags,
            "features": all_features,
        }

        trim_cache(FFS_TEXT_CACHE, FFS_TEXT_CACHE_MAX_ITEMS)
        return all_tags, all_features

def apply_latest_flash_flood_tags_to_text_features(text_features, ffs_tags):
    if not text_features:
        return text_features

    by_vtec = {}
    for (wfo, vtec_id), data in (ffs_tags or {}).items():
        if data.get("suppress"):
            continue
        by_vtec.setdefault(vtec_id, []).append(data)

    out = []
    for feature in text_features:
        props = feature.get("properties", {})
        if props.get("event") != "Flash Flood Warning":
            out.append(feature)
            continue

        vtec_id = derive_alert_vtec_id(props)
        if not vtec_id:
            out.append(feature)
            continue

        wfo = clean_wfo(props.get("wfo", ""))
        data = None
        if wfo:
            data = (ffs_tags or {}).get((wfo, vtec_id))

        if data is None:
            matches = by_vtec.get(vtec_id, [])
            if matches:
                data = max(matches, key=lambda v: (tag_rank(v.get("tag", "")), v.get("issue_dt") or datetime(1900, 1, 1, tzinfo=timezone.utc)))

        if data and data.get("suppress"):
            continue

        incoming_tag = (data or {}).get("tag", "")
        if tag_rank(incoming_tag) >= tag_rank(props.get("flash_flood_tag", "")):
            props["flash_flood_tag"] = incoming_tag

        status = "EMERGENCY" if props.get("flash_flood_tag") == "emergency" else "CONSIDERABLE" if props.get("flash_flood_tag") == "considerable" else "BASE"
        props["phen"] = "FF"
        props["sig"] = "W"
        props["etn"] = vtec_id.split(".")[-1]
        props["vtec_id"] = vtec_id
        props["warning_number"] = vtec_id
        props["product_code"] = "FFW+FFS" if (data or {}).get("source_product") == "FFS" or (data or {}).get("ffs_detected") else "FFW"
        props["product_label"] = "FFW"
        props["ffs_detected"] = bool((data or {}).get("ffs_detected"))
        props["statement_status"] = status
        props["display_label"] = f"{status} FF.W {props['etn']}"
        if data:
            props["latest_flash_flood_text_issue_utc"] = iso_z(data.get("issue_dt"))
            props["vtec_end_utc"] = iso_z(data.get("end_dt"))
        feature["properties"] = props
        out.append(feature)

    return out


def apply_ffs_tags_to_features(features, valid_dt, west=None, south=None, east=None, north=None):
    wfos = set()

    for feature in features:
        props = feature.get("properties", {})
        if props.get("event") == "Flash Flood Warning":
            wfos.add(props.get("wfo", ""))

    if west is not None:
        wfos.update(guess_wfos_for_bbox(west, south, east, north))

    ffs_tags, ffs_features = fetch_ffs_products(valid_dt, wfos)
    ffs_features = apply_latest_flash_flood_tags_to_text_features(ffs_features, ffs_tags)

    suppress_by_wfo_vtec = set()
    suppress_by_vtec = set()

    for (wfo, vtec_id), data in ffs_tags.items():
        if data.get("suppress"):
            suppress_by_wfo_vtec.add((wfo, vtec_id))
            suppress_by_vtec.add(vtec_id)

    filtered_features = []

    for feature in features:
        props = feature.get("properties", {})

        if props.get("event") == "Flash Flood Warning":
            wfo = clean_wfo(props.get("wfo", ""))
            vtec_id = props.get("vtec_id", "")

            if (wfo, vtec_id) in suppress_by_wfo_vtec or vtec_id in suppress_by_vtec:
                continue

        filtered_features.append(feature)

    features = filtered_features

    active_ffw_vtecs = set()
    for feature in features:
        props = feature.get("properties", {})
        if props.get("event") == "Flash Flood Warning" and props.get("vtec_id"):
            active_ffw_vtecs.add(props["vtec_id"])

    features = promote_text_warning_tags_by_overlap(features, ffs_tags, ffs_features)

    text_feature_bounds = []
    for feature in ffs_features:
        props = feature.get("properties", {})
        src = str(props.get("source", ""))
        if "AFOS FFW text" in src or "AFOS FFS text" in src:
            gb = geom_coord_bounds(feature.get("geometry"))
            if gb:
                text_feature_bounds.append(gb)

    if text_feature_bounds:
        cleaned = []
        for feature in features:
            props = feature.get("properties", {})
            source = str(props.get("source", ""))
            is_text_derived = "AFOS FFW text" in source or "AFOS FFS text" in source
            is_kml_ffw = props.get("event") == "Flash Flood Warning" and not is_text_derived
            gb = geom_coord_bounds(feature.get("geometry"))

            # If we have an AFOS LAT...LON polygon, it carries the exact VTEC ETN
            # and impact tag from the warning/statement text. Drop the overlapping
            # IEM KML version so an unreliable KML/CSV ETN cannot mis-label the map.
            if is_kml_ffw and gb and any(bbox_overlap_fraction(gb, tb) >= 0.01 for tb in text_feature_bounds):
                continue

            cleaned.append(feature)
        features = cleaned

    if ffs_tags:
        by_vtec = {}
        by_etn = {}

        for (wfo, vtec_id), data in ffs_tags.items():
            if data.get("suppress"):
                continue
            by_vtec.setdefault(vtec_id, []).append(data)
            etn = normalize_etn(vtec_id.split(".")[-1] if vtec_id else "")
            if etn:
                by_etn.setdefault(etn, []).append(data)

        for feature in features:
            props = feature.get("properties", {})

            if props.get("event") != "Flash Flood Warning":
                continue

            wfo = clean_wfo(props.get("wfo", ""))
            vtec_id = derive_alert_vtec_id(props)
            etn = normalize_etn(props.get("etn") or (vtec_id.split(".")[-1] if vtec_id else ""))

            data = ffs_tags.get((wfo, vtec_id)) if vtec_id else None

            if data is None and vtec_id:
                matches = by_vtec.get(vtec_id, [])
                if matches:
                    data = max(matches, key=lambda d: (tag_rank(d.get("tag", "")), d.get("issue_dt") or datetime(1900, 1, 1, tzinfo=timezone.utc)))

            if data is None and etn:
                matches = by_etn.get(etn, [])
                if matches:
                    preferred = [d for d in matches if clean_wfo(d.get("wfo", "")) == wfo]
                    pool = preferred or matches
                    data = max(pool, key=lambda d: (tag_rank(d.get("tag", "")), d.get("issue_dt") or datetime(1900, 1, 1, tzinfo=timezone.utc)))

            if not data or data.get("suppress"):
                continue

            source_product = data.get("source_product", "FFS")
            if not vtec_id:
                vtec_id = data.get("vtec_id", "")
                if vtec_id:
                    props["vtec_id"] = vtec_id
                    props["warning_number"] = vtec_id
                    props["etn"] = vtec_id.split(".")[-1]
            props["latest_flash_flood_text_issue_utc"] = iso_z(data.get("issue_dt"))
            props["vtec_end_utc"] = iso_z(data.get("end_dt"))

            old_tag = props.get("flash_flood_tag", "")
            new_tag = data.get("tag", "")

            if tag_rank(new_tag) > tag_rank(old_tag):
                props["flash_flood_tag"] = new_tag

            status = "EMERGENCY" if props.get("flash_flood_tag") == "emergency" else "CONSIDERABLE" if props.get("flash_flood_tag") == "considerable" else "BASE"

            if source_product == "FFS":
                props["ffs_detected"] = True
                props["product_code"] = "FFW+FFS"
                props["product_label"] = "FFW"
                status = "EMERGENCY" if props.get("flash_flood_tag") == "emergency" else "CONSIDERABLE" if props.get("flash_flood_tag") == "considerable" else "BASE"
                props["statement_status"] = status
                props["display_label"] = f"{status} FF.W {vtec_id.split('.')[-1]}".strip()
            else:
                props["product_code"] = "FFW"
                props["product_label"] = "FFW"
                props["statement_status"] = status
                props["display_label"] = f"{status} FF.W {vtec_id.split('.')[-1]}".strip()

            feature["properties"] = props

    if ffs_features:
        for feature in ffs_features:
            # These are text-derived FFW/FFS polygons with explicit FF.W/FF.S ETNs.
            # Keep them even when the polygon KML lacks a VTEC id; the later bbox
            # filter will remove anything outside the current view.
            features.append(feature)

    return features


def promote_text_warning_tags_by_overlap(features, ffs_tags, text_features):
    """Apply AFOS FFW/FFS VTEC and latest impact tag to overlapping warning polygons.

    FFS products upgrade the existing FF.W ETN; they should still label as
    FF.W #### with the latest BASE/CONSIDERABLE/EMERGENCY tag, not as FF.S.
    This also helps when IEM polygons lack ETN metadata.
    """
    if not features or not text_features:
        return features

    text_infos = []
    by_vtec = {}
    for feature in text_features:
        props = feature.get("properties", {})
        if props.get("event") != "Flash Flood Warning":
            continue
        vtec_id = derive_alert_vtec_id(props)
        if not vtec_id:
            continue
        gb = geom_coord_bounds(feature.get("geometry"))
        if not gb:
            continue
        wfo = clean_wfo(props.get("wfo", ""))
        tag_data = None
        if wfo:
            tag_data = ffs_tags.get((wfo, vtec_id))
        if tag_data is None:
            matches = [v for (twfo, tvtec), v in ffs_tags.items() if tvtec == vtec_id and not v.get("suppress")]
            if matches:
                tag_data = max(matches, key=lambda v: (tag_rank(v.get("tag", "")), v.get("issue_dt") or datetime(1900, 1, 1, tzinfo=timezone.utc)))
        tag = (tag_data or {}).get("tag") or props.get("flash_flood_tag", "")
        status = "EMERGENCY" if tag == "emergency" else "CONSIDERABLE" if tag == "considerable" else "BASE"
        text_infos.append({
            "bbox": gb,
            "vtec_id": vtec_id,
            "wfo": wfo,
            "tag": tag,
            "status": status,
            "end_dt": (tag_data or {}).get("end_dt"),
            "issue_dt": (tag_data or {}).get("issue_dt"),
            "source_product": (tag_data or {}).get("source_product") or props.get("source_product", "FFW"),
        })
        by_vtec.setdefault(vtec_id, []).append(text_infos[-1])

    if not text_infos:
        return features

    for feature in features:
        props = feature.get("properties", {})
        if props.get("event") != "Flash Flood Warning":
            continue
        fb = geom_coord_bounds(feature.get("geometry"))
        if not fb:
            continue

        vtec_id = derive_alert_vtec_id(props)
        etn = normalize_etn(props.get("etn") or (vtec_id.split(".")[-1] if vtec_id else ""))
        candidates = []
        if vtec_id:
            candidates.extend(by_vtec.get(vtec_id, []))
        if etn:
            candidates.extend([item for item in text_infos if normalize_etn(item.get("vtec_id", "").split(".")[-1]) == etn])
        if not candidates:
            candidates = text_infos
        best = None
        best_score = 0.0
        for item in candidates:
            score = bbox_overlap_fraction(fb, item["bbox"])
            # Same ETN is the controlling relationship; accept a lower overlap
            # because FFS LAT...LON polygons can be trimmed/updated relative to
            # the original IEM warning outline.
            same_etn = etn and normalize_etn(item.get("vtec_id", "").split(".")[-1]) == etn
            effective_score = score + (0.25 if same_etn else 0.0) + (0.50 if tag_rank(item.get("tag", "")) > 0 else 0.0)
            if effective_score > best_score:
                best = item
                best_score = effective_score

        if not best:
            continue

        props["vtec_id"] = best["vtec_id"]
        props["warning_number"] = best["vtec_id"]
        props["phen"] = "FF"
        props["sig"] = "W"
        props["etn"] = best["vtec_id"].split(".")[-1]
        if best.get("wfo"):
            props["wfo"] = best["wfo"]
        if tag_rank(best.get("tag", "")) >= tag_rank(props.get("flash_flood_tag", "")):
            props["flash_flood_tag"] = best.get("tag", "")
            props["statement_status"] = best["status"]
        status = "EMERGENCY" if props.get("flash_flood_tag") == "emergency" else "CONSIDERABLE" if props.get("flash_flood_tag") == "considerable" else "BASE"
        props["product_code"] = "FFW+FFS" if best.get("source_product") == "FFS" else "FFW"
        props["product_label"] = "FFW"
        props["display_label"] = f"{status} FF.W {props['etn']}"
        feature["properties"] = props

    return features


def alert_status_text_from_props(props):
    event = str(props.get("event", "")).lower()
    code = str(props.get("product_code", "")).upper()
    tag = str(props.get("flash_flood_tag", "")).lower()
    blob = " ".join(str(v) for v in props.values()).lower()

    if (
        tag == "emergency"
        or "flash flood emergency" in blob
        or "flash flood...emergency" in blob
        or "damage threat...catastrophic" in blob
        or "damage threat catastrophic" in blob
        or "catastrophic" in blob
        or "particularly dangerous situation" in blob
    ):
        props["flash_flood_tag"] = "emergency"
        return "EMERGENCY"

    if tag == "considerable" or "damage threat...considerable" in blob or "considerable" in blob:
        if "flash flood warning" in event or "ff.w" in blob or "ffs" in blob or code in ("FFW", "FFS", "FFW+FFS"):
            props["flash_flood_tag"] = "considerable"
            return "CONSIDERABLE"

    if "flood advisory" in event or code in ("FA.Y", "FAY"):
        return "ADVISORY"

    if code in ("FFS", "FFW+FFS") or props.get("ffs_detected"):
        if "flash flood warning" in event or code in ("FFW+FFS", "FFS"):
            statement_status = str(props.get("statement_status", "")).upper()
            if statement_status in ("BASE", "CONSIDERABLE", "EMERGENCY"):
                return statement_status
            return "BASE"
        return "STATEMENT"

    if "flash flood warning" in event or code == "FFW":
        return "BASE"

    return ""


def derive_alert_vtec_id(props):
    direct = props.get("vtec_id") or props.get("VTEC_ID") or props.get("vtec") or props.get("VTEC")
    if direct:
        direct = str(direct).strip().upper()
        match = re.search(r"\b(FF|FA)\.([A-Z])\.(\d{4})\b", direct)
        if match:
            return f"{match.group(1)}.{match.group(2)}.{match.group(3)}"

    blob = " ".join(str(v) for v in props.values())
    info = make_vtec_info(props, blob)
    if info.get("vtec_id"):
        return info["vtec_id"]

    loose = loose_vtec_from_text(blob)
    if loose:
        return f"{loose['phen']}.{loose['sig']}.{loose['etn']}"

    phen = str(prop_ci(props, "phen", "phenomena", "PHENOMENA", "phenom", "PHENOM")).upper().strip()
    sig = str(prop_ci(props, "sig", "significance", "SIGNIFICANCE", "SIG")).upper().strip()
    etn = normalize_etn(prop_ci(props, "etn", "ETN", "eventid", "EVENTID", "event_id", "eventID", "event", "EVENT"))
    event = str(props.get("event", "")).lower()
    code = str(props.get("product_code", "")).upper()

    if not phen:
        if "flash flood warning" in event or code in ("FFW", "FFS", "FFW+FFS"):
            phen = "FF"
        elif "flood advisory" in event or code in ("FA.Y", "FAY"):
            phen = "FA"

    if not sig:
        if phen == "FF":
            sig = "W"
        elif phen == "FA":
            sig = "Y"

    if phen and sig and etn:
        return f"{phen}.{sig}.{etn}"

    keyed_loose = loose_vtec_from_text(blob, default_phen=phen, default_sig=sig)
    if keyed_loose:
        return f"{keyed_loose['phen']}.{keyed_loose['sig']}.{keyed_loose['etn']}"

    return ""


def alert_display_code_and_number(props, vtec_id):
    code = str(props.get("product_code", "")).upper()
    status = alert_status_text_from_props(props)

    etn = ""
    phen = str(props.get("phen", "")).upper().strip()
    sig = str(props.get("sig", "")).upper().strip()

    if vtec_id:
        parts = vtec_id.split(".")
        if len(parts) == 3:
            phen, sig, etn = parts

    if not etn:
        etn = normalize_etn(prop_ci(props, "etn", "ETN", "eventid", "EVENTID", "event_id", "eventID"))

    if code in ("FFW", "FFS", "FFW+FFS") or props.get("ffs_detected") or phen == "FF":
        prefix = "FF.W"
    elif code in ("FA.Y", "FAY") or phen == "FA":
        prefix = "FA.Y"
    elif phen and sig:
        prefix = f"{phen}.{sig}"
    elif "flood advisory" in str(props.get("event", "")).lower():
        prefix = "FA.Y"
    else:
        prefix = "FF.W"

    return prefix, etn, status

def apply_display_labels_to_alerts(features):
    for feature in features:
        props = feature.get("properties", {})

        vtec_id = derive_alert_vtec_id(props)
        product_label = props.get("product_label") or props.get("product_code") or props.get("event") or "Alert"
        prefix, etn, status = alert_display_code_and_number(props, vtec_id)

        if vtec_id:
            parts = vtec_id.split(".")
            if len(parts) == 3:
                props["phen"] = parts[0]
                props["sig"] = parts[1]
                props["etn"] = parts[2]
            props["vtec_id"] = vtec_id
            props["warning_number"] = vtec_id

        if etn:
            props["display_label"] = f"{status + ' ' if status else ''}{prefix} {etn}".strip()
        else:
            # Prefer VTEC-style product codes over plain names. This prevents
            # labels like "Flood Advisory ADVISORY" when the source polygon
            # does not expose an advisory ETN.
            if prefix:
                props["display_label"] = f"{status + ' ' if status else ''}{prefix}".strip()
            else:
                props["display_label"] = f"{status + ' ' if status else ''}{product_label}".strip()

        props["status_text"] = status
        feature["properties"] = props

    return features

def draw_rank(feature):
    props = feature.get("properties", {})
    code = props.get("product_code", "")
    tag = str(props.get("flash_flood_tag", "")).lower()
    blob = " ".join(str(v) for v in props.values()).lower()
    if not tag:
        if (
            "flash flood emergency" in blob
            or "damage threat...catastrophic" in blob
            or "damage threat catastrophic" in blob
            or "catastrophic" in blob
            or "particularly dangerous situation" in blob
        ):
            tag = "emergency"
            props["flash_flood_tag"] = "emergency"
        elif "considerable" in blob:
            tag = "considerable"
            props["flash_flood_tag"] = "considerable"

    if tag == "emergency":
        return 100
    if code in ("FFS", "FFW+FFS") and tag == "considerable":
        return 95
    if tag == "considerable":
        return 90
    if code in ("FFS", "FFW+FFS"):
        return 80
    if props.get("event") == "Flash Flood Warning":
        return 60
    if props.get("event") == "Flood Advisory":
        return 30
    return 0


def fetch_iem_polygon_alerts_at_dt(valid_dt, west, south, east, north, deep_text=True):
    valid_dt = valid_dt.astimezone(timezone.utc)
    at = datetime_to_iem_at(valid_dt)
    now = time.time()

    qwest, qsouth, qeast, qnorth = quantize_alert_bbox(west, south, east, north, step=0.25)

    cache_key = json.dumps({
        "at": at,
        "west": round(qwest, 3),
        "south": round(qsouth, 3),
        "east": round(qeast, 3),
        "north": round(qnorth, 3),
        "deep_text": bool(deep_text),
        "csv_etn_enrichment": "geometry-safe plus AFOS-overlap v6",
    }, sort_keys=True)

    cached = ALERT_CACHE.get(cache_key)

    if cached and now - cached["time"] < ALERT_CACHE_TTL_SECONDS:
        return cached["geojson"]

    features = []

    try:
        kml_ffw = request_iem_kml(
            valid_dt,
            phen="FF",
            sig="W",
            limit1=True,
            addsvs=True,
        )
        gj_ffw = parse_kml_to_geojson(kml_ffw, requested_product_hint="FFW")
        ffw_features = [
            f for f in gj_ffw.get("features", [])
            if feature_valid_at_time(f, valid_dt)
        ]
        ffw_features = enrich_features_with_iem_csv(
            valid_dt,
            ffw_features,
            phen="FF",
            sig="W",
            limit1=True,
            addsvs=True,
        )
        features.extend(ffw_features)
    except Exception as e:
        print(f"[IEM FF.W fetch error] {e}")

    try:
        kml_fa = request_iem_kml(
            valid_dt,
            phen="FA",
            sig="Y",
            limit1=True,
            addsvs=False,
        )
        gj_fa = parse_kml_to_geojson(kml_fa, requested_product_hint="Flood Advisory")
        fa_features = [
            f for f in gj_fa.get("features", [])
            if feature_valid_at_time(f, valid_dt) and not is_county_like_flood_advisory(f)
        ]
        fa_features = enrich_features_with_iem_csv(
            valid_dt,
            fa_features,
            phen="FA",
            sig="Y",
            limit1=True,
            addsvs=False,
        )
        features.extend(fa_features)
    except Exception as e:
        print(f"[IEM FA.Y polygon-only fetch error] {e}")

    features = dedupe_features(features)

    if deep_text:
        features = apply_ffs_tags_to_features(
            features,
            valid_dt,
            west=qwest,
            south=qsouth,
            east=qeast,
            north=qnorth,
        )

    features = dedupe_features(features)
    features = filter_geojson_by_bbox(features, qwest, qsouth, qeast, qnorth)
    features = apply_display_labels_to_alerts(features)
    features.sort(key=draw_rank)

    gj = {
        "type": "FeatureCollection",
        "features": features,
        "source": "Valid-at-time IEM watchwarn + AFOS FFW/FFS text VTEC/impact-tag authority",
        "mode": "valid_at_utc",
        "at_utc": at,
        "ffw_valid_at_time": True,
        "latest_active_ffs_only": bool(deep_text),
        "future_ffs_products_excluded": True,
        "cancelled_expired_ffs_suppresses_base_warning": bool(deep_text),
        "latlon_parser": "NWS LAT...LON values treated as hundredths of degrees",
        "county_based_flood_advisories_filtered": True,
        "deep_ffw_ffs_text_check": bool(deep_text),
        "bbox_quantized_degrees": 0.25,
        "csv_etn_enrichment": "geometry-safe plus AFOS-overlap v6",
    }

    ALERT_CACHE[cache_key] = {
        "time": now,
        "geojson": gj,
    }

    trim_cache(ALERT_CACHE, ALERT_CACHE_MAX_ITEMS)
    return gj


def fetch_iem_polygon_alerts_at_token(token, west, south, east, north, deep_text=True):
    return fetch_iem_polygon_alerts_at_dt(token_to_datetime(token), west, south, east, north, deep_text=deep_text)


@app.route("/")
@app.route("/viewer")
def viewer():
    response = Response(VIEWER_HTML, mimetype="text/html")
    response.headers["Cache-Control"] = "no-store, max-age=0"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    return response





@app.route("/healthz")
def healthz():
    return jsonify({
        "ok": True,
        "app_title": APP_TITLE,
        "author": APP_AUTHOR,
        "generated_utc": now_utc_iso(),
    })


@app.route("/api/render.png")
def api_render_png():
    product = request.args.get("product", DEFAULT_PRODUCT)
    param = request.args.get("param", product).strip() or product
    requested_token = request.args.get("time", "").strip() or None

    try:
        param, pinfo = parameter_info(param, fallback_product=product)

        west = float(request.args.get("west", -91.95))
        south = float(request.args.get("south", 27.85))
        east = float(request.args.get("east", -88.25))
        north = float(request.args.get("north", 31.45))
        width = int(request.args.get("width", 1600))

        png_path, render_meta = render_parameter_png(
            param,
            product,
            requested_token,
            west,
            south,
            east,
            north,
            width,
        )

        response = send_file(png_path, mimetype="image/png")
        response.headers["Cache-Control"] = "no-store, max-age=0"
        response.headers["X-MRMS-Parameter"] = ascii_header_value(param)
        response.headers["X-MRMS-Product"] = ascii_header_value(render_meta.get("product", product))
        response.headers["X-MRMS-Units"] = ascii_header_value(render_meta.get("units", "cfs/mi^2"))
        response.headers["X-MRMS-Time"] = ascii_header_value(render_meta.get("file_time_utc", requested_token or "latest"))
        response.headers["X-MRMS-Generated-UTC"] = ascii_header_value(render_meta.get("generated_utc", now_utc_iso()))

        return response

    except Exception as e:
        print(f"[render error] {e}")
        return jsonify({
            "error": str(e),
            "product": product,
            "param": param,
            "requested_time": requested_token,
        }), 500


@app.route("/api/value")
def api_value():
    product = request.args.get("product", DEFAULT_PRODUCT)
    param = request.args.get("param", product).strip() or product
    requested_token = request.args.get("time", "").strip() or None

    try:
        param, pinfo = parameter_info(param, fallback_product=product)

        lat = float(request.args.get("lat"))
        lon = float(request.args.get("lon"))

        value, file_time = sample_parameter_value(param, product, requested_token, lat, lon)

        if value is None:
            return jsonify({
                "product": product,
                "param": param,
                "lat": lat,
                "lon": lon,
                "value_m3s_per_km2": None,
                "value_cfs_per_smi": None,
                "display_value": None,
                "display_units": pinfo.get("units", "cfs/mi^2"),
                "native_value": None,
                "native_units": pinfo.get("native_units", "m^3/s/km^2"),
                "file_time_utc": file_time,
            })

        value.update({
            "product": product,
            "param": param,
            "lat": lat,
            "lon": lon,
            "file_time_utc": file_time,
        })

        return jsonify(value)

    except Exception as e:
        return jsonify({
            "error": str(e),
            "product": product,
            "param": param,
            "requested_time": requested_token,
        }), 500


def sample_point_value_payload(param, product, requested_token, lat, lon):
    param, pinfo = parameter_info(param, fallback_product=product)
    value, file_time = sample_parameter_value(param, product, requested_token, lat, lon)

    payload = {
        "product": product,
        "param": param,
        "lat": float(lat),
        "lon": float(lon),
        "display_units": pinfo.get("units", "cfs/mi^2"),
        "native_units": pinfo.get("native_units", "m^3/s/km^2"),
        "file_time_utc": file_time,
    }

    if value is None:
        payload.update({
            "found": False,
            "value_m3s_per_km2": None,
            "value_cfs_per_smi": None,
            "display_value": None,
            "native_value": None,
        })
        return payload

    value.update(payload)
    value["found"] = True
    return value


def point_value_trend_for_parameter(param, product, requested_token, lat, lon, samples=3, step_minutes=10):
    param, pinfo = parameter_info(param, fallback_product=product)
    samples = max(2, min(int(samples or 3), 6))
    step_minutes = max(1, min(int(step_minutes or 10), 60))

    base_token = effective_trend_base_token_for_parameter(param, product, requested_token)
    if not base_token:
        payload = sample_point_value_payload(param, product, requested_token, lat, lon)
        payload["trend"] = {
            "available": False,
            "reason": "Could not determine a valid base time for point trend sampling.",
            "points": [],
            "samples": samples,
            "step_minutes": step_minutes,
        }
        return payload

    tokens = [token_add_minutes(base_token, -i * step_minutes) for i in range(samples - 1, -1, -1)]
    points = []
    latest_payload = None

    for token in tokens:
        minutes_ago = int(round((token_to_datetime(base_token) - token_to_datetime(token)).total_seconds() / 60.0))
        try:
            payload = sample_point_value_payload(param, product, token, lat, lon)
            found = bool(payload.get("found"))
            value = payload.get("display_value") if found else None
            points.append({
                "token": token,
                "label": token_to_label(token),
                "minutes_ago": minutes_ago,
                "found": found,
                "mean": value,
                "value": value,
                "file_time_utc": payload.get("file_time_utc", ""),
            })
            if token == base_token:
                latest_payload = payload
        except Exception as e:
            points.append({
                "token": token,
                "label": token_to_label(token),
                "minutes_ago": minutes_ago,
                "found": False,
                "mean": None,
                "value": None,
                "error": str(e),
            })

    if latest_payload is None:
        latest_payload = sample_point_value_payload(param, product, base_token, lat, lon)

    valid_points = [p for p in points if p.get("found") and p.get("mean") is not None]
    if len(valid_points) >= 2:
        delta = float(valid_points[-1]["mean"]) - float(valid_points[0]["mean"])
    else:
        delta = None

    latest_payload["trend"] = {
        "available": len(valid_points) >= 2,
        "base_token": base_token,
        "samples": samples,
        "step_minutes": step_minutes,
        "points": points,
        "delta": delta,
    }
    return latest_payload


@app.route("/api/value_trend")
def api_value_trend():
    product = request.args.get("product", DEFAULT_PRODUCT)
    param = request.args.get("param", product).strip() or product
    requested_token = request.args.get("time", "").strip() or None
    samples = request.args.get("samples", 3)
    step_minutes = request.args.get("step_minutes", 10)

    try:
        lat = float(request.args.get("lat"))
        lon = float(request.args.get("lon"))
        payload = point_value_trend_for_parameter(
            param,
            product,
            requested_token,
            lat,
            lon,
            samples=samples,
            step_minutes=step_minutes,
        )
        return jsonify(payload)
    except Exception as e:
        return jsonify({
            "error": str(e),
            "product": product,
            "param": param,
            "requested_time": requested_token,
        }), 500


@app.route("/api/max")
def api_max():
    product = request.args.get("product", DEFAULT_PRODUCT)
    param = request.args.get("param", product).strip() or product
    requested_token = request.args.get("time", "").strip() or None

    try:
        param, pinfo = parameter_info(param, fallback_product=product)

        west = float(request.args.get("west", -91.95))
        south = float(request.args.get("south", 27.85))
        east = float(request.args.get("east", -88.25))
        north = float(request.args.get("north", 31.45))
        width = int(request.args.get("width", 1200))
        min_cfs = float(request.args.get("min_cfs", 0.0))

        value, file_time, mode = find_extreme_value_for_parameter(
            param,
            product,
            requested_token,
            west,
            south,
            east,
            north,
            width,
            min_cfs=min_cfs,
        )

        if value is None:
            return jsonify({
                "product": product,
                "param": param,
                "found": False,
                "mode": mode,
                "file_time_utc": file_time,
                "message": "No finite pixels found in the current view for this parameter.",
            })

        value.update({
            "product": product,
            "param": param,
            "found": True,
            "mode": mode,
            "file_time_utc": file_time,
            "west": west,
            "south": south,
            "east": east,
            "north": north,
        })

        return jsonify(value)

    except Exception as e:
        return jsonify({
            "error": str(e),
            "product": product,
            "param": param,
            "requested_time": requested_token,
        }), 500


@app.route("/api/area_average")
def api_area_average():
    product = request.args.get("product", DEFAULT_PRODUCT)
    param = request.args.get("param", product).strip() or product
    requested_token = request.args.get("time", "").strip() or None

    try:
        lat = float(request.args.get("lat"))
        lon = float(request.args.get("lon"))
        radius_m = float(request.args.get("radius_m"))
        if radius_m <= 0:
            raise ValueError("radius_m must be greater than zero")

        payload = area_average_for_parameter(
            param,
            product,
            requested_token,
            lat,
            lon,
            radius_m,
        )
        return jsonify(payload)

    except Exception as e:
        return jsonify({
            "error": str(e),
            "product": product,
            "param": param,
            "requested_time": requested_token,
        }), 500


def effective_trend_base_token_for_parameter(param, product, requested_token):
    if requested_token:
        return requested_token

    try:
        sources = resolve_parameter_sources(param, product, None)
        metas = sources.get("metas") or []
        for meta in metas:
            token = meta.get("token") or meta.get("requested_token")
            if token:
                return token
    except Exception as e:
        print(f"[area trend token fallback] {param}: {e}")

    try:
        raw_product = raw_product_for_parameter_backend(param, product)
        item = choose_remote_file(raw_product, requested_token=None)
        return item.get("token")
    except Exception:
        return None


def raw_product_for_parameter_backend(param, product):
    param, pinfo = parameter_info(param, fallback_product=product)
    return pinfo.get("product") or product or param


def area_average_trend_for_polygon(param, product, requested_token, vertices, samples=3, step_minutes=10):
    samples = max(2, min(int(samples or 3), 6))
    step_minutes = max(1, min(int(step_minutes or 10), 60))

    base_token = effective_trend_base_token_for_parameter(param, product, requested_token)
    if not base_token:
        payload = area_average_for_polygon(param, product, requested_token, vertices)
        payload["trend"] = {
            "available": False,
            "reason": "Could not determine a valid base time for trend sampling.",
            "points": [],
            "samples": samples,
            "step_minutes": step_minutes,
        }
        return payload

    tokens = []
    for i in range(samples - 1, -1, -1):
        tokens.append(token_add_minutes(base_token, -i * step_minutes))

    points = []
    latest_payload = None
    for token in tokens:
        minutes_ago = int(round((token_to_datetime(base_token) - token_to_datetime(token)).total_seconds() / 60.0))
        try:
            payload = area_average_for_polygon(param, product, token, vertices)
            found = bool(payload.get("found"))
            mean = payload.get("mean") if found else None
            point = {
                "token": token,
                "label": token_to_label(token),
                "minutes_ago": minutes_ago,
                "found": found,
                "mean": mean,
                "file_time_utc": payload.get("file_time_utc", ""),
            }
            if found and payload.get("coverage_thresholds") is not None:
                point["coverage_thresholds"] = payload.get("coverage_thresholds", [])
                point["max"] = payload.get("max")
            points.append(point)
            if token == base_token:
                latest_payload = payload
        except Exception as e:
            points.append({
                "token": token,
                "label": token_to_label(token),
                "minutes_ago": minutes_ago,
                "found": False,
                "mean": None,
                "error": str(e),
            })

    if latest_payload is None:
        # Keep the popup useful even if the exact base-token trend sample snapped/failed.
        latest_payload = area_average_for_polygon(param, product, base_token, vertices)

    valid_points = [p for p in points if p.get("found") and p.get("mean") is not None]
    if len(valid_points) >= 2:
        delta = float(valid_points[-1]["mean"]) - float(valid_points[0]["mean"])
    else:
        delta = None

    latest_payload["trend"] = {
        "available": len(valid_points) >= 2,
        "base_token": base_token,
        "samples": samples,
        "step_minutes": step_minutes,
        "points": points,
        "delta": delta,
    }
    return latest_payload


@app.route("/api/area_average_polygon_trend", methods=["POST"])
def api_area_average_polygon_trend():
    body = request.get_json(silent=True) or {}
    product = str(body.get("product", DEFAULT_PRODUCT)).strip() or DEFAULT_PRODUCT
    param = str(body.get("param", product)).strip() or product
    requested_token = str(body.get("time", "")).strip() or None
    vertices = body.get("vertices") or []
    samples = body.get("samples", 3)
    step_minutes = body.get("step_minutes", 10)
    try:
        payload = area_average_trend_for_polygon(param, product, requested_token, vertices, samples=samples, step_minutes=step_minutes)
        return jsonify(payload)
    except Exception as e:
        return jsonify({
            "error": str(e),
            "product": product,
            "param": param,
            "requested_time": requested_token,
        }), 500


@app.route("/api/area_average_polygon", methods=["POST"])
def api_area_average_polygon():
    body = request.get_json(silent=True) or {}
    product = str(body.get("product", DEFAULT_PRODUCT)).strip() or DEFAULT_PRODUCT
    param = str(body.get("param", product)).strip() or product
    requested_token = str(body.get("time", "")).strip() or None
    vertices = body.get("vertices") or []
    try:
        payload = area_average_for_polygon(param, product, requested_token, vertices)
        return jsonify(payload)
    except Exception as e:
        return jsonify({
            "error": str(e),
            "product": product,
            "param": param,
            "requested_time": requested_token,
        }), 500


@app.route("/api/alerts")
def api_alerts():
    requested_token = request.args.get("time", "").strip() or None
    deep_text = str(request.args.get("deep", "1")).strip().lower() not in ("0", "false", "no", "off")

    try:
        west = float(request.args.get("west", -94.5))
        south = float(request.args.get("south", 27.0))
        east = float(request.args.get("east", -84.5))
        north = float(request.args.get("north", 33.0))

        if requested_token:
            return jsonify(fetch_iem_polygon_alerts_at_token(requested_token, west, south, east, north, deep_text=deep_text))

        return jsonify(fetch_iem_polygon_alerts_at_dt(now_utc(), west, south, east, north, deep_text=deep_text))

    except Exception as e:
        print(f"[alerts error] {e}")
        return jsonify({
            "error": str(e),
            "requested_time": requested_token,
        }), 500


@app.route("/api/archive/list")
def api_archive_list():
    product = request.args.get("product", DEFAULT_PRODUCT)

    try:
        product, product_meta = product_info(product)

        local_items = list_local_archive(product)

        try:
            remote_items = list_remote_files(product, limit=ARCHIVE_REMOTE_LIST_LIMIT)
        except Exception as e:
            print(f"[remote archive list error] {e}")
            remote_items = []

        seen = set()
        merged = []

        for item in local_items + remote_items:
            token = item["token"]
            if token in seen:
                continue
            seen.add(token)
            merged.append({
                "token": token,
                "label": item["label"],
                "source": item.get("source", "unknown"),
            })

        merged.sort(key=lambda x: x["token"], reverse=True)

        # Keep the picker focused on a true 24-hour archive window. The cutoff is
        # based on the newest available token instead of wall-clock time so a delayed
        # MRMS feed still shows the full previous 24 hours.
        if merged:
            newest_dt = token_to_datetime(merged[0]["token"])
            cutoff_dt = newest_dt - timedelta(hours=ARCHIVE_LOOKBACK_HOURS)
            merged = [
                item for item in merged
                if token_to_datetime(item["token"]) >= cutoff_dt
            ]

        return jsonify({
            "product": product,
            "times": merged,
            "lookback_hours": ARCHIVE_LOOKBACK_HOURS,
            "step_minutes": product_meta.get("step_minutes", MRMS_TIME_STEP_MINUTES),
        })

    except Exception as e:
        return jsonify({
            "error": str(e),
            "product": product,
        }), 500


@app.route("/api/archive/capture")
def api_archive_capture():
    product = request.args.get("product", DEFAULT_PRODUCT)

    try:
        payload = capture_latest_to_archive(product)
        return jsonify(payload)

    except Exception as e:
        return jsonify({
            "error": str(e),
            "product": product,
        }), 500


@app.route("/api/metadata")
def api_metadata():
    return jsonify({
        "app_title": APP_TITLE,
        "author": APP_AUTHOR,
        "disclaimer": APP_DISCLAIMER,
        "products": PRODUCTS,
        "parameters": PARAMETERS,
        "default_product": DEFAULT_PRODUCT,
        "cache_dir": CACHE_DIR,
        "archive_dir": ARCHIVE_DIR,
        "units": "cfs/mi^2",
        "conversion_from_m3s_per_km2_to_cfs_per_mi2": M3S_PER_KM2_TO_CFS_PER_SQMI,
        "legend_breaks_cfs_per_mi2": [0, 200, 400, 600, 1000, 2000],
        "alerts_source": "IEM watchwarn.py valid-at-time polygons + AFOS retrieve.py FFW/FFS text for authoritative VTEC/impact tags",
        "alert_speed_mode": "Both panels share one alert fetch; alert bboxes are quantized; AFOS 503s are negative-cached; deep text check can be disabled in the GUI.",
        "ffw": "FF.W storm-based valid-at-time polygons",
        "ffs_followups": "Latest FFS at archive/current time only; CAN/EXP suppresses older FFS and base warning",
        "draw_order": "FA.Y bottom, FFW middle, considerable/emergency/latest FFS top",
        "difference_scale": "Derived difference products are colorized from -200 to +200 cfs/mi^2 with tight color changes near zero.",
        "archive_fallback": "If a selected remote archive time has rolled off NCEP, the viewer snaps to the nearest advertised remote file instead of constructing a stale exact URL.",
        "latlon_parser": "NWS LAT...LON values parsed as hundredths of degrees",
        "flood_advisory": "FA.Y fetched polygon-only where available; county/parish-like advisories filtered",
        "opacity_default": "100 percent for streamflow pixels",
        "warning_labels": "Tooltips show AFOS-derived FF.W/FF.S VTEC number plus BASE, CONSIDERABLE, EMERGENCY, or ADVISORY status when available; click polygons for details",
        "max_pixel_marker": "Optional current-view max streamflow pixel search via /api/max; difference parameters mark largest absolute difference",
        "area_average_tool": "Optional mirrored Leaflet free-draw polygon tool; /api/area_average_polygon_trend returns panel-specific mean/min/max plus a compact 3-sample/30-minute mean trend sparkline",
        "two_panel_layout": "Left and right panel parameter selections persist in browser localStorage; maps pan and zoom together",
        "derived_parameters": {
            "CREST_DIFF_10M": "Current/selected CREST minus the previous CREST update 10 minutes earlier; red increase, blue decrease",
            "HP_MINUS_CREST": "HP Max Unit Streamflow minus regular CREST Max Unit Streamflow; red means HP is higher, blue means HP is lower",
        },
        "all_displayed_times": "UTC/Z",
        "archive_lookback_hours": ARCHIVE_LOOKBACK_HOURS,
        "archive_step_minutes": MRMS_TIME_STEP_MINUTES,
        "speedups": [
            "background archive disabled",
            "windowed GRIB read",
            "remote MRMS directory cache",
            "rendered PNG cache",
            "alert query cache",
            "FFS text cache",
            "AFOS text failure cache",
            "single shared alert fetch for both panels",
            "optional hover readout debounce",
            "Pillow PNG writing with compress_level=1",
            "fast render mode display-resolution cap",
            "skip unchanged client-side panel renders",
            "single-flight render and download locks",
            "parallel trailing-window MRMS frame downloads",
            "lower auto-render width",
        ],
    })


def archive_worker():
    while True:
        try:
            for product in PRODUCTS:
                try:
                    capture_latest_to_archive(product)
                    print(f"[archive worker] captured {product}")
                except Exception as e:
                    print(f"[archive worker] {product}: {e}")
                time.sleep(2)
        except Exception as e:
            print(f"[archive worker] {e}")

        time.sleep(ARCHIVE_INTERVAL_SECONDS)


if __name__ == "__main__":
    if ENABLE_BACKGROUND_ARCHIVE:
        t = threading.Thread(target=archive_worker, daemon=True)
        t.start()

    port = int(os.environ.get("PORT", "8080"))
    app.run(host="0.0.0.0", port=port, debug=False)
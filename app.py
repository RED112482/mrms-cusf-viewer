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
from email.utils import parsedate_to_datetime
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

print("RUNNING FILE:", os.path.abspath(__file__))
print("APP7 VERSION: realtime-viewer-032-animated-gif")

APP_USER_AGENT = "MRMSUnitStreamflowViewer/1.0 KevinGilmore"
DEFAULT_PRODUCT = "CREST"

CACHE_DIR = os.path.join(tempfile.gettempdir(), "mrms_unit_streamflow_cache")
ARCHIVE_DIR = os.path.join(CACHE_DIR, "archive")
os.makedirs(CACHE_DIR, exist_ok=True)
os.makedirs(ARCHIVE_DIR, exist_ok=True)

ENABLE_BACKGROUND_ARCHIVE = False
ARCHIVE_INTERVAL_SECONDS = 10 * 60

MRMS_TIME_STEP_MINUTES = 10
ARCHIVE_LOOKBACK_HOURS = 24
ARCHIVE_LOOKBACK_MINUTES = ARCHIVE_LOOKBACK_HOURS * 60
# Some radar mosaics update around every 2 minutes, so keep enough remote
# directory entries to cover a full 24-hour picker/loop window for both radar
# and 10-minute FLASH/QPE products.
ARCHIVE_REMOTE_LIST_LIMIT = int((ARCHIVE_LOOKBACK_MINUTES / 2) + 80)

# Historical MRMS archive on NOAA's public AWS bucket. The live NCEP
# directory is still used for the newest files, while arbitrary selected
# dates are resolved from this day-partitioned archive.
MRMS_S3_BASE_URL = "https://noaa-mrms-pds.s3.amazonaws.com"
S3_ARCHIVE_LIST_CACHE = {}
S3_ARCHIVE_LIST_TTL_SECONDS = 15 * 60
S3_PREFIX_CACHE = None
S3_PREFIX_CACHE_TIME = 0.0
S3_PREFIX_CACHE_TTL_SECONDS = 6 * 60 * 60

S3_PRODUCT_PREFIX_CANDIDATES = {
    "CREST": ["FLASH_CREST_MAXUNITSTREAMFLOW_00.00", "CREST_MAXUNITSTREAMFLOW_00.00"],
    "SAC": ["FLASH_SAC_MAXUNITSTREAMFLOW_00.00", "SAC_MAXUNITSTREAMFLOW_00.00"],
    "HP": ["FLASH_HP_MAXUNITSTREAMFLOW_00.00", "HP_MAXUNITSTREAMFLOW_00.00"],
    "PRECIPRATE": ["PrecipRate_00.00"],
    "QPE1H": ["RadarOnly_QPE_01H_00.00"],
    "QPE3H": ["RadarOnly_QPE_03H_00.00"],
    "QPE15M": ["RadarOnly_QPE_15M_00.00"],
    "QPE6H": ["RadarOnly_QPE_06H_00.00"],
    "RALA": ["ReflectivityAtLowestAltitude_00.50"],
    "REFLQC": ["MergedReflectivityQC_00.50"],
    "REFLCOMP": ["MergedReflectivityQCComposite_00.50"],
    "REFL10C": ["Reflectivity_-10C_00.50"],
    "REFL0C": ["Reflectivity_0C_00.50"],
}

CACHE_TTL_SECONDS = 10 * 60

REMOTE_LIST_CACHE = {}
REMOTE_LIST_TTL_SECONDS = 45
REMOTE_LIST_CONNECT_TIMEOUT_SECONDS = 5
REMOTE_LIST_READ_TIMEOUT_SECONDS = 12

# Lightweight LIVE freshness probes. The browser polls one API endpoint every
# minute; the server checks only the active products' small `.latest` objects
# with HEAD requests instead of scraping full NCEP directory listings. Failed
# probes retain the last-known-good token and back off exponentially.
LIVE_PROBE_CACHE = {}
LIVE_PROBE_LOCK = threading.RLock()
LIVE_PROBE_CONNECT_TIMEOUT_SECONDS = 4
LIVE_PROBE_READ_TIMEOUT_SECONDS = 8
LIVE_PROBE_SUCCESS_TTL_SECONDS = 45
LIVE_PROBE_BACKOFF_BASE_SECONDS = 30
LIVE_PROBE_BACKOFF_MAX_SECONDS = 15 * 60
LIVE_PROBE_PUBLICATION_LAG_SECONDS = 20
LIVE_LATEST_DOWNLOAD_CONNECT_TIMEOUT_SECONDS = 5
LIVE_LATEST_DOWNLOAD_READ_TIMEOUT_SECONDS = 60

# Requested times older than this should use the NOAA AWS day-partitioned
# archive first instead of asking the live NCEP directory about stale files.
HISTORICAL_REMOTE_DIRECTORY_MAX_AGE_HOURS = 6

RENDER_CACHE_TTL_SECONDS = 10 * 60
RENDER_STYLE_VERSION = "20260904_realtime_sim_style_esri_nearblack_screenshot_v3"

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

# Official NOAA/NWS reference-map County Warning Area layer. The same source
# powers the optional yellow CWA overlay and the exact CWA-shaped alarm masks.
NWS_CWA_FEATURE_URL = "https://mapservices.weather.noaa.gov/static/rest/services/nws_reference_maps/nws_reference_map/FeatureServer/1"
NWS_CWA_CACHE_TTL_SECONDS = 6 * 60 * 60
NWS_CWA_FAILURE_TTL_SECONDS = 5 * 60
NWS_CWA_LIST_CACHE = {"time": 0.0, "items": None, "error": ""}
NWS_CWA_GEOMETRY_CACHE = {}
NWS_CWA_CACHE_LOCK = threading.RLock()

FFS_TEXT_CACHE = OrderedDict()
FFS_TEXT_CACHE_TTL_SECONDS = 20 * 60
FFS_TEXT_CACHE_MAX_ITEMS = 160
FFS_TEXT_CACHE_LOCK = threading.RLock()

# Official NWS active-alert authority for current/live flash flood warnings.
# This avoids leaving warnings at BASE when per-office AFOS text discovery fails.
NWS_ACTIVE_FFW_CACHE = OrderedDict()
NWS_ACTIVE_FFW_CACHE_TTL_SECONDS = 30
NWS_ACTIVE_FFW_FAILURE_TTL_SECONDS = 15
NWS_ACTIVE_FFW_CACHE_MAX_ITEMS = 8
NWS_ACTIVE_FFW_LOCK = threading.RLock()
NWS_ACTIVE_FFW_LIVE_TOLERANCE_MINUTES = 20

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
    "QPE3H": {
        "display": "3hr QPE",
        "directory": "https://mrms.ncep.noaa.gov/2D/RadarOnly_QPE_03H/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/RadarOnly_QPE_03H/MRMS_RadarOnly_QPE_03H.latest.grib2.gz",
        "file_prefix": "MRMS_RadarOnly_QPE_03H_00.00_",
        "step_minutes": 60,
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
    "REFL0C": {
        "display": "Reflectivity at 0°C",
        "directory": "https://mrms.ncep.noaa.gov/2D/Reflectivity_0C/",
        "latest_url": "https://mrms.ncep.noaa.gov/2D/Reflectivity_0C/MRMS_Reflectivity_0C.latest.grib2.gz",
        "file_prefix": "MRMS_Reflectivity_0C_00.50_",
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

# Computed P palette and 0-5000 range copied from CMUSF_Auto.py.
# Exact zero is made transparent at render time, matching the viewer's
# existing zero-value transparency behavior.
COMPUTED_P_MAX = 5000.0
# CMUSF_Auto.py converts native CREST to C with a factor of 91.8 before
# clipping and differencing; preserve that exact source computation here.
COMPUTED_P_CREST_CONVERSION = 91.8
COMPUTED_P_COLOR_STOPS = [
    (0.0,    "#000000"),
    (1000.0, "#00ff00"),
    (2000.0, "#ffff00"),
    (3000.0, "#ffa500"),
    (4000.0, "#ff0000"),
    (5000.0, "#ff00ff"),
]
COMPUTED_P_CMAP = LinearSegmentedColormap.from_list(
    "computed_p",
    [(v / COMPUTED_P_MAX, c) for v, c in COMPUTED_P_COLOR_STOPS],
    N=256,
)
COMPUTED_P_NORM = Normalize(vmin=0.0, vmax=COMPUTED_P_MAX, clip=True)

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

# Dedicated rate-of-change palette. The normalized color progression is shared
# by CREST Δ10m (±300 cfs/mi^2) and instantaneous rain-rate Δ10m (±10 in/hr).
# CREST anchors: -300 white, -200 purple, -100 cyan, blue to black at 0;
# then red, +100 magenta, +200 orange, +300 white.
RATE_CHANGE_COLOR_STOPS = [
    (0.000000, "#ffffff"),
    (0.166667, "#800080"),
    (0.333333, "#00ffff"),
    (0.426667, "#0096ff"),
    (0.480000, "#0033ff"),
    (0.500000, "#000000"),
    (0.520000, "#ff0000"),
    (0.573333, "#ff4bff"),
    (0.666667, "#ff00ff"),
    (0.833333, "#ffa500"),
    (1.000000, "#ffffff"),
]
RATE_CHANGE_CMAP = LinearSegmentedColormap.from_list(
    "rate_change_shared", RATE_CHANGE_COLOR_STOPS, N=1201
)
CREST_RATE_CHANGE_ABS_MAX = 300.0
CREST_RATE_CHANGE_NORM = Normalize(
    vmin=-CREST_RATE_CHANGE_ABS_MAX, vmax=CREST_RATE_CHANGE_ABS_MAX, clip=True
)
RAINRATE_DIFF_ABS_MAX_INHR = 10.0
RAINRATE_DIFF_NORM = Normalize(
    vmin=-RAINRATE_DIFF_ABS_MAX_INHR, vmax=RAINRATE_DIFF_ABS_MAX_INHR, clip=True
)

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

# All QPE/QPF delta products use the same normalized rate-of-change palette
# as CREST Δ products. The precipitation-change range is fixed at ±10 inches:
# -10 white, -6.67 purple, -3.33 cyan, blue to black at 0, then red,
# +3.33 magenta, +6.67 orange, and +10 white.
QPE_DIFF_ABS_MAX_IN = 10.0
MRMS_QPE_DIFF_NORM = Normalize(
    vmin=-QPE_DIFF_ABS_MAX_IN, vmax=QPE_DIFF_ABS_MAX_IN, clip=True
)

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
    # MRMS FLASH Products
    "CREST": {
        "display": "CREST Max Unit Streamflow",
        "kind": "raw", "product": "CREST",
        "units": "cfs/mi^2", "native_units": "m^3/s/km^2", "style": "streamflow",
    },
    "CREST_DIFF_10M": {
        "display": "CREST Δ 10 min",
        "kind": "difference", "product": "CREST",
        "units": "cfs/mi^2", "native_units": "m^3/s/km^2", "style": "crest_rate_change",
        "description": "Current CREST minus CREST 10 minutes earlier",
    },
    "CREST_DIFF_30M": {
        "display": "CREST Δ 30 min",
        "kind": "difference", "product": "CREST",
        "units": "cfs/mi^2", "native_units": "m^3/s/km^2", "style": "crest_rate_change",
        "difference_minutes": 30, "difference_tolerance_seconds": 360,
        "description": "Cumulative CREST change over the preceding 30 minutes",
    },
    "SAC": {
        "display": "SAC Max Unit Streamflow",
        "kind": "raw", "product": "SAC",
        "units": "cfs/mi^2", "native_units": "m^3/s/km^2", "style": "streamflow",
    },
    "HP": {
        "display": "HP Max Unit Streamflow",
        "kind": "raw", "product": "HP",
        "units": "cfs/mi^2", "native_units": "m^3/s/km^2", "style": "streamflow",
    },
    "HP_MINUS_CREST": {
        "display": "HP - CREST Difference",
        "kind": "difference", "product": "HP",
        "units": "cfs/mi^2", "native_units": "m^3/s/km^2", "style": "difference",
        "description": "HP Max Unit Streamflow minus CREST Max Unit Streamflow",
    },

    # MRMS Instantaneous
    "RAINRATE": {
        "display": "Instantaneous Rain Rate",
        "kind": "raw", "product": "PRECIPRATE",
        "units": "in/hr", "native_units": "mm/hr", "style": "rainrate",
    },
    "RAINRATE_DIFF_10M": {
        "display": "Instantaneous Rain Rate Δ 10 min",
        "kind": "difference", "product": "PRECIPRATE",
        "units": "in/hr", "native_units": "mm/hr", "style": "rainrate_difference",
        "description": "Current instantaneous rain rate minus instantaneous rain rate 10 minutes earlier",
    },
    "RAINRATE_MAX_30M": {
        "display": "Instantaneous 30 min Max Rain Rate",
        "kind": "derived_max", "product": "PRECIPRATE",
        "units": "in/hr", "native_units": "mm/hr", "style": "rainrate",
        "description": "Pixel-wise maximum instantaneous rain rate during the trailing 30 minutes",
    },

    # MRMS Rain Totals
    "QPE30M": {
        "display": "30-min QPE",
        "kind": "derived_sum", "product": "QPE15M",
        "units": "in", "native_units": "mm", "style": "qpe",
        "description": "Current and previous 15-minute RadarOnly QPE combined into a 30-minute total",
    },
    "QPE30M_DIFF_30M": {
        "display": "30 min QPE Δ",
        "kind": "difference", "product": "QPE15M",
        "units": "in", "native_units": "mm", "style": "qpe_difference",
        "description": "Current 30-minute QPE minus the preceding non-overlapping 30-minute QPE",
    },
    "QPE1H": {
        "display": "1hr QPE",
        "kind": "raw", "product": "QPE1H",
        "units": "in", "native_units": "mm", "style": "qpe",
    },
    "QPE1H_DIFF_1H": {
        "display": "1hr QPE Δ",
        "kind": "difference", "product": "QPE1H",
        "units": "in", "native_units": "mm", "style": "qpe_difference",
        "difference_minutes": 60, "difference_tolerance_seconds": 480,
        "description": "Current rolling 1-hour QPE minus the rolling 1-hour QPE one hour earlier",
    },
    "QPE3H": {
        "display": "3hr QPE",
        "kind": "raw", "product": "QPE3H",
        "units": "in", "native_units": "mm", "style": "qpe",
    },
    "QPE3H_DIFF_3H": {
        "display": "3hr QPE Δ",
        "kind": "difference", "product": "QPE3H",
        "units": "in", "native_units": "mm", "style": "qpe_difference",
        "difference_minutes": 180, "difference_tolerance_seconds": 480,
        "description": "Current rolling 3-hour QPE minus the rolling 3-hour QPE three hours earlier",
    },
    "QPE6H": {
        "display": "6hr QPE",
        "kind": "raw", "product": "QPE6H",
        "units": "in", "native_units": "mm", "style": "qpe",
    },
    "QPE6H_DIFF_6H": {
        "display": "6hr QPE Δ",
        "kind": "difference", "product": "QPE6H",
        "units": "in", "native_units": "mm", "style": "qpe_difference",
        "difference_minutes": 360, "difference_tolerance_seconds": 480,
        "description": "Current rolling 6-hour QPE minus the rolling 6-hour QPE six hours earlier",
    },

    # MRMS Radar Products
    "RALA": {
        "display": "Reflectivity at Lowest Altitude (RALA)",
        "kind": "raw", "product": "RALA",
        "units": "dBZ", "native_units": "dBZ", "style": "reflectivity",
    },
    "REFLQC": {
        "display": "MRMS Merged Reflectivity QC Mosaic",
        "kind": "raw", "product": "REFLQC",
        "units": "dBZ", "native_units": "dBZ", "style": "reflectivity",
    },
    "REFL10C": {
        "display": "Reflectivity at -10°C",
        "kind": "raw", "product": "REFL10C",
        "units": "dBZ", "native_units": "dBZ", "style": "reflectivity",
    },
    "REFL0C": {
        "display": "Reflectivity at 0°C",
        "kind": "raw", "product": "REFL0C",
        "units": "dBZ", "native_units": "dBZ", "style": "reflectivity",
    },

    # Derived
    "COMPUTED_P": {
        "display": "Computed P",
        "kind": "computed", "product": "CREST",
        "units": "P", "native_units": "P", "style": "computed_p",
        "description": "Adjusted exponential relationship blending current CREST and its 10-minute change",
    },

    # Retained internally so old browser settings remain loadable.
    "QPE1H_DIFF_30M": {
        "display": "1hr QPE Δ 30 min (legacy)",
        "kind": "difference", "product": "QPE1H",
        "units": "in", "native_units": "mm", "style": "qpe_difference",
        "description": "Legacy rolling 1-hour QPE difference over 30 minutes",
    },
    "REFLCOMP": {
        "display": "MRMS Composite Reflectivity QC",
        "kind": "raw", "product": "REFLCOMP",
        "units": "dBZ", "native_units": "dBZ", "style": "reflectivity",
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
  <title>MRMS Unit Streamflow Viewer</title>

  <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css">
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;500;600;700;800;900&display=swap" rel="stylesheet">

  <style>
    html, body {
      height: 100%;
      width: 100%;
      margin: 0;
      padding: 0;
      background: #000;
      font-family: "Poppins", sans-serif;
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

    select.panelParam optgroup {
      background: #111820;
      color: #9fd0ff;
      font-weight: 900;
      letter-spacing: 0.15px;
    }

    select.panelParam option {
      background: #222;
      color: #fff;
      font-weight: 500;
      padding-left: 10px;
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


    /* Operational white target crosshair, matched to the training simulator. */
    .leaflet-container,
    .leaflet-container.leaflet-grab,
    .leaflet-container .leaflet-interactive,
    .leaflet-dragging .leaflet-container,
    .leaflet-dragging .leaflet-grab {
      cursor: url("data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIzMiIgaGVpZ2h0PSIzMiIgdmlld0JveD0iMCAwIDMyIDMyIj48cGF0aCBkPSJNMTYgMnYyOE0yIDE2aDI4IiBzdHJva2U9IiMwMDAiIHN0cm9rZS13aWR0aD0iNSIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIi8+PHBhdGggZD0iTTE2IDJ2MjhNMiAxNmgyOCIgc3Ryb2tlPSIjZmZmIiBzdHJva2Utd2lkdGg9IjIiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIvPjxjaXJjbGUgY3g9IjE2IiBjeT0iMTYiIHI9IjMiIGZpbGw9Im5vbmUiIHN0cm9rZT0iIzAwMCIgc3Ryb2tlLXdpZHRoPSIzIi8+PGNpcmNsZSBjeD0iMTYiIGN5PSIxNiIgcj0iMyIgZmlsbD0ibm9uZSIgc3Ryb2tlPSIjZmZmIiBzdHJva2Utd2lkdGg9IjEuMiIvPjwvc3ZnPg==") 16 16, crosshair !important;
    }

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

    .max-target-pulse-marker {
      background: transparent;
      border: none;
    }

    .max-target-pulse-ring {
      width: 30px;
      height: 30px;
      border: 3px solid #ffffff;
      border-radius: 50%;
      box-shadow: 0 0 10px rgba(255,255,255,0.95);
      animation: max-target-pulse 1.05s ease-out infinite;
    }

    @keyframes max-target-pulse {
      0% { opacity: 1.0; transform: scale(0.50); }
      65% { opacity: 0.38; transform: scale(1.05); }
      100% { opacity: 0.08; transform: scale(1.32); }
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


    .shared-readout-popup .leaflet-popup-content-wrapper {
      background: rgba(0,0,0,0.94);
      color: #ffffff;
      border: 1px solid #ffffff;
      border-radius: 4px;
      box-shadow: 0 0 8px rgba(255,255,255,0.25);
      font-size: 13px;
      font-weight: bold;
      width: 344px !important;
      min-width: 344px !important;
      max-width: 344px !important;
      box-sizing: border-box;
    }

    .shared-readout-popup .leaflet-popup-content {
      color: #ffffff;
      margin: 8px 11px;
      line-height: 1.35;
      width: 320px !important;
      min-width: 320px !important;
      max-width: 320px !important;
      box-sizing: border-box;
    }

    .shared-readout-popup .leaflet-popup-tip {
      background: rgba(0,0,0,0.94);
      border: 1px solid #ffffff;
    }

    .shared-readout-popup .leaflet-popup-close-button {
      color: #ffffff !important;
      font-weight: bold;
    }

    .readout-shell {
      display: block;
      width: 320px !important;
      min-width: 320px !important;
      max-width: 320px !important;
      box-sizing: border-box;
      overflow: visible;
    }

    .readout-trend-wrap {
      display: block;
      width: 320px !important;
      min-width: 320px !important;
      max-width: 320px !important;
      margin: 4px 0 6px 0;
      box-sizing: border-box;
    }

    .readout-trend-heading {
      font-size: 13px;
      line-height: 1.15;
      margin-bottom: 3px;
      font-weight: 900;
      white-space: nowrap;
    }

    .readout-trend-svg {
      display: block;
      width: 320px !important;
      min-width: 320px !important;
      max-width: 320px !important;
      height: 90px !important;
      box-sizing: border-box;
      border: 1px solid #777;
      background: #050505;
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

    .readout-title {
      font-size: 14px;
      font-weight: 900;
    }

    .readout-main-value {
      font-size: 18px;
      line-height: 1.12;
      font-weight: 900;
    }

    .readout-valid-time {
      font-size: 12px;
      color: #ffffff;
      font-weight: 800;
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


    .control-intro {
      margin-bottom: 10px;
      color: #d8d8d8;
      line-height: 1.35;
      padding: 10px 10px 11px 10px;
      border: 1px solid rgba(120,180,255,0.45);
      border-radius: 8px;
      background:
        radial-gradient(circle at top left, rgba(40,120,255,0.22), transparent 58%),
        linear-gradient(135deg, rgba(255,255,255,0.07), rgba(255,255,255,0.015));
      box-shadow: 0 0 12px rgba(35,120,255,0.16), inset 0 0 0 1px rgba(255,255,255,0.035);
    }

    .toolkit-title {
      margin-bottom: 5px;
      color: #ffffff;
      font-size: 15px;
      line-height: 1.12;
      font-weight: 900;
      letter-spacing: 0.25px;
      text-shadow: 0 0 8px rgba(120,190,255,0.46);
    }

    .toolkit-subtitle {
      margin-top: 4px;
      color: #dcecff;
      font-size: 11px;
      line-height: 1.3;
      font-weight: 700;
    }

    .toolkit-credit {
      margin-top: 6px;
      padding-top: 6px;
      border-top: 1px solid rgba(255,255,255,0.12);
      color: #b9d7ff;
      font-size: 10.5px;
      line-height: 1.25;
      font-weight: 700;
    }

    .toolkit-credit a {
      color: #d8ecff;
      text-decoration: none;
      font-weight: 900;
    }

    .control-section {
      margin: 0 0 10px 0;
      padding: 9px;
      border: 1px solid #3e3e3e;
      border-radius: 6px;
      background: rgba(255,255,255,0.035);
    }

    .control-section-title {
      margin: 0 0 7px 0;
      padding-bottom: 5px;
      border-bottom: 1px solid #353535;
      font-size: 13px;
      font-weight: 900;
      letter-spacing: 0.2px;
      color: #ffffff;
    }

    .control-section .panelRow:first-of-type {
      margin-top: 4px;
    }

    .control-actions {
      display: flex;
      flex-wrap: wrap;
      gap: 5px;
      margin-top: 7px;
    }

    .control-actions button {
      flex: 1 1 auto;
      margin-top: 0;
      min-width: 78px;
    }

    .force-refresh-button {
      width: 100%;
      margin: 0 0 7px 0;
      padding: 6px 8px;
      border: 1px solid #ff7777;
      background: #8b1111;
      color: #fff;
      font-weight: 900;
      letter-spacing: 0.35px;
      transition: background-color 0.2s ease, border-color 0.2s ease, opacity 0.2s ease;
    }

    .force-refresh-button:hover {
      background: #b51d1d;
      border-color: #ffaaaa;
    }

    .force-refresh-button:disabled {
      opacity: 0.65;
      cursor: wait;
    }

    .screenshot-block {
      margin-top: 9px;
      padding-top: 8px;
      border-top: 1px solid #3a3a3a;
    }

    .screenshot-title {
      margin-bottom: 5px;
      font-size: 12px;
      font-weight: 900;
      color: #fff;
    }

    #saveScreenshotBtn,
    #saveGifBtn {
      width: 100%;
      margin-top: 0;
      background: #2a2a2a;
      border-color: #777;
      font-weight: 800;
      transition: background-color 0.35s ease, border-color 0.35s ease, color 0.35s ease;
    }

    #saveScreenshotBtn:hover,
    #saveGifBtn:hover {
      background: #3a3a3a;
    }

    #saveScreenshotBtn.screenshot-saving,
    #saveGifBtn.screenshot-saving {
      background: #3b3b3b;
      border-color: #aaa;
      cursor: wait;
    }

    #saveScreenshotBtn.screenshot-success,
    #saveGifBtn.screenshot-success {
      background: #117a2f;
      border-color: #6dff94;
      color: #fff;
    }

    #saveScreenshotBtn.screenshot-error,
    #saveGifBtn.screenshot-error {
      background: #8b1111;
      border-color: #ff7777;
      color: #fff;
    }

    #saveGifBtn {
      margin-top: 6px;
    }

    .toggle-row {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 10px;
      margin: 6px 0;
      padding: 5px 0;
      border-bottom: 1px solid rgba(255,255,255,0.06);
      cursor: pointer;
    }

    .toggle-row:last-child {
      border-bottom: 0;
    }

    .toggle-copy {
      min-width: 0;
      flex: 1 1 auto;
      line-height: 1.25;
      font-weight: 700;
    }

    .toggle-copy small {
      display: block;
      margin-top: 2px;
      color: #aaa;
      font-size: 10px;
      font-weight: 400;
      line-height: 1.25;
    }

    .toggle-control {
      position: relative;
      display: inline-flex;
      align-items: center;
      gap: 5px;
      flex: 0 0 auto;
    }

    .toggle-control input {
      position: absolute;
      opacity: 0;
      width: 1px;
      height: 1px;
      pointer-events: none;
    }

    .toggle-track {
      position: relative;
      display: inline-block;
      width: 42px;
      height: 21px;
      border-radius: 999px;
      border: 1px solid #d05b5b;
      background: #8d1d1d;
      box-shadow: inset 0 0 5px rgba(0,0,0,0.45);
      transition: background 0.16s ease, border-color 0.16s ease;
    }

    .toggle-track::after {
      content: "";
      position: absolute;
      left: 2px;
      top: 2px;
      width: 15px;
      height: 15px;
      border-radius: 50%;
      background: #fff;
      box-shadow: 0 1px 4px rgba(0,0,0,0.65);
      transition: transform 0.16s ease;
    }

    .toggle-control input:checked + .toggle-track {
      background: #147b38;
      border-color: #54d97e;
    }

    .toggle-control input:checked + .toggle-track::after {
      transform: translateX(21px);
    }

    .toggle-state {
      min-width: 24px;
      font-size: 10px;
      font-weight: 900;
      color: #ff7373;
    }

    .toggle-state::after { content: "OFF"; }
    .toggle-control input:checked ~ .toggle-state { color: #5bea86; }
    .toggle-control input:checked ~ .toggle-state::after { content: "ON"; }

    .archive-date-wrap {
      margin-top: 7px;
      padding: 7px;
      border: 1px solid #333;
      border-radius: 4px;
      background: rgba(0,0,0,0.22);
      transition: opacity 0.15s ease;
    }

    .archive-date-wrap.archive-disabled {
      opacity: 0.48;
    }

    .archive-date-labels,
    .archive-date-grid {
      display: grid;
      grid-template-columns: 58px 42px 42px 42px 48px;
      gap: 4px;
      align-items: center;
    }

    .archive-date-labels {
      color: #aaa;
      font-size: 9px;
      font-weight: 800;
      text-align: center;
    }

    .archive-date-grid input,
    .archive-date-grid select {
      width: 100%;
      min-width: 0;
      margin-top: 2px;
      padding: 3px 2px;
      text-align: center;
    }

    .archive-date-grid input[type=number] {
      appearance: textfield;
      -moz-appearance: textfield;
    }

    .timeline-block {
      margin-top: 8px;
    }

    #timeOffset {
      width: 100% !important;
      margin-top: 5px;
    }

    #timeOffsetLabel {
      display: block;
      margin-top: 3px;
      font-size: 10px;
      color: #d6d6d6;
      line-height: 1.25;
    }

    .mode-banner {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 6px;
      padding: 5px 7px;
      margin-bottom: 6px;
      border: 1px solid #333;
      border-radius: 4px;
      background: rgba(0,0,0,0.28);
    }

    .mode-banner .mode-indicator {
      margin-left: 0;
    }

    .compact-select-row {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 8px;
      margin: 6px 0;
    }

    .compact-select-row label {
      margin-top: 0;
    }

    .compact-select-row select {
      width: 132px;
      margin-top: 0;
    }

    .overlay-key-collapsible {
      margin-top: 7px;
      padding-top: 6px;
      border-top: 1px solid #333;
    }

    .alarm-control-grid {
      display: grid;
      grid-template-columns: 1fr 1fr;
      gap: 6px;
      margin-top: 6px;
    }

    .alarm-control-grid label {
      margin-top: 0;
      font-size: 11px;
      color: #ddd;
    }

    .alarm-control-grid select {
      width: 100%;
    }

    .alarm-actions {
      display: grid;
      grid-template-columns: 1fr 1fr;
      gap: 5px;
      margin-top: 7px;
    }

    .alarm-actions button {
      margin-top: 0;
      min-width: 0;
    }

    #alarmStatus {
      margin-top: 6px;
      color: #cfcfcf;
      font-size: 10.5px;
      line-height: 1.3;
    }

    .alarm-draw-active {
      background: #856500 !important;
      border-color: #ffe36a !important;
      color: #fff !important;
      font-weight: 900;
    }

    .alarm-area-pulse-shape {
      stroke: #ffd200 !important;
      filter: drop-shadow(0 0 4px rgba(255,210,0,0.95));
    }

    .alarm-modal-backdrop {
      position: fixed;
      inset: 0;
      z-index: 20000;
      background: transparent;
      pointer-events: none;
    }

    .alarm-modal {
      position: fixed;
      left: 50%;
      top: 50%;
      transform: translate(-50%, -50%);
      width: min(410px, calc(100vw - 42px));
      background: rgba(0,0,0,0.96);
      color: #ffffff;
      border: 3px solid #fefe00;
      border-radius: 8px;
      box-shadow: 0 0 24px rgba(255,255,255,0.35);
      padding: 13px 15px 12px 15px;
      line-height: 1.35;
      pointer-events: auto;
      cursor: grab;
      user-select: none;
      touch-action: none;
    }

    .alarm-modal.alarm-modal-dragging {
      cursor: grabbing;
    }

    .alarm-modal-title {
      font-size: 18px;
      font-weight: 950;
      margin-bottom: 5px;
      letter-spacing: 0.2px;
    }

    .alarm-modal-value {
      font-size: 30px;
      line-height: 1.1;
      font-weight: 950;
      margin: 5px 0;
    }

    .alarm-modal-meta {
      color: #e4e4e4;
      font-size: 12px;
      margin-top: 6px;
    }

    .alarm-modal-close {
      width: 100%;
      margin-top: 11px;
      padding: 7px 8px;
      background: #222;
      border: 1px solid #aaa;
      font-weight: 900;
      cursor: pointer;
    }

    .alarm-max-pulse-marker {
      background: transparent;
      border: none;
      pointer-events: none;
    }

    .alarm-max-pulse-ring {
      width: 34px;
      height: 34px;
      border: 4px solid #ffffff;
      border-radius: 50%;
      background: rgba(0,0,0,0.10);
      animation: alarm-max-pulse 0.95s ease-out infinite;
    }

    @keyframes alarm-max-pulse {
      0% { opacity: 1.0; transform: scale(0.42); }
      55% { opacity: 0.60; transform: scale(1.08); }
      100% { opacity: 0.08; transform: scale(1.46); }
    }

    #alarmModeBell {
      position: fixed;
      top: 10px;
      right: 12px;
      z-index: 13050;
      width: 34px;
      height: 34px;
      display: none;
      align-items: center;
      justify-content: center;
      border: 1px solid #ff6b6b;
      border-radius: 50%;
      background: rgba(30,0,0,0.90);
      box-shadow: 0 0 10px rgba(255,0,0,0.72);
      pointer-events: none;
    }

    #alarmModeBell.alarm-bell-visible {
      display: flex;
      animation: alarm-bell-pulse 1.05s ease-in-out infinite;
    }

    #alarmModeBell svg {
      width: 20px;
      height: 20px;
      fill: #ff2b2b;
      filter: drop-shadow(0 0 3px rgba(255,60,60,0.95));
    }

    @keyframes alarm-bell-pulse {
      0% { opacity: 0.58; transform: scale(0.90); box-shadow: 0 0 5px rgba(255,0,0,0.45); }
      50% { opacity: 1.0; transform: scale(1.12); box-shadow: 0 0 18px rgba(255,0,0,0.95); }
      100% { opacity: 0.58; transform: scale(0.90); box-shadow: 0 0 5px rgba(255,0,0,0.45); }
    }

    @keyframes pulse-mode {
      0% { opacity: 0.30; transform: scale(0.9); }
      50% { opacity: 1.0; transform: scale(1.15); }
      100% { opacity: 0.30; transform: scale(0.9); }
    }


    html, body, button, input, select, textarea, option,
    .leaflet-container, .leaflet-control, .leaflet-popup-content,
    .leaflet-tooltip, .leaflet-marker-icon, .leaflet-marker-shadow {
      font-family: "Poppins", sans-serif !important;
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
    <div class="control-intro">
      <div class="toolkit-title">MRMS and Flash Flood Risk Assessment Toolkit</div>
      <div class="toolkit-subtitle">MRMS-derived and computed parameters for near-term prediction, analysis, proactive warning decisions, and warning-tag support.</div>
      <div class="toolkit-credit">Developed by Kevin Gilmore &bull; <a href="mailto:kevin.gilmore@noaa.gov">kevin.gilmore@noaa.gov</a></div>
    </div>

    <div class="control-section">
      <div class="control-section-title">Viewer Setup</div>
    <label class="toggle-row" for="showCwaBoundaries" style="margin-top:8px;">
      <span class="toggle-copy">NWS CWA boundaries<small>Official WFO County Warning Area outlines in yellow.</small></span>
      <span class="toggle-control"><input id="showCwaBoundaries" type="checkbox" checked onchange="toggleCwaBoundaries()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
    </label>

    <br>

    <label>Panel Elements</label><br>
    <div class="compact-select-row" style="margin-top:6px;">
      <label for="panelLayout">Panel Layout</label>
      <select id="panelLayout" onchange="layoutChanged()">
        <option value="1">1 panel</option>
        <option value="2" selected>2 panels</option>
        <option value="4">4 panels</option>
      </select>
    </div>
    <div id="panelControl-left" class="panelRow">Panel 1:
    <select id="leftParam" class="panelParam" onchange="panelParamChanged('left')">
      <optgroup label="MRMS FLASH Products:">
        <option value="CREST">CREST Max Unit Streamflow</option>
        <option value="CREST_DIFF_10M">CREST Δ 10 min</option>
        <option value="CREST_DIFF_30M">CREST Δ 30 min</option>
        <option value="SAC">SAC Max Unit Streamflow</option>
        <option value="HP">HP Max Unit Streamflow</option>
        <option value="HP_MINUS_CREST">HP - CREST Difference</option>
      </optgroup>
      <optgroup label="MRMS Instantaneous:">
        <option value="RAINRATE">Instantaneous Rain Rate</option>
        <option value="RAINRATE_DIFF_10M">Instantaneous Rain Rate Δ 10 min</option>
        <option value="RAINRATE_MAX_30M">Instantaneous 30 min Max Rain Rate</option>
      </optgroup>
      <optgroup label="MRMS Rain Totals:">
        <option value="QPE30M">30-min QPE</option>
        <option value="QPE30M_DIFF_30M">30 min QPE Δ</option>
        <option value="QPE1H">1hr QPE</option>
        <option value="QPE1H_DIFF_1H">1hr QPE Δ</option>
        <option value="QPE1H_DIFF_30M">MRMS One-Hour QPE Δ 30 min</option>
        <option value="QPE3H">3hr QPE</option>
        <option value="QPE3H_DIFF_3H">3hr QPE Δ</option>
        <option value="QPE6H">6hr QPE</option>
        <option value="QPE6H_DIFF_6H">6hr QPE Δ</option>
      </optgroup>
      <optgroup label="MRMS Radar Products:">
        <option value="RALA">Reflectivity at Lowest Altitude (RALA)</option>
        <option value="REFLQC">MRMS Merged Reflectivity QC Mosaic</option>
        <option value="REFLCOMP">MRMS Composite Reflectivity QC</option>
        <option value="REFL10C">Reflectivity at -10°C</option>
        <option value="REFL0C">Reflectivity at 0°C</option>
      </optgroup>
      <optgroup label="Derived:">
        <option value="COMPUTED_P">Computed P</option>
      </optgroup>
    </select></div>
    <div id="panelControl-right" class="panelRow">Panel 2:
    <select id="rightParam" class="panelParam" onchange="panelParamChanged('right')">
      <optgroup label="MRMS FLASH Products:">
        <option value="CREST">CREST Max Unit Streamflow</option>
        <option value="CREST_DIFF_10M">CREST Δ 10 min</option>
        <option value="CREST_DIFF_30M">CREST Δ 30 min</option>
        <option value="SAC">SAC Max Unit Streamflow</option>
        <option value="HP">HP Max Unit Streamflow</option>
        <option value="HP_MINUS_CREST">HP - CREST Difference</option>
      </optgroup>
      <optgroup label="MRMS Instantaneous:">
        <option value="RAINRATE">Instantaneous Rain Rate</option>
        <option value="RAINRATE_DIFF_10M">Instantaneous Rain Rate Δ 10 min</option>
        <option value="RAINRATE_MAX_30M">Instantaneous 30 min Max Rain Rate</option>
      </optgroup>
      <optgroup label="MRMS Rain Totals:">
        <option value="QPE30M">30-min QPE</option>
        <option value="QPE30M_DIFF_30M">30 min QPE Δ</option>
        <option value="QPE1H">1hr QPE</option>
        <option value="QPE1H_DIFF_1H">1hr QPE Δ</option>
        <option value="QPE1H_DIFF_30M">MRMS One-Hour QPE Δ 30 min</option>
        <option value="QPE3H">3hr QPE</option>
        <option value="QPE3H_DIFF_3H">3hr QPE Δ</option>
        <option value="QPE6H">6hr QPE</option>
        <option value="QPE6H_DIFF_6H">6hr QPE Δ</option>
      </optgroup>
      <optgroup label="MRMS Radar Products:">
        <option value="RALA">Reflectivity at Lowest Altitude (RALA)</option>
        <option value="REFLQC">MRMS Merged Reflectivity QC Mosaic</option>
        <option value="REFLCOMP">MRMS Composite Reflectivity QC</option>
        <option value="REFL10C">Reflectivity at -10°C</option>
        <option value="REFL0C">Reflectivity at 0°C</option>
      </optgroup>
      <optgroup label="Derived:">
        <option value="COMPUTED_P">Computed P</option>
      </optgroup>
    </select></div>
    <div id="panelControl-lowerLeft" class="panelRow">Panel 3:
    <select id="lowerLeftParam" class="panelParam" onchange="panelParamChanged('lowerLeft')">
      <optgroup label="MRMS FLASH Products:">
        <option value="CREST">CREST Max Unit Streamflow</option>
        <option value="CREST_DIFF_10M">CREST Δ 10 min</option>
        <option value="CREST_DIFF_30M">CREST Δ 30 min</option>
        <option value="SAC">SAC Max Unit Streamflow</option>
        <option value="HP">HP Max Unit Streamflow</option>
        <option value="HP_MINUS_CREST">HP - CREST Difference</option>
      </optgroup>
      <optgroup label="MRMS Instantaneous:">
        <option value="RAINRATE">Instantaneous Rain Rate</option>
        <option value="RAINRATE_DIFF_10M">Instantaneous Rain Rate Δ 10 min</option>
        <option value="RAINRATE_MAX_30M">Instantaneous 30 min Max Rain Rate</option>
      </optgroup>
      <optgroup label="MRMS Rain Totals:">
        <option value="QPE30M">30-min QPE</option>
        <option value="QPE30M_DIFF_30M">30 min QPE Δ</option>
        <option value="QPE1H">1hr QPE</option>
        <option value="QPE1H_DIFF_1H">1hr QPE Δ</option>
        <option value="QPE1H_DIFF_30M">MRMS One-Hour QPE Δ 30 min</option>
        <option value="QPE3H">3hr QPE</option>
        <option value="QPE3H_DIFF_3H">3hr QPE Δ</option>
        <option value="QPE6H">6hr QPE</option>
        <option value="QPE6H_DIFF_6H">6hr QPE Δ</option>
      </optgroup>
      <optgroup label="MRMS Radar Products:">
        <option value="RALA">Reflectivity at Lowest Altitude (RALA)</option>
        <option value="REFLQC">MRMS Merged Reflectivity QC Mosaic</option>
        <option value="REFLCOMP">MRMS Composite Reflectivity QC</option>
        <option value="REFL10C">Reflectivity at -10°C</option>
        <option value="REFL0C">Reflectivity at 0°C</option>
      </optgroup>
      <optgroup label="Derived:">
        <option value="COMPUTED_P">Computed P</option>
      </optgroup>
    </select></div>
    <div id="panelControl-lowerRight" class="panelRow">Panel 4:
    <select id="lowerRightParam" class="panelParam" onchange="panelParamChanged('lowerRight')">
      <optgroup label="MRMS FLASH Products:">
        <option value="CREST">CREST Max Unit Streamflow</option>
        <option value="CREST_DIFF_10M">CREST Δ 10 min</option>
        <option value="CREST_DIFF_30M">CREST Δ 30 min</option>
        <option value="SAC">SAC Max Unit Streamflow</option>
        <option value="HP">HP Max Unit Streamflow</option>
        <option value="HP_MINUS_CREST">HP - CREST Difference</option>
      </optgroup>
      <optgroup label="MRMS Instantaneous:">
        <option value="RAINRATE">Instantaneous Rain Rate</option>
        <option value="RAINRATE_DIFF_10M">Instantaneous Rain Rate Δ 10 min</option>
        <option value="RAINRATE_MAX_30M">Instantaneous 30 min Max Rain Rate</option>
      </optgroup>
      <optgroup label="MRMS Rain Totals:">
        <option value="QPE30M">30-min QPE</option>
        <option value="QPE30M_DIFF_30M">30 min QPE Δ</option>
        <option value="QPE1H">1hr QPE</option>
        <option value="QPE1H_DIFF_1H">1hr QPE Δ</option>
        <option value="QPE1H_DIFF_30M">MRMS One-Hour QPE Δ 30 min</option>
        <option value="QPE3H">3hr QPE</option>
        <option value="QPE3H_DIFF_3H">3hr QPE Δ</option>
        <option value="QPE6H">6hr QPE</option>
        <option value="QPE6H_DIFF_6H">6hr QPE Δ</option>
      </optgroup>
      <optgroup label="MRMS Radar Products:">
        <option value="RALA">Reflectivity at Lowest Altitude (RALA)</option>
        <option value="REFLQC">MRMS Merged Reflectivity QC Mosaic</option>
        <option value="REFLCOMP">MRMS Composite Reflectivity QC</option>
        <option value="REFL10C">Reflectivity at -10°C</option>
        <option value="REFL0C">Reflectivity at 0°C</option>
      </optgroup>
      <optgroup label="Derived:">
        <option value="COMPUTED_P">Computed P</option>
      </optgroup>
    </select></div>
    </div>

    <div class="control-section">
      <div class="control-section-title">Time &amp; Archive</div>
      <input id="timeMode" type="hidden" value="latest">

      <div class="mode-banner">
        <span id="modeIndicator" class="mode-indicator mode-live">
          <span class="mode-dot"></span><span id="modeText">LIVE</span>
        </span>
        <span id="modeTimeText" style="font-size:10px;color:#ddd;text-align:right;"></span>
      </div>

      <button id="forceRefreshBtn" class="force-refresh-button" onclick="forceRefreshLatestData()">FORCE REFRESH</button>

      <label class="toggle-row" for="archiveModeToggle">
        <span class="toggle-copy">Archive mode
          <small>OFF returns to latest live data. ON anchors the viewer to the selected UTC time.</small>
        </span>
        <span class="toggle-control">
          <input id="archiveModeToggle" type="checkbox" onchange="archiveModeToggleChanged()">
          <span class="toggle-track"></span><span class="toggle-state"></span>
        </span>
      </label>

      <div id="archiveDateWrap" class="archive-date-wrap archive-disabled">
        <div style="font-weight:800;margin-bottom:4px;">Archive anchor time (UTC/Z)</div>
        <div class="archive-date-labels"><span>YYYY</span><span>MM</span><span>DD</span><span>HH</span><span>MIN</span></div>
        <div class="archive-date-grid">
          <input id="archiveYear" type="number" min="2014" max="2100" step="1" onchange="archiveDateChanged(true)">
          <select id="archiveMonth" onchange="archiveDateChanged(true)"></select>
          <select id="archiveDay" onchange="archiveDateChanged(false)"></select>
          <select id="archiveHour" onchange="archiveDateChanged(false)"></select>
          <select id="archiveMinute" onchange="archiveDateChanged(false)"></select>
        </div>
      </div>

      <div class="timeline-block">
        <div style="font-weight:800;">Time trend slider</div>
        <input id="timeOffset" type="range" min="-10080" max="0" step="10" value="0" oninput="timelineChanged(false)">
        <span id="timeOffsetLabel">Current Z</span>
      </div>

      <div id="validTimeReadout">Valid: loading latest Z...</div>
    </div>

    <div class="control-section">
      <div class="control-section-title">Animation</div>
      <div class="loop-controls" style="margin-top:0;">
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
        </select>
        <div class="control-actions">
          <button onclick="startLoop()">Preload / Play</button>
          <button onclick="stopLoop(true)">Stop</button>
        </div>
        <div class="small-note">Frames step backward from the current live or selected archive time.</div>
      </div>

      <div class="screenshot-block">
        <div class="screenshot-title">Screenshot / Animation Export</div>
        <button id="saveScreenshotBtn" onclick="saveViewerScreenshot()">Save Screenshot</button>
        <button id="saveGifBtn" onclick="saveViewerAnimatedGif()">Save Animated GIF</button>
        <div class="small-note">PNG saves the current active 1-, 2-, or 4-panel viewer. Animated GIF uses the Frames, Skip, and Speed settings above and loops continuously.</div>
      </div>
    </div>

    <div class="control-section">
      <div class="control-section-title">Readouts &amp; Analysis</div>
      <div class="compact-select-row">
        <label for="readoutTrendLength">Trend length</label>
        <select id="readoutTrendLength" onchange="readoutTrendLengthChanged()">
          <option value="30" selected>30 minutes</option>
          <option value="60">1 hour</option>
        </select>
      </div>

      <label class="toggle-row" for="showHoverReadout">
        <span class="toggle-copy">Hover value readout<small>Shows a quick value beneath the cursor.</small></span>
        <span class="toggle-control"><input id="showHoverReadout" type="checkbox" onchange="toggleHoverReadouts()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <label class="toggle-row" for="showMaxPixel">
        <span class="toggle-copy">Max/extreme target<small>Marks the strongest value in each visible panel.</small></span>
        <span class="toggle-control"><input id="showMaxPixel" type="checkbox" onchange="refreshAllMaxMarkers()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <label class="toggle-row" for="enableAreaAvg">
        <span class="toggle-copy">Area-average free draw<small>Click vertices, then double-click or finish the area.</small></span>
        <span class="toggle-control"><input id="enableAreaAvg" type="checkbox" onchange="toggleAreaAverageTool()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <div class="control-actions">
        <button onclick="clearAllReadouts()">Clear All Readouts</button>
        <button onclick="finishAreaAveragePolygon()">Finish Area</button>
        <button onclick="clearAreaAverage()">Clear Area</button>
      </div>

      <label class="toggle-row" for="useMatchedMeanAverage" style="margin-top:8px;">
        <span class="toggle-copy">High-value weighted average<small>ON = high-value weighted average for drawn-area/alarm-area statistics. OFF = pure arithmetic average.</small></span>
        <span class="toggle-control"><input id="useMatchedMeanAverage" type="checkbox" checked onchange="averageModeChanged()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>
    </div>

    <div class="control-section">
      <div class="control-section-title">Alarm Notification</div>

      <label class="toggle-row" for="enableCrestAlarm">
        <span class="toggle-copy">CREST threshold alarm<small>Initial qualifying popup, then a new alarm only when a later LIVE scan crosses the next 100-level. Default OFF.</small></span>
        <span class="toggle-control"><input id="enableCrestAlarm" type="checkbox" onchange="toggleCrestAlarm()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <div class="alarm-control-grid">
        <div>
          <label for="alarmMinThreshold">Min alarm threshold</label>
          <select id="alarmMinThreshold" onchange="alarmSettingsChanged(true)"></select>
        </div>
        <div>
          <label for="alarmDomain">NWS WFO CWA</label>
          <select id="alarmDomain" onchange="alarmSettingsChanged(true)"></select>
        </div>
        <div>
          <label for="alarmScope">Alarm area</label>
          <select id="alarmScope" onchange="alarmSettingsChanged(true)">
            <option value="domain" selected>Official NWS WFO CWA</option>
            <option value="polygon">Drawn alarm polygon</option>
          </select>
        </div>
        <div>
          <label for="alarmStatistic">Alarm value</label>
          <select id="alarmStatistic" onchange="alarmSettingsChanged(true)">
            <option value="max" selected>Max pixel</option>
            <option value="area_average">Area average / high-value weighted average</option>
          </select>
        </div>
      </div>

      <div class="alarm-actions">
        <button id="drawAlarmAreaBtn" onclick="toggleAlarmAreaDraw()">Draw Alarm Area</button>
        <button onclick="finishAlarmAreaPolygon()">Finish Area</button>
        <button onclick="clearAlarmArea()">Clear Area</button>
        <button onclick="resetAlarmMemory()">Reset Alarm</button>
      </div>

      <div id="alarmStatus">Alarm is OFF. It will only check LIVE CREST updates when enabled.</div>
    </div>

    <div class="control-section">
      <div class="control-section-title">Warnings &amp; Overlays</div>

      <label class="toggle-row" for="showAlerts">
        <span class="toggle-copy">FFW / FFS / Flood Advisory<small>Valid-at-selected-time warning outlines.</small></span>
        <span class="toggle-control"><input id="showAlerts" type="checkbox" checked onchange="refreshAllAlerts()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <label class="toggle-row" for="showAlertLabels">
        <span class="toggle-copy">Warning labels<small>Warning number and status labels.</small></span>
        <span class="toggle-control"><input id="showAlertLabels" type="checkbox" checked onchange="refreshAllAlerts()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <label class="toggle-row" for="deepAlertText">
        <span class="toggle-copy">Deep warning text check<small>Detects considerable and emergency upgrades.</small></span>
        <span class="toggle-control"><input id="deepAlertText" type="checkbox" checked onchange="refreshAllAlerts()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <label for="opacity">Data opacity</label><br>
      <input id="opacity" type="range" min="0" max="100" value="100" oninput="setOverlayOpacity()" style="width:100%;">

      <div class="alert-key overlay-key-collapsible">
        <span class="color-chip" style="background:#00ff00"></span>FFW base<br>
        <span class="color-chip" style="background:#90ee90"></span>Flood Advisory<br>
        <span class="color-chip" style="background:#006400"></span>Considerable FFW / latest FFS<br>
        <span class="color-chip" style="background:#ff00ff"></span>Flash Flood Emergency<br>
      </div>
    </div>

    <div class="control-section">
      <div class="control-section-title">Rendering</div>

      <label class="toggle-row" for="autoRender">
        <span class="toggle-copy">Auto render after pan/zoom</span>
        <span class="toggle-control"><input id="autoRender" type="checkbox" checked><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <label class="toggle-row" for="fastRender">
        <span class="toggle-copy">Fast render mode<small>Lower display resolution; source data and readouts are unchanged.</small></span>
        <span class="toggle-control"><input id="fastRender" type="checkbox" checked onchange="fastRenderChanged()"><span class="toggle-track"></span><span class="toggle-state"></span></span>
      </label>

      <div class="control-actions">
        <button onclick="refreshAllLayers(false)">Refresh View</button>
        <button onclick="refreshAllLayers(true)">Render Current View</button>
        <button onclick="captureNow()">Capture Latest</button>
      </div>
    </div>

    <div id="status">Loading...</div>

    <div class="small-note">
      Panel choices are saved in this browser. All visible maps stay synchronized. Click any panel for matching readouts; Clear All Readouts or Esc removes every point and area result.
    </div>
    </div>
  </div>

  <div id="alarmModeBell" aria-hidden="true" title="CREST alarm mode is ON">
    <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M12 22a2.45 2.45 0 0 0 2.36-1.8H9.64A2.45 2.45 0 0 0 12 22Zm7-5.2-1.5-1.7V10a5.55 5.55 0 0 0-4.5-5.45V3.7a1 1 0 0 0-2 0v.85A5.55 5.55 0 0 0 6.5 10v5.1L5 16.8V18h14v-1.2Z"/></svg>
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
  <script src="https://cdnjs.cloudflare.com/ajax/libs/html2canvas/1.4.1/html2canvas.min.js"></script>

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

    // The archive anchor can be any UTC date available in the NOAA archive.
    // The slider always moves backward from that anchor in 10-minute steps.
    const TIME_TREND_LOOKBACK_MINUTES = 7 * 24 * 60;
    const TIME_TREND_STEP_MINUTES = 10;

    const parameterInfo = {
      CREST: { label: "CREST Max Unit Streamflow", shortLabel: "CREST", product: "CREST", units: "cfs/mi²", isDifference: false },
      CREST_DIFF_10M: { label: "CREST Δ 10 min", shortLabel: "CREST Δ10m", product: "CREST", units: "cfs/mi²", isDifference: true, isCrestRateChange: true },
      CREST_DIFF_30M: { label: "CREST Δ 30 min", shortLabel: "CREST Δ30m", product: "CREST", units: "cfs/mi²", isDifference: true, isCrestRateChange: true },
      SAC: { label: "SAC Max Unit Streamflow", shortLabel: "SAC", product: "SAC", units: "cfs/mi²", isDifference: false },
      HP: { label: "HP Max Unit Streamflow", shortLabel: "HP", product: "HP", units: "cfs/mi²", nativeUnits: "m³/s/km²", isDifference: false },
      HP_MINUS_CREST: { label: "HP - CREST Difference", shortLabel: "HP-CREST", product: "HP", units: "cfs/mi²", isDifference: true },

      RAINRATE: { label: "Instantaneous Rain Rate", shortLabel: "Rain Rate", product: "PRECIPRATE", units: "in/hr", nativeUnits: "mm/hr", isDifference: false },
      RAINRATE_DIFF_10M: { label: "Instantaneous Rain Rate Δ 10 min", shortLabel: "Rain Rate Δ10m", product: "PRECIPRATE", units: "in/hr", nativeUnits: "mm/hr", isDifference: true, isRainRateDifference: true },
      RAINRATE_MAX_30M: { label: "Instantaneous 30 min Max Rain Rate", shortLabel: "Max Rain Rate 30m", product: "PRECIPRATE", units: "in/hr", nativeUnits: "mm/hr", isDifference: false },

      QPE30M: { label: "30-min QPE", shortLabel: "QPE 30m", product: "QPE15M", units: "in", nativeUnits: "mm", isDifference: false },
      QPE30M_DIFF_30M: { label: "30 min QPE Δ", shortLabel: "QPE 30m Δ", product: "QPE15M", units: "in", nativeUnits: "mm", isDifference: true, isQpeDifference: true },
      QPE1H: { label: "1hr QPE", shortLabel: "QPE 1hr", product: "QPE1H", units: "in", nativeUnits: "mm", isDifference: false },
      QPE1H_DIFF_1H: { label: "1hr QPE Δ", shortLabel: "QPE 1hr Δ", product: "QPE1H", units: "in", nativeUnits: "mm", isDifference: true, isQpeDifference: true },
      QPE3H: { label: "3hr QPE", shortLabel: "QPE 3hr", product: "QPE3H", units: "in", nativeUnits: "mm", isDifference: false },
      QPE3H_DIFF_3H: { label: "3hr QPE Δ", shortLabel: "QPE 3hr Δ", product: "QPE3H", units: "in", nativeUnits: "mm", isDifference: true, isQpeDifference: true },
      QPE6H: { label: "6hr QPE", shortLabel: "QPE 6hr", product: "QPE6H", units: "in", nativeUnits: "mm", isDifference: false },
      QPE6H_DIFF_6H: { label: "6hr QPE Δ", shortLabel: "QPE 6hr Δ", product: "QPE6H", units: "in", nativeUnits: "mm", isDifference: true, isQpeDifference: true },

      RALA: { label: "Reflectivity at Lowest Altitude (RALA)", shortLabel: "RALA", product: "RALA", units: "dBZ", nativeUnits: "dBZ", isDifference: false },
      REFLQC: { label: "MRMS Merged Reflectivity QC Mosaic", shortLabel: "Refl QC", product: "REFLQC", units: "dBZ", nativeUnits: "dBZ", isDifference: false },
      REFL10C: { label: "Reflectivity at -10°C", shortLabel: "Refl -10°C", product: "REFL10C", units: "dBZ", nativeUnits: "dBZ", isDifference: false },
      REFL0C: { label: "Reflectivity at 0°C", shortLabel: "Refl 0°C", product: "REFL0C", units: "dBZ", nativeUnits: "dBZ", isDifference: false },
      COMPUTED_P: { label: "Computed P", shortLabel: "Computed P", product: "CREST", units: "P", isDifference: false, isComputedP: true },

      // Legacy/internal choices retained for saved browser state compatibility.
      QPE1H_DIFF_30M: { label: "1hr QPE Δ 30 min (legacy)", shortLabel: "QPE 1hr Δ30m", product: "QPE1H", units: "in", nativeUnits: "mm", isDifference: true, isQpeDifference: true },
      REFLCOMP: { label: "MRMS Composite Reflectivity QC", shortLabel: "Comp Refl", product: "REFLCOMP", units: "dBZ", nativeUnits: "dBZ", isDifference: false }
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
    let isGifExporting = false;
    let areaAvgEnabled = false;
    let areaAvgDrawing = null;
    let areaAvgVertices = [];
    let areaAvgSourcePanelKey = null;
    let areaAvgSerial = 0;
    let areaAvgPulseTimer = null;
    let areaAvgPulseStart = 0;
    let liveLatestToken = "";
    let liveLatestLabel = "";
    let liveLatestTokens = {};
    let liveLatestProbeDetails = {};
    let liveChangedProducts = [];
    let activeClickReadout = null;
    let areaAvgFinalizedVertices = [];
    let activeReadoutRefreshTimer = null;
    let readoutClearSerial = 0;
    let clickReadoutRequestKey = "";
    let clickReadoutRequestActive = false;
    let clickReadoutCompletedKey = "";
    let areaAverageRequestKey = "";
    let areaAverageRequestActive = false;
    let areaAverageCompletedKey = "";
    let crestAlarmEnabled = false;
    let crestAlarmTimer = null;
    let crestAlarmFetchSerial = 0;
    let crestAlarmLastCheckedKey = "";
    let crestAlarmLastLevel = 0;
    let crestAlarmBaselineReady = false;
    let crestAlarmInitialAlertPending = false;
    let crestAlarmLastDataToken = "";
    let crestAlarmAudioContext = null;
    let alarmAreaDrawEnabled = false;
    let alarmAreaDrawing = null;
    let alarmAreaVertices = [];
    let alarmAreaFinalizedVertices = [];
    let alarmAreaSourcePanelKey = null;
    let alarmMaxPulseSerial = 0;

    const censusBase = "https://tigerweb.geo.census.gov/arcgis/rest/services/TIGERweb/State_County/MapServer";
    const nwsCwaFeatureUrl = "https://mapservices.weather.noaa.gov/static/rest/services/nws_reference_maps/nws_reference_map/FeatureServer/1";

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

    function savedCwaBoundariesEnabled() {
      const raw = window.localStorage.getItem("mrms.viewer.showCwaBoundaries");
      return raw === null ? true : raw === "1";
    }

    function cwaBoundariesEnabled() {
      const el = document.getElementById("showCwaBoundaries");
      return !!(el && el.checked);
    }

    function toggleCwaBoundaries() {
      const enabled = cwaBoundariesEnabled();
      window.localStorage.setItem("mrms.viewer.showCwaBoundaries", enabled ? "1" : "0");
      forEachPanel(function (key, panel) {
        if (!panel || !panel.cwaLayer) return;
        try {
          if (enabled) {
            if (!panel.map.hasLayer(panel.cwaLayer)) panel.cwaLayer.addTo(panel.map);
            panel.cwaLayer.bringToFront();
          } else if (panel.map.hasLayer(panel.cwaLayer)) {
            panel.map.removeLayer(panel.cwaLayer);
          }
        } catch (e) {}
      });
      bringAllBoundariesToFront();
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

    const PRODUCT_STEP_MINUTES = {
      PRECIPRATE: 2,
      RALA: 2,
      REFLQC: 2,
      REFLCOMP: 2,
      REFL10C: 2,
      REFL0C: 2,
      CREST: 10,
      SAC: 10,
      HP: 10,
      QPE1H: 10,
      QPE15M: 15,
      QPE3H: 60,
      QPE6H: 60
    };

    function selectedArchiveProduct() {
      const keys = activePanelKeys();
      const products = keys.map(function (key) {
        try { return rawProductForParam(selectedParam(key)); } catch (e) { return null; }
      }).filter(Boolean);
      if (!products.length) return "CREST";
      products.sort(function (a, b) {
        return (PRODUCT_STEP_MINUTES[a] || 10) - (PRODUCT_STEP_MINUTES[b] || 10);
      });
      return products[0] || "CREST";
    }

    function liveSourceProductsForParam(param) {
      const p = String(param || "CREST").toUpperCase();
      if (p === "CREST_DIFF_10M" || p === "CREST_DIFF_30M") return ["CREST"];
      if (p === "RAINRATE_DIFF_10M" || p === "RAINRATE_MAX_30M") return ["PRECIPRATE"];
      if (p === "QPE30M" || p === "QPE30M_DIFF_30M") return ["QPE15M"];
      if (p === "QPE1H_DIFF_1H" || p === "QPE1H_DIFF_30M") return ["QPE1H"];
      if (p === "QPE3H_DIFF_3H") return ["QPE3H"];
      if (p === "QPE6H_DIFF_6H") return ["QPE6H"];
      if (p === "HP_MINUS_CREST") return ["HP", "CREST"];
      return [rawProductForParam(p) || "CREST"];
    }

    function selectedLiveProducts() {
      const seen = new Set();
      for (const key of activePanelKeys()) {
        for (const product of liveSourceProductsForParam(selectedParam(key))) {
          if (product) seen.add(product);
        }
      }
      // CREST must be included while its alarm is enabled even when no visible
      // panel currently displays CREST.
      if (crestAlarmEnabled) seen.add("CREST");
      return Array.from(seen);
    }

    function latestTokenAcrossProducts(tokensObj) {
      const values = Object.values(tokensObj || {}).filter(t => /^\d{8}-\d{6}$/.test(String(t || "")));
      return values.length ? values.sort().slice(-1)[0] : "";
    }

    function liveTokenForProduct(product) {
      return liveLatestTokens[String(product || "").toUpperCase()] || liveLatestToken || "";
    }

    function selectedEffectiveTokenForParam(param) {
      const mode = document.getElementById("timeMode").value;
      const offset = Number(document.getElementById("timeOffset").value);
      if (mode === "latest" && offset === 0) {
        const deps = liveSourceProductsForParam(param);
        const tokens = deps.map(liveTokenForProduct).filter(Boolean).sort();
        // For multi-source differences, anchor to the older of the latest
        // dependency tokens so both sources are available at a common time.
        return tokens.length ? tokens[0] : (liveLatestToken || "");
      }
      return selectedEffectiveToken();
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

  if (!indicator || !modeText || !timeText || !readout) return;

  const token = selectedEffectiveToken() || liveLatestToken || currentRoundedToken();
  const label = token ? tokenToIsoZ(token) : "No valid Z time selected";

  indicator.classList.remove("mode-live", "mode-archive");

  if (mode === "archive") {
    indicator.classList.add("mode-archive");
    modeText.textContent = "ARCHIVE";
    timeText.textContent = label;
    readout.innerHTML = `Archive valid: <b>${label}</b>`;
  } else {
    indicator.classList.add("mode-live");
    modeText.textContent = offset === 0 ? "LIVE" : "LIVE OFFSET";
    timeText.textContent = label;
    readout.innerHTML = offset === 0
      ? `Valid: <b>${label}</b>`
      : `Valid: <b>${label}</b> from live anchor ${tokenToIsoZ(liveLatestToken || currentRoundedToken())}`;
  }
}

    async function updateLiveLatestToken(silent=false, force=false) {
      try {
        const products = selectedLiveProducts();
        if (!products.length) products.push(selectedArchiveProduct() || "CREST");
        const forceArg = force ? "&force=1" : "";
        const resp = await fetch(
          `/api/live/latest?products=${encodeURIComponent(products.join(","))}${forceArg}&cacheBust=${Date.now()}`
        );
        const data = await resp.json();
        if (resp.ok && data.products) {
          const previous = Object.assign({}, liveLatestTokens);
          const nextTokens = Object.assign({}, liveLatestTokens);
          const details = {};

          for (const [product, detail] of Object.entries(data.products || {})) {
            details[product] = detail || {};
            if (detail && detail.token) nextTokens[product] = detail.token;
          }

          liveLatestTokens = nextTokens;
          liveLatestProbeDetails = details;
          liveChangedProducts = products.filter(product => {
            const before = previous[product] || "";
            const after = liveLatestTokens[product] || "";
            return !!after && after !== before;
          });

          liveLatestToken = latestTokenAcrossProducts(liveLatestTokens) || data.latest_token || liveLatestToken || "";
          liveLatestLabel = liveLatestToken ? tokenToIsoZ(liveLatestToken) : liveLatestLabel;
          updateTimelineLabel();
          updateLiveIndicator();
          return liveLatestToken;
        }
      } catch (err) {
        liveChangedProducts = [];
        if (!silent) {
          document.getElementById("status").innerHTML = `LIVE latest lookup failed; retaining last-known-good scan: ${err}`;
        }
      }
      updateTimelineLabel();
      updateLiveIndicator();
      return liveLatestToken;
    }


    function waitForPaint(frames=2) {
      return new Promise(function (resolve) {
        function next(remaining) {
          if (remaining <= 0) {
            resolve();
            return;
          }
          requestAnimationFrame(function () { next(remaining - 1); });
        }
        next(Math.max(1, Number(frames) || 1));
      });
    }

    function screenshotFilename() {
      const token = selectedEffectiveToken() || liveLatestToken || currentRoundedToken();
      const iso = tokenToIsoZ(token) || new Date().toISOString().replace(".000Z", "Z");
      return `${iso}.png`;
    }

    function animatedGifFilename() {
      const token = selectedEffectiveToken() || liveLatestToken || currentRoundedToken();
      const iso = tokenToIsoZ(token) || new Date().toISOString().replace(".000Z", "Z");
      return `${iso}.gif`;
    }

    function applyScreenshotCloneFixes(clonedDocument) {
      // html2canvas does not reliably reproduce CSS filter() on map panes.
      // The live viewer's Esri base is darkened with a filter, so exported
      // PNG/GIF frames otherwise fall back to Esri's original gray. In the
      // capture clone only, remove that unsupported filter and blend the base
      // tiles over true black with opacity instead. MRMS imagery, boundaries,
      // labels, warnings, legends, and readouts remain at normal brightness.
      clonedDocument.querySelectorAll('.mrms-near-black-base-pane').forEach(function (pane) {
        pane.style.filter = 'none';
        pane.style.opacity = '0.28';
        pane.style.backgroundColor = '#000000';
      });

      clonedDocument.querySelectorAll('.panelMap, .leaflet-container, .mapPane, #mapGrid').forEach(function (el) {
        el.style.backgroundColor = '#000000';
      });
    }

    async function captureViewerCanvas(scaleOverride=null) {
      const grid = document.getElementById("mapGrid");
      if (!grid) throw new Error("Viewer panel grid was not found");
      if (typeof html2canvas !== "function") {
        throw new Error("Screenshot library did not load");
      }

      invalidateAllPanelSizes();
      await waitForPaint(3);

      const captureScale = scaleOverride === null
        ? Math.min(2, Math.max(1, window.devicePixelRatio || 1))
        : Math.max(0.5, Number(scaleOverride) || 1);

      return await html2canvas(grid, {
        backgroundColor: "#000000",
        useCORS: true,
        allowTaint: false,
        logging: false,
        scale: captureScale,
        width: Math.round(grid.getBoundingClientRect().width),
        height: Math.round(grid.getBoundingClientRect().height),
        scrollX: 0,
        scrollY: 0,
        windowWidth: document.documentElement.clientWidth,
        windowHeight: document.documentElement.clientHeight,
        onclone: applyScreenshotCloneFixes
      });
    }

    async function saveViewerScreenshot() {
      const button = document.getElementById("saveScreenshotBtn");
      const gifButton = document.getElementById("saveGifBtn");
      if (!button || button.disabled || isGifExporting) return;

      button.disabled = true;
      if (gifButton) gifButton.disabled = true;
      button.classList.remove("screenshot-success", "screenshot-error");
      button.classList.add("screenshot-saving");
      button.textContent = "Saving...";

      try {
        const canvas = await captureViewerCanvas();

        const blob = await new Promise(function (resolve, reject) {
          canvas.toBlob(function (result) {
            if (result) resolve(result);
            else reject(new Error("Could not create PNG image"));
          }, "image/png");
        });

        const objectUrl = URL.createObjectURL(blob);
        const link = document.createElement("a");
        link.href = objectUrl;
        link.download = screenshotFilename();
        document.body.appendChild(link);
        link.click();
        link.remove();
        setTimeout(function () { URL.revokeObjectURL(objectUrl); }, 1500);

        button.classList.remove("screenshot-saving");
        button.classList.add("screenshot-success");
        button.textContent = "Screenshot Saved";
        setTimeout(function () {
          button.classList.remove("screenshot-success");
          button.textContent = "Save Screenshot";
          button.disabled = false;
          if (gifButton && !isGifExporting) gifButton.disabled = false;
        }, 1400);
      } catch (err) {
        console.error("Screenshot failed", err);
        button.classList.remove("screenshot-saving");
        button.classList.add("screenshot-error");
        button.textContent = "Screenshot Failed";
        document.getElementById("status").textContent = `Screenshot failed: ${err.message || err}`;
        setTimeout(function () {
          button.classList.remove("screenshot-error");
          button.textContent = "Save Screenshot";
          button.disabled = false;
          if (gifButton && !isGifExporting) gifButton.disabled = false;
        }, 1800);
      }
    }

    function waitForLoopFrameImages(timeoutMs=5000) {
      const promises = [];
      for (const key of activePanelKeys()) {
        const panel = panels[key];
        const img = panel && panel.loopOverlay ? panel.loopOverlay._image : null;
        if (!img) continue;
        if (img.complete && img.naturalWidth > 0) continue;
        promises.push(new Promise(function (resolve) {
          let done = false;
          const finish = function () {
            if (done) return;
            done = true;
            resolve();
          };
          img.addEventListener('load', finish, { once: true });
          img.addEventListener('error', finish, { once: true });
          setTimeout(finish, timeoutMs);
        }));
      }
      return Promise.all(promises);
    }

    async function buildGifLoopFrames(frameCount, skip, status) {
      const keys = activePanelKeys();
      const product = selectedArchiveProduct();
      const bounds = loopBoundsFromPrimaryMap();
      const cacheKey = `gif-${Date.now()}`;

      loopBaseBounds = bounds;
      suppressAutoRenderUntil = Date.now() + 999999;
      status.innerHTML = `Preparing ${frameCount}-frame GIF from ${product}. Preloading MRMS images...`;

      const tokens = await selectLoopTokens(product, frameCount, skip);
      if (!tokens.length) throw new Error("No valid GIF frame times were found.");

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
        throw new Error("All GIF frame image loads failed. Check terminal/server output.");
      }
      return { keys: keys, product: product, failed: failed };
    }

    async function saveViewerAnimatedGif() {
      const button = document.getElementById("saveGifBtn");
      const screenshotButton = document.getElementById("saveScreenshotBtn");
      const status = document.getElementById("status");
      if (!button || button.disabled || isGifExporting) return;

      const frameCount = Math.max(1, Number(document.getElementById("loopFrames").value || 12));
      const skip = Math.max(1, Number(document.getElementById("loopSkip").value || 1));
      const delay = Math.max(20, Number(document.getElementById("loopDelay").value || 220));
      const controlsToFreeze = ["loopFrames", "loopSkip", "loopDelay", "panelLayout"]
        .map(function (id) { return document.getElementById(id); })
        .filter(Boolean);

      isGifExporting = true;
      stopLoop(false);
      button.disabled = true;
      if (screenshotButton) screenshotButton.disabled = true;
      controlsToFreeze.forEach(function (el) { el.disabled = true; });
      button.classList.remove("screenshot-success", "screenshot-error");
      button.classList.add("screenshot-saving");
      button.textContent = "Preparing GIF...";

      try {
        const gifModule = await import("https://cdn.jsdelivr.net/npm/gifenc@1.0.3/+esm");
        const GIFEncoder = gifModule.GIFEncoder;
        const quantize = gifModule.quantize;
        const applyPalette = gifModule.applyPalette;
        if (!GIFEncoder || !quantize || !applyPalette) {
          throw new Error("GIF encoder library did not load correctly");
        }

        const prep = await buildGifLoopFrames(frameCount, skip, status);
        const gif = GIFEncoder();
        let outputWidth = 0;
        let outputHeight = 0;

        for (let i = 0; i < loopFrames.length; i++) {
          showLoopFrame(i);
          await waitForLoopFrameImages();
          await waitForPaint(3);

          button.textContent = `GIF ${i + 1}/${loopFrames.length}`;
          status.innerHTML = `Capturing GIF frame <b>${i + 1} of ${loopFrames.length}</b> — ${tokenToIsoZ(loopFrames[i].token)}.`;

          // GIFs are captured at 1 CSS pixel per output pixel. This preserves
          // the viewer's layout while keeping 18/24-frame exports practical in
          // browser memory and file size.
          const canvas = await captureViewerCanvas(1);
          outputWidth = canvas.width;
          outputHeight = canvas.height;
          const ctx = canvas.getContext("2d", { willReadFrequently: true });
          if (!ctx) throw new Error("Could not read GIF frame canvas");
          const rgba = ctx.getImageData(0, 0, outputWidth, outputHeight).data;
          const palette = quantize(rgba, 256);
          const indexed = applyPalette(rgba, palette);
          const frameOptions = { palette: palette, delay: delay };
          if (i === 0) frameOptions.repeat = 0;
          gif.writeFrame(indexed, outputWidth, outputHeight, frameOptions);

          // Let the UI repaint between expensive quantization passes.
          await new Promise(function (resolve) { setTimeout(resolve, 0); });
        }

        gif.finish();
        const bytes = gif.bytes();
        const blob = new Blob([bytes], { type: "image/gif" });
        const objectUrl = URL.createObjectURL(blob);
        const link = document.createElement("a");
        link.href = objectUrl;
        link.download = animatedGifFilename();
        document.body.appendChild(link);
        link.click();
        link.remove();
        setTimeout(function () { URL.revokeObjectURL(objectUrl); }, 3000);

        button.classList.remove("screenshot-saving");
        button.classList.add("screenshot-success");
        button.textContent = "GIF Saved";
        status.innerHTML = `Animated GIF saved: <b>${loopFrames.length} frames</b>, ${delay} ms/frame, ${prep.keys.length} panel(s), ${outputWidth}×${outputHeight}px.${prep.failed ? ` ${prep.failed} preloaded image(s) reported an error.` : ""}`;
      } catch (err) {
        console.error("Animated GIF export failed", err);
        button.classList.remove("screenshot-saving");
        button.classList.add("screenshot-error");
        button.textContent = "GIF Failed";
        status.textContent = `Animated GIF failed: ${err.message || err}`;
      } finally {
        stopLoop(false);
        refreshAllLayers(true);
        controlsToFreeze.forEach(function (el) { el.disabled = false; });
        isGifExporting = false;
        if (screenshotButton) screenshotButton.disabled = false;
        setTimeout(function () {
          button.classList.remove("screenshot-success", "screenshot-error", "screenshot-saving");
          button.textContent = "Save Animated GIF";
          button.disabled = false;
        }, 1600);
      }
    }

    async function forceRefreshLatestData() {
      const button = document.getElementById("forceRefreshBtn");
      if (!button || button.disabled) return;

      button.disabled = true;
      button.textContent = "REFRESHING...";
      try {
        if (isLooping) stopLoop(false);

        const archiveToggle = document.getElementById("archiveModeToggle");
        if (archiveToggle) archiveToggle.checked = false;
        document.getElementById("timeMode").value = "latest";
        document.getElementById("timeOffset").value = 0;

        clearAllReadouts();
        liveLatestToken = "";
        liveLatestLabel = "";
        liveLatestTokens = {};
        liveLatestProbeDetails = {};
        liveChangedProducts = [];
        alertCacheKey = "";
        alertCacheData = null;
        alertFetchSerial += 1;
        forEachPanel(function (key, panel) { panel.lastRenderKey = ""; });

        await updateLiveLatestToken(false, true);
        updateTimelineControls();
        updateLiveIndicator();
        refreshAllLayers(true);
        document.getElementById("status").innerHTML = `Force refreshed latest data at <b>${tokenToIsoZ(liveLatestToken || currentRoundedToken())}</b>.`;
      } catch (err) {
        document.getElementById("status").textContent = `Force refresh failed: ${err.message || err}`;
      } finally {
        setTimeout(function () {
          button.disabled = false;
          button.textContent = "FORCE REFRESH";
        }, 650);
      }
    }


async function goLive() {
  const archiveToggle = document.getElementById("archiveModeToggle");
  if (archiveToggle) archiveToggle.checked = false;
  document.getElementById("timeMode").value = "latest";
  document.getElementById("timeOffset").value = 0;
  clearAllReadouts();
  await updateLiveLatestToken(false);
  updateTimelineControls();
  refreshAllLayers(true);
}


function goArchiveMode() {
  const archiveToggle = document.getElementById("archiveModeToggle");
  if (archiveToggle) archiveToggle.checked = true;
  document.getElementById("timeMode").value = "archive";
  document.getElementById("timeOffset").value = 0;
  clearAllReadouts();
  updateTimelineControls();
  refreshAllLayers(true);
}

    function makeMap(divId) {
      const m = L.map(divId, {
        preferCanvas: true,
        zoomControl: true
      }).setView(domains[DEFAULT_VIEW_DOMAIN].center, domains[DEFAULT_VIEW_DOMAIN].zoom);

      const esriDarkBase = "https://server.arcgisonline.com/ArcGIS/rest/services/Canvas/World_Dark_Gray_Base/MapServer/tile/{z}/{y}/{x}";
      const esriDarkReference = "https://server.arcgisonline.com/ArcGIS/rest/services/Canvas/World_Dark_Gray_Reference/MapServer/tile/{z}/{y}/{x}";

      // Keep the API-free Esri Dark Gray basemap, but render its base canvas
      // much closer to black. This recreates the old CARTO-dark appearance
      // without depending on another third-party API key. The reference/label
      // layer remains brighter so roads, cities, and labels stay readable.
      if (!m.getPane("nearBlackBasePane")) {
        m.createPane("nearBlackBasePane");
      }
      if (!m.getPane("nearBlackReferencePane")) {
        m.createPane("nearBlackReferencePane");
      }
      const nearBlackBasePane = m.getPane("nearBlackBasePane");
      const nearBlackReferencePane = m.getPane("nearBlackReferencePane");
      // Stable class hooks let the screenshot clone darken only the basemap
      // tiles without touching MRMS raster overlays or operational graphics.
      nearBlackBasePane.classList.add("mrms-near-black-base-pane");
      nearBlackReferencePane.classList.add("mrms-near-black-reference-pane");
      nearBlackBasePane.style.zIndex = 200;
      nearBlackBasePane.style.backgroundColor = "#000000";
      nearBlackBasePane.style.filter = "brightness(0.38) contrast(1.55) saturate(0.50)";
      nearBlackReferencePane.style.zIndex = 250;
      nearBlackReferencePane.style.pointerEvents = "none";
      nearBlackReferencePane.style.filter = "brightness(1.08) contrast(1.12)";

      L.tileLayer(esriDarkBase, {
        pane: "nearBlackBasePane",
        maxZoom: 16,
        crossOrigin: true,
        attribution: "Tiles &copy; Esri"
      }).addTo(m);

      L.tileLayer(esriDarkReference, {
        pane: "nearBlackReferencePane",
        maxZoom: 16,
        crossOrigin: true,
        attribution: "Reference &copy; Esri"
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

      panel.cwaLayer = L.esri.featureLayer({
        url: nwsCwaFeatureUrl,
        simplifyFactor: 0.35,
        precision: 5,
        style: function () {
          return {
            color: "#ffff00",
            weight: 2.1,
            opacity: 0.95,
            fillOpacity: 0
          };
        }
      });
      if (cwaBoundariesEnabled()) panel.cwaLayer.addTo(panel.map);

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
        alarmAreaGroup: L.layerGroup(),
        areaAvgPopup: null,
        clickReadoutGroup: L.layerGroup(),
        clickReadoutPopup: null,
        clickReadoutSerial: 0,
        clickReadoutAbortController: null,
        areaAvgAbortController: null,
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
        handleAlarmAreaDoubleClick(key, e);
        handleAreaAverageDoubleClick(key, e);
      });

      panel.map.on("mousemove", function (e) {
        handleAlarmAreaMouseMove(key, e);
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

    async function panelParamChanged(panelKey) {
      const param = selectedParam(panelKey);
      window.localStorage.setItem(`mrms.viewer.${panelKey}Param`, param);
      updatePanelTitles();
      if (isLooping) {
        stopLoop(false);
      }
      if (activePanelKeys().includes(panelKey)) {
        await updateLiveLatestToken(true);
        refreshPanelLayer(panelKey, true);
        scheduleActiveReadoutRefresh();
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
        if (alarmAreaFinalizedVertices.length >= 3) {
          drawAlarmAreaShape(alarmAreaFinalizedVertices, true);
        }
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
      if (p.isComputedP) {
        return {
          background: "linear-gradient(to right, #000000 0%, #00ff00 20%, #ffff00 40%, #ffa500 60%, #ff0000 80%, #ff00ff 100%)",
          ticks: [
            {left:"0%", text:"0"},
            {left:"20%", text:"1000"},
            {left:"40%", text:"2000"},
            {left:"60%", text:"3000"},
            {left:"80%", text:"4000"},
            {left:"100%", text:"5000"}
          ]
        };
      }
      if (p.isCrestRateChange) {
        return {
          background: "linear-gradient(to right, #ffffff 0%, #800080 16.667%, #00ffff 33.333%, #0096ff 42.667%, #0033ff 48%, #000000 50%, #ff0000 52%, #ff4bff 57.333%, #ff00ff 66.667%, #ffa500 83.333%, #ffffff 100%)",
          ticks: [
            {left:"0%", text:"−300"},
            {left:"16.667%", text:"−200"},
            {left:"33.333%", text:"−100"},
            {left:"50%", text:"0"},
            {left:"66.667%", text:"+100"},
            {left:"83.333%", text:"+200"},
            {left:"100%", text:"+300"}
          ]
        };
      }
      if (p.isRainRateDifference) {
        return {
          background: "linear-gradient(to right, #ffffff 0%, #800080 16.667%, #00ffff 33.333%, #0096ff 42.667%, #0033ff 48%, #000000 50%, #ff0000 52%, #ff4bff 57.333%, #ff00ff 66.667%, #ffa500 83.333%, #ffffff 100%)",
          ticks: [
            {left:"0%", text:"−10"},
            {left:"16.667%", text:"−6.7"},
            {left:"33.333%", text:"−3.3"},
            {left:"50%", text:"0"},
            {left:"66.667%", text:"+3.3"},
            {left:"83.333%", text:"+6.7"},
            {left:"100%", text:"+10"}
          ]
        };
      }
      if (p.isQpeDifference) {
        return {
          background: "linear-gradient(to right, #ffffff 0%, #800080 16.667%, #00ffff 33.333%, #0096ff 42.667%, #0033ff 48%, #000000 50%, #ff0000 52%, #ff4bff 57.333%, #ff00ff 66.667%, #ffa500 83.333%, #ffffff 100%)",
          ticks: [
            {left:"0%", text:"−10"},
            {left:"16.667%", text:"−6.7"},
            {left:"33.333%", text:"−3.3"},
            {left:"50%", text:"0"},
            {left:"66.667%", text:"+3.3"},
            {left:"83.333%", text:"+6.7"},
            {left:"100%", text:"+10"}
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
      try { if (cwaBoundariesEnabled() && panel.cwaLayer) panel.cwaLayer.bringToFront(); } catch (e) {}
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
  return archivePickerToken();
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
  return TIME_TREND_STEP_MINUTES;
}

    function readoutTrendMinutes() {
      const el = document.getElementById("readoutTrendLength");
      const minutes = Number(el && el.value ? el.value : 30);
      return minutes === 60 ? 60 : 30;
    }

    function readoutTrendSamples() {
      return readoutTrendMinutes() === 60 ? 7 : 4;
    }

    function readoutTrendLengthChanged() {
      // Never overwrite an existing readout with a different trend window.
      // Abort all pending calculations and remove every point/area readout.
      clearAllReadouts();
    }

    function selectedAverageMode() {
      const el = document.getElementById("useMatchedMeanAverage");
      return !el || el.checked ? "matched" : "pure";
    }

    function selectedAverageLabel() {
      return selectedAverageMode() === "matched" ? "High-Value Weighted Avg" : "Pure Average";
    }

    function averageModeChanged() {
      const matched = selectedAverageMode() === "matched";
      window.localStorage.setItem("mrms.viewer.useMatchedMeanAverage", matched ? "1" : "0");
      areaAverageRequestKey = "";
      areaAverageCompletedKey = "";
      crestAlarmLastCheckedKey = "";
      crestAlarmLastLevel = 0;
      crestAlarmBaselineReady = false;
      crestAlarmLastDataToken = "";
      if (areaAvgFinalizedVertices && areaAvgFinalizedVertices.length >= 3) {
        finalizeAreaAveragePolygon(areaAvgFinalizedVertices.slice(), true);
      }
      alarmSettingsChanged(true);
    }


function updateTimelineControls() {
  const mode = document.getElementById("timeMode").value;
  const slider = document.getElementById("timeOffset");
  const archiveWrap = document.getElementById("archiveDateWrap");
  const archiveToggle = document.getElementById("archiveModeToggle");

  slider.step = TIME_TREND_STEP_MINUTES;
  slider.min = -TIME_TREND_LOOKBACK_MINUTES;
  slider.max = 0;
  if (Number(slider.value) > 0 || Number(slider.value) < -TIME_TREND_LOOKBACK_MINUTES) {
    slider.value = 0;
  }

  if (archiveToggle) archiveToggle.checked = mode === "archive";
  if (archiveWrap) archiveWrap.classList.toggle("archive-disabled", mode !== "archive");

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


function fillSelectOptions(selectId, values) {
  const el = document.getElementById(selectId);
  if (!el) return;
  el.innerHTML = "";
  for (const value of values) {
    const opt = document.createElement("option");
    opt.value = String(value).padStart(2, "0");
    opt.textContent = String(value).padStart(2, "0");
    el.appendChild(opt);
  }
}

function updateArchiveDayOptions(keepValue=true) {
  const yearEl = document.getElementById("archiveYear");
  const monthEl = document.getElementById("archiveMonth");
  const dayEl = document.getElementById("archiveDay");
  if (!yearEl || !monthEl || !dayEl) return;

  const oldDay = keepValue ? Number(dayEl.value || 1) : 1;
  const year = Math.max(2014, Number(yearEl.value || new Date().getUTCFullYear()));
  const month = Math.max(1, Math.min(12, Number(monthEl.value || 1)));
  const daysInMonth = new Date(Date.UTC(year, month, 0)).getUTCDate();
  fillSelectOptions("archiveDay", Array.from({length: daysInMonth}, (_, i) => i + 1));
  dayEl.value = String(Math.min(oldDay, daysInMonth)).padStart(2, "0");
}

function setArchivePickerFromToken(token) {
  const d = tokenToDate(token) || new Date();
  document.getElementById("archiveYear").value = d.getUTCFullYear();
  document.getElementById("archiveMonth").value = String(d.getUTCMonth() + 1).padStart(2, "0");
  updateArchiveDayOptions(false);
  document.getElementById("archiveDay").value = String(d.getUTCDate()).padStart(2, "0");
  document.getElementById("archiveHour").value = String(d.getUTCHours()).padStart(2, "0");
  const roundedMinute = Math.floor(d.getUTCMinutes() / 10) * 10;
  document.getElementById("archiveMinute").value = String(roundedMinute).padStart(2, "0");
}

function initializeArchivePicker() {
  fillSelectOptions("archiveMonth", Array.from({length: 12}, (_, i) => i + 1));
  fillSelectOptions("archiveHour", Array.from({length: 24}, (_, i) => i));
  fillSelectOptions("archiveMinute", [0, 10, 20, 30, 40, 50]);

  const saved = window.localStorage.getItem("mrms.viewer.archiveAnchor") || currentRoundedToken();
  setArchivePickerFromToken(saved);
}

function archivePickerToken() {
  const year = Number(document.getElementById("archiveYear").value);
  const month = Number(document.getElementById("archiveMonth").value);
  const day = Number(document.getElementById("archiveDay").value);
  const hour = Number(document.getElementById("archiveHour").value);
  const minute = Number(document.getElementById("archiveMinute").value);
  const d = new Date(Date.UTC(year, month - 1, day, hour, minute, 0));

  if (
    !Number.isFinite(year) || year < 2014 ||
    d.getUTCFullYear() !== year || d.getUTCMonth() !== month - 1 ||
    d.getUTCDate() !== day || d.getUTCHours() !== hour ||
    d.getUTCMinutes() !== minute
  ) {
    return "";
  }
  return dateToToken(d);
}

function archiveDateChanged(monthOrYearChanged=false) {
  if (monthOrYearChanged) updateArchiveDayOptions(true);
  const token = archivePickerToken();
  if (!token) {
    document.getElementById("status").innerHTML = "Choose a valid UTC archive date and time.";
    return;
  }

  window.localStorage.setItem("mrms.viewer.archiveAnchor", token);
  document.getElementById("timeOffset").value = 0;
  updateTimelineLabel();
  updateLiveIndicator();

  const archiveToggle = document.getElementById("archiveModeToggle");
  if (archiveToggle && archiveToggle.checked) {
    document.getElementById("timeMode").value = "archive";
    clearAllReadouts();
    clearTimeout(timelineTimer);
    timelineTimer = setTimeout(function () { refreshAllLayers(true); }, 180);
  }
}

function archiveModeToggleChanged() {
  const enabled = !!document.getElementById("archiveModeToggle").checked;
  if (enabled) {
    const token = archivePickerToken();
    if (!token) {
      document.getElementById("archiveModeToggle").checked = false;
      document.getElementById("status").innerHTML = "Choose a valid UTC archive date and time before enabling archive mode.";
      return;
    }
    window.localStorage.setItem("mrms.viewer.archiveAnchor", token);
    document.getElementById("timeMode").value = "archive";
    document.getElementById("timeOffset").value = 0;
    clearAllReadouts();
    updateTimelineControls();
    refreshAllLayers(true);
  } else {
    goLive();
  }
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

    function initializeAlarmControls() {
      const thresholdSelect = document.getElementById("alarmMinThreshold");
      if (thresholdSelect) {
        thresholdSelect.innerHTML = "";
        for (let v = 100; v <= 2000; v += 100) {
          const opt = document.createElement("option");
          opt.value = String(v);
          opt.textContent = `${v}+ cfs/mi²`;
          thresholdSelect.appendChild(opt);
        }
        thresholdSelect.value = window.localStorage.getItem("mrms.viewer.crestAlarmMinThreshold") || "200";
      }

      const domainEl = document.getElementById("alarmDomain");
      if (domainEl) {
        domainEl.innerHTML = '<option value="LIX">LIX — loading official NWS CWA list...</option>';
        domainEl.value = "LIX";
        loadAlarmCwaOptions();
      }

      const scopeEl = document.getElementById("alarmScope");
      if (scopeEl) {
        const savedScope = window.localStorage.getItem("mrms.viewer.crestAlarmScope") || "domain";
        scopeEl.value = savedScope === "polygon" ? "polygon" : "domain";
      }

      const statEl = document.getElementById("alarmStatistic");
      if (statEl) {
        const savedStat = window.localStorage.getItem("mrms.viewer.crestAlarmStatistic") || "max";
        statEl.value = savedStat === "area_average" ? "area_average" : "max";
      }

      const enableEl = document.getElementById("enableCrestAlarm");
      if (enableEl) enableEl.checked = false; // safety default: always OFF on reload
      crestAlarmEnabled = false;
      updateAlarmModeBell();
      updateAlarmStatus("Alarm is OFF. It will only check LIVE CREST updates when enabled.");
    }

    async function loadAlarmCwaOptions() {
      const domainEl = document.getElementById("alarmDomain");
      if (!domainEl) return;
      const savedDomain = String(window.localStorage.getItem("mrms.viewer.crestAlarmDomain") || "LIX").toUpperCase();

      try {
        const resp = await fetch(`/api/cwa/list?cacheBust=${Date.now()}`);
        const data = await resp.json();
        if (!resp.ok || !Array.isArray(data.items) || !data.items.length) {
          throw new Error(data.error || "No CWA list returned");
        }

        domainEl.innerHTML = "";
        for (const item of data.items) {
          const wfo = String(item.wfo || item.cwa || "").toUpperCase();
          if (!wfo) continue;
          const place = String(item.citystate || item.city || "").trim();
          const opt = document.createElement("option");
          opt.value = wfo;
          opt.textContent = place ? `${wfo} — ${place}` : wfo;
          domainEl.appendChild(opt);
        }

        const hasSaved = Array.from(domainEl.options).some(opt => opt.value === savedDomain);
        const hasLix = Array.from(domainEl.options).some(opt => opt.value === "LIX");
        domainEl.value = hasSaved ? savedDomain : (hasLix ? "LIX" : domainEl.options[0].value);
        window.localStorage.setItem("mrms.viewer.crestAlarmDomain", domainEl.value);
        prefetchAlarmCwaGeometry(domainEl.value);
      } catch (err) {
        console.warn("Official CWA list load failed", err);
        domainEl.innerHTML = "";
        Object.keys(domains).forEach(function (name) {
          const opt = document.createElement("option");
          opt.value = name;
          opt.textContent = `${name} — fallback local domain`;
          domainEl.appendChild(opt);
        });
        domainEl.value = domains[savedDomain] ? savedDomain : DEFAULT_VIEW_DOMAIN;
      }
    }

    function prefetchAlarmCwaGeometry(wfo) {
      const cwa = String(wfo || "").trim().toUpperCase();
      if (!/^[A-Z0-9]{3}$/.test(cwa)) return;
      fetch(`/api/cwa/prefetch?wfo=${encodeURIComponent(cwa)}&cacheBust=${Date.now()}`)
        .catch(function () {});
    }

    function alarmMinThreshold() {
      const el = document.getElementById("alarmMinThreshold");
      const value = Number(el && el.value ? el.value : 200);
      return Math.max(100, Math.min(2000, Math.round(value / 100) * 100));
    }

    function alarmScope() {
      const el = document.getElementById("alarmScope");
      return el && el.value === "polygon" ? "polygon" : "domain";
    }

    function alarmDomainName() {
      const el = document.getElementById("alarmDomain");
      const value = String((el && el.value) || "LIX").trim().toUpperCase();
      return value || "LIX";
    }

    function alarmDomainDisplayName() {
      const el = document.getElementById("alarmDomain");
      if (el && el.selectedIndex >= 0) {
        return String(el.options[el.selectedIndex].textContent || el.value || "LIX");
      }
      return alarmDomainName();
    }

    function alarmStatistic() {
      const el = document.getElementById("alarmStatistic");
      return el && el.value === "area_average" ? "area_average" : "max";
    }

    function alarmStatisticLabel() {
      if (alarmStatistic() === "area_average") return `${selectedAverageLabel()} area value`;
      return "Max pixel";
    }

    function updateAlarmStatus(html) {
      const el = document.getElementById("alarmStatus");
      if (el) el.innerHTML = html;
    }

    function alarmAreaPlainVertices() {
      return alarmAreaFinalizedVertices.map(v => ({ lat: Number(v.lat), lon: Number(v.lng) }));
    }

    function resetAlarmMemory() {
      crestAlarmLastLevel = 0;
      crestAlarmLastCheckedKey = "";
      crestAlarmBaselineReady = false;
      crestAlarmInitialAlertPending = !!crestAlarmEnabled;
      crestAlarmLastDataToken = "";
      clearAlarmMaxPulse();
      updateAlarmStatus(crestAlarmEnabled
        ? `Alarm memory reset. Checking the current LIVE scan now; an initial notification will fire if ${alarmStatisticLabel()} is at or above CREST ${alarmMinThreshold()}+. Future notifications require a genuinely new scan to cross the next 100-level.`
        : "Alarm memory reset. Alarm is OFF.");
      scheduleCrestAlarmCheck(300, true);
    }

    function alarmSettingsChanged(resetMemory=false) {
      const threshold = alarmMinThreshold();
      window.localStorage.setItem("mrms.viewer.crestAlarmMinThreshold", String(threshold));
      window.localStorage.setItem("mrms.viewer.crestAlarmScope", alarmScope());
      window.localStorage.setItem("mrms.viewer.crestAlarmDomain", alarmDomainName());
      window.localStorage.setItem("mrms.viewer.crestAlarmStatistic", alarmStatistic());
      if (alarmScope() === "domain") prefetchAlarmCwaGeometry(alarmDomainName());
      if (resetMemory) {
        crestAlarmLastLevel = 0;
        crestAlarmLastCheckedKey = "";
        crestAlarmBaselineReady = false;
        crestAlarmInitialAlertPending = !!crestAlarmEnabled;
        crestAlarmLastDataToken = "";
        clearAlarmMaxPulse();
      }
      updateAlarmStatus(crestAlarmEnabled
        ? `Alarm ON. Monitoring CREST ${threshold}+ by 100-levels using ${alarmScope() === "polygon" ? "drawn polygon" : alarmDomainDisplayName()} | ${alarmStatisticLabel()}.`
        : "Alarm is OFF. It will only check LIVE CREST updates when enabled.");
      scheduleCrestAlarmCheck(500, true);
    }

    function initAlarmAudio() {
      try {
        const AudioCtx = window.AudioContext || window.webkitAudioContext;
        if (!AudioCtx) return null;
        if (!crestAlarmAudioContext) crestAlarmAudioContext = new AudioCtx();
        if (crestAlarmAudioContext.state === "suspended") crestAlarmAudioContext.resume().catch(() => {});
        return crestAlarmAudioContext;
      } catch (e) {
        return null;
      }
    }

    function playSoftAlarmDings() {
      const ctx = initAlarmAudio();
      if (!ctx) return;
      try {
        const start = ctx.currentTime + 0.04;
        [0.0, 0.28, 0.56].forEach(function (offset, i) {
          const osc = ctx.createOscillator();
          const gain = ctx.createGain();
          osc.type = "sine";
          osc.frequency.setValueAtTime(i === 1 ? 880 : 740, start + offset);
          gain.gain.setValueAtTime(0.0001, start + offset);
          gain.gain.exponentialRampToValueAtTime(0.11, start + offset + 0.018);
          gain.gain.exponentialRampToValueAtTime(0.0001, start + offset + 0.18);
          osc.connect(gain);
          gain.connect(ctx.destination);
          osc.start(start + offset);
          osc.stop(start + offset + 0.20);
        });
      } catch (e) {}
    }

    function hexToRgb(hex) {
      const s = String(hex || "").replace("#", "");
      if (s.length !== 6) return {r: 255, g: 255, b: 255};
      return {
        r: parseInt(s.slice(0, 2), 16),
        g: parseInt(s.slice(2, 4), 16),
        b: parseInt(s.slice(4, 6), 16)
      };
    }

    function rgbToHex(rgb) {
      const h = n => Math.max(0, Math.min(255, Math.round(n))).toString(16).padStart(2, "0");
      return `#${h(rgb.r)}${h(rgb.g)}${h(rgb.b)}`;
    }

    function crestAlarmColorForValue(value) {
      const stops = [
        {v:0.0, c:"#000000"},
        {v:100.0, c:"#fefefe"},
        {v:100.01, c:"#fefe00"},
        {v:200.0, c:"#999900"},
        {v:200.01, c:"#ff6346"},
        {v:400.0, c:"#ffa500"},
        {v:400.01, c:"#f08080"},
        {v:600.0, c:"#800000"},
        {v:600.01, c:"#800080"},
        {v:1000.0, c:"#fe00fe"},
        {v:1000.01, c:"#0000ff"},
        {v:2000.0, c:"#000080"}
      ];
      const v = Math.max(0, Math.min(2000, Number(value) || 0));
      for (let i = 0; i < stops.length - 1; i++) {
        const a = stops[i];
        const b = stops[i + 1];
        if (v >= a.v && v <= b.v) {
          const denom = Math.max(1e-9, b.v - a.v);
          const t = Math.max(0, Math.min(1, (v - a.v) / denom));
          const ca = hexToRgb(a.c);
          const cb = hexToRgb(b.c);
          return rgbToHex({
            r: ca.r + (cb.r - ca.r) * t,
            g: ca.g + (cb.g - ca.g) * t,
            b: ca.b + (cb.b - ca.b) * t
          });
        }
      }
      return stops[stops.length - 1].c;
    }

    function formatAlarmDiffHtml(payload) {
      const rawDiff = payload ? payload.diff_10m : null;
      const diff = rawDiff === null || rawDiff === undefined ? NaN : Number(rawDiff);
      const label = escapeHtml((payload && payload.diff_10m_label) || "10-min difference");
      const units = (payload && payload.diff_10m_units) || "cfs/mi²";
      if (payload && payload.diff_pending) {
        return `<div id="crestAlarmDiffLine" class="alarm-modal-meta"><b>${label}:</b> calculating...</div>`;
      }
      if (!Number.isFinite(diff)) {
        return `<div id="crestAlarmDiffLine" class="alarm-modal-meta"><b>${label}:</b> unavailable</div>`;
      }
      const sign = diff > 0 ? "+" : "";
      const text = `${sign}${Math.round(diff).toLocaleString()} ${units}`;
      if (diff > 0.5) {
        return `<div id="crestAlarmDiffLine" class="alarm-modal-meta"><b>${label}:</b> <span style="color:#ff4b4b;font-weight:950;">${text} — THREAT INCREASING</span></div>`;
      }
      if (diff < -0.5) {
        return `<div id="crestAlarmDiffLine" class="alarm-modal-meta"><b>${label}:</b> <span style="color:#4bb3ff;font-weight:950;">${text} — THREAT DECREASING</span></div>`;
      }
      return `<div id="crestAlarmDiffLine" class="alarm-modal-meta"><b>${label}:</b> <span style="color:#dddddd;font-weight:900;">${text} — NEAR STEADY</span></div>`;
    }

    function updateOpenCrestAlarmDiff(payload) {
      const line = document.getElementById("crestAlarmDiffLine");
      if (!line) return;
      const holder = document.createElement("div");
      holder.innerHTML = formatAlarmDiffHtml(payload);
      const replacement = holder.firstElementChild;
      if (replacement) line.replaceWith(replacement);
    }

    async function fetchCrestAlarmDiffDetails(basePayload, alarmData) {
      try {
        const detailedPayload = Object.assign({}, basePayload, { include_diff: true });
        const resp = await fetch(`/api/alarm/check?cacheBust=${Date.now()}-diff`, {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify(detailedPayload)
        });
        const data = await resp.json();
        if (!resp.ok || !data || !data.found) return;

        const expectedTime = String((alarmData && alarmData.file_time_utc) || "");
        const returnedTime = String(data.file_time_utc || "");
        if (expectedTime && returnedTime && expectedTime !== returnedTime) return;
        updateOpenCrestAlarmDiff(data);
      } catch (err) {
        console.debug("Deferred CREST alarm difference unavailable", err);
        updateOpenCrestAlarmDiff({
          diff_10m: null,
          diff_10m_label: (alarmData && alarmData.diff_10m_label) || "10-min difference",
          diff_10m_units: "cfs/mi²"
        });
      }
    }

    function clearAlarmMaxPulse() {
      alarmMaxPulseSerial += 1;
      forEachPanel(function (key, panel) {
        try {
          panel.alarmMaxMarkerGroup.clearLayers();
          if (panel.map.hasLayer(panel.alarmMaxMarkerGroup)) panel.map.removeLayer(panel.alarmMaxMarkerGroup);
        } catch (e) {}
      });
    }

    function showAlarmMaxPulse(payload, color) {
      const lat = Number(payload && payload.lat);
      const lon = Number(payload && payload.lon);
      const maxValue = Number(payload && payload.max_value);
      if (!Number.isFinite(lat) || !Number.isFinite(lon)) return;
      clearAlarmMaxPulse();
      const serial = ++alarmMaxPulseSerial;
      const diff = Number(payload && payload.diff_10m);
      const diffText = Number.isFinite(diff) ? ` | Δ10m ${diff > 0 ? "+" : ""}${Math.round(diff).toLocaleString()}` : "";
      const label = `ALARM MAX ${Number.isFinite(maxValue) ? Math.round(maxValue).toLocaleString() : ""} cfs/mi²${diffText}`;
      const latlng = [lat, lon];
      const pulseColor = "#ffffff";
      const icon = L.divIcon({
        className: "alarm-max-pulse-marker",
        html: `<div class="alarm-max-pulse-ring" style="border-color:${pulseColor};box-shadow:0 0 16px ${pulseColor},0 0 34px rgba(255,255,255,0.95);"></div>`,
        iconSize: [42, 42],
        iconAnchor: [21, 21]
      });
      forEachActivePanel(function (key, panel) {
        try {
          panel.alarmMaxMarkerGroup = L.layerGroup().addTo(panel.map);
          const marker = L.marker(latlng, {icon: icon, interactive: false, keyboard: false});
          marker.bindTooltip(label, {
            permanent: true,
            direction: "top",
            offset: [0, -18],
            className: "max-tooltip"
          });
          panel.alarmMaxMarkerGroup.addLayer(marker);
          panel.alarmMaxMarkerGroup.addLayer(L.circleMarker(latlng, {
            radius: 11,
            color: pulseColor,
            weight: 4,
            opacity: 1,
            fill: false,
            interactive: false
          }));
          bringPanelBoundariesToFront(key);
        } catch (e) {}
      });
      setTimeout(function () {
        if (serial === alarmMaxPulseSerial) {
          // Keep it visible while the popup is open; the close button clears it.
        }
      }, 50);
    }

    function makeCrestAlarmPopupDraggable(modal) {
      if (!modal) return;

      let dragging = false;
      let startX = 0;
      let startY = 0;
      let startLeft = 0;
      let startTop = 0;

      function pointerFromEvent(e) {
        if (e && e.touches && e.touches.length) {
          return {x: e.touches[0].clientX, y: e.touches[0].clientY};
        }
        if (e && e.changedTouches && e.changedTouches.length) {
          return {x: e.changedTouches[0].clientX, y: e.changedTouches[0].clientY};
        }
        return {x: e.clientX, y: e.clientY};
      }

      function clampModalToViewport(left, top) {
        const rect = modal.getBoundingClientRect();
        const margin = 6;
        const maxLeft = Math.max(margin, window.innerWidth - rect.width - margin);
        const maxTop = Math.max(margin, window.innerHeight - rect.height - margin);
        return {
          left: Math.max(margin, Math.min(maxLeft, left)),
          top: Math.max(margin, Math.min(maxTop, top))
        };
      }

      function startDrag(e) {
        if (!e) return;
        if (e.target && e.target.closest && e.target.closest("button, input, select, textarea, a")) return;
        const p = pointerFromEvent(e);
        const rect = modal.getBoundingClientRect();
        dragging = true;
        startX = p.x;
        startY = p.y;
        startLeft = rect.left;
        startTop = rect.top;
        modal.classList.add("alarm-modal-dragging");
        modal.style.left = `${startLeft}px`;
        modal.style.top = `${startTop}px`;
        modal.style.transform = "none";
        e.preventDefault();
      }

      function moveDrag(e) {
        if (!dragging) return;
        const p = pointerFromEvent(e);
        const next = clampModalToViewport(startLeft + (p.x - startX), startTop + (p.y - startY));
        modal.style.left = `${next.left}px`;
        modal.style.top = `${next.top}px`;
        e.preventDefault();
      }

      function endDrag() {
        if (!dragging) return;
        dragging = false;
        modal.classList.remove("alarm-modal-dragging");
      }

      modal.addEventListener("mousedown", startDrag);
      document.addEventListener("mousemove", moveDrag);
      document.addEventListener("mouseup", endDrag);
      modal.addEventListener("touchstart", startDrag, {passive: false});
      document.addEventListener("touchmove", moveDrag, {passive: false});
      document.addEventListener("touchend", endDrag);
    }

    function showCrestAlarmPopup(payload, level, color) {
      const old = document.getElementById("crestAlarmModalBackdrop");
      if (old) old.remove();

      const alarmValue = Number(payload && (payload.alarm_value ?? payload.max_value));
      const maxValue = Number(payload && payload.max_value);
      const statisticLabel = escapeHtml((payload && payload.alarm_value_label) || "Max pixel");
      const alarmText = Number.isFinite(alarmValue)
        ? `${Math.round(alarmValue).toLocaleString()} cfs/mi²`
        : "No valid alarm value";
      const maxText = Number.isFinite(maxValue)
        ? `${Math.round(maxValue).toLocaleString()} cfs/mi²`
        : "No valid max value";
      const validText = cleanValidTimeText((payload && payload.file_time_utc) || selectedTimeLabel());
      const scopeText = alarmScope() === "polygon" ? "drawn alarm area" : `${alarmDomainDisplayName()}`;
      const latLonText = payload && Number.isFinite(Number(payload.lat)) && Number.isFinite(Number(payload.lon))
        ? `<br>Max pixel: ${maxText} at ${Number(payload.lat).toFixed(4)}, ${Number(payload.lon).toFixed(4)}`
        : "";
      const pureText = payload && Number.isFinite(Number(payload.pure_mean))
        ? `<br>Pure avg: ${Math.round(Number(payload.pure_mean)).toLocaleString()} cfs/mi²`
        : "";
      const matchedText = payload && Number.isFinite(Number(payload.matched_mean))
        ? `<br>High-value weighted average: ${Math.round(Number(payload.matched_mean)).toLocaleString()} cfs/mi²`
        : "";

      const backdrop = document.createElement("div");
      backdrop.id = "crestAlarmModalBackdrop";
      backdrop.className = "alarm-modal-backdrop";
      backdrop.innerHTML = `
        <div class="alarm-modal" role="alertdialog" aria-modal="true" title="Click and drag this alarm box to move it" style="border-color:${color};box-shadow:0 0 26px ${color};">
          <div class="alarm-modal-title" style="color:${color};">CREST Alarm Notification</div>
          <div>CREST <b>${statisticLabel}</b> of <b>${level.toLocaleString()}+</b> has been detected in the ${scopeText} with the latest scan.</div>
          <div class="alarm-modal-value" style="color:${color};">${alarmText}</div>
          ${formatAlarmDiffHtml(payload)}
          <div class="alarm-modal-meta">Valid: ${escapeHtml(validText || "latest scan")}${latLonText}${payload && payload.alarm_statistic === "area_average" ? pureText + matchedText : ""}<br>Next alarm level: ${(level + 100).toLocaleString()}+ cfs/mi²</div>
          <button class="alarm-modal-close" onclick="closeCrestAlarmPopup()">Acknowledge / Close</button>
        </div>`;
      document.body.appendChild(backdrop);
      makeCrestAlarmPopupDraggable(backdrop.querySelector(".alarm-modal"));
      showAlarmMaxPulse(payload, "#ffffff");
      playSoftAlarmDings();
    }

    function closeCrestAlarmPopup() {
      const el = document.getElementById("crestAlarmModalBackdrop");
      if (el) el.remove();
      clearAlarmMaxPulse();
    }

    function updateAlarmModeBell() {
      const bell = document.getElementById("alarmModeBell");
      if (!bell) return;
      bell.classList.toggle("alarm-bell-visible", !!crestAlarmEnabled);
      bell.setAttribute("aria-hidden", crestAlarmEnabled ? "false" : "true");
    }

    function toggleCrestAlarm() {
      const enabled = !!document.getElementById("enableCrestAlarm").checked;
      crestAlarmEnabled = enabled;
      updateAlarmModeBell();
      initAlarmAudio();
      crestAlarmLastCheckedKey = "";
      if (enabled) {
        // First successful check may issue one initial notification for the
        // current area/category. After that, only genuinely new LIVE scans that
        // cross the next higher 100-level can notify.
        crestAlarmLastLevel = 0;
        crestAlarmBaselineReady = false;
        crestAlarmInitialAlertPending = true;
        crestAlarmLastDataToken = "";
        if (alarmScope() === "domain") prefetchAlarmCwaGeometry(alarmDomainName());
        updateAlarmStatus(`Alarm ON. Analyzing the latest LIVE CREST scan for ${alarmMinThreshold()}+ using ${alarmScope() === "polygon" ? "drawn polygon" : alarmDomainDisplayName()} | ${alarmStatisticLabel()}...`);
        scheduleCrestAlarmCheck(100, true);
      } else {
        clearTimeout(crestAlarmTimer);
        clearAlarmMaxPulse();
        crestAlarmBaselineReady = false;
        crestAlarmInitialAlertPending = false;
        crestAlarmLastDataToken = "";
        updateAlarmStatus("Alarm is OFF. It will only check LIVE CREST updates when enabled.");
      }
    }

    function scheduleCrestAlarmCheck(delay=1200, force=false) {
      clearTimeout(crestAlarmTimer);
      if (!crestAlarmEnabled) return;
      crestAlarmTimer = setTimeout(function () {
        checkCrestAlarmNow(force);
      }, Math.max(50, Number(delay) || 1200));
    }

    function alarmDomainBounds() {
      const d = domains[alarmDomainName()] || domains[DEFAULT_VIEW_DOMAIN] || domains.LIX;
      return {
        west: d.west,
        south: d.south,
        east: d.east,
        north: d.north
      };
    }

    async function checkCrestAlarmNow(force=false) {
      if (!crestAlarmEnabled) return;

      const modeEl = document.getElementById("timeMode");
      if (modeEl && modeEl.value !== "latest") {
        updateAlarmStatus("Alarm ON, but paused in ARCHIVE mode. Return to LIVE for latest-scan alarms.");
        return;
      }

      const token = liveTokenForProduct("CREST") || liveLatestToken || selectedEffectiveToken() || currentRoundedToken();
      if (!token) {
        updateAlarmStatus("Alarm ON. Waiting for latest CREST time...");
        return;
      }

      const scope = alarmScope();
      const threshold = alarmMinThreshold();
      const statistic = alarmStatistic();
      const meanMode = selectedAverageMode();
      const vertices = alarmAreaPlainVertices();
      if (scope === "polygon" && vertices.length < 3) {
        updateAlarmStatus("Alarm ON. Draw and finish an alarm polygon before polygon alarms can run.");
        return;
      }

      const checkKey = JSON.stringify({
        token,
        scope,
        threshold,
        statistic,
        mean_mode: meanMode,
        vertices: scope === "polygon" ? vertices.map(v => [v.lat.toFixed(5), v.lon.toFixed(5)]) : [],
        cwa: scope === "domain" ? alarmDomainName() : null
      });
      if (!force && checkKey === crestAlarmLastCheckedKey) return;
      crestAlarmLastCheckedKey = checkKey;

      const thisFetch = ++crestAlarmFetchSerial;
      const payload = {
        scope,
        threshold,
        statistic,
        mean_mode: meanMode,
        // LIVE alarms must analyze the actual newest CREST object directly.
        // The token is only a browser-side de-duplication hint and is not used
        // by the server to resolve a historical/archive file.
        live: true,
        crest_probe_token: token,
        width: 950,
        vertices,
        cwa: scope === "domain" ? alarmDomainName() : "",
        bounds: alarmDomainBounds(),
        include_diff: false
      };

      try {
        const resp = await fetch(`/api/alarm/check?cacheBust=${Date.now()}`, {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify(payload)
        });
        const data = await resp.json();
        if (thisFetch !== crestAlarmFetchSerial) return;
        if (!resp.ok) throw new Error(data.error || "alarm check failed");

        const alarmValue = Number(data.alarm_value ?? data.max_value);
        if (!data.found || !Number.isFinite(alarmValue)) {
          updateAlarmStatus(`Alarm ON. No valid CREST pixels found for ${tokenToIsoZ(token)}.`);
          return;
        }

        const level = Math.floor(alarmValue / 100.0) * 100;
        const scopeText = scope === "polygon" ? "drawn polygon" : `${alarmDomainDisplayName()}`;
        const statLabel = data.alarm_value_label || alarmStatisticLabel();
        const rawDiff = data ? data.diff_10m : null;
        const diff = rawDiff === null || rawDiff === undefined ? NaN : Number(rawDiff);
        const diffStatus = Number.isFinite(diff)
          ? ` | Δ10m <b style="color:${diff > 0.5 ? "#ff4b4b" : (diff < -0.5 ? "#4bb3ff" : "#dddddd")};">${diff > 0 ? "+" : ""}${Math.round(diff).toLocaleString()}</b>`
          : "";
        const dataToken = String((data && data.file_time_utc) || token);

        if (!crestAlarmBaselineReady) {
          crestAlarmBaselineReady = true;
          crestAlarmLastDataToken = dataToken;
          // Remember the current 100-level. Example: 490 -> 400, so after the
          // initial 490 notification the next eligible new-scan category is 500.
          // If below the minimum threshold, no initial popup occurs; e.g. 180
          // baselines at 100 and a later new scan at 210 can alert at 200.
          crestAlarmLastLevel = Math.max(0, level);

          const shouldInitialAlert = crestAlarmInitialAlertPending && level >= threshold;
          crestAlarmInitialAlertPending = false;

          if (shouldInitialAlert) {
            const exactColor = data.color_hex || crestAlarmColorForValue(alarmValue);
            updateAlarmStatus(`Alarm ON. Initial ${scopeText} notification: ${escapeHtml(statLabel)} <b>${Math.round(alarmValue).toLocaleString()} cfs/mi²</b>${diffStatus} at ${cleanValidTimeText(data.file_time_utc || tokenToIsoZ(token))}. Current 100-level: ${crestAlarmLastLevel.toLocaleString()}+. Next new-scan alarm level: ${(crestAlarmLastLevel + 100).toLocaleString()}+.`);
            data.diff_pending = true;
            showCrestAlarmPopup(data, crestAlarmLastLevel, exactColor);
            fetchCrestAlarmDiffDetails(payload, data);
            return;
          }

          updateAlarmStatus(`Alarm ON. Baseline established from ${cleanValidTimeText(data.file_time_utc || tokenToIsoZ(token))}: ${escapeHtml(statLabel)} <b>${Math.round(alarmValue).toLocaleString()} cfs/mi²</b>${diffStatus}. Current value is below the ${threshold.toLocaleString()}+ minimum, so no initial alert was issued. A genuinely new scan can alert when it reaches an eligible higher 100-level.`);
          return;
        }

        const isNewScan = dataToken !== crestAlarmLastDataToken;
        updateAlarmStatus(`Alarm ON. Latest ${scopeText} ${escapeHtml(statLabel)}: <b>${Math.round(alarmValue).toLocaleString()} cfs/mi²</b>${diffStatus} at ${cleanValidTimeText(data.file_time_utc || tokenToIsoZ(token))}. Last alarm level: ${crestAlarmLastLevel || "none"}.${isNewScan ? " New scan evaluated." : " Same scan; no repeat alert."}`);

        // Only a genuinely newer LIVE scan can generate a banner. Re-checks of
        // the same token (including one-minute polling and forced UI refreshes)
        // are status updates only.
        if (isNewScan) {
          crestAlarmLastDataToken = dataToken;
          if (level >= threshold && level > crestAlarmLastLevel) {
            crestAlarmLastLevel = level;
            const exactColor = data.color_hex || crestAlarmColorForValue(alarmValue);
            data.diff_pending = true;
            showCrestAlarmPopup(data, level, exactColor);
            fetchCrestAlarmDiffDetails(payload, data);
          }
        }
      } catch (err) {
        if (thisFetch === crestAlarmFetchSerial) {
          updateAlarmStatus(`Alarm check failed: ${escapeHtml(err.message || err)}`);
        }
      }
    }

    function disableAlarmAreaDrawMode() {
      alarmAreaDrawEnabled = false;
      alarmAreaDrawing = null;
      alarmAreaSourcePanelKey = null;
      const btn = document.getElementById("drawAlarmAreaBtn");
      if (btn) {
        btn.classList.remove("alarm-draw-active");
        btn.textContent = "Draw Alarm Area";
      }
      forEachPanel(function (key, panel) {
        const container = panel.map.getContainer();
        if (!areaAvgEnabled) {
          try { panel.map.dragging.enable(); } catch (e) {}
          try { panel.map.doubleClickZoom.enable(); } catch (e) {}
          container.style.cursor = "";
        }
      });
    }

    function toggleAlarmAreaDraw() {
      const next = !alarmAreaDrawEnabled;
      if (next) {
        const areaEl = document.getElementById("enableAreaAvg");
        if (areaEl && areaEl.checked) {
          areaEl.checked = false;
          toggleAreaAverageTool();
        }
        alarmAreaDrawEnabled = true;
        alarmAreaDrawing = null;
        alarmAreaVertices = [];
        alarmAreaSourcePanelKey = null;
        const btn = document.getElementById("drawAlarmAreaBtn");
        if (btn) {
          btn.classList.add("alarm-draw-active");
          btn.textContent = "Drawing...";
        }
        forEachPanel(function (key, panel) {
          try { panel.map.dragging.disable(); } catch (e) {}
          try { panel.map.doubleClickZoom.disable(); } catch (e) {}
          panel.map.getContainer().style.cursor = "crosshair";
        });
        updateAlarmStatus("Click vertices on any active panel, then double-click or press Finish Area. Alarm scope will switch to Drawn alarm polygon.");
      } else {
        disableAlarmAreaDrawMode();
      }
    }

    function drawAlarmAreaShape(vertices, finalized=false) {
      if (!Array.isArray(vertices)) return;
      forEachActivePanel(function (key, panel) {
        if (!panel.map.hasLayer(panel.alarmAreaGroup)) {
          panel.alarmAreaGroup.addTo(panel.map);
        }
        panel.alarmAreaGroup.clearLayers();
        if (vertices.length >= 3 && finalized) {
          const polygon = L.polygon(vertices, {
            color: "#ffd200",
            weight: 3.0,
            opacity: 1.0,
            fill: true,
            fillColor: "#ffd200",
            fillOpacity: 0.10,
            interactive: false,
            className: "alarm-area-pulse-shape"
          });
          panel.alarmAreaGroup.addLayer(polygon);
        } else if (vertices.length > 0) {
          panel.alarmAreaGroup.addLayer(L.polyline(vertices, {
            color: "#ffd200",
            weight: 2.5,
            opacity: 1.0,
            dashArray: "5,5",
            interactive: false
          }));
          for (const latlng of vertices) {
            panel.alarmAreaGroup.addLayer(L.circleMarker(latlng, {
              radius: 4,
              color: "#ffd200",
              weight: 2,
              fill: true,
              fillColor: "#000000",
              fillOpacity: 0.85,
              interactive: false
            }));
          }
        }
        bringPanelBoundariesToFront(key);
      });
    }

    function clearAlarmArea() {
      alarmAreaDrawing = null;
      alarmAreaVertices = [];
      alarmAreaFinalizedVertices = [];
      alarmAreaSourcePanelKey = null;
      disableAlarmAreaDrawMode();
      forEachPanel(function (key, panel) {
        try { panel.alarmAreaGroup.clearLayers(); } catch (e) {}
        try {
          if (panel.map.hasLayer(panel.alarmAreaGroup)) panel.map.removeLayer(panel.alarmAreaGroup);
        } catch (e) {}
      });
      crestAlarmLastCheckedKey = "";
      updateAlarmStatus(crestAlarmEnabled
        ? "Alarm area cleared. Selected CWA/domain mode is available, or draw a new polygon."
        : "Alarm area cleared. Alarm is OFF.");
      scheduleCrestAlarmCheck(300, true);
    }

    function finishAlarmAreaPolygon() {
      if (!alarmAreaDrawEnabled || alarmAreaVertices.length < 3) return;
      alarmAreaFinalizedVertices = alarmAreaVertices.slice();
      alarmAreaDrawing = null;
      drawAlarmAreaShape(alarmAreaFinalizedVertices, true);
      disableAlarmAreaDrawMode();
      const scopeEl = document.getElementById("alarmScope");
      if (scopeEl) scopeEl.value = "polygon";
      alarmSettingsChanged(true);
      updateAlarmStatus(`Alarm polygon set with ${alarmAreaFinalizedVertices.length} vertices. ${crestAlarmEnabled ? `Checking the current LIVE scan now; an initial notification will fire if ${alarmStatisticLabel()} meets CREST ${alarmMinThreshold()}+.` : "Alarm is OFF."}`);
      scheduleCrestAlarmCheck(350, true);
    }

    function handleAlarmAreaMapClick(panelKey, e) {
      if (!alarmAreaDrawEnabled || !activePanelKeys().includes(panelKey) || !e.latlng) return false;
      if (e.originalEvent) {
        L.DomEvent.preventDefault(e.originalEvent);
        L.DomEvent.stopPropagation(e.originalEvent);
      }
      if (!alarmAreaDrawing || alarmAreaSourcePanelKey !== panelKey) {
        alarmAreaDrawing = { mode: "polygon" };
        alarmAreaVertices = [];
        alarmAreaSourcePanelKey = panelKey;
      }
      alarmAreaVertices.push(e.latlng);
      drawAlarmAreaShape(alarmAreaVertices, false);
      return true;
    }

    function handleAlarmAreaMouseMove(panelKey, e) {
      if (!alarmAreaDrawEnabled || !alarmAreaDrawing || alarmAreaSourcePanelKey !== panelKey || !e.latlng) return;
      drawAlarmAreaShape(alarmAreaVertices.concat([e.latlng]), false);
    }

    function handleAlarmAreaDoubleClick(panelKey, e) {
      if (!alarmAreaDrawEnabled || alarmAreaSourcePanelKey !== panelKey || alarmAreaVertices.length < 3) return;
      if (e && e.originalEvent) {
        L.DomEvent.preventDefault(e.originalEvent);
        L.DomEvent.stopPropagation(e.originalEvent);
      }
      finishAlarmAreaPolygon();
    }


async function loadArchiveList() {
  return updateLiveLatestToken(true);
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
      await updateLiveLatestToken(true);
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
      const token = selectedEffectiveTokenForParam("CREST") || selectedEffectiveToken();
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
      const token = selectedEffectiveTokenForParam(param);
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

        const maxPulseIcon = L.divIcon({
          className: "max-target-pulse-marker",
          html: '<div class="max-target-pulse-ring"></div>',
          iconSize: [36, 36],
          iconAnchor: [18, 18]
        });

        const pulseMarker = L.marker(latlng, {
          icon: maxPulseIcon,
          interactive: true,
          keyboard: false
        });

        pulseMarker.bindTooltip(`${labelPrefix} ${valueText}`, {
          permanent: true,
          direction: "top",
          offset: [0, -16],
          className: "max-tooltip"
        });

        circleOuter.bindPopup(popupHtml);
        circleInner.bindPopup(popupHtml);
        pulseMarker.bindPopup(popupHtml);

        panel.maxMarkerGroup.addLayer(pulseMarker);
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
      const token = selectedEffectiveTokenForParam(param);
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
        scheduleCrestAlarmCheck(750);
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

    function scheduleActiveReadoutRefresh(delay=650) {
      clearTimeout(activeReadoutRefreshTimer);
      activeReadoutRefreshTimer = setTimeout(function () {
        refreshActiveReadoutsForCurrentTime();
      }, delay);
    }

    function refreshActiveReadoutsForCurrentTime() {
      if (activeClickReadout && Number.isFinite(Number(activeClickReadout.lat)) && Number.isFinite(Number(activeClickReadout.lon))) {
        showClickReadoutsAt(activeClickReadout.lat, activeClickReadout.lon, false);
      }

      if (Array.isArray(areaAvgFinalizedVertices) && areaAvgFinalizedVertices.length >= 3) {
        finalizeAreaAveragePolygon(areaAvgFinalizedVertices.slice(), true);
      }
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
          clearPanelClickReadout(key);
        }
      });
      scheduleActiveReadoutRefresh();
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

    function escapeHtml(value) {
      return String(value ?? "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#39;");
    }

    function compactSparkValue(value, units, signed=false) {
      const n = Number(value);
      if (!Number.isFinite(n)) return "--";
      const unitText = String(units || "");
      let digits = 0;
      if (unitText.includes("in")) digits = Math.abs(n) < 1 ? 2 : 1;
      if (unitText.includes("dBZ")) digits = 0;
      const sign = signed && n > 0 ? "+" : "";
      if (!unitText.includes("in") && !unitText.includes("dBZ") && Math.abs(n) >= 1000) {
        return `${sign}${Math.round(n / 100) / 10}k`;
      }
      return `${sign}${n.toLocaleString(undefined, {minimumFractionDigits: digits, maximumFractionDigits: digits})}`;
    }

    function compactSparkTimeLabel(point) {
      const label = String((point && point.label) || "");
      const m = label.match(/\b(\d{2}):(\d{2})(?::\d{2})?Z?\b/);
      if (m) return `${m[1]}${m[2]}Z`;
      const minutesAgo = Number(point && point.minutesAgo);
      if (Number.isFinite(minutesAgo)) return `-${minutesAgo}m`;
      return "";
    }

    const READOUT_POPUP_WIDTH = 344;
    const READOUT_CONTENT_WIDTH = 320;
    const READOUT_TREND_GRAPH_WIDTH = 320;
    const READOUT_TREND_GRAPH_HEIGHT = 90;

    function enforceReadoutPopupDimensions(popup) {
      if (!popup || typeof popup.getElement !== "function") return;
      const root = popup.getElement();
      if (!root) return;

      root.style.width = `${READOUT_POPUP_WIDTH}px`;
      root.style.minWidth = `${READOUT_POPUP_WIDTH}px`;
      root.style.maxWidth = `${READOUT_POPUP_WIDTH}px`;

      const wrapper = root.querySelector(".leaflet-popup-content-wrapper");
      if (wrapper) {
        wrapper.style.width = `${READOUT_POPUP_WIDTH}px`;
        wrapper.style.minWidth = `${READOUT_POPUP_WIDTH}px`;
        wrapper.style.maxWidth = `${READOUT_POPUP_WIDTH}px`;
      }

      const content = root.querySelector(".leaflet-popup-content");
      if (content) {
        content.style.width = `${READOUT_CONTENT_WIDTH}px`;
        content.style.minWidth = `${READOUT_CONTENT_WIDTH}px`;
        content.style.maxWidth = `${READOUT_CONTENT_WIDTH}px`;
      }

      root.querySelectorAll(".readout-shell, .readout-trend-wrap").forEach(function (el) {
        el.style.width = `${READOUT_CONTENT_WIDTH}px`;
        el.style.minWidth = `${READOUT_CONTENT_WIDTH}px`;
        el.style.maxWidth = `${READOUT_CONTENT_WIDTH}px`;
      });

      root.querySelectorAll(".readout-trend-svg").forEach(function (svg) {
        svg.setAttribute("width", String(READOUT_TREND_GRAPH_WIDTH));
        svg.setAttribute("height", String(READOUT_TREND_GRAPH_HEIGHT));
        svg.style.width = `${READOUT_TREND_GRAPH_WIDTH}px`;
        svg.style.minWidth = `${READOUT_TREND_GRAPH_WIDTH}px`;
        svg.style.maxWidth = `${READOUT_TREND_GRAPH_WIDTH}px`;
        svg.style.height = `${READOUT_TREND_GRAPH_HEIGHT}px`;
      });
    }

    function refreshReadoutPopupLayout(popup) {
      if (!popup) return;
      try { if (typeof popup.update === "function") popup.update(); } catch (e) {}
      enforceReadoutPopupDimensions(popup);
      requestAnimationFrame(function () {
        try { if (typeof popup.update === "function") popup.update(); } catch (e) {}
        enforceReadoutPopupDimensions(popup);
      });
      setTimeout(function () {
        try { if (typeof popup.update === "function") popup.update(); } catch (e) {}
        enforceReadoutPopupDimensions(popup);
      }, 40);
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
      const windowMinutes = Math.max(...pts.map(p => Number(p.minutesAgo || 0)));
      const windowLabel = windowMinutes >= 60 ? "1h" : `${windowMinutes}m`;

      // Signed Δ/rate-of-change products need threat-aware trend logic rather
      // than a simple up=bad/down=good rule. A negative value already means
      // the underlying quantity is decreasing. Therefore a rise that remains
      // negative (for example -164 -> -90) is recovery back toward neutral/0,
      // not renewed worsening. Crossing into positive territory is worsening.
      const trendScore = delta;
      const recoveringTowardZero = signed && first < 0 && last <= 0 && trendScore > eps;

      let color = "#9a9a9a";
      let label = `${windowLabel} SAME`;
      let arrow = "→";
      let trendQualifier = "";
      if (Math.abs(trendScore) > eps) {
        if (recoveringTowardZero) {
          color = "#4bb3ff";
          label = `${windowLabel} BETTER`;
          arrow = "↗";
          trendQualifier = " toward 0";
        } else if (trendScore > 0) {
          color = "#ff4b4b";
          label = `${windowLabel} WORSE`;
          arrow = "↗";
        } else {
          color = "#4bb3ff";
          label = `${windowLabel} BETTER`;
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

      // Width is based only on popup type, never on the number of trend frames.
      // Therefore 30-minute and 60-minute trends always render at the same width.
      const w = READOUT_TREND_GRAPH_WIDTH;
      const h = READOUT_TREND_GRAPH_HEIGHT;
      const padX = 14;
      const padTop = 19;
      const padBottom = 14;
      const plotH = h - padTop - padBottom;
      const xStep = pts.length > 1 ? (w - 2 * padX) / (pts.length - 1) : 0;
      const coords = pts.map((p, i) => {
        const x = padX + i * xStep;
        const y = padTop + (1 - ((p.mean - vmin) / (vmax - vmin))) * plotH;
        return {x, y, p};
      });
      const pointText = coords.map(c => `${c.x.toFixed(1)},${c.y.toFixed(1)}`).join(" ");
      const latest = coords[coords.length - 1];
      const oldest = coords[0];
      const dotHtml = coords.map((c, i) => {
        const r = i === coords.length - 1 ? 4.6 : 3.7;
        return `<circle cx="${c.x.toFixed(1)}" cy="${c.y.toFixed(1)}" r="${r}" fill="${color}" stroke="#ffffff" stroke-width="0.8"></circle>`;
      }).join("");
      const valueLabels = coords.map((c, i) => {
        const y = i % 2 === 0 ? Math.max(12, c.y - 6) : Math.min(h - 13, c.y + 13);
        return `<text x="${c.x.toFixed(1)}" y="${y.toFixed(1)}" fill="#ffffff" font-size="12" text-anchor="middle" font-weight="900" style="paint-order:stroke;stroke:#000000;stroke-width:2.2px;stroke-linejoin:round;">${escapeHtml(compactSparkValue(c.p.mean, units, signed))}</text>`;
      }).join("");
      const timeLabels = coords.map((c, i) => {
        if (pts.length > 5 && i % 2 === 1 && i !== coords.length - 1) return "";
        return `<text x="${c.x.toFixed(1)}" y="${h - 4}" fill="#cfcfcf" font-size="7" text-anchor="middle">${escapeHtml(compactSparkTimeLabel(c.p))}</text>`;
      }).join("");
      const titleText = pts.map(p => `${compactSparkTimeLabel(p)} (${p.minutesAgo}m ago): ${formatAreaAverageValue(p.mean, units, signed)}`).join(" | ");
      const zeroLine = (vmin < 0 && vmax > 0)
        ? `<line x1="${padX}" y1="${(padTop + (1 - ((0 - vmin) / (vmax - vmin))) * plotH).toFixed(1)}" x2="${w - padX}" y2="${(padTop + (1 - ((0 - vmin) / (vmax - vmin))) * plotH).toFixed(1)}" stroke="#555" stroke-width="1" stroke-dasharray="3,3"></line>`
        : "";
      const selectedLine = `<line x1="${latest.x.toFixed(1)}" y1="3" x2="${latest.x.toFixed(1)}" y2="${h - 11}" stroke="#ffffff" stroke-width="1.4"></line>`;
      const deltaText = `${arrow} ${label} (${compactSparkValue(delta, units, true)} Δ${trendQualifier})`;

      return `
        <div class="readout-trend-wrap">
          <div class="readout-trend-heading" style="color:${color};">${escapeHtml(deltaText)}</div>
          <svg class="readout-trend-svg" width="${w}" height="${h}" viewBox="0 0 ${w} ${h}">
            <title>${escapeHtml(titleText)}</title>
            ${zeroLine}
            ${selectedLine}
            <polyline points="${pointText}" fill="none" stroke="${color}" stroke-width="3.0" stroke-linecap="round" stroke-linejoin="round"></polyline>
            ${dotHtml}
            ${valueLabels}
          </svg>
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
      if (param === "RAINRATE_DIFF_10M") {
        if (v > 0.01) {
          return `<span style="color:#ff4b4b;font-size:15px;font-weight:900;">CURRENT Δ: RAIN RATE INCREASING</span><br>`;
        }
        if (v < -0.01) {
          return `<span style="color:#4bb3ff;font-size:15px;font-weight:900;">CURRENT Δ: RAIN RATE DECREASING</span><br>`;
        }
        return `<span style="color:#dddddd;font-size:14px;font-weight:800;">CURRENT Δ: RAIN RATE NEAR STEADY</span><br>`;
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
      if (areaAvgEnabled && alarmAreaDrawEnabled) {
        disableAlarmAreaDrawMode();
      }
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
      areaAverageRequestKey = "";
      areaAverageRequestActive = false;
      areaAverageCompletedKey = "";
      areaAvgDrawing = null;
      areaAvgVertices = [];
      areaAvgFinalizedVertices = [];
      areaAvgSourcePanelKey = null;
      forEachPanel(function (key, panel) {
        try {
          if (panel.areaAvgAbortController) panel.areaAvgAbortController.abort();
        } catch (e) {}
        panel.areaAvgAbortController = null;
        try { panel.areaAvgGroup.clearLayers(); } catch (e) {}
        try {
          if (panel.map.hasLayer(panel.areaAvgGroup)) panel.map.removeLayer(panel.areaAvgGroup);
        } catch (e) {}
        try {
          if (panel.areaAvgPopup) {
            panel.map.closePopup(panel.areaAvgPopup);
            if (panel.map.hasLayer(panel.areaAvgPopup)) panel.map.removeLayer(panel.areaAvgPopup);
            if (typeof panel.areaAvgPopup.remove === "function") panel.areaAvgPopup.remove();
          }
        } catch (e) {}
        panel.areaAvgPopup = null;
        try {
          panel.map.getContainer().querySelectorAll(".area-avg-popup").forEach(el => el.remove());
        } catch (e) {}
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

    async function finalizeAreaAveragePolygon(vertices, refreshOnly=false) {
      const plainVertices = vertices.map(v => ({lat: v.lat, lon: v.lng}));
      const keys = activePanelKeys();
      const requestKey = JSON.stringify({
        vertices: plainVertices.map(v => [Number(v.lat).toFixed(5), Number(v.lon).toFixed(5)]),
        tokens: keys.map(key => selectedEffectiveTokenForParam(selectedParam(key)) || "latest"),
        samples: readoutTrendSamples(),
        mean_mode: selectedAverageMode(),
        params: keys.map(key => selectedParam(key))
      });
      if (refreshOnly && requestKey === areaAverageRequestKey &&
          (areaAverageRequestActive || areaAverageCompletedKey === requestKey)) return;
      areaAverageRequestKey = requestKey;
      areaAverageRequestActive = true;
      const serial = ++areaAvgSerial;
      const clearSerialAtStart = readoutClearSerial;
      areaAvgFinalizedVertices = vertices.slice();
      drawAreaAverageShape(vertices, true);
      let pending = keys.length;
      const completeOne = function () {
        pending -= 1;
        if (pending <= 0 && areaAverageRequestKey === requestKey) {
          areaAverageRequestActive = false;
          areaAverageCompletedKey = requestKey;
        }
      };

      forEachActivePanel(async function (key, panel) {
        const param = selectedParam(key);
        const product = rawProductForParam(param);
        const token = selectedEffectiveTokenForParam(param);
        const info = selectedParamInfo(key);
        try { if (panel.areaAvgAbortController) panel.areaAvgAbortController.abort(); } catch (e) {}
        const controller = new AbortController();
        panel.areaAvgAbortController = controller;
        const loadingHtml = `<div class="readout-shell"><span class="readout-title">${info.shortLabel} area average</span><br>Computing...</div>`;
        try {
          if (panel.areaAvgPopup) panel.map.closePopup(panel.areaAvgPopup);
          panel.areaAvgPopup = L.popup({
              autoClose: false,
              closeOnClick: false,
              className: "shared-readout-popup area-avg-popup",
              maxWidth: READOUT_POPUP_WIDTH,
              minWidth: READOUT_POPUP_WIDTH,
              autoPan: true,
              autoPanPadding: [18, 18],
              offset: [0, 0]
            })
            .setLatLng(areaAveragePopupLatLng(vertices, panel.map))
            .setContent(loadingHtml)
            .openOn(panel.map);
          refreshReadoutPopupLayout(panel.areaAvgPopup);
        } catch (e) {}

        try {
          const resp = await fetch(`/api/area_average_polygon_trend`, {
            method: 'POST',
            headers: {'Content-Type': 'application/json'},
            body: JSON.stringify({param, product, time: token || "", vertices: plainVertices, samples: readoutTrendSamples(), step_minutes: 10, mean_mode: selectedAverageMode()}),
            signal: controller.signal
          });
          const data = await resp.json();
          if (controller.signal.aborted) return;
          if (clearSerialAtStart !== readoutClearSerial) return;
          if (serial !== areaAvgSerial) return;
          const units = data.display_units || info.units || "";
          const signed = !!info.isDifference;
          const meanText = resp.ok && data.found ? formatAreaAverageValue(data.mean, units, signed) : "No valid pixels";
          const pureMeanText = resp.ok && data.found && Number.isFinite(Number(data.pure_mean)) ? formatAreaAverageValue(data.pure_mean, units, signed) : "";
          const matchedMeanText = resp.ok && data.found && Number.isFinite(Number(data.matched_mean)) ? formatAreaAverageValue(data.matched_mean, units, signed) : "";
          const minText = resp.ok && data.found ? formatAreaAverageValue(data.min, units, signed) : "";
          const maxText = resp.ok && data.found ? formatAreaAverageValue(data.max, units, signed) : "";
          const isCrestStreamflow = String(param || "").toUpperCase() === "CREST";
          const validText = cleanValidTimeText(resp.ok ? data.file_time_utc : "");
          const meanLabel = data.mean_label || selectedAverageLabel();
          const compareMeanHtml = data.found
            ? (data.mean_mode === "matched"
                ? `<span style="font-size:12px;color:#cccccc;">Pure avg: ${pureMeanText}</span><br>`
                : `<span style="font-size:12px;color:#cccccc;">High-value weighted average: ${matchedMeanText}</span><br>`)
            : "";
          const html =
            `<div class="readout-shell">` +
            `<span class="readout-title">${info.shortLabel} area average</span><br>` +
            `${data.found ? makeThreatTrendHtml(param, data.mean) : ""}` +
            `${data.found ? makeAreaTrendSparklineHtml(data, units, signed) : ""}` +
            `<span style="font-size:12px;color:#ffd27a;font-weight:900;">${escapeHtml(meanLabel)}</span><br>` +
            `<span class="readout-main-value">${meanText}</span><br>` +
            `${compareMeanHtml}` +
            `${validText ? `<span class="readout-valid-time">Valid: ${validText}</span><br>` : ""}` +
            `${data.found ? makeStreamflowCoverageHtml(data, param, units) : ""}` +
            `${data.found && !isCrestStreamflow ? `<span style="font-size:13px;">Min/Max: ${minText} / ${maxText}</span><br>` : ""}` +
            `${data.found ? makeAreaEstimateHtml(data, units, signed) : ""}` +
            `</div>`;
          if (panel.areaAvgPopup) {
            panel.areaAvgPopup.setContent(html).openOn(panel.map);
            refreshReadoutPopupLayout(panel.areaAvgPopup);
          }
          drawAreaAverageShape(vertices, true);
        } catch (err) {
          if (err && err.name === "AbortError") return;
          if (controller.signal.aborted || clearSerialAtStart !== readoutClearSerial) return;
          if (serial !== areaAvgSerial) return;
          if (panel.areaAvgPopup) panel.areaAvgPopup.setContent(`<span class="readout-title">${info.shortLabel} area average</span><br>Average query failed.`).openOn(panel.map);
        } finally {
          completeOne();
        }
      });
    }

    function hoverValueFetchUrl(panelKey, lat, lon, token) {
      const param = selectedParam(panelKey);
      let url =
        `/api/value?param=${encodeURIComponent(param)}` +
        `&product=${encodeURIComponent(rawProductForParam(param))}` +
        `&lat=${lat}&lon=${lon}` +
        `&cacheBust=${Date.now()}`;
      if (token) {
        url += `&time=${encodeURIComponent(token)}`;
      }
      return url;
    }

    function handleHoverMove(panelKey, e) {
      if (areaAvgEnabled) return;
      const show = document.getElementById("showHoverReadout").checked;
      const panel = panels[panelKey];
      if (!show || !panel) return;

      const param = selectedParam(panelKey);
      const info = parameterInfo[param] || parameterInfo.CREST;
      const signed = !!info.isDifference;
      const token = selectedEffectiveTokenForParam(param);
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
        if (panel.clickReadoutAbortController) panel.clickReadoutAbortController.abort();
      } catch (e) {}
      panel.clickReadoutAbortController = null;
      try {
        if (panel.clickReadoutPopup) {
          panel.map.closePopup(panel.clickReadoutPopup);
          if (panel.map.hasLayer(panel.clickReadoutPopup)) panel.map.removeLayer(panel.clickReadoutPopup);
          if (typeof panel.clickReadoutPopup.remove === "function") panel.clickReadoutPopup.remove();
        }
      } catch (e) {}
      panel.clickReadoutPopup = null;
      try {
        panel.clickReadoutGroup.clearLayers();
        if (panel.map.hasLayer(panel.clickReadoutGroup)) {
          panel.map.removeLayer(panel.clickReadoutGroup);
        }
      } catch (e) {}
      try {
        panel.map.getContainer().querySelectorAll(".click-readout-popup").forEach(el => el.remove());
      } catch (e) {}
    }

    function clearAllClickReadouts(preserveState=false) {
      clickReadoutRequestKey = "";
      clickReadoutRequestActive = false;
      clickReadoutCompletedKey = "";
      if (!preserveState) activeClickReadout = null;
      forEachPanel(function (key) {
        clearPanelClickReadout(key);
      });
    }

    function clearAllReadouts() {
      readoutClearSerial += 1;
      clearTimeout(activeReadoutRefreshTimer);
      activeReadoutRefreshTimer = null;
      clearAllClickReadouts(false);
      clearAreaAverage();
      // Repeat cleanup briefly because Leaflet may finish an open/close DOM
      // operation after the button click. Stale async results are also blocked
      // by abort controllers, request serials, and readoutClearSerial.
      [0, 60, 180].forEach(function (delay) {
        setTimeout(function () {
          forEachPanel(function (key, panel) {
            clearPanelClickReadout(key);
            try {
              if (panel.areaAvgPopup) {
                panel.map.closePopup(panel.areaAvgPopup);
                if (panel.map.hasLayer(panel.areaAvgPopup)) panel.map.removeLayer(panel.areaAvgPopup);
                if (typeof panel.areaAvgPopup.remove === "function") panel.areaAvgPopup.remove();
              }
            } catch (e) {}
            panel.areaAvgPopup = null;
            try {
              panel.map.getContainer().querySelectorAll(".click-readout-popup, .area-avg-popup").forEach(el => el.remove());
            } catch (e) {}
          });
        }, delay);
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

    async function fetchClickedValueForPanel(panelKey, lat, lon, token, signal=null) {
      const param = selectedParam(panelKey);
      const product = rawProductForParam(param);
      const info = parameterInfo[param] || parameterInfo.CREST;
      const signed = !!info.isDifference;
      const panelLabel = PANEL_LABELS[panelKey] || panelKey.toUpperCase();
      token = selectedEffectiveTokenForParam(param) || token;

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
        // same compact trend graphic, tied to the selected/archive scan.
        url =
          `/api/value_trend?param=${encodeURIComponent(param)}` +
          `&product=${encodeURIComponent(product)}` +
          `&lat=${lat}&lon=${lon}` +
          `&samples=${readoutTrendSamples()}&step_minutes=10` +
          `&cacheBust=${Date.now()}`;

        if (token) {
          url += `&time=${encodeURIComponent(token)}`;
        }

        const resp = await fetch(url, signal ? {signal} : undefined);
        const data = await resp.json();
        const units = data.display_units || info.units || "";
        const valueHtml = resp.ok ? formatClickValueHtml(data, info, signed) : "Value error";
        const threatHtml = (resp.ok && signed) ? makeThreatTrendHtml(param, data.display_value ?? data.value_cfs_per_smi) : "";
        const trendHtml = resp.ok ? makeAreaTrendSparklineHtml(data, units, signed) : "";
        const validText = cleanValidTimeText(resp.ok ? data.file_time_utc : "");
        const validHtml = validText ? `<br><span class="readout-valid-time">Valid: ${validText}</span>` : "";

        return (
          `<div class="readout-shell">` +
          `<span class="readout-title">${panelLabel} — ${info.shortLabel}</span><br>` +
          `${threatHtml}` +
          `${trendHtml}` +
          `<span class="readout-main-value">${valueHtml}</span>` +
          `${validHtml}` +
          `</div>`
        );
      } catch (err) {
        if (err && err.name === "AbortError") throw err;
        return (
          `<b>${panelLabel} — ${info.shortLabel}</b><br><br>` +
          `Value query failed`
        );
      }
    }

    function showClickReadoutsAt(lat, lon, updateStoredLocation=true) {
      const token = selectedEffectiveToken();
      const latlng = [lat, lon];
      const keys = activePanelKeys();
      const requestKey = JSON.stringify({
        lat: Number(lat).toFixed(5),
        lon: Number(lon).toFixed(5),
        token: token || "latest",
        samples: readoutTrendSamples(),
        params: keys.map(key => selectedParam(key))
      });

      if (!updateStoredLocation && requestKey === clickReadoutRequestKey &&
          (clickReadoutRequestActive || clickReadoutCompletedKey === requestKey)) {
        return;
      }

      clickReadoutRequestKey = requestKey;
      clickReadoutRequestActive = true;
      const clearSerialAtStart = readoutClearSerial;

      if (updateStoredLocation) {
        activeClickReadout = { lat: Number(lat), lon: Number(lon), requestKey };
      }

      forEachPanel(function (key) {
        if (!keys.includes(key)) clearPanelClickReadout(key);
      });

      let pending = keys.length;
      const completeOne = function () {
        pending -= 1;
        if (pending <= 0 && clickReadoutRequestKey === requestKey) {
          clickReadoutRequestActive = false;
          clickReadoutCompletedKey = requestKey;
        }
      };

      for (const key of keys) {
        const panel = panels[key];
        if (!panel) {
          completeOne();
          continue;
        }

        clearPanelClickReadout(key);
        const info = selectedParamInfo(key);
        const thisClick = ++panel.clickReadoutSerial;
        const controller = new AbortController();
        panel.clickReadoutAbortController = controller;
        addClickReadoutPulse(key, latlng);

        const popup = L.popup({
          maxWidth: READOUT_POPUP_WIDTH,
          minWidth: READOUT_POPUP_WIDTH,
          className: "shared-readout-popup click-readout-popup",
          closeOnClick: false,
          autoClose: false
        })
          .setLatLng(latlng)
          .setContent(
            `<div class="readout-shell"><span class="readout-title">${PANEL_LABELS[key] || key.toUpperCase()} — ${info.shortLabel}</span><br>` +
            `Loading value...</div>`
          );

        panel.clickReadoutPopup = popup;
        popup.openOn(panel.map);
        refreshReadoutPopupLayout(popup);

        fetchClickedValueForPanel(key, lat, lon, token, controller.signal)
          .then(function (html) {
            if (controller.signal.aborted) return;
            if (clearSerialAtStart !== readoutClearSerial) return;
            if (thisClick !== panel.clickReadoutSerial || panel.clickReadoutPopup !== popup) return;
            popup.setContent(html);
            refreshReadoutPopupLayout(popup);
          })
          .catch(function (err) {
            if (err && err.name === "AbortError") return;
            if (controller.signal.aborted || clearSerialAtStart !== readoutClearSerial) return;
            if (thisClick !== panel.clickReadoutSerial || panel.clickReadoutPopup !== popup) return;
            popup.setContent(
              `<span class="readout-title">${PANEL_LABELS[key] || key.toUpperCase()} — ${info.shortLabel}</span><br>` +
              `Value query failed.`
            );
          })
          .finally(completeOne);
      }
    }

    async function handleMapClick(panelKey, e) {
      if (alarmAreaDrawEnabled) {
        handleAlarmAreaMapClick(panelKey, e);
        return;
      }
      if (areaAvgEnabled) {
        handleAreaAverageMapClick(panelKey, e);
        return;
      }
      if (areaAvgDrawing || alarmAreaDrawing) return;

      clearAllClickReadouts(false);
      showClickReadoutsAt(e.latlng.lat, e.latlng.lng, true);
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
  const baseToken = selectedEffectiveToken() || liveLatestToken || currentRoundedToken();
  if (!baseToken) throw new Error("No valid live or archive anchor time is selected.");

  const step = TIME_TREND_STEP_MINUTES * Math.max(1, skip);
  const picked = [];
  for (let i = frameCount - 1; i >= 0; i--) {
    picked.push(addMinutesToToken(baseToken, -i * step));
  }
  return picked;
}

    async function startLoop() {
      if (isGifExporting) {
        document.getElementById("status").textContent = "Animated GIF export is already in progress.";
        return;
      }
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

    document.getElementById("timeMode").addEventListener("change", function () {
      updateTimelineControls();
      refreshAllLayers(true);
    });

    document.addEventListener("keydown", function (e) {
      if (e.key === "Escape") {
        clearAllReadouts();
      }
    });

    function initializeViewer() {
      setSidebarCollapsed(savedSidebarCollapsed(), false);
      const fastRenderCheckbox = document.getElementById("fastRender");
      if (fastRenderCheckbox) fastRenderCheckbox.checked = savedFastRenderEnabled();
      const trendLengthEl = document.getElementById("readoutTrendLength");
      if (trendLengthEl) trendLengthEl.value = "30";
      const hoverEl = document.getElementById("showHoverReadout");
      if (hoverEl) hoverEl.checked = false;
      const areaEl = document.getElementById("enableAreaAvg");
      if (areaEl) areaEl.checked = false;
      const matchedMeanEl = document.getElementById("useMatchedMeanAverage");
      if (matchedMeanEl) {
        const savedMatched = window.localStorage.getItem("mrms.viewer.useMatchedMeanAverage");
        matchedMeanEl.checked = savedMatched === null ? true : savedMatched === "1";
      }
      const cwaBoundaryEl = document.getElementById("showCwaBoundaries");
      if (cwaBoundaryEl) cwaBoundaryEl.checked = savedCwaBoundariesEnabled();

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
      initializeArchivePicker();
      initializeAlarmControls();
      updateTimelineControls();
      updatePanelTitles();
      updateLiveIndicator();

      setTimeout(async function () {
        invalidateAllPanelSizes();
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

        const changed = new Set(liveChangedProducts || []);
        const anyChanged = changed.size > 0;
        if (anyChanged && !isLooping) {
          let refreshedAnyPanel = false;
          forEachActivePanel(function (key, panel) {
            const deps = liveSourceProductsForParam(selectedParam(key));
            if (deps.some(product => changed.has(product))) {
              panel.lastRenderKey = "";
              refreshPanelLayer(key, true);
              refreshedAnyPanel = true;
            }
          });
          if (refreshedAnyPanel) scheduleActiveReadoutRefresh();
        }

        const crestChanged = changed.has("CREST");
        scheduleCrestAlarmCheck(crestChanged ? 900 : 250, crestChanged);
      }
    }, 60 * 1000);
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


def requests_head(url, **kwargs):
    headers = kwargs.pop("headers", {})
    headers.setdefault("User-Agent", APP_USER_AGENT)
    return requests.head(url, headers=headers, **kwargs)


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

    try:
        # Keep the one-minute live freshness check lightweight. A slow/unreachable
        # live directory must not stall the viewer for 60 seconds.
        r = requests_get(
            directory,
            timeout=(REMOTE_LIST_CONNECT_TIMEOUT_SECONDS, REMOTE_LIST_READ_TIMEOUT_SECONDS),
        )
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
        if items:
            REMOTE_LIST_CACHE[product] = {
                "time": now,
                "items": items,
            }
            return items[:limit]

        # An empty directory parse is treated like a transient upstream failure
        # when we already have a known-good list.
        if cached and cached.get("items"):
            return cached["items"][:limit]
        return []

    except Exception:
        # Stale-if-error: preserve the most recently successful live listing.
        # This prevents temporary NCEP connection timeouts from producing noisy
        # Max-retries errors or knocking the viewer off its latest known scan.
        if cached and cached.get("items"):
            return cached["items"][:limit]
        raise



def _round_datetime_to_product_step(product, dt):
    product, info = product_info(product)
    step_minutes = max(1, int(info.get("step_minutes") or MRMS_TIME_STEP_MINUTES))
    dt = dt.astimezone(timezone.utc)
    total_minutes = dt.hour * 60 + dt.minute
    rounded_minutes = (total_minutes // step_minutes) * step_minutes
    rounded = dt.replace(
        hour=rounded_minutes // 60,
        minute=rounded_minutes % 60,
        second=0,
        microsecond=0,
    )
    return rounded


def _token_from_latest_headers(product, headers):
    """Infer the newest product time from `.latest` response headers.

    NCEP latest objects normally expose Last-Modified. Subtract a tiny
    publication-lag cushion before flooring to the product cadence so a file
    published just after a cadence boundary maps to the scan that produced it.
    """
    for key, value in (headers or {}).items():
        match = re.search(r"(\d{8}-\d{6})", str(value or ""))
        if match:
            return match.group(1), "header-token"

    last_modified = (headers or {}).get("Last-Modified") or (headers or {}).get("last-modified")
    if last_modified:
        try:
            dt = parsedate_to_datetime(last_modified)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            dt = dt.astimezone(timezone.utc) - timedelta(seconds=LIVE_PROBE_PUBLICATION_LAG_SECONDS)
            rounded = _round_datetime_to_product_step(product, dt)
            return rounded.strftime("%Y%m%d-%H%M%S"), "last-modified"
        except Exception:
            pass

    return None, None


def _latest_known_token_without_network(product):
    product, _ = product_info(product)

    cached = REMOTE_LIST_CACHE.get(product) or {}
    items = cached.get("items") or []
    if items:
        token = items[0].get("token")
        if token:
            return token, "remote-list-cache"

    local_items = list_local_archive(product)
    if local_items:
        token = local_items[0].get("token")
        if token:
            return token, "local-archive"

    return None, None


def probe_latest_product(product, force=False):
    """Lightweight, resilient latest-token probe for one MRMS product.

    This intentionally does not scrape the product directory. It HEADs the
    product's `.latest` object, retains last-known-good state on failure, and
    exponentially backs off repeated network misses.
    """
    product, info = product_info(product)
    now_epoch = time.time()

    with LIVE_PROBE_LOCK:
        cached = dict(LIVE_PROBE_CACHE.get(product) or {})

    if cached and not force:
        failure_count = int(cached.get("failure_count") or 0)

        if (
            failure_count == 0
            and cached.get("token")
            and now_epoch - float(cached.get("checked_epoch") or 0.0) < LIVE_PROBE_SUCCESS_TTL_SECONDS
        ):
            result = dict(cached)
            result.update({"product": product, "stale": False, "backoff_active": False})
            return result

        if failure_count > 0 and now_epoch < float(cached.get("next_probe_epoch") or 0.0):
            result = dict(cached)
            result.update({
                "product": product,
                "stale": True,
                "backoff_active": True,
                "next_probe_utc": datetime.fromtimestamp(
                    float(cached.get("next_probe_epoch")), tz=timezone.utc
                ).isoformat(timespec="seconds").replace("+00:00", "Z"),
            })
            return result

    headers = None
    status_code = None
    error_text = ""

    try:
        response = requests_head(
            info["latest_url"],
            timeout=(LIVE_PROBE_CONNECT_TIMEOUT_SECONDS, LIVE_PROBE_READ_TIMEOUT_SECONDS),
            allow_redirects=True,
        )
        status_code = response.status_code

        # Some upstream/proxy paths reject HEAD. A one-byte ranged GET retains
        # the lightweight behavior while still exposing object headers.
        if response.status_code in (400, 403, 405, 501):
            response.close()
            response = requests_get(
                info["latest_url"],
                headers={"Range": "bytes=0-0"},
                timeout=(LIVE_PROBE_CONNECT_TIMEOUT_SECONDS, LIVE_PROBE_READ_TIMEOUT_SECONDS),
                allow_redirects=True,
                stream=True,
            )
            status_code = response.status_code

        response.raise_for_status()
        headers = dict(response.headers)
        response.close()

        token, token_source = _token_from_latest_headers(product, headers)
        signature = "|".join([
            str(headers.get("ETag") or headers.get("Etag") or ""),
            str(headers.get("Last-Modified") or ""),
            str(headers.get("Content-Length") or ""),
        ])

        if not token and cached.get("token"):
            token = cached.get("token")
            token_source = "last-known-good"
        elif not token:
            token, fallback_source = _latest_known_token_without_network(product)
            token_source = fallback_source or "unknown"

        result = {
            "product": product,
            "token": token,
            "label": token_to_label(token) if token else "Latest token unavailable",
            "source": "ncep-latest-head",
            "token_source": token_source,
            "signature": signature,
            "etag": headers.get("ETag") or headers.get("Etag") or "",
            "last_modified": headers.get("Last-Modified") or "",
            "status_code": status_code,
            "checked_epoch": now_epoch,
            "checked_utc": now_utc_iso(),
            "next_probe_epoch": now_epoch + LIVE_PROBE_SUCCESS_TTL_SECONDS,
            "failure_count": 0,
            "stale": False,
            "backoff_active": False,
            "last_error": "",
        }

        with LIVE_PROBE_LOCK:
            LIVE_PROBE_CACHE[product] = dict(result)
        return result

    except Exception as exc:
        error_text = f"{type(exc).__name__}: {exc}"
        failure_count = int(cached.get("failure_count") or 0) + 1
        backoff_seconds = min(
            LIVE_PROBE_BACKOFF_MAX_SECONDS,
            LIVE_PROBE_BACKOFF_BASE_SECONDS * (2 ** max(0, failure_count - 1)),
        )

        token = cached.get("token")
        fallback_source = "last-known-good"
        if not token:
            token, fallback_source = _latest_known_token_without_network(product)

        result = dict(cached)
        result.update({
            "product": product,
            "token": token,
            "label": token_to_label(token) if token else "Latest token unavailable",
            "source": cached.get("source") or fallback_source or "unavailable",
            "token_source": cached.get("token_source") or fallback_source or "unavailable",
            "checked_epoch": now_epoch,
            "checked_utc": now_utc_iso(),
            "next_probe_epoch": now_epoch + backoff_seconds,
            "failure_count": failure_count,
            "stale": True,
            "backoff_active": True,
            "last_error": error_text,
            "retry_in_seconds": backoff_seconds,
            "next_probe_utc": datetime.fromtimestamp(
                now_epoch + backoff_seconds, tz=timezone.utc
            ).isoformat(timespec="seconds").replace("+00:00", "Z"),
        })

        with LIVE_PROBE_LOCK:
            LIVE_PROBE_CACHE[product] = dict(result)
        return result


def _normalize_s3_prefix_name(value):
    return re.sub(r"[^a-z0-9]", "", str(value or "").lower())


def list_s3_conus_product_prefixes():
    global S3_PREFIX_CACHE, S3_PREFIX_CACHE_TIME
    now = time.time()
    if S3_PREFIX_CACHE is not None and now - S3_PREFIX_CACHE_TIME < S3_PREFIX_CACHE_TTL_SECONDS:
        return list(S3_PREFIX_CACHE)

    r = requests_get(
        MRMS_S3_BASE_URL,
        params={"list-type": "2", "prefix": "CONUS/", "delimiter": "/"},
        timeout=60,
    )
    r.raise_for_status()
    root = ET.fromstring(r.content)
    prefixes = []
    for elem in root.findall(".//{*}CommonPrefixes/{*}Prefix"):
        text = (elem.text or "").strip()
        if text.startswith("CONUS/"):
            prefixes.append(text[len("CONUS/"):].strip("/"))

    S3_PREFIX_CACHE = sorted(set(prefixes))
    S3_PREFIX_CACHE_TIME = now
    return list(S3_PREFIX_CACHE)


def resolved_s3_prefix_candidates(product):
    product, info = product_info(product)
    candidates = list(S3_PRODUCT_PREFIX_CANDIDATES.get(product, []))

    try:
        available = list_s3_conus_product_prefixes()
        target_names = list(candidates)
        file_stem = info.get("file_prefix", "").replace("MRMS_", "").rstrip("_")
        if file_stem:
            target_names.append(file_stem)

        normalized_targets = [_normalize_s3_prefix_name(x) for x in target_names if x]
        for prefix in available:
            norm = _normalize_s3_prefix_name(prefix)
            if any(norm == target or norm.endswith(target) or target.endswith(norm) for target in normalized_targets):
                candidates.append(prefix)
    except Exception as e:
        print(f"[{product} S3 prefix discovery fallback] {e}")

    seen = set()
    output = []
    for item in candidates:
        if item and item not in seen:
            seen.add(item)
            output.append(item)
    return output


def list_s3_archive_files(product, day_yyyymmdd):
    product, _ = product_info(product)
    cache_key = (product, str(day_yyyymmdd))
    now = time.time()
    cached = S3_ARCHIVE_LIST_CACHE.get(cache_key)
    if cached and now - cached["time"] < S3_ARCHIVE_LIST_TTL_SECONDS:
        return list(cached["items"])

    all_items = []
    for product_prefix in resolved_s3_prefix_candidates(product):
        prefix = f"CONUS/{product_prefix}/{day_yyyymmdd}/"
        try:
            r = requests_get(
                MRMS_S3_BASE_URL,
                params={"list-type": "2", "prefix": prefix},
                timeout=60,
            )
            r.raise_for_status()
            root = ET.fromstring(r.content)
        except Exception as e:
            print(f"[{product} S3 day list skipped] {prefix}: {e}")
            continue

        for elem in root.findall(".//{*}Contents/{*}Key"):
            key = (elem.text or "").strip()
            if not key.endswith(".grib2.gz"):
                continue
            token = parse_mrms_token(os.path.basename(key))
            if not token:
                continue
            all_items.append({
                "product": product,
                "token": token,
                "filename": os.path.basename(key),
                "url": f"{MRMS_S3_BASE_URL}/{key}",
                "label": f"{token_to_label(token)} - NOAA AWS archive",
                "source": "aws_s3_archive",
                "s3_key": key,
            })

        if all_items:
            break

    all_items.sort(key=lambda x: x["token"], reverse=True)
    S3_ARCHIVE_LIST_CACHE[cache_key] = {"time": now, "items": all_items}
    return list(all_items)


def requested_time_tolerance_seconds(product):
    product, info = product_info(product)
    step_minutes = max(1, int(info.get("step_minutes") or MRMS_TIME_STEP_MINUTES))
    return float(max(150, min(40 * 60, step_minutes * 60 * 0.70 + 60)))


def nearest_s3_archive_item(product, requested_token):
    product, _ = product_info(product)
    requested_dt = token_to_datetime(requested_token)
    dates = [
        (requested_dt - timedelta(days=1)).strftime("%Y%m%d"),
        requested_dt.strftime("%Y%m%d"),
        (requested_dt + timedelta(days=1)).strftime("%Y%m%d"),
    ]

    best_item = None
    best_delta = None
    for day in dates:
        for item in list_s3_archive_files(product, day):
            delta = abs((token_to_datetime(item["token"]) - requested_dt).total_seconds())
            if best_delta is None or delta < best_delta:
                best_delta = delta
                best_item = item

    return best_item, best_delta


def nearest_requested_archive_item(product, requested_token, tolerance_seconds=None):
    product, _ = product_info(product)
    tolerance_seconds = float(tolerance_seconds if tolerance_seconds is not None else requested_time_tolerance_seconds(product))
    candidates = []

    requested_dt = token_to_datetime(requested_token)
    age_hours = (now_utc() - requested_dt).total_seconds() / 3600.0
    historical_request = age_hours > HISTORICAL_REMOTE_DIRECTORY_MAX_AGE_HOURS

    def try_current_directory():
        try:
            item, delta = nearest_remote_item(product, requested_token, limit=2500)
            if item is not None and delta is not None:
                candidates.append((item, float(delta)))
                return True
        except Exception:
            # The live NCEP directory is optional here; NOAA AWS remains the
            # archive source of truth for historical requests.
            pass
        return False

    def try_aws_archive():
        try:
            item, delta = nearest_s3_archive_item(product, requested_token)
            if item is not None and delta is not None:
                candidates.append((item, float(delta)))
                return True
        except Exception as e:
            print(f"[{product} AWS archive lookup skipped] {e}")
        return False

    if historical_request:
        # Old archive frames should not touch the live current-directory page.
        # Go straight to the day-partitioned NOAA AWS archive, and only try the
        # live directory as a last-resort fallback if AWS produced no candidate.
        found_aws = try_aws_archive()
        if not found_aws:
            try_current_directory()
    else:
        # Near-live requests prefer the current directory for freshest data,
        # with AWS as an immediate fallback when NCEP is slow or unavailable.
        try_current_directory()
        try_aws_archive()

    if not candidates:
        return None, None

    item, delta = min(candidates, key=lambda pair: pair[1])
    if delta > tolerance_seconds:
        return None, delta
    return annotate_snapped_item(item, requested_token, delta), delta


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



def token_from_grib_metadata(grib_path):
    """Best-effort extraction of the actual valid time embedded in a GRIB2 file."""
    try:
        with rasterio.open(grib_path) as src:
            tags = {}
            try:
                tags.update(src.tags())
            except Exception:
                pass
            try:
                tags.update(src.tags(1))
            except Exception:
                pass
    except Exception:
        return None

    priority_keys = [
        "GRIB_VALID_TIME",
        "VALID_TIME",
        "valid_time",
        "GRIB_REF_TIME",
        "REF_TIME",
        "reference_time",
    ]

    def parse_value(value):
        text = str(value or "").strip()
        if not text:
            return None

        # Common GDAL GRIB metadata form: "1783105800 sec UTC".
        for match in re.finditer(r"(?<!\d)(\d{9,12})(?!\d)", text):
            try:
                epoch = int(match.group(1))
                if 946684800 <= epoch <= 4102444800:  # 2000-01-01 through 2100-01-01
                    return datetime.fromtimestamp(epoch, tz=timezone.utc).strftime("%Y%m%d-%H%M%S")
            except Exception:
                pass

        match = re.search(r"(20\d{6})[-_ T]?(\d{2})(\d{2})(\d{2})", text)
        if match:
            return f"{match.group(1)}-{match.group(2)}{match.group(3)}{match.group(4)}"

        match = re.search(r"(20\d{2})-(\d{2})-(\d{2})[ T](\d{2}):(\d{2})(?::(\d{2}))?", text)
        if match:
            return f"{match.group(1)}{match.group(2)}{match.group(3)}-{match.group(4)}{match.group(5)}{match.group(6) or '00'}"
        return None

    for key in priority_keys:
        if key in tags:
            token = parse_value(tags.get(key))
            if token:
                return token

    for key, value in tags.items():
        if "TIME" not in str(key).upper():
            continue
        token = parse_value(value)
        if token:
            return token

    return None


def get_latest_grib_direct(product, force=False):
    """Return the actual current `.latest` MRMS object without archive resolution.

    A lightweight HEAD probe supplies change detection. The full GRIB is only
    downloaded when its signature/token changes. On a transient network failure,
    the last successfully downloaded latest object is retained as stale fallback.
    """
    product, info = product_info(product)
    latest_url = info["latest_url"]
    gz_path, grib_path, meta_path = cache_paths_for_url(product, latest_url)
    lock = keyed_lock(DOWNLOAD_LOCKS, grib_path)

    probe = probe_latest_product(product, force=force)
    probe_token = probe.get("token")
    probe_signature = str(probe.get("signature") or "").strip()

    with lock:
        cached_meta = read_json(meta_path)
        if os.path.exists(grib_path) and not force:
            cached_signature = str(cached_meta.get("latest_signature") or "").strip()
            cached_token = cached_meta.get("token")

            if probe_signature and cached_signature and probe_signature == cached_signature:
                return grib_path, cached_meta
            if probe_token and cached_token and probe_token == cached_token:
                return grib_path, cached_meta
            if probe.get("stale") and cached_token:
                stale_meta = dict(cached_meta)
                stale_meta["stale"] = True
                stale_meta["probe_last_error"] = probe.get("last_error", "")
                stale_meta["source"] = stale_meta.get("source") or "ncep_latest_cached"
                return grib_path, stale_meta

        tmp_gz = f"{gz_path}.latest.tmp"
        tmp_grib = f"{grib_path}.latest.tmp"
        try:
            response = requests_get(
                latest_url,
                timeout=(
                    LIVE_LATEST_DOWNLOAD_CONNECT_TIMEOUT_SECONDS,
                    LIVE_LATEST_DOWNLOAD_READ_TIMEOUT_SECONDS,
                ),
                stream=True,
            )
            response.raise_for_status()

            with open(tmp_gz, "wb") as f:
                for chunk in response.iter_content(chunk_size=1024 * 1024):
                    if chunk:
                        f.write(chunk)

            with gzip.open(tmp_gz, "rb") as src, open(tmp_grib, "wb") as dst:
                shutil.copyfileobj(src, dst, length=1024 * 1024)

            actual_token = token_from_grib_metadata(tmp_grib) or probe_token
            response_signature = "|".join([
                str(response.headers.get("ETag") or response.headers.get("Etag") or ""),
                str(response.headers.get("Last-Modified") or ""),
                str(response.headers.get("Content-Length") or ""),
            ])
            latest_signature = response_signature or probe_signature

            os.replace(tmp_gz, gz_path)
            os.replace(tmp_grib, grib_path)

            meta = {
                "product": product,
                "url": latest_url,
                "token": actual_token,
                "label": token_to_label(actual_token) if actual_token else "Latest/current Z",
                "downloaded_utc": now_utc_iso(),
                "last_modified": response.headers.get("Last-Modified", ""),
                "content_length": response.headers.get("Content-Length", ""),
                "etag": response.headers.get("ETag") or response.headers.get("Etag") or "",
                "latest_signature": latest_signature,
                "source": "ncep_latest_direct",
                "stale": False,
                "probe_token": probe_token,
                "probe_token_source": probe.get("token_source"),
            }
            write_json(meta_path, meta)
            response.close()
            return grib_path, meta

        except Exception as exc:
            for tmp in (tmp_gz, tmp_grib):
                try:
                    if os.path.exists(tmp):
                        os.remove(tmp)
                except Exception:
                    pass

            if os.path.exists(grib_path):
                stale_meta = dict(cached_meta or {})
                stale_meta.update({
                    "product": product,
                    "url": latest_url,
                    "source": stale_meta.get("source") or "ncep_latest_cached",
                    "stale": True,
                    "latest_download_error": f"{type(exc).__name__}: {exc}",
                })
                return grib_path, stale_meta
            raise


def get_grib_for_product_time(product, requested_token=None):
    product, _ = product_info(product)

    if requested_token:
        local_grib, local_meta = archive_paths(product, requested_token)
        if os.path.exists(local_grib):
            meta = read_json(local_meta)
            meta["source"] = "local_archive"
            return local_grib, meta

        item, delta = nearest_requested_archive_item(product, requested_token)
        if not item:
            raise FileNotFoundError(
                f"No {product} file was found near {token_to_label(requested_token)} in the live directory, local archive, or NOAA AWS MRMS archive."
            )
    else:
        # LIVE/current requests must read the actual `.latest` object directly.
        # Do not convert a probe timestamp into a historical nearest-file lookup.
        return get_latest_grib_direct(product, force=False)

    grib_path, meta = download_and_unzip_url(product, item["url"])
    source_name = item.get("source") or ("remote_ncep" if not requested_token else "remote_ncep")
    meta.update({
        "token": item.get("token"),
        "label": item.get("label"),
        "source": source_name,
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

    if not requested_token:
        return get_grib_for_product_time(product, requested_token=None)

    local_grib, local_meta = archive_paths(product, requested_token)
    if os.path.exists(local_grib):
        meta = read_json(local_meta)
        meta["source"] = "local_archive"
        return local_grib, meta

    item, delta = nearest_requested_archive_item(product, requested_token, tolerance_seconds=tolerance_seconds)
    if not item:
        raise FileNotFoundError(
            f"No {product} file was found within {int(tolerance_seconds)} seconds of {token_to_label(requested_token)}."
        )

    grib_path, meta = download_and_unzip_url(product, item["url"])
    meta.update({
        "token": item.get("token"),
        "label": item.get("label"),
        "source": item.get("source") or "remote_ncep",
        "requested_token": item.get("requested_token", requested_token),
        "snapped_from_requested": bool(item.get("snapped_from_requested", False)),
        "delta_seconds_from_requested": item.get("delta_seconds_from_requested"),
        "outside_strict_tolerance": False,
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

    if requested_token:
        archive_days = sorted({dt.strftime("%Y%m%d") for _, dt in target_dts})
        for archive_day in archive_days:
            try:
                remote_items.extend(list_s3_archive_files(product, archive_day))
            except Exception as e:
                print(f"[{product} trailing-window AWS list skipped] {archive_day}: {e}")

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
            "source": item.get("source") or "remote_ncep",
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


def streamflow_color_hex(value_cfs):
    try:
        value = float(value_cfs)
    except Exception:
        value = 0.0
    rgba = STREAMFLOW_CMAP(STREAMFLOW_NORM([value]))[0]
    r, g, b = [int(max(0, min(255, round(float(x) * 255.0)))) for x in rgba[:3]]
    return f"#{r:02x}{g:02x}{b:02x}"


def compute_p_from_crest_and_diff(C, dC):
    """Compute P using the exact adjusted exponential relationship from CMUSF_Auto.py.

    C and dC are in the viewer's CREST display units (cfs/mi^2).
    The source formulation blends a low-CREST and high-CREST exponential
    response using frac=clip(C/200, 0, 1). Final clipping to 0-5000 is
    applied by callers exactly as in the source script.
    """
    a0, P0_max, a1, P1_max, dC_max = 0.001, 1500.0, 0.007, 5000.0, 250.0
    C_arr = np.asarray(C, dtype=np.float64)
    dC_arr = np.asarray(dC, dtype=np.float64)
    frac = np.clip(C_arr / 200.0, 0.0, 1.0)
    P0 = P0_max * (np.exp(a0 * dC_arr) - 1.0) / (np.exp(a0 * dC_max) - 1.0)
    P1 = P1_max * (np.exp(a1 * dC_arr) - 1.0) / (np.exp(a1 * dC_max) - 1.0)
    return (1.0 - frac) * P0 + frac * P1


def colorize_computed_p(arr_p):
    arr = arr_p.astype(np.float32).copy()
    arr[arr < 0] = np.nan
    rgba = COMPUTED_P_CMAP(COMPUTED_P_NORM(arr))
    rgba[..., 3] = 0.92
    rgba = apply_zero_transparency(rgba, arr, signed=False)
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def colorize_difference_cfs(diff_cfs):
    # Existing generic ±200 difference palette retained for non-rate-change fields.
    arr = diff_cfs.copy()
    rgba = DIFF_CMAP(DIFF_NORM(arr))
    rgba[..., 3] = 0.88
    rgba = apply_zero_transparency(rgba, arr, signed=True)
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def colorize_crest_rate_change(diff_cfs):
    arr = diff_cfs.astype(np.float32).copy()
    rgba = RATE_CHANGE_CMAP(CREST_RATE_CHANGE_NORM(arr))
    rgba[..., 3] = 0.90
    rgba = apply_zero_transparency(rgba, arr, signed=True)
    return np.clip(rgba * 255, 0, 255).astype(np.uint8)


def colorize_rainrate_difference(diff_inhr):
    arr = diff_inhr.astype(np.float32).copy()
    rgba = RATE_CHANGE_CMAP(RAINRATE_DIFF_NORM(arr))
    rgba[..., 3] = 0.90
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
    rgba = RATE_CHANGE_CMAP(MRMS_QPE_DIFF_NORM(arr))
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


    if pinfo.get("difference_minutes"):
        raw_product = pinfo.get("product") or product
        minutes = int(pinfo["difference_minutes"])
        tolerance = int(pinfo.get("difference_tolerance_seconds", 8 * 60))
        curr_path, curr_meta = get_grib_for_product_time(raw_product, requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError(f"Could not determine the current {raw_product} token for {pinfo['display']}.")
        prev_token = token_add_minutes(current_token, -minutes)
        prev_path, prev_meta = get_grib_for_product_time_strict(raw_product, prev_token, tolerance_seconds=tolerance)
        return {
            "param": param, "product": raw_product, "kind": "difference",
            "display": pinfo["display"], "units": pinfo.get("units", ""),
            "native_units": pinfo.get("native_units", ""), "style": pinfo.get("style", "difference"),
            "grib_paths": [curr_path, prev_path], "metas": [curr_meta, prev_meta],
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {
                "current": file_time_from_meta(curr_meta), "previous": file_time_from_meta(prev_meta),
                "difference_minutes": minutes, "previous_token": prev_token,
            },
        }

    if param == "QPE30M_DIFF_30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE15M", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current QPE15M token for the 30-minute QPE change.")
        tokens = [token_add_minutes(current_token, -m) for m in (15, 30, 45)]
        p15, m15 = get_grib_for_product_time_strict("QPE15M", tokens[0], tolerance_seconds=8 * 60)
        p30, m30 = get_grib_for_product_time_strict("QPE15M", tokens[1], tolerance_seconds=8 * 60)
        p45, m45 = get_grib_for_product_time_strict("QPE15M", tokens[2], tolerance_seconds=8 * 60)
        return {
            "param": param, "product": "QPE15M", "kind": "difference",
            "display": pinfo["display"], "units": pinfo.get("units", "in"),
            "native_units": pinfo.get("native_units", "mm"), "style": "qpe_difference",
            "grib_paths": [curr_path, p15, p30, p45], "metas": [curr_meta, m15, m30, m45],
            "file_time_utc": f"30m ending {file_time_from_meta(curr_meta)} minus 30m ending {file_time_from_meta(m30)}",
            "component_times": {
                "current_30m": [file_time_from_meta(m15), file_time_from_meta(curr_meta)],
                "previous_30m": [file_time_from_meta(m45), file_time_from_meta(m30)],
            },
        }

    if param == "COMPUTED_P":
        curr_path, curr_meta = get_grib_for_product_time("CREST", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current CREST token for Computed P.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("CREST", prev_token, tolerance_seconds=6 * 60)
        return {
            "param": param,
            "product": "CREST",
            "kind": "computed",
            "display": pinfo["display"],
            "units": pinfo.get("units", "P"),
            "native_units": pinfo.get("native_units", "P"),
            "style": pinfo.get("style", "computed_p"),
            "grib_paths": [curr_path, prev_path],
            "metas": [curr_meta, prev_meta],
            "file_time_utc": file_time_from_meta(curr_meta),
            "component_times": {
                "current_crest": file_time_from_meta(curr_meta),
                "previous_crest_10m": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
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
            "units": pinfo.get("units", "cfs/mi^2"),
            "native_units": pinfo.get("native_units", "m^3/s/km^2"),
            "style": pinfo.get("style", "crest_rate_change"),
            "grib_paths": [curr_path, prev_path],
            "metas": [curr_meta, prev_meta],
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {
                "current_crest": file_time_from_meta(curr_meta),
                "previous_crest": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
        }

    if param == "RAINRATE_DIFF_10M":
        curr_path, curr_meta = get_grib_for_product_time("PRECIPRATE", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current PrecipRate token for the 10-minute difference.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("PRECIPRATE", prev_token, tolerance_seconds=3 * 60)
        return {
            "param": param,
            "product": "PRECIPRATE",
            "kind": "difference",
            "display": pinfo["display"],
            "units": pinfo.get("units", "in/hr"),
            "native_units": pinfo.get("native_units", "mm/hr"),
            "style": pinfo.get("style", "rainrate_difference"),
            "grib_paths": [curr_path, prev_path],
            "metas": [curr_meta, prev_meta],
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {
                "current_preciprate": file_time_from_meta(curr_meta),
                "previous_preciprate_10m": file_time_from_meta(prev_meta),
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
            "resolved_token": meta.get("token") or requested_token,
            "file_time_utc": file_time_from_meta(meta),
            "component_times": {raw_product: file_time_from_meta(meta)},
        }


    if pinfo.get("difference_minutes"):
        raw_product = pinfo.get("product") or product
        minutes = int(pinfo["difference_minutes"])
        tolerance = int(pinfo.get("difference_tolerance_seconds", 8 * 60))
        curr_path, curr_meta = get_grib_for_product_time(raw_product, requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError(f"Could not determine the current {raw_product} token for {pinfo['display']}.")
        prev_token = token_add_minutes(current_token, -minutes)
        prev_path, prev_meta = get_grib_for_product_time_strict(raw_product, prev_token, tolerance_seconds=tolerance)
        curr = read_grib_to_webmercator_grid(curr_path, west, south, east, north, width, height, dst_transform)
        prev = read_grib_to_webmercator_grid(prev_path, west, south, east, north, width, height, dst_transform)
        diff_raw = curr - prev
        if pinfo.get("style") == "crest_rate_change":
            diff_display = diff_raw * M3S_PER_KM2_TO_CFS_PER_SQMI
        elif pinfo.get("style") == "qpe_difference":
            diff_display = diff_raw * MM_TO_IN
        else:
            diff_display = diff_raw
        return {
            "param": param, "product": raw_product, "kind": "difference",
            "display": pinfo["display"], "units": pinfo.get("units", ""),
            "native_units": pinfo.get("native_units", ""), "style": pinfo.get("style", "difference"),
            "arr_cfs": diff_display, "arr_m3s_per_km2": diff_raw,
            "width": width, "height": height, "dst_transform": dst_transform, "merc_bounds": merc_bounds,
            "grib_paths": [curr_path, prev_path], "meta": curr_meta,
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {"current": file_time_from_meta(curr_meta), "previous": file_time_from_meta(prev_meta), "difference_minutes": minutes},
        }

    if param == "QPE30M_DIFF_30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE15M", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current QPE15M token for the 30-minute QPE change.")
        tokens = [token_add_minutes(current_token, -m) for m in (15, 30, 45)]
        p15, m15 = get_grib_for_product_time_strict("QPE15M", tokens[0], tolerance_seconds=8 * 60)
        p30, m30 = get_grib_for_product_time_strict("QPE15M", tokens[1], tolerance_seconds=8 * 60)
        p45, m45 = get_grib_for_product_time_strict("QPE15M", tokens[2], tolerance_seconds=8 * 60)
        frames = [read_grib_to_webmercator_grid(path, west, south, east, north, width, height, dst_transform)
                  for path in (curr_path, p15, p30, p45)]
        diff_raw = (frames[0] + frames[1]) - (frames[2] + frames[3])
        diff_in = diff_raw * MM_TO_IN
        return {
            "param": param, "product": "QPE15M", "kind": "difference",
            "display": pinfo["display"], "units": "in", "native_units": "mm", "style": "qpe_difference",
            "arr_cfs": diff_in, "arr_m3s_per_km2": diff_raw,
            "width": width, "height": height, "dst_transform": dst_transform, "merc_bounds": merc_bounds,
            "grib_paths": [curr_path, p15, p30, p45], "meta": curr_meta,
            "file_time_utc": f"30m ending {file_time_from_meta(curr_meta)} minus 30m ending {file_time_from_meta(m30)}",
            "component_times": {"current_30m": [file_time_from_meta(m15), file_time_from_meta(curr_meta)], "previous_30m": [file_time_from_meta(m45), file_time_from_meta(m30)]},
        }

    if param == "COMPUTED_P":
        curr_path, curr_meta = get_grib_for_product_time("CREST", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current CREST token for Computed P.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("CREST", prev_token, tolerance_seconds=6 * 60)

        curr_raw = read_grib_to_webmercator_grid(curr_path, west, south, east, north, width, height, dst_transform)
        prev_raw = read_grib_to_webmercator_grid(prev_path, west, south, east, north, width, height, dst_transform)

        # Match CMUSF_Auto.py exactly: convert native CREST with 91.8, clip
        # current and prior C to 0-2000, then compute the 10-minute dC.
        C = np.clip(curr_raw * COMPUTED_P_CREST_CONVERSION, 0.0, 2000.0)
        C0 = np.clip(prev_raw * COMPUTED_P_CREST_CONVERSION, 0.0, 2000.0)
        dC = C - C0
        P_raw = compute_p_from_crest_and_diff(C, dC)
        P = np.clip(P_raw, 0.0, COMPUTED_P_MAX).astype(np.float32)

        return {
            "param": param,
            "product": "CREST",
            "kind": "computed",
            "display": pinfo["display"],
            "units": pinfo.get("units", "P"),
            "native_units": pinfo.get("native_units", "P"),
            "style": pinfo.get("style", "computed_p"),
            "arr_cfs": P,
            "arr_m3s_per_km2": P,
            "width": width,
            "height": height,
            "dst_transform": dst_transform,
            "merc_bounds": merc_bounds,
            "grib_paths": [curr_path, prev_path],
            "meta": curr_meta,
            "resolved_token": current_token,
            "file_time_utc": file_time_from_meta(curr_meta),
            "component_times": {
                "current_crest": file_time_from_meta(curr_meta),
                "previous_crest_10m": file_time_from_meta(prev_meta),
                "previous_token": prev_token,
            },
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
            "native_units": pinfo.get("native_units", "m^3/s/km^2"),
            "style": pinfo.get("style", "crest_rate_change"),
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

    if param == "RAINRATE_DIFF_10M":
        curr_path, curr_meta = get_grib_for_product_time("PRECIPRATE", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current PrecipRate token for the 10-minute difference.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("PRECIPRATE", prev_token, tolerance_seconds=3 * 60)

        curr = read_grib_to_webmercator_grid(curr_path, west, south, east, north, width, height, dst_transform)
        prev = read_grib_to_webmercator_grid(prev_path, west, south, east, north, width, height, dst_transform)
        diff_raw = curr - prev
        diff_inhr = diff_raw * MM_TO_IN

        return {
            "param": param,
            "product": "PRECIPRATE",
            "kind": "difference",
            "display": pinfo["display"],
            "units": pinfo.get("units", "in/hr"),
            "native_units": pinfo.get("native_units", "mm/hr"),
            "style": pinfo.get("style", "rainrate_difference"),
            "arr_cfs": diff_inhr,
            "arr_m3s_per_km2": diff_raw,
            "width": width,
            "height": height,
            "dst_transform": dst_transform,
            "merc_bounds": merc_bounds,
            "grib_paths": [curr_path, prev_path],
            "meta": curr_meta,
            "resolved_token": current_token,
            "file_time_utc": f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}",
            "component_times": {
                "current_preciprate": file_time_from_meta(curr_meta),
                "previous_preciprate_10m": file_time_from_meta(prev_meta),
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

        if data.get("style") == "computed_p":
            rgba_u8 = colorize_computed_p(arr_cfs)
        elif data.get("style") == "qpe_difference":
            rgba_u8 = colorize_mrms_qpe_difference(arr_cfs)
        elif data.get("style") == "crest_rate_change":
            rgba_u8 = colorize_crest_rate_change(arr_cfs)
        elif data.get("style") == "rainrate_difference":
            rgba_u8 = colorize_rainrate_difference(arr_cfs)
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


    if pinfo.get("difference_minutes"):
        raw_product = pinfo.get("product") or product
        minutes = int(pinfo["difference_minutes"])
        tolerance = int(pinfo.get("difference_tolerance_seconds", 8 * 60))
        curr_path, curr_meta = get_grib_for_product_time(raw_product, requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError(f"Could not determine the current {raw_product} token for {pinfo['display']}.")
        prev_token = token_add_minutes(current_token, -minutes)
        prev_path, prev_meta = get_grib_for_product_time_strict(raw_product, prev_token, tolerance_seconds=tolerance)
        curr_val = sample_native_value(curr_path, lat, lon)
        prev_val = sample_native_value(prev_path, lat, lon)
        if curr_val is None or prev_val is None:
            return None, f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}"
        diff_raw = curr_val - prev_val
        if pinfo.get("style") == "crest_rate_change":
            display_value = diff_raw * M3S_PER_KM2_TO_CFS_PER_SQMI
        elif pinfo.get("style") == "qpe_difference":
            display_value = diff_raw * MM_TO_IN
        else:
            display_value = diff_raw
        return {
            "value_m3s_per_km2": diff_raw, "value_cfs_per_smi": display_value,
            "display_value": display_value, "display_units": pinfo.get("units", ""),
            "native_value": diff_raw, "native_units": pinfo.get("native_units", ""),
        }, f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}"

    if param == "QPE30M_DIFF_30M":
        curr_path, curr_meta = get_grib_for_product_time("QPE15M", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine the current QPE15M token for the 30-minute QPE change.")
        tokens = [token_add_minutes(current_token, -m) for m in (15, 30, 45)]
        p15, m15 = get_grib_for_product_time_strict("QPE15M", tokens[0], tolerance_seconds=8 * 60)
        p30, m30 = get_grib_for_product_time_strict("QPE15M", tokens[1], tolerance_seconds=8 * 60)
        p45, m45 = get_grib_for_product_time_strict("QPE15M", tokens[2], tolerance_seconds=8 * 60)
        vals = [sample_native_value(path, lat, lon) for path in (curr_path, p15, p30, p45)]
        if any(v is None for v in vals):
            return None, f"30m ending {file_time_from_meta(curr_meta)} minus 30m ending {file_time_from_meta(m30)}"
        diff_mm = (vals[0] + vals[1]) - (vals[2] + vals[3])
        diff_in = diff_mm * MM_TO_IN
        return {
            "value_m3s_per_km2": diff_mm, "value_cfs_per_smi": diff_in,
            "display_value": diff_in, "display_units": "in",
            "native_value": diff_mm, "native_units": "mm",
        }, f"30m ending {file_time_from_meta(curr_meta)} minus 30m ending {file_time_from_meta(m30)}"

    if param == "COMPUTED_P":
        curr_path, curr_meta = get_grib_for_product_time("CREST", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine current CREST token for Computed P.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("CREST", prev_token, tolerance_seconds=6 * 60)
        curr_val = sample_native_value(curr_path, lat, lon)
        prev_val = sample_native_value(prev_path, lat, lon)

        if curr_val is None or prev_val is None:
            return None, file_time_from_meta(curr_meta)

        C = float(np.clip(curr_val * COMPUTED_P_CREST_CONVERSION, 0.0, 2000.0))
        C0 = float(np.clip(prev_val * COMPUTED_P_CREST_CONVERSION, 0.0, 2000.0))
        dC = C - C0
        p_value = float(np.clip(compute_p_from_crest_and_diff(C, dC), 0.0, COMPUTED_P_MAX))
        return {
            "value_m3s_per_km2": p_value,
            "value_cfs_per_smi": p_value,
            "display_value": p_value,
            "display_units": pinfo.get("units", "P"),
            "native_value": p_value,
            "native_units": pinfo.get("native_units", "P"),
            "crest_cfs_per_smi": C,
            "crest_diff_10m_cfs_per_smi": dC,
        }, file_time_from_meta(curr_meta)

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

    if param == "RAINRATE_DIFF_10M":
        curr_path, curr_meta = get_grib_for_product_time("PRECIPRATE", requested_token)
        current_token = curr_meta.get("token") or requested_token
        if not current_token:
            raise ValueError("Could not determine current PrecipRate token for 10-minute difference.")
        prev_token = token_add_minutes(current_token, -10)
        prev_path, prev_meta = get_grib_for_product_time_strict("PRECIPRATE", prev_token, tolerance_seconds=3 * 60)
        curr_val = sample_native_value(curr_path, lat, lon)
        prev_val = sample_native_value(prev_path, lat, lon)

        if curr_val is None or prev_val is None:
            return None, f"{file_time_from_meta(curr_meta)} minus {file_time_from_meta(prev_meta)}"

        diff_mmhr = curr_val - prev_val
        dv = diff_mmhr * MM_TO_IN
        return {
            "value_m3s_per_km2": diff_mmhr,
            "value_cfs_per_smi": dv,
            "display_value": dv,
            "display_units": pinfo.get("units", "in/hr"),
            "native_value": diff_mmhr,
            "native_units": pinfo.get("native_units", "mm/hr"),
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
    if param == "COMPUTED_P":
        # P is already the final display quantity; suppress a duplicate
        # "native" line in the max-target popup.
        native_val = None
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

    mode = "max" if param == "COMPUTED_P" else "extreme"
    return value, data.get("file_time_utc", ""), mode


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


MATCHED_MEAN_RANK_POWER = 4.0


def normalize_mean_mode(mean_mode):
    text = str(mean_mode or "matched").strip().lower().replace("-", "_")
    if text in ("pure", "average", "avg", "arithmetic", "arithmetic_mean"):
        return "pure"
    return "matched"


def matched_mean_average(vals):
    """Upper-tail-weighted average for a single gridded field/area.

    This is PMM-inspired, but not a true ensemble probability-matched mean.
    It weights each finite pixel by its ranked intensity so broad high-value
    areas influence the mean more than they would in a pure arithmetic average,
    while still staying below the true max-pixel value.
    """
    vals = np.asarray(vals, dtype=np.float64)
    vals = vals[np.isfinite(vals)]
    if vals.size == 0:
        return None
    if vals.size == 1:
        return float(vals[0])

    sorted_vals = np.sort(vals)
    ranks = np.linspace(1.0 / float(sorted_vals.size), 1.0, sorted_vals.size, dtype=np.float64)
    weights = np.power(ranks, MATCHED_MEAN_RANK_POWER)
    weight_sum = float(np.sum(weights))
    if weight_sum <= 0 or not np.isfinite(weight_sum):
        return float(np.nanmean(sorted_vals))
    return float(np.sum(sorted_vals * weights) / weight_sum)


def summarize_area_average_values(vals, param, product, pinfo, data, extra=None, mean_mode="matched"):
    extra = extra or {}
    mean_mode = normalize_mean_mode(mean_mode)
    mean_label = "High-Value Weighted Avg" if mean_mode == "matched" else "Pure Average"
    if vals is None or vals.size == 0:
        payload = {
            "found": False,
            "param": param,
            "product": data.get("product") or product,
            "display": data.get("display", pinfo.get("display", param)),
            "display_units": pinfo.get("units", ""),
            "native_units": data.get("native_units", pinfo.get("native_units", "")),
            "file_time_utc": data.get("file_time_utc", ""),
            "resolved_token": data.get("resolved_token"),
            "mean_mode": mean_mode,
            "mean_label": mean_label,
            "high_value_weighted_method": "upper_tail_rank_weighted_power_4",
            "count": 0,
        }
        payload.update(extra)
        return payload

    vals = vals.astype(np.float64)
    vals = vals[np.isfinite(vals)]
    if vals.size == 0:
        return summarize_area_average_values(np.array([], dtype=np.float64), param, product, pinfo, data, extra=extra, mean_mode=mean_mode)

    vmin = float(np.nanmin(vals))
    vmax = float(np.nanmax(vals))
    pure_mean = float(np.nanmean(vals))
    matched_mean = matched_mean_average(vals)
    if matched_mean is None or not np.isfinite(matched_mean):
        matched_mean = pure_mean
    selected_mean = matched_mean if mean_mode == "matched" else pure_mean
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
        "resolved_token": data.get("resolved_token"),
        # mean is the currently selected average mode so the existing readout
        # and trend code can stay compact.
        "mean": float(selected_mean),
        "pure_mean": pure_mean,
        "matched_mean": float(matched_mean),
        "mean_mode": mean_mode,
        "mean_label": mean_label,
        "high_value_weighted_method": "upper_tail_rank_weighted_power_4",
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

def area_average_for_parameter(param, product, requested_token, lat, lon, radius_m, mean_mode="matched"):
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
    }, mean_mode=mean_mode)


def area_average_for_polygon(param, product, requested_token, vertices, mean_mode="matched"):
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
    }, mean_mode=mean_mode)


def area_average_for_bounds(param, product, requested_token, west, south, east, north, width=950, mean_mode="matched"):
    param, pinfo = parameter_info(param, fallback_product=product)
    width = int(max(320, min(1600, width)))
    data = compute_parameter_array(param, product, requested_token, west, south, east, north, width)
    arr = data["arr_cfs"]
    finite = np.isfinite(arr)
    vals = arr[finite] if np.any(finite) else np.array([], dtype=np.float64)
    return summarize_area_average_values(vals, param, product, pinfo, data, {
        "west": float(west),
        "south": float(south),
        "east": float(east),
        "north": float(north),
        "width": int(width),
    }, mean_mode=mean_mode)


def max_for_polygon_parameter(param, product, requested_token, vertices, width=None, min_threshold=0.0):
    if not vertices or len(vertices) < 3:
        raise ValueError("At least 3 vertices are required")

    lats = [float(v["lat"]) for v in vertices]
    lons = [float(v["lon"]) for v in vertices]
    west, east = min(lons), max(lons)
    south, north = min(lats), max(lats)
    param, pinfo = parameter_info(param, fallback_product=product)

    vx, vy = rio_transform("EPSG:4326", "EPSG:3857", lons, lats)
    path = MplPath(np.column_stack([vx, vy]), closed=True)

    if width is None:
        width = int(max(320, min(1200, max((east - west) * 111320.0, (north - south) * 111320.0) / 250.0)))
    else:
        width = int(max(320, min(1600, width)))

    data = compute_parameter_array(param, product, requested_token, west, south, east, north, width)
    arr = data["arr_cfs"]
    raw = data["arr_m3s_per_km2"]
    transform = data["dst_transform"]

    rows = np.arange(data["height"], dtype=np.float64) + 0.5
    cols = np.arange(data["width"], dtype=np.float64) + 0.5
    xs = transform.c + cols * transform.a
    ys = transform.f + rows * transform.e
    grid_x, grid_y = np.meshgrid(xs, ys)
    points = np.column_stack([grid_x.ravel(), grid_y.ravel()])
    mask = path.contains_points(points, radius=1e-9).reshape(arr.shape)
    finite = mask & np.isfinite(arr)
    if min_threshold > 0:
        finite &= arr >= float(min_threshold)

    if not np.any(finite):
        return None, data.get("file_time_utc", ""), "polygon"

    work = np.where(finite, arr, np.nan)
    row, col = np.unravel_index(np.nanargmax(work), work.shape)
    lat, lon = pixel_latlon_from_webmercator_transform(transform, int(row), int(col))
    display_val = float(arr[row, col])
    native_val = float(raw[row, col]) if np.isfinite(raw[row, col]) else None

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
        "west": west,
        "south": south,
        "east": east,
        "north": north,
        "count": int(np.count_nonzero(finite)),
    }
    return value, data.get("file_time_utc", ""), "polygon"


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
    tag = str(tag or "").strip().lower()
    if tag == "emergency":
        return 3
    if tag == "considerable":
        return 2
    return 0


def flash_flood_status_from_tag(tag):
    tag = str(tag or "").strip().lower()
    if tag == "emergency":
        return "EMERGENCY"
    if tag == "considerable":
        return "CONSIDERABLE"
    return "BASE"


def vtec_action_suppresses(action):
    """Only cancellation/expiration actions end the FF.W event.

    NEW, CON, UPG, EXT, and COR are all active event updates and are allowed to
    carry or preserve CONSIDERABLE/CATASTROPHIC damage-threat tags.
    """
    return str(action or "").strip().upper() in {"CAN", "EXP"}


def warning_candidate_issue(candidate):
    value = (candidate or {}).get("issue_dt")
    if isinstance(value, datetime):
        return value
    return datetime(1900, 1, 1, tzinfo=timezone.utc)


def resolve_flash_flood_event_candidates(candidates, valid_dt):
    """Resolve one FF.W product chain at ``valid_dt``.

    Impact tags belong to the warning event, not just to the individual product
    that first contained the tag. Therefore a later CON/EXT/COR/UPG that omits
    the tag must not downgrade an earlier CONSIDERABLE or CATASTROPHIC tag.
    The latest non-cancelled product controls the active end time and geometry;
    the highest tag observed anywhere in the event chain controls the tier.
    """
    if not candidates:
        return None

    ordered = sorted(
        candidates,
        key=lambda c: (warning_candidate_issue(c), int(c.get("source_index", 0))),
    )
    latest = ordered[-1]
    latest_action = str(latest.get("action", "")).upper()
    latest_end = latest.get("end_dt")

    explicit_suppress = vtec_action_suppresses(latest_action)
    expired = bool(latest_end and valid_dt > latest_end + timedelta(minutes=1))
    suppress = explicit_suppress or expired

    # Preserve the strongest tag from every prior non-cancelled update. This is
    # the key behavior for NEW -> CON/EXT/COR/UPG chains where only one product
    # repeats FLASH FLOOD DAMAGE THREAT...CONSIDERABLE/CATASTROPHIC.
    tag_candidates = [c for c in ordered if not vtec_action_suppresses(c.get("action"))]
    if tag_candidates:
        best_tag_candidate = max(
            tag_candidates,
            key=lambda c: (
                tag_rank(c.get("tag", "")),
                warning_candidate_issue(c),
                int(c.get("source_index", 0)),
            ),
        )
    else:
        best_tag_candidate = latest

    best_tag = str(best_tag_candidate.get("tag", "") or "").lower()

    active_candidates = []
    for candidate in ordered:
        if vtec_action_suppresses(candidate.get("action")):
            continue
        end_dt = candidate.get("end_dt")
        if end_dt and valid_dt > end_dt + timedelta(minutes=1):
            continue
        active_candidates.append(candidate)

    # Use the newest active polygon/update for placement, then apply the event's
    # strongest tier to it. This avoids retaining an obsolete original polygon.
    feature_candidates = [c for c in active_candidates if c.get("feature") is not None]
    if feature_candidates:
        feature_candidate = max(
            feature_candidates,
            key=lambda c: (warning_candidate_issue(c), int(c.get("source_index", 0))),
        )
    else:
        feature_candidate = None

    return {
        "latest": latest,
        "best_tag_candidate": best_tag_candidate,
        "best_tag": best_tag,
        "status": flash_flood_status_from_tag(best_tag),
        "feature_candidate": feature_candidate,
        "suppress": suppress,
        "explicit_suppress": explicit_suppress,
        "suppress_reason": "action" if explicit_suppress else "expired" if expired else "",
    }


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
    raw = str(text or "")
    blob = raw.lower()
    compact = re.sub(r"[^a-z0-9]+", " ", blob).strip()

    # Match the official IBW tag with arbitrary whitespace, newlines, periods,
    # colons, HTML remnants, or other separators between THREAT and the value.
    # This explicitly supports NEW, CON, UPG, EXT, and COR product bodies; the
    # VTEC action is deliberately irrelevant to classification.
    damage_match = re.search(
        r"\bFLASH\s+FLOOD\s+DAMAGE\s+THREAT\b(?:\W|_){0,80}\b(CATASTROPHIC|CONSIDERABLE)\b",
        raw,
        re.IGNORECASE | re.DOTALL,
    )
    if damage_match:
        return "emergency" if damage_match.group(1).upper() == "CATASTROPHIC" else "considerable"

    # Some source formats expose the field name and value separately after KML
    # or CSV parsing. The compact form catches those without requiring literal
    # ellipses in the source text.
    if re.search(r"\bflash flood damage threat catastrophic\b", compact):
        return "emergency"
    if re.search(r"\bflash flood damage threat considerable\b", compact):
        return "considerable"

    # Explicit emergency wording remains authoritative.
    if (
        "flash flood emergency" in blob
        or "flash flood emergency" in compact
        or "particularly dangerous situation" in blob
        or re.search(r"\bdamage threat catastrophic\b", compact)
    ):
        return "emergency"

    if re.search(r"\bdamage threat considerable\b", compact):
        return "considerable"

    # Last-resort metadata fallbacks. These are useful when KML ExtendedData
    # contains only the tier value, but they are evaluated after the exact tag.
    if re.search(r"\bcatastrophic\b", compact):
        return "emergency"
    if re.search(r"\bconsiderable\b", compact):
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
    # Texas / southern Plains offices. These are needed for panned archive
    # cases where the original FFW was issued as NEW with
    # FLASH FLOOD DAMAGE THREAT...CONSIDERABLE/CATASTROPHIC, but the IEM
    # polygon layer only exposes a generic BASE warning. Deep text fetches
    # FFWxxx as well as FFSxxx, so the original NEW warning can promote itself.
    "FWD": (-99.80, 30.80, -94.00, 34.90),
    "EWX": (-101.20, 28.00, -96.00, 31.80),
    "SJT": (-102.20, 29.30, -98.00, 33.10),
    "MAF": (-106.80, 29.00, -100.00, 33.60),
    "LUB": (-103.80, 32.80, -99.20, 35.80),
    "AMA": (-103.80, 34.20, -99.20, 37.20),
    "HGX": (-97.00, 28.20, -93.00, 31.60),
    "CRP": (-99.80, 26.60, -96.20, 29.60),
    "BRO": (-99.80, 25.00, -96.50, 27.80),
    "EPZ": (-109.20, 30.80, -103.00, 33.80),
    "OUN": (-100.40, 33.40, -95.00, 37.20),
    "TSA": (-96.80, 33.40, -91.80, 37.40),
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
    """Parse FFS products and resolve the authoritative tier for each FF.W."""
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
        vtec_id = f"FF.W.{etn}"
        action = match.group("action").upper()
        begin_dt = parse_vtec_time(match.group("begin"))
        end_dt = parse_vtec_time(match.group("end"))
        issue_dt = infer_issue_time_from_segment(segment, valid_dt)

        if issue_dt and issue_dt > valid_dt + timedelta(minutes=1):
            continue
        if begin_dt and valid_dt < begin_dt - timedelta(minutes=1):
            continue

        tag = classify_flash_flood_tag_from_text(segment)
        status = flash_flood_status_from_tag(tag)
        geom = parse_latlon_polygon_from_text(segment)
        issue_for_sort = issue_dt or datetime(1900, 1, 1, tzinfo=timezone.utc)
        key = (wfo, vtec_id)

        feature = None
        if geom is not None and not vtec_action_suppresses(action):
            feature = {
                "type": "Feature",
                "geometry": geom,
                "properties": {
                    "event": "Flash Flood Warning",
                    "product_code": "FFW+FFS",
                    "product_label": "FFW",
                    "display_label": f"{status} FF.W {etn}",
                    "headline": f"Valid Flash Flood Statement update for {vtec_id} {status}",
                    "wfo": wfo,
                    "vtec_id": vtec_id,
                    "warning_number": vtec_id,
                    "phen": "FF",
                    "sig": "W",
                    "etn": etn,
                    "action": action,
                    "flash_flood_tag": tag,
                    "ffs_detected": True,
                    "statement_status": status,
                    "issue_utc": iso_z(issue_dt),
                    "vtec_begin_utc": iso_z(begin_dt),
                    "vtec_end_utc": iso_z(end_dt),
                    "source": "IEM AFOS FFS text authoritative event-chain polygon",
                    "source_product": "FFS",
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
            "source_index": idx,
            "source_product": "FFS",
        })

    out_tags = {}
    out_features = []

    for key, candidates in grouped.items():
        resolved = resolve_flash_flood_event_candidates(candidates, valid_dt)
        if not resolved:
            continue

        latest = resolved["latest"]
        best_tag = resolved["best_tag"]
        status = resolved["status"]
        out_tags[key] = {
            "wfo": latest.get("wfo"),
            "vtec_id": latest.get("vtec_id"),
            "tag": best_tag,
            "action": latest.get("action"),
            "ffs_detected": not resolved["suppress"],
            "suppress": resolved["suppress"],
            "explicit_suppress": resolved["explicit_suppress"],
            "suppress_reason": resolved["suppress_reason"],
            "issue_dt": latest.get("issue_dt"),
            "begin_dt": latest.get("begin_dt"),
            "end_dt": latest.get("end_dt"),
            "statement_status": status,
            "source_product": "FFS",
        }

        selected = resolved.get("feature_candidate")
        if not resolved["suppress"] and selected and selected.get("feature"):
            feature = selected["feature"]
            props = feature.get("properties", {})
            props["flash_flood_tag"] = best_tag
            props["statement_status"] = status
            props["display_label"] = f"{status} FF.W {props.get('etn', latest.get('vtec_id', '').split('.')[-1])}"
            props["action"] = latest.get("action", props.get("action", ""))
            props["vtec_end_utc"] = iso_z(latest.get("end_dt"))
            feature["properties"] = props
            out_features.append(feature)

    return out_tags, out_features


def parse_ffw_products_from_text(text, valid_dt):
    """Parse original FFW products and preserve IBW tags across all updates."""
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
        vtec_id = f"FF.W.{etn}"
        action = match.group("action").upper()
        begin_dt = parse_vtec_time(match.group("begin"))
        end_dt = parse_vtec_time(match.group("end"))
        issue_dt = infer_issue_time_from_segment(segment, valid_dt)

        if issue_dt and issue_dt > valid_dt + timedelta(minutes=1):
            continue
        if begin_dt and valid_dt < begin_dt - timedelta(minutes=1):
            continue

        tag = classify_flash_flood_tag_from_text(segment)
        status = flash_flood_status_from_tag(tag)
        geom = parse_latlon_polygon_from_text(segment)
        issue_for_sort = issue_dt or datetime(1900, 1, 1, tzinfo=timezone.utc)
        key = (wfo, vtec_id)

        feature = None
        if geom is not None and not vtec_action_suppresses(action):
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
                    "source": "IEM AFOS FFW text authoritative event-chain polygon",
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
            "feature": feature,
            "source_index": idx,
            "source_product": "FFW",
        })

    out_tags = {}
    out_features = []

    for key, candidates in grouped.items():
        resolved = resolve_flash_flood_event_candidates(candidates, valid_dt)
        if not resolved:
            continue

        latest = resolved["latest"]
        best_tag = resolved["best_tag"]
        status = resolved["status"]
        out_tags[key] = {
            "wfo": latest.get("wfo"),
            "vtec_id": latest.get("vtec_id"),
            "tag": best_tag,
            "action": latest.get("action"),
            "ffs_detected": False,
            "suppress": resolved["suppress"],
            "explicit_suppress": resolved["explicit_suppress"],
            "suppress_reason": resolved["suppress_reason"],
            "issue_dt": latest.get("issue_dt"),
            "begin_dt": latest.get("begin_dt"),
            "end_dt": latest.get("end_dt"),
            "statement_status": status,
            "source_product": "FFW",
        }

        selected = resolved.get("feature_candidate")
        if not resolved["suppress"] and selected and selected.get("feature"):
            feature = selected["feature"]
            props = feature.get("properties", {})
            props["flash_flood_tag"] = best_tag
            props["statement_status"] = status
            props["display_label"] = f"{status} FF.W {props.get('etn', latest.get('vtec_id', '').split('.')[-1])}"
            props["action"] = latest.get("action", props.get("action", ""))
            props["vtec_end_utc"] = iso_z(latest.get("end_dt"))
            feature["properties"] = props
            out_features.append(feature)

    return out_tags, out_features


def merge_flash_flood_text_tag(existing, incoming):
    """Merge FFW and FFS event states by chronology, preserving the top tier."""
    if existing is None:
        return dict(incoming)
    if incoming is None:
        return existing

    old = dict(existing)
    new = dict(incoming)
    old_issue = warning_candidate_issue(old)
    new_issue = warning_candidate_issue(new)

    # The newest product controls whether the event is active. This allows a
    # later CON/EXT/COR/UPG FFS to supersede the original FFW end time, while a
    # later CAN/EXP still suppresses the event.
    if new_issue > old_issue:
        merged = new
        prior = old
    elif old_issue > new_issue:
        merged = old
        prior = new
    else:
        # At equal issue time, explicit cancellation/expiration wins. Otherwise
        # prefer FFS because it is the follow-up authority for the FF.W event.
        if new.get("explicit_suppress") and not old.get("explicit_suppress"):
            merged, prior = new, old
        elif old.get("explicit_suppress") and not new.get("explicit_suppress"):
            merged, prior = old, new
        elif new.get("source_product") == "FFS":
            merged, prior = new, old
        else:
            merged, prior = old, new

    # Highest observed damage-threat tier persists for the life of the event.
    if tag_rank(prior.get("tag", "")) > tag_rank(merged.get("tag", "")):
        merged["tag"] = prior.get("tag", "")
        merged["statement_status"] = flash_flood_status_from_tag(merged["tag"])

    merged["ffs_detected"] = bool(old.get("ffs_detected") or new.get("ffs_detected")) and not merged.get("suppress", False)
    if old.get("source_product") == "FFS" or new.get("source_product") == "FFS":
        merged["source_product"] = "FFS"

    return merged


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


def collapse_text_flash_flood_features(features, tags):
    """Return one authoritative AFOS polygon per WFO/FF.W event."""
    if not features:
        return []

    by_vtec = {}
    for (wfo, vtec_id), data in (tags or {}).items():
        by_vtec.setdefault(vtec_id, []).append((wfo, data))

    grouped = {}
    passthrough = []
    for feature in features:
        props = feature.get("properties", {})
        vtec_id = derive_alert_vtec_id(props)
        wfo = clean_wfo(props.get("wfo", ""))
        if not vtec_id:
            passthrough.append(feature)
            continue
        grouped.setdefault((wfo, vtec_id), []).append(feature)

    out = list(passthrough)
    for (wfo, vtec_id), group in grouped.items():
        data = (tags or {}).get((wfo, vtec_id))
        if data is None:
            matches = by_vtec.get(vtec_id, [])
            if matches:
                _, data = max(
                    matches,
                    key=lambda item: (
                        tag_rank(item[1].get("tag", "")),
                        warning_candidate_issue(item[1]),
                    ),
                )
        if data and data.get("suppress"):
            continue

        def feature_score(feature):
            props = feature.get("properties", {})
            issue = parse_iso_z(props.get("issue_utc", "")) or datetime(1900, 1, 1, tzinfo=timezone.utc)
            source = str(props.get("source_product", "")).upper()
            return (issue, 1 if source == "FFS" else 0, tag_rank(props.get("flash_flood_tag", "")))

        selected = max(group, key=feature_score)
        props = selected.get("properties", {})
        tag = (data or {}).get("tag", props.get("flash_flood_tag", ""))
        status = flash_flood_status_from_tag(tag)
        props["flash_flood_tag"] = tag
        props["statement_status"] = status
        props["product_label"] = "FFW"
        props["product_code"] = "FFW+FFS" if (data or {}).get("source_product") == "FFS" or (data or {}).get("ffs_detected") else "FFW"
        props["ffs_detected"] = bool((data or {}).get("ffs_detected"))
        props["display_label"] = f"{status} FF.W {vtec_id.split('.')[-1]}"
        if data:
            props["action"] = data.get("action", props.get("action", ""))
            props["vtec_end_utc"] = iso_z(data.get("end_dt"))
            props["latest_flash_flood_text_issue_utc"] = iso_z(data.get("issue_dt"))
        selected["properties"] = props
        out.append(selected)

    return out


def collapse_alert_feature_versions(features):
    """Remove lower-tier duplicate copies of the same warning event."""
    grouped = {}
    passthrough = []

    for feature in features or []:
        props = feature.get("properties", {})
        if props.get("event") != "Flash Flood Warning":
            passthrough.append(feature)
            continue
        vtec_id = derive_alert_vtec_id(props)
        if not vtec_id:
            passthrough.append(feature)
            continue
        key = (clean_wfo(props.get("wfo", "")), vtec_id)
        grouped.setdefault(key, []).append(feature)

    out = list(passthrough)
    for key, group in grouped.items():
        def score(feature):
            props = feature.get("properties", {})
            source = str(props.get("source", ""))
            issue = (
                parse_iso_z(props.get("latest_flash_flood_text_issue_utc", ""))
                or parse_iso_z(props.get("issue_utc", ""))
                or datetime(1900, 1, 1, tzinfo=timezone.utc)
            )
            return (
                1 if "AFOS FFW text" in source or "AFOS FFS text" in source else 0,
                issue,
                tag_rank(props.get("flash_flood_tag", "")),
                1 if str(props.get("product_code", "")).upper() == "FFW+FFS" else 0,
            )

        selected = max(group, key=score)
        strongest = max(
            group,
            key=lambda f: tag_rank(f.get("properties", {}).get("flash_flood_tag", "")),
        )
        strong_tag = strongest.get("properties", {}).get("flash_flood_tag", "")
        props = selected.get("properties", {})
        if tag_rank(strong_tag) > tag_rank(props.get("flash_flood_tag", "")):
            props["flash_flood_tag"] = strong_tag
        status = flash_flood_status_from_tag(props.get("flash_flood_tag", ""))
        props["statement_status"] = status
        props["display_label"] = f"{status} FF.W {key[1].split('.')[-1]}"
        selected["properties"] = props
        out.append(selected)

    return out


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
        "classifier": "authoritative_event_chain_tags_v13_all_vtec_actions",
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

        all_features = collapse_text_flash_flood_features(all_features, all_tags)

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
            if is_kml_ffw and gb and any(bbox_overlap_fraction(gb, tb) >= 0.40 for tb in text_feature_bounds):
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
    """Promote a polygon only when VTEC identity or geometry supports the match."""
    if not features or not text_features:
        return features

    text_infos = []
    by_vtec = {}
    for feature in text_features:
        props = feature.get("properties", {})
        if props.get("event") != "Flash Flood Warning":
            continue
        vtec_id = derive_alert_vtec_id(props)
        gb = geom_coord_bounds(feature.get("geometry"))
        if not vtec_id or not gb:
            continue
        wfo = clean_wfo(props.get("wfo", ""))
        tag_data = (ffs_tags or {}).get((wfo, vtec_id)) if wfo else None
        if tag_data is None:
            matches = [
                v for (twfo, tvtec), v in (ffs_tags or {}).items()
                if tvtec == vtec_id and not v.get("suppress")
            ]
            if matches:
                tag_data = max(
                    matches,
                    key=lambda v: (tag_rank(v.get("tag", "")), warning_candidate_issue(v)),
                )
        tag = (tag_data or {}).get("tag") or props.get("flash_flood_tag", "")
        info = {
            "bbox": gb,
            "vtec_id": vtec_id,
            "etn": normalize_etn(vtec_id.split(".")[-1]),
            "wfo": wfo,
            "tag": tag,
            "status": flash_flood_status_from_tag(tag),
            "end_dt": (tag_data or {}).get("end_dt"),
            "issue_dt": (tag_data or {}).get("issue_dt"),
            "source_product": (tag_data or {}).get("source_product") or props.get("source_product", "FFW"),
        }
        text_infos.append(info)
        by_vtec.setdefault(vtec_id, []).append(info)

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
        wfo = clean_wfo(props.get("wfo", ""))

        exact = list(by_vtec.get(vtec_id, [])) if vtec_id else []
        same_identity = [
            item for item in text_infos
            if etn and item["etn"] == etn and (not wfo or not item["wfo"] or item["wfo"] == wfo)
        ]
        pool = exact or same_identity
        identity_match = bool(pool)
        if not pool:
            same_wfo = [item for item in text_infos if wfo and item["wfo"] == wfo]
            pool = same_wfo or text_infos

        scored = [(bbox_overlap_fraction(fb, item["bbox"]), item) for item in pool]
        scored.sort(
            key=lambda pair: (
                pair[0],
                tag_rank(pair[1].get("tag", "")),
                warning_candidate_issue(pair[1]),
            ),
            reverse=True,
        )
        if not scored:
            continue
        overlap, best = scored[0]

        # Exact VTEC identity is authoritative. ETN/WFO identity permits a small
        # overlap because follow-up polygons can be trimmed. Geometry-only
        # fallback requires a strong overlap to prevent tag drift.
        if not identity_match and overlap < 0.40:
            continue
        if same_identity and not exact and overlap < 0.02:
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
        status = flash_flood_status_from_tag(props.get("flash_flood_tag", ""))
        props["statement_status"] = status
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



def _nws_parameter_values(parameters, key):
    if not isinstance(parameters, dict):
        return []
    value = parameters.get(key)
    if value is None:
        # CAP parameter keys can vary in case across serializers.
        for candidate_key, candidate_value in parameters.items():
            if str(candidate_key).lower() == str(key).lower():
                value = candidate_value
                break
    if value is None:
        return []
    if isinstance(value, (list, tuple)):
        return [str(v) for v in value if v not in (None, "")]
    return [str(value)]


def _nws_alert_text_blob(props):
    parts = []
    for key in (
        "headline", "description", "instruction", "event", "senderName",
        "messageType", "severity", "certainty", "urgency",
    ):
        value = props.get(key)
        if value:
            parts.append(str(value))
    parameters = props.get("parameters") or {}
    if isinstance(parameters, dict):
        for key, value in parameters.items():
            parts.append(str(key))
            if isinstance(value, (list, tuple)):
                parts.extend(str(v) for v in value)
            elif value is not None:
                parts.append(str(value))
    return "\n".join(parts)


def _nws_alert_vtec_info(props):
    blob = _nws_alert_text_blob(props)
    vtec_values = _nws_parameter_values(props.get("parameters") or {}, "VTEC")
    # VTEC in the parameters block is the cleanest identity. Include the full
    # alert text as a fallback because some serializers place it only there.
    return make_vtec_info(props, "\n".join(vtec_values + [blob]))


def _nws_feature_issue_dt(props):
    for key in ("sent", "effective", "onset"):
        dt = parse_iso_z(props.get(key, ""))
        if dt:
            return dt
    return datetime(1900, 1, 1, tzinfo=timezone.utc)


def _nws_feature_end_dt(props, vtec_info):
    # Prefer the VTEC event end because CAP expires may represent product
    # expiration rather than the warning event's authoritative end.
    vtec_end = parse_iso_z(vtec_info.get("vtec_end_utc", ""))
    if vtec_end:
        return vtec_end
    for key in ("ends", "expires"):
        dt = parse_iso_z(props.get(key, ""))
        if dt:
            return dt
    return None


def fetch_nws_active_flash_flood_warnings(valid_dt):
    """Fetch current active FF.W alerts directly from the official NWS API.

    The endpoint already returns active alerts, their CAP text, VTEC parameters,
    and warning geometry. It is used only near real time; historical/archive
    requests continue through the existing IEM valid-at-time path.
    """
    valid_dt = valid_dt.astimezone(timezone.utc)
    if abs((now_utc() - valid_dt).total_seconds()) > NWS_ACTIVE_FFW_LIVE_TOLERANCE_MINUTES * 60:
        return []

    cache_key = "active-flash-flood-warning"
    now_ts = time.time()
    with NWS_ACTIVE_FFW_LOCK:
        cached = NWS_ACTIVE_FFW_CACHE.get(cache_key)
        if cached:
            ttl = NWS_ACTIVE_FFW_FAILURE_TTL_SECONDS if cached.get("failed") else NWS_ACTIVE_FFW_CACHE_TTL_SECONDS
            if now_ts - cached.get("time", 0) < ttl:
                return list(cached.get("features", []))

    url = "https://api.weather.gov/alerts/active"
    params = {
        "status": "actual",
        "event": "Flash Flood Warning",
    }
    headers = {
        "Accept": "application/geo+json, application/json",
        "User-Agent": APP_USER_AGENT,
    }

    try:
        response = requests_get(url, params=params, headers=headers, timeout=12)
        response.raise_for_status()
        payload = response.json()
    except Exception as exc:
        print(f"[NWS active FF.W authority fetch error] {exc}")
        with NWS_ACTIVE_FFW_LOCK:
            NWS_ACTIVE_FFW_CACHE[cache_key] = {
                "time": now_ts,
                "failed": True,
                "features": [],
                "error": str(exc),
            }
            trim_cache(NWS_ACTIVE_FFW_CACHE, NWS_ACTIVE_FFW_CACHE_MAX_ITEMS)
        return []

    grouped = {}
    for source_index, raw_feature in enumerate(payload.get("features", []) or []):
        props = dict(raw_feature.get("properties") or {})
        event = str(props.get("event", "")).strip().lower()
        if event != "flash flood warning":
            continue

        text_blob = _nws_alert_text_blob(props)
        vtec_info = _nws_alert_vtec_info(props)
        if vtec_info.get("phen") != "FF" or vtec_info.get("sig") != "W":
            continue

        action = str(vtec_info.get("action", "") or "").upper()
        if vtec_action_suppresses(action):
            continue

        issue_dt = _nws_feature_issue_dt(props)
        begin_dt = parse_iso_z(vtec_info.get("vtec_begin_utc", "")) or parse_iso_z(props.get("onset", "")) or parse_iso_z(props.get("effective", ""))
        end_dt = _nws_feature_end_dt(props, vtec_info)
        if issue_dt and issue_dt > valid_dt + timedelta(minutes=2):
            continue
        if begin_dt and valid_dt < begin_dt - timedelta(minutes=1):
            continue
        if end_dt and valid_dt > end_dt + timedelta(minutes=1):
            continue

        tag = classify_flash_flood_tag_from_text(text_blob)
        status = flash_flood_status_from_tag(tag)
        vtec_id = vtec_info.get("vtec_id", "")
        wfo = clean_wfo(vtec_info.get("wfo", "") or props.get("sender", ""))
        etn = normalize_etn(vtec_info.get("etn", "") or (vtec_id.split(".")[-1] if vtec_id else ""))

        geom = raw_feature.get("geometry")
        if not geom:
            geom = parse_latlon_polygon_from_text(text_blob)
        if not geom:
            continue

        out_props = {
            "event": "Flash Flood Warning",
            "product_code": "FFW+FFS" if action in {"CON", "UPG", "EXT", "COR"} else "FFW",
            "product_label": "FFW",
            "display_label": f"{status} FF.W {etn}".strip(),
            "headline": props.get("headline") or f"Active Flash Flood Warning {vtec_id}",
            "description": props.get("description", ""),
            "instruction": props.get("instruction", ""),
            "wfo": wfo,
            "vtec_id": vtec_id,
            "warning_number": vtec_id,
            "phen": "FF",
            "sig": "W",
            "etn": etn,
            "action": action,
            "flash_flood_tag": tag,
            "ffs_detected": action in {"CON", "UPG", "EXT", "COR"},
            "statement_status": status,
            "issue_utc": iso_z(issue_dt),
            "vtec_begin_utc": iso_z(begin_dt),
            "vtec_end_utc": iso_z(end_dt),
            "source": "Official NWS API active FF.W authoritative alert",
            "source_product": "NWS_API",
            "nws_alert_id": props.get("id") or raw_feature.get("id", ""),
        }
        candidate = {
            "type": "Feature",
            "geometry": geom,
            "properties": out_props,
        }
        key = (wfo, vtec_id)
        grouped.setdefault(key, []).append((issue_dt, source_index, candidate))

    features = []
    for key, candidates in grouped.items():
        # The newest active CAP alert controls geometry/timing, while the highest
        # damage-threat tier anywhere in the active chain controls classification.
        candidates.sort(key=lambda item: (item[0], item[1]))
        selected = candidates[-1][2]
        strongest = max(
            (item[2] for item in candidates),
            key=lambda feature: tag_rank(feature.get("properties", {}).get("flash_flood_tag", "")),
        )
        selected_props = selected.get("properties", {})
        strong_tag = strongest.get("properties", {}).get("flash_flood_tag", "")
        if tag_rank(strong_tag) > tag_rank(selected_props.get("flash_flood_tag", "")):
            selected_props["flash_flood_tag"] = strong_tag
        status = flash_flood_status_from_tag(selected_props.get("flash_flood_tag", ""))
        selected_props["statement_status"] = status
        selected_props["display_label"] = f"{status} FF.W {selected_props.get('etn', '')}".strip()
        selected["properties"] = selected_props
        features.append(selected)

    with NWS_ACTIVE_FFW_LOCK:
        NWS_ACTIVE_FFW_CACHE[cache_key] = {
            "time": now_ts,
            "failed": False,
            "features": features,
        }
        trim_cache(NWS_ACTIVE_FFW_CACHE, NWS_ACTIVE_FFW_CACHE_MAX_ITEMS)
    return list(features)


def apply_nws_active_flash_flood_authority(features, valid_dt, west, south, east, north):
    """Promote/replace live FF.W polygons from the official NWS active feed."""
    official = fetch_nws_active_flash_flood_warnings(valid_dt)
    if not official:
        return features

    official = filter_geojson_by_bbox(official, west, south, east, north)
    if not official:
        return features

    by_exact = {}
    by_vtec = {}
    official_infos = []
    for feature in official:
        props = feature.get("properties", {})
        vtec_id = derive_alert_vtec_id(props)
        wfo = clean_wfo(props.get("wfo", ""))
        gb = geom_coord_bounds(feature.get("geometry"))
        if not vtec_id or not gb:
            continue
        by_exact[(wfo, vtec_id)] = feature
        by_vtec.setdefault(vtec_id, []).append(feature)
        official_infos.append((feature, gb))

    retained = []
    replaced_exact = set()
    for feature in features or []:
        props = feature.get("properties", {})
        if props.get("event") != "Flash Flood Warning":
            retained.append(feature)
            continue

        vtec_id = derive_alert_vtec_id(props)
        wfo = clean_wfo(props.get("wfo", ""))
        match = by_exact.get((wfo, vtec_id)) if vtec_id else None
        if match is None and vtec_id:
            matches = by_vtec.get(vtec_id, [])
            if len(matches) == 1:
                match = matches[0]

        if match is None:
            gb = geom_coord_bounds(feature.get("geometry"))
            if gb:
                overlap_matches = []
                for official_feature, official_bbox in official_infos:
                    overlap = bbox_overlap_fraction(gb, official_bbox)
                    if overlap >= 0.55:
                        overlap_matches.append((overlap, tag_rank(official_feature.get("properties", {}).get("flash_flood_tag", "")), official_feature))
                if overlap_matches:
                    match = max(overlap_matches, key=lambda item: (item[0], item[1]))[2]

        if match is not None:
            match_props = match.get("properties", {})
            key = (clean_wfo(match_props.get("wfo", "")), derive_alert_vtec_id(match_props))
            if key not in replaced_exact:
                retained.append(match)
                replaced_exact.add(key)
            continue

        retained.append(feature)

    for feature in official:
        props = feature.get("properties", {})
        key = (clean_wfo(props.get("wfo", "")), derive_alert_vtec_id(props))
        if key not in replaced_exact:
            retained.append(feature)
            replaced_exact.add(key)

    return retained


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
        "csv_etn_enrichment": "authoritative AFOS FF.W event-chain tags v13",
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

    # For live/current warnings, the official NWS active-alert feed is the
    # final authority for FF.W identity, geometry, and damage-threat tier.
    features = apply_nws_active_flash_flood_authority(
        features, valid_dt, qwest, qsouth, qeast, qnorth
    )

    features = collapse_alert_feature_versions(features)
    features = dedupe_features(features)
    features = filter_geojson_by_bbox(features, qwest, qsouth, qeast, qnorth)
    features = apply_display_labels_to_alerts(features)
    features.sort(key=draw_rank)

    gj = {
        "type": "FeatureCollection",
        "features": features,
        "source": "IEM valid-at-time polygons + official NWS active FF.W authority + AFOS archive text",
        "mode": "valid_at_utc",
        "at_utc": at,
        "ffw_valid_at_time": True,
        "latest_active_ffs_only": bool(deep_text),
        "future_ffs_products_excluded": True,
        "cancelled_expired_ffs_suppresses_base_warning": bool(deep_text),
        "latlon_parser": "NWS LAT...LON values treated as hundredths of degrees",
        "county_based_flood_advisories_filtered": True,
        "deep_ffw_ffs_text_check": bool(deep_text),
        "nws_active_ffw_authority": abs((now_utc() - valid_dt).total_seconds()) <= NWS_ACTIVE_FFW_LIVE_TOLERANCE_MINUTES * 60,
        "bbox_quantized_degrees": 0.25,
        "csv_etn_enrichment": "authoritative AFOS FF.W event-chain tags v13",
    }

    ALERT_CACHE[cache_key] = {
        "time": now,
        "geojson": gj,
    }

    trim_cache(ALERT_CACHE, ALERT_CACHE_MAX_ITEMS)
    return gj


def fetch_iem_polygon_alerts_at_token(token, west, south, east, north, deep_text=True):
    return fetch_iem_polygon_alerts_at_dt(token_to_datetime(token), west, south, east, north, deep_text=deep_text)



def _nws_cwa_list_from_service(force=False):
    now_epoch = time.time()
    with NWS_CWA_CACHE_LOCK:
        cached_items = NWS_CWA_LIST_CACHE.get("items")
        cached_time = float(NWS_CWA_LIST_CACHE.get("time") or 0.0)
        cached_error = str(NWS_CWA_LIST_CACHE.get("error") or "")

    if cached_items and not force and now_epoch - cached_time < NWS_CWA_CACHE_TTL_SECONDS:
        return list(cached_items)
    if not cached_items and cached_error and not force and now_epoch - cached_time < NWS_CWA_FAILURE_TTL_SECONDS:
        raise RuntimeError(cached_error)

    try:
        r = requests_get(
            NWS_CWA_FEATURE_URL + "/query",
            params={
                "where": "1=1",
                "outFields": "wfo,cwa,citystate,city,state,st,fullstaid",
                "returnGeometry": "false",
                "orderByFields": "wfo",
                "f": "json",
            },
            timeout=(6, 20),
        )
        r.raise_for_status()
        data = r.json()
        if data.get("error"):
            raise RuntimeError(data["error"].get("message") or str(data["error"]))

        items_by_wfo = {}
        for feature in data.get("features") or []:
            attrs = feature.get("attributes") or {}
            wfo = str(attrs.get("wfo") or attrs.get("cwa") or "").strip().upper()
            if not wfo:
                continue
            item = {
                "wfo": wfo,
                "cwa": str(attrs.get("cwa") or wfo).strip().upper(),
                "citystate": str(attrs.get("citystate") or "").strip(),
                "city": str(attrs.get("city") or "").strip(),
                "state": str(attrs.get("state") or "").strip(),
                "st": str(attrs.get("st") or "").strip(),
                "fullstaid": str(attrs.get("fullstaid") or "").strip(),
            }
            items_by_wfo[wfo] = item

        items = sorted(items_by_wfo.values(), key=lambda x: x["wfo"])
        if not items:
            raise RuntimeError("Official NOAA/NWS CWA service returned no WFO records.")

        with NWS_CWA_CACHE_LOCK:
            NWS_CWA_LIST_CACHE.update({"time": now_epoch, "items": list(items), "error": ""})
        return items
    except Exception as exc:
        with NWS_CWA_CACHE_LOCK:
            stale_items = NWS_CWA_LIST_CACHE.get("items")
            NWS_CWA_LIST_CACHE.update({"time": now_epoch, "error": str(exc)})
        if stale_items:
            return list(stale_items)
        raise


def _nws_cwa_geojson_feature(wfo, force=False):
    wfo = str(wfo or "").strip().upper()
    if not re.fullmatch(r"[A-Z0-9]{3}", wfo):
        raise ValueError(f"Invalid WFO/CWA id '{wfo}'.")

    now_epoch = time.time()
    with NWS_CWA_CACHE_LOCK:
        cached = dict(NWS_CWA_GEOMETRY_CACHE.get(wfo) or {})
    if cached.get("feature") and not force and now_epoch - float(cached.get("time") or 0.0) < NWS_CWA_CACHE_TTL_SECONDS:
        return cached["feature"]

    try:
        r = requests_get(
            NWS_CWA_FEATURE_URL + "/query",
            params={
                "where": f"wfo='{wfo}'",
                "outFields": "wfo,cwa,citystate,city,state,st,fullstaid",
                "returnGeometry": "true",
                "outSR": "4326",
                "f": "geojson",
            },
            timeout=(6, 25),
        )
        r.raise_for_status()
        data = r.json()
        features = data.get("features") or []
        if not features:
            raise FileNotFoundError(f"Official NOAA/NWS CWA geometry not found for WFO {wfo}.")
        feature = features[0]
        geom = feature.get("geometry") or {}
        if geom.get("type") not in ("Polygon", "MultiPolygon"):
            raise ValueError(f"Unsupported CWA geometry type for {wfo}: {geom.get('type')}")
        with NWS_CWA_CACHE_LOCK:
            NWS_CWA_GEOMETRY_CACHE[wfo] = {"time": now_epoch, "feature": feature, "error": ""}
        return feature
    except Exception as exc:
        if cached.get("feature"):
            return cached["feature"]
        with NWS_CWA_CACHE_LOCK:
            NWS_CWA_GEOMETRY_CACHE[wfo] = {"time": now_epoch, "feature": None, "error": str(exc)}
        raise


def _geojson_polygon_groups(geometry):
    geometry = geometry or {}
    gtype = geometry.get("type")
    coords = geometry.get("coordinates") or []
    if gtype == "Polygon":
        return [coords]
    if gtype == "MultiPolygon":
        return coords
    raise ValueError(f"Expected Polygon or MultiPolygon geometry, got {gtype!r}.")


def _geojson_geometry_bounds(geometry):
    lons = []
    lats = []
    for polygon in _geojson_polygon_groups(geometry):
        for ring in polygon:
            for coord in ring:
                if len(coord) >= 2:
                    lons.append(float(coord[0]))
                    lats.append(float(coord[1]))
    if not lons or not lats:
        raise ValueError("CWA geometry contains no coordinates.")
    return min(lons), min(lats), max(lons), max(lats)


def _geojson_geometry_mask(geometry, data):
    transform = data["dst_transform"]
    rows = np.arange(data["height"], dtype=np.float64) + 0.5
    cols = np.arange(data["width"], dtype=np.float64) + 0.5
    xs = transform.c + cols * transform.a
    ys = transform.f + rows * transform.e
    grid_x, grid_y = np.meshgrid(xs, ys)
    points = np.column_stack([grid_x.ravel(), grid_y.ravel()])
    union_mask = np.zeros((data["height"], data["width"]), dtype=bool)

    for polygon in _geojson_polygon_groups(geometry):
        if not polygon or len(polygon[0]) < 3:
            continue
        outer_lons = [float(c[0]) for c in polygon[0]]
        outer_lats = [float(c[1]) for c in polygon[0]]
        ox, oy = rio_transform("EPSG:4326", "EPSG:3857", outer_lons, outer_lats)
        poly_mask = MplPath(np.column_stack([ox, oy]), closed=True).contains_points(points, radius=1e-9)
        poly_mask = poly_mask.reshape(union_mask.shape)

        for hole in polygon[1:]:
            if len(hole) < 3:
                continue
            hole_lons = [float(c[0]) for c in hole]
            hole_lats = [float(c[1]) for c in hole]
            hx, hy = rio_transform("EPSG:4326", "EPSG:3857", hole_lons, hole_lats)
            hole_mask = MplPath(np.column_stack([hx, hy]), closed=True).contains_points(points, radius=1e-9)
            poly_mask &= ~hole_mask.reshape(union_mask.shape)

        union_mask |= poly_mask

    return union_mask


def area_average_for_geojson_geometry(param, product, requested_token, geometry, width=950, mean_mode="matched"):
    west, south, east, north = _geojson_geometry_bounds(geometry)
    param, pinfo = parameter_info(param, fallback_product=product)
    width = int(max(320, min(1800, width)))
    data = compute_parameter_array(param, product, requested_token, west, south, east, north, width)
    arr = data["arr_cfs"]
    mask = _geojson_geometry_mask(geometry, data)
    finite = mask & np.isfinite(arr)
    vals = arr[finite] if np.any(finite) else np.array([], dtype=np.float64)
    return summarize_area_average_values(vals, param, product, pinfo, data, {
        "west": west, "south": south, "east": east, "north": north, "width": width,
        "geometry_scope": "official_nws_cwa",
    }, mean_mode=mean_mode)


def max_for_geojson_geometry_parameter(param, product, requested_token, geometry, width=950, min_threshold=0.0):
    west, south, east, north = _geojson_geometry_bounds(geometry)
    param, pinfo = parameter_info(param, fallback_product=product)
    width = int(max(320, min(1800, width)))
    data = compute_parameter_array(param, product, requested_token, west, south, east, north, width)
    arr = data["arr_cfs"]
    raw = data["arr_m3s_per_km2"]
    mask = _geojson_geometry_mask(geometry, data)
    finite = mask & np.isfinite(arr)
    if min_threshold > 0:
        finite &= arr >= float(min_threshold)
    if not np.any(finite):
        return None, data.get("file_time_utc", ""), "official_cwa"

    work = np.where(finite, arr, np.nan)
    row, col = np.unravel_index(np.nanargmax(work), work.shape)
    lat, lon = pixel_latlon_from_webmercator_transform(data["dst_transform"], int(row), int(col))
    display_val = float(arr[row, col])
    native_val = float(raw[row, col]) if np.isfinite(raw[row, col]) else None
    value = {
        "lat": lat, "lon": lon,
        "value_m3s_per_km2": native_val,
        "value_cfs_per_smi": display_val,
        "display_value": display_val,
        "display_units": pinfo.get("units", "cfs/mi^2"),
        "native_value": native_val,
        "native_units": pinfo.get("native_units", "m^3/s/km^2"),
        "source_row": int(row), "source_col": int(col),
        "west": west, "south": south, "east": east, "north": north,
    }
    return value, data.get("file_time_utc", ""), "official_cwa"


@app.route("/api/cwa/list")
def api_cwa_list():
    try:
        items = _nws_cwa_list_from_service(force=False)
        return jsonify({"items": items, "count": len(items), "source": "official_noaa_nws_reference_map"})
    except Exception as exc:
        return jsonify({"error": str(exc), "items": []}), 502


@app.route("/api/cwa/prefetch")
def api_cwa_prefetch():
    wfo = str(request.args.get("wfo") or "").strip().upper()
    try:
        feature = _nws_cwa_geojson_feature(wfo, force=False)
        return jsonify({
            "ok": True,
            "wfo": wfo,
            "geometry_type": (feature.get("geometry") or {}).get("type"),
            "source": "official_noaa_nws_reference_map",
        })
    except Exception as exc:
        return jsonify({"ok": False, "wfo": wfo, "error": str(exc)}), 502


@app.route("/")
@app.route("/viewer")
def viewer():
    response = Response(VIEWER_HTML, mimetype="text/html")
    response.headers["Cache-Control"] = "no-store, max-age=0"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    return response



@app.route("/api/alarm/check", methods=["POST"])
def api_alarm_check():
    payload = request.get_json(silent=True) or {}
    scope = str(payload.get("scope") or "domain").lower()
    live_mode = bool(payload.get("live", False))
    requested_token = None if live_mode else (str(payload.get("time") or "").strip() or None)
    threshold = float(payload.get("threshold") or 0.0)
    width = int(payload.get("width") or 950)
    statistic = str(payload.get("statistic") or "max").strip().lower()
    mean_mode = normalize_mean_mode(payload.get("mean_mode", "matched"))
    cwa_id = str(payload.get("cwa") or "").strip().upper()
    include_diff = bool(payload.get("include_diff", True))

    try:
        param = "CREST"
        product = "CREST"
        vertices = payload.get("vertices") or []
        bounds = payload.get("bounds") or {}
        west = float(bounds.get("west", -91.95))
        south = float(bounds.get("south", 27.85))
        east = float(bounds.get("east", -88.25))
        north = float(bounds.get("north", 31.45))
        cwa_feature = None
        cwa_geometry = None
        cwa_label = ""

        # On the first LIVE CWA alarm check, fetch/cache the official CWA
        # geometry and the current CREST `.latest` object concurrently. This
        # avoids serial network waits before threshold detection.
        if live_mode and scope != "polygon" and cwa_id:
            with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
                cwa_future = executor.submit(_nws_cwa_geojson_feature, cwa_id, False)
                crest_future = executor.submit(get_latest_grib_direct, "CREST", False)
                cwa_feature = cwa_future.result()
                # Ensure the latest file prewarm completed; downstream array
                # computation reuses the cached object without redownloading.
                crest_future.result()
        elif scope != "polygon" and cwa_id:
            cwa_feature = _nws_cwa_geojson_feature(cwa_id)

        if cwa_feature:
            cwa_geometry = cwa_feature.get("geometry") or {}
            cwa_props = cwa_feature.get("properties") or {}
            cwa_place = str(cwa_props.get("citystate") or cwa_props.get("city") or "").strip()
            cwa_label = f"{cwa_id} — {cwa_place}" if cwa_place else cwa_id

        if scope == "polygon":
            max_payload, max_file_time, max_mode = max_for_polygon_parameter(
                param,
                product,
                requested_token,
                vertices,
                width=width,
                min_threshold=0.0,
            )
        elif cwa_geometry:
            max_payload, max_file_time, max_mode = max_for_geojson_geometry_parameter(
                param, product, requested_token, cwa_geometry, width=width, min_threshold=0.0
            )
        else:
            max_payload, max_file_time, max_mode = find_extreme_value_for_parameter(
                param,
                product,
                requested_token,
                west,
                south,
                east,
                north,
                width,
                min_cfs=0.0,
            )

        if max_payload is None:
            return jsonify({
                "found": False,
                "scope": scope,
                "param": param,
                "product": product,
                "threshold": threshold,
                "file_time_utc": max_file_time,
                "mode": max_mode,
                "alarm_statistic": statistic,
                "mean_mode": mean_mode,
                "cwa": cwa_id or None,
                "cwa_label": cwa_label or None,
            })

        max_value = max_payload.get("display_value", max_payload.get("value_cfs_per_smi"))
        lat = max_payload.get("lat")
        lon = max_payload.get("lon")
        file_time = max_file_time
        mode = max_mode
        alarm_value = float(max_value) if max_value is not None else None
        alarm_value_label = "Max Pixel"
        diff_10m = None
        diff_10m_file_time = ""
        diff_10m_trend = "unavailable"
        diff_10m_label = "10-min difference"
        area_payload = None

        if statistic in ("area", "area_average", "mean", "matched", "matched_mean"):
            statistic = "area_average"
            if scope == "polygon":
                area_payload = area_average_for_polygon(param, product, requested_token, vertices, mean_mode=mean_mode)
            elif cwa_geometry:
                area_payload = area_average_for_geojson_geometry(param, product, requested_token, cwa_geometry, width=width, mean_mode=mean_mode)
            else:
                area_payload = area_average_for_bounds(param, product, requested_token, west, south, east, north, width=width, mean_mode=mean_mode)

            if not area_payload.get("found") or area_payload.get("mean") is None:
                return jsonify({
                    "found": False,
                    "scope": scope,
                    "param": param,
                    "product": product,
                    "threshold": threshold,
                    "file_time_utc": area_payload.get("file_time_utc", file_time),
                    "mode": "area_average",
                    "alarm_statistic": statistic,
                    "mean_mode": mean_mode,
                })

            alarm_value = float(area_payload.get("mean"))
            alarm_value_label = area_payload.get("mean_label") or ("High-Value Weighted Avg" if mean_mode == "matched" else "Pure Average")
            file_time = area_payload.get("file_time_utc") or file_time
            mode = "area_average"
            diff_10m_label = f"{alarm_value_label} 10-min difference"

            current_area_token = area_payload.get("resolved_token") or requested_token
            if include_diff and current_area_token:
                prev_token = token_add_minutes(current_area_token, -10)
                try:
                    if scope == "polygon":
                        prev_area = area_average_for_polygon(param, product, prev_token, vertices, mean_mode=mean_mode)
                    elif cwa_geometry:
                        prev_area = area_average_for_geojson_geometry(param, product, prev_token, cwa_geometry, width=width, mean_mode=mean_mode)
                    else:
                        prev_area = area_average_for_bounds(param, product, prev_token, west, south, east, north, width=width, mean_mode=mean_mode)
                    if prev_area.get("found") and prev_area.get("mean") is not None:
                        diff_10m = float(alarm_value) - float(prev_area.get("mean"))
                        diff_10m_file_time = prev_area.get("file_time_utc", "")
                except Exception as diff_error:
                    diff_10m_file_time = f"unavailable: {diff_error}"
        else:
            statistic = "max"
            if include_diff and lat is not None and lon is not None:
                try:
                    # Anchor Δ10m to the actual resolved current CREST scan.
                    # This runs only for the deferred detail request so the
                    # threshold popup is never blocked by prior-scan lookup.
                    resolved_current_token = max_payload.get("resolved_token") or requested_token
                    diff_payload, diff_10m_file_time = sample_parameter_value(
                        "CREST_DIFF_10M",
                        "CREST",
                        resolved_current_token,
                        float(lat),
                        float(lon),
                    )
                    if diff_payload is not None and diff_payload.get("display_value") is not None:
                        diff_10m = float(diff_payload.get("display_value"))
                except Exception as diff_error:
                    diff_10m_file_time = f"unavailable: {diff_error}"

        if diff_10m is not None:
            if diff_10m > 0.5:
                diff_10m_trend = "increasing"
            elif diff_10m < -0.5:
                diff_10m_trend = "decreasing"
            else:
                diff_10m_trend = "steady"

        alarm_level = int(math.floor(float(alarm_value) / 100.0) * 100) if alarm_value is not None else 0

        response = {
            "found": True,
            "scope": scope,
            "param": param,
            "product": product,
            "threshold": threshold,
            "alarm_statistic": statistic,
            "alarm_value": float(alarm_value),
            "alarm_value_label": alarm_value_label,
            "alarm_level": alarm_level,
            "max_value": float(max_value),
            "display_units": max_payload.get("display_units", "cfs/mi^2"),
            "native_value": max_payload.get("native_value"),
            "native_units": max_payload.get("native_units", "m^3/s/km^2"),
            "lat": lat,
            "lon": lon,
            "file_time_utc": file_time,
            "mode": mode,
            "color_hex": streamflow_color_hex(alarm_value),
            "diff_10m": diff_10m,
            "diff_10m_units": "cfs/mi²",
            "diff_10m_label": diff_10m_label,
            "diff_10m_trend": diff_10m_trend,
            "diff_10m_file_time_utc": diff_10m_file_time,
            "diff_pending": not include_diff,
            "include_diff": include_diff,
            "mean_mode": mean_mode,
            "live_mode": live_mode,
            "resolved_token": (area_payload or {}).get("resolved_token") if area_payload else None,
            "cwa": cwa_id or None,
            "cwa_label": cwa_label or None,
            "cwa_source": "official_noaa_nws_reference_map" if cwa_geometry else None,
        }

        if area_payload:
            response.update({
                "pure_mean": area_payload.get("pure_mean"),
                "matched_mean": area_payload.get("matched_mean"),
                "mean_label": area_payload.get("mean_label"),
                "area_count": area_payload.get("count"),
                "area_min": area_payload.get("min"),
                "area_max": area_payload.get("max"),
                "high_value_weighted_method": area_payload.get("high_value_weighted_method"),
            })

        return jsonify(response)

    except Exception as e:
        return jsonify({
            "error": str(e),
            "scope": scope,
            "requested_time": requested_token,
            "alarm_statistic": statistic,
            "cwa": cwa_id or None,
        }), 500

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


def normalize_readout_trend_samples(samples):
    try:
        samples = int(samples or 4)
    except Exception:
        samples = 4
    return 7 if samples >= 7 else 4


def point_value_trend_for_parameter(param, product, requested_token, lat, lon, samples=4, step_minutes=10):
    param, pinfo = parameter_info(param, fallback_product=product)
    samples = normalize_readout_trend_samples(samples)
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
    samples = request.args.get("samples", 4)
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
    mean_mode = normalize_mean_mode(request.args.get("mean_mode", "matched"))

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
            mean_mode=mean_mode,
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


def area_average_trend_for_polygon(param, product, requested_token, vertices, samples=4, step_minutes=10, mean_mode="matched"):
    samples = normalize_readout_trend_samples(samples)
    step_minutes = max(1, min(int(step_minutes or 10), 60))

    base_token = effective_trend_base_token_for_parameter(param, product, requested_token)
    if not base_token:
        payload = area_average_for_polygon(param, product, requested_token, vertices, mean_mode=mean_mode)
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
            payload = area_average_for_polygon(param, product, token, vertices, mean_mode=mean_mode)
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
        latest_payload = area_average_for_polygon(param, product, base_token, vertices, mean_mode=mean_mode)

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
    samples = body.get("samples", 4)
    step_minutes = body.get("step_minutes", 10)
    mean_mode = normalize_mean_mode(body.get("mean_mode", "matched"))
    try:
        payload = area_average_trend_for_polygon(param, product, requested_token, vertices, samples=samples, step_minutes=step_minutes, mean_mode=mean_mode)
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
    mean_mode = normalize_mean_mode(body.get("mean_mode", "matched"))
    try:
        payload = area_average_for_polygon(param, product, requested_token, vertices, mean_mode=mean_mode)
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


@app.route("/api/live/latest")
def api_live_latest():
    raw_products = str(request.args.get("products") or request.args.get("product") or "CREST")
    force = str(request.args.get("force") or "0").lower() in ("1", "true", "yes")

    requested_products = []
    for raw in raw_products.split(","):
        name = raw.strip().upper()
        if not name:
            continue
        try:
            name, _ = product_info(name)
        except Exception:
            continue
        if name not in requested_products:
            requested_products.append(name)

    if not requested_products:
        requested_products = ["CREST"]

    results = {}
    max_workers = max(1, min(4, len(requested_products)))
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_map = {
            executor.submit(probe_latest_product, product, force): product
            for product in requested_products
        }
        for future in concurrent.futures.as_completed(future_map):
            product = future_map[future]
            try:
                results[product] = future.result()
            except Exception as exc:
                # Defensive only: probe_latest_product already converts network
                # failures into stale last-known-good responses.
                token, source = _latest_known_token_without_network(product)
                results[product] = {
                    "product": product,
                    "token": token,
                    "label": token_to_label(token) if token else "Latest token unavailable",
                    "source": source or "unavailable",
                    "stale": True,
                    "backoff_active": True,
                    "last_error": f"{type(exc).__name__}: {exc}",
                }

    tokens = [
        detail.get("token")
        for detail in results.values()
        if detail.get("token") and re.match(r"^\d{8}-\d{6}$", str(detail.get("token")))
    ]
    latest_token = max(tokens) if tokens else None

    return jsonify({
        "products": results,
        "latest_token": latest_token,
        "latest_label": token_to_label(latest_token) if latest_token else "",
        "checked_utc": now_utc_iso(),
    })


@app.route("/api/archive/list")
def api_archive_list():
    product = request.args.get("product", DEFAULT_PRODUCT)
    force = str(request.args.get("force") or "0").lower() in ("1", "true", "yes")

    try:
        product, product_meta = product_info(product)
        if force:
            # Preserve stale last-known-good remote listings on force refresh;
            # only expire the success timestamp so a fresh attempt is made.
            cached_remote = REMOTE_LIST_CACHE.get(product)
            if cached_remote:
                cached_remote["time"] = 0.0
            S3_ARCHIVE_LIST_CACHE.pop((product, now_utc().strftime("%Y%m%d")), None)

        local_items = list_local_archive(product)

        try:
            remote_items = list_remote_files(product, limit=ARCHIVE_REMOTE_LIST_LIMIT)
        except Exception:
            cached_remote = REMOTE_LIST_CACHE.get(product) or {}
            remote_items = list(cached_remote.get("items") or [])[:ARCHIVE_REMOTE_LIST_LIMIT]

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
        "products": PRODUCTS,
        "parameters": PARAMETERS,
        "default_product": DEFAULT_PRODUCT,
        "cache_dir": CACHE_DIR,
        "archive_dir": ARCHIVE_DIR,
        "units": "cfs/mi^2",
        "conversion_from_m3s_per_km2_to_cfs_per_mi2": M3S_PER_KM2_TO_CFS_PER_SQMI,
        "legend_breaks_cfs_per_mi2": [0, 100, 200, 400, 600, 1000, 2000],
        "alerts_source": "IEM watchwarn.py valid-at-time polygons + AFOS retrieve.py FFW/FFS text for authoritative VTEC/impact tags",
        "alert_speed_mode": "Both panels share one alert fetch; alert bboxes are quantized; AFOS 503s are negative-cached; deep text check can be disabled in the GUI.",
        "ffw": "FF.W storm-based valid-at-time polygons",
        "ffs_followups": "Latest FFS at archive/current time only; CAN/EXP suppresses older FFS and base warning",
        "draw_order": "FA.Y bottom, FFW middle, considerable/emergency/latest FFS top",
        "difference_scale": "CREST Δ10m uses -300 to +300 cfs/mi^2; RainRate Δ10m uses -10 to +10 in/hr with the same normalized white-purple-cyan-blue-black-red-magenta-orange-white palette. Other difference products retain their existing scales.",
        "archive_fallback": "Selected historical times use the NOAA AWS MRMS archive; live/current times use the NCEP directory, with local archive files preferred when present.",
        "latlon_parser": "NWS LAT...LON values parsed as hundredths of degrees",
        "flood_advisory": "FA.Y fetched polygon-only where available; county/parish-like advisories filtered",
        "opacity_default": "100 percent for streamflow pixels",
        "warning_labels": "Tooltips show AFOS-derived FF.W/FF.S VTEC number plus BASE, CONSIDERABLE, EMERGENCY, or ADVISORY status when available; click polygons for details",
        "max_pixel_marker": "Optional current-view max streamflow pixel search via /api/max; difference parameters mark largest absolute difference",
        "area_average_tool": "Optional mirrored Leaflet free-draw polygon tool; /api/area_average_polygon_trend returns panel-specific mean/min/max plus a compact 7-sample/60-minute mean trend sparkline with selected-time marker",
        "alarm_notification": "Optional CREST live-scan alarm, default OFF; /api/alarm/check checks max or selected average over an exact official NOAA/NWS WFO CWA polygon or a drawn polygon, returns exact streamflow palette color, 10-minute difference information, and alerts only when a higher 100-level threshold is reached.",
            "live_freshness": "One-minute browser poll uses /api/live/latest lightweight `.latest` HEAD probes for active products, retains last-known-good tokens, exponentially backs off failures, and refreshes only panels whose source products changed.",
        "two_panel_layout": "Left and right panel parameter selections persist in browser localStorage; maps pan and zoom together",
        "derived_parameters": {
            "COMPUTED_P": "Adjusted exponential significance parameter combining current CREST and CREST 10-minute rate of change; exact CMUSF_Auto.py formulation clipped to 0-5000 P",
            "CREST_DIFF_10M": "Current/selected CREST minus the previous CREST update 10 minutes earlier; displayed from -300 to +300 cfs/mi^2 with the dedicated rate-change palette",
            "RAINRATE_DIFF_10M": "Current/selected MRMS instantaneous rain rate minus the instantaneous rain rate 10 minutes earlier; displayed from -10 to +10 in/hr using the same normalized rate-change palette",
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

    app.run(host="0.0.0.0", port=8080, debug=False)
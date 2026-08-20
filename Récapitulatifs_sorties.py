"""
=========================================================
  ATLAS PERSONNEL GARMIN — Application Web & Cartographie
=========================================================
Génère une carte Folium dynamique avec serveur web local.
Inclus : Wi-Fi, Graphiques (Chart.js), Focus plein écran,
Métriques WorldTour (VAM, Pente, Suffer Score, Maillots),
Palmarès filtrable par sport ET par année, téléchargement GPX.
NOUVEAUTÉ : Carte Satellite Hybride (avec noms des villes/routes) !
NOUVEAUTÉ SWISSTOPO : Altimétrie officielle (MNT swissALTI3D) recalculée
pour chaque montée + identification automatique des cols suisses via la
toponymie officielle (swissNAMES3D), avec mise en cache locale fiable.
AUTOMATISATION : Génération et Push sur GitHub des versions Publique ET Privée.
"""

import os
import sys
import json
import shutil
import base64
import time
import math
import socket
import xml.etree.ElementTree as ET
import subprocess
from datetime import datetime
import threading
import webbrowser
import http.server
import socketserver
import urllib.parse
import mimetypes

import folium
from folium import plugins
from garminconnect import Garmin
from dotenv import load_dotenv
import requests

# =========================================================
# 📂 CONFIGURATION & DOSSIERS
# =========================================================
load_dotenv(r"C:\Users\gogni\Garmin.env")

DOSSIER_BASE = r"C:\Users\gogni\Documents\Code Garmin\Atlas"
DOSSIER_PHOTOS = os.path.join(DOSSIER_BASE, "photos")
DOSSIER_GPX = os.path.join(DOSSIER_BASE, "gpx")
DB_PATH = os.path.join(DOSSIER_BASE, "atlas_db.json")

MAP_HTML_PATH = os.path.join(DOSSIER_BASE, "atlas_prive.html")
MAP_HTML_PUBLIC_PATH = os.path.join(DOSSIER_BASE, "ma_carte_publique.html")

for dossier in [DOSSIER_BASE, DOSSIER_PHOTOS, DOSSIER_GPX]:
    if not os.path.exists(dossier):
        os.makedirs(dossier)

db_lock = threading.RLock()

# 🏷️ Titre affiché dans l'onglet du navigateur / la carte.
APP_TITLE = "Atlas Cycling — Explorateur de Sorties"

# =========================================================
# ❤️ PARAMÈTRES CHARGE D'ENTRAÎNEMENT (Suffer Score)
# =========================================================
FC_REPOS = 50

# =========================================================
# 🌍 CONFIGURATION DE LA VERSION PUBLIQUE
# =========================================================
PUBLIC_CONFIG = {
    "masquer_palmares": True,
    "masquer_maillots": True,
    "masquer_fc_calories": True,
    "masquer_vitesse": False,
    "masquer_commentaires": False,
    "trim_debut_m": 500,
    "trim_fin_m": 500,
}

# =========================================================
# 🎨 PARAMÉTRAGE DES SPORTS & STYLES
# =========================================================
SPORTS_CONFIG = {
    "vtt": {"nom": "VTT", "couleur": "#2ca02c", "icone": "bicycle"},
    "route": {"nom": "Route", "couleur": "#1f77b4", "icone": "road"},
    "gravel": {"nom": "Gravel", "couleur": "#9467bd", "icone": "leaf"},
    "randonnee": {"nom": "Randonnée", "couleur": "#ff7f0e", "icone": "tree-conifer"},
    "ski": {"nom": "Ski de Fond", "couleur": "#17becf", "icone": "asterisk"},
}

# =========================================================
# 🇨🇭 SWISSTOPO — API OFFICIELLES (MNT swissALTI3D + toponymie swissNAMES3D)
# =========================================================
SWISSTOPO_PROFILE_URL = "https://api3.geo.admin.ch/rest/services/profile.json"
SWISSTOPO_IDENTIFY_URL = "https://api3.geo.admin.ch/rest/services/ech/MapServer/identify"
SWISS_BBOX = {"lat_min": 45.75, "lat_max": 47.95, "lon_min": 5.85, "lon_max": 10.65}

# =========================================================
# 🌍 RELAIS MONDIAL — Open Topo Data (MNT SRTM/ASTER, hors de Suisse)
# =========================================================
OPENTOPODATA_URL = "https://api.opentopodata.org/v1/mapzen"
OPENTOPODATA_BATCH = 100
COLS_CACHE_PATH = os.path.join(DOSSIER_BASE, "swiss_cols_cache.json")

def is_in_switzerland(lat, lon):
    return (SWISS_BBOX["lat_min"] <= lat <= SWISS_BBOX["lat_max"] and
            SWISS_BBOX["lon_min"] <= lon <= SWISS_BBOX["lon_max"])

def load_cols_cache():
    with db_lock:
        if os.path.exists(COLS_CACHE_PATH):
            try:
                with open(COLS_CACHE_PATH, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                return {}
        return {}

def save_cols_cache(cache):
    with db_lock:
        with open(COLS_CACHE_PATH, "w", encoding="utf-8") as f:
            json.dump(cache, f, indent=2, ensure_ascii=False)

def wgs84_to_lv95(lat, lon):
    lat_sec = lat * 3600.0
    lon_sec = lon * 3600.0
    phi = (lat_sec - 169028.66) / 10000.0
    lam = (lon_sec - 26782.5) / 10000.0
    e = (2600072.37 + 211455.93 * lam - 10938.51 * lam * phi - 0.36 * lam * (phi ** 2) - 44.54 * (lam ** 3))
    n = (1200147.07 + 308807.95 * phi + 3745.25 * (lam ** 2) + 76.63 * (phi ** 2) - 194.56 * (lam ** 2) * phi + 119.79 * (phi ** 3))
    return e, n

def fetch_swisstopo_profile(coords):
    if not coords or len(coords) < 2: return None
    if not is_in_switzerland(coords[0][0], coords[0][1]): return None
    cum_dist = [0.0]
    for i in range(1, len(coords)): cum_dist.append(cum_dist[-1] + haversine_m(coords[i - 1], coords[i]))
    total_dist = cum_dist[-1]
    if total_dist <= 0: return None
    pts = coords
    if len(pts) > 2000:
        step = math.ceil(len(pts) / 2000)
        pts = pts[::step]
        if pts[-1] != coords[-1]: pts = pts + [coords[-1]]
    lv95_pts = [wgs84_to_lv95(p[0], p[1]) for p in pts]
    geom = {"type": "LineString", "coordinates": [[round(e, 2), round(n, 2)] for e, n in lv95_pts]}
    params = {"geom": json.dumps(geom), "sr": 2056, "nb_points": min(max(len(pts) * 2, 200), 2500)}
    try:
        r = requests.post(SWISSTOPO_PROFILE_URL, data=params, timeout=25)
        r.raise_for_status()
        data = r.json()
        if not data or len(data) < 2: return None
        profile_dist, profile_ele = [], []
        for pt in data:
            d = pt.get("dist")
            alts = pt.get("alts", {})
            alt = alts.get("COMB", alts.get("DTM2", alts.get("DTM25")))
            if d is None or alt is None: continue
            profile_dist.append(d)
            profile_ele.append(alt)
        if len(profile_dist) < 2: return None
        result_eles = []
        j = 0
        for d in cum_dist:
            while j < len(profile_dist) - 2 and profile_dist[j + 1] < d: j += 1
            d0, d1 = profile_dist[j], profile_dist[j + 1]
            e0, e1 = profile_ele[j], profile_ele[j + 1]
            if d1 == d0: result_eles.append(e0)
            else:
                t = max(0.0, min(1.0, (d - d0) / (d1 - d0)))
                result_eles.append(round(e0 + t * (e1 - e0), 1))
        return result_eles
    except Exception as e:
        print(f"   ⚠️ Profil swisstopo indisponible : {e}")
        return None

def fetch_global_elevation_profile(coords):
    if not coords or len(coords) < 2: return None
    cum_dist = [0.0]
    for i in range(1, len(coords)): cum_dist.append(cum_dist[-1] + haversine_m(coords[i - 1], coords[i]))
    total_dist = cum_dist[-1]
    if total_dist <= 0: return None
    pts = coords
    max_pts = 300
    if len(pts) > max_pts:
        step = math.ceil(len(pts) / max_pts)
        pts = pts[::step]
        if pts[-1] != coords[-1]: pts = pts + [coords[-1]]
    profile_ele = []
    try:
        for i in range(0, len(pts), OPENTOPODATA_BATCH):
            batch = pts[i:i + OPENTOPODATA_BATCH]
            locations = "|".join(f"{p[0]:.5f},{p[1]:.5f}" for p in batch)
            r = requests.get(OPENTOPODATA_URL, params={"locations": locations}, timeout=20)
            r.raise_for_status()
            data = r.json()
            if data.get("status") != "OK": return None
            for res in data.get("results", []): profile_ele.append(res.get("elevation"))
            if i + OPENTOPODATA_BATCH < len(pts): time.sleep(1.05)
        if len(profile_ele) != len(pts) or any(e is None for e in profile_ele): return None
        pts_cum_dist = [0.0]
        for i in range(1, len(pts)): pts_cum_dist.append(pts_cum_dist[-1] + haversine_m(pts[i - 1], pts[i]))
        result_eles = []
        j = 0
        for d in cum_dist:
            while j < len(pts_cum_dist) - 2 and pts_cum_dist[j + 1] < d: j += 1
            d0, d1 = pts_cum_dist[j], pts_cum_dist[j + 1]
            e0, e1 = profile_ele[j], profile_ele[j + 1]
            if d1 == d0: result_eles.append(e0)
            else:
                t = max(0.0, min(1.0, (d - d0) / (d1 - d0)))
                result_eles.append(round(e0 + t * (e1 - e0), 1))
        return result_eles
    except Exception as e:
        print(f"   ⚠️ Profil mondial indisponible : {e}")
        return None

def identify_swiss_col(lat, lon, cache):
    key = f"{round(lat, 4)},{round(lon, 4)}"
    if key in cache: return cache[key]
    if not is_in_switzerland(lat, lon):
        cache[key] = None
        return None
    result = None
    try:
        e, n = wgs84_to_lv95(lat, lon)
        params = {"geometry": f"{e:.2f},{n:.2f}", "geometryType": "esriGeometryPoint", "layers": "all:ch.swisstopo.swissnames3d", "mapExtent": "0,0,100,100", "imageDisplay": "100,100,100", "tolerance": 300, "sr": 2056, "lang": "fr", "returnGeometry": "false"}
        r = requests.get(SWISSTOPO_IDENTIFY_URL, params=params, timeout=4)
        r.raise_for_status()
        data = r.json()
        for feat in data.get("results", []):
            attrs = feat.get("attributes", {})
            kind = str(attrs.get("objektart", "")).lower()
            name = attrs.get("name") or attrs.get("label")
            if name and "pass" in kind:
                result = {"name": name}
                break
        if result: print(f"   🇨🇭 Col swisstopo : {result['name']}")
    except Exception: result = None
    cache[key] = result
    return result

def compute_climbs_for_activity(coords, elevations, swiss_eles, global_eles, sport_key):
    used_swisstopo_ele, used_global_ele = False, False
    stat_elevations = elevations
    if swiss_eles and len(swiss_eles) == len(coords):
        stat_elevations = swiss_eles
        used_swisstopo_ele = True
    elif global_eles and len(global_eles) == len(coords):
        stat_elevations = global_eles
        used_global_ele = True
    window = 4 if sport_key in ['vtt', 'gravel'] else 2
    n_points = len(stat_elevations)
    smoothed = []
    for j in range(n_points):
        start_j, end_j = max(0, j - window), min(n_points, j + window + 1)
        smoothed.append(sum(stat_elevations[start_j:end_j]) / (end_j - start_j))
    climbs = find_climbs(coords, smoothed, sport_key)
    return smoothed, climbs, used_swisstopo_ele, used_global_ele

def warm_col_cache_for_activity(coords, elevations, swiss_eles, global_eles, sport_key, cache):
    try:
        _, climbs, _, _ = compute_climbs_for_activity(coords, elevations, swiss_eles, global_eles, sport_key)
        for c in climbs: identify_swiss_col(coords[c['end']][0], coords[c['end']][1], cache)
    except Exception: pass

def load_db():
    with db_lock:
        if os.path.exists(DB_PATH):
            with open(DB_PATH, "r", encoding="utf-8") as f: return json.load(f)
        return {"last_sync": None, "activities": {}}

def save_db(db):
    with db_lock:
        with open(DB_PATH, "w", encoding="utf-8") as f: json.dump(db, f, indent=2, ensure_ascii=False)

def get_garmin_client():
    email = os.getenv('GARMIN_EMAIL')
    password = os.getenv('GARMIN_PASSWORD')
    client = Garmin(email, password)
    client.login()
    return client

def get_local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(('10.255.255.255', 1))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception: return '127.0.0.1'

def classify_activity(activity):
    t = (activity.get('activityType', {}).get('typeKey', '') or '').lower()
    if 'e_bike' in t or 'ebike' in t: return None 
    if any(x in t for x in ['mountain', 'vtt', 'enduro', 'downhill', 'dirt']): return "vtt"
    elif 'gravel' in t: return "gravel"
    elif any(x in t for x in ['cycling', 'road_biking']): return "route"
    elif any(x in t for x in ['hiking', 'walking', 'mountaineering']): return "randonnee"
    elif any(x in t for x in ['cross_country_skiing', 'skate_skiing']): return "ski"
    return None

def extract_gpx_data(gpx_bytes):
    coords, elevations = [], []
    try:
        root = ET.fromstring(gpx_bytes)
        for elem in root.iter():
            if elem.tag.endswith('trkpt'):
                lat_str = elem.attrib.get('lat')
                lon_str = elem.attrib.get('lon')
                if not lat_str or not lon_str: continue
                lat = float(lat_str)
                lon = float(lon_str)
                ele = None
                for child in elem.iter():
                    if child.tag.endswith('ele') and child.text:
                        try:
                            ele = float(child.text)
                            break
                        except ValueError: pass
                if ele is not None and ele != 0.0:
                    coords.append([lat, lon])
                    elevations.append(ele)
        if not coords: return [], []
        return coords[::5], elevations[::5]
    except Exception: return [], []

def format_duration(seconds):
    if not seconds: return "N/A"
    h = int(seconds // 3600)
    m = int((seconds % 3600) // 60)
    return f"{h}h {m:02d}min" if h > 0 else f"{m} min"

def calculate_suffer_score(avg_hr, duration_s, fc_repos, fc_max):
    try: avg_hr = float(avg_hr)
    except (TypeError, ValueError): return 0
    if not avg_hr or not duration_s or fc_max <= fc_repos: return 0
    dur_min = duration_s / 60.0
    hr_ratio = (avg_hr - fc_repos) / (fc_max - fc_repos)
    hr_ratio = max(0.0, min(hr_ratio, 1.15))
    return round(dur_min * hr_ratio * 0.64 * math.exp(1.92 * hr_ratio))

def haversine_m(p1, p2):
    R = 6371000.0
    lat1, lon1 = math.radians(p1[0]), math.radians(p1[1])
    lat2, lon2 = math.radians(p2[0]), math.radians(p2[1])
    a = math.sin((lat2-lat1)/2)**2 + math.cos(lat1)*math.cos(lat2)*math.sin((lon2-lon1)/2)**2
    return 2 * R * math.asin(math.sqrt(min(1.0, a)))

def trim_track_endpoints(coords, elevations, trim_start_m=0, trim_end_m=0):
    if (not trim_start_m and not trim_end_m) or not coords or len(coords) < 3: return coords, elevations
    n = len(coords)
    start_idx = 0
    cum = 0.0
    while start_idx < n - 1 and cum < trim_start_m:
        cum += haversine_m(coords[start_idx], coords[start_idx + 1])
        start_idx += 1
    end_idx = n - 1
    cum = 0.0
    while end_idx > start_idx and cum < trim_end_m:
        cum += haversine_m(coords[end_idx], coords[end_idx - 1])
        end_idx -= 1
    if start_idx >= end_idx: return coords, elevations
    return coords[start_idx:end_idx + 1], elevations[start_idx:end_idx + 1] if elevations else elevations

def save_raw_gpx(act_id, gpx_bytes):
    try:
        path = os.path.join(DOSSIER_GPX, f"{act_id}.gpx")
        with open(path, "wb") as f: f.write(gpx_bytes)
        return f"gpx/{act_id}.gpx"
    except Exception: return None

def generate_svg_elevation(elevations, color):
    if not elevations or len(elevations) < 2: return ""
    w, h = 350, 70
    min_e, max_e = min(elevations), max(elevations)
    diff = max_e - min_e if max_e > min_e else 1
    pts = [f"{(i/(len(elevations)-1))*w:.1f},{h - ((ele-min_e)/diff)*h:.1f}" for i, ele in enumerate(elevations)]
    poly_pts = pts + [f"{w},{h}", f"0,{h}"]
    return f'''
    <div style="margin-top:15px; border:1px solid #e9ecef; border-radius:8px; background:#fdfdfd; padding:6px; box-shadow: inset 0 1px 3px rgba(0,0,0,0.05);">
        <div style="font-size:11px; color:#555; text-align:center; font-weight:bold; margin-bottom:4px; letter-spacing:1px; text-transform:uppercase;">Profil Altimétrique Global</div>
        <svg width="100%" height="{h}px" viewBox="0 0 {w} {h}" preserveAspectRatio="none">
            <polygon points="{" ".join(poly_pts)}" fill="{color}" opacity="0.15"/>
            <polyline points="{" ".join(pts)}" fill="none" stroke="{color}" stroke-width="2.5"/>
            <text x="3" y="12" fill="#555" font-size="10" font-weight="bold">{int(max_e)}m</text>
            <text x="3" y="{h - 4}" fill="#555" font-size="10" font-weight="bold">{int(min_e)}m</text>
        </svg>
    </div>
    '''

def get_vv_color(grad):
    if grad <= 2.0: return "#53a8cf"
    elif grad <= 4.0: return "#5ebf6b"
    elif grad <= 6.0: return "#d6cc1f"
    elif grad <= 9.0: return "#e57b27"
    elif grad <= 12.0: return "#d62728"
    else: return "#000000"

def get_climb_category(dist_km, grad):
    score = dist_km * 1000 * grad
    if score >= 120000: return "HC"
    elif score >= 80000: return "Cat 1"
    elif score >= 50000: return "Cat 2"
    elif score >= 30000: return "Cat 3"
    elif score >= 15000: return "Cat 4"
    else: return "NC"

def find_climbs(coords, elevations, sport_key):
    climbs = []
    if not coords or not elevations or len(coords) < 10: return climbs
    if sport_key == "vtt": descent_tol, min_dist, min_gain, min_grad = 60, 250, 25, 1.0
    elif sport_key == "gravel": descent_tol, min_dist, min_gain, min_grad = 50, 300, 30, 1.0
    else: descent_tol, min_dist, min_gain, min_grad = 40, 400, 30, 1.5
    
    in_climb, start_idx, max_ele_idx, min_ele = False, 0, 0, elevations[0]
    for i in range(1, len(coords)):
        ele = elevations[i]
        if not in_climb:
            if ele > min_ele + 5:
                in_climb = True
                start_idx = i - 1
                max_ele_idx = i
            elif ele < min_ele: min_ele = ele
        else:
            if ele >= elevations[max_ele_idx]: max_ele_idx = i
            if elevations[max_ele_idx] - ele > descent_tol or i == len(coords) - 1:
                dist = sum(haversine_m(coords[j], coords[j+1]) for j in range(start_idx, max_ele_idx))
                gain = elevations[max_ele_idx] - elevations[start_idx]
                if dist >= min_dist and gain >= min_gain:
                    grad = (gain / dist) * 100
                    if grad >= min_grad:
                        dist_km = round(dist/1000, 2)
                        climbs.append({'start': start_idx, 'end': max_ele_idx, 'dist': dist_km, 'gain': int(gain), 'grad': round(grad, 1), 'cat': get_climb_category(dist_km, grad)})
                in_climb, min_ele = False, ele
    return climbs

def generate_vv_climb_html(climb, coords, elevations, climb_id, col_match=None):
    start, end = climb['start'], climb['end']
    c_coords, c_eles = coords[start:end+1], elevations[start:end+1]
    w, h = 350, 40
    if len(c_eles) == 0: return ""
    min_e, max_e = min(c_eles), max(c_eles)
    diff = max_e - min_e if max_e > min_e else 1
    lines_html = ""
    cum_dists = [0]
    for i in range(len(c_coords)-1): cum_dists.append(cum_dists[-1] + haversine_m(c_coords[i], c_coords[i+1]))
    if cum_dists[-1] == 0: return ""
    
    for i in range(len(c_coords)-1):
        d1, d2 = cum_dists[i], cum_dists[i+1]
        e1, e2 = c_eles[i], c_eles[i+1]
        x1, x2 = (d1 / cum_dists[-1]) * w, (d2 / cum_dists[-1]) * w
        y1, y2 = h - ((e1 - min_e) / diff) * h, h - ((e2 - min_e) / diff) * h
        dist_seg = d2 - d1
        gain_seg = e2 - e1
        grad = (gain_seg / dist_seg * 100) if dist_seg > 0 else 0
        if grad < 0: grad = 0
        color = get_vv_color(grad)
        lines_html += f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{color}" stroke-width="4" stroke-linecap="round"/>'
        
    grad_color = get_vv_color(climb['grad'])
    title_text = col_match['name'] if col_match else "Montée non nommée"
    title_suffix = ' <span style="background:#1f77b4;color:#fff;font-size:8px;font-weight:800;padding:1px 4px;border-radius:2px;vertical-align:middle;">🇨🇭</span>' if col_match else ""

    return f'''
    <div onclick="openClimbPanel('{climb_id}')" class="vv-row" style="background:#fff; border:1px solid var(--vv-line); border-radius:4px; margin-bottom:6px; padding:8px 10px;">
        <span class="vv-chip" style="background:#14181c; min-width:34px; justify-content:center;">{climb['cat']}</span>
        <div class="vv-row-main">
            <div class="vv-row-title" id="title-preview-{climb_id}" style="font-family:'Oswald','Segoe UI',sans-serif; text-transform:uppercase; letter-spacing:0.2px;">{title_text}{title_suffix}</div>
            <svg width="120" height="16" viewBox="0 0 {w} {h}" preserveAspectRatio="none" style="margin-top:3px; display:block;">{lines_html}</svg>
        </div>
        <div class="vv-row-stats">
            <span>{climb['dist']}<small>km</small></span>
            <span>+{climb['gain']}<small>m+</small></span>
            <span style="color:{grad_color};">{climb['grad']}%<small>pente</small></span>
        </div>
    </div>
    '''

def generate_1km_segments_svg(c_coords, c_eles, dist_km, gain_m, cat):
    cum_dists = [0]
    for i in range(len(c_coords)-1): cum_dists.append(cum_dists[-1] + haversine_m(c_coords[i], c_coords[i+1]))
    total_dist = cum_dists[-1]
    if total_dist == 0: return ""
    min_e, max_e = min(c_eles), max(c_eles)
    diff = max_e - min_e if max_e > min_e else 1

    w, h = 900, 300 
    chunks = []
    current_chunk_start_idx = 0
    current_chunk_target = 1000

    for i in range(len(cum_dists)):
        if cum_dists[i] >= current_chunk_target or i == len(cum_dists) - 1:
            chunk_dist = cum_dists[i] - cum_dists[current_chunk_start_idx]
            chunk_gain = c_eles[i] - c_eles[current_chunk_start_idx]
            grad = (chunk_gain / chunk_dist * 100) if chunk_dist > 0 else 0
            chunks.append({
                'start_d': cum_dists[current_chunk_start_idx], 'end_d': cum_dists[i],
                'start_e': c_eles[current_chunk_start_idx], 'end_e': c_eles[i],
                'grad': max(0, grad)
            })
            current_chunk_start_idx = i
            current_chunk_target += 1000

    svg_elements = []
    for i in range(5):
        gy = h - (i/4)*h
        svg_elements.append(f'<line x1="0" y1="{gy:.1f}" x2="{w}" y2="{gy:.1f}" stroke="#ddd" stroke-width="1" stroke-dasharray="4,4"/>')

    for c in chunks:
        x1, x2 = (c['start_d'] / total_dist) * w, (c['end_d'] / total_dist) * w
        y1, y2 = h - ((c['start_e'] - min_e) / diff) * h, h - ((c['end_e'] - min_e) / diff) * h
        color = get_vv_color(c['grad'])
        svg_elements.append(f'<polygon points="{x1:.1f},{y1:.1f} {x2:.1f},{y2:.1f} {x2:.1f},{h} {x1:.1f},{h}" fill="{color}" opacity="0.4"/>')
        svg_elements.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{color}" stroke-width="6" stroke-linecap="round"/>')
        mid_x, mid_y = (x1 + x2) / 2, (y1 + y2) / 2 - 15
        if (x2 - x1) > 25:
            svg_elements.append(f'<text x="{mid_x:.1f}" y="{mid_y:.1f}" fill="{color}" font-size="16" font-weight="900" text-anchor="middle" font-family="Arial" style="text-shadow: 1px 1px 0 #fff, -1px -1px 0 #fff, 1px -1px 0 #fff, -1px 1px 0 #fff;">{c["grad"]:.1f}%</text>')
        if c['end_d'] <= total_dist:
            km_val = round(c['end_d']/1000, 1)
            if km_val.is_integer(): km_val = int(km_val)
            svg_elements.append(f'<line x1="{x2:.1f}" y1="{h}" x2="{x2:.1f}" y2="{h+5}" stroke="#999" stroke-width="2"/>')
            if (x2 - x1) > 20: 
                svg_elements.append(f'<text x="{x2:.1f}" y="{h+20}" fill="#666" font-size="13" font-weight="bold" text-anchor="middle" font-family="Arial">{km_val}km</text>')

    html_out = f'''
    <div style="flex-grow:1; display:flex; flex-direction:column; justify-content:space-between; position:relative; height:100%;">
        <div class="vv-stat-grid" style="grid-template-columns: repeat(4, 1fr); margin-bottom:20px;">
            <div class="vv-stat-cell" style="text-align:center;"><div class="vv-label" style="margin-bottom:4px;">Catégorie</div><div class="vv-stat-val" style="color:#d62728; font-size:19px;">{cat}</div></div>
            <div class="vv-stat-cell" style="text-align:center;"><div class="vv-label" style="margin-bottom:4px;">Distance</div><div class="vv-stat-val" style="color:#1f77b4; font-size:19px;">{dist_km}<span style="font-size:11px;">km</span></div></div>
            <div class="vv-stat-cell" style="text-align:center;"><div class="vv-label" style="margin-bottom:4px;">Dénivelé</div><div class="vv-stat-val" style="color:#ff7f0e; font-size:19px;">+{gain_m}<span style="font-size:11px;">m</span></div></div>
            <div class="vv-stat-cell" style="text-align:center;"><div class="vv-label" style="margin-bottom:4px;">Sommet</div><div class="vv-stat-val" style="color:#333; font-size:19px;">{max_e:.0f}<span style="font-size:11px;">m</span></div></div>
        </div>
        <div style="flex-grow:1; position:relative; min-height: 250px;">
            <div class="zoom-btn" onclick="zoomClimbSVG()" style="position:absolute; bottom:15px; right:15px; background:#fff; border:2px solid #1f77b4; color:#1f77b4; border-radius:8px; cursor:pointer; padding:6px 12px; font-size:14px; font-weight:bold; box-shadow:0 2px 4px rgba(0,0,0,0.15); z-index:10; font-family:'Segoe UI',sans-serif;">🔍 Agrandir</div>
            <svg width="100%" height="100%" viewBox="-20 -20 {w+40} {h+40}" preserveAspectRatio="none" style="overflow:visible;">{ "".join(svg_elements) }</svg>
        </div>
    </div>
    '''
    return html_out

# =========================================================
# 1️⃣ SYNCHRONISATION GARMIN
# =========================================================
def sync_garmin():
    db = load_db()
    swiss_cols_cache = load_cols_cache() 
    n_cols_warmed = 0
    print("\n🔄 Connexion à Garmin Connect...")
    try:
        client = get_garmin_client()
    except Exception as e:
        print(f"❌ Erreur connexion : {e}")
        return

    print("📥 Récupération des activités...")
    start, limit, n_added, n_backfilled = 0, 50, 0, 0

    while True:
        activities = client.get_activities(start, limit)
        if not activities: break

        for act in activities:
            act_id = str(act.get("activityId"))
            existing = db["activities"].get(act_id)

            if existing:
                if not existing.get("gpx_file"):
                    try:
                        gpx_data = client.download_activity(int(act_id), dl_fmt=client.ActivityDownloadFormat.GPX)
                        gpx_path = save_raw_gpx(act_id, gpx_data)
                        if gpx_path:
                            existing["gpx_file"] = gpx_path
                            n_backfilled += 1
                            print(f"   🔁 GPX rattrapé : {existing.get('name')}")
                    except Exception as e:
                        pass

                if "swiss_elevations" not in existing:
                    swiss_eles = fetch_swisstopo_profile(existing.get("coords", []))
                    existing["swiss_elevations"] = swiss_eles

                if not existing.get("swiss_elevations") and "global_elevations" not in existing:
                    global_eles = fetch_global_elevation_profile(existing.get("coords", []))
                    existing["global_elevations"] = global_eles

                if not existing.get("_cols_warmed") and existing.get("coords"):
                    before = len(swiss_cols_cache)
                    warm_col_cache_for_activity(
                        existing.get("coords", []), existing.get("elevations", []),
                        existing.get("swiss_elevations"), existing.get("global_elevations"),
                        existing.get("sport", "route"), swiss_cols_cache
                    )
                    n_cols_warmed += len(swiss_cols_cache) - before
                    existing["_cols_warmed"] = True
                continue

            sport = classify_activity(act)
            if not sport: continue
            
            distance_km = round((act.get('distance') or 0) / 1000, 2)
            if distance_km < 1.0: continue
            print(f"   ⬇️ {act.get('activityName')} ({distance_km} km)")
            
            try:
                gpx_data = client.download_activity(int(act_id), dl_fmt=client.ActivityDownloadFormat.GPX)
                coords, elevations = extract_gpx_data(gpx_data)
                if not coords: continue

                gpx_path = save_raw_gpx(act_id, gpx_data)
                duration_s = act.get('duration', 0)
                speed_kmh = round((act.get('averageSpeed', 0) * 3.6), 1)
                max_speed_kmh = round((act.get('maxSpeed', 0) * 3.6), 1)
                hr = round(act.get('averageHR', 0)) or "N/A"
                calories = round(act.get('calories', 0)) or "N/A"
                elevation = round(act.get('elevationGain', 0)) or 0

                swiss_eles = fetch_swisstopo_profile(coords)
                global_eles = None
                if not swiss_eles:
                    global_eles = fetch_global_elevation_profile(coords)
                    
                db["activities"][act_id] = {
                    "id": act_id, "name": act.get("activityName", "Activité sans nom"),
                    "date": act.get("startTimeLocal", "")[:10], "sport": sport,
                    "exact_type": act.get('activityType', {}).get('typeKey', sport).replace('_', ' ').title(),
                    "distance": distance_km, "elevation": elevation, "duration": duration_s,
                    "speed": speed_kmh, "max_speed": max_speed_kmh, "hr": hr, "calories": calories,
                    "gear": "", "coords": coords, "elevations": elevations,
                    "swiss_elevations": swiss_eles, "global_elevations": global_eles,
                    "comment": "", "photos": [], "gpx_file": gpx_path,
                }

                before = len(swiss_cols_cache)
                warm_col_cache_for_activity(coords, elevations, swiss_eles, global_eles, sport, swiss_cols_cache)
                n_cols_warmed += len(swiss_cols_cache) - before
                db["activities"][act_id]["_cols_warmed"] = True
                n_added += 1
            except Exception as e:
                print(f"   ⚠️ Erreur sur {act_id} : {e}")
                
        if start >= 150 and n_added == 0 and n_backfilled == 0: break
        start += limit
        
    db["last_sync"] = datetime.now().isoformat()
    save_db(db)
    save_cols_cache(swiss_cols_cache)
    print(f"\n✅ Terminé ! {n_added} nouveau(x) tracé(s), {n_backfilled} GPX rattrapé(s), {n_cols_warmed} nouveau(x) col(s) en cache.")
    generate_map()

# =========================================================
# 2️⃣ GÉNÉRATION DE LA CARTE INTERACTIVE (HTML)
# =========================================================
def generate_map(public_mode=False):
    db = load_db()
    db_healed = False 
    cfg = PUBLIC_CONFIG
    trim_start = cfg["trim_debut_m"] if public_mode else 0
    trim_end = cfg["trim_fin_m"] if public_mode else 0
    hide_stats = public_mode and cfg["masquer_palmares"]
    hide_jerseys = public_mode and cfg["masquer_maillots"]
    hide_hr = public_mode and cfg["masquer_fc_calories"]
    hide_speed = public_mode and cfg["masquer_vitesse"]
    hide_comments = public_mode and cfg["masquer_commentaires"]

    swiss_cols_cache = load_cols_cache()
    live_col_lookups_budget = [6]

    map_center = [46.2333, 7.3500] 
    m = folium.Map(location=map_center, zoom_start=11, tiles=None, control_scale=True)
    
    folium.TileLayer('OpenTopoMap', name='⛰️ Topographie').add_to(m)
    folium.TileLayer('https://wmts.geo.admin.ch/1.0.0/ch.swisstopo.pixelkarte-farbe/default/current/3857/{z}/{x}/{y}.jpeg', attr='swisstopo', name='🇨🇭 Swisstopo', max_zoom=18, control=True).add_to(m)
    folium.TileLayer('https://wmts.geo.admin.ch/1.0.0/ch.swisstopo.swissimage/default/current/3857/{z}/{x}/{y}.jpeg', attr='swisstopo', name='🇨🇭 Swisstopo Satellite', max_zoom=19, control=True).add_to(m)
    folium.TileLayer('https://wmts.geo.admin.ch/1.0.0/ch.swisstopo.swissalti3d-reliefschattierung/default/current/3857/{z}/{x}/{y}.png', attr='swisstopo', name='🇨🇭 Relief Swisstopo (ombrage MNT)', max_zoom=18, control=True, overlay=False, show=False).add_to(m)
    folium.TileLayer('https://wmts.geo.admin.ch/1.0.0/ch.swisstopo.pixelkarte-grau/default/current/3857/{z}/{x}/{y}.jpeg', attr='swisstopo', name='🇨🇭 Swisstopo (Gris)', max_zoom=18, control=True, show=False).add_to(m)
    folium.TileLayer('https://mt1.google.com/vt/lyrs=y&x={x}&y={y}&z={z}', attr='Google', name='🛰️ Satellite Hybride (Google)', max_zoom=20, control=True).add_to(m)
    folium.TileLayer('OpenStreetMap', name='🌐 Standard (OSM)').add_to(m)
    folium.TileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', attr='Esri', name='🛰️ Satellite').add_to(m)
    folium.TileLayer('CartoDB positron', name='🗺️ Clair Minimaliste').add_to(m)
    
    feature_groups, clusters = {}, {}
    for key, config in SPORTS_CONFIG.items():
        fg = folium.FeatureGroup(name=config["nom"], show=True)
        mc = plugins.MarkerCluster(name=f"📍 Clusters {config['nom']}", disableClusteringAtZoom=14, spiderfyOnMaxZoom=True)
        fg.add_child(mc)
        m.add_child(fg)
        feature_groups[key], clusters[key] = fg, mc

    search_features, all_heat_coords, js_activities_data = [], [], []
    full_details_dict = {}
    gpx_fallback_dict = {}
    py_climb_svg_dict = {}
    py_climb_coords_dict = {}
    py_climb_meta_dict = {}
    py_climb_map_segments_dict = {}
    unique_gears = set()
    col_catalog = {}

    observed_hrs = [a.get('hr') for a in db["activities"].values() if isinstance(a.get('hr'), (int, float))]
    FC_MAX = (max(observed_hrs) + 5) if observed_hrs else 190
    
    for act in db["activities"].values():
        cached_coords = act.get("coords") or []
        cached_eles = act.get("elevations") or []
        needs_gpx_reparse = (not cached_coords or not cached_eles or len(cached_coords) != len(cached_eles) or any(e == 0 for e in cached_eles))
        if needs_gpx_reparse:
            gpx_path_full = os.path.join(DOSSIER_BASE, act.get('gpx_file', ''))
            if act.get('gpx_file') and os.path.exists(gpx_path_full):
                with open(gpx_path_full, "rb") as f: coords, elevations = extract_gpx_data(f.read())
                act["coords"], act["elevations"] = coords, elevations
                db_healed = True
            else: coords, elevations = cached_coords, cached_eles
        else: coords, elevations = cached_coords, cached_eles
            
        if not coords or not elevations or len(coords) < 10: continue

        coords, elevations = trim_track_endpoints(coords, elevations, trim_start, trim_end)
        if not coords or len(coords) < 2: continue

        sport_key = act["sport"]
        color = SPORTS_CONFIG[sport_key]["couleur"]
        dist = act.get('distance', 0)
        ele = act.get('elevation', 0)
        dur = act.get("duration", 0)
        has_photos = bool(act.get("photos"))
        
        gear_str = "Olympia" if sport_key == "vtt" else "Mérida Silex" if sport_key == "gravel" else "Trek Madone SL6 Gen 8" if sport_key == "route" else "Non spécifié"
        act['gear'] = gear_str
        unique_gears.add(gear_str)
        all_heat_coords.extend(coords)
        
        lats, lons = [c[0] for c in coords], [c[1] for c in coords]
        bounds = [[min(lats), min(lons)], [max(lats), max(lons)]]
        escaped_name = act['name'].replace("'", "\\'").replace('"', '&quot;')
        suffer = 0 if hide_hr else calculate_suffer_score(act.get('hr'), dur, FC_REPOS, FC_MAX)
        gpx_file_field = None if public_mode else act.get("gpx_file")
        if not gpx_file_field: gpx_fallback_dict[act['id']] = {"coords": coords, "elevations": elevations}

        js_activities_data.append({"id": act['id'], "name": escaped_name, "date": act['date'], "sport": SPORTS_CONFIG[sport_key]['nom'], "dist": dist, "ele": ele, "duration": dur, "speed": 0 if hide_speed else act.get('speed', 0), "suffer": suffer, "gear": gear_str.replace("'", "\\'"), "lat": coords[0][0], "lng": coords[0][1], "bounds": bounds, "color": color, "has_photos": has_photos, "gpxFile": gpx_file_field})
        escaped_comment = "" if hide_comments else (act.get('comment') or "").replace("'", "\\'").replace('"', '&quot;')

        used_swisstopo_ele, used_global_ele = False, False
        raw_coords_len = len(act.get("coords") or [])
        stat_swiss_eles, stat_global_eles = None, None

        swiss_eles_raw = act.get("swiss_elevations")
        if swiss_eles_raw and raw_coords_len and len(swiss_eles_raw) == raw_coords_len:
            _, trimmed = trim_track_endpoints(act.get("coords"), swiss_eles_raw, trim_start, trim_end)
            if trimmed and len(trimmed) == len(coords): stat_swiss_eles = trimmed

        if not stat_swiss_eles:
            global_eles_raw = act.get("global_elevations")
            if global_eles_raw and raw_coords_len and len(global_eles_raw) == raw_coords_len:
                _, trimmed = trim_track_endpoints(act.get("coords"), global_eles_raw, trim_start, trim_end)
                if trimmed and len(trimmed) == len(coords): stat_global_eles = trimmed

        stat_elevations, climbs, used_swisstopo_ele, used_global_ele = compute_climbs_for_activity(coords, elevations, stat_swiss_eles, stat_global_eles, sport_key)
            
        climbs_html = ""
        if climbs:
            climbs_html += '<div style="margin-top:20px;"><h4 style="font-size:12px; letter-spacing:0.05em; color:#14181c; margin-bottom:8px; border-bottom:2px solid #14181c; padding-bottom:6px; font-family:\'Oswald\', sans-serif; text-transform:uppercase;">🚵‍♂️ Ascensions Répertoriées</h4>'
            for idx, c in enumerate(climbs):
                c_id = f"climb_{act['id']}_{idx}"
                peak_lat, peak_lon = coords[c['end']][0], coords[c['end']][1]
                col_key = f"{round(peak_lat,4)},{round(peak_lon,4)}"
                if col_key in swiss_cols_cache or live_col_lookups_budget[0] > 0:
                    if col_key not in swiss_cols_cache: live_col_lookups_budget[0] -= 1
                    col_match = identify_swiss_col(peak_lat, peak_lon, swiss_cols_cache)
                else: col_match = None

                climbs_html += generate_vv_climb_html(c, coords, stat_elevations, c_id, col_match)
                c_coords, c_eles = coords[c['start']:c['end']+1], stat_elevations[c['start']:c['end']+1]
                map_segments = []
                for j in range(len(c_coords)-1):
                    dist_seg = haversine_m(c_coords[j], c_coords[j+1])
                    gain_seg = c_eles[j+1] - c_eles[j]
                    grad_seg = (gain_seg / dist_seg * 100) if dist_seg > 0 else 0
                    c_color = get_vv_color(max(0, grad_seg))
                    map_segments.append({'coords': [c_coords[j], c_coords[j+1]], 'color': c_color})
                
                py_climb_map_segments_dict[c_id] = map_segments
                py_climb_svg_dict[c_id] = generate_1km_segments_svg(c_coords, c_eles, c['dist'], c['gain'], c['cat'])
                py_climb_coords_dict[c_id] = c_coords
                py_climb_meta_dict[c_id] = {'title': f"{c['dist']} km | +{c['gain']}m", 'act_id': act['id'], 'idx': idx, 'peak_lat': peak_lat, 'peak_lon': peak_lon, 'official_name': col_match['name'] if col_match else None}

                if not public_mode:
                    col_key = f"swiss:{col_match['name']}" if col_match else f"loc:{round(peak_lat,3)}_{round(peak_lon,3)}"
                    if col_key not in col_catalog: col_catalog[col_key] = {'name': col_match['name'] if col_match else None, 'official': bool(col_match), 'lat': peak_lat, 'lon': peak_lon, 'ascents': []}
                    col_catalog[col_key]['ascents'].append({'c_id': c_id, 'act_id': act['id'], 'date': act['date'], 'sport': SPORTS_CONFIG[sport_key]['nom'], 'dist': c['dist'], 'gain': c['gain'], 'grad': c['grad'], 'cat': c['cat']})
            climbs_html += '</div>'

        vam = int((ele / dur) * 3600) if dur > 0 else 0
        gradient = round((ele / (dist * 500)) * 100, 1) if dist > 0 else 0
            
        effort_index = dist + (ele / 100) * 1.5
        if effort_index >= 80: diff_badge = "<span class='vv-chip' style='background:#d62728;'>🏔️ ÉTAPE REINE</span>"
        elif effort_index >= 50: diff_badge = "<span class='vv-chip' style='background:#ff7f0e;'>🔥 EXIGEANTE</span>"
        elif effort_index >= 25: diff_badge = "<span class='vv-chip' style='background:#1f77b4;'>⏱️ RYTHMÉE</span>"
        else: diff_badge = "<span class='vv-chip' style='background:#2ca02c;'>☕ RÉCUPÉRATION</span>"

        suffer_badge_html = ""
        if not hide_hr:
            if suffer >= 200: suffer_badge_html = f"<div style='margin-bottom:14px;'><span class='vv-chip' style='background:#7f1d1d;'>❤️‍🔥 CHARGE EXTRÊME · {suffer}</span></div>"
            elif suffer >= 120: suffer_badge_html = f"<div style='margin-bottom:14px;'><span class='vv-chip' style='background:#d62728;'>❤️‍🔥 CHARGE ÉLEVÉE · {suffer}</span></div>"
            elif suffer >= 60: suffer_badge_html = f"<div style='margin-bottom:14px;'><span class='vv-chip' style='background:#ff7f0e;'>❤️ CHARGE MODÉRÉE · {suffer}</span></div>"
            elif suffer > 0: suffer_badge_html = f"<div style='margin-bottom:14px;'><span class='vv-chip' style='background:#2ca02c;'>❤️ CHARGE LÉGÈRE · {suffer}</span></div>"

        photo_title_icon = " 🖼️" if has_photos else ""
        tile_speed = "" if hide_speed else f"""<div class="vv-stat-cell"><div class="vv-stat-val" style="color:#1f77b4;">{act.get('speed', 0)}<span style="font-size:11px;font-weight:600;"> km/h</span></div><div class="vv-label">Moyenne</div></div>"""
        tile_maxspeed_hr = "" if hide_speed and hide_hr else f"""
                <div class="vv-stat-cell"><div class="vv-stat-val" style="color:#555;">{'—' if hide_speed else act.get('max_speed', 0)}<span style="font-size:11px;font-weight:600;"> km/h</span></div><div class="vv-label">Vitesse Max</div></div>
                <div class="vv-stat-cell"><div class="vv-stat-val" style="color:#d62728;">{'—' if hide_hr else act.get('hr', 'N/A')}<span style="font-size:11px;font-weight:600;"> bpm</span></div><div class="vv-label">Cardiaque</div></div>"""

        swisstopo_badge_html = ""
        if used_swisstopo_ele: swisstopo_badge_html = '<div style="font-size:11px; color:#0b5394; margin-bottom:10px; padding:7px 10px; background:#e8f0fe; border-radius:4px; border-left:3px solid #1f77b4; font-weight:bold;">🇨🇭 Altitudes recalculées (swissALTI3D).</div>'
        elif used_global_ele: swisstopo_badge_html = '<div style="font-size:11px; color:#0b5394; margin-bottom:10px; padding:7px 10px; background:#e8f0fe; border-radius:4px; border-left:3px solid #2ca02c; font-weight:bold;">🌍 Altitudes recalculées (Open Topo Data).</div>'

        edit_btn_html = ""
        if not public_mode:
            edit_btn_html = f"""<button onclick="openEditModal('{act['id']}', '{escaped_comment}', '{escaped_name}')" style="flex:1; padding:15px; background:{color}; color:white; border:none; border-radius:10px; cursor:pointer; font-weight:bold; font-size:14px; box-shadow: 0 4px 6px rgba(0,0,0,0.15);">📝 Éditer</button>"""

        full_html = f"""
        <div style="padding: 25px; padding-top: 10px; font-family: 'Segoe UI', Tahoma, sans-serif;">
            <h2 style="color:{color}; margin:0 0 10px 0; font-size: 24px; font-weight: 700; line-height: 1.15; font-family:'Oswald','Segoe UI',sans-serif; text-transform:uppercase; letter-spacing:0.3px;">{act['name']}{photo_title_icon}</h2>
            <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom: 12px; border-bottom: 2px solid var(--vv-ink); padding-bottom: 10px; flex-wrap:wrap; gap:8px;">
                <span class="mono-num" style="font-size: 12px; color: #444;">📅 {act['date']}</span>{diff_badge}
            </div>
            {suffer_badge_html}
            <div class="vv-stat-grid" style="grid-template-columns: repeat(3, 1fr); margin-bottom: 15px; text-align:left;">
                <div class="vv-stat-cell"><div class="vv-stat-val" style="color:#1f77b4;">{dist}<span style="font-size:11px;font-weight:600;"> km</span></div><div class="vv-label">Distance</div></div>
                <div class="vv-stat-cell"><div class="vv-stat-val" style="color:#ff7f0e;">+{ele}<span style="font-size:11px;font-weight:600;"> m</span></div><div class="vv-label">Dénivelé</div></div>
                <div class="vv-stat-cell"><div class="vv-stat-val" style="color:#333;">{format_duration(dur)}</div><div class="vv-label">Temps</div></div>
                {tile_speed}
                <div class="vv-stat-cell"><div class="vv-stat-val" style="color:#d62728;">{vam}<span style="font-size:11px;font-weight:600;"> m/h</span></div><div class="vv-label">VAM</div></div>
                <div class="vv-stat-cell"><div class="vv-stat-val" style="color:#8c564b;">~{gradient}<span style="font-size:11px;font-weight:600;">%</span></div><div class="vv-label">Pente Moy.</div></div>
                {tile_maxspeed_hr}
            </div>
            <div style="font-size: 13px; color: #333; margin-bottom: 10px; padding: 9px 10px; background: var(--vv-panel); border-radius: 4px; border-left: 3px solid #9467bd; display:flex; justify-content:space-between; align-items:center;">
                <span>🚲 <b>Équipement</b></span> <span class="mono-num" style="color:#1f77b4; font-size:13px;">{gear_str}</span>
            </div>
            {swisstopo_badge_html}{generate_svg_elevation(stat_elevations, color)}{climbs_html}
        """
        
        if not hide_comments and act.get("comment"): full_html += f'<div style="background:#fff3cd; border-left:4px solid #ffc107; padding:12px; border-radius:8px; margin-top:15px; font-size:15px; font-style:italic; color:#664d03; box-shadow:0 2px 4px rgba(0,0,0,0.05);">"{act["comment"]}"</div>'
        if act.get("photos"):
            full_html += '<div style="display:grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr)); gap:10px; margin-top:15px;">'
            for p in act["photos"]: full_html += f'<img src="{p}" onclick="openLightbox(this.src)" style="width:100%; height:140px; object-fit:cover; border-radius:8px; box-shadow: 0 3px 6px rgba(0,0,0,0.15); transition:transform 0.2s; cursor:zoom-in;" onmouseover="this.style.transform=\'scale(1.03)\'" onmouseout="this.style.transform=\'scale(1)\'">'
            full_html += '</div>'

        full_html += f"""
            <div style="display:flex; gap:10px; margin-top:20px;">
                <button onclick="shareActivity('{act['id']}', '{escaped_name}')" style="flex:1; padding:15px; background:#1f77b4; color:white; border:none; border-radius:10px; cursor:pointer; font-weight:bold; font-size:14px; box-shadow: 0 4px 6px rgba(0,0,0,0.15);">🔗 Partager</button>
                <button onclick="downloadGPX('{act['id']}')" style="flex:1; padding:15px; background:#222; color:white; border:none; border-radius:10px; cursor:pointer; font-weight:bold; font-size:14px; box-shadow: 0 4px 6px rgba(0,0,0,0.15);">⬇️ GPX</button>
                {edit_btn_html}
            </div></div>"""
        full_details_dict[act['id']] = full_html

        cover_photo_html = f'<div style="display:flex; justify-content:center; margin-top:8px; margin-bottom:8px;"><img src="{act["photos"][0]}" style="width:75px; height:75px; object-fit:cover; border-radius:50%; border:3px solid {color}; box-shadow: 0 3px 6px rgba(0,0,0,0.15);"></div>' if act.get("photos") else ""
        mini_popup_html = f"""<div style="font-family: 'Segoe UI', sans-serif; text-align: center; min-width: 190px;"><div style="font-size: 15px; font-weight: 900; color: {color}; margin-bottom: 5px; border-bottom: 2px solid #ccc; padding-bottom: 4px; line-height:1.2;">{act['name']}{photo_title_icon}</div>{cover_photo_html}<div style="font-size: 14px; font-weight: bold; color: #333; margin-bottom: 12px;">📏 {dist} km &nbsp;|&nbsp; ⛰️ {ele} m+</div><div style="display:flex; gap:6px;"><button onclick="focusOnActivity('{act['id']}')" style="flex:2; background:#2ca02c; color:white; border:none; border-radius:6px; padding:10px; cursor:pointer; font-weight:bold; box-shadow:0 2px 4px rgba(0,0,0,0.2);">🔍 Développer</button><button onclick="downloadGPX('{act['id']}')" title="Télécharger le GPX" style="flex:1; background:#333; color:white; border:none; border-radius:6px; padding:10px; cursor:pointer; font-weight:bold; box-shadow:0 2px 4px rgba(0,0,0,0.2);">⬇️</button></div></div>"""

        track_popup_html = f"""<div style="font-family: 'Segoe UI', sans-serif; text-align: center; min-width: 160px;"><div style="font-size: 14px; font-weight: 900; color: {color}; margin-bottom: 5px;">{escaped_name}</div><div style="font-size: 12px; font-weight: bold; color: #555; margin-bottom: 10px;">📅 {act['date']} | 📏 {dist} km</div><button onclick="focusOnActivity('{act['id']}');" style="width:100%; background:{color}; color:white; border:none; border-radius:6px; padding:8px; cursor:pointer; font-weight:bold; box-shadow:0 2px 4px rgba(0,0,0,0.2);">🔍 Ouvrir cette sortie</button></div>"""
        folium.PolyLine(coords, color=color, weight=5, className=f"activity-track track-{act['id']}", tooltip=folium.Tooltip(f"🚴 {escaped_name}", sticky=True), popup=folium.Popup(track_popup_html, max_width=250)).add_to(feature_groups[sport_key])
        red_pin_html = f"""<div style="position:relative; width:24px; height:34px; cursor:pointer;"><svg class="pin-svg" viewBox="0 0 384 512" style="fill:#d62728; width:24px; height:34px; position:absolute; top:-34px; left:-12px; filter: drop-shadow(0 2px 3px rgba(0,0,0,0.5)); transition: transform 0.15s ease-out;"><path d="M172.268 501.67C26.97 291.031 0 269.413 0 192 0 85.961 85.961 0 192 0s192 85.961 192 192c0 77.413-26.97 99.031-172.268 309.67-9.535 13.774-29.93 13.773-39.464 0zM192 272c44.183 0 80-35.817 80-80s-35.817-80-80-80-80 35.817-80 80 35.817 80 80 80z"/></svg></div>"""
        folium.Marker(location=coords[0], icon=folium.DivIcon(html=red_pin_html, class_name=f"leaflet-marker-icon leaflet-interactive global-marker-wrapper garmin-{act['id']}"), tooltip=folium.Tooltip(f"🏁 {act['name']}{photo_title_icon}", sticky=True), popup=folium.Popup(mini_popup_html, max_width=250)).add_to(clusters[sport_key])
        folium.Marker(location=coords[0], icon=folium.DivIcon(html=f'<div style="width:20px;height:20px;background:#2ca02c;border:3px solid white;border-radius:50%;box-shadow:0 0 6px rgba(0,0,0,0.8);transform:translate(-50%,-50%);"></div>', class_name=f"start-end-wrapper track-{act['id']}-points"), tooltip=folium.Tooltip("🟢 Départ", sticky=True)).add_to(feature_groups[sport_key])
        folium.Marker(location=coords[-1], icon=folium.DivIcon(html=f'<div style="width:20px;height:20px;background:#d62728;border:3px solid white;border-radius:4px;box-shadow:0 0 6px rgba(0,0,0,0.8);transform:translate(-50%,-50%);"></div>', class_name=f"start-end-wrapper track-{act['id']}-points"), tooltip=folium.Tooltip("🏁 Arrivée", sticky=True)).add_to(feature_groups[sport_key])
        search_features.append({"type": "Feature", "geometry": {"type": "Point", "coordinates": [coords[0][1], coords[0][0]]}, "properties": {"name": f"{act['name']} ({act['date']})"}})

    if all_heat_coords:
        heat_layer = folium.FeatureGroup(name="🔥 Heatmap Globale", show=False)
        plugins.HeatMap(all_heat_coords, radius=8, blur=12).add_to(heat_layer)
        heat_layer.add_to(m)

    if db_healed: save_db(db)
    save_cols_cache(swiss_cols_cache)

    col_catalog_summary = []
    if not public_mode:
        for key, entry in col_catalog.items():
            ascents = entry['ascents']
            sports = sorted(set(a['sport'] for a in ascents))
            dates = sorted(a['date'] for a in ascents)
            best = max(ascents, key=lambda a: a['grad'])
            biggest = max(ascents, key=lambda a: a['gain'])
            col_catalog_summary.append({
                'name': entry['name'] or f"Montée non nommée ({entry['lat']:.3f}, {entry['lon']:.3f})",
                'official': entry['official'], 'lat': entry['lat'], 'lon': entry['lon'],
                'times': len(ascents), 'sports': sports,
                'first_date': dates[0], 'last_date': dates[-1],
                'best_grad': best['grad'], 'best_cat': best['cat'],
                'best_gain': biggest['gain'], 'best_dist': biggest['dist'],
                'latest_c_id': max(ascents, key=lambda a: a['date'])['c_id'],
                'latest_act_id': max(ascents, key=lambda a: a['date'])['act_id'],
            })
        col_catalog_summary.sort(key=lambda c: (-c['times'], -c['best_gain']))

    search_layer = folium.GeoJson({"type": "FeatureCollection", "features": search_features}, name="Moteur de recherche", show=False, style_function=lambda x: {'opacity': 0, 'fillOpacity': 0}, marker=folium.CircleMarker(radius=0, opacity=0, fill_opacity=0, weight=0)).add_to(m)
    plugins.Search(layer=search_layer, geom_type="Point", placeholder="🔍 Chercher une activité...", collapsed=True, search_label="name").add_to(m)
    plugins.Fullscreen(position='topright').add_to(m)
    plugins.MeasureControl(position='bottomleft').add_to(m)
    plugins.LocateControl(position='topright', strings={"title": "Où suis-je ?"}).add_to(m)
    plugins.Draw(export=True, position='topleft', draw_options={'polyline': False, 'polygon': True, 'rectangle': True, 'circle': False, 'marker': False, 'circlemarker': False}).add_to(m)
    folium.LayerControl(position='topright', collapsed=False).add_to(m)

    activities_json = json.dumps(js_activities_data)
    full_details_json = json.dumps(full_details_dict)
    gpx_fallback_json = json.dumps(gpx_fallback_dict)
    climb_segments_json = json.dumps(py_climb_map_segments_dict)
    climb_svg_json = json.dumps(py_climb_svg_dict)
    climb_coords_json = json.dumps(py_climb_coords_dict)
    climb_meta_json = json.dumps(py_climb_meta_dict)
    col_catalog_json = json.dumps(col_catalog_summary)
    
    gear_options_html = "".join([f'<option value="{g}">{g}</option>' for g in sorted(unique_gears)])
    sport_options_html = "".join([f'<option value="{cfg2["nom"]}">{cfg2["nom"]}</option>' for cfg2 in SPORTS_CONFIG.values()])
    hide_stats_js = "true" if hide_stats else "false"

    dashboard_block = "" if hide_stats else f"""
    <div id="stats-dashboard-inner">
        <div class="stat-header"><h4>📊 Palmarès Personnel</h4></div>
        <div style="display:flex; gap:6px; margin-bottom:12px;">
            <select id="dash-year-select" onchange="refreshDashboard()" style="flex:1; padding:5px; border-radius:6px; border:1px solid #ccc; font-size:12px;"><option value="all">Toutes années</option></select>
            <select id="dash-sport-select" onchange="refreshDashboard()" style="flex:1; padding:5px; border-radius:6px; border:1px solid #ccc; font-size:12px;"><option value="all">Tous sports</option>{sport_options_html}</select>
        </div>
        <div class="stat-line"><span>🚲 Activités</span> <b id="dash-count">0</b></div>
        <div class="stat-line"><span>📏 Distance</span> <b id="dash-km">0 km</b></div>
        <div class="stat-line"><span>⛰️ Dénivelé</span> <b id="dash-dplus">0 m</b></div>
        <div class="stat-line"><span>⏱️ Temps</span> <b id="dash-time">0h</b></div>
        <div class="stat-line"><span>🏔️ Everesting</span> <b id="dash-everest">0%</b></div>
        <div style="background:#eee; border-radius:6px; height:8px; overflow:hidden; margin-bottom:12px;"><div id="dash-everest-bar" style="background:linear-gradient(90deg,#1f77b4,#8c564b); height:100%; width:0%; transition:width 0.4s;"></div></div>
        <div style="margin-top:15px; height:120px;"><canvas id="monthlyChart"></canvas></div>
    </div>
    """

    # --- HTML Conditionnel (Public vs Privé) ---
    extra_buttons_html = ""
    extra_modals_html = ""
    edit_modal_html = ""

    if not public_mode:
        extra_buttons_html = """
        <div class="action-btn" id="cols-catalog-btn" onclick="openColsModal()" style="background:#8c564b; box-shadow:0 8px 20px rgba(140,86,75,0.4); display:none;" title="Mes Cols"><span class="btn-icon">🏔️</span><span class="btn-label" id="cols-catalog-label"> Mes Cols</span></div>
        <div class="action-btn" id="on-this-day-btn" onclick="openOnThisDayModal()" style="background:#d62728; box-shadow:0 8px 20px rgba(214,39,40,0.4); display:none;" title="Ce jour-là"><span class="btn-icon">📅</span><span class="btn-label"> Ce jour-là</span></div>
        """
        extra_modals_html = """
    <div id="cols-modal" class="modal-overlay">
        <div class="modal-content" style="max-width: 560px; padding: 0; overflow: hidden; display: flex; flex-direction: column;">
            <div style="background: #8c564b; color: white; padding: 18px 25px; display: flex; justify-content: space-between; align-items: center;">
                <h3 style="margin: 0; font-size: 18px;">🏔️ Mes Cols <span id="cols-count" style="background:rgba(255,255,255,0.25); padding:2px 10px; border-radius:12px; font-size:13px;">0</span></h3>
                <span class="close-modal" style="color:white; position:static;" onclick="document.getElementById('cols-modal').style.display='none'">&times;</span>
            </div>
            <div id="cols-list" style="padding: 20px; max-height: 65vh; overflow-y: auto;"></div>
        </div>
    </div>
    <div id="on-this-day-modal" class="modal-overlay">
        <div class="modal-content" style="max-width: 500px; padding: 0; overflow: hidden; display: flex; flex-direction: column;">
            <div style="background: #d62728; color: white; padding: 18px 25px; display: flex; justify-content: space-between; align-items: center;">
                <h3 style="margin: 0; font-size: 18px;">📅 Ce jour-là, les années précédentes</h3>
                <span class="close-modal" style="color:white; position:static;" onclick="document.getElementById('on-this-day-modal').style.display='none'">&times;</span>
            </div>
            <div id="on-this-day-list" style="padding: 20px; max-height: 60vh; overflow-y: auto;"></div>
        </div>
    </div>
        """
        edit_modal_html = """
    <div id="edit-modal-overlay" class="modal-overlay">
        <div class="modal-content">
            <span class="close-modal" onclick="closeEditModal()">&times;</span>
            <h3 style="border-bottom: 2px solid #ccc; font-family:'Oswald',sans-serif;">📝 Éditer l'activité</h3>
            <input type="hidden" id="edit-act-id">
            <label style="font-size:13px; font-weight:bold; color:#555; display:block; margin-bottom:5px;">Titre de la sortie :</label>
            <input type="text" id="edit-name" style="width:100%; padding:10px; border-radius:8px; border:1px solid #ccc; margin-bottom:15px; font-family:inherit; font-size:14px; box-sizing:border-box;">
            <label style="font-size:13px; font-weight:bold; color:#555; display:block; margin-bottom:5px;">Commentaire / Météo :</label>
            <textarea id="edit-comment" style="width:100%; height:100px; padding:10px; margin-bottom:15px; border-radius:8px; border:1px solid #ccc; font-family:inherit; resize:none; box-sizing:border-box;"></textarea>
            <label style="font-size:13px; font-weight:bold; color:#555; display:block; margin-bottom:5px;">📸 Ajouter des Photos :</label>
            <input type="file" id="edit-photo" accept="image/png, image/jpeg, image/jpg" multiple style="width:100%; margin-bottom:20px; padding:8px; border:1px dashed #aaa; background:#f9f9f9; border-radius:8px; box-sizing:border-box;">
            <button class="btn-apply" onclick="saveActivityData()" style="background:#2ca02c; color:white; padding:12px; width:100%; border:none; border-radius:8px; font-weight:bold; font-size:16px; cursor:pointer;">💾 Sauvegarder</button>
            <div id="save-loader" style="display:none; text-align:center; color:#2ca02c; font-size:14px; margin-top:15px; font-weight:bold;">⏳...</div>
        </div>
    </div>
        """

    custom_ui = f"""
    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no, viewport-fit=cover">
    <meta name="theme-color" content="#1f77b4">
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link href="https://fonts.googleapis.com/css2?family=Oswald:wght@500;600;700&family=Roboto+Mono:wght@500;700&display=swap" rel="stylesheet">
    <style>
      * {{ box-sizing: border-box; }}
      :root {{ --vv-ink: #14181c; --vv-ink-soft: #4b5560; --vv-line: #dde2e6; --vv-panel: #f4f6f7; --vv-accent: #fc4c02; }}
      .mono-num {{ font-family: 'Roboto Mono', 'Segoe UI', monospace; font-variant-numeric: tabular-nums; font-weight: 700; }}
      .vv-label {{ font-size: 10px; font-weight: 700; letter-spacing: 0.06em; text-transform: uppercase; color: var(--vv-ink-soft); }}
      .vv-stat-grid {{ display: grid; border: 1px solid var(--vv-line); border-radius: 6px; overflow: hidden; background: #fff; }}
      .vv-stat-cell {{ padding: 10px 12px; border-right: 1px solid var(--vv-line); border-bottom: 1px solid var(--vv-line); }}
      .vv-stat-val {{ font-family: 'Roboto Mono', monospace; font-variant-numeric: tabular-nums; font-weight: 700; font-size: 17px; letter-spacing: -0.01em; line-height: 1.15; }}
      .vv-chip {{ display: inline-flex; align-items: center; font-family: 'Roboto Mono', monospace; font-size: 10px; font-weight: 700; letter-spacing: 0.03em; padding: 2px 7px; border-radius: 3px; color: #fff; }}
      .vv-row {{ display: flex; align-items: center; gap: 10px; padding: 9px 10px; border-bottom: 1px solid var(--vv-line); cursor: pointer; transition: background 0.12s; }}
      .vv-row:hover {{ background: var(--vv-panel); }}
      .vv-row-main {{ flex: 1; min-width: 0; }}
      .vv-row-title {{ font-size: 13px; font-weight: 700; color: var(--vv-ink); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }}
      .vv-row-stats {{ display: flex; gap: 12px; font-family: 'Roboto Mono', monospace; font-size: 12px; font-weight: 700; text-align: right; white-space: nowrap; }}
      .vv-row-stats small {{ display: block; font-family: 'Segoe UI', sans-serif; font-size: 8px; font-weight: 700; color: var(--vv-ink-soft); text-transform: uppercase; letter-spacing: 0.04em; }}
      .leaflet-tooltip {{ pointer-events: none !important; white-space: nowrap; transition: opacity 0.1s; margin-top: -15px !important; }}
      .global-marker-wrapper {{ z-index: 400 !important; }}
      .global-marker-wrapper:hover {{ z-index: 1000 !important; }}
      .global-marker-wrapper:hover .pin-svg {{ transform: scale(1.25) translateY(-4px); }}
      path.activity-track {{ stroke-opacity: 0 !important; pointer-events: none !important; transition: stroke-opacity 0.3s ease; stroke-width: 6px !important; }}
      path.activity-track.show-track, path.activity-track.show-track-forced {{ stroke-opacity: 0.9 !important; pointer-events: auto !important; filter: drop-shadow(0 0 5px rgba(0,0,0,0.5)); }}
      body.focus-mode .marker-cluster, body.focus-mode .global-marker-wrapper {{ display: none !important; opacity: 0 !important; pointer-events: none !important; }}
      .start-end-wrapper {{ display: none !important; opacity: 0 !important; pointer-events: none !important; }}
      body.focus-mode .start-end-wrapper.active-focus {{ display: block !important; opacity: 1 !important; z-index: 9999 !important; }}
      #stats-dashboard-inner {{ background: #fff; padding: 15px; border-radius: 12px; box-shadow: 0 2px 8px rgba(0,0,0,0.05); margin-bottom: 20px; border-left: 6px solid #1f77b4; }}
      .stat-header {{ display:flex; justify-content:space-between; align-items:center; border-bottom: 2px solid #1f77b4; padding-bottom: 5px; margin-bottom:10px; }}
      .stat-header h4 {{ margin: 0; font-size: 16px; color: #222; text-transform: uppercase; font-family:'Oswald','Segoe UI',sans-serif; letter-spacing:0.5px; }}
      .stat-line {{ font-size: 14px; color: #444; margin-bottom: 8px; display: flex; justify-content: space-between; }}
      .stat-line b {{ color: #1f77b4; font-size: 15px; font-family:'Roboto Mono',monospace; font-variant-numeric: tabular-nums; }}
      .action-btns-container {{ position: fixed; bottom: 25px; left: 50%; transform: translateX(-50%); z-index: 999; display: flex; gap: 10px; transition: transform 0.4s; }}
      .action-btn {{ background: #1f77b4; color: white; padding: 12px 25px; border-radius: 30px; cursor: pointer; display: flex; align-items: center; gap: 6px; font-family: 'Segoe UI', sans-serif; font-size: 14px; font-weight: bold; box-shadow: 0 8px 20px rgba(31, 119, 180, 0.4); border: 2px solid white; transition: all 0.3s ease; white-space: nowrap; }}
      .action-btn:hover {{ transform: scale(1.05); }}
      .btn-filter-toggle {{ background: #2ca02c; box-shadow: 0 8px 20px rgba(44,160,44, 0.4); }}
      #activity-focus-panel {{ position: fixed; top: 0; left: 0; width: 420px; height: 100vh; background: #ffffff; z-index: 10000; overflow-y: auto; overflow-x: hidden; box-shadow: 5px 0 30px rgba(0,0,0,0.3); transition: transform 0.4s cubic-bezier(0.25, 0.8, 0.25, 1); transform: translateX(-105%); }}
      #activity-focus-panel.active {{ transform: translateX(0); }}
      .btn-close-focus {{ background: #222; color: white; padding: 18px; text-align: center; font-weight: bold; cursor: pointer; position: sticky; top: 0; z-index: 10; font-size: 14px; letter-spacing: 1px; display: flex; align-items: center; justify-content: center; gap: 10px; transition: 0.2s; }}
      .btn-close-focus:hover {{ background: #000; }}
      .btn-close-focus svg {{ width: 20px; fill: white; }}
      #shutdown-btn {{ position: fixed; bottom: 25px; right: 25px; z-index: 9999; background: #dc3545; color: white; padding: 10px 20px; border-radius: 12px; cursor: pointer; font-weight: bold; border: 2px solid white; box-shadow: 0 4px 10px rgba(0,0,0,0.3); transition: transform 0.2s;}}
      #shutdown-btn:hover {{ transform: scale(1.05); }}
      .modal-overlay {{ display: none; position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0,0,0,0.6); z-index: 10001; justify-content: center; align-items: center; backdrop-filter: blur(5px); font-family: 'Segoe UI', sans-serif; }}
      .modal-content {{ background: white; padding: 30px; border-radius: 16px; width: 90%; max-width: 450px; position: relative; box-shadow: 0 20px 40px rgba(0,0,0,0.3); }}
      .close-modal {{ position:absolute; right:20px; top:20px; cursor:pointer; font-size:28px; font-weight:bold; color:#888; line-height:0.8; transition:0.2s; z-index: 100; }}
      .close-modal:hover {{ color: #d62728; }}
      .explorer-modal-content {{ max-width: 900px; padding: 0; overflow: hidden; display: flex; flex-direction: column; background: #fff; border-radius: 16px; width: 95%; max-height: 85vh; box-shadow: 0 20px 50px rgba(0,0,0,0.4); }}
      .explorer-header {{ background: #1f77b4; color: white; padding: 18px 25px; display: flex; justify-content: space-between; align-items: center; }}
      .explorer-header h3 {{ margin: 0; font-size: 20px; font-family:'Oswald', sans-serif; letter-spacing:0.5px; }}
      .explorer-body {{ display: flex; flex-wrap: wrap; height: 65vh; max-height: 600px; }}
      .explorer-left {{ flex: 1; min-width: 320px; padding: 25px; background: #f8f9fa; border-right: 1px solid #ddd; overflow-y: auto; }}
      .explorer-right {{ flex: 1.5; min-width: 300px; padding: 25px; background: #fff; display: flex; flex-direction: column; height: 100%; overflow: hidden; }}
      #filter-results-list {{ flex-grow: 1; overflow-y: auto; padding-right: 10px; margin-bottom: 20px; }}
      .filter-row {{ margin-bottom: 12px; font-size: 13px; font-weight: bold; color: #444; }}
      .filter-row input, .filter-row select {{ width: 100%; padding: 8px; border-radius: 6px; border: 1px solid #ccc; margin-top: 5px; box-sizing: border-box; font-family: inherit; }}
      .filter-row .flex-row {{ display: flex; gap: 10px; align-items: center; }}
      .zone-item {{ background: #fff; border: 1px solid var(--vv-line); border-left: 3px solid transparent; padding: 10px 12px; border-radius: 3px; margin-bottom: 6px; cursor: pointer; transition: 0.15s; }}
      .zone-item:hover {{ border-left-color: #1f77b4; background: var(--vv-panel); }}
      .lightbox-overlay {{ display: none; position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0,0,0,0.9); z-index: 20000; justify-content: center; align-items: center; cursor: zoom-out; backdrop-filter: blur(10px); }}
      .lightbox-img {{ max-width: 90%; max-height: 90vh; border-radius: 12px; box-shadow: 0 10px 40px rgba(0,0,0,0.6); object-fit: contain; }}
      #climb-side-panel {{ position: fixed; top: 0; left: 0; width: 450px; height: 100vh; background: #ffffff; z-index: 10010; overflow-y: auto; overflow-x: hidden; box-shadow: 5px 0 30px rgba(0,0,0,0.4); transition: transform 0.4s cubic-bezier(0.25, 0.8, 0.25, 1); transform: translateX(-105%); font-family: 'Segoe UI', sans-serif; }}
      #climb-side-panel.active {{ transform: translateX(0); }}
      path.vv-climb-segment {{ pointer-events: none !important; filter: drop-shadow(0 0 4px rgba(0,0,0,0.5)); z-index: 9000 !important; stroke-linejoin: round; stroke-linecap: round; }}

      @media (max-width: 768px) {{
          .action-btns-container {{ bottom: calc(15px + env(safe-area-inset-bottom, 0px)); flex-direction: row; flex-wrap: wrap; justify-content: center; gap: 8px; max-width: 96vw; }}
          .action-btn {{ padding: 11px 16px; font-size: 13px; }}
          #activity-focus-panel {{ width: 100%; height: 55vh; top: auto; bottom: 0; transform: translateY(105%); border-radius: 25px 25px 0 0; border-top: 3px solid #ccc; }}
          #activity-focus-panel.active {{ transform: translateY(0); }}
          .btn-close-focus {{ border-radius: 25px 25px 0 0; }}
          .explorer-body {{ flex-direction: column; height: 75vh; }}
          .explorer-left {{ border-right: none; border-bottom: 2px solid #ddd; flex: none; height: 50%; }}
          .explorer-right {{ flex: 1; height: 50%; padding: 15px; }}
          #climb-side-panel {{ width: 100%; height: 65vh; top: auto; bottom: 0; transform: translateY(105%); border-radius: 25px 25px 0 0; border-top: 3px solid #d62728; }}
          #climb-side-panel.active {{ transform: translateY(0); }}
          #shutdown-btn {{ bottom: calc(15px + env(safe-area-inset-bottom, 0px)); right: 15px; padding: 8px 12px; font-size: 12px; }}
          .modal-content {{ max-height: 85vh; }}
          .zone-item {{ padding: 14px 12px; }}
      }}
      @media (max-width: 420px) {{
          .action-btn {{ padding: 12px; border-radius: 50%; width: 48px; height: 48px; display: flex; align-items: center; justify-content: center; font-size: 18px; }}
          .action-btn .btn-label {{ display: none; }}
          .btn-icon {{ line-height: 1; }}
      }}
    </style>

    <div id="search-container" style="position: fixed; top: 15px; left: 50%; transform: translateX(-50%); z-index: 1000; display: flex; flex-direction: column; align-items: center; gap: 8px; pointer-events: none; width: 90vw; max-width: 450px;">
        <div style="pointer-events: auto; background: white; padding: 5px 15px; border-radius: 30px; box-shadow: 0 4px 10px rgba(0,0,0,0.2); display: flex; align-items: center; border: 2px solid #d62728; width: 100%; font-family: 'Segoe UI', sans-serif;">
            <span style="margin-right: 8px; font-size: 18px;" title="Recherche géographique Suisse">🇨🇭</span>
            <input type="text" id="ch-search-input" placeholder="Lieu, sommet suisse..." onkeypress="if(event.key === 'Enter') searchCH()" style="border: none; outline: none; padding: 5px; flex-grow: 1; font-family: inherit; font-size: 14px;">
            <button onclick="searchCH()" style="background: none; border: none; cursor: pointer; font-size: 16px;">🔍</button>
        </div>
        <div style="pointer-events: auto; background: white; padding: 5px 15px; border-radius: 30px; box-shadow: 0 4px 10px rgba(0,0,0,0.2); display: flex; align-items: center; border: 2px solid #1f77b4; width: 100%; font-family: 'Segoe UI', sans-serif;">
            <span style="margin-right: 8px; font-size: 18px;" title="Recherche Mondiale">🌍</span>
            <input type="text" id="global-search-input" placeholder="Cortina d'Ampezzo, Ventoux..." onkeypress="if(event.key === 'Enter') searchGlobal()" style="border: none; outline: none; padding: 5px; flex-grow: 1; font-family: inherit; font-size: 14px;">
            <button onclick="searchGlobal()" style="background: none; border: none; cursor: pointer; font-size: 16px;">🔍</button>
        </div>
        <div style="font-size: 11px; font-weight: bold; color: #333; text-shadow: 0 0 3px white, 0 0 5px white; background: rgba(255,255,255,0.85); padding: 4px 10px; border-radius: 12px; pointer-events: none; box-shadow: 0 1px 3px rgba(0,0,0,0.2);">
            📍 Clic-droit n'importe où sur la carte pour voir l'altitude (Mondial)
        </div>
    </div>

    <!-- BOUTON ÉTEINDRE (visible partout, géré par le code) -->
    <div id="shutdown-btn" onclick="shutdownServer()">🛑 Éteindre</div>

    <div id="lightbox-overlay" class="lightbox-overlay" onclick="closeLightbox()"><img id="lightbox-img" class="lightbox-img" src=""></div>
    <div id="svg-lightbox-overlay" class="lightbox-overlay" onclick="if(event.target === this) closeSvgLightbox()">
        <div style="background: #fff; padding: 20px; border-radius: 12px; width: 95%; max-width: 1200px; height: 85vh; display: flex; flex-direction: column; position: relative; box-shadow: 0 20px 40px rgba(0,0,0,0.5);">
            <span class="close-modal" style="right:15px; top:10px; color:#333; z-index:1000;" onclick="closeSvgLightbox()">&times;</span>
            <div id="svg-lightbox-content" style="flex-grow: 1; display: flex; flex-direction: column; height: 100%; margin-top:20px;"></div>
        </div>
    </div>

    <div id="climb-side-panel">
        <div class="btn-close-focus" onclick="closeClimbPanel()" style="background:#d62728;">
            <svg viewBox="0 0 448 512" style="width:20px; fill:white; margin-right:8px;"><path d="M9.4 233.4c-12.5 12.5-12.5 32.8 0 45.3l160 160c12.5 12.5 32.8 12.5 45.3 0s12.5-32.8 0-45.3L109.2 288 416 288c17.7 0 32-14.3 32-32s-14.3-32-32-32l-306.7 0L214.6 118.6c12.5-12.5 12.5-32.8 0-45.3s-32.8-12.5-45.3 0l-160 160z"/></svg>
            Retour au Menu de l'Activité
        </div>
        <div style="padding: 25px;">
            <h3 id="climb-panel-title" style="margin-top:0; font-family:'Oswald', sans-serif; text-transform:uppercase; color:#1f77b4; border-bottom:2px solid #eee; padding-bottom:10px;">Profil Détaillé</h3>
            <div id="climb-panel-content-inner" style="min-height: 250px;"></div>
            <div style="margin-top:25px; background:#f8f9fa; padding:15px; border-radius:8px; border:1px solid #e9ecef;">
                <h4 style="margin:0 0 10px 0; font-size:13px; text-transform:uppercase; color:#555; font-family:'Oswald', sans-serif;">Légende des pentes</h4>
                <div style="display:flex; flex-wrap:wrap; gap:8px; font-size:12px; font-weight:bold;">
                    <span style="background:#53a8cf; color:#fff; padding:4px 8px; border-radius:4px;">🔵 &lt; 2%</span>
                    <span style="background:#5ebf6b; color:#fff; padding:4px 8px; border-radius:4px;">🟢 2-4%</span>
                    <span style="background:#d6cc1f; color:#fff; padding:4px 8px; border-radius:4px;">🟡 4-6%</span>
                    <span style="background:#e57b27; color:#fff; padding:4px 8px; border-radius:4px;">🟠 6-9%</span>
                    <span style="background:#d62728; color:#fff; padding:4px 8px; border-radius:4px;">🔴 9-12%</span>
                    <span style="background:#000000; color:#fff; padding:4px 8px; border-radius:4px;">⚫ &gt; 12%</span>
                </div>
            </div>
            <div id="climb-nav-container"></div>
        </div>
    </div>

    <div class="action-btns-container" id="main-action-btns">
        <div class="action-btn btn-filter-toggle" onclick="document.getElementById('explorer-modal').style.display='flex'" title="Palmarès & Explorateur"><span class="btn-icon">🧭</span><span class="btn-label"> Palmarès & Explorateur</span></div>
        <div class="action-btn" id="toggle-tracks-btn" onclick="toggleAllTracks()" title="Afficher la toile d'araignée"><span class="btn-icon">👁️</span><span class="btn-label" id="toggle-tracks-label"> Afficher la toile d'araignée</span></div>
        {extra_buttons_html}
    </div>

    {extra_modals_html}

    <div id="explorer-modal" class="modal-overlay">
        <div class="explorer-modal-content">
            <div class="explorer-header">
                <h3>🧭 Centre de Contrôle Atlas</h3>
                <span class="close-modal" style="color:white; position:static;" onclick="document.getElementById('explorer-modal').style.display='none'">&times;</span>
            </div>
            <div class="explorer-body">
                <div class="explorer-left">
                    {dashboard_block}
                    <h4 style="margin: 0 0 10px 0; font-size: 16px; border-bottom: 2px solid #2ca02c; padding-bottom: 5px; font-family:'Oswald',sans-serif; text-transform:uppercase;">🔎 Filtrer les sorties</h4>
                    <div class="filter-row">Recherche textuelle : <input type="text" id="fil-text" placeholder="Nom..." onkeyup="applyAdvancedFilters()"></div>
                    <div class="filter-row">Sport : <select id="fil-sport" onchange="applyAdvancedFilters()"><option value="">Tous</option>{sport_options_html}</select></div>
                    <div class="filter-row">Période : <div class="flex-row"><input type="date" id="fil-date-min" onchange="applyAdvancedFilters()"> au <input type="date" id="fil-date-max" onchange="applyAdvancedFilters()"></div></div>
                    <div class="filter-row">Dist (km) : <div class="flex-row"><input type="number" id="fil-dist-min" onkeyup="applyAdvancedFilters()" placeholder="Min"> à <input type="number" id="fil-dist-max" onkeyup="applyAdvancedFilters()" placeholder="Max"></div></div>
                    <div class="filter-row">Dénivelé (m) : <div class="flex-row"><input type="number" id="fil-ele-min" onkeyup="applyAdvancedFilters()" placeholder="Min"> à <input type="number" id="fil-ele-max" onkeyup="applyAdvancedFilters()" placeholder="Max"></div></div>
                    <div class="filter-row">Équipement : <select id="fil-gear" onchange="applyAdvancedFilters()"><option value="">Tous</option>{gear_options_html}</select></div>
                    <button onclick="resetFilters()" style="width:100%; margin-top:15px; padding:10px; background:#fff; border:2px solid #ccc; border-radius:8px; cursor:pointer; font-weight:bold; color:#444;">🔄 Réinitialiser</button>
                </div>
                <div class="explorer-right">
                    <h4 style="margin: 0 0 15px 0; font-size: 16px; border-bottom: 2px solid #1f77b4; padding-bottom: 8px; display:flex; justify-content:space-between; color:#333; font-family:'Oswald',sans-serif; text-transform:uppercase;">
                        <span>📋 Résultats</span><span id="filter-result-count" style="background:#e8f5e9; color:#2ca02c; padding:2px 10px; border-radius:12px; font-size:13px; font-weight:bold;">0</span>
                    </h4>
                    <div id="filter-results-list"></div>
                </div>
            </div>
        </div>
    </div>

    <div id="zone-results-modal" class="modal-overlay">
        <div class="modal-content" style="max-width: 500px; padding: 0; overflow: hidden; display: flex; flex-direction: column;">
            <div style="background: #ff7f0e; color: white; padding: 18px 25px; display: flex; justify-content: space-between; align-items: center;">
                <h3 style="margin: 0; font-size: 18px;">📍 <span id="zone-count">0</span> Activité(s)</h3>
                <span class="close-modal" style="color:white; position:static;" onclick="document.getElementById('zone-results-modal').style.display='none'">&times;</span>
            </div>
            <div id="zone-results-list" style="padding: 20px; max-height: 60vh; overflow-y: auto;"></div>
        </div>
    </div>

    <div id="activity-focus-panel">
        <div class="btn-close-focus" onclick="closeFocusPanel()"><svg viewBox="0 0 448 512"><path d="M9.4 233.4c-12.5 12.5-12.5 32.8 0 45.3l160 160c12.5 12.5 32.8 12.5 45.3 0s12.5-32.8 0-45.3L109.2 288 416 288c17.7 0 32-14.3 32-32s-14.3-32-32-32l-306.7 0L214.6 118.6c12.5-12.5 12.5-32.8 0-45.3s-32.8-12.5-45.3 0l-160 160z"/></svg> Fermer</div>
        <div id="activity-focus-content"></div>
    </div>

    {edit_modal_html}

    <script>
    const allActivities = {activities_json};
    const fullDetailsDict = {full_details_json};
    const gpxFallbackDict = {gpx_fallback_json};
    const climbMapSegmentsDict = {climb_segments_json};
    const climbSvgDict = {climb_svg_json};
    const climbCoordsDict = {climb_coords_json};
    const climbMetaDict = {climb_meta_json};
    const colCatalog = {col_catalog_json};
    const HIDE_STATS = {hide_stats_js};

    let chartInstance = null;
    let allVisible = false;
    let myLeafletMap = null;
    window.currentClimbHighlight = null;
    window.currentActivityBounds = null;

    function fetchAltitude(lat, lon, label, source_context) {{
        fetch(`https://geodesy.geo.admin.ch/reframe/wgs84tolv95?easting=${{lon}}&northing=${{lat}}`)
        .then(res => res.json())
        .then(coord => fetch(`https://api3.geo.admin.ch/rest/services/height?easting=${{coord.easting}}&northing=${{coord.northing}}`))
        .then(res => res.json())
        .then(data => {{
            if (data.height && parseFloat(data.height) > 0) showAltitudePopup(lat, lon, label, parseFloat(data.height).toFixed(1) + ' m', '🇨🇭 Swisstopo');
            else throw new Error("Hors Suisse");
        }})
        .catch(err => {{
            fetch(`https://api.open-elevation.com/api/v1/lookup?locations=${{lat}},${{lon}}`)
            .then(res => res.json())
            .then(data => {{
                if (data && data.results && data.results.length > 0) showAltitudePopup(lat, lon, label, parseFloat(data.results[0].elevation).toFixed(1) + ' m', '🌍 Open-Elevation');
                else showAltitudePopup(lat, lon, label, 'N/A', 'Erreur');
            }}).catch(e => showAltitudePopup(lat, lon, label, 'N/A', 'Réseau'));
        }});
    }}

    function showAltitudePopup(lat, lon, label, heightVal, source) {{
        L.popup().setLatLng([lat, lon]).setContent(`<div style="font-family:'Oswald',sans-serif; text-align:center; padding:5px;"><div style="font-size:12px; color:#d62728; font-weight:bold; text-transform:uppercase;">${{source}}</div><div style="font-size:16px; font-weight:bold; color:#333;">${{label}}</div><div style="font-size:14px; font-weight:bold; color:#1f77b4; margin-top:4px;">⛰️ Altitude : ${{heightVal}}</div></div>`).openOn(myLeafletMap);
    }}

    function searchCH() {{
        let q = document.getElementById('ch-search-input').value;
        if(!q) return;
        fetch(`https://api3.geo.admin.ch/rest/services/ech/SearchServer?searchText=${{encodeURIComponent(q)}}&type=locations`)
        .then(res => res.json())
        .then(data => {{
            if(data.results && data.results.length > 0) {{
                let lat = parseFloat(data.results[0].attrs.lat), lon = parseFloat(data.results[0].attrs.lon);
                myLeafletMap.setView([lat, lon], 14);
                fetchAltitude(lat, lon, data.results[0].attrs.label.replace(/<[^>]*>?/gm, ''), "Recherche");
            }} else alert("Lieu non trouvé en Suisse.");
        }}).catch(err => console.log(err));
    }}

    function searchGlobal() {{
        let q = document.getElementById('global-search-input').value;
        if(!q) return;
        fetch(`https://nominatim.openstreetmap.org/search?q=${{encodeURIComponent(q)}}&format=json&limit=1&accept-language=fr,en`)
        .then(res => res.json())
        .then(data => {{
            if(data && data.length > 0) {{
                let lat = parseFloat(data[0].lat), lon = parseFloat(data[0].lon);
                myLeafletMap.setView([lat, lon], 14);
                fetchAltitude(lat, lon, data[0].name ? data[0].name : q, "Recherche Mondiale");
            }} else alert("Lieu non trouvé dans le monde.");
        }}).catch(err => console.log(err));
    }}

    function openClimbPanel(climb_id) {{
        let meta = climbMetaDict[climb_id];
        if(!meta) return;
        
        let titlePrefix = meta.official_name ? ("🏔️ " + meta.official_name + " 🇨🇭 — ") : "Profil Détaillé — ";
        document.getElementById('climb-panel-title').innerText = titlePrefix + meta.title;
        document.getElementById('climb-panel-content-inner').innerHTML = climbSvgDict[climb_id];
        
        if (!meta.official_name) {{
            fetch(`https://overpass-api.de/api/interpreter?data=[out:json];node(around:400,${{meta.peak_lat}},${{meta.peak_lon}})["mountain_pass"="yes"];out;`)
            .then(r => r.json()).then(data => {{
                if(data.elements && data.elements.length > 0 && data.elements[0].tags.name) document.getElementById('climb-panel-title').innerText = "🏔️ " + data.elements[0].tags.name + " — " + meta.title;
            }}).catch(e => console.log(e));
        }}
        
        let navHtml = '<div style="display:flex; justify-content:space-between; margin-top:20px; border-top:2px solid #eee; padding-top:15px; gap:10px;">';
        let prevId = 'climb_' + meta.act_id + '_' + (meta.idx - 1);
        let nextId = 'climb_' + meta.act_id + '_' + (meta.idx + 1);
        navHtml += climbMetaDict[prevId] ? `<button onclick="openClimbPanel('${{prevId}}')" style="flex:1; padding:12px; background:#1f77b4; color:white; border:none; border-radius:8px; cursor:pointer; font-weight:bold; box-shadow:0 2px 4px rgba(0,0,0,0.2); transition:0.2s;">◀ Montée précédente</button>` : `<div style="flex:1;"></div>`;
        navHtml += climbMetaDict[nextId] ? `<button onclick="openClimbPanel('${{nextId}}')" style="flex:1; padding:12px; background:#1f77b4; color:white; border:none; border-radius:8px; cursor:pointer; font-weight:bold; box-shadow:0 2px 4px rgba(0,0,0,0.2); transition:0.2s;">Montée suivante ▶</button>` : `<div style="flex:1;"></div>`;
        navHtml += '</div>';

        document.getElementById('climb-nav-container').innerHTML = navHtml;
        document.getElementById('climb-side-panel').classList.add('active');
        
        if (window.currentClimbHighlight) myLeafletMap.removeLayer(window.currentClimbHighlight);
        let layers = [];
        climbMapSegmentsDict[climb_id].forEach(seg => layers.push(L.polyline(seg.coords, {{color: seg.color, weight: 8, opacity: 1.0, className: 'vv-climb-segment'}})));
        window.currentClimbHighlight = L.layerGroup(layers).addTo(myLeafletMap);
        
        let coords = climbCoordsDict[climb_id];
        let isDesktop = window.innerWidth > 768;
        myLeafletMap.fitBounds(L.latLngBounds(coords), {{paddingTopLeft: [isDesktop ? 480 : 20, 20], paddingBottomRight: [20, isDesktop ? 20 : window.innerHeight * 0.65], animate: true, duration: 1.5}});
    }}

    function closeClimbPanel() {{
        document.getElementById('climb-side-panel').classList.remove('active');
        if (window.currentClimbHighlight) {{ myLeafletMap.removeLayer(window.currentClimbHighlight); window.currentClimbHighlight = null; }}
        if (window.currentActivityBounds) myLeafletMap.fitBounds(window.currentActivityBounds, {{paddingTopLeft: [window.innerWidth > 768 ? 430 : 20, 20], paddingBottomRight: [20, window.innerWidth > 768 ? 20 : window.innerHeight * 0.55], animate: true, duration: 1.0}});
    }}
    
    function zoomClimbSVG() {{
        document.getElementById('svg-lightbox-content').innerHTML = document.getElementById('climb-panel-content-inner').innerHTML;
        let clonedBtn = document.getElementById('svg-lightbox-content').querySelector('.zoom-btn');
        if(clonedBtn) clonedBtn.style.display = 'none';
        document.getElementById('svg-lightbox-overlay').style.display = 'flex';
    }}
    
    function closeSvgLightbox() {{ document.getElementById('svg-lightbox-overlay').style.display = 'none'; document.getElementById('svg-lightbox-content').innerHTML = ''; }}
    function openLightbox(src) {{ document.getElementById('lightbox-img').src = src; document.getElementById('lightbox-overlay').style.display = 'flex'; }}
    function closeLightbox() {{ document.getElementById('lightbox-overlay').style.display = 'none'; document.getElementById('lightbox-img').src = ""; }}

    function formatTimeJS(seconds) {{
        let h = Math.floor(seconds / 3600); let m = Math.floor((seconds % 3600) / 60);
        return h > 0 ? h + "h " + m.toString().padStart(2, '0') + "m" : m + " min";
    }}

    function sanitizeFilename(name) {{ return (name || 'sortie').replace(/[^a-zA-Z0-9 _.-]/g, '_').trim() || 'sortie'; }}

    function shareActivity(id, name) {{
        const link = location.origin + location.pathname + '#activity=' + id;
        const shareData = {{ title: 'Atlas Cycling — ' + name, text: name, url: link }};
        if (navigator.share) navigator.share(shareData).catch(() => {{}});
        else if (navigator.clipboard) navigator.clipboard.writeText(link).then(() => alert("🔗 Lien copié !\\n" + link)).catch(() => prompt("Copie ce lien :", link));
        else prompt("Copie ce lien :", link);
    }}

    function downloadGPX(id) {{
        const act = allActivities.find(a => a.id === id);
        if (!act) return;
        if (act.gpxFile) {{
            const a = document.createElement('a'); a.href = act.gpxFile; a.download = sanitizeFilename(act.name) + '.gpx'; document.body.appendChild(a); a.click(); a.remove(); return;
        }}
        const fb = gpxFallbackDict[id];
        if (!fb || !fb.coords || fb.coords.length < 2) {{ alert("GPX indisponible."); return; }}
        let points = fb.coords.map((c, i) => `<trkpt lat="${{c[0]}}" lon="${{c[1]}}"><ele>${{(fb.elevations && fb.elevations[i] !== undefined) ? fb.elevations[i] : 0}}</ele></trkpt>`).join('\\n      ');
        let gpxContent = `<?xml version="1.0" encoding="UTF-8"?>\\n<gpx version="1.1" creator="Atlas Cycling" xmlns="http://www.topografix.com/GPX/1/1">\\n  <trk>\\n    <name>${{act.name || 'Sortie'}}</name>\\n    <trkseg>\\n      ${{points}}\\n    </trkseg>\\n  </trk>\\n</gpx>`;
        let blob = new Blob([gpxContent], {{type: 'application/gpx+xml'}});
        let url = URL.createObjectURL(blob);
        let a = document.createElement('a'); a.href = url; a.download = sanitizeFilename(act.name) + '.gpx'; document.body.appendChild(a); a.click(); a.remove(); URL.revokeObjectURL(url);
    }}

    function getAvailableYears() {{
        let years = new Set();
        allActivities.forEach(a => years.add(a.date.substring(0, 4)));
        return Array.from(years).sort().reverse();
    }}

    function refreshDashboard() {{
        if (HIDE_STATS) return;
        const year = document.getElementById('dash-year-select').value;
        const sport = document.getElementById('dash-sport-select').value;
        
        let filtered = allActivities.filter(a => {{
            if (year !== 'all' && !a.date.startsWith(year)) return false;
            if (sport !== 'all' && a.sport !== sport) return false;
            return true;
        }});
        
        let km = 0, dplus = 0, duration = 0;
        let months = Array(12).fill(0);
        filtered.forEach(a => {{
            km += a.dist; dplus += a.ele; duration += (a.duration || 0);
            let mIdx = parseInt(a.date.substring(5, 7), 10) - 1;
            if (mIdx >= 0 && mIdx < 12) months[mIdx] += a.dist;
        }});

        document.getElementById('dash-count').innerText = filtered.length;
        document.getElementById('dash-km').innerText = km.toLocaleString('fr-FR', {{maximumFractionDigits: 0}}) + " km";
        document.getElementById('dash-dplus').innerText = dplus.toLocaleString('fr-FR', {{maximumFractionDigits: 0}}) + " m";
        document.getElementById('dash-time').innerText = formatTimeJS(duration);

        let everestPct = Math.min(999, (dplus / 8848) * 100);
        let dashEverest = document.getElementById('dash-everest');
        if(dashEverest) dashEverest.innerText = everestPct.toFixed(1) + "% (" + (dplus/8848).toFixed(2) + "×)";
        let dashEverestBar = document.getElementById('dash-everest-bar');
        if(dashEverestBar) dashEverestBar.style.width = Math.min(100, everestPct) + "%";

        const ctx = document.getElementById('monthlyChart').getContext('2d');
        if (chartInstance) chartInstance.destroy();
        chartInstance = new Chart(ctx, {{
            type: 'bar', data: {{ labels: ['J', 'F', 'M', 'A', 'M', 'J', 'J', 'A', 'S', 'O', 'N', 'D'], datasets: [{{ data: months, backgroundColor: '#1f77b4', borderRadius: 4 }}] }},
            options: {{ responsive: true, maintainAspectRatio: false, plugins: {{ legend: {{ display: false }} }}, scales: {{ x: {{ grid: {{ display: false }} }} }} }}
        }});
    }}

    window.allLeafletPolylines = [];
    window.allLeafletMarkers = [];
    function extractLeafletMarkers(layer) {{
        if (layer instanceof L.MarkerClusterGroup) {{
            layer.eachLayer(function(marker) {{
                if (marker.options && marker.options.icon && marker.options.icon.options && marker.options.icon.options.className && marker.options.icon.options.className.includes('global-marker-wrapper')) {{
                     let match = marker.options.icon.options.className.match(/garmin-([^\\s]+)/);
                     if (match) window.allLeafletMarkers.push({{ id: match[1], marker: marker, cluster: layer }});
                }}
            }});
        }} else if (layer.options && layer.options.className && layer.options.className.includes('activity-track') && typeof layer.getLatLngs === 'function') {{
            let match = layer.options.className.match(/track-([^\\s]+)/);
            if (match) {{
                window.allLeafletPolylines.push({{ id: match[1], polyline: layer }});
                layer.on('click', function(e) {{
                    L.DomEvent.stopPropagation(e);
                    let nearbyActs = [];
                    window.allLeafletPolylines.forEach(item => {{
                        let act = allActivities.find(a => a.id === item.id);
                        if(act && act._match && item.polyline._path && (item.polyline._path.classList.contains('show-track-forced') || item.polyline._path.classList.contains('show-track'))) {{
                            let distPx = Infinity;
                            const p = myLeafletMap.latLngToLayerPoint(e.latlng);
                            const latlngs = item.polyline.getLatLngs();
                            for (let i = 0; i < latlngs.length - 1; i++) {{
                                const p1 = myLeafletMap.latLngToLayerPoint(latlngs[i]);
                                const p2 = myLeafletMap.latLngToLayerPoint(latlngs[i+1]);
                                const d = L.LineUtil.pointToSegmentDistance(p, p1, p2);
                                if (d < distPx) distPx = d;
                            }}
                            if (distPx < 15) nearbyActs.push(act);
                        }}
                    }});
                    
                    if (nearbyActs.length > 0) {{
                        nearbyActs.sort((a,b) => (a.date < b.date) ? 1 : -1);
                        nearbyActs = nearbyActs.filter((v, i, a) => a.findIndex(t => (t.id === v.id)) === i);
                        let popupContent = `<div style="font-family: 'Segoe UI', sans-serif; min-width: 220px; max-height: 250px; overflow-y: auto; padding-right:5px;">
                            <div style="font-size: 14px; font-weight: 900; color: #d62728; margin-bottom: 8px; border-bottom: 2px solid #eee; padding-bottom:4px; position:sticky; top:0; background:white; z-index:10;">
                                🚴 ${{nearbyActs.length}} sortie(s) à cet endroit :
                            </div>`;
                        nearbyActs.forEach(a => {{
                            popupContent += `
                            <div style="background:#f8f9fa; border:1px solid #ccc; padding:8px; border-radius:6px; margin-bottom:6px; transition:0.2s;" onmouseover="this.style.borderColor='${{a.color}}'; this.style.backgroundColor='#f0f7ff';" onmouseout="this.style.borderColor='#ccc'; this.style.backgroundColor='#f8f9fa';">
                                <div style="font-size: 13px; font-weight: bold; color: ${{a.color}}; margin-bottom: 2px;">${{a.name}}</div>
                                <div style="font-size: 11px; color: #666; margin-bottom: 6px;">📅 ${{a.date}} | 📏 ${{a.dist}} km</div>
                                <button onclick="focusOnActivity('${{a.id}}')" style="width:100%; background:${{a.color}}; color:white; border:none; border-radius:4px; padding:6px; cursor:pointer; font-weight:bold; font-size:11px; box-shadow:0 1px 3px rgba(0,0,0,0.2);">
                                    🔍 Ouvrir cette sortie
                                </button>
                            </div>`;
                        }});
                        popupContent += `</div>`;
                        L.popup().setLatLng(e.latlng).setContent(popupContent).openOn(myLeafletMap);
                    }}
                }});
            }}
        }} else if (layer.eachLayer) {{
            layer.eachLayer(extractLeafletMarkers);
        }}
    }}

    function applyAdvancedFilters() {{
        let txt = document.getElementById('fil-text').value.toLowerCase();
        let sportVal = document.getElementById('fil-sport').value;
        let dMinDate = document.getElementById('fil-date-min').value;
        let dMaxDate = document.getElementById('fil-date-max').value;
        let dMin = parseFloat(document.getElementById('fil-dist-min').value) || 0;
        let dMax = parseFloat(document.getElementById('fil-dist-max').value) || 99999;
        let eMin = parseFloat(document.getElementById('fil-ele-min').value) || 0;
        let eMax = parseFloat(document.getElementById('fil-ele-max').value) || 99999;
        let gear = document.getElementById('fil-gear').value;

        let visibleCount = 0;
        let filteredActs = [];

        allActivities.forEach(a => {{
            let match = true;
            if (txt && !a.name.toLowerCase().includes(txt)) match = false;
            if (sportVal && a.sport !== sportVal) match = false;
            if (dMinDate && new Date(a.date) < new Date(dMinDate)) match = false;
            if (dMaxDate && new Date(a.date) > new Date(dMaxDate)) match = false;
            if (a.dist < dMin || a.dist > dMax) match = false;
            if (a.ele < eMin || a.ele > eMax) match = false;
            if (gear && (!a.gear || !a.gear.includes(gear))) match = false;

            a._match = match;
            if (match) {{
                visibleCount++;
                filteredActs.push(a);
            }} else {{
                document.querySelectorAll('.track-' + a.id).forEach(el => el.classList.remove('show-track', 'show-track-forced'));
            }}
        }});
        
        document.getElementById('filter-result-count').innerText = visibleCount;
        let listHtml = '';
        filteredActs.sort((a,b) => (a.date < b.date) ? 1 : -1).forEach(a => {{
            let photoIcon = a.has_photos ? ' 🖼️' : '';
            listHtml += `<div class="zone-item" onclick="focusOnActivity('${{a.id}}')" style="border-left:5px solid ${{a.color}};">
                <b style="font-size:15px; color:#222; display:block; margin-bottom:4px;">${{a.name}}${{photoIcon}}</b>
                <div style="color:#666; font-size:12px; font-weight:bold;">📅 ${{a.date}} &nbsp;|&nbsp; 📏 ${{a.dist}}km &nbsp;|&nbsp; ⛰️ ${{a.ele}}m+</div>
            </div>`;
        }});
        document.getElementById('filter-results-list').innerHTML = listHtml || '<div style="text-align:center; padding:20px; color:#888; font-style:italic;">Aucune activité ne correspond à vos filtres.</div>';

        if (window.allLeafletMarkers && window.allLeafletMarkers.length > 0) {{
            let toAddMap = new Map();
            let toRemoveMap = new Map();
            
            window.allLeafletMarkers.forEach(item => {{
                let act = allActivities.find(a => a.id === item.id);
                if (act) {{
                    if(!toAddMap.has(item.cluster)) toAddMap.set(item.cluster, []);
                    if(!toRemoveMap.has(item.cluster)) toRemoveMap.set(item.cluster, []);
                    
                    if (act._match && !item.cluster.hasLayer(item.marker)) toAddMap.get(item.cluster).push(item.marker);
                    else if (!act._match && item.cluster.hasLayer(item.marker)) toRemoveMap.get(item.cluster).push(item.marker);
                }}
            }});
            
            toRemoveMap.forEach((markers, cluster) => {{ if(markers.length > 0) cluster.removeLayers(markers); }});
            toAddMap.forEach((markers, cluster) => {{ if(markers.length > 0) cluster.addLayers(markers); }});
        }}
    }}

    function resetFilters() {{
        document.getElementById('fil-text').value = ''; document.getElementById('fil-sport').value = '';
        document.getElementById('fil-date-min').value = ''; document.getElementById('fil-date-max').value = '';
        document.getElementById('fil-dist-min').value = ''; document.getElementById('fil-dist-max').value = '';
        document.getElementById('fil-ele-min').value = ''; document.getElementById('fil-ele-max').value = '';
        document.getElementById('fil-gear').value = ''; 
        applyAdvancedFilters();
    }}

    function focusOnActivity(id) {{
        let act = allActivities.find(a => a.id === id);
        if(!act) return;

        window.currentActivityBounds = act.bounds;
        document.body.classList.add('focus-mode');
        if(myLeafletMap) myLeafletMap.closePopup();
        
        document.getElementById('explorer-modal').style.display = 'none';
        document.getElementById('zone-results-modal').style.display = 'none';
        document.getElementById('main-action-btns').style.transform = 'translateY(150px) translateX(-50%)';
        
        document.getElementById('activity-focus-content').innerHTML = fullDetailsDict[id];
        document.getElementById('activity-focus-panel').classList.add('active');
        
        document.querySelectorAll('.activity-track').forEach(el => el.classList.remove('show-track', 'show-track-forced'));
        document.querySelectorAll('.track-' + id).forEach(el => el.classList.add('show-track-forced'));
        document.querySelectorAll('.start-end-wrapper').forEach(el => el.classList.remove('active-focus'));
        document.querySelectorAll('.track-' + id + '-points').forEach(el => el.classList.add('active-focus'));
        
        if (myLeafletMap && act.bounds) {{
            myLeafletMap.fitBounds(act.bounds, {{paddingTopLeft: [window.innerWidth > 768 ? 430 : 20, 20], paddingBottomRight: [20, window.innerWidth > 768 ? 20 : window.innerHeight * 0.55], animate: true, duration: 1.5}});
        }}
    }}

    function closeFocusPanel() {{
        document.body.classList.remove('focus-mode');
        document.querySelectorAll('.start-end-wrapper').forEach(el => el.classList.remove('active-focus'));
        document.getElementById('activity-focus-panel').classList.remove('active');
        closeClimbPanel(); 
        document.getElementById('main-action-btns').style.transform = 'translateY(0) translateX(-50%)';
        if (!allVisible) document.querySelectorAll('.activity-track').forEach(el => el.classList.remove('show-track', 'show-track-forced'));
        else document.querySelectorAll('.activity-track').forEach(el => el.classList.add('show-track-forced'));
    }}

    function anyModalOpen() {{
        return ['explorer-modal', 'zone-results-modal', 'edit-modal-overlay', 'svg-lightbox-overlay', 'cols-modal', 'on-this-day-modal'].some(id => {{ let el = document.getElementById(id); return el && el.style.display === 'flex'; }});
    }}

    document.addEventListener('keydown', function(e) {{
        if (e.key !== 'Escape') return;
        if (document.getElementById('lightbox-overlay').style.display === 'flex') {{ closeLightbox(); return; }}
        if (document.getElementById('svg-lightbox-overlay').style.display === 'flex') {{ closeSvgLightbox(); return; }}
        if (document.getElementById('climb-side-panel').classList.contains('active')) {{ closeClimbPanel(); return; }}
        if (anyModalOpen()) {{
            ['explorer-modal', 'zone-results-modal', 'edit-modal-overlay', 'cols-modal', 'on-this-day-modal'].forEach(id => {{ let el = document.getElementById(id); if (el) el.style.display = 'none'; }});
            return;
        }}
        if (document.body.classList.contains('focus-mode')) closeFocusPanel();
    }});

    document.addEventListener("DOMContentLoaded", function() {{
        if (!HIDE_STATS) {{
            let selectDash = document.getElementById('dash-year-select');
            getAvailableYears().forEach(y => selectDash.appendChild(new Option(y, y)));
            refreshDashboard();
        }}

        let colsBtn = document.getElementById('cols-catalog-btn');
        if (colCatalog.length > 0 && colsBtn) colsBtn.style.display = 'flex';
        computeOnThisDay();

        if (location.hash && location.hash.startsWith('#activity=')) {{
            let sharedId = decodeURIComponent(location.hash.replace('#activity=', ''));
            if (allActivities.some(a => a.id === sharedId)) setTimeout(() => focusOnActivity(sharedId), 500);
        }}

        setTimeout(() => {{
            const addTitle = (selector, title) => {{ document.querySelectorAll(selector).forEach(el => el.title = title); }};
            addTitle('.leaflet-draw-draw-polygon', 'Dessiner un polygone');
            addTitle('.leaflet-draw-draw-rectangle', 'Dessiner un rectangle');
            addTitle('.leaflet-control-fullscreen-button', 'Plein écran');
            addTitle('.leaflet-control-locate a', 'Me géolocaliser');
            addTitle('.leaflet-control-layers-toggle', 'Fonds de carte');
            addTitle('.leaflet-control-measure', 'Mesurer');
        }}, 1200);

        for (let key in window) {{
            if (key.startsWith("map_") && window[key] instanceof L.Map) {{
                myLeafletMap = window[key];
                myLeafletMap.eachLayer(extractLeafletMarkers);
                applyAdvancedFilters();
                
                let drawnItems = new L.FeatureGroup();
                myLeafletMap.addLayer(drawnItems);
                myLeafletMap.on(L.Draw.Event.CREATED, function (e) {{
                    drawnItems.clearLayers();
                    var layer = e.layer;
                    drawnItems.addLayer(layer);
                    var bounds = layer.getBounds();
                    var found = allActivities.filter(a => bounds.contains([a.lat, a.lng]));
                    showZoneResults(found);
                }});

                myLeafletMap.on('contextmenu', function(e) {{
                    fetchAltitude(e.latlng.lat, e.latlng.lng, "📍 Position sélectionnée", "Clic sur la carte");
                }});
                break;
            }}
        }}
    }});

    function showZoneResults(activities) {{
        const panel = document.getElementById('zone-results-modal');
        const list = document.getElementById('zone-results-list');
        panel.style.display = 'flex';
        if(activities.length === 0) {{
            list.innerHTML = '<div style="text-align:center; padding:20px; color:#888;">Aucune activité trouvée.</div>';
            let countEl = document.getElementById('zone-count');
            if(countEl) countEl.innerText = "0"; 
            return;
        }}
        let countEl = document.getElementById('zone-count');
        if(countEl) countEl.innerText = activities.length;
        activities.sort((a,b) => (a.date < b.date) ? 1 : -1);
        
        let html = '';
        activities.forEach(a => {{
            let photoIcon = a.has_photos ? ' 🖼️' : '';
            html += `<div class="zone-item" onclick="focusOnActivity('${{a.id}}')" style="border-left:5px solid ${{a.color}};">
                <b style="font-size:15px; color:#222; display:block; margin-bottom:4px;">${{a.name}}${{photoIcon}}</b>
                <div style="color:#666; font-size:12px; font-weight:bold;">📅 ${{a.date}} &nbsp;|&nbsp; 📏 ${{a.dist}}km &nbsp;|&nbsp; ⛰️ ${{a.ele}}m+</div>
            </div>`;
        }});
        list.innerHTML = html;
    }}

    function openColsModal() {{
        const modal = document.getElementById('cols-modal');
        const list = document.getElementById('cols-list');
        let countEl = document.getElementById('cols-count');
        
        if (!modal || !list) return;
        if (countEl) countEl.innerText = colCatalog.length;

        if (colCatalog.length === 0) {{
            list.innerHTML = '<div style="text-align:center; padding:20px; color:#888;">Aucune montée détectée pour le moment.</div>';
        }} else {{
            let html = '';
            colCatalog.forEach(c => {{
                let officialBadge = c.official ? ' <span style="background:#1f77b4;color:#fff;font-size:9px;font-weight:800;padding:1px 5px;border-radius:3px;">🇨🇭 SWISSTOPO</span>' : '';
                let timesBadge = c.times > 1 ? `<span style="background:#8c564b;color:#fff;font-size:11px;font-weight:bold;padding:2px 8px;border-radius:10px;">×${{c.times}}</span>` : '';
                html += `<div class="zone-item" onclick="document.getElementById('cols-modal').style.display='none'; focusOnActivity('${{c.latest_act_id}}'); setTimeout(() => openClimbPanel('${{c.latest_c_id}}'), 400);">
                    <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:4px;">
                        <b style="font-size:15px; color:#222;">${{c.name}}${{officialBadge}}</b>
                        ${{timesBadge}}
                    </div>
                    <div style="color:#666; font-size:12px; font-weight:bold;">
                        🚵 ${{c.sports.join(', ')}} &nbsp;|&nbsp; 📈 Record ${{c.best_grad}}% (${{c.best_cat}}) &nbsp;|&nbsp; ⛰️ Max +${{c.best_gain}}m
                    </div>
                    <div style="color:#999; font-size:11px; margin-top:2px;">
                        Première fois : ${{c.first_date}} ${{c.times > 1 ? '&nbsp;→&nbsp; Dernière fois : ' + c.last_date : ''}}
                    </div>
                </div>`;
            }});
            list.innerHTML = html;
        }}
        modal.style.display = 'flex';
    }}

    let onThisDayMatches = [];
    function computeOnThisDay() {{
        const today = new Date();
        const mmdd = String(today.getMonth() + 1).padStart(2,'0') + '-' + String(today.getDate()).padStart(2,'0');
        const thisYear = today.getFullYear();
        onThisDayMatches = allActivities.filter(a => a.date.substring(5,10) === mmdd && parseInt(a.date.substring(0,4)) < thisYear);
        onThisDayMatches.sort((a,b) => (a.date < b.date) ? 1 : -1);
        if (onThisDayMatches.length > 0) {{
            let btn = document.getElementById('on-this-day-btn');
            if (btn) btn.style.display = 'flex';
        }}
    }}
    
    function openOnThisDayModal() {{
        const modal = document.getElementById('on-this-day-modal');
        const list = document.getElementById('on-this-day-list');
        if (!modal || !list) return;
        
        let html = '';
        onThisDayMatches.forEach(a => {{
            let yearsAgo = new Date().getFullYear() - parseInt(a.date.substring(0,4));
            let photoIcon = a.has_photos ? ' 🖼️' : '';
            html += `<div class="zone-item" onclick="document.getElementById('on-this-day-modal').style.display='none'; focusOnActivity('${{a.id}}');" style="border-left:5px solid ${{a.color}};">
                <div style="font-size:11px; color:#d62728; font-weight:bold; text-transform:uppercase; margin-bottom:2px;">Il y a ${{yearsAgo}} an${{yearsAgo>1?'s':''}}</div>
                <b style="font-size:15px; color:#222; display:block; margin-bottom:4px;">${{a.name}}${{photoIcon}}</b>
                <div style="color:#666; font-size:12px; font-weight:bold;">📅 ${{a.date}} &nbsp;|&nbsp; 📏 ${{a.dist}}km &nbsp;|&nbsp; ⛰️ ${{a.ele}}m+</div>
            </div>`;
        }});
        list.innerHTML = html || '<div style="text-align:center; padding:20px; color:#888;">Rien à ce jour-là.</div>';
        modal.style.display = 'flex';
    }}

    function toggleAllTracks() {{
        allVisible = !allVisible;
        document.getElementById('toggle-tracks-label').innerText = allVisible ? " Masquer les tracés" : " Afficher la toile d'araignée";
        document.querySelectorAll('.activity-track').forEach(el => el.classList.toggle('show-track-forced', allVisible));
    }}

    function shutdownServer() {{
        if(confirm("Veux-tu vraiment éteindre le serveur en arrière-plan et fermer la carte ?")) {{
            fetch('/api/shutdown', {{ method: 'POST' }}).then(() => {{
                document.body.innerHTML = `<div style="display:flex; flex-direction:column; align-items:center; justify-content:center; height:100vh; background:#f0f2f5; font-family:'Segoe UI', sans-serif;"><h1 style="color:#dc3545; font-size:45px; margin-bottom:10px;">✅ Serveur éteint.</h1><p style="color:#555; font-size:20px;">Tu peux fermer cet onglet.</p></div>`;
            }}).catch(() => alert("Le serveur est déjà éteint."));
        }}
    }}

    function openEditModal(id, comment, name) {{
        document.getElementById('edit-act-id').value = id;
        document.getElementById('edit-comment').value = comment;
        document.getElementById('edit-name').value = name;
        document.getElementById('edit-photo').value = "";
        let modal = document.getElementById('edit-modal-overlay');
        if(modal) modal.style.display = 'flex';
    }}
    function closeEditModal() {{ 
        let modal = document.getElementById('edit-modal-overlay');
        if(modal) modal.style.display = 'none'; 
    }}

    function saveActivityData() {{
        document.querySelector('.btn-apply').style.display = 'none';
        document.getElementById('save-loader').style.display = 'block';
        
        let id = document.getElementById('edit-act-id').value;
        let comment = document.getElementById('edit-comment').value;
        let newName = document.getElementById('edit-name').value;
        let fileInput = document.getElementById('edit-photo');
        
        let payload = {{ "act_id": id, "comment": comment, "name": newName, "photos_b64": [] }};
        
        if (fileInput.files.length > 0) {{
            let promises = Array.from(fileInput.files).map(file => {{
                return new Promise((resolve) => {{
                    let reader = new FileReader();
                    reader.onload = e => resolve(e.target.result);
                    reader.readAsDataURL(file);
                }});
            }});
            
            Promise.all(promises).then(results => {{
                payload["photos_b64"] = results;
                sendPostRequest(payload);
            }});
        }} else {{ 
            sendPostRequest(payload); 
        }}
    }}

    function sendPostRequest(payload) {{
        fetch('/api/update_activity', {{ method: 'POST', headers: {{ 'Content-Type': 'application/json' }}, body: JSON.stringify(payload)
        }}).then(res => res.json()).then(data => {{ window.location.reload(); 
        }}).catch(err => {{ alert("Mode Lecture Seule : Modifie tes données depuis l'ordinateur local."); closeEditModal(); document.querySelector('.btn-apply').style.display = 'block'; document.getElementById('save-loader').style.display = 'none'; }});
    }}
    </script>
    """
    m.get_root().html.add_child(folium.Element(custom_ui))
    m.get_root().title = APP_TITLE + (" · Aperçu public" if public_mode else "")
    
    output_path = MAP_HTML_PUBLIC_PATH if public_mode else MAP_HTML_PATH
    m.save(output_path)
    return output_path

# =========================================================
# 3️⃣ SERVEUR WEB LOCAL (PORT DYNAMIQUE & SHUTDOWN)
# =========================================================
class AtlasServerHandler(http.server.BaseHTTPRequestHandler):
    def log_message(self, format, *args): pass 
    
    def do_GET(self):
        # Séparation totale du serveur local : 
        # / ou /index.html = Carte publique
        # /atlas_prive.html = Carte privée
        parsed_path = urllib.parse.unquote(self.path.lstrip('/'))
        if self.path == '/' or self.path == '/index.html':
            target_file = os.path.join(DOSSIER_BASE, 'index.html')
        elif self.path == '/atlas_prive.html':
            target_file = os.path.join(DOSSIER_BASE, 'atlas_prive.html')
        else:
            target_file = os.path.join(DOSSIER_BASE, parsed_path)

        if os.path.exists(target_file) and os.path.isfile(target_file):
            mime_type, _ = mimetypes.guess_type(target_file)
            self.send_response(200)
            self.send_header('Content-type', mime_type or 'application/octet-stream')
            # 🛑 ANTI-CACHE PUISSANT POUR ÉVITER LES BUGS SUR MOBILE
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.end_headers()
            with open(target_file, 'rb') as f:
                self.wfile.write(f.read())
        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):
        if self.path == '/api/shutdown':
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({'status': 'ok'}).encode('utf-8'))
            threading.Thread(target=self.server.shutdown).start()
            return
            
        if self.path == '/api/update_activity':
            content_length = int(self.headers['Content-Length'])
            post_data = self.rfile.read(content_length)
            data = json.loads(post_data.decode('utf-8'))
            
            act_id = data.get("act_id")
            comment = data.get("comment", "")
            new_name = data.get("name", "")
            photos_b64 = data.get("photos_b64", [])
            
            db = load_db()
            if act_id in db["activities"]:
                db["activities"][act_id]["comment"] = comment
                if new_name:
                    db["activities"][act_id]["name"] = new_name
                
                if photos_b64:
                    if "photos" not in db["activities"][act_id]:
                        db["activities"][act_id]["photos"] = []
                        
                    for idx, b64_str in enumerate(photos_b64):
                        try:
                            header, encoded = b64_str.split(",", 1)
                            file_ext = header.split(";")[0].split("/")[1]
                            if file_ext == "jpeg": file_ext = "jpg"
                            
                            file_name = f"{act_id}_{int(time.time() * 1000)}_{idx}.{file_ext}"
                            filepath = os.path.join(DOSSIER_PHOTOS, file_name)
                            
                            with open(filepath, "wb") as f:
                                f.write(base64.b64decode(encoded))
                                
                            db["activities"][act_id]["photos"].append(f"photos/{file_name}")
                        except Exception as e:
                            print(f"Erreur d'image : {e}")
                
                save_db(db)
                # Met à jour les deux cartes après une édition
                generate_map(public_mode=False)
                out = generate_map(public_mode=True)
                shutil.copy2(out, os.path.join(DOSSIER_BASE, "index.html"))
                
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({'status': 'ok'}).encode('utf-8'))
            else:
                self.send_response(400)
                self.end_headers()

class ThreadingSimpleServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    allow_reuse_address = True

def _try_open_windows_firewall(port):
    if sys.platform != "win32":
        return
    try:
        rule_name = "Atlas Cycling (auto)"
        subprocess.run(
            ["netsh", "advfirewall", "firewall", "add", "rule",
             f"name={rule_name}", "dir=in", "action=allow", "protocol=TCP",
             f"localport={port}", "profile=private"],
            capture_output=True, timeout=5, check=False,
        )
    except Exception:
        pass


def start_server():
    # En Option 2, on génère directement les 2 pour que les 2 liens locaux marchent
    generate_map(public_mode=False)
    out = generate_map(public_mode=True)
    shutil.copy2(out, os.path.join(DOSSIER_BASE, "index.html"))
    
    port = 8080
    max_port = 8095
    server = None
    
    while port <= max_port:
        try:
            server = ThreadingSimpleServer(('0.0.0.0', port), AtlasServerHandler)
            break
        except OSError:
            port += 1
            
    if server is None:
        print("\n❌ Impossible de lancer le serveur. Tous les ports sont occupés.")
        return

    local_ip = get_local_ip()
    _try_open_windows_firewall(port)

    scheme = "http"
    print(f"\n✅ Serveur Cartographique lancé !")
    print(f"\n💻 ACCÈS LOCAL (sur ce PC) :")
    print(f"   -> 🔓 Version Publique : {scheme}://localhost:{port}/")
    print(f"   -> 🔒 Version Privée   : {scheme}://localhost:{port}/atlas_prive.html")
    print(f"\n📱 ACCÈS MOBILE LOCAL (Même Wi-Fi) :")
    print(f"   -> 🔓 Version Publique : {scheme}://{local_ip}:{port}/")
    print(f"   -> 🔒 Version Privée   : {scheme}://{local_ip}:{port}/atlas_prive.html")
    print("\n🌐 ACCÈS 4G / INTERNET (Accessible partout via GitHub si Option 3 faite) :")
    print("   -> 🔓 Version Publique : https://gogniatnorman-doc.github.io/Atlas/")
    print("   -> 🔒 Version Privée   : https://gogniatnorman-doc.github.io/Atlas/atlas_prive.html")
    print("\n👉 Tu pourras éteindre le système local directement depuis la carte web (Bouton Rouge).")
    
    threading.Timer(1, lambda: webbrowser.open(f'{scheme}://localhost:{port}/atlas_prive.html')).start()
    
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass

# =========================================================
# 🎮 MENU PRINCIPAL
# =========================================================
def main_menu():
    while True:
        print("\n" + "═"*55)
        print(" 🗺️  ATLAS PERSONNEL GARMIN PRO (Application Web)")
        print("═"*55)
        print(" 1. 🔄 Synchroniser Garmin (nouvelles sorties + rattrapage GPX)")
        print(" 2. 🌍 Lancer la Carte Interactive (Ordi & Mobile + Édition)")
        print(" 3. 📤 Générer et envoyer sur GitHub (Versions Publique ET Privée)")
        print(" 4. ❌ Quitter")
        print("═"*55)
        
        try:
            choix = input("👉 Ton choix : ").strip()
            
            if choix == "1":
                sync_garmin()
            elif choix == "2":
                start_server()
                break
            elif choix == "3":
                print("\n⚙️ Génération de la carte privée (complète)...")
                generate_map(public_mode=False)
                
                print("⚙️ Génération de la carte publique (allégée)...")
                out = generate_map(public_mode=True)
                
                index_path = os.path.join(DOSSIER_BASE, "index.html")
                try:
                    shutil.copy2(out, index_path)
                    print("✅ Fichier 'index.html' mis à jour.")
                except Exception:
                    pass

                # ANTI-ERREUR 404 POUR GITHUB PAGES
                # Crée un fichier invisible .nojekyll qui force GitHub à afficher atlas_prive.html
                nojekyll_path = os.path.join(DOSSIER_BASE, ".nojekyll")
                with open(nojekyll_path, "w") as f:
                    f.write("")

                print("\n🚀 Exécution automatique des commandes Git...")
                try:
                    # -A ajoute absolument tout, y compris le nouveau nom (atlas_prive.html) et .nojekyll
                    subprocess.run(["git", "add", "-A"], cwd=DOSSIER_BASE, check=True)
                    commit_msg = f"Mise à jour auto - {datetime.now().strftime('%H:%M:%S')}"
                    subprocess.run(["git", "commit", "-m", commit_msg], cwd=DOSSIER_BASE)
                    subprocess.run(["git", "push"], cwd=DOSSIER_BASE, check=True)
                    print("\n✅ PUSH RÉUSSI ! Ton site sera à jour d'ici 1 à 2 minutes.")
                except subprocess.CalledProcessError as e:
                    print(f"\n❌ Erreur Git lors de l'envoi. (Code: {e.returncode})")
                except Exception as e:
                    print(f"\n❌ Erreur inattendue : {e}")

                print("\n" + "═"*55)
                print(" 🌐 ACCÈS 4G / INTERNET (Accessible partout via GitHub) :")
                print("   -> 🔓 Version Publique (Allégée) : https://gogniatnorman-doc.github.io/Atlas/")
                print("   -> 🔒 Version Privée (Complète)  : https://gogniatnorman-doc.github.io/Atlas/atlas_prive.html")
                print("═"*55)
            elif choix == "4":
                print("👋 Bonne balade sur tes futurs parcours ! À bientôt.")
                break
            else:
                print("❌ Choix invalide.")
        except KeyboardInterrupt:
            sys.exit(0)

if __name__ == "__main__":
    main_menu()
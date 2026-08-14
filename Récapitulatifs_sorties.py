"""
=========================================================
  ATLAS PERSONNEL GARMIN — Application Web & Cartographie
=========================================================
Génère une carte Folium dynamique avec serveur web local.
Inclus : Wi-Fi, Graphiques (Chart.js), Focus plein écran,
Métriques WorldTour (VAM, Pente, Suffer Score, Maillots),
Palmarès filtrable par sport ET par année, téléchargement GPX.
NOUVEAUTÉ : Anti-clignotement absolu des marqueurs (SVG Scaling), 
UI 100% épurée (Fusion du Palmarès et des Filtres dans un menu Modal).
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

# =========================================================
# 📂 CONFIGURATION & DOSSIERS
# =========================================================
load_dotenv(r"C:\Users\gogni\Garmin.env")

DOSSIER_BASE = r"C:\Users\gogni\Documents\Code Garmin\Atlas"
DOSSIER_PHOTOS = os.path.join(DOSSIER_BASE, "photos")
DOSSIER_GPX = os.path.join(DOSSIER_BASE, "gpx")
DB_PATH = os.path.join(DOSSIER_BASE, "atlas_db.json")
MAP_HTML_PATH = os.path.join(DOSSIER_BASE, "ma_carte.html")
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

def load_db():
    with db_lock:
        if os.path.exists(DB_PATH):
            with open(DB_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
        return {"last_sync": None, "activities": {}}

def save_db(db):
    with db_lock:
        with open(DB_PATH, "w", encoding="utf-8") as f:
            json.dump(db, f, indent=2, ensure_ascii=False)

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
    except Exception:
        return '127.0.0.1'

# =========================================================
# 🔍 CLASSIFICATION & PARSING
# =========================================================
def classify_activity(activity):
    t = (activity.get('activityType', {}).get('typeKey', '') or '').lower()
    if any(x in t for x in ['mountain', 'vtt', 'enduro', 'downhill', 'dirt']): return "vtt"
    elif 'gravel' in t: return "gravel"
    elif any(x in t for x in ['cycling', 'road_biking', 'e_bike']): return "route"
    elif any(x in t for x in ['hiking', 'walking', 'mountaineering']): return "randonnee"
    elif any(x in t for x in ['cross_country_skiing', 'skate_skiing']): return "ski"
    return None

def extract_gpx_data(gpx_bytes):
    coords, elevations = [], []
    try:
        root = ET.fromstring(gpx_bytes)
        ns = {'gpx': 'http://www.topografix.com/GPX/1/1'}
        for trkpt in root.findall('.//gpx:trkpt', ns):
            lat, lon = float(trkpt.attrib['lat']), float(trkpt.attrib['lon'])
            ele_node = trkpt.find('gpx:ele', ns)
            ele = float(ele_node.text) if (ele_node is not None and ele_node.text) else 0.0
            coords.append([lat, lon])
            elevations.append(ele)
        return coords[::10], elevations[::10]
    except Exception:
        return [], []

def format_duration(seconds):
    if not seconds: return "N/A"
    h = int(seconds // 3600)
    m = int((seconds % 3600) // 60)
    return f"{h}h {m:02d}min" if h > 0 else f"{m} min"

def calculate_suffer_score(avg_hr, duration_s, fc_repos, fc_max):
    try:
        avg_hr = float(avg_hr)
    except (TypeError, ValueError):
        return 0
    if not avg_hr or not duration_s or fc_max <= fc_repos:
        return 0
    dur_min = duration_s / 60.0
    hr_ratio = (avg_hr - fc_repos) / (fc_max - fc_repos)
    hr_ratio = max(0.0, min(hr_ratio, 1.15))
    score = dur_min * hr_ratio * 0.64 * math.exp(1.92 * hr_ratio)
    return round(score)

def haversine_m(p1, p2):
    R = 6371000.0
    lat1, lon1 = math.radians(p1[0]), math.radians(p1[1])
    lat2, lon2 = math.radians(p2[0]), math.radians(p2[1])
    dlat = lat2 - lat1
    dlon = lon2 - lon1
    a = math.sin(dlat / 2) ** 2 + math.cos(lat1) * math.cos(lat2) * math.sin(dlon / 2) ** 2
    return 2 * R * math.asin(math.sqrt(min(1.0, a)))

def trim_track_endpoints(coords, elevations, trim_start_m=0, trim_end_m=0):
    if (not trim_start_m and not trim_end_m) or not coords or len(coords) < 3:
        return coords, elevations

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

    if start_idx >= end_idx:
        return coords, elevations

    trimmed_coords = coords[start_idx:end_idx + 1]
    trimmed_elevations = elevations[start_idx:end_idx + 1] if elevations else elevations
    return trimmed_coords, trimmed_elevations

def save_raw_gpx(act_id, gpx_bytes):
    try:
        path = os.path.join(DOSSIER_GPX, f"{act_id}.gpx")
        with open(path, "wb") as f:
            f.write(gpx_bytes)
        return f"gpx/{act_id}.gpx"
    except Exception as e:
        print(f"   ⚠️ Sauvegarde GPX échouée sur {act_id} : {e}")
        return None

def generate_svg_elevation(elevations, color):
    if not elevations or len(elevations) < 2:
        return ""
    w, h = 350, 70
    min_e, max_e = min(elevations), max(elevations)
    diff = max_e - min_e if max_e > min_e else 1
    
    # CORRECTION : i, ele au lieu de i, enumerate
    pts = [f"{(i/(len(elevations)-1))*w:.1f},{h - ((ele-min_e)/diff)*h:.1f}" for i, ele in enumerate(elevations)]
    poly_pts = pts + [f"{w},{h}", f"0,{h}"]
    
    return f'''
    <div style="margin-top:15px; border:1px solid #e9ecef; border-radius:8px; background:#fdfdfd; padding:6px; box-shadow: inset 0 1px 3px rgba(0,0,0,0.05);">
        <div style="font-size:11px; color:#555; text-align:center; font-weight:bold; margin-bottom:4px; letter-spacing:1px; text-transform:uppercase;">Profil Altimétrique</div>
        <svg width="100%" height="{h}px" viewBox="0 0 {w} {h}" preserveAspectRatio="none">
            <polygon points="{" ".join(poly_pts)}" fill="{color}" opacity="0.15"/>
            <polyline points="{" ".join(pts)}" fill="none" stroke="{color}" stroke-width="2.5"/>
            <text x="3" y="12" fill="#555" font-size="10" font-weight="bold">{int(max_e)}m</text>
            <text x="3" y="{h - 4}" fill="#555" font-size="10" font-weight="bold">{int(min_e)}m</text>
        </svg>
    </div>
    '''

# =========================================================
# 1️⃣ SYNCHRONISATION GARMIN
# =========================================================
def sync_garmin():
    db = load_db()
    print("\n🔄 Connexion à Garmin Connect...")
    try:
        client = get_garmin_client()
    except Exception as e:
        print(f"❌ Erreur connexion : {e}")
        return

    print("📥 Récupération des activités (nouvelles + rattrapage GPX manquants)...")
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
                        print(f"   ⚠️ Rattrapage GPX échoué sur {act_id} : {e}")
                continue

            sport = classify_activity(act)
            distance_km = round((act.get('distance') or 0) / 1000, 2)
            if not sport or distance_km < 1.0: continue
                
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
                    
                db["activities"][act_id] = {
                    "id": act_id,
                    "name": act.get("activityName", "Activité sans nom"),
                    "date": act.get("startTimeLocal", "")[:10],
                    "sport": sport,
                    "exact_type": act.get('activityType', {}).get('typeKey', sport).replace('_', ' ').title(),
                    "distance": distance_km,
                    "elevation": elevation,
                    "duration": duration_s,
                    "speed": speed_kmh,
                    "max_speed": max_speed_kmh,
                    "hr": hr,
                    "calories": calories,
                    "gear": "",
                    "coords": coords,
                    "elevations": elevations,
                    "comment": "",
                    "photos": [],
                    "gpx_file": gpx_path,
                }
                n_added += 1
            except Exception as e:
                print(f"   ⚠️ Erreur sur {act_id} : {e}")
                
        if start >= 150 and n_added == 0 and n_backfilled == 0: break
        start += limit
        
    db["last_sync"] = datetime.now().isoformat()
    save_db(db)
    print(f"\n✅ Terminé ! {n_added} nouveau(x) tracé(s), {n_backfilled} GPX rattrapé(s).")
    generate_map()

# =========================================================
# 2️⃣ GÉNÉRATION DE LA CARTE INTERACTIVE (HTML)
# =========================================================
def generate_map(public_mode=False):
    db = load_db()
    cfg = PUBLIC_CONFIG
    trim_start = cfg["trim_debut_m"] if public_mode else 0
    trim_end = cfg["trim_fin_m"] if public_mode else 0
    hide_stats = public_mode and cfg["masquer_palmares"]
    hide_jerseys = public_mode and cfg["masquer_maillots"]
    hide_hr = public_mode and cfg["masquer_fc_calories"]
    hide_speed = public_mode and cfg["masquer_vitesse"]
    hide_comments = public_mode and cfg["masquer_commentaires"]

    map_center = [46.2333, 7.3500] 
    m = folium.Map(location=map_center, zoom_start=11, tiles=None, control_scale=True)
    
    folium.TileLayer('OpenTopoMap', name='⛰️ Topographie').add_to(m)
    folium.TileLayer('OpenStreetMap', name='🌐 Standard (OSM)').add_to(m)
    folium.TileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', attr='Esri', name='🛰️ Satellite').add_to(m)
    folium.TileLayer('CartoDB positron', name='🗺️ Clair Minimaliste').add_to(m)
    
    feature_groups, clusters = {}, {}
    for key, config in SPORTS_CONFIG.items():
        fg = folium.FeatureGroup(name=config["nom"], show=True)
        mc = plugins.MarkerCluster(name=f"📍 Clusters {config['nom']}")
        fg.add_child(mc)
        m.add_child(fg)
        feature_groups[key], clusters[key] = fg, mc

    search_features, all_heat_coords, js_activities_data = [], [], []
    full_details_dict = {}
    gpx_fallback_dict = {}
    unique_gears = set()

    observed_hrs = [a.get('hr') for a in db["activities"].values() if isinstance(a.get('hr'), (int, float))]
    FC_MAX = (max(observed_hrs) + 5) if observed_hrs else 190
    
    for act in db["activities"].values():
        raw_coords = act.get("coords")
        if not raw_coords or len(raw_coords) < 2: continue

        coords, elevations = trim_track_endpoints(
            raw_coords, act.get("elevations", []), trim_start, trim_end
        )
        if not coords or len(coords) < 2: continue

        sport_key = act["sport"]
        color = SPORTS_CONFIG[sport_key]["couleur"]
        dist = act.get('distance', 0)
        ele = act.get('elevation', 0)
        dur = act.get("duration", 0)
        has_photos = bool(act.get("photos"))
        
        # 🚴 RÈGLES STRICTES POUR LE MATÉRIEL 🚴
        if sport_key == "vtt": gear_str = "Olympia"
        elif sport_key == "gravel": gear_str = "Mérida Silex"
        elif sport_key == "route": gear_str = "Trek Madone SL6 Gen 8"
        else: gear_str = "Non spécifié"
        
        act['gear'] = gear_str
        unique_gears.add(gear_str)
        
        all_heat_coords.extend(coords)
        
        lats = [c[0] for c in coords]
        lons = [c[1] for c in coords]
        bounds = [[min(lats), min(lons)], [max(lats), max(lons)]]
        
        escaped_name = act['name'].replace("'", "\\'").replace('"', '&quot;')

        suffer = 0 if hide_hr else calculate_suffer_score(act.get('hr'), dur, FC_REPOS, FC_MAX)

        gpx_file_field = None if public_mode else act.get("gpx_file")
        if not gpx_file_field:
            gpx_fallback_dict[act['id']] = {"coords": coords, "elevations": elevations}

        js_activities_data.append({
            "id": act['id'],
            "name": escaped_name,
            "date": act['date'],
            "sport": SPORTS_CONFIG[sport_key]['nom'],
            "dist": dist,
            "ele": ele,
            "duration": dur,
            "speed": 0 if hide_speed else act.get('speed', 0),
            "suffer": suffer,
            "gear": gear_str.replace("'", "\\'"),
            "lat": coords[0][0],
            "lng": coords[0][1],
            "bounds": bounds,
            "color": color,
            "has_photos": has_photos,
            "gpxFile": gpx_file_field,
        })
        
        escaped_comment = "" if hide_comments else (act.get('comment') or "").replace("'", "\\'").replace('"', '&quot;')
        
        # ⚡ CALCULS WORLDTOUR
        vam = int((ele / dur) * 3600) if dur > 0 else 0
        gradient = round((ele / (dist * 500)) * 100, 1) if dist > 0 else 0
            
        effort_index = dist + (ele / 100) * 1.5
        if effort_index >= 80:
            diff_badge = "<span style='background:#d62728; color:white; padding:4px 10px; border-radius:12px; font-size:12px; font-weight:bold; box-shadow:0 2px 4px rgba(214,39,40,0.4);'>🏔️ Étape Reine (Extrême)</span>"
        elif effort_index >= 50:
            diff_badge = "<span style='background:#ff7f0e; color:white; padding:4px 10px; border-radius:12px; font-size:12px; font-weight:bold; box-shadow:0 2px 4px rgba(255,127,14,0.4);'>🔥 Sortie Exigeante</span>"
        elif effort_index >= 25:
            diff_badge = "<span style='background:#1f77b4; color:white; padding:4px 10px; border-radius:12px; font-size:12px; font-weight:bold; box-shadow:0 2px 4px rgba(31,119,180,0.4);'>⏱️ Sortie Rythmée</span>"
        else:
            diff_badge = "<span style='background:#2ca02c; color:white; padding:4px 10px; border-radius:12px; font-size:12px; font-weight:bold; box-shadow:0 2px 4px rgba(44,160,44,0.4);'>☕ Récupération / Balade</span>"

        suffer_badge_html = ""
        if not hide_hr:
            if suffer >= 200:
                suffer_badge_html = f"<div style='margin-bottom:20px;'><span style='background:#7f1d1d; color:white; padding:4px 10px; border-radius:12px; font-size:12px; font-weight:bold;'>❤️‍🔥 Charge Extrême · {suffer}</span></div>"
            elif suffer >= 120:
                suffer_badge_html = f"<div style='margin-bottom:20px;'><span style='background:#d62728; color:white; padding:4px 10px; border-radius:12px; font-size:12px; font-weight:bold;'>❤️‍🔥 Charge Élevée · {suffer}</span></div>"
            elif suffer >= 60:
                suffer_badge_html = f"<div style='margin-bottom:20px;'><span style='background:#ff7f0e; color:white; padding:4px 10px; border-radius:12px; font-size:12px; font-weight:bold;'>❤️ Charge Modérée · {suffer}</span></div>"
            elif suffer > 0:
                suffer_badge_html = f"<div style='margin-bottom:20px;'><span style='background:#2ca02c; color:white; padding:4px 10px; border-radius:12px; font-size:12px; font-weight:bold;'>❤️ Charge Légère · {suffer}</span></div>"

        photo_title_icon = " 🖼️" if has_photos else ""

        tile_speed = "" if hide_speed else f"""
                <div style="background:#fff; padding:8px; border-radius:8px; box-shadow:0 1px 3px rgba(0,0,0,0.05);">
                    <div style="font-size: 15px; color:#333; font-weight:bold;">⚡ {act.get('speed', 0)} km/h</div>
                    <span style="font-size:10px; color:#888; text-transform:uppercase; font-weight:bold;">Moyenne</span>
                </div>"""
        tile_maxspeed_hr = "" if hide_speed and hide_hr else f"""
                <div style="background:#fff; padding:8px; border-radius:8px; box-shadow:0 1px 3px rgba(0,0,0,0.05);">
                    <div style="font-size: 14px; color:#555; font-weight:bold;">🚀 {'—' if hide_speed else act.get('max_speed', 0)} km/h</div>
                    <span style="font-size:10px; color:#888; text-transform:uppercase; font-weight:bold;">Vitesse Max</span>
                </div>
                <div style="background:#fff; padding:8px; border-radius:8px; box-shadow:0 1px 3px rgba(0,0,0,0.05);">
                    <div style="font-size: 14px; color:#555; font-weight:bold;">❤️ {'—' if hide_hr else act.get('hr', 'N/A')} bpm</div>
                    <span style="font-size:10px; color:#888; text-transform:uppercase; font-weight:bold;">Cardiaque</span>
                </div>"""

        # ========================================================
        # 📄 PAGE FOCUS PLEIN ÉCRAN
        # ========================================================
        full_html = f"""
        <div style="padding: 25px; padding-top: 10px; font-family: 'Segoe UI', Tahoma, sans-serif;">
            <h2 style="color:{color}; margin:0 0 10px 0; font-size: 26px; font-weight: 900; line-height: 1.1; font-family:'Oswald','Segoe UI',sans-serif; text-transform:uppercase; letter-spacing:0.5px;">
                {act['name']}{photo_title_icon}
            </h2>
            <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom: 12px; border-bottom: 2px solid #eee; padding-bottom: 12px; flex-wrap:wrap; gap:8px;">
                <span style="font-size: 14px; color: #444; font-weight: bold;">📅 {act['date']}</span>
                {diff_badge}
            </div>
            {suffer_badge_html}
            
            <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 12px; background: #f8f9fa; padding: 15px; border-radius: 12px; border: 1px solid #e9ecef; margin-bottom: 15px; text-align:center;">
                <div style="background:#fff; padding:8px; border-radius:8px; box-shadow:0 1px 3px rgba(0,0,0,0.05);">
                    <div style="font-size: 18px; color:#1f77b4; font-weight:900; font-family:'Oswald','Segoe UI',sans-serif;">📏 {dist} km</div>
                    <span style="font-size:10px; color:#888; text-transform:uppercase; font-weight:bold;">Distance</span>
                </div>
                <div style="background:#fff; padding:8px; border-radius:8px; box-shadow:0 1px 3px rgba(0,0,0,0.05);">
                    <div style="font-size: 18px; color:#ff7f0e; font-weight:900; font-family:'Oswald','Segoe UI',sans-serif;">⛰️ {ele} m+</div>
                    <span style="font-size:10px; color:#888; text-transform:uppercase; font-weight:bold;">Dénivelé</span>
                </div>
                <div style="background:#fff; padding:8px; border-radius:8px; box-shadow:0 1px 3px rgba(0,0,0,0.05);">
                    <div style="font-size: 15px; color:#333; font-weight:bold;">⏱️ {format_duration(dur)}</div>
                    <span style="font-size:10px; color:#888; text-transform:uppercase; font-weight:bold;">Temps</span>
                </div>
                {tile_speed}
                <div style="background:#fff; padding:8px; border-radius:8px; box-shadow:0 1px 3px rgba(0,0,0,0.05);">
                    <div style="font-size: 15px; color:#d62728; font-weight:bold;">📈 {vam} m/h</div>
                    <span style="font-size:10px; color:#888; text-transform:uppercase; font-weight:bold;">VAM (Ascension)</span>
                </div>
                <div style="background:#fff; padding:8px; border-radius:8px; box-shadow:0 1px 3px rgba(0,0,0,0.05);">
                    <div style="font-size: 15px; color:#8c564b; font-weight:bold;">📐 ~{gradient}%</div>
                    <span style="font-size:10px; color:#888; text-transform:uppercase; font-weight:bold;">Pente estimée</span>
                </div>
                {tile_maxspeed_hr}
            </div>
            
            <div style="font-size: 14px; color: #333; margin-bottom: 10px; padding: 10px; background: #eef2f5; border-radius: 8px; border-left: 4px solid #9467bd;">
                🚲 <b>Équipement utilisé :</b> <span style="color:#1f77b4; font-weight:bold; float:right;">{gear_str}</span>
            </div>
            
            {generate_svg_elevation(elevations, color)}
        """
        
        if not hide_comments and act.get("comment"):
            full_html += f'<div style="background:#fff3cd; border-left:4px solid #ffc107; padding:12px; border-radius:8px; margin-top:15px; font-size:15px; font-style:italic; color:#664d03; box-shadow:0 2px 4px rgba(0,0,0,0.05);">"{act["comment"]}"</div>'
            
        if act.get("photos"):
            full_html += '<div style="display:grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr)); gap:10px; margin-top:15px;">'
            for p in act["photos"]:
                full_html += f'<img src="{p}" onclick="openLightbox(this.src)" style="width:100%; height:140px; object-fit:cover; border-radius:8px; box-shadow: 0 3px 6px rgba(0,0,0,0.15); transition:transform 0.2s; cursor:zoom-in;" onmouseover="this.style.transform=\'scale(1.03)\'" onmouseout="this.style.transform=\'scale(1)\'">'
            full_html += '</div>'

        full_html += f"""
            <div style="display:flex; gap:10px; margin-top:20px;">
                <button onclick="downloadGPX('{act['id']}')" 
                        style="flex:1; padding:15px; background:#222; color:white; border:none; border-radius:10px; cursor:pointer; font-weight:bold; font-size:14px; box-shadow: 0 4px 6px rgba(0,0,0,0.15);">
                    ⬇️ Télécharger le GPX
                </button>
                <button class="edit-only-btn" onclick="openEditModal('{act['id']}', '{escaped_comment}', '{escaped_name}')" 
                        style="flex:1; padding:15px; background:{color}; color:white; border:none; border-radius:10px; cursor:pointer; font-weight:bold; font-size:14px; box-shadow: 0 4px 6px rgba(0,0,0,0.15);">
                    📝 Éditer
                </button>
            </div>
        </div>
        """
        full_details_dict[act['id']] = full_html

        # ========================================================
        # 💬 MINI-POPUP RAPIDE (Sur la carte) AVEC PHOTO RONDE
        # ========================================================
        cover_photo_html = ""
        if act.get("photos") and len(act["photos"]) > 0:
            cover_photo_html = f'''
            <div style="display:flex; justify-content:center; margin-top:8px; margin-bottom:8px;">
                <img src="{act["photos"][0]}" style="width:75px; height:75px; object-fit:cover; border-radius:50%; border:3px solid {color}; box-shadow: 0 3px 6px rgba(0,0,0,0.15);">
            </div>
            '''

        mini_popup_html = f"""
        <div style="font-family: 'Segoe UI', sans-serif; text-align: center; min-width: 190px;">
            <div style="font-size: 15px; font-weight: 900; color: {color}; margin-bottom: 5px; border-bottom: 2px solid #ccc; padding-bottom: 4px; line-height:1.2;">
                {act['name']}{photo_title_icon}
            </div>
            {cover_photo_html}
            <div style="font-size: 14px; font-weight: bold; color: #333; margin-bottom: 12px;">
                📏 {dist} km &nbsp;|&nbsp; ⛰️ {ele} m+
            </div>
            <div style="display:flex; gap:6px;">
                <button onclick="focusOnActivity('{act['id']}')" style="flex:2; background:#2ca02c; color:white; border:none; border-radius:6px; padding:10px; cursor:pointer; font-weight:bold; box-shadow:0 2px 4px rgba(0,0,0,0.2);">
                    🔍 Développer
                </button>
                <button onclick="downloadGPX('{act['id']}')" title="Télécharger le GPX" style="flex:1; background:#333; color:white; border:none; border-radius:6px; padding:10px; cursor:pointer; font-weight:bold; box-shadow:0 2px 4px rgba(0,0,0,0.2);">
                    ⬇️
                </button>
            </div>
        </div>
        """

        # 1. TRACÉ MASQUÉ PAR DÉFAUT
        folium.PolyLine(
            coords, color=color, weight=5, className=f"activity-track track-{act['id']}"
        ).add_to(feature_groups[sport_key])
        
        # 2. 📍 MARQUEUR PIN ROUGE MAPS (Anti-flicker: SVG est animé, pas le wrapper)
        red_pin_html = f"""
        <div style="position:relative; width:24px; height:34px; cursor:pointer;">
            <svg class="pin-svg" viewBox="0 0 384 512" style="fill:#d62728; width:24px; height:34px; position:absolute; top:-34px; left:-12px; filter: drop-shadow(0 2px 3px rgba(0,0,0,0.5)); transition: transform 0.15s ease-out;">
                <path d="M172.268 501.67C26.97 291.031 0 269.413 0 192 0 85.961 85.961 0 192 0s192 85.961 192 192c0 77.413-26.97 99.031-172.268 309.67-9.535 13.774-29.93 13.773-39.464 0zM192 272c44.183 0 80-35.817 80-80s-35.817-80-80-80-80 35.817-80 80 35.817 80 80 80z"/>
            </svg>
        </div>
        """
        folium.Marker(
            location=coords[0],
            icon=folium.DivIcon(html=red_pin_html, class_name=f"leaflet-marker-icon leaflet-interactive global-marker-wrapper garmin-{act['id']}"),
            tooltip=folium.Tooltip(f"🏁 {act['name']}{photo_title_icon}", sticky=True),
            popup=folium.Popup(mini_popup_html, max_width=250)
        ).add_to(clusters[sport_key])

        # 3. 🟢 MARQUEUR DÉPART FOCUS
        start_html = f'<div style="width:20px;height:20px;background:#2ca02c;border:3px solid white;border-radius:50%;box-shadow:0 0 6px rgba(0,0,0,0.8);transform:translate(-50%,-50%);"></div>'
        folium.Marker(
            location=coords[0], 
            icon=folium.DivIcon(html=start_html, class_name=f"start-end-wrapper track-{act['id']}-points"),
            tooltip=folium.Tooltip("🟢 Départ", sticky=True)
        ).add_to(feature_groups[sport_key])

        # 4. 🛑 MARQUEUR ARRIVÉE FOCUS 
        end_html = f'<div style="width:20px;height:20px;background:#d62728;border:3px solid white;border-radius:4px;box-shadow:0 0 6px rgba(0,0,0,0.8);transform:translate(-50%,-50%);"></div>'
        folium.Marker(
            location=coords[-1], 
            icon=folium.DivIcon(html=end_html, class_name=f"start-end-wrapper track-{act['id']}-points"),
            tooltip=folium.Tooltip("🏁 Arrivée", sticky=True)
        ).add_to(feature_groups[sport_key])

        search_features.append({
            "type": "Feature", "geometry": {"type": "Point", "coordinates": [coords[0][1], coords[0][0]]},
            "properties": {"name": f"{act['name']} ({act['date']})"}
        })

    if all_heat_coords:
        heat_layer = folium.FeatureGroup(name="🔥 Heatmap Globale", show=False)
        plugins.HeatMap(all_heat_coords, radius=8, blur=12).add_to(heat_layer)
        heat_layer.add_to(m)

    search_layer = folium.GeoJson(
        {"type": "FeatureCollection", "features": search_features}, 
        name="Moteur de recherche", 
        show=False,
        style_function=lambda x: {'opacity': 0, 'fillOpacity': 0},
        marker=folium.CircleMarker(radius=0, opacity=0, fill_opacity=0, weight=0)
    ).add_to(m)
    
    plugins.Search(layer=search_layer, geom_type="Point", placeholder="🔍 Chercher...", collapsed=True, search_label="name").add_to(m)
    try: plugins.Geocoder(position="topleft", add_marker=True, placeholder="🌍 Lieu...").add_to(m)
    except: pass

    plugins.Fullscreen(position='topright').add_to(m)
    plugins.MeasureControl(position='bottomleft').add_to(m)
    plugins.LocateControl(position='topright', strings={"title": "Où suis-je ?"}).add_to(m)
    plugins.Draw(export=True, position='topleft', draw_options={'polyline': False, 'polygon': True, 'rectangle': True, 'circle': False, 'marker': False, 'circlemarker': False}).add_to(m)
    folium.LayerControl(position='topright', collapsed=False).add_to(m)

    activities_json = json.dumps(js_activities_data)
    full_details_json = json.dumps(full_details_dict)
    gpx_fallback_json = json.dumps(gpx_fallback_dict)
    
    gear_options_html = "".join([f'<option value="{g}">{g}</option>' for g in sorted(unique_gears)])
    sport_options_html = "".join([f'<option value="{cfg2["nom"]}">{cfg2["nom"]}</option>' for cfg2 in SPORTS_CONFIG.values()])

    hide_stats_js = "true" if hide_stats else "false"

    dashboard_block = "" if hide_stats else f"""
    <div id="stats-dashboard-inner">
        <div class="stat-header">
            <h4>📊 Palmarès Personnel</h4>
        </div>
        <div style="display:flex; gap:6px; margin-bottom:12px;">
            <select id="dash-year-select" onchange="refreshDashboard()" style="flex:1; padding:5px; border-radius:6px; border:1px solid #ccc; font-size:12px;"><option value="all">Toutes années</option></select>
            <select id="dash-sport-select" onchange="refreshDashboard()" style="flex:1; padding:5px; border-radius:6px; border:1px solid #ccc; font-size:12px;"><option value="all">Tous sports</option>{sport_options_html}</select>
        </div>
        <div class="stat-line"><span>🚲 Activités</span> <b id="dash-count">0</b></div>
        <div class="stat-line"><span>📏 Distance</span> <b id="dash-km">0 km</b></div>
        <div class="stat-line"><span>⛰️ Dénivelé</span> <b id="dash-dplus">0 m</b></div>
        <div class="stat-line"><span>⏱️ Temps</span> <b id="dash-time">0h</b></div>
        <div style="margin-top:15px; height:120px;"><canvas id="monthlyChart"></canvas></div>
        <div id="jerseys-grid" style="display:grid; grid-template-columns:1fr 1fr; gap:6px; margin-top:14px;"></div>
    </div>
    """

    # ========================================================
    # 🛠️ INJECTION HTML/JS (CSS, JS, et Nouveaux Filtres)
    # ========================================================
    custom_ui = f"""
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link href="https://fonts.googleapis.com/css2?family=Oswald:wght@500;700&display=swap" rel="stylesheet">
    <style>
      * {{ box-sizing: border-box; }}
      
      /* 🛑 FIX CLIGNOTEMENT 🛑 */
      .leaflet-tooltip {{ pointer-events: none !important; white-space: nowrap; transition: opacity 0.1s; margin-top: -15px !important; }}
      .global-marker-wrapper {{ z-index: 400 !important; }}
      .global-marker-wrapper:hover {{ z-index: 1000 !important; }}
      .global-marker-wrapper:hover .pin-svg {{ transform: scale(1.25) translateY(-4px); }}
      
      path.activity-track {{ stroke-opacity: 0 !important; pointer-events: none !important; transition: stroke-opacity 0.3s ease; stroke-width: 6px !important; }}
      path.activity-track.show-track, path.activity-track.show-track-forced {{ stroke-opacity: 0.9 !important; pointer-events: auto !important; filter: drop-shadow(0 0 5px rgba(0,0,0,0.5)); }}
      
      /* 🔴 RÈGLE D'OR MODE FOCUS : Masquage PUR CSS des clusters et pins globaux */
      body.focus-mode .marker-cluster, body.focus-mode .global-marker-wrapper {{ display: none !important; opacity: 0 !important; pointer-events: none !important; }}
      .start-end-wrapper {{ display: none !important; opacity: 0 !important; pointer-events: none !important; }}
      body.focus-mode .start-end-wrapper.active-focus {{ display: block !important; opacity: 1 !important; z-index: 9999 !important; }}

      /* Design du Dashboard (déplacé dans l'explorateur) */
      #stats-dashboard-inner {{ background: #fff; padding: 15px; border-radius: 12px; box-shadow: 0 2px 8px rgba(0,0,0,0.05); margin-bottom: 20px; border-left: 6px solid #1f77b4; }}
      .stat-header {{ display:flex; justify-content:space-between; align-items:center; border-bottom: 2px solid #1f77b4; padding-bottom: 5px; margin-bottom:10px; }}
      .stat-header h4 {{ margin: 0; font-size: 16px; color: #222; text-transform: uppercase; font-family:'Oswald','Segoe UI',sans-serif; letter-spacing:0.5px; }}
      .stat-line {{ font-size: 14px; color: #444; margin-bottom: 8px; display: flex; justify-content: space-between; }}
      .stat-line b {{ color: #1f77b4; font-size: 15px; font-family:'Oswald','Segoe UI',sans-serif; }}

      .jersey-card {{ background:#fff; border-radius:10px; padding:8px; cursor:pointer; box-shadow:0 1px 4px rgba(0,0,0,0.08); border:2px solid transparent; transition:0.2s; }}
      .jersey-card:hover {{ transform:translateY(-2px); box-shadow:0 4px 10px rgba(0,0,0,0.15); }}
      .jersey-card .jersey-title {{ font-size:10px; font-weight:bold; text-transform:uppercase; letter-spacing:0.5px; display:flex; align-items:center; gap:4px; margin-bottom:3px; }}
      .jersey-card .jersey-name {{ font-size:11px; color:#333; font-weight:bold; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }}
      .jersey-card .jersey-stat {{ font-size:12px; color:#666; }}
      .jersey-yellow {{ border-color:#f4c400; }}
      .jersey-polka {{ border-color:#d62728; }}
      .jersey-green {{ border-color:#2ca02c; }}
      .jersey-white {{ border-color:#bbb; }}
      
      /* Boutons Centraux (Uniques sur la map) */
      .action-btns-container {{ position: fixed; bottom: 25px; left: 50%; transform: translateX(-50%); z-index: 999; display: flex; gap: 10px; transition: transform 0.4s; }}
      .action-btn {{ background: #1f77b4; color: white; padding: 12px 25px; border-radius: 30px; cursor: pointer; font-family: 'Segoe UI', sans-serif; font-size: 14px; font-weight: bold; box-shadow: 0 8px 20px rgba(31, 119, 180, 0.4); border: 2px solid white; transition: all 0.3s ease; white-space: nowrap; }}
      .action-btn:hover {{ transform: scale(1.05); }}
      .btn-filter-toggle {{ background: #2ca02c; box-shadow: 0 8px 20px rgba(44,160,44, 0.4); }}
      
      /* Focus Plein Écran */
      #activity-focus-panel {{ position: fixed; top: 0; left: 0; width: 420px; height: 100vh; background: #ffffff; z-index: 10000; overflow-y: auto; overflow-x: hidden; box-shadow: 5px 0 30px rgba(0,0,0,0.3); transition: transform 0.4s cubic-bezier(0.25, 0.8, 0.25, 1); transform: translateX(-105%); }}
      #activity-focus-panel.active {{ transform: translateX(0); }}
      .btn-close-focus {{ background: #222; color: white; padding: 18px; text-align: center; font-weight: bold; cursor: pointer; position: sticky; top: 0; z-index: 10; font-size: 14px; letter-spacing: 1px; display: flex; align-items: center; justify-content: center; gap: 10px; transition: 0.2s; }}
      .btn-close-focus:hover {{ background: #000; }}
      .btn-close-focus svg {{ width: 20px; fill: white; }}

      #shutdown-btn {{ position: fixed; top: 15px; left: 50%; transform: translateX(-50%); z-index: 999; background: #dc3545; color: white; padding: 10px 20px; border-radius: 12px; cursor: pointer; font-weight: bold; border: 2px solid white; transition: transform 0.4s;}}
      
      /* 🌟 L'EXPLORATEUR CENTRAL MODAL */
      .modal-overlay {{ display: none; position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0,0,0,0.6); z-index: 10001; justify-content: center; align-items: center; backdrop-filter: blur(5px); font-family: 'Segoe UI', sans-serif; }}
      .modal-content {{ background: white; padding: 30px; border-radius: 16px; width: 90%; max-width: 450px; position: relative; box-shadow: 0 20px 40px rgba(0,0,0,0.3); }}
      .close-modal {{ position:absolute; right:20px; top:20px; cursor:pointer; font-size:28px; font-weight:bold; color:#888; line-height:0.8; transition:0.2s; }}
      .close-modal:hover {{ color: #d62728; }}

      .explorer-modal-content {{ max-width: 900px; padding: 0; overflow: hidden; display: flex; flex-direction: column; background: #fff; border-radius: 16px; width: 95%; max-height: 85vh; box-shadow: 0 20px 50px rgba(0,0,0,0.4); }}
      .explorer-header {{ background: #1f77b4; color: white; padding: 18px 25px; display: flex; justify-content: space-between; align-items: center; }}
      .explorer-header h3 {{ margin: 0; font-size: 20px; font-family:'Oswald', sans-serif; letter-spacing:0.5px; }}
      .explorer-body {{ display: flex; flex-wrap: wrap; height: 65vh; max-height: 600px; }}
      .explorer-left {{ flex: 1; min-width: 320px; padding: 25px; background: #f8f9fa; border-right: 1px solid #ddd; overflow-y: auto; }}
      .explorer-right {{ flex: 1.5; min-width: 300px; padding: 25px; overflow-y: auto; background: #fff; display: flex; flex-direction: column; }}
      
      .filter-row {{ margin-bottom: 12px; font-size: 13px; font-weight: bold; color: #444; }}
      .filter-row input, .filter-row select {{ width: 100%; padding: 8px; border-radius: 6px; border: 1px solid #ccc; margin-top: 5px; box-sizing: border-box; font-family: inherit; }}
      .filter-row .flex-row {{ display: flex; gap: 10px; align-items: center; }}
      
      .zone-item {{ background: #fff; border: 1px solid #e9ecef; padding: 12px; border-radius: 8px; margin-bottom: 10px; cursor: pointer; transition: 0.2s; box-shadow: 0 2px 4px rgba(0,0,0,0.02); }}
      .zone-item:hover {{ border-color: #1f77b4; transform: translateY(-2px); background: #f0f7ff; box-shadow: 0 4px 8px rgba(0,0,0,0.1); }}
      
      /* 🔥 LIGHTBOX (Zoom Photo) */
      .lightbox-overlay {{ display: none; position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0,0,0,0.9); z-index: 20000; justify-content: center; align-items: center; cursor: zoom-out; backdrop-filter: blur(10px); }}
      .lightbox-img {{ max-width: 90%; max-height: 90vh; border-radius: 12px; box-shadow: 0 10px 40px rgba(0,0,0,0.6); object-fit: contain; }}

      @media (max-width: 768px) {{
          .action-btns-container {{ bottom: 15px; flex-direction: column; align-items: center; gap: 5px; }}
          #activity-focus-panel {{ width: 100%; height: 55vh; top: auto; bottom: 0; transform: translateY(105%); border-radius: 25px 25px 0 0; border-top: 3px solid #ccc; }}
          #activity-focus-panel.active {{ transform: translateY(0); }}
          .btn-close-focus {{ border-radius: 25px 25px 0 0; }}
          .explorer-body {{ flex-direction: column; height: 75vh; }}
          .explorer-left {{ border-right: none; border-bottom: 2px solid #ddd; flex: none; height: 50%; }}
          .explorer-right {{ flex: 1; height: 50%; padding: 15px; }}
      }}
    </style>

    <div id="shutdown-btn" class="edit-only-btn" onclick="shutdownServer()">🛑 Éteindre le serveur</div>

    <!-- Lightbox pour Photos Plein Écran -->
    <div id="lightbox-overlay" class="lightbox-overlay" onclick="closeLightbox()">
        <img id="lightbox-img" class="lightbox-img" src="">
    </div>

    <!-- Boutons Fixes (Carte épurée) -->
    <div class="action-btns-container" id="main-action-btns">
        <div class="action-btn btn-filter-toggle" onclick="document.getElementById('explorer-modal').style.display='flex'">🧭 Palmarès & Explorateur</div>
        <div class="action-btn" id="toggle-tracks-btn" onclick="toggleAllTracks()">👁️ Afficher la toile d'araignée</div>
    </div>

    <!-- 🌟 L'EXPLORATEUR CENTRAL MODAL (Remplace l'ancien Dashboard sur la carte) -->
    <div id="explorer-modal" class="modal-overlay">
        <div class="explorer-modal-content">
            <div class="explorer-header">
                <h3>🧭 Centre de Contrôle Atlas</h3>
                <span class="close-modal" style="color:white; position:static;" onclick="document.getElementById('explorer-modal').style.display='none'">&times;</span>
            </div>
            <div class="explorer-body">
                <!-- Gauche : Palmarès & Filtres Temps Réel -->
                <div class="explorer-left">
                    {dashboard_block}
                    
                    <h4 style="margin: 0 0 10px 0; font-size: 16px; border-bottom: 2px solid #2ca02c; padding-bottom: 5px; font-family:'Oswald',sans-serif; text-transform:uppercase;">🔎 Filtrer les sorties</h4>
                    <div class="filter-row">Recherche textuelle : <input type="text" id="fil-text" placeholder="Nom de la sortie..." onkeyup="applyAdvancedFilters()"></div>
                    <div class="filter-row">Sport : <select id="fil-sport" onchange="applyAdvancedFilters()"><option value="">Tous les sports</option>{sport_options_html}</select></div>
                    <div class="filter-row">Période exacte : <div class="flex-row"><input type="date" id="fil-date-min" onchange="applyAdvancedFilters()"> au <input type="date" id="fil-date-max" onchange="applyAdvancedFilters()"></div></div>
                    <div class="filter-row">Distance (km) : <div class="flex-row"><input type="number" id="fil-dist-min" onkeyup="applyAdvancedFilters()" placeholder="Min"> à <input type="number" id="fil-dist-max" onkeyup="applyAdvancedFilters()" placeholder="Max"></div></div>
                    <div class="filter-row">Dénivelé (m) : <div class="flex-row"><input type="number" id="fil-ele-min" onkeyup="applyAdvancedFilters()" placeholder="Min"> à <input type="number" id="fil-ele-max" onkeyup="applyAdvancedFilters()" placeholder="Max"></div></div>
                    <div class="filter-row">Équipement Garmin : <select id="fil-gear" onchange="applyAdvancedFilters()"><option value="">Tous les équipements</option>{gear_options_html}</select></div>
                    <button onclick="resetFilters()" style="width:100%; margin-top:15px; padding:10px; background:#fff; border:2px solid #ccc; border-radius:8px; cursor:pointer; font-weight:bold; color:#444;">🔄 Réinitialiser les filtres</button>
                </div>
                <!-- Droite : Liste Interactive -->
                <div class="explorer-right">
                    <h4 style="margin: 0 0 15px 0; font-size: 16px; border-bottom: 2px solid #1f77b4; padding-bottom: 8px; display:flex; justify-content:space-between; color:#333; font-family:'Oswald',sans-serif; text-transform:uppercase;">
                        <span>📋 Résultats de la recherche</span>
                        <span id="filter-result-count" style="background:#e8f5e9; color:#2ca02c; padding:2px 10px; border-radius:12px; font-size:13px; font-weight:bold;">0</span>
                    </h4>
                    <div id="filter-results-list" style="flex-grow: 1; padding-right: 5px;"></div>
                </div>
            </div>
        </div>
    </div>

    <!-- Modale Résultats de Zone (Lasso) -->
    <div id="zone-results-modal" class="modal-overlay">
        <div class="modal-content" style="max-width: 500px; padding: 0; overflow: hidden; display: flex; flex-direction: column;">
            <div style="background: #ff7f0e; color: white; padding: 18px 25px; display: flex; justify-content: space-between; align-items: center;">
                <h3 style="margin: 0; font-size: 18px;">📍 <span id="zone-count">0</span> Activité(s) ciblée(s)</h3>
                <span class="close-modal" style="color:white; position:static;" onclick="document.getElementById('zone-results-modal').style.display='none'">&times;</span>
            </div>
            <div id="zone-results-list" style="padding: 20px; max-height: 60vh; overflow-y: auto;"></div>
        </div>
    </div>

    <!-- 🔥 PANNEAU FOCUS PLEIN ÉCRAN 🔥 -->
    <div id="activity-focus-panel">
        <div class="btn-close-focus" onclick="closeFocusPanel()">
            <svg viewBox="0 0 448 512"><path d="M9.4 233.4c-12.5 12.5-12.5 32.8 0 45.3l160 160c12.5 12.5 32.8 12.5 45.3 0s12.5-32.8 0-45.3L109.2 288 416 288c17.7 0 32-14.3 32-32s-14.3-32-32-32l-306.7 0L214.6 118.6c12.5-12.5 12.5-32.8 0-45.3s-32.8-12.5-45.3 0l-160 160z"/></svg>
            Fermer la vue & Retour à la carte globale
        </div>
        <div id="activity-focus-content"></div>
    </div>

    <!-- Modale d'Édition Complète -->
    <div id="edit-modal-overlay" class="modal-overlay">
        <div class="modal-content">
            <span class="close-modal" onclick="closeEditModal()">&times;</span>
            <h3 style="border-bottom: 2px solid #ccc; font-family:'Oswald',sans-serif;">📝 Éditer l'activité</h3>
            <input type="hidden" id="edit-act-id">
            
            <label style="font-size:13px; font-weight:bold; color:#555; display:block; margin-bottom:5px;">Titre de la sortie :</label>
            <input type="text" id="edit-name" style="width:100%; padding:10px; border-radius:8px; border:1px solid #ccc; margin-bottom:15px; font-family:inherit; font-size:14px; box-sizing:border-box;">
            
            <label style="font-size:13px; font-weight:bold; color:#555; display:block; margin-bottom:5px;">Commentaire / Météo :</label>
            <textarea id="edit-comment" style="width:100%; height:100px; padding:10px; margin-bottom:15px; border-radius:8px; border:1px solid #ccc; font-family:inherit; resize:none; box-sizing:border-box;"></textarea>
            
            <label style="font-size:13px; font-weight:bold; color:#555; display:block; margin-bottom:5px;">📸 Ajouter des Photos (Sélection multiple) :</label>
            <input type="file" id="edit-photo" accept="image/png, image/jpeg, image/jpg" multiple style="width:100%; margin-bottom:20px; padding:8px; border:1px dashed #aaa; background:#f9f9f9; border-radius:8px; box-sizing:border-box;">
            
            <button class="btn-apply" onclick="saveActivityData()" style="background:#2ca02c; color:white; padding:12px; width:100%; border:none; border-radius:8px; font-weight:bold; font-size:16px; cursor:pointer;">💾 Sauvegarder & Actualiser</button>
            <div id="save-loader" style="display:none; text-align:center; color:#2ca02c; font-size:14px; margin-top:15px; font-weight:bold;">Traitement en cours... ⏳</div>
        </div>
    </div>

    <script>
    const allActivities = {activities_json};
    const fullDetailsDict = {full_details_json};
    const gpxFallbackDict = {gpx_fallback_json};
    const HIDE_STATS = {hide_stats_js};

    let chartInstance = null;
    let allVisible = false;
    let myLeafletMap = null;

    const isEditableEnv = (location.hostname === 'localhost' || location.hostname === '127.0.0.1');
    if (!isEditableEnv) {{
        document.querySelectorAll('.edit-only-btn').forEach(el => el.style.display = 'none');
    }}

    function openLightbox(src) {{
        document.getElementById('lightbox-img').src = src;
        document.getElementById('lightbox-overlay').style.display = 'flex';
    }}
    function closeLightbox() {{
        document.getElementById('lightbox-overlay').style.display = 'none';
        document.getElementById('lightbox-img').src = "";
    }}

    function formatTimeJS(seconds) {{
        let h = Math.floor(seconds / 3600); let m = Math.floor((seconds % 3600) / 60);
        return h > 0 ? h + "h " + m.toString().padStart(2, '0') + "m" : m + " min";
    }}

    function sanitizeFilename(name) {{
        return (name || 'sortie').replace(/[^a-zA-Z0-9 _.-]/g, '_').trim() || 'sortie';
    }}

    function downloadGPX(id) {{
        const act = allActivities.find(a => a.id === id);
        if (!act) return;
        if (act.gpxFile) {{
            const a = document.createElement('a');
            a.href = act.gpxFile;
            a.download = sanitizeFilename(act.name) + '.gpx';
            document.body.appendChild(a);
            a.click();
            a.remove();
            return;
        }}
        const fb = gpxFallbackDict[id];
        if (!fb || !fb.coords || fb.coords.length < 2) {{
            alert("GPX indisponible pour cette sortie.");
            return;
        }}
        let points = fb.coords.map((c, i) => {{
            let ele = (fb.elevations && fb.elevations[i] !== undefined) ? fb.elevations[i] : 0;
            return '<trkpt lat="' + c[0] + '" lon="' + c[1] + '"><ele>' + ele + '</ele></trkpt>';
        }}).join('\\n      ');
        let gpxContent = '<?xml version="1.0" encoding="UTF-8"?>\\n' +
            '<gpx version="1.1" creator="Atlas Cycling" xmlns="http://www.topografix.com/GPX/1/1">\\n' +
            '  <trk>\\n    <name>' + (act.name || 'Sortie') + '</name>\\n    <trkseg>\\n      ' +
            points + '\\n    </trkseg>\\n  </trk>\\n</gpx>';
        let blob = new Blob([gpxContent], {{type: 'application/gpx+xml'}});
        let url = URL.createObjectURL(blob);
        let a = document.createElement('a');
        a.href = url;
        a.download = sanitizeFilename(act.name) + '.gpx';
        document.body.appendChild(a);
        a.click();
        a.remove();
        URL.revokeObjectURL(url);
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

        const ctx = document.getElementById('monthlyChart').getContext('2d');
        if (chartInstance) chartInstance.destroy();
        chartInstance = new Chart(ctx, {{
            type: 'bar',
            data: {{ labels: ['J', 'F', 'M', 'A', 'M', 'J', 'J', 'A', 'S', 'O', 'N', 'D'], datasets: [{{ data: months, backgroundColor: '#1f77b4', borderRadius: 4 }}] }},
            options: {{ responsive: true, maintainAspectRatio: false, plugins: {{ legend: {{ display: false }} }}, scales: {{ x: {{ grid: {{ display: false }} }} }} }}
        }});
    }}

    window.allLeafletMarkers = [];
    function extractLeafletMarkers(layer) {{
        if (layer instanceof L.MarkerClusterGroup) {{
            layer.eachLayer(function(marker) {{
                if (marker.options && marker.options.icon && marker.options.icon.options && marker.options.icon.options.className && marker.options.icon.options.className.includes('global-marker-wrapper')) {{
                     let match = marker.options.icon.options.className.match(/garmin-([^\\s]+)/);
                     if (match) window.allLeafletMarkers.push({{ id: match[1], marker: marker, cluster: layer }});
                }}
            }});
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
            window.allLeafletMarkers.forEach(item => {{
                let act = allActivities.find(a => a.id === item.id);
                if (act) {{
                    if (act._match) {{
                        if (!item.cluster.hasLayer(item.marker)) item.cluster.addLayer(item.marker);
                    }} else {{
                        if (item.cluster.hasLayer(item.marker)) item.cluster.removeLayer(item.marker);
                    }}
                }}
            }});
        }}
    }}

    function resetFilters() {{
        document.getElementById('fil-text').value = '';
        document.getElementById('fil-sport').value = '';
        document.getElementById('fil-date-min').value = '';
        document.getElementById('fil-date-max').value = '';
        document.getElementById('fil-dist-min').value = ''; 
        document.getElementById('fil-dist-max').value = '';
        document.getElementById('fil-ele-min').value = ''; 
        document.getElementById('fil-ele-max').value = '';
        document.getElementById('fil-gear').value = ''; 
        applyAdvancedFilters();
    }}

    function focusOnActivity(id) {{
        let act = allActivities.find(a => a.id === id);
        if(!act) return;

        document.body.classList.add('focus-mode');
        document.querySelectorAll('.leaflet-popup-close-button').forEach(b => b.click());
        
        document.getElementById('explorer-modal').style.display = 'none';
        document.getElementById('zone-results-modal').style.display = 'none';
        document.getElementById('main-action-btns').style.transform = 'translateY(150px) translateX(-50%)';
        document.getElementById('shutdown-btn').style.transform = 'translateY(-150px) translateX(-50%)';
        
        document.getElementById('activity-focus-content').innerHTML = fullDetailsDict[id];
        document.getElementById('activity-focus-panel').classList.add('active');
        
        document.querySelectorAll('.activity-track').forEach(el => el.classList.remove('show-track', 'show-track-forced'));
        document.querySelectorAll('.track-' + id).forEach(el => el.classList.add('show-track-forced'));
        
        document.querySelectorAll('.start-end-wrapper').forEach(el => el.classList.remove('active-focus'));
        document.querySelectorAll('.track-' + id + '-points').forEach(el => el.classList.add('active-focus'));
        
        if (myLeafletMap && act.bounds) {{
            let isDesktop = window.innerWidth > 768;
            myLeafletMap.fitBounds(act.bounds, {{
                paddingTopLeft: [isDesktop ? 430 : 20, 20],
                paddingBottomRight: [20, isDesktop ? 20 : window.innerHeight * 0.55],
                animate: true,
                duration: 1.5
            }});
        }}
    }}

    function closeFocusPanel() {{
        document.body.classList.remove('focus-mode');
        document.querySelectorAll('.start-end-wrapper').forEach(el => el.classList.remove('active-focus'));
        
        document.getElementById('activity-focus-panel').classList.remove('active');
        
        document.getElementById('main-action-btns').style.transform = 'translateY(0) translateX(-50%)';
        document.getElementById('shutdown-btn').style.transform = 'translateY(0) translateX(-50%)';
        
        if (!allVisible) {{
            document.querySelectorAll('.activity-track').forEach(el => el.classList.remove('show-track', 'show-track-forced'));
        }} else {{
            document.querySelectorAll('.activity-track').forEach(el => el.classList.add('show-track-forced'));
        }}
    }}

    function anyModalOpen() {{
        return ['explorer-modal', 'zone-results-modal', 'edit-modal-overlay'].some(id => {{
            let el = document.getElementById(id);
            return el && el.style.display === 'flex';
        }});
    }}

    document.addEventListener('keydown', function(e) {{
        if (e.key !== 'Escape') return;
        if (document.getElementById('lightbox-overlay').style.display === 'flex') {{ closeLightbox(); return; }}
        if (anyModalOpen()) {{
            ['explorer-modal', 'zone-results-modal', 'edit-modal-overlay'].forEach(id => {{
                let el = document.getElementById(id);
                if (el) el.style.display = 'none';
            }});
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

        setTimeout(() => {{
            const addTitle = (selector, title) => {{ document.querySelectorAll(selector).forEach(el => el.title = title); }};
            addTitle('.leaflet-draw-draw-polygon', 'Dessiner un polygone pour cibler une zone');
            addTitle('.leaflet-draw-draw-rectangle', 'Dessiner un rectangle pour cibler une zone');
            addTitle('.leaflet-control-fullscreen-button', 'Passer en plein écran');
            addTitle('.leaflet-control-locate a', 'Me géolocaliser');
            addTitle('.leaflet-control-layers-toggle', 'Changer le fond de carte');
            addTitle('.leaflet-control-measure', 'Mesurer une distance');
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
                break;
            }}
        }}
    }});

    function showZoneResults(activities) {{
        const panel = document.getElementById('zone-results-modal');
        const list = document.getElementById('zone-results-list');
        panel.style.display = 'flex';
        if(activities.length === 0) {{
            list.innerHTML = '<div style="text-align:center; padding:20px; color:#888;">Aucune activité trouvée dans cette zone.</div>';
            document.getElementById('zone-count').innerText = "0"; return;
        }}
        document.getElementById('zone-count').innerText = activities.length;
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

    function toggleAllTracks() {{
        allVisible = !allVisible;
        document.getElementById('toggle-tracks-btn').innerHTML = allVisible ? "👁️ Masquer les tracés" : "👁️ Afficher la toile d'araignée";
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
        document.getElementById('edit-modal-overlay').style.display = 'flex';
    }}
    function closeEditModal() {{ document.getElementById('edit-modal-overlay').style.display = 'none'; }}

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
        if self.path == '/' or self.path == '/index.html':
            self.send_response(200)
            self.send_header('Content-type', 'text/html; charset=utf-8')
            self.end_headers()
            with open(MAP_HTML_PATH, 'rb') as f:
                self.wfile.write(f.read())
        else:
            try:
                file_path = os.path.join(DOSSIER_BASE, urllib.parse.unquote(self.path.lstrip('/')))
                if os.path.exists(file_path) and os.path.isfile(file_path):
                    mime_type, _ = mimetypes.guess_type(file_path)
                    self.send_response(200)
                    self.send_header('Content-type', mime_type or 'application/octet-stream')
                    self.end_headers()
                    with open(file_path, 'rb') as f:
                        self.wfile.write(f.read())
                else:
                    self.send_response(404)
                    self.end_headers()
            except:
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
                generate_map()
                
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({'status': 'ok'}).encode('utf-8'))
            else:
                self.send_response(400)
                self.end_headers()

class ThreadingSimpleServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    allow_reuse_address = True

def start_server():
    generate_map()
    
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
    
    print(f"\n✅ Serveur Cartographique lancé !")
    print(f"💻 Sur ce PC, la carte s'ouvre via : http://localhost:{port}")
    print(f"📱 Lien global GitHub Pages : https://gogniatnorman-doc.github.io/Atlas/ma_carte.html")
    print("👉 Tu pourras éteindre le système local directement depuis la carte web (Bouton Rouge).")
    
    threading.Timer(1, lambda: webbrowser.open(f'http://localhost:{port}')).start()
    
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
        print(" 3. 📤 Générer la version PUBLIQUE (sans mes stats, tracés tronqués)")
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
                out = generate_map(public_mode=True)
                print(f"\n✅ Version publique générée : {out}")
                print("\n" + "═"*55)
                print(" 🚀 COMMENT METTRE EN LIGNE TON LIEN PUBLIC ?")
                print("═"*55)
                print(" ÉTAPE 1 (La première fois seulement) - Le Bouclier de Sécurité :")
                print(" Tape ces commandes dans le terminal pour cacher tes données privées :")
                print("   echo \"atlas_db.json\" > .gitignore")
                print("   echo \"ma_carte.html\" >> .gitignore")
                print("   echo \"*.env\" >> .gitignore")
                print("   git rm --cached atlas_db.json ma_carte.html")
                print("\n ÉTAPE 2 - Mettre en ligne la carte publique :")
                print(" 1. Renomme le fichier 'ma_carte_publique.html' en 'index.html'.")
                print(" 2. Tape ces 3 commandes dans le terminal :")
                print("   git add .")
                print("   git commit -m \"Mise a jour de l'Atlas public\"")
                print("   git push")
                print("\n 💡 LEXIQUE VS CODE (Lettres à côté des fichiers) :")
                print("   [U] Untracked : Nouveau fichier que Git découvre (ex: .gitignore).")
                print("   [M] Modified  : Fichier existant que tu as modifié.")
                print("   [D] Deleted   : Fichier retiré du cloud (ex: tes données privées).")
                print("   [A] Added     : Fichier prêt à décoller après un 'git add .' !")
                print("═"*55)
                print(" 👉 Ton site sera en ligne d'ici 2 à 3 minutes sur GitHub Pages !")
            elif choix == "4":
                print("👋 Bonne balade sur tes futurs parcours ! À bientôt.")
                break
            else:
                print("❌ Choix invalide.")
        except KeyboardInterrupt:
            sys.exit(0)

if __name__ == "__main__":
    main_menu()
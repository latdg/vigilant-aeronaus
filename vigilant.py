#!/usr/bin/env python3
# =============================================================================
# VIGILANT D'AERONAUS — La TdG · portat d'Apps Script a GitHub el 21.10.2026
#
# És el mateix vigilant que AvisadorAeronausLaTdG.gs (projecte Correu), però
# corre aquí, just després de la vigilància contínua (opensky.yml), cada 5
# minuts i sense gastar quota de Google:
#   · llegeix del Gist el que la vigilància ha acumulat (adsb.lol, adsb.fi i
#     OpenSky, 35 minuts, fins a 40 km);
#   · classifica cada aeronau (aeronaus conegudes, plane-alert-db i regles);
#   · avisa el bot privat latdg_infos (aeronaus no comercials a la zona,
#     esdeveniments, sobrevols previstos, passos entre revisions i aeronaus que
#     desapareixen volant baix), amb els mateixos textos que l'Apps Script;
#   · desa el registre del dia a la branca «dades» d'aquest repo (una fila per
#     pas de cada aeronau), que llegeixen el tauler i la pàgina del registre.
#
# PRIVACITAT: el repo és públic. Al registre públic, la matrícula, l'indicatiu i
# el codi icao24 només hi surten per als vols comercials i els serveis públics
# (sanitari, extinció, seguretat, salvament, militar i d'estat). Els avisos de
# Telegram porten totes les dades. La memòria entre execucions es desa al Gist
# (secret), no al repo.
#
# Variables d'entorn: GIST_ID, GIST_TOKEN, TELEGRAM_BOT_TOKEN_INFOS,
# TELEGRAM_CHAT_ID_INFOS, ENVIAR_AVISOS ("1" per enviar; altrament, prova).
# Ús: python3 vigilant.py <carpeta de la branca dades>
# =============================================================================

import csv
import datetime as dt
import hashlib
import io
import json
import math
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from zoneinfo import ZoneInfo

TZ = ZoneInfo("Europe/Madrid")
UA = "LaTdG-vigilant-aeronaus/1.0 (latdg@laguait.cat)"

# -----------------------------------------------------------------------------
# CONFIGURACIÓ (la mateixa de l'Apps Script)
# -----------------------------------------------------------------------------
CENTRE = (41.962, 3.040)
RADI_KM = 8                     # zona d'avisos
RADI_REGISTRE_KM = 40           # registre
RADI_SOBREVOL_KM = 3
HORITZO_SOBREVOL_MIN = 20
VELOCITAT_MIN_SOBREVOL_KMH = 60
ALTITUD_BAIXA_M = 400
MINUTS_ENTRE_AVISOS = 60
INTERVAL_MINUTS = 5             # cada quan corre (amb la vigilància contínua)
GITHUB_ACTUAL_MIN = 4           # posició «actual»: de fa menys de 4 minuts
GIST_MAX_MINUTS = 10            # dades del Gist més velles: no es fan servir
HORES_FONT_CAIGUDA = 2          # avís si una font falla durant 2 hores seguides
AVISAR_COMERCIALS = False
MINUTS_NOU_PAS = 60             # sense veure-la 60 min, és un pas nou
DIES_REGISTRE = 60              # dies que es guarden a la branca dades

FITXER_GIST = "opensky.json"
FITXER_ESTAT = "vigilant-estat.json"

NUCLIS = [
    ("la Bisbal d'Empordà", "la Bisbal d'Empordà", 41.9597, 3.0386),
    ("Corçà", "Corçà", 41.9886, 3.0115),
    ("Casavells", "Corçà", 41.9980, 3.0420),
    ("Monells", "Cruïlles, Monells i Sant Sadurní de l'Heura", 41.9745, 2.9975),
    ("Cruïlles", "Cruïlles, Monells i Sant Sadurní de l'Heura", 41.9560, 3.0060),
    ("Sant Sadurní de l'Heura", "Cruïlles, Monells i Sant Sadurní de l'Heura", 41.9280, 3.0000),
    ("Vulpellac", "Forallac", 41.9530, 3.0570),
    ("Canapost", "Forallac", 41.9690, 3.0760),
    ("Peratallada", "Forallac", 41.9765, 3.0900),
    ("Fonteta", "Forallac", 41.9440, 3.0690),
    ("Ullastret", "Ullastret", 42.0004, 3.0675),   # 31.10.2026 (a uns 5 km del centre, dins la zona d'avisos)
]

# AERONAUS CONEGUDES (tenen prioritat sobre plane-alert-db). Per afegir-ne una,
# n'hi ha prou amb una línia: matrícula o codi icao24.
CONEGUDES = {
    "399503": {"categoria": "sanitari", "nota": "Helicòpter del SEM (F-HFID, EC135)", "color": "vermell"},
    "F-HFID": {"categoria": "sanitari", "nota": "Helicòpter del SEM (F-HFID, EC135)", "color": "vermell"},
}

CATEGORIES = {
    "sanitari": ("🚑", "AERONAU SANITÀRIA"),
    "extincio": ("🚒", "MITJÀ AERI D'EXTINCIÓ"),
    "seguretat": ("🚓", "POLICIA, TRÀNSIT O SEGURETAT"),
    "salvament": ("🛟", "SALVAMENT MARÍTIM"),
    "militar": ("🎖️", "AERONAU MILITAR"),
    "estat": ("🏛️", "AERONAU MILITAR O D'ESTAT"),
    "dron": ("🛸", "DRON"),
    "jet": ("💼", "JET PRIVAT O AEROTAXI"),
    "treballs": ("📷", "TREBALLS AERIS"),
    "helicopter": ("🚁", "HELICÒPTER (SERVEI SENSE IDENTIFICAR)"),
    "vol_lliure": ("🪂", "PLANADOR, ULTRALLEUGER O GLOBUS"),
    "general": ("🛩️", "AVIONETA (AVIACIÓ GENERAL)"),
    "desconegut": ("❓", "AERONAU SENSE IDENTIFICAR"),
    "comercial": ("✈️", "VOL COMERCIAL"),
}
# Categories que al registre públic porten matrícula, indicatiu i icao24.
CATEGORIES_PUBLIQUES = {"sanitari", "extincio", "seguretat", "salvament", "militar", "estat", "comercial"}

SQUAWKS = {
    "7500": "interferència il·lícita (possible segrest)",
    "7600": "fallada de comunicacions",
    "7700": "emergència general",
}

RX_SANITARI = re.compile(r"\bSEM\b|SISTEMA D.EMERG|MEDIC|AMBUL|HEMS|SANIT|HELIMED|MEDEVAC")
RX_EXTINCIO = re.compile(r"BOMBER|INCEND|FIRE|EXTINC|FORESTAL|FAASA")
RX_SEGURETAT = re.compile(r"POLIC|MOSSOS|GUARDIA CIVIL|ADUAN|\bDGT\b|TRAFICO|PEGASO|INTERIOR")
RX_SALVAMENT = re.compile(r"SALVAMENT|SASEMAR|HELIMER|\bSAR\b")
RX_TREBALLS = re.compile(r"CARTOGR|ICGC|FOTOGRAM|TOPOGRA|AGRIC|FUMIG|AERIAL WORK|SURVEY|INSPEC|PHOTO")
RX_IND_MILITAR = re.compile(r"^(AME|CTM|FAF|FNY|GAF|BAF|IAM|RRR|RCH|NATO|NAVY|ARMY|HKY|SHF|CFC|PLF|MMF|LAGR|DUKE)")
RX_IND_AEROLINIA = re.compile(r"^[A-Z]{3}\d")
RX_IND_MATRICULA = re.compile(r"^[A-Z]{1,2}-?[A-Z]{3,4}$")
MODELS_EXTINCIO = {"CL2T", "CL5T", "AT8T", "AT6T", "AT5T", "M18"}
MODELS_JET = set("""C25A C25B C25C C25M C510 C525 C550 C560 C56X C650 C680 C68A C700 C750 CL30 CL35 CL60
GL5T GL7T GLEX GLF4 GLF5 GLF6 G150 G280 FA7X FA8X F2TH F900 FA50 E50P E55P E545 E550 E35L H25B LJ35 LJ45
LJ60 LJ75 PC24 PC12 PRM1 BE40 HDJT SF50""".split())
RX_MODEL_HELI = re.compile(r"^(EC\d|AS3|AS5|AS6|H1[2-7]\d|H160|R22|R44|R66|B06|B05|B407|B412|B429|B505|A109|A119|A139|"
                           r"A169|A189|AW|BK17|S76|S92|EXPL|NH90|EH10|MI\d|UH\d|H47|H60|EN28|EN48|CABR)")
RX_MODEL_LLEUGER = re.compile(r"^(C15\d|C17\d|C18\d|C20\d|C21\d|P28|PA\d|DA[24]\d|DV20|SR2\d|TB\d|M20|BE3\d|BE2\d|RV\d|"
                              r"TOBA|AA5|DR\d{2}|CAP\d|G115|TECN|P92|P2002|WT9|VIRU|SIRA)")

PAD_URL = "https://raw.githubusercontent.com/sdr-enthusiasts/plane-alert-db/main/plane-alert-db.csv"
PAD_DIES = 7

NOMS_FONTS = {"github": "GitHub", "opensky": "OpenSky", "adsblol": "adsb.lol", "adsbfi": "adsb.fi"}


# -----------------------------------------------------------------------------
# UTILITATS
# -----------------------------------------------------------------------------
def peticio(url, metode="GET", dades=None, capcaleres=None, temps=30):
    h = {"User-Agent": UA}
    h.update(capcaleres or {})
    req = urllib.request.Request(url, data=dades, headers=h, method=metode)
    try:
        with urllib.request.urlopen(req, timeout=temps) as r:
            return r.status, r.read()
    except urllib.error.HTTPError as e:
        return e.code, e.read()
    except Exception as e:
        return 0, str(e).encode()


def num(v):
    try:
        if v is None or v == "" or isinstance(v, bool):
            return None
        n = float(v)
        return n if math.isfinite(n) else None
    except Exception:
        return None


def arrodoneix(x):
    return int(math.floor(x + 0.5))


def distancia(lat1, lon1, lat2, lon2):
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = (math.sin(dlat / 2) ** 2 + math.cos(math.radians(lat1)) *
         math.cos(math.radians(lat2)) * math.sin(dlon / 2) ** 2)
    return 2 * 6371 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def rumb(lat1, lon1, lat2, lon2):
    f1, f2 = math.radians(lat1), math.radians(lat2)
    dl = math.radians(lon2 - lon1)
    y = math.sin(dl) * math.cos(f2)
    x = math.cos(f1) * math.sin(f2) - math.sin(f1) * math.cos(f2) * math.cos(dl)
    graus = (math.degrees(math.atan2(y, x)) + 360) % 360
    noms = ["al nord", "al nord-est", "a l'est", "al sud-est", "al sud", "al sud-oest", "a l'oest", "al nord-oest"]
    return noms[arrodoneix(graus / 45) % 8]


def km_text(km):
    return f"{km:.1f}".replace(".", ",")


def nom_nucli(n):
    return n[0] + (f" ({n[1]})" if n[1] != n[0] else "")


def ubicacio(lat, lon):
    millor, d_min = NUCLIS[0], math.inf
    for n in NUCLIS:
        d = distancia(n[2], n[3], lat, lon)
        if d < d_min:
            millor, d_min = n, d
    if d_min < 0.5:
        return "sobre " + nom_nucli(millor)
    return f"a {km_text(d_min)} km {rumb(millor[2], millor[3], lat, lon)} de {nom_nucli(millor)}"


def moment(ms):
    return dt.datetime.fromtimestamp(ms / 1000, TZ)


def data_hora(ms):
    d = moment(ms)
    return f"el {d:%d.%m.%Y} a les {d:%H.%M} h"


def nom_font(f):
    return NOMS_FONTS.get(f, f)


# -----------------------------------------------------------------------------
# PLANE-ALERT-DB (es renova cada 7 dies; es desa a la branca dades)
# -----------------------------------------------------------------------------
def categoria_pad(tipus, categoria):
    t, c = str(tipus or "").strip(), str(categoria or "")
    if re.search(r"Flying Doctors", c, re.I):
        return "sanitari"
    if re.search(r"Firefight|Fire Fighting", c, re.I):
        return "extincio"
    if re.search(r"Coastguard", c, re.I):
        return "salvament"
    if t == "Pol" or re.search(r"Police", c, re.I):
        return "seguretat"
    if re.fullmatch(r"UAV", c, re.I):
        return "dron"
    if re.search(r"Ptolemy", c, re.I):
        return "treballs"
    if t == "Mil":
        return "militar"
    if t == "Gov":
        return "estat"
    return ""


def carrega_pad(carpeta):
    fitxer = carpeta / "pad.json"
    try:
        pad = json.loads(fitxer.read_text(encoding="utf-8"))
        if time.time() - pad.get("data", 0) < PAD_DIES * 86400:
            return pad["base"]
    except Exception:
        pad = None

    codi, cos = peticio(PAD_URL, temps=60)
    if codi != 200:
        print(f"⚠️ plane-alert-db: HTTP {codi}; es continua amb la versió anterior.")
        return pad["base"] if pad else {}
    files = list(csv.reader(io.StringIO(cos.decode("utf-8", errors="replace"))))
    cap = [re.sub(r"^[$#]+", "", c).strip() for c in files[0]]
    col = lambda nom: cap.index(nom) if nom in cap else -1
    i_hex, i_reg, i_op, i_mod, i_tip, i_cat = (col("ICAO"), col("Registration"), col("Operator"),
                                               col("ICAO Type"), col("CMPG"), col("Category"))
    if -1 in (i_hex, i_tip, i_cat):
        print("⚠️ plane-alert-db: el format ha canviat; es continua amb la versió anterior.")
        return pad["base"] if pad else {}
    base = {}
    for f in files[1:]:
        if len(f) <= max(i_hex, i_tip, i_cat):
            continue
        h = f[i_hex].strip().lower()
        if not re.fullmatch(r"[0-9a-f]{6}", h):
            continue
        cel = lambda i: f[i].strip() if i != -1 and i < len(f) else ""
        base[h] = [cel(i_reg), cel(i_op), cel(i_mod), categoria_pad(f[i_tip], f[i_cat]), f[i_cat].strip()]
    fitxer.write_text(json.dumps({"data": time.time(), "base": base}, separators=(",", ":")), encoding="utf-8")
    print(f"📚 plane-alert-db actualitzada: {len(base)} aeronaus.")
    return base


# -----------------------------------------------------------------------------
# CLASSIFICACIÓ (igual que classificarAeronau_)
# -----------------------------------------------------------------------------
def motiu_coneguda(c):
    return "aeronau coneguda" + (f" ({c['nota']})" if c.get("nota") else "")


def coneguda(a):
    matric = re.sub(r"\s", "", str(a.get("matricula") or "")).upper()
    return CONEGUDES.get(matric) or CONEGUDES.get(a["hex"])


def classificar(a, pad):
    c = coneguda(a)
    if c and c["categoria"] in CATEGORIES:
        return c["categoria"], motiu_coneguda(c), c.get("nota", "")

    p = pad.get(a["hex"])
    if p:
        if not a["matricula"] and p[0]:
            a["matricula"] = p[0]
        if not a["operador"] and p[1]:
            a["operador"] = p[1]
        if not a["model"] and p[2]:
            a["model"] = p[2]
        if p[3] in CATEGORIES:
            return p[3], f"plane-alert-db ({p[4]})", ""

    operador = f"{a['operador']} {a['indicatiu']}".upper()
    model = str(a["model"] or "").upper()
    cat = str(a["categoria"] or "").upper()
    indic = str(a["indicatiu"] or "").upper()
    matric = re.sub(r"\s", "", str(a["matricula"] or "")).upper()

    if RX_SANITARI.search(operador):
        return "sanitari", "operador o indicatiu sanitari", ""
    if RX_EXTINCIO.search(operador):
        return "extincio", "operador d'extinció", ""
    if model in MODELS_EXTINCIO:
        return "extincio", f"model d'extinció ({model})", ""
    if RX_SEGURETAT.search(operador):
        return "seguretat", "operador de seguretat o trànsit", ""
    if RX_SALVAMENT.search(operador):
        return "salvament", "operador de salvament", ""
    if a["militar"]:
        return "militar", "marcada com a militar per la font", ""
    if RX_IND_MILITAR.search(indic):
        return "militar", "indicatiu militar", ""
    if cat == "B6":
        return "dron", "categoria dron (B6)", ""
    if model in MODELS_JET:
        return "jet", f"model de jet privat ({model})", ""
    if RX_TREBALLS.search(operador):
        return "treballs", "operador de treballs aeris", ""
    if cat == "A7" or re.search(r"HELICOPTER", a["descripcio"] or "", re.I) or RX_MODEL_HELI.search(model):
        return "helicopter", "helicòpter sense operador identificat", ""
    if cat in ("B1", "B2", "B3", "B4"):
        return "vol_lliure", f"categoria {cat}", ""
    if a["flarm"] and not cat:
        return "vol_lliure", "senyal FLARM", ""
    if cat == "A1" or RX_MODEL_LLEUGER.search(model):
        return "general", "aeronau lleugera", ""
    if RX_IND_AEROLINIA.search(indic):
        return "comercial", "indicatiu de companyia", ""
    if cat in ("A3", "A4", "A5"):
        return "comercial", f"categoria d'avió gran ({cat})", ""
    if RX_IND_MATRICULA.search(indic) or (not indic and matric):
        return "general", "vola amb la matrícula com a indicatiu", ""
    return "desconegut", "sense dades suficients", ""


def aeronau(o, fonts):
    return {
        "hex": str(o.get("hex") or "").lower().strip(),
        "indicatiu": str(o.get("indicatiu") or "").strip(),
        "matricula": str(o.get("matricula") or "").strip(),
        "model": str(o.get("model") or "").strip(),
        "descripcio": str(o.get("descripcio") or "").strip(),
        "operador": str(o.get("operador") or "").strip(),
        "categoria": str(o.get("categoria") or "").strip(),
        "lat": num(o.get("lat")), "lon": num(o.get("lon")),
        "altitudM": num(o.get("altitudM")),
        "aTerra": o.get("aTerra") is True,
        "velocitatKmh": num(o.get("velocitatKmh")),
        "trackGraus": num(o.get("trackGraus")),
        "verticalMmin": num(o.get("verticalMmin")),
        "squawk": str(o.get("squawk") or "").strip(),
        "militar": o.get("militar") is True,
        "flarm": o.get("flarm") is True,
        "tempsPosMs": num(o.get("tempsPosMs")) or time.time() * 1000,
        "fonts": list(fonts or [o.get("font") or "github"]),
    }


def completa_amb(a, model, pad):
    for k in ("indicatiu", "matricula", "model", "descripcio", "operador", "categoria", "squawk"):
        if not a[k] and model[k]:
            a[k] = model[k]
    if model["militar"]:
        a["militar"] = True
    a["distanciaKm"] = distancia(CENTRE[0], CENTRE[1], a["lat"], a["lon"])
    a["cat"], a["motiu"], a["nota"] = classificar(a, pad)
    a["emergencia"] = SQUAWKS.get(a["squawk"], "")
    a["esdeveniment"] = ""
    return a


# -----------------------------------------------------------------------------
# MISSATGES (els mateixos textos que l'Apps Script)
# -----------------------------------------------------------------------------
def identificacio(a):
    parts = []
    if a["indicatiu"]:
        parts.append("Indicatiu: " + a["indicatiu"])
    if a["matricula"]:
        parts.append("Matrícula: " + a["matricula"])
    if not parts:
        parts.append("Codi icao24: " + a["hex"])
    return " · ".join(parts)


def text_vol(a):
    if a["aTerra"]:
        return "A terra"
    parts = []
    if a["altitudM"] is not None:
        parts.append(f"Altitud: {arrodoneix(a['altitudM'])} m")
    if a["velocitatKmh"] is not None:
        parts.append(f"Velocitat: {arrodoneix(a['velocitatKmh'])} km/h")
    if a["verticalMmin"] is not None:
        if a["verticalMmin"] <= -60:
            parts.append(f"baixant ({arrodoneix(a['verticalMmin'])} m/min)")
        elif a["verticalMmin"] >= 60:
            parts.append(f"pujant (+{arrodoneix(a['verticalMmin'])} m/min)")
        else:
            parts.append("vol estable")
    return " · ".join(parts)


def enllacos(hexa, lat, lon):
    linies = [f"🗺️ https://www.google.com/maps?q={lat:.5f},{lon:.5f}"]
    if re.fullmatch(r"[0-9a-f]{6}", hexa or ""):
        linies.append("🔎 https://globe.adsb.lol/?icao=" + hexa)
    return linies


def linia_model(a):
    if a["descripcio"] or a["model"]:
        return "Model: " + (a["descripcio"] + (f" ({a['model']})" if a["model"] else "") if a["descripcio"] else a["model"])
    return None


def cos_comu(a, linies, sufix_vol=""):
    for l in (identificacio(a), linia_model(a),
              ("Operador: " + a["operador"]) if a["operador"] else None,
              ("Nota: " + a["nota"]) if a["nota"] else None):
        if l:
            linies.append(l)
    vol = text_vol(a)
    if vol:
        linies.append(vol + sufix_vol)


def missatge_aeronau(a):
    emoji, nom = CATEGORIES.get(a["cat"], CATEGORIES["desconegut"])
    linies = []
    if a["emergencia"]:
        linies.append(f"🆘 CODI D'EMERGÈNCIA {a['squawk']}: {a['emergencia']}")
    linies.append(f"{emoji} {nom}" + (" — CONTINUA A LA ZONA" if a.get("continua") else ""))
    linies.append("📍 " + ubicacio(a["lat"], a["lon"]))
    if a["esdeveniment"] == "terra":
        linies.append("🛬 A terra dins la zona: ha aterrat o és a punt d'enlairar-se.")
    if a["esdeveniment"] == "baixant":
        linies.append(f"🛬 Possible aterratge: vola a menys de {ALTITUD_BAIXA_M} m i baixant.")
    if a["esdeveniment"] == "pujant":
        linies.append("🛫 Possible enlairament: ha aparegut volant baix i pujant.")
    linies.append(identificacio(a))
    for l in (linia_model(a), ("Operador: " + a["operador"]) if a["operador"] else None,
              ("Nota: " + a["nota"]) if a["nota"] else None):
        if l:
            linies.append(l)
    vol = text_vol(a)
    if vol:
        linies.append(vol)
    linies.append("Vist " + data_hora(a["tempsPosMs"]))
    linies.append("Fonts: " + ", ".join(nom_font(f) for f in a["fonts"]))
    return "\n".join(linies + enllacos(a["hex"], a["lat"], a["lon"]))


def missatge_pas(a):
    emoji, nom = CATEGORIES.get(a["cat"], CATEGORIES["desconegut"])
    linies = []
    if a["emergencia"]:
        linies.append(f"🆘 CODI D'EMERGÈNCIA {a['squawk']}: {a['emergencia']}")
    linies.append(f"⏱️ PAS ENTRE REVISIONS — {emoji} {nom}")
    linies.append(f"📍 Va passar {ubicacio(a['lat'], a['lon'])} {data_hora(a['tempsPosMs'])}.")
    cos_comu(a, linies, " (en aquell moment)")
    linies.append("Fonts: " + ", ".join(nom_font(f) for f in a["fonts"]))
    linies.append("(Detectat per la vigilància contínua de GitHub entre dues revisions.)")
    return "\n".join(linies + enllacos(a["hex"], a["lat"], a["lon"]))


def text_rumb(graus):
    noms = ["cap al nord", "cap al nord-est", "cap a l'est", "cap al sud-est",
            "cap al sud", "cap al sud-oest", "cap a l'oest", "cap al nord-oest"]
    return noms[arrodoneix((graus % 360) / 45) % 8]


def prediccio_sobrevol(a, ara_ms):
    if a["aTerra"] or a["trackGraus"] is None:
        return None
    if a["velocitatKmh"] is None or a["velocitatKmh"] < VELOCITAT_MIN_SOBREVOL_KMH:
        return None
    lat0 = CENTRE[0]
    km_lat, km_lon = 111.32, 111.32 * math.cos(math.radians(lat0))
    px, py = (a["lon"] - CENTRE[1]) * km_lon, (a["lat"] - lat0) * km_lat
    rad = math.radians(a["trackGraus"])
    vx, vy = (a["velocitatKmh"] / 60) * math.sin(rad), (a["velocitatKmh"] / 60) * math.cos(rad)
    v2 = vx * vx + vy * vy
    if not v2:
        return None
    retard = max(0, (ara_ms - (a["tempsPosMs"] or ara_ms)) / 60000)
    millor = None
    for n in NUCLIS:
        nx, ny = (n[3] - CENTRE[1]) * km_lon, (n[2] - lat0) * km_lat
        wx, wy = px - nx, py - ny
        tca = -(wx * vx + wy * vy) / v2
        if tca < 0:
            continue
        minuts = tca - retard
        if minuts < -1 or minuts > HORITZO_SOBREVOL_MIN:
            continue
        d = math.hypot(wx + vx * tca, wy + vy * tca)
        if d > RADI_SOBREVOL_KM:
            continue
        if not millor or minuts < millor["minuts"]:
            millor = {"nucli": n, "minuts": max(0, minuts), "horaMs": ara_ms + max(0, minuts) * 60000,
                      "distanciaKm": d}
    return millor


def missatge_sobrevol(a, p):
    emoji, nom = CATEGORIES.get(a["cat"], CATEGORIES["desconegut"])
    hora = moment(p["horaMs"]).strftime("%H.%M")
    minuts = arrodoneix(p["minuts"])
    linies = []
    if a["emergencia"]:
        linies.append(f"🆘 CODI D'EMERGÈNCIA {a['squawk']}: {a['emergencia']}")
    linies.append(f"🛫 SOBREVOL PREVIST — {emoji} {nom}")
    linies.append("📍 Passarà " + ("per sobre de " if p["distanciaKm"] < 0.8 else f"a {km_text(p['distanciaKm'])} km de ") +
                  nom_nucli(p["nucli"]) + f" cap a les {hora} h" +
                  (f" (d'aquí a {minuts} min)" if minuts > 0 else " (ara mateix)"))
    linies.append(f"Ara és {ubicacio(a['lat'], a['lon'])}, {text_rumb(a['trackGraus'])}.")
    cos_comu(a, linies)
    linies.append("Fonts: " + ", ".join(nom_font(f) for f in a["fonts"]))
    linies.append("(Predicció en línia recta: si l'aeronau gira, pot no passar-hi.)")
    return "\n".join(linies + enllacos(a["hex"], a["lat"], a["lon"]))


def missatge_desaparegut(hexa, reg):
    emoji, nom = CATEGORIES.get(reg.get("cat"), CATEGORIES["desconegut"])
    alt = reg.get("alt")
    linies = [
        f"🛬 POSSIBLE ATERRATGE — {emoji} {nom}",
        "📍 Última posició: " + ubicacio(reg["lat"], reg["lon"]),
        reg.get("ident") or ("Codi icao24: " + hexa),
        f"L'últim cop que es va veure ({data_hora(reg['vist'])}) volava a " +
        (f"{arrodoneix(alt)} m" if alt is not None else "poca altura") +
        ". Ja no apareix a cap font: pot haver aterrat o haver sortit de la cobertura dels receptors.",
    ]
    return "\n".join(linies + enllacos(hexa, reg["lat"], reg["lon"]))


# -----------------------------------------------------------------------------
# TELEGRAM I GIST
# -----------------------------------------------------------------------------
def enviar(text):
    token = os.environ.get("TELEGRAM_BOT_TOKEN_INFOS", "").strip()
    xat = os.environ.get("TELEGRAM_CHAT_ID_INFOS", "").strip()
    if os.environ.get("ENVIAR_AVISOS") != "1" or not token or not xat:
        print("🧪 [prova, no s'envia]\n" + text + "\n---")
        return "prova (no enviat)"
    dades = urllib.parse.urlencode({"chat_id": xat, "text": text, "disable_web_page_preview": "false"}).encode()
    codi, cos = peticio(f"https://api.telegram.org/bot{token}/sendMessage", "POST", dades,
                        {"Content-Type": "application/x-www-form-urlencoded"})
    try:
        if codi == 200 and json.loads(cos).get("ok"):
            return "enviat"
    except Exception:
        pass
    print(f"❌ Telegram: HTTP {codi} {cos[:200]!r}")
    return "error de Telegram"


def gist(metode="GET", fitxers=None):
    gid, tok = os.environ.get("GIST_ID", "").strip(), os.environ.get("GIST_TOKEN", "").strip()
    cap = {"Authorization": "Bearer " + tok, "Accept": "application/vnd.github+json"}
    if metode == "GET":
        codi, cos = peticio("https://api.github.com/gists/" + gid, capcaleres=cap)
        if codi != 200:
            raise RuntimeError(f"Gist: HTTP {codi}")
        return json.loads(cos)
    cos = json.dumps({"files": {k: {"content": v} for k, v in fitxers.items()}}).encode()
    codi, _ = peticio("https://api.github.com/gists/" + gid, "PATCH", cos, {**cap, "Content-Type": "application/json"})
    if codi != 200:
        print(f"⚠️ No s'ha pogut desar l'estat al Gist: HTTP {codi}")


def contingut_gist(g, nom):
    f = (g.get("files") or {}).get(nom)
    if not f:
        return None
    if f.get("truncated") and f.get("raw_url"):
        codi, cos = peticio(f["raw_url"])
        return cos.decode("utf-8") if codi == 200 else None
    return f.get("content")


# -----------------------------------------------------------------------------
# REGISTRE (branca dades)
# -----------------------------------------------------------------------------
ESDEVENIMENTS = {"terra": "a terra", "baixant": "possible aterratge", "pujant": "possible enlairament"}


def fila_registre(a, avis, alerta):
    t = moment(a["tempsPosMs"])
    color = (coneguda(a) or {}).get("color", "")
    publica = a["cat"] in CATEGORIES_PUBLIQUES or bool(color)
    esdev = ESDEVENIMENTS.get(a["esdeveniment"], "")
    if a["esdeveniment"] == "emergencia":
        esdev = "codi d'emergència " + a["squawk"]
    return {
        "data": f"{t:%d.%m.%Y}", "hora": f"{t:%H.%M}",
        "icao24": a["hex"] if publica else "",
        "indicatiu": a["indicatiu"] if publica else "",
        "matricula": a["matricula"] if publica else "",
        "model": a["model"], "descripcio": a["descripcio"],
        "operador": a["operador"] if publica else "",
        "categoria": CATEGORIES.get(a["cat"], CATEGORIES["desconegut"])[1],
        "clau": a["cat"],
        "motiu": a["motiu"],
        "esdeveniment": esdev,
        "avis": avis,
        "alerta": alerta,
        "altitud": arrodoneix(a["altitudM"]) if a["altitudM"] is not None else None,
        "velocitat": arrodoneix(a["velocitatKmh"]) if a["velocitatKmh"] is not None else None,
        "vertical": arrodoneix(a["verticalMmin"]) if a["verticalMmin"] is not None else None,
        "aTerra": a["aTerra"],
        "squawk": a["squawk"],
        "distancia": round(a["distanciaKm"], 1),
        "ubicacio": ubicacio(a["lat"], a["lon"]),
        "lat": round(a["lat"], 5), "lon": round(a["lon"], 5),
        "fonts": ", ".join(nom_font(f) for f in a["fonts"]),
        "color": color,
    }


class Registre:
    """Una fila per pas de cada aeronau; mentre continua passant, s'actualitza
    amb el punt on ha estat més a prop de la Bisbal."""

    def __init__(self, carpeta, estat):
        self.carpeta = carpeta / "registre"
        self.carpeta.mkdir(parents=True, exist_ok=True)
        self.passos = estat.setdefault("passos", {})
        self.dies = {}

    def dia(self, d):
        if d not in self.dies:
            try:
                self.dies[d] = json.loads((self.carpeta / f"{d}.json").read_text(encoding="utf-8"))
            except Exception:
                self.dies[d] = []
        return self.dies[d]

    def apunta(self, a, avis, alerta, ara_ms):
        p = self.passos.get(a["hex"])
        if not p or ara_ms - p["vist"] > MINUTS_NOU_PAS * 60000:
            p = {"id": hashlib.sha1(f"{a['hex']}{ara_ms}".encode()).hexdigest()[:12],
                 "dia": moment(a["tempsPosMs"]).strftime("%Y-%m-%d"), "dist": 1e9, "avis": ""}
            self.passos[a["hex"]] = p
        p["vist"] = ara_ms
        files = self.dia(p["dia"])
        fila = next((f for f in files if f.get("id") == p["id"]), None)
        # Un avís enviat no s'esborra encara que l'actualització posterior no n'enviï cap.
        if avis and (not p["avis"] or "enviat" not in p["avis"] or "enviat" in avis):
            p["avis"] = avis
        alerta = alerta or bool(fila and fila.get("alerta"))
        if fila is None or a["distanciaKm"] < p["dist"]:
            nova = fila_registre(a, p["avis"], alerta)
            nova["id"] = p["id"]
            if fila is None:
                files.append(nova)
            else:
                fila.clear()
                fila.update(nova)
            p["dist"] = a["distanciaKm"]
        else:
            fila["avis"], fila["alerta"] = p["avis"], alerta
            if a["esdeveniment"] and not fila["esdeveniment"]:
                fila["esdeveniment"] = fila_registre(a, "", alerta)["esdeveniment"]

    def apunta_desaparegut(self, hexa, reg, avis):
        p = self.passos.get(hexa)
        files = self.dia(p["dia"]) if p else []
        fila = next((f for f in files if p and f.get("id") == p["id"]), None)
        if fila is not None:
            fila["esdeveniment"] = "desaparegut volant baix"
            fila["avis"] = avis if avis else fila["avis"]

    def desa(self, ara_ms):
        for d, files in self.dies.items():
            files.sort(key=lambda f: (f["data"][6:], f["data"][3:5], f["data"][:2], f["hora"]))
            (self.carpeta / f"{d}.json").write_text(json.dumps(files, ensure_ascii=False, separators=(",", ":")),
                                                    encoding="utf-8")
        limit = (moment(ara_ms) - dt.timedelta(days=DIES_REGISTRE)).strftime("%Y-%m-%d")
        dies = sorted(f.stem for f in self.carpeta.glob("*.json"))
        for d in dies:
            if d < limit:
                (self.carpeta / f"{d}.json").unlink()
        dies = [d for d in dies if d >= limit]
        (self.carpeta.parent / "dies.json").write_text(json.dumps(sorted(dies, reverse=True)), encoding="utf-8")
        for h in list(self.passos):
            if ara_ms - self.passos[h]["vist"] > 6 * 3600000:
                del self.passos[h]


# -----------------------------------------------------------------------------
# FUNCIÓ PRINCIPAL (com comprovarAeronaus)
# -----------------------------------------------------------------------------
def main(carpeta):
    carpeta.mkdir(parents=True, exist_ok=True)
    ara_ms = time.time() * 1000
    finestra = MINUTS_ENTRE_AVISOS * 60000

    g = gist()
    try:
        estat = json.loads(contingut_gist(g, FITXER_ESTAT) or "{}")
    except Exception:
        estat = {}
    avisos = estat.setdefault("avisos", {})
    estat_fonts = estat.setdefault("fonts", {})

    d = json.loads(contingut_gist(g, FITXER_GIST) or "{}")
    edat_min = (ara_ms - num(d.get("generat") or 0)) / 60000 if d.get("generat") else math.inf
    if not d.get("ok") or edat_min > GIST_MAX_MINUTS:
        print(f"⚠️ Dades del Gist no vàlides o velles ({edat_min:.0f} min). No es fa res.")
        return

    pad = carrega_pad(carpeta)
    registre = Registre(carpeta, estat)

    # 0. Vigilant de fonts: avís si una font falla durant HORES_FONT_CAIGUDA hores.
    for idf, f in (d.get("fonts") or {}).items():
        e = estat_fonts.get(idf) or {"desDe": 0, "avisat": False}
        if f.get("ok"):
            if e.get("avisat"):
                enviar(f"✅ VIGILANT D'AERONAUS\nLa font {nom_font(idf)} torna a respondre.")
            e = {"desDe": 0, "avisat": False}
        else:
            e["desDe"] = e.get("desDe") or ara_ms
            e["error"] = f.get("error", "")
            if not e["avisat"] and ara_ms - e["desDe"] >= HORES_FONT_CAIGUDA * 3600000:
                text = (f"⚠️ VIGILANT D'AERONAUS\nLa font {nom_font(idf)} no respon des del "
                        f"{data_hora(e['desDe'])[3:]}.\nDarrer error: {e['error']}\nLes altres fonts continuen funcionant.")
                if enviar(text) != "error de Telegram":
                    e["avisat"] = True
        estat_fonts[idf] = e

    # Aeronaus del Gist: posició actual (si és recent) i punt més proper.
    actuals, passos = [], []
    for e in d.get("aeronaus") or []:
        if not e or not e.get("darrer") or not e.get("proper"):
            continue
        darrer, proper = aeronau(e["darrer"], e.get("fonts")), aeronau(e["proper"], e.get("fonts"))
        if not darrer["hex"] or darrer["lat"] is None or darrer["lon"] is None:
            continue
        completa_amb(darrer, darrer, pad)
        if darrer["distanciaKm"] > RADI_REGISTRE_KM:
            continue
        if proper["lat"] is not None and proper["lon"] is not None:
            completa_amb(proper, darrer, pad)
            passos.append(proper)
        if ara_ms - darrer["tempsPosMs"] <= GITHUB_ACTUAL_MIN * 60000:
            actuals.append(darrer)

    vistos = {a["hex"] for a in actuals}
    dins = [a for a in actuals if a["distanciaKm"] <= RADI_KM]
    fora = [a for a in actuals if a["distanciaKm"] > RADI_KM]
    comercials = no_comercials = sobrevols = passos_avisats = 0

    # 1. Aeronaus que hi ha ara a la zona d'avisos.
    for a in dins:
        if a["cat"] == "comercial" and not a["emergencia"] and not AVISAR_COMERCIALS:
            comercials += 1
            registre.apunta(a, "no s'avisa (comercial)", False, ara_ms)
            continue
        no_comercials += a["cat"] != "comercial"
        comercials += a["cat"] == "comercial"

        reg = avisos.get(a["hex"])
        nova_estada = not reg or ara_ms - reg["vist"] > finestra
        if nova_estada:
            reg = {"primer": ara_ms, "avisat": 0, "esdev": {}}
        baix = a["aTerra"] or (a["altitudM"] is not None and a["altitudM"] <= ALTITUD_BAIXA_M)
        vr = a["verticalMmin"]
        esdev = ""
        if a["emergencia"] and not reg["esdev"].get("sq" + a["squawk"]):
            esdev = "emergencia"
        elif a["aTerra"] and not reg["esdev"].get("terra"):
            esdev = "terra"
        elif not a["aTerra"] and baix and vr is not None and vr <= -60 and not reg["esdev"].get("baixant"):
            esdev = "baixant"
        elif not a["aTerra"] and baix and vr is not None and vr >= 60 and nova_estada:
            esdev = "pujant"
        a["esdeveniment"] = esdev
        a["continua"] = bool(reg["avisat"]) and not esdev

        avis = ""
        if esdev or not reg["avisat"] or ara_ms - reg["avisat"] > finestra:
            avis = enviar(missatge_aeronau(a))
            if avis != "error de Telegram":
                reg["avisat"] = ara_ms
                if esdev:
                    reg["esdev"]["sq" + a["squawk"] if esdev == "emergencia" else esdev] = True
        reg.update({"vist": ara_ms, "lat": a["lat"], "lon": a["lon"], "alt": a["altitudM"],
                    "dist": a["distanciaKm"], "baix": baix, "aTerra": a["aTerra"], "cat": a["cat"],
                    "ident": identificacio(a)})
        avisos[a["hex"]] = reg
        registre.apunta(a, avis, True, ara_ms)

    # 1b. Fora de la zona d'avisos (fins a 40 km): registre i sobrevols previstos.
    for a in fora:
        avis = "fora de la zona d'avisos"
        alerta = False
        p = prediccio_sobrevol(a, ara_ms)
        if p:
            clau = "pred-" + a["hex"]
            reg_pred = avisos.get(clau)
            hora = moment(p["horaMs"]).strftime("%H.%M")
            avis = f"sobrevol previst: {p['nucli'][0]} cap a les {hora} h"
            if a["cat"] == "comercial" and not a["emergencia"] and not AVISAR_COMERCIALS:
                avis += " (comercial, no s'avisa)"
            elif reg_pred and ara_ms - reg_pred["avisat"] < finestra:
                avis += " (ja avisat)"
            else:
                resultat = enviar(missatge_sobrevol(a, p))
                avis += f" ({resultat})"
                alerta = True   # com a l'Apps Script: els sobrevols avisats surten al tauler
                if resultat != "error de Telegram":
                    avisos[clau] = {"avisat": ara_ms, "vist": ara_ms}
                    sobrevols += 1
            if clau in avisos:
                avisos[clau]["vist"] = ara_ms
        registre.apunta(a, avis, alerta, ara_ms)

    # 1c. Passos entre revisions: punts més propers dins la zona d'aeronaus que ara no hi són.
    hex_dins = {a["hex"] for a in dins}
    for a in passos:
        if a["hex"] in hex_dins or a["distanciaKm"] > RADI_KM:
            if a["hex"] not in vistos and a["distanciaKm"] <= RADI_REGISTRE_KM:
                registre.apunta(a, "", False, ara_ms)   # també queden al registre
            continue
        reg = avisos.get(a["hex"])
        if reg and (reg["vist"] >= a["tempsPosMs"] or ara_ms - (reg.get("avisat") or 0) < finestra):
            continue
        clau = "pas-" + a["hex"]
        if avisos.get(clau) and ara_ms - avisos[clau]["avisat"] < finestra:
            continue
        hex_dins.add(a["hex"])
        if a["cat"] == "comercial" and not a["emergencia"] and not AVISAR_COMERCIALS:
            avis = "pas entre revisions · no s'avisa (comercial)"
            avisos[clau] = {"avisat": ara_ms, "vist": ara_ms}
            comercials += 1
            registre.apunta(a, avis, False, ara_ms)
            continue
        resultat = enviar(missatge_pas(a))
        if resultat != "error de Telegram":
            avisos[clau] = {"avisat": ara_ms, "vist": ara_ms}
            passos_avisats += 1
        no_comercials += 1
        registre.apunta(a, f"pas entre revisions ({resultat})", True, ara_ms)

    # 2. Aeronaus que volaven baix a la zona i ja no apareixen.
    for hexa, reg in list(avisos.items()):
        if "-" in hexa or hexa in vistos:
            continue
        if not reg.get("baix") or reg.get("aTerra") or reg.get("esdev", {}).get("desaparegut"):
            continue
        if reg["dist"] > RADI_KM * 0.75 or ara_ms - reg["vist"] > (INTERVAL_MINUTS * 2 + 5) * 60000:
            continue
        avis = enviar(missatge_desaparegut(hexa, reg))
        if avis != "error de Telegram":
            reg["esdev"]["desaparegut"] = True
        registre.apunta_desaparegut(hexa, reg, avis)

    # 3. Neteja de la memòria (més de 6 hores sense veure-les).
    for k in list(avisos):
        if ara_ms - avisos[k]["vist"] > 6 * 3600000:
            del avisos[k]

    # 4. Fonts de la revisió (com la pestanya «Fonts»).
    dia = moment(ara_ms).strftime("%Y-%m-%d")
    fitxer_fonts = carpeta / "fonts" / f"{dia}.json"
    fitxer_fonts.parent.mkdir(exist_ok=True)
    try:
        llista_fonts = json.loads(fitxer_fonts.read_text(encoding="utf-8"))
    except Exception:
        llista_fonts = []
    f = d.get("fonts") or {}
    estat_font = lambda k: ("✅" if f.get(k, {}).get("ok") else "❌ " + f.get(k, {}).get("error", "")) if k in f else "—"
    llista_fonts.append({"hora": moment(ara_ms).strftime("%H.%M"), "adsblol": estat_font("adsblol"),
                         "adsbfi": estat_font("adsbfi"), "opensky": estat_font("opensky"),
                         "zona": len(dins), "noComercials": no_comercials, "registre": len(actuals)})
    fitxer_fonts.write_text(json.dumps(llista_fonts, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    for vell in (carpeta / "fonts").glob("*.json"):
        if vell.stem < (moment(ara_ms) - dt.timedelta(days=DIES_REGISTRE)).strftime("%Y-%m-%d"):
            vell.unlink()

    registre.desa(ara_ms)
    (carpeta / "estat-public.json").write_text(json.dumps({
        "generat": moment(ara_ms).strftime("%d.%m.%Y %H.%M"), "zona": len(dins), "registre": len(actuals),
        "fonts": {k: {"ok": v.get("ok"), "error": v.get("error", "")} for k, v in f.items()}
    }, ensure_ascii=False), encoding="utf-8")
    gist("PATCH", {FITXER_ESTAT: json.dumps(estat, separators=(",", ":"))})

    print(f"✈️ A la zona: {len(dins)} (comercials: {comercials} · no comercials: {no_comercials}) · "
          f"fins a {RADI_REGISTRE_KM} km: {len(actuals)} · sobrevols avisats: {sobrevols} · "
          f"passos avisats: {passos_avisats}.")


if __name__ == "__main__":
    main(Path(sys.argv[1] if len(sys.argv) > 1 else "dades"))

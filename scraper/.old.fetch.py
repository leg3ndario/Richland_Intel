#!/usr/bin/env python3
"""
Richland County SC – Motivated Seller Lead Scraper
====================================================
Source  : The Columbia Star – Public Notices
          https://www.thecolumbiastar.com/category/public-notices/
Strategy: WordPress REST API (primary) → HTML category pagination (fallback)
          Each post is fetched and its full text parsed with regex to extract
          individual legal notices (foreclosures, judgments, liens, probate …)
Parcel  : Richland County ArcGIS REST FeatureServer + DBF bulk ZIP fallback
Output  : dashboard/records.json | data/records.json | data/leads_ghl_export.csv

Lead types extracted from notice text:
  NOFC  / LP    – Foreclosure / Lis Pendens summons & Master's Sale notices
  TAXDEED       – Tax deed / delinquent-tax sale notices
  JUD / CCJ     – Judgment / transcript-judgment notices
  DRJUD         – Domestic / Family Court judgment
  LNCORPTX      – Corp / business tax lien
  LNIRS         – IRS / federal tax lien
  LNFED         – Federal government lien
  LN            – General lien notices
  LNMECH        – Mechanic's lien
  LNHOA         – HOA / condo lien (from HOA foreclosure notices)
  MEDLN         – Medicaid / hospital lien
  PRO           – Probate: "Notice to Creditors", estate notices
  NOC           – Notice of Commencement
  RELLP         – Release / cancellation of lis pendens
"""

import asyncio
import csv
import json
import os
import re
import sys
import time
import traceback
import zipfile
from datetime import datetime, timedelta, timezone
from io import BytesIO
from pathlib import Path
from urllib.parse import urlencode, urljoin, quote

import requests
from bs4 import BeautifulSoup

# Optional Playwright (used only for JS-heavy fallback if needed)
try:
    from playwright.async_api import async_playwright, TimeoutError as PWTimeout
    HAS_PW = True
except ImportError:
    HAS_PW = False

try:
    from dbfread import DBF
    HAS_DBF = True
except ImportError:
    HAS_DBF = False

# ══════════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ══════════════════════════════════════════════════════════════════════════════

LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "7"))
STATE         = "SC"
COUNTY        = "Richland"

BASE_URL      = "https://www.thecolumbiastar.com"
# WordPress REST API – public-notices category (id discovered below)
WP_API_BASE   = f"{BASE_URL}/wp-json/wp/v2"
CAT_SLUG      = "public-notices"
CAT_URL       = f"{BASE_URL}/category/public-notices/"

# Richland County parcel endpoints (tried in order)
PARCEL_ENDPOINTS = [
    "https://richlandmaps.com/arcgis/rest/services/Parcels/Parcels/MapServer/0/query",
    "https://services1.arcgis.com/YkiDNd5aIbTOILfR/arcgis/rest/services/Richland_County_Parcels/FeatureServer/0/query",
    "https://gis.richlandcountysc.gov/arcgis/rest/services/Parcels/MapServer/0/query",
]
DBF_URLS = [
    "https://www.richlandcountysc.gov/Portals/0/GIS/Parcels.zip",
    "https://richlandmaps.com/data/Parcels.zip",
]

SCRIPT_DIR = Path(__file__).parent
REPO_ROOT  = SCRIPT_DIR.parent
OUT_PATHS  = [
    REPO_ROOT / "dashboard" / "records.json",
    REPO_ROOT / "data"      / "records.json",
]
CSV_PATH   = REPO_ROOT / "data" / "leads_ghl_export.csv"

RETRY_MAX   = 3
RETRY_DELAY = 4
REQ_TIMEOUT = 25

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "en-US,en;q=0.9",
}

# ── Document-type classification patterns ─────────────────────────────────────
# Each entry: (doc_type, category, cat_label, [regex_patterns on notice text])
# Patterns are applied to the UPPER-CASED text block of each individual notice
CLASSIFICATION_RULES = [
    # ── Foreclosure / Lis Pendens ─────────────────────────────────────────────
    ("LP", "preforeclosure", "Lis Pendens", [
        r"NOTICE\s+OF\s+PEND[EI]NC[YE]\s+OF\s+ACTION",
        r"LIS\s+PENDENS",
        r"NOTICE\s+OF\s+FILING\s+COMPLAINT",
    ]),
    ("NOFC", "preforeclosure", "Notice of Foreclosure", [
        r"MASTER['']?S?\s+SALE",
        r"NOTICE\s+OF\s+(MASTER|FORECLOSURE|SALE)",
        r"FORECLOSURE\s+OF\s+REAL\s+ESTATE",
        r"SUMMONS\s+AND\s+NOTICE[S]?\s+FORECLOSURE",
        r"NOTICE\s+OF\s+FORECLOSURE\s+SALE",
        r"FORECLOSURE\s+SALE",
        r"BY\s+VIRTUE\s+OF\s+(A\s+)?DECREE",
        r"MASTER\s+IN\s+EQUITY",
    ]),
    # ── Tax / Delinquent tax ──────────────────────────────────────────────────
    ("TAXDEED", "tax", "Tax Deed / Tax Sale", [
        r"TAX\s+DEED",
        r"DELINQUENT\s+TAX\s+(SALE|AUCTION)",
        r"TAX\s+SALE",
        r"RICHLAND\s+COUNTY\s+TAX\s+COLLECTOR",
    ]),
    # ── Judgments ─────────────────────────────────────────────────────────────
    ("DRJUD", "judgment", "Domestic Judgment", [
        r"FAMILY\s+COURT",
        r"IN\s+THE\s+FAMILY\s+COURT",
        r"DOMESTIC\s+JUDGMENT",
    ]),
    ("JUD", "judgment", "Judgment / Certified Judgment", [
        r"TRANSCRIPT\s+(?:OF\s+)?JUDGMENT",
        r"CONFESSION\s+OF\s+JUDGMENT",
        r"FOREIGN\s+JUDGMENT",
        r"(?:ABSTRACT|NOTICE)\s+OF\s+JUDGMENT",
        r"JUDGMENT\s+(?:LIEN|DOCKET)",
        r"NOTICE\s+OF\s+JUDGMENT",
    ]),
    # ── Liens ─────────────────────────────────────────────────────────────────
    ("LNIRS", "tax_lien", "IRS Lien", [
        r"INTERNAL\s+REVENUE",
        r"IRS\s+(?:TAX\s+)?LIEN",
        r"FEDERAL\s+TAX\s+LIEN",
    ]),
    ("LNCORPTX", "tax_lien", "Corp Tax Lien", [
        r"CORP(?:ORATE)?\s+TAX\s+LIEN",
        r"SOUTH\s+CAROLINA\s+DEPARTMENT\s+OF\s+REVENUE.*LIEN",
        r"BUSINESS\s+TAX\s+LIEN",
    ]),
    ("LNFED", "tax_lien", "Federal Lien", [
        r"UNITED\s+STATES.*LIEN",
        r"FEDERAL\s+(?:GOVERNMENT\s+)?LIEN",
        r"U\.?S\.?\s+GOVERNMENT.*LIEN",
    ]),
    ("LNMECH", "lien", "Mechanic Lien", [
        r"MECHANIC['']?S?\s+LIEN",
        r"MATERIALMAN['']?S?\s+LIEN",
        r"CONTRACTOR'S?\s+LIEN",
        r"NOTICE\s+OF\s+(?:MECHANIC|CONTRACTOR|MATERIALMAN)",
    ]),
    ("LNHOA", "lien", "HOA Lien", [
        r"HOMEOWNER['']?S?\s+ASSOCIATION.*(?:LIEN|SALE)",
        r"HOA.*(?:LIEN|SALE|FORECLOSURE)",
        r"HOMEOWNERS'\s+ASSOCIATION.*FORECLOSURE",
        r"PROPERTY\s+OWNERS'\s+ASSOCIATION.*LIEN",
        r"CONDOMINIUM.*(?:LIEN|SALE)",
    ]),
    ("MEDLN", "lien", "Medicaid / Medical Lien", [
        r"MEDICAID\s+LIEN",
        r"DHEC.*LIEN",
        r"HOSPITAL.*LIEN",
        r"MEDICAL.*LIEN",
        r"SOUTH\s+CAROLINA\s+DEPARTMENT\s+OF\s+HEALTH",
    ]),
    ("LN", "lien", "Lien", [
        r"NOTICE\s+OF\s+LIEN\s+SALE",
        r"LIEN\s+SALE",
        r"STORAGE\s+(?:UNIT|AUCTION|LIEN)",
        r"TOWING.*LIEN",
        r"LIEN\s+(?:NOTICE|CLAIM)",
    ]),
    # ── Probate ───────────────────────────────────────────────────────────────
    ("PRO", "probate", "Probate / Estate", [
        r"NOTICE\s+TO\s+CREDITORS\s+OF\s+ESTATES?",
        r"PROBATE\s+COURT",
        r"PERSONAL\s+REPRESENTATIVE",
        r"ESTATE\s+OF\s+[A-Z]",
        r"LETTERS\s+(?:TESTAMENTARY|OF\s+ADMINISTRATION)",
        r"INTESTATE\s+ESTATE",
    ]),
    # ── Notice of Commencement ────────────────────────────────────────────────
    ("NOC", "construction", "Notice of Commencement", [
        r"NOTICE\s+OF\s+COMMENCEMENT",
        r"NOTICE\s+IS\s+HEREBY\s+GIVEN.*COMMENCEMENT",
    ]),
    # ── Release Lis Pendens ───────────────────────────────────────────────────
    ("RELLP", "release", "Release Lis Pendens", [
        r"RELEASE\s+(?:OF\s+)?LIS\s+PENDENS",
        r"CANCELLATION\s+(?:OF\s+)?LIS\s+PENDENS",
        r"WITHDRAWAL\s+(?:OF\s+)?LIS\s+PENDENS",
    ]),
    # ── CCJ ───────────────────────────────────────────────────────────────────
    ("CCJ", "judgment", "Certified Judgment", [
        r"CERTIFIED\s+JUDGMENT",
        r"CERTIFICATE\s+OF\s+JUDGMENT",
    ]),
]

# ══════════════════════════════════════════════════════════════════════════════
# UTILITIES
# ══════════════════════════════════════════════════════════════════════════════

def log(msg: str):
    ts = datetime.now(timezone.utc).strftime("%H:%M:%S")
    print(f"[{ts}] {msg}", flush=True)


def today_utc() -> datetime:
    return datetime.now(timezone.utc)


def cutoff_dt() -> datetime:
    return today_utc() - timedelta(days=LOOKBACK_DAYS)


def retry(fn, attempts=RETRY_MAX, delay=RETRY_DELAY):
    last = None
    for i in range(attempts):
        try:
            return fn()
        except Exception as e:
            last = e
            if i < attempts - 1:
                log(f"  ↻ retry {i+1}: {e}")
                time.sleep(delay)
    raise last


def parse_amount(text: str) -> float | None:
    if not text:
        return None
    c = re.sub(r"[^\d.]", "", str(text))
    try:
        return float(c) if c else None
    except ValueError:
        return None


def name_variants(name: str) -> list[str]:
    if not name:
        return []
    n = name.strip().upper()
    parts = n.split()
    v = {n}
    if len(parts) >= 2:
        last  = parts[-1]
        first = " ".join(parts[:-1])
        v.add(f"{last} {first}")
        v.add(f"{last}, {first}")
        if "," in n:
            halves = n.split(",", 1)
            v.add(f"{halves[1].strip()} {halves[0].strip()}")
    return list(v)


def clean_text(html_text: str) -> str:
    """Strip HTML tags and normalise whitespace."""
    soup = BeautifulSoup(html_text, "lxml")
    return re.sub(r"\s+", " ", soup.get_text(separator=" ")).strip()

# ══════════════════════════════════════════════════════════════════════════════
# NOTICE TEXT PARSER
# ══════════════════════════════════════════════════════════════════════════════

# Patterns that mark the START of a new individual notice block
_NOTICE_SPLIT_RE = re.compile(
    r"(?:MASTER['']?S?\s+SALE|"
    r"NOTICE\s+OF\s+(?:MASTER|SALE|FORECLOSURE|LIEN|PENDENCY|APPLICATION|"
    r"COMMENCEMENT|UNCLAIMED|JUDGMENT)|"
    r"SUMMONS\s+AND\s+NOTICE|"
    r"NOTICE\s+TO\s+CREDITORS|"
    r"NOTICE\s+OF\s+FORECLOSURE|"
    r"ORDER\s+APPOINTING|"
    r"MASTER\s+IN\s+EQUITY'?S?\s+(?:NOTICE|SALE)|"
    r"NOTICE\s+IS\s+HEREBY\s+GIVEN)",
    re.IGNORECASE,
)

def split_into_notices(full_text: str) -> list[str]:
    """
    Split the full post text into individual notice blocks.
    Returns a list of non-empty text blocks, each beginning with a notice header.
    """
    text = re.sub(r"\s+", " ", full_text).strip()
    # Find all header positions
    matches = list(_NOTICE_SPLIT_RE.finditer(text))
    if not matches:
        return [text] if text else []

    blocks = []
    for i, m in enumerate(matches):
        start = m.start()
        end   = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        block = text[start:end].strip()
        if len(block) > 80:   # skip tiny fragments
            blocks.append(block)

    # Anything before first match
    if matches[0].start() > 100:
        prefix = text[:matches[0].start()].strip()
        if len(prefix) > 80:
            blocks.insert(0, prefix)

    return blocks


def classify_notice(text: str) -> tuple[str, str, str]:
    """
    Return (doc_type, category, cat_label) for a notice text block.
    Falls back to (NOFC, preforeclosure) for unclassified court sale text.
    """
    upper = text.upper()
    for doc_type, cat, label, patterns in CLASSIFICATION_RULES:
        for pat in patterns:
            if re.search(pat, upper):
                return doc_type, cat, label
    # If it mentions "CASE NO" or "C/A NO" with a court-action number → likely foreclosure
    if re.search(r"C/?A\s*NO\.?|CASE\s*NO\.?|CIVIL\s+ACTION", upper):
        return "NOFC", "preforeclosure", "Notice of Foreclosure"
    return "LN", "lien", "Lien / Notice"


def extract_ca_number(text: str) -> str:
    """Extract C/A No. / Civil Action No. / Case No."""
    for pat in [
        r"C/?A\.?\s*No\.?\s*:?\s*([\d]{4}[-–]CP[-–]\d+[-–]\d+)",
        r"CIVIL\s+ACTION\s+NO\.?\s*:?\s*([\d]{4}[-–]CP[-–]\d+[-–]\d+)",
        r"CASE\s+NO\.?\s*:?\s*([\d]{4}[-–]CP[-–]\d+[-–]\d+)",
        r"CASE\s+NO\.?\s*:?\s*([\w\d\-–]+\d{4,})",
        r"C/?A\s*No\.?\s*([\dA-Z]{4,}CP\d+[-–]\d+)",
        r"No\.?\s+(20\d\d[-–](?:CP|DR)[-–]\d+[-–]\d+)",
        r"(20\d\d[-–]CP[-–]\d+[-–]\d+)",
        r"(20\d\dCP\d{4,})",
    ]:
        m = re.search(pat, text, re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return ""


def extract_property_address(text: str) -> tuple[str, str, str, str]:
    """Extract street, city, state, zip from notice text."""
    # "Property Address: 1710 Oriole Rd Columbia, SC 29204"
    patterns = [
        r"Property\s+Address\s*:?\s+([^\n\r]{5,80})",
        r"property\s+(?:is\s+)?(?:located\s+(?:at\s+)?)([0-9]\d*\s+[^\n\r,]{5,60}(?:,\s*\w[\w\s]+,?\s*SC\s+\d{5}))",
        r"PROPERTY\s+ADDRESS\s*:?\s*([^\n\r]+)",
        r"commonly\s+known\s+as\s+([0-9]\d*\s+[^\n\r,]+(?:SC\s+\d{5}))",
        r"also\s+known\s+as\s+([0-9]\d*\s+[^\n\r,]+(?:SC\s+\d{5}))",
    ]
    for pat in patterns:
        m = re.search(pat, text, re.IGNORECASE)
        if m:
            raw = re.sub(r"\s+", " ", m.group(1)).strip()
            # Parse "123 Main St Columbia, SC 29201" or "123 Main St, Columbia SC 29201"
            city_state_zip = re.search(
                r"([A-Za-z ]+),?\s*(SC)\s*(\d{5})", raw, re.IGNORECASE
            )
            if city_state_zip:
                addr_end   = raw.find(city_state_zip.group(0))
                street     = raw[:addr_end].strip(" ,")
                city       = city_state_zip.group(1).strip()
                state_code = city_state_zip.group(2).upper()
                zipcode    = city_state_zip.group(3)
                return street, city, state_code, zipcode
            return raw, "Columbia", "SC", ""
    return "", "", "SC", ""


def extract_tms(text: str) -> str:
    """Extract TMS# / PIN# parcel number."""
    for pat in [
        r"TMS[/#\s]*(?:No\.?\s*)?[:=]?\s*([RMrm]?\d[\dA-Z\-]+)",
        r"TMS#\s*:?\s*([RMrm]?\d[\dA-Z\-]+)",
        r"PIN#?\s*:?\s*([RMrm]?\d[\dA-Z\-]+)",
        r"Parcel\s+No\.?\s*:?\s*([RMrm]?\d[\dA-Z\-]+)",
        r"APN\s*:?\s*([RMrm]?\d[\dA-Z\-]+)",
    ]:
        m = re.search(pat, text, re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return ""


def extract_parties(text: str, doc_type: str) -> tuple[str, str]:
    """
    Extract grantor (owner/defendant) and grantee (plaintiff/lender).
    For foreclosure: plaintiff = lender (grantee), defendant = homeowner (grantor/owner).
    """
    owner, grantee = "", ""

    # Look for "X vs. Y" or "X against Y" pattern
    vs_patterns = [
        r"case\s+of\s*:?\s*(.+?)\s+(?:vs?\.?|against)\s+(.+?)(?:\s*,\s*I,|\s*C/A|\s*BY\s+VIRTUE|\.|$)",
        r"(.+?)\s*,\s*Plaintiff\s*,?\s*(?:vs?\.?|against)\s+(.+?)\s*(?:,\s*Defendant|$)",
    ]
    for pat in vs_patterns:
        m = re.search(pat, text, re.IGNORECASE | re.DOTALL)
        if m:
            plaintiff = re.sub(r"\s+", " ", m.group(1)).strip()[:120]
            defendant = re.sub(r"\s+", " ", m.group(2)).strip()[:120]
            # For foreclosure/sale: defendant is homeowner/grantor
            if doc_type in ("NOFC", "LP", "LNHOA", "LN", "JUD", "CCJ"):
                owner, grantee = defendant, plaintiff
            else:
                owner, grantee = plaintiff, defendant
            break

    # Probate: "Estate of JOHN SMITH"
    if doc_type == "PRO" and not owner:
        m = re.search(r"Estate\s+of\s+([A-Z][a-zA-Z\s,\.]{3,60})", text, re.IGNORECASE)
        if m:
            owner = m.group(1).strip()

    return owner, grantee


def extract_amount(text: str) -> float | None:
    """Extract dollar amount from notice text."""
    patterns = [
        r"original\s+principal\s+sum\s+of\s+\$\s*([\d,]+(?:\.\d{2})?)",
        r"amount\s+of\s+\$\s*([\d,]+(?:\.\d{2})?)",
        r"principal\s+(?:balance|sum|amount).*?\$\s*([\d,]+(?:\.\d{2})?)",
        r"judgment\s+(?:amount\s+of\s+)?\$\s*([\d,]+(?:\.\d{2})?)",
        r"debt\s+of\s+\$\s*([\d,]+(?:\.\d{2})?)",
        r"\$([\d,]+(?:\.\d{2})?)\s*(?:lien|mortgage|judgment|balance)",
        r"sum\s+of\s+\$\s*([\d,]+(?:\.\d{2})?)",
    ]
    best = None
    for pat in patterns:
        m = re.search(pat, text, re.IGNORECASE)
        if m:
            v = parse_amount(m.group(1))
            if v and v > 0:
                if best is None or v > best:
                    best = v
    return best


def extract_legal_description(text: str) -> str:
    """Extract a concise legal description."""
    # Try to grab the lot/block/subdivision description
    patterns = [
        r"(?:ALL\s+THAT\s+CERTAIN\s+PIECE|being\s+shown\s+(?:and\s+)?(?:designated|delineated)\s+as)\s+(.{20,300}?)(?:\.|This\s+being|SUBJECT\s+TO|TERMS|TMS)",
        r"(?:LEGAL\s+DESCRIPTION[:\s]+)(.{20,300}?)(?:\.|TMS|Property\s+Address)",
        r"(?:situated?\s+in|lying\s+and\s+being\s+in)[^.]{0,40}(Lot\s+\d[^.]{0,200}?)(?:\.|TMS|This\s+being)",
    ]
    for pat in patterns:
        m = re.search(pat, text, re.IGNORECASE | re.DOTALL)
        if m:
            legal = re.sub(r"\s+", " ", m.group(1)).strip()[:300]
            return legal
    return ""


def extract_pub_date(post: dict) -> datetime | None:
    """Parse post publication date from WordPress API response."""
    raw = post.get("date_gmt") or post.get("date", "")
    if not raw:
        return None
    try:
        return datetime.fromisoformat(raw.rstrip("Z")).replace(tzinfo=timezone.utc)
    except Exception:
        return None


def post_date_str(post: dict) -> str:
    dt = extract_pub_date(post)
    if dt:
        return dt.strftime("%m/%d/%Y")
    return ""

# ══════════════════════════════════════════════════════════════════════════════
# SCORER
# ══════════════════════════════════════════════════════════════════════════════

def score_record(rec: dict) -> tuple[list[str], int]:
    flags = []
    cat   = rec.get("cat", "")
    dtype = rec.get("doc_type", "")
    amt   = rec.get("amount")
    owner = (rec.get("owner") or "").upper()
    filed = rec.get("filed", "")

    if dtype == "LP" or "LIS PENDENS" in owner.upper():
        flags.append("Lis pendens")
    if dtype in ("NOFC", "LP") or cat == "preforeclosure":
        flags.append("Pre-foreclosure")
    if cat == "judgment" or dtype in ("JUD", "CCJ", "DRJUD"):
        flags.append("Judgment lien")
    if cat == "tax_lien" or dtype in ("LNCORPTX", "LNIRS", "LNFED", "TAXDEED"):
        flags.append("Tax lien")
    if dtype in ("LNMECH", "LNHOA", "LN", "MEDLN") or (cat == "lien" and dtype not in ("LNIRS","LNCORPTX","LNFED")):
        flags.append("Mechanic lien")
    if cat == "probate" or dtype == "PRO":
        flags.append("Probate / estate")

    CORP = ["LLC", "INC", "CORP", "L.L.C", "L.P.", "LTD", "TRUST", "ESTATE",
            "HOLDINGS", "PROPERTIES", "GROUP", "PARTNERS", "FUND",
            "SERVICING", "MORTGAGE", "BANK", "NATIONAL ASSOCIATION",
            "VENTURES", "REALTY", "INVESTMENTS", "FINANCIAL"]
    if any(kw in owner for kw in CORP):
        flags.append("LLC / corp owner")

    try:
        fd = datetime.strptime(filed, "%m/%d/%Y")
        if fd >= (today_utc() - timedelta(days=7)):
            flags.append("New this week")
    except Exception:
        pass

    # Deduplicate
    seen, unique = set(), []
    for f in flags:
        if f not in seen:
            seen.add(f)
            unique.append(f)

    score = 30
    score += 10 * len(unique)
    if "Lis pendens" in unique and "Pre-foreclosure" in unique:
        score += 20
    if amt is not None:
        if amt > 100_000:
            score += 15
        elif amt > 50_000:
            score += 10
    if "New this week" in unique:
        score += 5
    if rec.get("prop_address") or rec.get("mail_address"):
        score += 5

    return unique, min(score, 100)

# ══════════════════════════════════════════════════════════════════════════════
# PARCEL LOOKUP
# ══════════════════════════════════════════════════════════════════════════════

class ParcelLookup:
    def __init__(self):
        self.by_name: dict[str, dict] = {}
        self.by_pin:  dict[str, dict] = {}
        self.by_addr: dict[str, dict] = {}
        self._loaded = False

    @staticmethod
    def _norm(raw: dict) -> dict:
        def g(*keys):
            for k in keys:
                for c in [k, k.upper(), k.lower()]:
                    v = raw.get(c)
                    if v and str(v).strip() not in ("", "None", "NULL", "null"):
                        return str(v).strip()
            return ""
        return {
            "pin":        g("PIN","PARCELID","PARCEL_ID","TaxParcelNumber","PARID","OBJECTID"),
            "owner":      g("OWNER","OWN1","OWNERNAME","OWNER_NAME","OWN_NAME","OWNER1"),
            "site_addr":  g("SITE_ADDR","SITEADDR","SiteAddress","SITE_ADDRESS",
                             "PROPADDR","PROP_ADDR","ADDRESS","LOCATION"),
            "site_city":  g("SITE_CITY","SITECITY","PROPCITY","PROP_CITY","CITY"),
            "site_zip":   g("SITE_ZIP","SITEZIP","PROPZIP","PROP_ZIP"),
            "mail_addr":  g("ADDR_1","MAILADR1","MAILADDR","MAIL_ADDR",
                             "MAILING_ADDRESS","MAIL1","ADDR1"),
            "mail_city":  g("CITY","MAILCITY","MAIL_CITY"),
            "mail_state": g("STATE","MAILSTATE","MAIL_STATE"),
            "mail_zip":   g("ZIP","MAILZIP","MAIL_ZIP","ZIPCODE"),
        }

    def _load_arcgis(self, url: str) -> list[dict]:
        records, offset, ps = [], 0, 1000
        s = requests.Session()
        s.headers.update(HEADERS)
        while True:
            params = {
                "where":             "1=1",
                "outFields":         "*",
                "f":                 "json",
                "resultOffset":      offset,
                "resultRecordCount": ps,
                "returnGeometry":    "false",
            }
            resp = retry(lambda u=url, p=params: s.get(u, params=p, timeout=REQ_TIMEOUT))
            data = resp.json()
            if "error" in data:
                raise RuntimeError(f"ArcGIS error: {data['error']}")
            feats = data.get("features", [])
            if not feats:
                break
            for f in feats:
                records.append(f.get("attributes", {}))
            if not data.get("exceededTransferLimit", True):
                break
            offset += ps
            time.sleep(0.1)
        return records

    def _load_dbf(self) -> list[dict]:
        if not HAS_DBF:
            log("  dbfread not installed – skipping DBF fallback")
            return []
        for url in DBF_URLS:
            try:
                log(f"  DBF fallback: {url}")
                resp = requests.get(url, timeout=45, headers=HEADERS)
                if resp.status_code != 200:
                    continue
                z = zipfile.ZipFile(BytesIO(resp.content))
                dbf_names = [n for n in z.namelist() if n.lower().endswith(".dbf")]
                if not dbf_names:
                    continue
                tmp = Path("/tmp/_parcels.dbf")
                tmp.write_bytes(z.read(dbf_names[0]))
                table = DBF(str(tmp), load=True, ignore_missing_memofile=True,
                            encoding="utf-8", char_decode_errors="replace")
                return [dict(row) for row in table]
            except Exception as e:
                log(f"  DBF failed for {url}: {e}")
        return []

    def load(self):
        if self._loaded:
            return
        raw: list[dict] = []
        for url in PARCEL_ENDPOINTS:
            try:
                log(f"Loading parcels → {url.split('/')[2]}")
                raw = self._load_arcgis(url)
                if raw:
                    log(f"  ✓ {len(raw):,} parcels via ArcGIS REST")
                    break
            except Exception as e:
                log(f"  ArcGIS failed: {e}")

        if not raw:
            raw = self._load_dbf()

        if not raw:
            log("  ⚠ No parcel data – address enrichment disabled")
            self._loaded = True
            return

        for r in raw:
            try:
                p = self._norm(r)
                if p["pin"]:
                    self.by_pin[p["pin"].upper()] = p
                if p["owner"]:
                    for v in name_variants(p["owner"]):
                        if v not in self.by_name:
                            self.by_name[v] = p
                if p["site_addr"]:
                    key = p["site_addr"].upper().strip()
                    if key not in self.by_addr:
                        self.by_addr[key] = p
            except Exception:
                pass

        self._loaded = True
        log(f"  Parcel index: {len(self.by_name):,} name keys / "
            f"{len(self.by_pin):,} PINs / {len(self.by_addr):,} addresses")

    def lookup_name(self, owner: str) -> dict | None:
        if not self._loaded:
            self.load()
        for v in name_variants(owner):
            p = self.by_name.get(v)
            if p:
                return p
        return None

    def lookup_addr(self, addr: str) -> dict | None:
        if not self._loaded:
            self.load()
        if not addr:
            return None
        key = re.sub(r"\s+", " ", addr.upper().strip())
        return self.by_addr.get(key)

    def lookup_pin(self, pin: str) -> dict | None:
        if not self._loaded:
            self.load()
        return self.by_pin.get(pin.upper().strip()) if pin else None

# ══════════════════════════════════════════════════════════════════════════════
# COLUMBIA STAR FETCHER
# ══════════════════════════════════════════════════════════════════════════════

class ColumbiaStarFetcher:
    """
    Fetches public-notice posts from The Columbia Star.
    Strategy:
      1. WordPress REST API  →  get posts in public-notices category
         within the lookback window
      2. HTML category page pagination fallback
    """

    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update(HEADERS)
        self._cat_id: int | None = None

    # ── WordPress category ID lookup ──────────────────────────────────────────

    def _get_category_id(self) -> int | None:
        if self._cat_id is not None:
            return self._cat_id
        try:
            url  = f"{WP_API_BASE}/categories"
            resp = retry(lambda: self.session.get(
                url, params={"slug": CAT_SLUG, "per_page": 5}, timeout=REQ_TIMEOUT
            ))
            cats = resp.json()
            if isinstance(cats, list) and cats:
                self._cat_id = cats[0]["id"]
                log(f"  WP category id for '{CAT_SLUG}': {self._cat_id}")
                return self._cat_id
        except Exception as e:
            log(f"  Category ID lookup failed: {e}")
        return None

    # ── WordPress REST API fetch ──────────────────────────────────────────────

    def fetch_via_api(self, cutoff: datetime) -> list[dict]:
        """
        Retrieve posts from the WP REST API.
        Returns list of WP post objects (with 'content', 'title', 'date', 'link').
        """
        cat_id = self._get_category_id()
        if not cat_id:
            return []

        posts    = []
        page     = 1
        per_page = 20
        cutoff_str = cutoff.strftime("%Y-%m-%dT%H:%M:%S")

        while True:
            params = {
                "categories": cat_id,
                "per_page":   per_page,
                "page":       page,
                "after":      cutoff_str,
                "orderby":    "date",
                "order":      "desc",
                "_fields":    "id,date,date_gmt,title,content,link,excerpt",
            }
            try:
                resp = retry(lambda p=params: self.session.get(
                    f"{WP_API_BASE}/posts", params=p, timeout=REQ_TIMEOUT
                ))
                if resp.status_code == 400:
                    break  # bad page number = past the end
                batch = resp.json()
                if not isinstance(batch, list) or not batch:
                    break
                posts.extend(batch)
                log(f"  API page {page}: {len(batch)} posts")
                if len(batch) < per_page:
                    break
                page += 1
                time.sleep(0.5)
            except Exception as e:
                log(f"  API page {page} error: {e}")
                break

        log(f"  WP API: {len(posts)} posts fetched")
        return posts

    # ── HTML pagination fallback ──────────────────────────────────────────────

    def fetch_via_html(self, cutoff: datetime) -> list[dict]:
        """
        Scrape the HTML category listing pages.
        Returns list of synthetic post dicts with 'link', 'date', 'title', 'content'.
        """
        posts    = []
        page_url = CAT_URL
        stop     = False

        while page_url and not stop:
            try:
                resp = retry(lambda u=page_url: self.session.get(u, timeout=REQ_TIMEOUT))
                soup = BeautifulSoup(resp.text, "lxml")

                articles = soup.find_all("article") or soup.find_all(
                    "div", class_=re.compile(r"post|entry|article", re.I)
                )

                if not articles:
                    # Fallback: grab all <h2> links
                    h2_links = soup.select("h2 a[href]")
                    articles = [{"link": a["href"], "title": a.get_text(strip=True)}
                                for a in h2_links]

                for art in articles:
                    try:
                        if isinstance(art, dict):
                            link  = art.get("link", "")
                            title = art.get("title", "")
                            date_str = ""
                        else:
                            a_tag  = art.find("a", href=True)
                            link   = a_tag["href"] if a_tag else ""
                            title  = a_tag.get_text(strip=True) if a_tag else ""
                            # Date usually in <time> or meta
                            time_el = art.find("time")
                            date_str = ""
                            if time_el:
                                date_str = time_el.get("datetime") or time_el.get_text(strip=True)

                        if not link:
                            continue

                        # Parse date
                        post_dt = None
                        if date_str:
                            for fmt in ["%Y-%m-%dT%H:%M:%S", "%Y-%m-%d",
                                        "%B %d, %Y", "%b %d, %Y"]:
                                try:
                                    post_dt = datetime.strptime(
                                        date_str.strip(), fmt
                                    ).replace(tzinfo=timezone.utc)
                                    break
                                except ValueError:
                                    pass

                        if post_dt and post_dt < cutoff:
                            stop = True
                            break

                        # Fetch the full article
                        art_resp = retry(lambda u=link: self.session.get(u, timeout=REQ_TIMEOUT))
                        art_soup = BeautifulSoup(art_resp.text, "lxml")

                        # Pull publish date from article page if not already known
                        if not post_dt:
                            t_el = art_soup.find("time")
                            if t_el:
                                ds = t_el.get("datetime") or t_el.get_text(strip=True)
                                for fmt in ["%Y-%m-%dT%H:%M:%S", "%B %d, %Y",
                                            "%b %d, %Y", "%Y-%m-%d"]:
                                    try:
                                        post_dt = datetime.strptime(
                                            ds.strip(), fmt
                                        ).replace(tzinfo=timezone.utc)
                                        break
                                    except ValueError:
                                        pass

                        if post_dt and post_dt < cutoff:
                            stop = True
                            break

                        content_el = (
                            art_soup.find("div", class_=re.compile(r"entry-content|post-content|article-body", re.I))
                            or art_soup.find("article")
                        )
                        content_html = str(content_el) if content_el else art_resp.text

                        posts.append({
                            "link":     link,
                            "title":    {"rendered": title},
                            "date":     post_dt.isoformat() if post_dt else "",
                            "date_gmt": post_dt.isoformat() if post_dt else "",
                            "content":  {"rendered": content_html},
                        })
                        time.sleep(0.4)

                    except Exception as e:
                        log(f"  Article fetch error: {e}")

                # Next page
                next_link = soup.find("a", string=re.compile(r"Next", re.I))
                if next_link and not stop:
                    href = next_link.get("href", "")
                    page_url = href if href.startswith("http") else BASE_URL + href
                else:
                    page_url = None

            except Exception as e:
                log(f"  HTML page error: {e}")
                break

        log(f"  HTML scrape: {len(posts)} posts fetched")
        return posts

    # ── Main fetch entry point ────────────────────────────────────────────────

    def get_posts(self) -> list[dict]:
        cutoff = cutoff_dt()
        log(f"Fetching posts published after {cutoff.strftime('%Y-%m-%d')} …")

        # Try REST API first
        posts = self.fetch_via_api(cutoff)

        if not posts:
            log("  REST API returned nothing – falling back to HTML scrape")
            posts = self.fetch_via_html(cutoff)

        return posts

# ══════════════════════════════════════════════════════════════════════════════
# NOTICE PARSER  (post → individual records)
# ══════════════════════════════════════════════════════════════════════════════

_EMPTY_RECORD = {
    "doc_num":      "",
    "doc_type":     "",
    "filed":        "",
    "cat":          "",
    "cat_label":    "",
    "owner":        "",
    "grantee":      "",
    "amount":       None,
    "legal":        "",
    "prop_address": "",
    "prop_city":    "",
    "prop_state":   STATE,
    "prop_zip":     "",
    "mail_address": "",
    "mail_city":    "",
    "mail_state":   STATE,
    "mail_zip":     "",
    "clerk_url":    "",
    "flags":        [],
    "score":        0,
}


def parse_post_into_records(post: dict) -> list[dict]:
    """
    Parse a single WordPress post object into a list of lead records.
    Each distinct notice block within the post becomes one record.
    """
    records   = []
    post_url  = post.get("link", "")
    pub_date  = post_date_str(post)
    raw_html  = (post.get("content") or {}).get("rendered", "")
    full_text = clean_text(raw_html)

    if not full_text.strip():
        return []

    blocks = split_into_notices(full_text)
    if not blocks:
        blocks = [full_text]

    for block in blocks:
        try:
            doc_type, cat, label = classify_notice(block)
            ca_num               = extract_ca_number(block)
            street, city, state, zipcode = extract_property_address(block)
            owner, grantee       = extract_parties(block, doc_type)
            amount               = extract_amount(block)
            legal                = extract_legal_description(block)
            tms                  = extract_tms(block)

            # Skip blocks that have absolutely no identifying information
            if not ca_num and not street and not owner and not tms:
                continue

            rec = dict(_EMPTY_RECORD)
            rec.update({
                "doc_num":      ca_num or tms or "",
                "doc_type":     doc_type,
                "filed":        pub_date,
                "cat":          cat,
                "cat_label":    label,
                "owner":        owner,
                "grantee":      grantee,
                "amount":       amount,
                "legal":        legal,
                "prop_address": street,
                "prop_city":    city or "Columbia",
                "prop_state":   state or STATE,
                "prop_zip":     zipcode,
                "clerk_url":    post_url,
                "_tms":         tms,   # internal – used for parcel lookup; removed later
            })
            records.append(rec)

        except Exception as e:
            log(f"  ⚠ block parse error: {e}")

    return records

# ══════════════════════════════════════════════════════════════════════════════
# ENRICHMENT
# ══════════════════════════════════════════════════════════════════════════════

def enrich_records(records: list[dict], parcels: ParcelLookup) -> list[dict]:
    enriched = 0
    for rec in records:
        try:
            p = None
            # Try PIN first (most accurate)
            tms = rec.pop("_tms", "")
            if tms:
                p = parcels.lookup_pin(tms)
            # Then owner name
            if not p and rec.get("owner"):
                p = parcels.lookup_name(rec["owner"])
            # Then property address
            if not p and rec.get("prop_address"):
                p = parcels.lookup_addr(rec["prop_address"])

            if p:
                if p.get("site_addr") and not rec.get("prop_address"):
                    rec["prop_address"] = p["site_addr"]
                    rec["prop_city"]    = p.get("site_city", "Columbia")
                    rec["prop_zip"]     = p.get("site_zip", "")
                rec["mail_address"] = p.get("mail_addr", "")
                rec["mail_city"]    = p.get("mail_city", "")
                rec["mail_state"]   = p.get("mail_state", STATE) or STATE
                rec["mail_zip"]     = p.get("mail_zip", "")
                enriched += 1
            else:
                rec.pop("_tms", None)  # clean up if not already popped
        except Exception:
            rec.pop("_tms", None)

        try:
            flags, sc    = score_record(rec)
            rec["flags"] = flags
            rec["score"] = sc
        except Exception:
            rec["flags"] = []
            rec["score"] = 30

    log(f"Parcel enrichment: {enriched}/{len(records)} records matched")
    return records

# ══════════════════════════════════════════════════════════════════════════════
# OUTPUT WRITERS
# ══════════════════════════════════════════════════════════════════════════════

def write_json(records: list[dict], date_from: str, date_to: str):
    with_addr = sum(1 for r in records if r.get("prop_address") or r.get("mail_address"))
    payload   = {
        "fetched_at":   datetime.now(timezone.utc).isoformat(),
        "source":       "The Columbia Star – Public Notices (Richland County SC)",
        "source_url":   CAT_URL,
        "date_range":   {"from": date_from, "to": date_to},
        "total":        len(records),
        "with_address": with_addr,
        "records":      records,
    }
    for path in OUT_PATHS:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, default=str), encoding="utf-8")
        log(f"  ✓ Wrote {path}")


def write_csv(records: list[dict]):
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    cols = [
        "First Name", "Last Name",
        "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
        "Property Address", "Property City", "Property State", "Property Zip",
        "Lead Type", "Document Type", "Date Filed", "Document Number",
        "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
        "Source", "Public Records URL",
    ]
    rows = []
    for rec in records:
        parts = (rec.get("owner") or "").split()
        first = parts[0] if parts else ""
        last  = " ".join(parts[1:]) if len(parts) > 1 else ""
        rows.append({
            "First Name":             first,
            "Last Name":              last,
            "Mailing Address":        rec.get("mail_address", ""),
            "Mailing City":           rec.get("mail_city", ""),
            "Mailing State":          rec.get("mail_state", STATE),
            "Mailing Zip":            rec.get("mail_zip", ""),
            "Property Address":       rec.get("prop_address", ""),
            "Property City":          rec.get("prop_city", ""),
            "Property State":         rec.get("prop_state", STATE),
            "Property Zip":           rec.get("prop_zip", ""),
            "Lead Type":              rec.get("cat_label", ""),
            "Document Type":          rec.get("doc_type", ""),
            "Date Filed":             rec.get("filed", ""),
            "Document Number":        rec.get("doc_num", ""),
            "Amount/Debt Owed":       rec.get("amount", ""),
            "Seller Score":           rec.get("score", 0),
            "Motivated Seller Flags": "; ".join(rec.get("flags", [])),
            "Source":                 "The Columbia Star – Richland County Public Notices",
            "Public Records URL":     rec.get("clerk_url", ""),
        })

    with open(CSV_PATH, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=cols)
        w.writeheader()
        w.writerows(rows)
    log(f"  ✓ GHL CSV → {CSV_PATH} ({len(rows)} rows)")

# ══════════════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════════════

async def main():
    date_from = cutoff_dt().strftime("%m/%d/%Y")
    date_to   = today_utc().strftime("%m/%d/%Y")

    log("=" * 62)
    log(f"Richland County SC – Columbia Star Public Notice Scraper")
    log(f"Source : {CAT_URL}")
    log(f"Range  : {date_from} → {date_to}  ({LOOKBACK_DAYS} days)")
    log("=" * 62)

    # 1. Load parcel data
    parcels = ParcelLookup()
    parcels.load()

    # 2. Fetch posts from Columbia Star
    log("\n── Fetching Columbia Star posts ────────────────────────────")
    fetcher = ColumbiaStarFetcher()
    posts   = fetcher.get_posts()
    log(f"  Posts retrieved: {len(posts)}")

    # 3. Parse each post into individual notice records
    log("\n── Parsing notices ─────────────────────────────────────────")
    all_records: list[dict] = []
    for post in posts:
        try:
            recs = parse_post_into_records(post)
            all_records.extend(recs)
        except Exception as e:
            log(f"  ⚠ post parse error: {e}")

    log(f"  Raw records extracted: {len(all_records)}")

    # 4. Enrich with parcel data + scoring
    log("\n── Enriching records ───────────────────────────────────────")
    all_records = enrich_records(all_records, parcels)

    # 5. Sort by score desc
    all_records.sort(key=lambda r: r.get("score", 0), reverse=True)

    # 6. Write outputs
    log("\n── Writing outputs ─────────────────────────────────────────")
    write_json(all_records, date_from, date_to)
    write_csv(all_records)

    high   = sum(1 for r in all_records if r.get("score", 0) >= 60)
    w_addr = sum(1 for r in all_records if r.get("prop_address") or r.get("mail_address"))
    log(f"\n✅  Done.  total={len(all_records)}  score≥60={high}  with_address={w_addr}")
    log(f"   Types: { {r['doc_type'] for r in all_records} }")


if __name__ == "__main__":
    asyncio.run(main())

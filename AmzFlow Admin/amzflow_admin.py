#!/usr/bin/env python3
"""AmzFlow - Amazon product graphics automation.

This is the customer-facing launcher. It contains both working engines and
does not import scraper_ui.py, exporter_ui.py, or amazon_scraper.py.
"""

import csv
import html
import json
import os
import re
import sys
import time
import subprocess
import argparse
import base64
import hashlib
import platform
import urllib.request
import uuid
from datetime import datetime
try:
    from playwright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeout
except ModuleNotFoundError:
    # The desktop app can still open and point the customer to setup if the
    # optional browser runtime has not been installed yet.
    sync_playwright = None

    class PlaywrightTimeout(Exception):
        pass


BASE_DIR = os.path.dirname(os.path.abspath(__file__))

ASIN_RE = re.compile(r"^B[0-9A-Z]{9}$")          # e.g. B0D9MBGVRT

def to_url(token: str) -> str:
    """Convert an ASIN or full URL to a canonical amazon.in/dp/... URL."""
    token = token.strip()
    if ASIN_RE.match(token.upper()):
        return f"https://www.amazon.in/dp/{token.upper()}"
    return token                                   # already a URL

# ---------------------------------------------------------------------------
# Folder helpers
# ---------------------------------------------------------------------------

def get_run_folder() -> tuple:
    """Create and return (date_folder, images_folder) for today's run."""
    date_str = datetime.now().strftime("%Y-%m-%d")
    date_folder = os.path.join(BASE_DIR, date_str)
    images_folder = os.path.join(date_folder, "images")
    os.makedirs(images_folder, exist_ok=True)
    return date_folder, images_folder


def delete_old_csvs(folder: str) -> None:
    for fname in os.listdir(folder):
        if fname.endswith(".csv"):
            os.remove(os.path.join(folder, fname))
            print(f"  Deleted old CSV: {fname}")


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------

def fmt_price(raw: str) -> str:
    """'999.00' → '₹999',  '2999' → '₹2,999'  (Indian number grouping, ₹ symbol)"""
    raw = re.sub(r'[^\d.]', '', str(raw).replace(',', ''))  # strip ₹, spaces, commas
    try:
        n = int(float(raw))
    except (ValueError, TypeError):
        return ''  # never return raw with stray symbols/spaces
    s = str(n)
    if len(s) <= 3:
        return f"₹{s}"
    result = s[-3:]
    s = s[:-3]
    while s:
        result = s[-2:] + "," + result
        s = s[:-2]
    return "₹" + result.lstrip(",")


def fmt_discount(raw: str) -> str:
    """'67% off' → '67%'"""
    m = re.search(r"(\d+)", raw)
    return f"{m.group(1)}%" if m else raw


# ---------------------------------------------------------------------------
# Title shortening
# ---------------------------------------------------------------------------

# Product-type nouns we must never chop off even if they fall past word 6
_PRODUCT_NOUNS = {
    "spoon","spoons","fork","forks","knife","knives","bowl","bowls",
    "plate","plates","cup","cups","glass","glasses","mug","mugs",
    "pan","pans","pot","pots","wok","board","boards","tray","trays",
    "rack","racks","bottle","bottles","jar","jars","box","boxes",
    "case","bag","bags","pouch","organizer","organiser","container",
    "containers","set","kit","pack","coaster","coasters","mat","mats",
    "cloth","towel","toy","block","puzzle","ring","stacker",
    "lotion","cream","serum","wash","shampoo","mask","compact",
    "foundation","concealer","lipstick","powder","carafe","pitcher",
    "dispenser","hanger","stand","holder","cutter","peeler","grater",
    "ladle","spatula","tongs","whisk","strainer","colander","steamer",
    "lid","lids","cover","covers","wrap","sheet","brush","comb",
    "mirror","watch","wallet","belt","cap","hat","socks","gloves",
    "diaper","diapers","wipes","hanky","hankies","toy","toys",
    "book","books","pen","pens","pencil","pencils","notebook",
}

# Dangling words that should never end a title after truncation
_TRAILING_STOP = {
    "for","with","and","or","in","of","to","by","a","an","the",
    "at","on","from","into","its","per","than","as","&",
}

# Phrases that are pure feature-fluff — strip anything matching these
_STRIP_PATTERNS = [
    r",\s*.+$",                  # "Egg Cutter, Egg Slicer, ..."  — first comma onward
    r",?\s+with\s+.+$",          # "with Anti-Slip" / "with Golden Ring" — greedy to end
    r",?\s+\|\s+.+$",            # "| Pack of 2"
    r",?\s+-\s+[A-Z].+$",        # "- BPA Free"  (dash + Capital = side note)
    r"\s*\([^)]*\)",             # (Grey/Tan)
    r"\s*\[[^\]]*\]",            # [Pack of 3]
]


def shorten_title(full_title: str, brand: str, max_chars: int = 50) -> str:
    title = full_title

    # 1. Strip brand prefix — handle compound brands like "SOPL-OLIVEWARE"
    brand_variants = [brand] + re.split(r"[\s\-/]+", brand) if brand else []
    for b in brand_variants:
        if b and title.lower().startswith(b.lower()):
            title = title[len(b):].lstrip(" -–:")
            break

    # 2. Strip fluff patterns
    for pat in _STRIP_PATTERNS:
        title = re.sub(pat, "", title, flags=re.IGNORECASE)

    # 3. Clean up punctuation & extra spaces
    title = re.sub(r"\s+", " ", title).strip().strip(",-–|. ")

    words = title.split()

    if len(words) <= 6:
        while words and words[-1].lower() in _TRAILING_STOP:
            words.pop()
        result = " ".join(words)
    else:
        # 4. Always include the first product-type noun found, even past word 6
        kept = words[:6]
        for i, w in enumerate(words[6:], start=6):
            if w.lower() in _PRODUCT_NOUNS:
                kept = words[:i + 1]
                break

        # 5. Drop any dangling trailing preposition/conjunction after truncation
        while kept and kept[-1].lower() in _TRAILING_STOP:
            kept.pop()

        result = " ".join(kept)

    # 6. Hard cap at max_chars — trim whole words, never mid-word
    if len(result) > max_chars:
        trimmed = result[:max_chars].rsplit(" ", 1)[0]
        # Drop trailing stop words left after the cut
        words2 = trimmed.split()
        while words2 and words2[-1].lower() in _TRAILING_STOP:
            words2.pop()
        result = " ".join(words2)

    return result


# ---------------------------------------------------------------------------
# Page extraction helpers
# ---------------------------------------------------------------------------

def _text(page, selector: str) -> str:
    try:
        el = page.locator(selector).first
        if el.count():
            return el.inner_text().strip()
    except Exception:
        pass
    return ""


def _attr(page, selector: str, attr: str) -> str:
    try:
        el = page.locator(selector).first
        if el.count():
            return el.get_attribute(attr) or ""
    except Exception:
        pass
    return ""


def _page_html(page) -> str:
    try:
        return page.content()
    except Exception:
        return ""


def _strip_html(raw: str) -> str:
    raw = re.sub(r"<script\b[^>]*>.*?</script>", " ", raw, flags=re.I | re.S)
    raw = re.sub(r"<style\b[^>]*>.*?</style>", " ", raw, flags=re.I | re.S)
    raw = re.sub(r"<[^>]+>", " ", raw)
    raw = html.unescape(raw)
    return re.sub(r"\s+", " ", raw).strip()


def _html_id_text(page, element_id: str) -> str:
    content = _page_html(page)
    if not content:
        return ""
    m = re.search(
        rf"<(?P<tag>[a-z0-9]+)\b[^>]*\bid=[\"']{re.escape(element_id)}[\"'][^>]*>(?P<body>.*?)</(?P=tag)>",
        content,
        flags=re.I | re.S,
    )
    return _strip_html(m.group("body")) if m else ""


class _EmptyLocator:
    @property
    def first(self):
        return self

    def count(self):
        return 0

    def wait_for(self, timeout=0):
        raise PlaywrightTimeout("Static HTML has no live locator")

    def inner_text(self):
        return ""

    def get_attribute(self, attr):
        return ""

    def all(self):
        return []


class _StaticHtmlPage:
    def __init__(self, content: str):
        self._content = content

    def content(self):
        return self._content

    def locator(self, selector: str):
        return _EmptyLocator()

    def evaluate(self, script: str):
        raise RuntimeError("Static HTML has no JavaScript runtime")


def fetch_static_page(url: str, browser_page=None):
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/124.0.0.0 Safari/537.36"
        ),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-IN,en;q=0.9",
    }

    if browser_page is not None:
        try:
            resp = browser_page.context.request.get(url, headers=headers, timeout=25000)
            content = resp.text()
            if resp.ok and not re.search(r"captcha|Robot Check|Enter the characters", content, re.I):
                return _StaticHtmlPage(content)
        except Exception:
            pass

    try:
        req = urllib.request.Request(
            url,
            headers=headers,
        )
        with urllib.request.urlopen(req, timeout=25) as resp:
            raw = resp.read()
        content = raw.decode("utf-8", errors="ignore")
        if re.search(r"captcha|Robot Check|Enter the characters", content, re.I):
            return None
        return _StaticHtmlPage(content)
    except Exception:
        return None


def _clean_brand_legacy(s: str) -> str:
    """Remove ®, ™, © and extra whitespace from a brand string."""
    return re.sub(r"[®™©]", "", s).strip()


def _clean_brand(s: str) -> str:
    s = html.unescape(s or "")
    s = re.sub(r"(?:Brand\s*:\s*|Visit the\s+|\s+Store\b)", "", s, flags=re.I)
    s = re.sub(r"[Â®â„¢Â©®™©]", "", s)
    return re.sub(r"\s+", " ", s).strip(" :-|")


def extract_brand(page) -> str:
    # 1. bylineInfo — "Brand: MOCA" or "Visit the MOCA Store"
    text = _text(page, "#bylineInfo")
    if text:
        m = re.search(r"(?:Brand[:\s]+|Visit the\s+)(.+?)(?:\s+Store|$)", text, re.IGNORECASE)
        if m:
            return _clean_brand(m.group(1))
        if len(text) < 40:
            return _clean_brand(text)

    # 2. #brand element
    b = _text(page, "#brand")
    if b:
        return _clean_brand(b)

    text = _html_id_text(page, "bylineInfo")
    if text:
        m = re.search(r"(?:Brand[:\s]+|Visit the\s+)(.+?)(?:\s+Store|$)", text, re.IGNORECASE)
        if m:
            return _clean_brand(m.group(1))
        if len(text) < 60:
            return _clean_brand(text)

    # 3. Product details table
    try:
        rows = page.locator(
            "#productDetails_techSpec_section_1 tr, "
            "#productDetails_detailBullets_sections1 tr"
        ).all()
        for row in rows:
            t = row.inner_text()
            if re.search(r"\bBrand\b", t, re.IGNORECASE):
                parts = [p.strip() for p in re.split(r"[\t\n]+", t) if p.strip()]
                if len(parts) >= 2:
                    return _clean_brand(parts[-1])
    except Exception:
        pass

    content = _page_html(page)
    if content:
        m = re.search(
            r"<(?:th|span)\b[^>]*>\s*Brand\s*</(?:th|span)>\s*<td\b[^>]*>(.*?)</td>",
            content,
            flags=re.I | re.S,
        )
        if m:
            return _clean_brand(_strip_html(m.group(1)))

        m = re.search(r'"brand"\s*:\s*"([^"]+)"', content, flags=re.I)
        if m:
            try:
                return _clean_brand(m.group(1).encode("utf-8").decode("unicode_escape"))
            except Exception:
                return _clean_brand(m.group(1))

    return ""


def extract_full_title(page) -> str:
    try:
        el = page.locator("span#productTitle").first
        el.wait_for(timeout=5000)
        return el.inner_text().strip()
    except Exception:
        pass

    for selector in ["h1#title span", "#title span"]:
        title = _text(page, selector)
        if title:
            return title

    return _html_id_text(page, "productTitle")


def _price_digits(raw: str) -> str:
    raw = html.unescape(_strip_html(raw or ""))
    raw = re.sub(r"\.\d+", "", raw)
    return re.sub(r"[^0-9]", "", raw)


def _money_digits(raw: str) -> str:
    raw = html.unescape(_strip_html(raw or ""))
    raw = raw.replace("\xa0", " ")
    patterns = [
        r"(?:₹|Rs\.?|INR|â‚¹)\s*([0-9][0-9,]*(?:\.[0-9]{1,2})?)",
        r"([0-9][0-9,]*(?:\.[0-9]{1,2})?)",
    ]
    for pat in patterns:
        m = re.search(pat, raw, flags=re.I)
        if not m:
            continue
        try:
            return str(int(float(m.group(1).replace(",", ""))))
        except Exception:
            pass
    return ""


def _money_candidates(raw: str) -> list:
    raw = html.unescape(_strip_html(raw or "")).replace("\xa0", " ")
    candidates = []
    for m in re.finditer(r"(?:₹|Rs\.?|INR|â‚¹)\s*([0-9][0-9,]*(?:\.[0-9]{1,2})?)", raw, flags=re.I):
        try:
            candidates.append(str(int(float(m.group(1).replace(",", "")))))
        except Exception:
            pass
    if candidates:
        return candidates
    value = _money_digits(raw)
    return [value] if value else []


def _snippets_around(content: str, marker: str, before: int = 250, after: int = 900) -> list:
    snippets = []
    for m in re.finditer(re.escape(marker), content, flags=re.I):
        start = max(0, m.start() - before)
        end = min(len(content), m.end() + after)
        snippets.append(content[start:end])
    return snippets


def _first_valid_price(snippets: list, *, min_value: int = 0, max_value: int = 10000000) -> str:
    for snippet in snippets:
        for value in _money_candidates(snippet):
            try:
                n = int(value)
            except Exception:
                continue
            if min_value < n <= max_value:
                return value
    return ""


def _discount_number(raw: str) -> str:
    m = re.search(r"(\d+)\s*%", raw or "")
    return m.group(1) if m else ""


def _calculated_discount(price: str, mrp: str) -> str:
    try:
        p, r = int(price), int(mrp)
        if r > p > 0:
            return str(round((r - p) / r * 100))
    except Exception:
        pass
    return ""


def _pricing_warnings(row: dict) -> list:
    warnings = []
    price = row.get("raw_price", "")
    mrp = row.get("raw_mrp", "")
    disc = _discount_number(row.get("raw_disc", ""))

    if not price:
        warnings.append("Price missing - verify this product manually")
    if not mrp:
        warnings.append("MRP missing - verify this product manually")

    try:
        if price and mrp and int(price) > int(mrp):
            warnings.append(f"Price greater than MRP ({price} > {mrp}) - verify manually")
    except Exception:
        warnings.append("Price/MRP could not be validated - verify manually")

    calculated = _calculated_discount(price, mrp)
    if disc and calculated:
        try:
            if abs(int(disc) - int(calculated)) > 2:
                warnings.append(
                    f"Discount mismatch - Amazon shows {disc}%, calculated {calculated}%"
                )
        except Exception:
            warnings.append("Discount could not be validated - verify manually")

    return warnings


def _extract_price_mrp_discount_from_html(page) -> dict:
    content = _page_html(page)
    if not content:
        return {}

    data = {"price": "", "mrp": "", "discount": ""}

    price_snippets = []
    for marker in [
        "apex-pricetopay-value",
        "priceToPay",
        "apex-pricetopay-accessibility-label",
        "priceblock_dealprice",
        "priceblock_ourprice",
        "price_inside_buybox",
    ]:
        price_snippets.extend(_snippets_around(content, marker))
    data["price"] = _first_valid_price(price_snippets)

    min_mrp = int(data["price"]) if data["price"] else 0
    for marker in [
        "apex-basisprice-value",
        "M.R.P.",
        "basisPrice",
        "List Price",
        "a-text-price",
    ]:
        data["mrp"] = _first_valid_price(_snippets_around(content, marker), min_value=min_mrp)
        if data["mrp"]:
            break

    m = re.search(r'class="[^"]*savingsPercentage[^"]*"[^>]*>(.*?)</span>', content, flags=re.I | re.S)
    if m:
        d = re.search(r"(\d+)\s*%", _strip_html(m.group(1)))
        if d:
            data["discount"] = d.group(1) + "% off"

    if not data["discount"] and data["price"] and data["mrp"]:
        try:
            p, r = int(data["price"]), int(data["mrp"])
            if r > p:
                data["discount"] = f"{round((r - p) / r * 100)}% off"
        except Exception:
            pass

    return data


def _extract_price_mrp_discount(page) -> dict:
    """
    Single JS pass using the ACTUAL class names Amazon India uses.
    Confirmed from live DOM inspection.
    """
    try:
        result = page.evaluate("""
        () => {
            const clean = el => {
                if (!el) return '';
                const off = el.querySelector('.a-offscreen');
                const raw = ((off && off.textContent.trim()) || el.getAttribute('aria-label') || el.textContent || '');
                // Strip decimal part FIRST (e.g. "₹799.00" → "₹799"), then strip non-digits
                const money = raw.match(/(?:₹|Rs\\.?|INR)\\s*([0-9][0-9,]*(?:[.][0-9]{1,2})?)/i)
                           || raw.match(/([0-9][0-9,]*(?:[.][0-9]{1,2})?)/);
                if (!money) return '';
                return String(parseInt(money[1].replace(/,/g, ''), 10));
            };

            // ── Price: .apex-pricetopay-value  (confirmed class name) ────
            let price = '';
            for (const el of document.querySelectorAll('.apex-pricetopay-value')) {
                const v = clean(el);
                if (v) { price = v; break; }
            }
            // fallbacks
            if (!price) {
                for (const sel of [
                    '#priceblock_dealprice', '#priceblock_ourprice',
                    '#price_inside_buybox', '.priceToPay',
                    '#corePriceDisplay_desktop_feature_div .priceToPay',
                    '#corePriceDisplay_mobile_feature_div .priceToPay',
                    '#apex-pricetopay-accessibility-label'
                ]) {
                    const el = document.querySelector(sel);
                    const v = clean(el);
                    if (v) { price = v; break; }
                }
            }

            // ── MRP: .apex-basisprice-value  (confirmed class name) ──────
            let mrp = '';
            for (const el of document.querySelectorAll('.apex-basisprice-value')) {
                const v = clean(el);
                if (v) { mrp = v; break; }
            }
            // fallbacks
            if (!mrp) {
                for (const sel of [
                    '.basisPrice .a-offscreen',
                    '.basisPrice',
                    '#corePriceDisplay_desktop_feature_div .a-text-price .a-offscreen',
                    '#corePriceDisplay_desktop_feature_div .a-text-price',
                    '#corePriceDisplay_mobile_feature_div .a-text-price',
                    'span.a-price.a-text-price'
                ]) {
                    const el = document.querySelector(sel);
                    if (el) {
                        const v = clean(el);
                        if (v && v !== price && (!price || parseInt(v) > parseInt(price))) { mrp = v; break; }
                    }
                }
            }

            // ── Discount: .savingsPercentage  (confirmed) ────────────────
            let discount = '';
            const discEl = document.querySelector('.savingsPercentage');
            if (discEl) {
                const m = discEl.textContent.match(/(\\d+)\\s*%/);
                if (m) discount = m[1] + '% off';
            }
            if (!discount && price && mrp) {
                const p = parseInt(price), r = parseInt(mrp);
                if (r > p) discount = Math.round((r - p) / r * 100) + '% off';
            }

            return { price, mrp, discount };
        }
        """)
        result = result or {}
        fallback = _extract_price_mrp_discount_from_html(page)
        for key in ("price", "mrp", "discount"):
            if not result.get(key) and fallback.get(key):
                result[key] = fallback[key]
        return result
    except Exception:
        return _extract_price_mrp_discount_from_html(page)


def extract_price(page) -> str:
    return _extract_price_mrp_discount(page).get("price", "")


def extract_mrp(page, price: str = "") -> str:
    data = _extract_price_mrp_discount(page)
    mrp = data.get("mrp", "")
    # Sanity: mrp must be >= price
    try:
        if mrp and price and int(mrp) < int(float(price)):
            return ""
    except Exception:
        pass
    return mrp



def extract_discount(page, price: str, mrp: str) -> str:
    disc = _extract_price_mrp_discount(page).get("discount", "")
    if disc:
        return disc
    # Final fallback: calculate
    try:
        p, r = float(price), float(mrp)
        if r > p > 0:
            return f"{round((r - p) / r * 100)}% off"
    except Exception:
        pass
    return ""


def extract_image_url(page) -> str:
    def clean_url(url: str) -> str:
        return html.unescape((url or "").replace("\\/", "/"))

    def best_dynamic_image(raw: str) -> str:
        if not raw:
            return ""
        try:
            data = json.loads(html.unescape(raw))
            best_url = ""
            best_area = 0
            for url, dims in data.items():
                if not isinstance(dims, list) or len(dims) < 2:
                    continue
                area = int(dims[0]) * int(dims[1])
                if area > best_area:
                    best_area = area
                    best_url = url
            if best_url:
                return best_url
        except Exception:
            pass
        return ""

    def color_image_urls(content: str) -> list:
        starts = [i for i in (content.find("'colorImages'"), content.find('"colorImages"')) if i >= 0]
        if not starts:
            return []
        block = content[min(starts):min(starts) + 60000]
        end_candidates = [i for i in (block.find("'colorToAsin'"), block.find('"colorToAsin"')) if i > 0]
        if end_candidates:
            block = block[:min(end_candidates)]

        main_urls = []
        other_urls = []
        for m in re.finditer(r'\{(?P<obj>.*?"variant"\s*:\s*"(?P<variant>[^"]+)".*?)\}(?=,\s*\{|\s*\])', block, flags=re.S):
            obj = m.group("obj")
            url_match = re.search(r'"hiRes"\s*:\s*"([^"]+)"', obj) or re.search(r'"large"\s*:\s*"([^"]+)"', obj)
            if not url_match:
                continue
            url = clean_url(url_match.group(1))
            if m.group("variant").upper() == "MAIN":
                main_urls.append(url)
            else:
                other_urls.append(url)

        if main_urls or other_urls:
            return main_urls + other_urls

        return [clean_url(m.group(1)) for m in re.finditer(r'"hiRes"\s*:\s*"([^"]+)"', block)]

    content = _page_html(page)

    if content:
        urls = color_image_urls(content)
        if urls:
            return urls[0]

    val = _attr(page, "#landingImage", "data-old-hires")
    if val:
        return val

    if content:
        m = re.search(
            r'<img\b[^>]+\bid=["\']landingImage["\'][^>]+\bdata-old-hires=["\']([^"\']+)',
            content,
            flags=re.I,
        )
        if m:
            return clean_url(m.group(1))

    for sel, attr in [
        ("#landingImage", "data-a-dynamic-image"),
        ("#landingImage", "src"),
        ("#imgBlkFront", "src"),
        ("#imageBlock img", "src"),
    ]:
        val = _attr(page, sel, attr)
        if attr == "data-a-dynamic-image":
            val = best_dynamic_image(val)
        if val:
            return val

    if content:
        for attr in ["data-a-dynamic-image", "src"]:
            m = re.search(
                rf'<img\b[^>]+\bid=["\']landingImage["\'][^>]+\b{attr}=["\']([^"\']+)',
                content,
                flags=re.I,
            )
            if m:
                val = best_dynamic_image(m.group(1)) if attr == "data-a-dynamic-image" else clean_url(m.group(1))
                if val:
                    return val

        m = re.search(r'data-a-dynamic-image="([^"]+)"', content, flags=re.I)
        val = best_dynamic_image(m.group(1) if m else "")
        if val:
            return val

        m = re.search(r'"hiRes"\s*:\s*"([^"]+)"', content)
        if m:
            return clean_url(m.group(1))

    return ""


def extract_product_data(page, url: str = "") -> dict:
    def read_from(src) -> dict:
        full_title = extract_full_title(src)
        brand = extract_brand(src)
        prices = _extract_price_mrp_discount(src)
        raw_price = prices.get("price", "")
        raw_mrp = prices.get("mrp", "")
        raw_disc = prices.get("discount", "")
        image_url = extract_image_url(src)
        return {
            "full_title": full_title,
            "brand": brand,
            "title": shorten_title(full_title, brand),
            "raw_price": raw_price,
            "raw_mrp": raw_mrp,
            "raw_disc": raw_disc,
            "image_url": image_url,
            "source": "browser",
        }

    def bad_pricing(row: dict) -> bool:
        warnings = _pricing_warnings(row)
        return any(
            "Price missing" in warning
            or "MRP missing" in warning
            or "greater than MRP" in warning
            or "Discount mismatch" in warning
            for warning in warnings
        )

    def finalize(row: dict) -> dict:
        try:
            if row.get("raw_price") and row.get("raw_mrp") and int(row["raw_price"]) > int(row["raw_mrp"]):
                row["raw_price"] = ""
                row["raw_mrp"] = ""
                row["raw_disc"] = ""
        except Exception:
            pass
        row["warnings"] = _pricing_warnings(row)
        return row

    data = read_from(page)
    needs_static = bad_pricing(data) or not data.get("full_title") or not data.get("brand") or not data.get("image_url")
    if not needs_static or not url:
        return finalize(data)

    static_page = fetch_static_page(url, page)
    if not static_page:
        return finalize(data)

    fallback = read_from(static_page)
    fallback["source"] = "static"
    fallback_has_valid_price = not bad_pricing(fallback)
    for key, value in fallback.items():
        if not value:
            continue
        if key in ("raw_price", "raw_mrp", "raw_disc") and fallback_has_valid_price and bad_pricing(data):
            data[key] = value
        elif not data.get(key):
            data[key] = value
    if fallback_has_valid_price or any(fallback.get(k) and not data.get(k) for k in ("full_title", "brand", "image_url")):
        data["source"] = "static"

    return finalize(data)


def _estimate_background_rgb(img):
    from PIL import ImageStat

    rgb = img.convert("RGB")
    w, h = rgb.size
    sample = max(8, min(60, w // 12, h // 12))
    corners = [
        rgb.crop((0, 0, sample, sample)),
        rgb.crop((w - sample, 0, w, sample)),
        rgb.crop((0, h - sample, sample, h)),
        rgb.crop((w - sample, h - sample, w, h)),
    ]
    pixels = []
    for corner in corners:
        pixels.extend(corner.resize((8, 8)).getdata())
    return tuple(sorted(channel)[len(channel) // 2] for channel in zip(*pixels))


def _content_bbox(img, tolerance: int = 18):
    from PIL import Image, ImageChops

    rgba = img.convert("RGBA")
    alpha_bbox = rgba.getchannel("A").point(lambda a: 255 if a < 250 else 0).getbbox()
    bg = _estimate_background_rgb(rgba)
    diff = ImageChops.difference(rgba.convert("RGB"), Image.new("RGB", rgba.size, bg))
    mask = diff.convert("L").point(lambda p: 255 if p > tolerance else 0)
    color_bbox = mask.getbbox()
    if alpha_bbox and color_bbox:
        return (
            min(alpha_bbox[0], color_bbox[0]),
            min(alpha_bbox[1], color_bbox[1]),
            max(alpha_bbox[2], color_bbox[2]),
            max(alpha_bbox[3], color_bbox[3]),
        )
    return color_bbox or alpha_bbox


def _pad_bbox(bbox, image_size, padding: int):
    w, h = image_size
    left, top, right, bottom = bbox
    return (
        max(0, left - padding),
        max(0, top - padding),
        min(w, right + padding),
        min(h, bottom + padding),
    )


def normalize_product_image(img, size: int = 1500, fill: float = 0.92):
    """
    Trim Amazon's random white frame and fit the product on a consistent square.
    """
    from PIL import Image

    img = img.convert("RGBA")
    bbox = _content_bbox(img)
    if bbox:
        pad = max(12, round(min(img.size) * 0.015))
        img = img.crop(_pad_bbox(bbox, img.size, pad))

    max_side = max(1, round(size * fill))
    scale = max_side / max(img.width, img.height)
    new_size = (max(1, round(img.width * scale)), max(1, round(img.height * scale)))
    img = img.resize(new_size, Image.LANCZOS)

    canvas = Image.new("RGB", (size, size), (255, 255, 255))
    x = (size - img.width) // 2
    y = (size - img.height) // 2
    canvas.paste(img.convert("RGB"), (x, y), img.getchannel("A"))
    return canvas


def download_image(url: str, dest_no_ext: str, size: int = 1500) -> str:
    """
    Download product image.
    - If already large (min dimension >= 1000 px): save as-is.
    - Otherwise: trim whitespace, fit to size×size on white canvas.
    Saved as JPG.
    """
    try:
        from PIL import Image
        import io

        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req) as resp:
            data = resp.read()

        img = Image.open(io.BytesIO(data))
        final_path = dest_no_ext + ".jpg"
        normalize_product_image(img, size=size).save(final_path, "JPEG", quality=95)
        return final_path

        # Already large enough — save as-is, no processing needed

        # Trim excess whitespace so the product fills the canvas

        # Fit trimmed image inside size×size, centred on white canvas

    except Exception as e:
        print(f"    [!] Image download failed: {e}")
        return ""


# ---------------------------------------------------------------------------
# Pincode / location helper
# ---------------------------------------------------------------------------

def set_pincode(page, pincode: str = "122001") -> bool:
    """
    Set Amazon.in delivery location to the given pincode.
    Strategy 1: POST to Amazon's own AJAX location-change endpoint (most reliable).
    Strategy 2: JS-driven UI interaction as fallback.
    Returns True on success, False otherwise (scraping continues either way).
    """
    try:
        page.goto("https://www.amazon.in", wait_until="domcontentloaded", timeout=20000)
        page.wait_for_timeout(2000)

        # ── Strategy 1: AJAX endpoint ─────────────────────────────────────────
        # This is what Amazon's own frontend calls when you submit the GLUX form.
        status = page.evaluate(f"""
            async () => {{
                try {{
                    const r = await fetch('/gp/delivery/ajax/address-change.html', {{
                        method: 'POST',
                        credentials: 'include',
                        headers: {{
                            'Content-Type': 'application/x-www-form-urlencoded',
                            'X-Requested-With': 'XMLHttpRequest'
                        }},
                        body: 'locationType=LOCATION_INPUT&zipCode={pincode}'
                             + '&storeContext=generic&deviceType=web'
                             + '&pageType=Gateway&actionSource=glow'
                    }});
                    return r.status;
                }} catch(e) {{
                    return -1;
                }}
            }}
        """)

        if status == 200:
            return True

        # ── Strategy 2: JS-driven UI ──────────────────────────────────────────
        # Click the "Deliver to" trigger via JS (avoids visibility/timing issues)
        page.evaluate("""
            () => {
                var t = document.querySelector('#glow-ingress-block')
                     || document.querySelector('#nav-global-location-popover-link');
                if (t) t.click();
            }
        """)
        page.wait_for_timeout(1500)

        # Wait for the GLUX input to appear in the DOM
        try:
            page.wait_for_selector("#GLUXZipUpdateInput", timeout=5000)
        except Exception:
            pass

        # Fill pincode and fire input/change events so Amazon's JS picks it up
        filled = page.evaluate(f"""
            () => {{
                var inp = document.querySelector('#GLUXZipUpdateInput');
                if (!inp) return false;
                inp.value = '{pincode}';
                inp.dispatchEvent(new Event('input',  {{bubbles: true}}));
                inp.dispatchEvent(new Event('change', {{bubbles: true}}));
                return true;
            }}
        """)

        if not filled:
            return False

        page.wait_for_timeout(400)

        # Click Apply button via JS
        page.evaluate("""
            () => {
                var btn = document.querySelector('#GLUXZipUpdate input[type=submit]')
                       || document.querySelector('input.a-button-input[aria-labelledby*="GLUXZip"]')
                       || document.querySelector('.a-popover-content input[type=submit]');
                if (btn) btn.click();
                else document.querySelector('#GLUXZipUpdateInput')?.form?.submit();
            }
        """)
        page.wait_for_timeout(1500)

        # Dismiss "Done" confirmation if it appeared
        page.evaluate("""
            () => {
                var done = document.querySelector('#GLUXConfirmClose input')
                        || document.querySelector('.a-popover-footer input[type=submit]');
                if (done) done.click();
            }
        """)
        page.wait_for_timeout(500)
        return True

    except Exception as e:
        print(f"  [pincode] Could not set pincode ({e}) — continuing without it.")
        return False


# ---------------------------------------------------------------------------
# Main scraping loop
# ---------------------------------------------------------------------------

def scrape_products(urls: list, delay: float, images_folder: str) -> list:
    records = []
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        context = browser.new_context(
            user_agent=(
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36"
            ),
            locale="en-IN",
            viewport={"width": 1280, "height": 800},
        )
        context.add_init_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined});")
        page = context.new_page()

        print("  Setting delivery location to pincode 122001 …")
        set_pincode(page)

        for i, url in enumerate(urls):
            num = i + 1
            print(f"\n[{num}/{len(urls)}]")
            print(f"  Fetching: {url}")
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=30000)
                # Wait for buybox to render (price loads slightly after DOM)
                try:
                    page.wait_for_selector(
                        "#productTitle, #landingImage, #apex_desktop, #buybox, #corePriceDisplay_desktop_feature_div",
                        timeout=6000
                    )
                except Exception:
                    pass
                page.wait_for_timeout(2000)

                if "captcha" in page.url.lower() or page.locator("form[action*='captcha']").count():
                    print("  [!] CAPTCHA detected.")
                    records.append(_empty_record(url, "CAPTCHA"))
                    continue

                data = extract_product_data(page, url)
                if data.get("source") == "static":
                    print("    [i] Used static HTML fallback to complete/validate product data")

                brand       = data["brand"]
                short_title = data["title"]
                raw_price   = data["raw_price"]
                raw_mrp     = data["raw_mrp"]
                raw_disc    = data["raw_disc"]
                image_url   = data["image_url"]
                for warning in data.get("warnings", []):
                    print(f"    [!] {warning}")

                # Download image → images/1.jpg, 2.jpg …
                img_dest  = os.path.join(images_folder, str(num))
                img_path  = download_image(image_url, img_dest) if image_url else ""
                img_file  = os.path.basename(img_path) if img_path else ""

                price    = fmt_price(raw_price)
                mrp      = fmt_price(raw_mrp)
                discount = fmt_discount(raw_disc)
                status   = "OK" if (raw_price or raw_mrp) else "PARTIAL"

                print(f"    Brand   : {brand or '-'}")
                print(f"    Title   : {short_title}")
                print(f"    Price   : {price.replace(chr(8377), 'Rs.') if price else '-'}")
                print(f"    MRP     : {mrp.replace(chr(8377), 'Rs.') if mrp else '-'}")
                print(f"    Discount: {discount or '-'}")
                print(f"    Image   : {img_file or '(not found)'}")

                records.append({
                    "brand":         brand,
                    "title":         short_title,
                    "price":         price,
                    "mrp":           mrp,
                    "discount":      discount,
                    "product_image": img_path.replace("\\", "/"),
                })

            except Exception as exc:
                print(f"  [!] Failed: {exc}")
                records.append(_empty_record(url, "FAILED"))

            if i < len(urls) - 1:
                time.sleep(delay)

        browser.close()
    return records


def _empty_record(url: str, status: str) -> dict:
    return {
        "brand": "", "title": "", "price": "", "mrp": "", "discount": "", "product_image": "",
    }


# ---------------------------------------------------------------------------
# CSV writer
# ---------------------------------------------------------------------------

CSV_FIELDS = ["brand", "title", "price", "mrp", "discount", "product_image"]


def save_csv(records: list, date_folder: str) -> None:
    delete_old_csvs(date_folder)
    path = os.path.join(date_folder, "products.csv")
    with open(path, "w", newline="", encoding="utf-8-sig") as f:  # utf-8-sig → ₹ shows in Excel
        writer = csv.DictWriter(f, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(records)
    print(f"\nSaved {len(records)} record(s) -> {path}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args():
    parser = argparse.ArgumentParser(
        description="Scrape Amazon products for Photoshop variable data.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("urls", nargs="*", help="Amazon product URLs.")
    parser.add_argument("--file", "-f", metavar="FILE", help="Text file with one URL per line.")
    parser.add_argument("--delay", "-d", type=float, default=2.0, help="Delay between requests (default: 2s).")
    return parser.parse_args()


def main():
    args = parse_args()

    # ── Expand tokens: space-separated ASINs, plain ASINs, or .txt file paths ──
    raw_tokens = []
    for item in args.urls:
        # If the token is a .txt file that exists → treat it as a file input
        if item.lower().endswith(".txt") and os.path.exists(item):
            with open(item, encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        raw_tokens.extend(line.split())
        else:
            raw_tokens.extend(item.split())      # "B0AAA B0BBB" → ["B0AAA", "B0BBB"]

    urls = [to_url(t) for t in raw_tokens if t]

    if args.file:
        with open(args.file, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    for t in line.split():
                        urls.append(to_url(t))

    # ── If nothing provided, read ASINs/URLs from stdin (paste + blank line) ──
    if not urls:
        print("Paste ASINs or URLs (one per line), then press Enter twice to start:\n")
        try:
            while True:
                line = input()
                if not line.strip():      # blank line → done
                    break
                for t in line.strip().split():
                    if t and not t.startswith("#"):
                        urls.append(to_url(t))
        except (EOFError, KeyboardInterrupt):
            pass

    if not urls:
        print("No URLs provided. Use --help for usage.")
        sys.exit(1)

    date_folder, images_folder = get_run_folder()
    print(f"Output folder : {date_folder}")
    print(f"\nScraping {len(urls)} product(s)...")

    records = scrape_products(urls, args.delay, images_folder)
    save_csv(records, date_folder)


if __name__ == "__main__" and False:
    # The command-line entry point is retained for reference only. This file is
    # now launched through the combined desktop interface below.
    main()

def run_export_thread(csv_path, psd_path, psd_single, out_folder, naming_mode, log_fn, done_fn, stop_event):
    try:
        log_fn("Importing photoshop-python-api …")
        try:
            import photoshop.api as ps
        except ModuleNotFoundError as exc:
            if exc.name == "photoshop":
                log_fn("  [!] Missing dependency: photoshop-python-api")
                log_fn("  Run setup_dependencies.bat, or run:")
                log_fn("      py -m pip install -r requirements.txt")
                done_fn(False)
                return
            raise
        import csv as csv_mod
        import re

        IMAGE_LAYER   = "product_image"
        CLIP_TO_LAYER = "Rectangle 1"

        _JS_FIND_LAYER = """
        function findLayer(container, name) {
            for (var i = 0; i < container.layers.length; i++) {
                var lyr = container.layers[i];
                if (lyr.name === name) return lyr;
                if (lyr.layers && lyr.layers.length > 0) {
                    var found = findLayer(lyr, name);
                    if (found) return found;
                }
            }
            return null;
        }
        """

        def normalize_export_text(text):
            rupee = chr(8377)
            text = str(text).replace("\ufeff", "").replace("\u200b", "")
            gap = r"[\s\u00a0\u2007\u202f\u200b\u200c\u200d\ufeff]+"
            text = re.sub(rf"{re.escape(rupee)}{gap}(?=\d)", rupee, text)
            text = re.sub(rf"â‚¹{gap}(?=\d)", "â‚¹", text)
            return text

        def set_text(layer_name, text):
            rupee = chr(8377)
            text = re.sub(rf"{re.escape(rupee)}\s+", rupee, str(text))
            text = re.sub(r"â‚¹\s+", "â‚¹", text)
            safe = json.dumps(normalize_export_text(text))
            app.doJavaScript(f"""
            (function(){{
                {_JS_FIND_LAYER}
                var doc = app.activeDocument;
                var lyr = findLayer(doc, "{layer_name}");
                if(lyr && lyr.kind == LayerKind.TEXT) {{
                    var content = {safe};
                    content = content.replace(new RegExp("\\u20b9[\\s\\u00a0\\u2007\\u202f\\u200b\\u200c\\u200d\\ufeff]+(?=\\d)", "g"), "\\u20b9");
                    lyr.textItem.contents = content;
                }}
            }})();
            """)

        def replace_img(image_path):
            fwd = image_path.replace("\\", "/")
            return app.doJavaScript(f"""
            (function(){{
                {_JS_FIND_LAYER}
                var doc = app.activeDocument;
                var clipLyr = findLayer(doc, "Rectangle 1");
                var oldLyr  = findLayer(doc, "product_image");
                var refLyr  = clipLyr || oldLyr;
                if (!refLyr) return "NOT_FOUND";
                var b = refLyr.bounds;
                var tX = b[0].value, tY = b[1].value;
                var tW = Math.round(b[2].value - b[0].value);
                var tH = Math.round(b[3].value - b[1].value);
                if (oldLyr && oldLyr.kind == LayerKind.SMARTOBJECT) {{
                    try {{
                        doc.activeLayer = oldLyr;
                        var d = new ActionDescriptor();
                        d.putPath(charIDToTypeID("null"), new File("{fwd}"));
                        executeAction(stringIDToTypeID("placedLayerReplaceContents"), d, DialogModes.NO);
                        return "OK:smartobj";
                    }} catch(e) {{}}
                }}
                var imgDoc = app.open(new File("{fwd}"));
                imgDoc.resizeImage(UnitValue(tW,"px"), UnitValue(tH,"px"), imgDoc.resolution, ResampleMethod.BICUBIC);
                imgDoc.flatten();
                imgDoc.selection.selectAll();
                imgDoc.selection.copy();
                imgDoc.close(SaveOptions.DONOTSAVECHANGES);
                app.activeDocument = doc;
                if (oldLyr) oldLyr.remove();
                if (clipLyr) doc.activeLayer = clipLyr;
                executeAction(stringIDToTypeID("paste"), new ActionDescriptor(), DialogModes.NO);
                var pasted = doc.activeLayer;
                pasted.name = "product_image";
                var nb = pasted.bounds;
                pasted.translate(tX - nb[0].value, tY - nb[1].value);
                if (clipLyr) pasted.grouped = true;
                return "OK:pixel_paste";
            }})();
            """)

        def export_png(out_path):
            fwd = out_path.replace("\\", "/")
            app.doJavaScript(f"""
            (function(){{
                var doc = app.activeDocument;
                var opts = new ExportOptionsSaveForWeb();
                opts.format  = SaveDocumentType.PNG;
                opts.PNG8    = false;
                opts.quality = 100;
                doc.exportDocument(new File("{fwd}"), ExportType.SAVEFORWEB, opts);
            }})();
            """)

        def revert(doc):
            try: doc.revertToSaved()
            except Exception:
                try: app.doJavaScript(
                    'executeAction(charIDToTypeID("Rvrt"), new ActionDescriptor(), DialogModes.NO);')
                except Exception: pass

        log_fn(f"Reading CSV: {csv_path}")
        with open(csv_path, encoding="utf-8-sig") as f:
            reader = csv_mod.DictReader(f)
            csv_columns = reader.fieldnames or []
            text_columns = [c for c in csv_columns if c and c != IMAGE_LAYER]
            records = list(reader)
        log_fn(f"Found {len(records)} product(s)")
        log_fn("Text columns: " + (", ".join(text_columns) if text_columns else "(none)"))

        os.makedirs(out_folder, exist_ok=True)

        log_fn("Connecting to Photoshop …")
        app = ps.Application()

        # Open both PSDs upfront if single-price PSD is provided
        log_fn(f"Opening PSD: {os.path.basename(psd_path)}")
        doc_full = app.open(os.path.abspath(psd_path))
        time.sleep(2)

        doc_single = None
        if psd_single and os.path.exists(psd_single):
            log_fn(f"Opening single-price PSD: {os.path.basename(psd_single)}")
            doc_single = app.open(os.path.abspath(psd_single))
            time.sleep(2)

        used_paths = set()   # tracks every out_file path used this run

        def pick_doc(row):
            """Return the right doc based on whether MRP/discount are present."""
            has_mrp      = bool(row.get("mrp","").strip())
            has_discount = bool(row.get("discount","").strip())
            if doc_single and not has_mrp and not has_discount:
                return doc_single, "single-price"
            return doc_full, "full"

        for i, row in enumerate(records, start=1):
            if stop_event.is_set():
                log_fn("⏹  Stopped by user."); break

            brand = row.get("brand","").strip()
            title = row.get("title","").strip()

            doc, doc_type = pick_doc(row)
            app.activeDocument = doc
            log_fn(f"[{i}/{len(records)}]  {brand} — {title[:45]}  [{doc_type}]")

            for col in text_columns:
                val = row.get(col,"").strip()
                if val: set_text(col, val)

            time.sleep(0.3)

            img_path = row.get("product_image","").strip()
            if img_path and os.path.exists(img_path):
                r = replace_img(img_path)
                log_fn(f"         image → {r}")
                time.sleep(0.5)
            elif img_path:
                log_fn(f"         [!] image not found: {img_path}")

            if naming_mode == "branded":
                brand_folder = os.path.join(out_folder, _safe_name(brand) if brand else "Unknown Brand")
                os.makedirs(brand_folder, exist_ok=True)
                fname = _safe_name(title) if title else str(i)
                out_file = os.path.join(brand_folder, f"{fname}.png")
                # Avoid overwriting — use in-memory set (don't rely on disk timing)
                counter = 1
                while out_file.lower() in used_paths:
                    out_file = os.path.join(brand_folder, f"{fname} ({counter}).png")
                    counter += 1
                used_paths.add(out_file.lower())
                label = os.path.relpath(out_file, out_folder)
            elif naming_mode == "title_naming":
                name_parts = [part for part in [brand, title] if part]
                fname = _safe_name(" ".join(name_parts)) if name_parts else str(i)
                out_file = os.path.join(out_folder, f"{fname}.png")
                counter = 1
                while out_file.lower() in used_paths:
                    out_file = os.path.join(out_folder, f"{fname} ({counter}).png")
                    counter += 1
                used_paths.add(out_file.lower())
                label = os.path.relpath(out_file, out_folder)
            else:
                out_file = os.path.join(out_folder, f"{i}.png")
                label = f"{i}.png"

            export_png(out_file)
            log_fn(f"         → saved {label} ✓")

            revert(doc)
            time.sleep(1)
            app.activeDocument = doc

        status = "stopped early" if stop_event.is_set() else "complete"
        log_fn(f"\n✅  Done!  [{status}]  PNGs saved to:\n   {out_folder}")
        done_fn(success=True)

    except Exception as exc:
        log_fn(f"\n❌  Error: {exc}")
        done_fn(success=False)


# ─────────────────────────────────────────────────────────────────────────────
# GUI
# ─────────────────────────────────────────────────────────────────────────────


# ---------------------------------------------------------------------------
# Combined desktop launcher
# ---------------------------------------------------------------------------
# This interface deliberately lives in this file so a customer only needs the
# launcher, requirements.txt, and their Photoshop templates - not scraper_ui.py
# or amazon_scraper.py.
import tkinter as tk
from tkinter import filedialog
import threading
import math

APP_BG = "#080b10"
CARD_BG = "#10151d"
CARD_ALT = "#141b25"
FIELD_BG = "#0b1017"
INK = "#e7ecf2"
SUBTLE = "#8491a1"
LINE = "#273341"
AMAZON = "#ad824a"
AMAZON_DARK = "#76552f"
PHOTOSHOP = "#667fa5"
PHOTOSHOP_DARK = "#435674"
GREEN_UI = "#6fa581"
RED_UI = "#d2757d"
AMBER = "#c59b5c"
LOG_BG = "#090d13"
LOG_TEXT = "#c9d3de"
HUD_BG = "#0a0f16"
HUD_LINE = "#263849"
HUD_DIM = "#1a2734"
SAFE_SCRAPE_DELAY = 3.0
SOUND_ENABLED = True
APP_VERSION = "1.2.0"
APP_BUILD_DATE = "2026-09-02"
LICENSE_PUBLIC_KEY_FILE = "license_public_key.pem"
UPDATE_SOURCE_URL = "https://raw.githubusercontent.com/freakyrits/AmzFlow/main/AmzFlow%20Admin/amzflow_admin.py"
NEON_CYAN = "#35e6ff"
NEON_BLUE = "#148eae"
NEON_PURPLE = "#a85cff"
NEON_PINK = "#ff4fc3"
FONT = ("Segoe UI", 10)
FONT_SMALL = ("Segoe UI", 9)
FONT_TITLE = ("Segoe UI Semibold", 16)

try:
    import winsound
except ImportError:
    winsound = None


def play_sfx(style="click"):
    """Small non-blocking UI tones; silently disabled on unsupported systems."""
    if winsound is None or not SOUND_ENABLED:
        return
    tones = {
        "click": [(610, 35), (760, 45)],
        "start": [(420, 55), (560, 55), (720, 80)],
        "stop": [(440, 70), (280, 90)],
        "success": [(560, 50), (720, 50), (880, 90)],
        "error": [(300, 90), (240, 120)],
    }.get(style, [])

    def _play():
        try:
            for frequency, duration in tones:
                winsound.Beep(frequency, duration)
        except RuntimeError:
            pass

    threading.Thread(target=_play, daemon=True).start()


def launcher_config_path():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), ".product_launcher_config.json")


def load_launcher_config():
    try:
        with open(launcher_config_path(), encoding="utf-8") as handle:
            return json.load(handle)
    except Exception:
        return {}


def save_launcher_config(data):
    try:
        with open(launcher_config_path(), "w", encoding="utf-8") as handle:
            json.dump(data, handle, indent=2)
    except Exception:
        pass


def license_state_path():
    appdata = os.environ.get("APPDATA") or os.path.expanduser("~")
    folder = os.path.join(appdata, "AmzFlow")
    os.makedirs(folder, exist_ok=True)
    return os.path.join(folder, "license.json")


def load_license_state():
    try:
        with open(license_state_path(), encoding="utf-8") as handle:
            return json.load(handle)
    except Exception:
        return {}


def save_license_state(data):
    try:
        with open(license_state_path(), "w", encoding="utf-8") as handle:
            json.dump(data, handle, indent=2)
    except Exception:
        pass


def machine_fingerprint():
    """Stable, one-way device id used only to enforce the license device limit."""
    parts = [platform.system(), platform.release(), platform.node(), str(uuid.getnode())]
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\Cryptography") as key:
            parts.append(winreg.QueryValueEx(key, "MachineGuid")[0])
    except Exception:
        pass
    return hashlib.sha256("|".join(parts).encode("utf-8", "ignore")).hexdigest()


def _base64url_decode(value):
    return base64.urlsafe_b64decode(value + "=" * (-len(value) % 4))


def verify_license(license_key):
    """Verify an offline key signed by the seller and locked to this device."""
    public_key_path = os.path.join(BASE_DIR, LICENSE_PUBLIC_KEY_FILE)
    if not os.path.isfile(public_key_path):
        return False, "This copy of AmzFlow has not been configured for manual activation yet. Contact the seller."
    try:
        from cryptography.exceptions import InvalidSignature
        from cryptography.hazmat.primitives import hashes, serialization
        from cryptography.hazmat.primitives.asymmetric import ec

        prefix, payload_part, signature_part = license_key.strip().split(".")
        if prefix != "AMZF1":
            return False, "This is not a valid AmzFlow license key."
        signed_payload = _base64url_decode(payload_part)
        signature = _base64url_decode(signature_part)
        with open(public_key_path, "rb") as handle:
            public_key = serialization.load_pem_public_key(handle.read())
        public_key.verify(signature, signed_payload, ec.ECDSA(hashes.SHA256()))
        payload = json.loads(signed_payload.decode("utf-8"))
        if payload.get("version") != 1 or payload.get("device") != machine_fingerprint():
            return False, "This key belongs to a different computer. Send the device code shown here to the seller."
        for field in ("valid_until", "updates_until"):
            value = payload.get(field)
            if value and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", value):
                return False, "This license key has an invalid expiry date."
        if payload.get("valid_until") and datetime.now().date().isoformat() > payload["valid_until"]:
            return False, "This license has expired. Contact the seller to renew it."
        if payload.get("updates_until") and APP_BUILD_DATE > payload["updates_until"]:
            return False, "This AmzFlow version is outside your update period. Contact the seller for a renewal key."
        return True, "License verified."
    except ValueError:
        return False, "This is not a valid AmzFlow license key."
    except InvalidSignature:
        return False, "This key was not issued by AmzFlow."
    except ModuleNotFoundError:
        return False, "AmzFlow needs its licensing component. Run AmzFlow Setup again."
    except Exception:
        return False, "This key could not be read. Check that it was copied completely."


def scrape_worker_gui(urls, out_folder, delay, log_fn, done_fn, stop_event):
    """Scrape worker with customer-readable progress and explicit price checks."""
    try:
        from playwright.sync_api import sync_playwright

        images_folder = os.path.join(out_folder, "images")
        os.makedirs(images_folder, exist_ok=True)
        records = []
        warning_count = 0

        with sync_playwright() as p:
            log_fn("Preparing browser and Amazon delivery settings...", "info")
            browser = p.chromium.launch(headless=True)
            context = browser.new_context(
                user_agent=("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                            "AppleWebKit/537.36 (KHTML, like Gecko) "
                            "Chrome/124.0.0.0 Safari/537.36"),
                locale="en-IN", viewport={"width": 1280, "height": 800},
            )
            context.add_init_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined});")
            page = context.new_page()
            try:
                if set_pincode(page):
                    log_fn("Delivery location set to pincode 122001.", "success")
                else:
                    log_fn("Delivery location could not be confirmed. Continuing normally.", "warning")
            except Exception as exc:
                log_fn(f"Delivery location step skipped: {exc}", "warning")

            for number, url in enumerate(urls, start=1):
                if stop_event.is_set():
                    log_fn("Scraping stopped by user.", "warning")
                    break

                log_fn(f"Product {number} of {len(urls)}: loading Amazon page...", "heading")
                try:
                    page.goto(url, wait_until="domcontentloaded", timeout=30000)
                    try:
                        page.wait_for_selector(
                            "#productTitle, #landingImage, #apex_desktop, #buybox, #corePriceDisplay_desktop_feature_div",
                            timeout=8000,
                        )
                    except Exception:
                        pass
                    page.wait_for_timeout(2000)

                    if "captcha" in page.url.lower() or page.locator("form[action*='captcha']").count():
                        log_fn("Amazon showed a CAPTCHA. This product was skipped.", "error")
                        records.append({field: "" for field in CSV_FIELDS})
                        continue

                    data = extract_product_data(page, url)
                    if data.get("source") == "static":
                        log_fn("Browser data was incomplete; used Amazon page fallback to verify it.", "info")

                    brand = data.get("brand", "")
                    title = data.get("title", "")
                    raw_price = data.get("raw_price", "")
                    raw_mrp = data.get("raw_mrp", "")
                    raw_disc = data.get("raw_disc", "")
                    image_url = data.get("image_url", "")
                    warnings = data.get("warnings", [])

                    if warnings:
                        warning_count += 1
                        log_fn("PRICE CHECK REQUIRED", "price_error")
                        for warning in warnings:
                            log_fn(f"  {warning}", "price_error")
                    else:
                        log_fn("Price and MRP passed the automatic check.", "success")

                    image_path = ""
                    if image_url:
                        image_path = download_image(image_url, os.path.join(images_folder, str(number)))
                        if image_path:
                            log_fn("Product image downloaded and centered on a white canvas.", "success")
                        else:
                            log_fn("Image could not be downloaded.", "warning")
                    else:
                        log_fn("No main product image was found.", "warning")

                    price = fmt_price(raw_price)
                    mrp = fmt_price(raw_mrp)
                    discount = fmt_discount(raw_disc)
                    log_fn(f"Saved data: {brand or 'Brand unavailable'} | {title or 'Title unavailable'}", "info")
                    log_fn(f"Price: {price or 'Not found'}   MRP: {mrp or 'Not found'}   Discount: {discount or 'Not found'}", "info")

                    records.append({
                        "brand": brand, "title": title, "price": price, "mrp": mrp,
                        "discount": discount, "product_image": image_path.replace("\\", "/"),
                    })
                except Exception as exc:
                    log_fn(f"This product could not be scraped: {exc}", "error")
                    records.append({field: "" for field in CSV_FIELDS})

                if number < len(urls) and not stop_event.is_set():
                    log_fn(f"Waiting {delay:g} second(s) before the next product...", "muted")
                    time.sleep(delay)

            browser.close()

        for filename in os.listdir(out_folder):
            if filename.lower().endswith(".csv"):
                os.remove(os.path.join(out_folder, filename))
        csv_path = os.path.join(out_folder, "products.csv")
        with open(csv_path, "w", newline="", encoding="utf-8-sig") as handle:
            writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
            writer.writeheader()
            writer.writerows(records)

        status = "stopped early" if stop_event.is_set() else "complete"
        summary_tag = "warning" if warning_count else "success"
        log_fn(f"Scraping {status}. Saved {len(records)} product(s) to products.csv.", "success")
        if warning_count:
            log_fn(f"{warning_count} product(s) need a manual price/MRP review before export.", summary_tag)
        done_fn(True)
    except ModuleNotFoundError as exc:
        if exc.name == "playwright":
            log_fn("Browser support is not installed. Run setup_dependencies.bat once, then reopen AmzFlow.", "error")
        else:
            log_fn(f"Scraper could not start or complete: {exc}", "error")
        done_fn(False)
    except Exception as exc:
        log_fn(f"Scraper could not start or complete: {exc}", "error")
        done_fn(False)


class ScrollLog(tk.Frame):
    def __init__(self, parent):
        super().__init__(parent, bg=LOG_BG, highlightthickness=1, highlightbackground=LINE)
        self.text = tk.Text(self, bg=LOG_BG, fg=LOG_TEXT, font=("Consolas", 9),
                            relief="flat", wrap="word", state="disabled", padx=10, pady=8,
                            yscrollcommand=self._set_scroll)
        self.bar = tk.Scrollbar(self, orient="vertical", command=self.text.yview,
                                bg=CARD_ALT, activebackground=LINE, troughcolor=LOG_BG,
                                highlightthickness=0, bd=0)
        self.text.pack(side="left", fill="both", expand=True)
        self.bar.pack(side="right", fill="y")
        self.text.tag_config("success", foreground="#79ad8a")
        self.text.tag_config("error", foreground="#d98288")
        self.text.tag_config("price_error", foreground="#dc7d85", font=("Consolas", 9, "bold"))
        self.text.tag_config("warning", foreground="#c8a464")
        self.text.tag_config("heading", foreground="#8ba0bc", font=("Consolas", 9, "bold"))
        self.text.tag_config("info", foreground=LOG_TEXT)
        self.text.tag_config("muted", foreground="#788695")
        self.text.bind("<MouseWheel>", self._mouse_wheel)

    def _set_scroll(self, first, last):
        self.bar.set(first, last)

    def _mouse_wheel(self, event):
        self.text.yview_scroll(int(-event.delta / 120), "units")
        return "break"

    def write(self, message, tag="info"):
        self.text.configure(state="normal")
        self.text.insert("end", message + "\n", tag)
        self.text.see("end")
        self.text.configure(state="disabled")


class HudHeader(tk.Canvas):
    """Canvas-only animated command deck, deliberately light on system resources."""
    def __init__(self, parent):
        super().__init__(parent, height=260, bg=HUD_BG, bd=0, highlightthickness=0)
        self._frame = 0
        self.mode = "idle"
        self.current = 0
        self.total = 0
        self.result = None
        self.bind("<Configure>", lambda _event: self._draw())
        self._animate()

    def set_activity(self, mode, current=0, total=0):
        self.mode = mode
        self.current = current
        self.total = total
        self.result = None
        self._draw()

    def set_result(self, success):
        self.mode = "idle"
        self.result = success
        self._draw()

    def _draw(self):
        self.delete("all")
        width = max(self.winfo_width(), 1000)
        height = 260
        cyan = "#4c9cb3"
        cyan_dim = "#183a4a"
        glow = "#28677c"
        for x in range(0, width, 32):
            self.create_line(x, 0, x, height, fill="#0e1822")
        for y in range(8, height, 16):
            self.create_line(0, y, width, y, fill="#0e1822")

        scan_y = 20 + (self._frame * 3) % 216
        self.create_line(14, scan_y, width - 14, scan_y, fill="#173949")
        self.create_line(14, scan_y + 1, width - 14, scan_y + 1, fill="#102a37")

        def module_box(x, y, box_w, box_h, accent, title, subtext):
            cut = 12
            points = [x + cut, y, x + box_w - cut, y, x + box_w, y + cut,
                      x + box_w, y + box_h - cut, x + box_w - cut, y + box_h,
                      x + cut, y + box_h, x, y + box_h - cut, x, y + cut]
            self.create_polygon(points, fill="#0d1822", outline="#39566a", width=1)
            self.create_line(x + 10, y + 7, x + 66, y + 7, fill=accent, width=2)
            self.create_text(x + 14, y + 22, anchor="w", text=title, fill="#b7c8d4",
                             font=("Consolas", 10))
            self.create_text(x + 14, y + 41, anchor="w", text=subtext, fill="#657b8d",
                             font=("Consolas", 7))
            for offset, value in enumerate([18, 29, 41, 25, 47, 34]):
                bx = x + 15 + offset * 13
                self.create_line(bx, y + box_h - 18, bx, y + box_h - 18 - value / 3,
                                 fill=accent if offset in (1, 4) else cyan_dim, width=3)
            self.create_line(x + 14, y + box_h - 34, x + box_w - 14, y + box_h - 34, fill="#213a4a")

        left_w = min(270, max(210, width // 5))
        right_w = left_w
        module_box(30, 72, left_w, 122, AMAZON, "Amazon Products", "Links and ASINs")
        module_box(width - right_w - 30, 72, right_w, 122, PHOTOSHOP, "Photoshop Export", "CSV and PSD templates")

        cx, cy = width // 2, 132
        outer = min(78, max(64, width // 17))
        phase = (self._frame * 3) % 360
        activity_color = AMAZON if self.mode == "scrape" else PHOTOSHOP if self.mode == "export" else NEON_CYAN
        activity_text = ""
        if self.mode == "scrape":
            activity_text = f"SCRAPING  {self.current}/{self.total}" if self.total else "SCRAPING"
        elif self.mode == "export":
            activity_text = f"EXPORTING  {self.current}/{self.total}" if self.total else "EXPORTING"
        elif self.result is True:
            activity_text = "DONE"
            activity_color = GREEN_UI
        elif self.result is False:
            activity_text = "CHECK"
            activity_color = RED_UI

        # Layered rings simulate bloom without expensive images or transparency.
        for radius, color, line_w in [(outer + 18, "#0a2533", 5), (outer + 12, "#0e3850", 4),
                                      (outer + 7, "#12516a", 3), (outer + 3, NEON_BLUE, 2),
                                      (outer, NEON_CYAN, 2), (outer - 21, "#15465d", 3),
                                      (outer - 25, "#267f98", 2)]:
            self.create_oval(cx - radius, cy - radius, cx + radius, cy + radius, outline=color, width=line_w)
        for degree in range(0, 360, 6):
            angle = math.radians(degree + phase)
            tick_inner = outer - (10 if degree % 30 == 0 else 5)
            x0 = cx + math.cos(angle) * tick_inner
            y0 = cy + math.sin(angle) * tick_inner
            x1 = cx + math.cos(angle) * (outer + 4)
            y1 = cy + math.sin(angle) * (outer + 4)
            self.create_line(x0, y0, x1, y1, fill=NEON_CYAN if degree % 30 == 0 else cyan_dim,
                             width=2 if degree % 30 == 0 else 1)
        self.create_arc(cx - outer - 8, cy - outer - 8, cx + outer + 8, cy + outer + 8,
                        start=phase if self.mode != "export" else -phase, extent=82, style="arc", outline=activity_color, width=4)
        self.create_arc(cx - outer + 15, cy - outer + 15, cx + outer - 15, cy + outer - 15,
                        start=180 - phase, extent=116, style="arc", outline=NEON_PURPLE if self.mode == "export" else NEON_CYAN, width=3)
        left_edge = 30 + left_w
        right_edge = width - right_w - 30
        if self.mode == "scrape":
            self.create_line(left_edge, cy, cx - outer - 13, cy, fill=AMAZON_DARK, width=1)
            for packet in range(4):
                progress = ((self._frame / 35) + packet / 4) % 1.0
                x = left_edge + (cx - outer - 16 - left_edge) * progress
                y = cy + math.sin((progress * 9) + packet) * 18
                self.create_oval(x - 6, y - 6, x + 6, y + 6, outline="#5b381b")
                self.create_oval(x - 3, y - 3, x + 3, y + 3, fill="#ffb44a", outline="")
        elif self.mode == "export":
            self.create_line(cx + outer + 13, cy, right_edge, cy, fill=PHOTOSHOP_DARK, width=1)
            for packet in range(4):
                progress = ((self._frame / 28) + packet / 4) % 1.0
                x = cx + outer + 16 + (right_edge - (cx + outer + 16)) * progress
                y = cy + math.sin((progress * 9) + packet) * 18
                self.create_rectangle(x - 6, y - 6, x + 6, y + 6, outline="#3e2866")
                self.create_rectangle(x - 3, y - 3, x + 3, y + 3, fill=NEON_PURPLE, outline="")
        self.create_oval(cx - 31, cy - 31, cx + 31, cy + 31, outline="#15546c", width=4)
        self.create_oval(cx - 24, cy - 24, cx + 24, cy + 24, outline=NEON_CYAN, width=2)
        self.create_oval(cx - 15, cy - 15, cx + 15, cy + 15, fill="#0a1a25", outline="#27758d", width=2)
        self.create_oval(cx - 8, cy - 8, cx + 8, cy + 8, outline="#276a81", width=3)
        self.create_oval(cx - 3, cy - 3, cx + 3, cy + 3, fill="#c2f8ff", outline="")
        status = activity_text or "READY"
        self.create_text(cx, 224, text=status, fill=activity_color if activity_text else "#8caab9",
                         font=("Consolas", 9, "bold"))

        self.create_text(30, 24, anchor="w", text="AMZFLOW", fill=INK,
                         font=("Segoe UI Semibold", 18))
        self.create_text(31, 47, anchor="w", text="Amazon to Photoshop", fill=SUBTLE,
                         font=("Consolas", 9))
        self.create_line(30, 55, width - 30, 55, fill="#2b4354")
        self.create_line(30, 238, width - 30, 238, fill="#2b4354")
        for x in range(30, width - 30, 18):
            active = (x // 18 + self._frame // 3) % 7 == 0
            self.create_rectangle(x, 246, x + 11, 249, fill=activity_color if active else "#203846", outline="")

        corners = [(14, 14, 1, 1), (width - 14, 14, -1, 1), (14, height - 14, 1, -1), (width - 14, height - 14, -1, -1)]
        for x, y, dx, dy in corners:
            self.create_line(x, y, x + dx * 20, y, fill="#6f8ca0", width=2)
            self.create_line(x, y, x, y + dy * 15, fill="#6f8ca0", width=2)

    def _animate(self):
        self._frame += 1
        self._draw()
        self.after(90, self._animate)


class HudShell(tk.Frame):
    """Cut-corner panel housing a normal frame so controls remain reliable."""
    def __init__(self, parent, accent):
        super().__init__(parent, bg=APP_BG)
        self.accent = accent
        self.canvas = tk.Canvas(self, bg=APP_BG, bd=0, highlightthickness=0)
        self.canvas.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.content = tk.Frame(self, bg=CARD_BG)
        self.content.place(relx=0.026, rely=0.024, relwidth=0.948, relheight=0.952)
        self.bind("<Configure>", self._resize)

    def _resize(self, _event=None):
        self.canvas.delete("all")
        width, height = max(self.winfo_width(), 120), max(self.winfo_height(), 120)
        cut = 24
        points = [cut, 0, width - cut, 0, width, cut, width, height - cut,
                  width - cut, height, cut, height, 0, height - cut, 0, cut]
        self.canvas.create_polygon(points, fill="#0d141d", outline=self.accent, width=1)
        self.canvas.create_line(cut + 12, 6, width // 2 - 50, 6, fill=HUD_LINE)
        self.canvas.create_line(width // 2 + 50, 6, width - cut - 12, 6, fill=HUD_LINE)
        self.canvas.create_line(7, cut + 10, 7, height // 2 - 35, fill=HUD_LINE)
        self.canvas.create_line(width - 7, height // 2 + 35, width - 7, height - cut - 10, fill=HUD_LINE)
        self.canvas.create_line(18, 1, 45, 1, fill=self.accent, width=2)
        self.canvas.create_line(width - 45, height - 1, width - 18, height - 1, fill=self.accent, width=2)


class SoundControl(tk.Frame):
    """Compact icon-only volume control for the HUD."""
    def __init__(self, parent, variable):
        super().__init__(parent, bg=HUD_BG)
        self.variable = variable
        self._speaker(self, muted=True).pack(side="left", padx=(0, 4))
        tk.Scale(self, from_=0, to=1, orient="horizontal", showvalue=0, variable=variable,
                 length=42, width=7, sliderlength=10, bd=0, highlightthickness=0,
                 troughcolor="#263b4a", bg=HUD_BG, fg="#88a5b7", activebackground="#88a5b7").pack(side="left")
        self._speaker(self, muted=False).pack(side="left", padx=(4, 0))

    def _speaker(self, parent, muted):
        icon = tk.Canvas(parent, width=17, height=17, bg=HUD_BG, bd=0, highlightthickness=0)
        icon.create_polygon(2, 7, 6, 7, 11, 3, 11, 14, 6, 10, 2, 10, fill="#8ca7b7", outline="")
        if muted:
            icon.create_line(12, 5, 16, 12, fill="#8ca7b7", width=1)
            icon.create_line(16, 5, 12, 12, fill="#8ca7b7", width=1)
        else:
            icon.create_arc(8, 3, 17, 14, start=-55, extent=110, style="arc", outline="#8ca7b7")
        return icon


class ActivationWindow(tk.Tk):
    """Manual, device-bound activation gate shown before the workspace."""
    def __init__(self):
        super().__init__()
        self.licensed = False
        self.title("Activate AmzFlow")
        self.configure(bg=APP_BG)
        self.resizable(False, False)
        self.geometry("560x420")
        self.eval("tk::PlaceWindow . center")
        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.key_var = tk.StringVar(value=load_license_state().get("license_key", ""))
        self.device_code = machine_fingerprint()
        self.status_var = tk.StringVar(value="Send your device code to the seller, then paste the key you receive.")
        self._build()
        if self.key_var.get().strip():
            self.after(150, self._activate)

    def _build(self):
        shell = HudShell(self, NEON_CYAN)
        shell.pack(fill="both", expand=True, padx=18, pady=18)
        content = shell.content
        content.grid_columnconfigure(0, weight=1)

        tk.Label(content, text="AMZFLOW", font=("Segoe UI Semibold", 20), bg=CARD_BG, fg=NEON_CYAN).grid(
            row=0, column=0, sticky="w", padx=24, pady=(26, 2)
        )
        tk.Label(content, text="Activate this device", font=("Segoe UI", 11), bg=CARD_BG, fg=INK).grid(
            row=1, column=0, sticky="w", padx=24
        )
        tk.Label(content, text="Your key is issued for this computer and works offline after activation.",
                 font=FONT_SMALL, bg=CARD_BG, fg=SUBTLE, wraplength=470, justify="left").grid(
            row=2, column=0, sticky="w", padx=24, pady=(5, 14)
        )
        tk.Label(content, text="DEVICE CODE", font=("Consolas", 9), bg=CARD_BG, fg=NEON_PURPLE).grid(
            row=3, column=0, sticky="w", padx=24, pady=(0, 4)
        )
        device_line = tk.Frame(content, bg=CARD_BG)
        device_line.grid(row=4, column=0, sticky="ew", padx=24)
        device_line.grid_columnconfigure(0, weight=1)
        device_entry = tk.Entry(device_line, font=("Consolas", 8), bg=FIELD_BG, fg=SUBTLE,
                                readonlybackground=FIELD_BG, relief="solid", bd=1, highlightthickness=1,
                                highlightbackground=LINE)
        device_entry.grid(row=0, column=0, sticky="ew", ipady=6)
        device_entry.insert(0, self.device_code)
        device_entry.config(state="readonly")
        tk.Button(device_line, text="Copy", font=FONT_SMALL, bg=CARD_ALT, fg=INK, activebackground=LINE,
                  activeforeground=INK, relief="flat", padx=10, pady=5, command=self._copy_device_code).grid(
            row=0, column=1, padx=(6, 0)
        )
        tk.Label(content, text="LICENSE KEY", font=("Consolas", 9), bg=CARD_BG, fg=NEON_PURPLE).grid(
            row=5, column=0, sticky="w", padx=24, pady=(14, 4)
        )
        self.key_entry = tk.Entry(content, textvariable=self.key_var, font=("Consolas", 10), bg=FIELD_BG, fg=INK,
                                  insertbackground=INK, relief="solid", bd=1, highlightthickness=1,
                                  highlightbackground=LINE, highlightcolor=NEON_CYAN)
        self.key_entry.grid(row=6, column=0, sticky="ew", padx=24, ipady=8)
        self.key_entry.focus_set()
        self.key_entry.bind("<Return>", lambda _event: self._activate())

        self.status = tk.Label(content, textvariable=self.status_var, font=FONT_SMALL, bg=CARD_BG, fg=SUBTLE,
                               wraplength=470, justify="left")
        self.status.grid(row=7, column=0, sticky="w", padx=24, pady=(12, 12))
        actions = tk.Frame(content, bg=CARD_BG)
        actions.grid(row=8, column=0, sticky="ew", padx=24, pady=(0, 24))
        self.activate_button = tk.Button(actions, text="Activate", font=("Segoe UI Semibold", 10), bg=NEON_BLUE,
                                         fg="#071219", activebackground=NEON_CYAN, activeforeground="#071219",
                                         relief="flat", padx=20, pady=7, command=self._activate)
        self.activate_button.pack(side="left")
        tk.Button(actions, text="Exit", font=FONT_SMALL, bg=CARD_ALT, fg=INK, activebackground=LINE,
                  activeforeground=INK, relief="flat", padx=14, pady=7, command=self.destroy).pack(side="left", padx=8)

    def _copy_device_code(self):
        self.clipboard_clear()
        self.clipboard_append(self.device_code)
        self.status_var.set("Device code copied. Send it to the seller to receive your key.")
        self.status.config(fg=NEON_CYAN)

    def _activate(self):
        key = self.key_var.get().strip().upper()
        if not key:
            self.status_var.set("Enter the license key you received after purchase.")
            self.status.config(fg=RED_UI)
            return
        self.activate_button.config(state="disabled")
        self.status_var.set("Checking your manual license key...")
        self.status.config(fg=NEON_CYAN)
        threading.Thread(target=self._verify_worker, args=(key,), daemon=True).start()

    def _verify_worker(self, key):
        ok, message = verify_license(key)
        self.after(0, lambda: self._finish_activation(ok, message, key))

    def _finish_activation(self, ok, message, key):
        if ok:
            save_license_state({"license_key": key, "last_verified": datetime.now().isoformat(timespec="seconds")})
            self.licensed = True
            self.status_var.set("Activated. Opening AmzFlow...")
            self.status.config(fg=GREEN_UI)
            self.after(450, self.destroy)
            return
        self.status_var.set(message)
        self.status.config(fg=RED_UI)
        self.activate_button.config(state="normal")


def run_activation_gate():
    gate = ActivationWindow()
    gate.mainloop()
    return gate.licensed


class ProductLauncher(tk.Tk):
    def __init__(self):
        global SOUND_ENABLED
        super().__init__()
        self.title("AmzFlow - Amazon Product Graphics Automation")
        self.configure(bg=APP_BG)
        self.minsize(1080, 760)
        self.geometry("1420x920")
        self.scrape_stop = threading.Event()
        self.export_stop = threading.Event()
        self.cfg = load_launcher_config()
        self.sound_enabled = tk.IntVar(value=int(self.cfg.get("sound_enabled", 1)))
        SOUND_ENABLED = bool(self.sound_enabled.get())
        self.sound_enabled.trace_add("write", self._on_sound_change)
        self._build()

    def _build(self):
        header = tk.Frame(self, bg=HUD_BG, height=260)
        header.pack(fill="x")
        header.pack_propagate(False)
        self.hud = HudHeader(header)
        self.hud.pack(fill="both", expand=True)
        SoundControl(header, self.sound_enabled).place(relx=0.87, y=12)

        pane = tk.PanedWindow(self, orient="horizontal", sashwidth=8, sashrelief="flat", bg=APP_BG, bd=0)
        pane.pack(fill="both", expand=True, padx=16, pady=16)
        self.scrape_panel = self._panel(pane, "Amazon Scraper", "Paste Amazon links or ASINs. Saves a CSV and product images.", AMAZON)
        self.export_panel = self._panel(pane, "Photoshop Exporter", "Use a CSV and PSD templates to create PNG graphics.", PHOTOSHOP)
        pane.add(self.scrape_panel, minsize=490)
        pane.add(self.export_panel, minsize=490)
        self._build_scraper(self.scrape_panel.content)
        self._build_exporter(self.export_panel.content)

    def _panel(self, parent, title, description, accent):
        outer = HudShell(parent, accent)
        content = outer.content
        content.grid_columnconfigure(0, weight=1)
        content.grid_rowconfigure(3, weight=1)
        top = tk.Frame(content, bg=CARD_BG)
        top.grid(row=0, column=0, sticky="ew", padx=18, pady=(16, 6))
        tk.Label(top, text=title, font=("Segoe UI Semibold", 13), bg=CARD_BG, fg=accent).pack(anchor="w")
        tk.Label(top, text=description, font=FONT_SMALL, bg=CARD_BG, fg=SUBTLE, justify="left", wraplength=520).pack(anchor="w", pady=(2, 0))
        tk.Frame(top, height=1, bg=accent).pack(fill="x", pady=(10, 0))
        return outer

    def _field(self, parent, row, label, variable, browse, filetypes=None):
        tk.Label(parent, text=label, font=FONT_SMALL, bg=CARD_BG, fg=INK).grid(row=row, column=0, sticky="w", pady=(8, 3))
        line = tk.Frame(parent, bg=CARD_BG)
        line.grid(row=row + 1, column=0, sticky="ew", pady=(0, 4))
        line.grid_columnconfigure(0, weight=1)
        tk.Entry(line, textvariable=variable, font=FONT_SMALL, bg=FIELD_BG, fg=INK,
                 insertbackground=INK, relief="solid", bd=1, highlightthickness=1,
                 highlightbackground=LINE, highlightcolor=SUBTLE).grid(row=0, column=0, sticky="ew", ipady=5)
        tk.Button(line, text="Browse", font=FONT_SMALL, bg=CARD_ALT, fg=INK, activebackground=LINE,
                  activeforeground=INK, relief="flat", padx=10, command=browse).grid(row=0, column=1, padx=(6, 0), ipady=3)

    def _build_scraper(self, panel):
        body = tk.Frame(panel, bg=CARD_BG)
        body.grid(row=1, column=0, sticky="nsew", padx=18)
        body.grid_columnconfigure(0, weight=1)
        tk.Label(body, text="Amazon links or ASINs", font=FONT_SMALL, bg=CARD_BG, fg=INK).grid(row=0, column=0, sticky="w")
        self.targets = tk.Text(body, height=7, font=FONT_SMALL, bg=FIELD_BG, fg=INK, insertbackground=INK,
                               relief="solid", bd=1, highlightthickness=1, highlightbackground=LINE,
                               highlightcolor=AMAZON, wrap="word", padx=7, pady=6)
        self.targets.grid(row=1, column=0, sticky="ew", pady=(3, 5))
        self.targets.insert("1.0", self.cfg.get("targets", ""))
        tk.Label(body, text="One per line or space-separated. You can paste full Amazon links or 10-character ASINs.",
                 font=FONT_SMALL, bg=CARD_BG, fg=SUBTLE).grid(row=2, column=0, sticky="w")
        self.scrape_out = tk.StringVar(value=self.cfg.get("scrape_out", ""))
        self._field(body, 3, "Save CSV and images to", self.scrape_out, self._browse_scrape_out)
        delay_row = tk.Frame(body, bg=CARD_BG)
        delay_row.grid(row=5, column=0, sticky="w", pady=(6, 5))
        tk.Label(delay_row, text="SAFETY INTERVAL", font=("Consolas", 8), bg=CARD_BG, fg=AMAZON).pack(side="left")
        tk.Label(delay_row, text="3 seconds between products", font=FONT_SMALL, bg=CARD_ALT, fg=INK,
                 padx=10, pady=4).pack(side="left", padx=8)
        tk.Label(delay_row, text="Fixed for reliable Amazon data.", font=FONT_SMALL, bg=CARD_BG, fg=SUBTLE).pack(side="left")
        actions = tk.Frame(body, bg=CARD_BG)
        actions.grid(row=6, column=0, sticky="ew", pady=(5, 10))
        self.scrape_start = tk.Button(actions, text="Start Scraping", font=("Segoe UI Semibold", 10), bg=AMAZON_DARK, fg=INK, activebackground=AMAZON, activeforeground="#12171d", relief="flat", padx=14, pady=7, command=self._start_scrape)
        self.scrape_start.pack(side="left")
        self.scrape_abort = tk.Button(actions, text="Stop", font=("Segoe UI Semibold", 10), bg="#302027", fg=RED_UI, activebackground="#482831", activeforeground=RED_UI, relief="flat", padx=12, pady=7, state="disabled", command=self._stop_scrape)
        self.scrape_abort.pack(side="left", padx=7)
        self.scrape_status = tk.Label(actions, text="Ready", font=FONT_SMALL, bg=CARD_BG, fg=SUBTLE)
        self.scrape_status.pack(side="left", padx=6)
        log_label = tk.Label(panel, text="Amazon scraping progress", font=FONT_SMALL, bg=CARD_BG, fg=INK)
        log_label.grid(row=2, column=0, sticky="w", padx=18, pady=(0, 3))
        self.scrape_log = ScrollLog(panel)
        self.scrape_log.grid(row=3, column=0, sticky="nsew", padx=18, pady=(0, 18))
        self.scrape_log.write("Ready. Paste products, choose a folder, then start scraping.", "muted")

    def _build_exporter(self, panel):
        body = tk.Frame(panel, bg=CARD_BG)
        body.grid(row=1, column=0, sticky="nsew", padx=18)
        body.grid_columnconfigure(0, weight=1)
        self.csv_path = tk.StringVar(value=self.cfg.get("csv_path", ""))
        self.full_psd = tk.StringVar(value=self.cfg.get("full_psd", ""))
        self.single_psd = tk.StringVar(value=self.cfg.get("single_psd", ""))
        self.export_out = tk.StringVar(value=self.cfg.get("export_out", ""))
        self.export_mode = tk.StringVar(value=self.cfg.get("export_mode", "sequence"))
        self._field(body, 0, "Products CSV", self.csv_path, self._browse_csv)
        self._field(body, 2, "Full PSD template (price, MRP and discount)", self.full_psd, self._browse_full_psd)
        self._field(body, 4, "Single-price PSD template (optional)", self.single_psd, self._browse_single_psd)
        self._field(body, 6, "Save PNG files to", self.export_out, self._browse_export_out)
        tk.Label(body, text="Export naming", font=FONT_SMALL, bg=CARD_BG, fg=INK).grid(row=8, column=0, sticky="w", pady=(7, 3))
        modes = tk.Frame(body, bg=CARD_BG)
        modes.grid(row=9, column=0, sticky="w", pady=(0, 5))
        for label, value in [("Sequence (1.png)", "sequence"), ("Brand Folders", "branded"), ("Brand+Title", "title_naming")]:
            tk.Radiobutton(modes, text=label, variable=self.export_mode, value=value, font=FONT_SMALL,
                           bg=CARD_BG, fg=INK, activebackground=CARD_BG, activeforeground=INK,
                           selectcolor=CARD_ALT).pack(side="left", padx=(0, 10))
        actions = tk.Frame(body, bg=CARD_BG)
        actions.grid(row=10, column=0, sticky="ew", pady=(4, 10))
        self.export_start = tk.Button(actions, text="Start Export", font=("Segoe UI Semibold", 10), bg=PHOTOSHOP_DARK, fg=INK, activebackground=PHOTOSHOP, activeforeground="#10151d", relief="flat", padx=14, pady=7, command=self._start_export)
        self.export_start.pack(side="left")
        self.export_abort = tk.Button(actions, text="Stop", font=("Segoe UI Semibold", 10), bg="#302027", fg=RED_UI, activebackground="#482831", activeforeground=RED_UI, relief="flat", padx=12, pady=7, state="disabled", command=self._stop_export)
        self.export_abort.pack(side="left", padx=7)
        self.export_status = tk.Label(actions, text="Ready", font=FONT_SMALL, bg=CARD_BG, fg=SUBTLE)
        self.export_status.pack(side="left", padx=6)
        log_label = tk.Label(panel, text="Photoshop export progress", font=FONT_SMALL, bg=CARD_BG, fg=INK)
        log_label.grid(row=2, column=0, sticky="w", padx=18, pady=(0, 3))
        self.export_log = ScrollLog(panel)
        self.export_log.grid(row=3, column=0, sticky="nsew", padx=18, pady=(0, 18))
        self.export_log.write("Ready. Select a CSV, PSD template and destination folder to export PNGs.", "muted")

    def _browse_scrape_out(self):
        path = filedialog.askdirectory(title="Choose where to save the CSV and images")
        if path:
            self.scrape_out.set(path)
            play_sfx("click")

    def _browse_csv(self):
        path = filedialog.askopenfilename(title="Choose products CSV", filetypes=[("CSV files", "*.csv"), ("All files", "*.*")])
        if path:
            self.csv_path.set(path)
            play_sfx("click")

    def _browse_full_psd(self):
        path = filedialog.askopenfilename(title="Choose full PSD template", filetypes=[("Photoshop files", "*.psd *.psb"), ("All files", "*.*")])
        if path:
            self.full_psd.set(path)
            play_sfx("click")

    def _browse_single_psd(self):
        path = filedialog.askopenfilename(title="Choose single-price PSD template", filetypes=[("Photoshop files", "*.psd *.psb"), ("All files", "*.*")])
        if path:
            self.single_psd.set(path)
            play_sfx("click")

    def _browse_export_out(self):
        path = filedialog.askdirectory(title="Choose PNG export folder")
        if path:
            self.export_out.set(path)
            play_sfx("click")

    def _target_urls(self):
        values = []
        for line in self.targets.get("1.0", "end").splitlines():
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            values.extend(to_url(token) for token in line.split())
        return values

    def _save_settings(self):
        save_launcher_config({
            "targets": self.targets.get("1.0", "end").strip(), "scrape_out": self.scrape_out.get().strip(),
            "scrape_delay": SAFE_SCRAPE_DELAY, "csv_path": self.csv_path.get().strip(),
            "full_psd": self.full_psd.get().strip(), "single_psd": self.single_psd.get().strip(),
            "export_out": self.export_out.get().strip(), "export_mode": self.export_mode.get(),
            "sound_enabled": self.sound_enabled.get(),
        })

    def _on_sound_change(self, *_):
        global SOUND_ENABLED
        SOUND_ENABLED = bool(self.sound_enabled.get())
        config = load_launcher_config()
        config["sound_enabled"] = self.sound_enabled.get()
        save_launcher_config(config)

    def _start_scrape(self):
        urls, out_folder = self._target_urls(), self.scrape_out.get().strip()
        if not urls:
            self.scrape_log.write("Add at least one Amazon link or ASIN before starting.", "error")
            play_sfx("error")
            return
        if not out_folder:
            self.scrape_log.write("Choose a folder for the CSV and images before starting.", "error")
            play_sfx("error")
            return
        self._save_settings()
        self.scrape_stop.clear()
        self.scrape_start.config(state="disabled")
        self.scrape_abort.config(state="normal")
        self.scrape_status.config(text=f"Working on {len(urls)} product(s)...", fg=AMAZON)
        self.scrape_log.write(f"Starting scrape for {len(urls)} product(s).", "heading")
        self.hud.set_activity("scrape", 0, len(urls))
        play_sfx("start")
        threading.Thread(target=scrape_worker_gui, args=(urls, out_folder, SAFE_SCRAPE_DELAY, self._scrape_log_thread, self._finish_scrape, self.scrape_stop), daemon=True).start()

    def _scrape_log_thread(self, message, tag="info"):
        match = re.search(r"Product\s+(\d+)\s+of\s+(\d+)", message)
        def _update():
            self.scrape_log.write(message, tag)
            if match:
                self.hud.set_activity("scrape", int(match.group(1)), int(match.group(2)))
        self.after(0, _update)

    def _finish_scrape(self, success):
        self.after(0, lambda: self._set_scrape_done(success))

    def _set_scrape_done(self, success):
        self.scrape_start.config(state="normal")
        self.scrape_abort.config(state="disabled")
        self.scrape_status.config(text="Complete" if success else "Could not complete", fg=GREEN_UI if success else RED_UI)
        self.hud.set_result(success)
        play_sfx("success" if success else "error")

    def _stop_scrape(self):
        self.scrape_stop.set()
        self.scrape_status.config(text="Stopping after this product...", fg=AMBER)
        self.scrape_abort.config(state="disabled")
        self.hud.set_activity("idle")
        play_sfx("stop")

    def _start_export(self):
        csv_path, full_psd, single_psd, out_folder = (self.csv_path.get().strip(), self.full_psd.get().strip(), self.single_psd.get().strip(), self.export_out.get().strip())
        errors = []
        if not os.path.isfile(csv_path): errors.append("Choose a valid products CSV.")
        if not os.path.isfile(full_psd): errors.append("Choose a valid full PSD template.")
        if single_psd and not os.path.isfile(single_psd): errors.append("The optional single-price PSD path is not valid.")
        if not out_folder: errors.append("Choose a PNG destination folder.")
        if errors:
            for error in errors: self.export_log.write(error, "error")
            play_sfx("error")
            return
        self._save_settings()
        self.export_stop.clear()
        self.export_start.config(state="disabled")
        self.export_abort.config(state="normal")
        self.export_status.config(text="Exporting PNGs...", fg=PHOTOSHOP)
        self.export_log.write("Starting Photoshop export...", "heading")
        self.hud.set_activity("export")
        play_sfx("start")
        mode = {"sequence": "normal", "branded": "branded", "title_naming": "title_naming"}[self.export_mode.get()]
        threading.Thread(target=run_export_thread, args=(csv_path, full_psd, single_psd, out_folder, mode, self._export_log_thread, self._finish_export, self.export_stop), daemon=True).start()

    def _export_log_thread(self, message):
        lower = message.lower()
        tag = "error" if any(word in lower for word in ["[!]", "error", "missing", "not found", "could not"]) else "success" if any(word in lower for word in ["done", "saved", "ok:", "✓"]) else "info"
        match = re.search(r"\[(\d+)/(\d+)\]", message)
        def _update():
            self.export_log.write(message, tag)
            if match:
                self.hud.set_activity("export", int(match.group(1)), int(match.group(2)))
        self.after(0, _update)

    def _finish_export(self, success):
        self.after(0, lambda: self._set_export_done(success))

    def _set_export_done(self, success):
        self.export_start.config(state="normal")
        self.export_abort.config(state="disabled")
        self.export_status.config(text="Complete" if success else "Could not complete", fg=GREEN_UI if success else RED_UI)
        self.hud.set_result(success)
        play_sfx("success" if success else "error")
        if success:
            try:
                os.startfile(self.export_out.get().strip())
                self.export_log.write("Opened the PNG destination folder.", "success")
            except Exception:
                pass

    def _stop_export(self):
        self.export_stop.set()
        self.export_status.config(text="Stopping after this file...", fg=AMBER)
        self.export_abort.config(state="disabled")
        self.hud.set_activity("idle")
        play_sfx("stop")


def version_parts(value):
    """Turn a simple dotted release number into a comparable tuple."""
    return tuple(int(part) for part in value.split(".") if part.isdigit())


def install_available_update():
    """Replace this launcher with a newer public GitHub version, if one exists."""
    try:
        request = urllib.request.Request(UPDATE_SOURCE_URL, headers={"User-Agent": "AmzFlow-Admin-Updater"})
        with urllib.request.urlopen(request, timeout=4) as response:
            remote_source = response.read(1_500_000).decode("utf-8")
        match = re.search(r'^APP_VERSION\\s*=\\s*"([0-9.]+)"', remote_source, re.MULTILINE)
        if not match or version_parts(match.group(1)) <= version_parts(APP_VERSION):
            return False
        if "class ProductLauncher" not in remote_source:
            return False
        app_path = os.path.abspath(__file__)
        staged_path = f"{app_path}.update"
        with open(staged_path, "w", encoding="utf-8", newline="") as handle:
            handle.write(remote_source)
        os.replace(staged_path, app_path)
        creation_flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        subprocess.Popen([sys.executable, app_path], creationflags=creation_flags)
        return True
    except Exception:
        return False


if __name__ == "__main__":
    # The separately stored seller/admin copy intentionally opens directly.
    if install_available_update():
        raise SystemExit
    ProductLauncher().mainloop()

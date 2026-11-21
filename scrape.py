#!/usr/bin/env python3
"""
Tripura Job Alert - scraper (Step 2).

  python scraper/scrape.py --mode selftest            offline check of the parsers
  python scraper/scrape.py --mode dry-run --group all scrape, print results, save nothing
  python scraper/scrape.py --mode real --group all    scrape and save data/*.json
"""
import argparse
import hashlib
import io
import json
import os
import re
import sys
import time
import traceback
import urllib.robotparser
from datetime import date, datetime, timedelta, timezone
from urllib.parse import urljoin, urlparse

import feedparser
import requests
import yaml
from bs4 import BeautifulSoup
from dateutil import parser as dateparser
from pypdf import PdfReader

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "data")
JOBS_FILE = os.path.join(DATA, "jobs.json")
HEALTH_FILE = os.path.join(DATA, "health.json")
STATE_FILE = os.path.join(DATA, "state.json")
SAMPLE_FILE = os.path.join(DATA, "sample_jobs.json")

IST = timezone(timedelta(hours=5, minutes=30))
NOW = datetime.now(IST)
TODAY = NOW.date()
NOW_ISO = NOW.isoformat(timespec="seconds")

UPDATE_KINDS = ("admit_card", "result", "corrigendum", "extension")
KIND_ORDER = {"recruitment": 0, "corrigendum": 1, "extension": 1, "admit_card": 2, "result": 2}
EMPTY = (None, "", [], "not_found")
FILL_FIELDS = ("post", "vacancies", "qualification", "levels", "min_qualification",
               "stream_req", "age_limit", "age_min", "age_max", "age_cutoff",
               "age_relaxation", "pay", "start_date", "last_date",
               "notification_url", "page_url")


class FetchError(Exception):
    pass


class RobotsBlocked(Exception):
    pass


class RobotsUnavailable(Exception):
    pass


class EmptyResult(Exception):
    pass


# ----------------------------------------------------------------- small helpers

def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def save_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def load_yaml(name):
    with open(os.path.join(ROOT, name), encoding="utf-8") as f:
        return yaml.safe_load(f)


def norm(text):
    return re.sub(r"\s+", " ", text or "").strip()


def norm_words(text):
    return re.sub(r"[^a-z0-9]+", " ", (text or "").lower()).strip()


def short(text, n=110):
    text = norm(text)
    return text if len(text) <= n else text[: n - 1] + "…"


def hours_since(iso):
    if not iso:
        return 999
    try:
        return (NOW - datetime.fromisoformat(iso)).total_seconds() / 3600
    except ValueError:
        return 999


# ----------------------------------------------------------------- classification

EXCLUDE_RE = re.compile(
    r"tender|quotation|auction|training calendar|die[- ]?in[- ]?harness|compassionate|"
    r"annual report|\brti\b|vehicle|procurement|store articles|roof treatment|"
    r"citizen charter|transfer|seniority|disciplinary|suspension|\bretire", re.I)
ADMIT_RE = re.compile(
    r"admit card|e-?admit|call letter|interview letter|hall ticket|"
    r"admission certificate|interview card", re.I)
RESULT_RE = re.compile(
    r"\bresults?\b|recommend(?:ed|ation)|merit list|score summ|cut[- ]?off marks|"
    r"final list|selection list|selected candidates|provisional list|"
    r"list of (?:eligible |shortlisted )?candidates|shortlisted", re.I)
EXT_RE = re.compile(r"extension|extended|\bextend\b", re.I)
CORR_RE = re.compile(r"corrigendum|addendum|amendment|erratum|rectification", re.I)
NOT_JOB_RE = re.compile(
    r"tentative|schedule|syllabus|programme|guideline|instruction|clarification|"
    r"inquir|representation|\bomr\b|scrutin|written test|personal interaction|answer key", re.I)
RECRUIT_RE = re.compile(
    r"advertisement|\badvt|vacanc|applications? (?:are |is )?invited|invites? applications?|"
    r"recruitment (?:of|to|for)|recruitment drive|walk[- ]in|engagement of|selection test|"
    r"\bhiring\b|\bposts? of\b", re.I)


def classify(title):
    """Return recruitment / admit_card / result / corrigendum / extension, or None to ignore."""
    t = norm(title)
    if EXCLUDE_RE.search(t):
        return None
    if ADMIT_RE.search(t):
        return "admit_card"
    if RESULT_RE.search(t):
        return "result"
    if EXT_RE.search(t):
        return "extension"
    if CORR_RE.search(t):
        return "corrigendum"
    if NOT_JOB_RE.search(t):
        return None
    if RECRUIT_RE.search(t):
        return "recruitment"
    return None


# ----------------------------------------------------------------- field extraction

MONTHS = r"(?:jan|feb|mar|apr|may|jun|jul|aug|sep|sept|oct|nov|dec)[a-z]*"
DATE_RE = (r"(\d{1,2}\s*[./-]\s*\d{1,2}\s*[./-]\s*\d{2,4}"
           r"|\d{1,2}(?:st|nd|rd|th)?[\s,-]+" + MONTHS + r"\.?,?[\s-]+\d{4})")
ADVT_RE = re.compile(r"advt\.?\s*(?:no\.?)?\s*[-:.]?\s*(\d{1,3})\s*/\s*(\d{4})", re.I)
POST_RE = re.compile(
    r"posts?\s+of\s+(.+?)\s*(?:[\(\[]\s*advt|\s+under\s|\s+in\s+(?:the\s+)?directorate|$)", re.I)

POSTGRAD_RE = re.compile(
    r"\bpost[- ]?graduat\w*|\bmaster(?:'?s)?\b|\bm\.?\s?(?:a|sc|com|tech|ed)\b|\bmca\b|\bmba\b", re.I)
LEVELS = [
    ("8th", 1, re.compile(r"\b(?:8th|viii|class[- ]?8|eighth)\b", re.I)),
    ("10th", 2, re.compile(
        r"\b(?:10th|matriculation|matric|madhyamik|class[- ]?(?:10|x)|hslc|tenth)\b", re.I)),
    ("12th", 3, re.compile(
        r"\b(?:12th|xii|10\s*\+\s*2|higher secondary|senior secondary|intermediate|"
        r"class[- ]?(?:12|xii)|twelfth|plus two)\b", re.I)),
    ("diploma_iti", 3.5, re.compile(r"\b(?:diploma|iti|polytechnic)\b", re.I)),
    ("graduate", 4, re.compile(
        r"\bgraduat\w*|\bbachelor\w*|\bb\.?\s?(?:sc|com|tech|ed)\b|\bb\.\s?[ae]\b|\bdegree\b", re.I)),
    ("postgraduate", 5, POSTGRAD_RE),
]
SCIENCE_RE = re.compile(
    r"science\s+stream|stream\s+of\s+science|\bpcm\b|\bpcb\b|physics|chemistry|biology|"
    r"science\s+subjects?|(?:with|having)\s+science", re.I)
MATHS_RE = re.compile(r"mathematics|\bmaths?\b", re.I)
COMMERCE_RE = re.compile(r"commerce|accountancy|business studies|book[- ]?keeping", re.I)
ARTS_RE = re.compile(r"\barts\b|humanities", re.I)


def parse_date(text):
    s = re.sub(r"\s*([./-])\s*", r"\1", (text or "").strip())
    s = re.sub(r"(\d)(st|nd|rd|th)\b", r"\1", s)
    try:
        d = dateparser.parse(s, dayfirst=True, default=datetime(2000, 1, 1))
    except (ValueError, OverflowError):
        return None
    if not (2015 <= d.year <= TODAY.year + 2):
        return None
    return d.date()


def find_advt(text):
    m = ADVT_RE.search(text or "")
    return "%d/%s" % (int(m.group(1)), m.group(2)) if m else None


def find_post(title):
    m = POST_RE.search(norm(title))
    if not m:
        return None
    return re.sub(r"\s+,", ",", m.group(1)).strip(" .,-") or None


def find_dates(text):
    """Return (start_date, last_date) as date objects or None."""
    t = norm(text)
    start = last = None
    for m in re.finditer(r"last\s*date.{0,90}?" + DATE_RE, t, re.I):
        if re.search(r"\bfee|payment|scrutiny|correction", m.group(0), re.I):
            continue
        last = parse_date(m.group(1))
        if last:
            break
    rng = re.search(
        r"(?:appl(?:y|ication|ications)|registration|online).{0,120}?" + DATE_RE +
        r"\s*(?:to|till|until|up\s*to|-|–|and)\s*" + DATE_RE, t, re.I)
    if rng:
        s, e = parse_date(rng.group(1)), parse_date(rng.group(2))
        if s:
            start = s
        if e and not last:
            last = e
    return start, last


def find_age(text):
    t = norm(text)
    out = {}
    for m in re.finditer(r"\bage\b", t, re.I):
        seg = t[m.start(): m.start() + 260]
        rng = re.search(
            r"(\d{2})\s*(?:years?|yrs?)?\s*(?:to|-|–|and)\s*(\d{2})\s*(?:years?|yrs?)", seg, re.I)
        top = re.search(
            r"(?:up\s*to|upto|not\s+(?:more|older)\s+than|not\s+exceed(?:ing)?|"
            r"maximum(?:\s+age)?(?:\s+limit)?(?:\s+is)?|below|under)\D{0,12}(\d{2})\s*(?:years?|yrs?)",
            seg, re.I)
        if rng and 14 <= int(rng.group(1)) < int(rng.group(2)) <= 70:
            lo, hi = int(rng.group(1)), int(rng.group(2))
            out.update(age_limit="%d–%d years" % (lo, hi), age_min=lo, age_max=hi)
        elif top and 14 <= int(top.group(1)) <= 70:
            hi = int(top.group(1))
            out.update(age_limit="Up to %d years" % hi, age_max=hi)
        if out:
            cut = re.search(
                r"(?:as\s+on|cut[- ]?off(?:\s+date)?|reckoned\s+(?:as\s+)?on|on\s+the\s+date)"
                r"\D{0,25}?" + DATE_RE, seg, re.I)
            if cut:
                d = parse_date(cut.group(1))
                if d:
                    out["age_cutoff"] = d.isoformat()
            break
    rel = re.search(r"relaxation", t, re.I)
    if rel:
        snippet = t[rel.start(): rel.start() + 170]
        if len(snippet) >= 170:
            snippet = snippet.rsplit(" ", 1)[0]
        out["age_relaxation"] = snippet
    return out


def find_pay(text):
    t = norm(text)
    for m in re.finditer(
            r"pay\s*(?:scale|matrix|level|band)|scale of pay|salary|remuneration|"
            r"consolidated|honorarium|stipend|emolument", t, re.I):
        seg = t[m.start(): m.start() + 200]
        c = re.search(
            r"(?:Rs\.?|INR|₹)\s?\d[\d,]{3,}(?:\s*(?:to|-|–)\s*(?:Rs\.?|₹)?\s?\d[\d,]{3,})?",
            seg, re.I)
        if c:
            return c.group(0).strip()
        lv = re.search(r"level[\s-]*(\d{1,2})", seg, re.I)
        if lv:
            return "Pay Level %s" % lv.group(1)
    return None


def find_vacancies(title, text):
    patterns = [
        r"(?:total\s+)?(?:no\.?\s*of\s*)?vacanc(?:y|ies)\s*[:\-–=]?\s*(\d{1,5})\b",
        r"no\.?\s*of\s*posts?\s*[:\-–=]?\s*(\d{1,5})\b",
        r"(\d{1,5})\s*(?:\(\s*[a-z\- ]+\s*\)\s*)?(?:vacanc(?:y|ies)|posts?\b)",
    ]
    for source in (text, title):
        t = norm(source)
        for p in patterns:
            m = re.search(p, t, re.I)
            if m and int(m.group(1)) > 0:
                return int(m.group(1))
    return None


def qualification_window(text):
    t = norm(text)
    windows = []
    for m in re.finditer(r"(?:educational\s+)?qualifications?|eligibility|essential\s+qualification",
                         t, re.I):
        windows.append(t[m.start(): m.start() + 450])
        if len(windows) >= 4:
            break
    return " ".join(windows)


def qualification_excerpt(text):
    t = norm(text)
    m = re.search(r"(?:educational\s+)?(?:essential\s+)?qualifications?\s*[:\-–]*\s*", t, re.I)
    if not m:
        return None
    ex = t[m.end(): m.end() + 220].strip(" :-–")
    return ex if len(ex) > 8 else None


def find_levels(title, text):
    scope = norm(title) + " " + qualification_window(text)
    scope_no_pg = POSTGRAD_RE.sub(" ", scope)
    found = []
    for name, rank, rx in LEVELS:
        hay = scope_no_pg if name == "graduate" else scope
        if rx.search(hay):
            found.append((rank, name))
    found.sort()
    return [name for _, name in found]


def find_stream(levels, text):
    if not levels:
        return "not_found"
    if "12th" not in levels:
        return "n/a"
    win = qualification_window(text)
    if not win:
        return "not_found"
    sci, maths = bool(SCIENCE_RE.search(win)), bool(MATHS_RE.search(win))
    com, arts = bool(COMMERCE_RE.search(win)), bool(ARTS_RE.search(win))
    if sci and (com or arts):
        return "mixed"
    if sci:
        return "science"
    if maths and (com or arts):
        return "mixed"
    if maths:
        return "maths"
    if com:
        return "commerce"
    return "not_specified"


def apply_extraction(job, text):
    start, last = find_dates(text)
    found = {
        "start_date": start.isoformat() if start else None,
        "last_date": last.isoformat() if last else None,
        "vacancies": find_vacancies(job["title"], text),
        "pay": find_pay(text),
        "qualification": qualification_excerpt(text),
    }
    found.update(find_age(text))
    for key, value in found.items():
        if job.get(key) in EMPTY and value not in EMPTY:
            job[key] = value
    levels = find_levels(job["title"], text)
    if levels:
        job["levels"] = levels
        job["min_qualification"] = levels[0]
    if job.get("stream_req") in EMPTY:
        job["stream_req"] = find_stream(levels, text)


# ----------------------------------------------------------------- web access

class Fetcher:
    def __init__(self, cfg):
        h = cfg["http"]
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": h["user_agent"],
            "Accept": "text/html,application/pdf,application/xml;q=0.9,*/*;q=0.5",
            "Accept-Language": "en-IN,en;q=0.8",
        })
        self.agent = h["robots_agent"]
        self.timeout = (h["connect_timeout"], h["read_timeout"])
        self.retries = h["retries"]
        self.delay = h["delay_seconds"]
        self.last_hit = {}
        self.robots = {}

    def _pause(self, host):
        wait = self.delay - (time.time() - self.last_hit.get(host, 0))
        if wait > 0:
            time.sleep(wait)
        self.last_hit[host] = time.time()

    def _request(self, url, stream=False):
        host = urlparse(url).netloc
        error = "unknown error"
        for attempt in range(self.retries + 1):
            if attempt:
                time.sleep(3 * attempt)
            self._pause(host)
            try:
                resp = self.session.get(url, timeout=self.timeout, stream=stream)
            except requests.RequestException as exc:
                error = type(exc).__name__
                continue
            if resp.status_code >= 500:
                error = "HTTP %d" % resp.status_code
                resp.close()
                continue
            return resp
        raise FetchError(error)

    def _check_robots(self, url):
        parts = urlparse(url)
        base = "%s://%s" % (parts.scheme, parts.netloc)
        if base not in self.robots:
            try:
                resp = self._request(base + "/robots.txt")
                if resp.status_code == 200:
                    rp = urllib.robotparser.RobotFileParser()
                    rp.parse(resp.text.splitlines())
                    self.robots[base] = rp
                else:
                    self.robots[base] = "allow"      # 3xx/4xx: no robots rules published
            except FetchError:
                self.robots[base] = "unavailable"
        state = self.robots[base]
        if state == "unavailable":
            raise RobotsUnavailable(base)
        if state == "allow":
            return
        if not state.can_fetch(self.agent, url):
            raise RobotsBlocked(url)

    def get(self, url, stream=False):
        self._check_robots(url)
        resp = self._request(url, stream=stream)
        if resp.status_code != 200:
            code = resp.status_code
            resp.close()
            raise FetchError("HTTP %d" % code)
        return resp

    def fetch_items(self, src):
        resp = self.get(src["url"])
        if src.get("type", "html") == "rss":
            feed = feedparser.parse(resp.content)
            return [{"title": norm(e.get("title", "")), "url": e.get("link", "")}
                    for e in feed.entries if e.get("link")]
        return extract_links(resp.content, resp.url)

    def fetch_text(self, url, max_mb, max_pages):
        resp = self.get(url, stream=True)
        limit = int(max_mb * 1024 * 1024)
        data = bytearray()
        try:
            declared = resp.headers.get("Content-Length", "")
            if declared.isdigit() and int(declared) > limit:
                raise FetchError("file larger than %s MB" % max_mb)
            for chunk in resp.iter_content(65536):
                data.extend(chunk)
                if len(data) > limit:
                    raise FetchError("file larger than %s MB" % max_mb)
        finally:
            resp.close()
        raw = bytes(data)
        if raw[:5] == b"%PDF-":
            reader = PdfReader(io.BytesIO(raw))
            return "\n".join((p.extract_text() or "") for p in reader.pages[:max_pages])
        soup = BeautifulSoup(raw, "lxml")
        for tag in soup(["script", "style", "noscript", "nav", "header", "footer"]):
            tag.decompose()
        return soup.get_text(" ", strip=True)


def extract_links(content, base_url):
    soup = BeautifulSoup(content, "lxml")
    for tag in soup(["script", "style", "noscript"]):
        tag.decompose()
    out, seen = [], set()
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
            continue
        text = norm(a.get_text(" ", strip=True))
        text = re.sub(r"^pdf icon\s*", "", text, flags=re.I).strip()
        if len(text) < 15 or len(text.split()) < 3:
            continue
        url = urljoin(base_url, href)
        key = (text.lower(), url)
        if key in seen:
            continue
        seen.add(key)
        out.append({"title": text, "url": url})
    return out


# ----------------------------------------------------------------- jobs

def make_id(org, title, advt, kind):
    if advt and kind == "recruitment":
        base = "%s|advt:%s" % (norm_words(org), advt)
    else:
        base = "%s|%s|%s" % (norm_words(org), kind, norm_words(title))
    return hashlib.sha1(base.encode("utf-8")).hexdigest()[:12]


def make_job(item, src, kind, baseline):
    title, url = item["title"], item["url"]
    advt = find_advt(title)
    is_file = bool(re.search(r"\.(pdf|docx?)($|\?)", url, re.I)) or "/sites/default/files/" in url
    levels = find_levels(title, "")
    return {
        "id": make_id(src["org"], title, advt, kind),
        "kind": kind,
        "title": title,
        "organization": src["org"],
        "sector": src.get("sector", "Other"),
        "post": find_post(title),
        "advt_no": advt,
        "vacancies": find_vacancies(title, ""),
        "qualification": None,
        "levels": levels,
        "min_qualification": levels[0] if levels else None,
        "stream_req": "not_found",
        "age_limit": None, "age_min": None, "age_max": None,
        "age_cutoff": None, "age_relaxation": None,
        "pay": None,
        "location": src.get("location", "Tripura"),
        "start_date": None,
        "last_date": None,
        "notification_url": url if is_file else None,
        "page_url": None if is_file else url,
        "apply_url": src.get("apply_url") or src["url"],
        "source": src["name"],
        "source_url": src["url"],
        "trust": src.get("trust", "OFFICIAL"),
        "first_seen": NOW_ISO,
        "initial": bool(baseline),
        "enriched": False,
        "enrich_tries": 0,
        "enrich_note": None,
        "updates": [],
        "updated_at": None,
        "also_on": [],
        "archived": False,
    }


def upsert(jobs, new):
    """Add a job, or fill empty fields of the existing one. Returns True if it was new."""
    old = jobs.get(new["id"])
    if old is None:
        jobs[new["id"]] = new
        return True
    for key in FILL_FIELDS:
        if old.get(key) in EMPTY and new.get(key) not in EMPTY:
            old[key] = new[key]
    return False


def attach_update(jobs, job, baseline):
    """Attach a corrigendum/admit card/result to its parent job (same Advt. number)."""
    if not job["advt_no"]:
        return False
    parent = jobs.get(make_id(job["organization"], "", job["advt_no"], "recruitment"))
    if parent is None:
        return False
    key = job["kind"] + "|" + norm_words(job["title"])
    if all(u.get("key") != key for u in parent["updates"]):
        parent["updates"].append({
            "key": key, "kind": job["kind"], "title": job["title"],
            "url": job["notification_url"] or job["page_url"],
            "seen": NOW_ISO, "initial": bool(baseline),
        })
        if not baseline:
            parent["updated_at"] = NOW_ISO
    return True


def enrich_jobs(jobs, fetcher, cfg):
    p = cfg["pdf"]
    todo = [j for j in jobs.values()
            if j["kind"] == "recruitment" and not j["enriched"] and j["enrich_tries"] < p["max_tries"]]
    todo.sort(key=lambda j: j["first_seen"], reverse=True)
    todo.sort(key=lambda j: j["initial"])          # newest real jobs first, old baseline last
    done = 0
    for job in todo[: p["max_per_run"]]:
        url = job["notification_url"] or job["page_url"]
        if not url:
            job["enriched"] = True
            continue
        try:
            text = fetcher.fetch_text(url, p["max_mb"], p["max_pages"])
        except (FetchError, RobotsBlocked, RobotsUnavailable) as exc:
            job["enrich_tries"] += 1
            job["enrich_note"] = "Could not read notice: %s" % short(str(exc) or type(exc).__name__, 60)
            continue
        except Exception as exc:                    # broken or unusual PDF
            job["enrich_tries"] += 1
            job["enrich_note"] = "Could not read notice: %s" % type(exc).__name__
            continue
        if len(norm(text)) < 40:
            job["enriched"] = True
            job["enrich_note"] = "No readable text in the notice (scanned PDF?). Open it manually."
            continue
        apply_extraction(job, text)
        job["enriched"] = True
        job["enrich_note"] = None
        done += 1
    return done


def housekeeping(jobs, cfg):
    h = cfg["history"]
    removed = archived = 0
    for jid in list(jobs):
        j = jobs[jid]
        age_days = (TODAY - date.fromisoformat(j["first_seen"][:10])).days
        if age_days > h["keep_days"]:
            del jobs[jid]
            removed += 1
            continue
        if j.get("last_date"):
            expired = date.fromisoformat(j["last_date"]) < TODAY - timedelta(days=h["expired_grace_days"])
        elif j["kind"] == "recruitment":
            expired = age_days > h["no_date_archive_days"]
        else:
            expired = age_days > h["update_archive_days"]
        j["archived"] = bool(expired)
        archived += 1 if expired else 0
    return removed, archived


# ----------------------------------------------------------------- reporting

def health_sig(health):
    skip = ("last_run", "last_success", "seconds")
    return json.dumps({k: {a: b for a, b in v.items() if a not in skip}
                       for k, v in health["sources"].items()}, sort_keys=True)


def write_step_summary(lines):
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")


def print_preview(name, accepted, ignored):
    print("\n--- %s: kept %d, ignored %d ---" % (name, len(accepted), len(ignored)))
    for it, kind in accepted[:25]:
        print("  [%s] %s" % (kind, short(it["title"])))
    if ignored:
        print("  (ignored examples)")
        for title in ignored[:10]:
            print("   -  %s" % short(title, 90))


# ----------------------------------------------------------------- main run

def run(args):
    cfg = load_yaml("config.yaml")
    sources = [s for s in load_yaml("sources.yaml").get("sources", []) if s.get("enabled")]
    if args.group == "fast":
        sources = [s for s in sources if s.get("frequency") == "fast"]
    dry = args.mode == "dry-run"
    print("Mode: %s | group: %s | sources to check: %d" % (args.mode, args.group, len(sources)), flush=True)

    jobs_doc = load_json(JOBS_FILE, {"updated": None, "jobs": []})
    health = load_json(HEALTH_FILE, {"updated": None, "sources": {}})
    health.setdefault("sources", {})
    state = load_json(STATE_FILE, {"updated": None, "last_keepalive": None,
                                   "alerted": {}, "seen_hashes": {}})
    state.setdefault("baselined", {})
    jobs = {j["id"]: j for j in jobs_doc.get("jobs", [])}
    jobs_before = json.dumps(jobs_doc.get("jobs", []), sort_keys=True)   # snapshot before any edits
    health_before = health_sig(health)
    health_old_updated = health.get("updated")
    state_before = json.dumps(state, sort_keys=True)

    fetcher = Fetcher(cfg)
    rows = []
    for src in sources:
        name = src["name"]
        rec = health["sources"].setdefault(name, {})
        rec["url"] = src["url"]
        rec["last_run"] = NOW_ISO
        began = time.time()
        found = kept = new_jobs = 0
        status, note = "ok", ""
        try:
            items = fetcher.fetch_items(src)
            found = len(items)
            if found == 0:
                raise EmptyResult("page opened but no links were found; the layout may have changed")
            accepted, ignored = [], []
            for it in items:
                kind = classify(it["title"])
                if kind:
                    accepted.append((it, kind))
                else:
                    ignored.append(it["title"])
            accepted.sort(key=lambda pair: KIND_ORDER[pair[1]])
            baseline = name not in state["baselined"]
            for it, kind in accepted:
                job = make_job(it, src, kind, baseline)
                if kind in UPDATE_KINDS:
                    if attach_update(jobs, job, baseline):
                        continue
                    if baseline:
                        continue                    # skip old standalone results on first run
                    job["updated_at"] = NOW_ISO
                if upsert(jobs, job):
                    new_jobs += 1
            kept = len(accepted)
            state["baselined"][name] = True
            prev = rec.get("items_found")
            if prev and found < 0.3 * prev:
                status = "warn"
                note = "link count fell from %d to %d; the layout may have changed" % (prev, found)
            print_preview(name, accepted, ignored)
        except RobotsBlocked:
            status, note = "blocked", "robots.txt does not allow this page; skipped"
        except RobotsUnavailable:
            status, note = "error", "robots.txt could not be read; skipped to stay polite"
        except EmptyResult as exc:
            status, note = "warn", str(exc)
        except FetchError as exc:
            status, note = "error", str(exc)
        except Exception as exc:
            status, note = "error", "unexpected: %s" % exc
            traceback.print_exc()

        rec["status"] = status
        rec["error"] = note or None
        rec["seconds"] = round(time.time() - began, 1)
        if status in ("ok", "warn") and found:
            rec["items_found"] = found
            rec["kept"] = kept
            rec["last_success"] = NOW_ISO
            rec["consecutive_failures"] = 0
        elif status != "ok":
            rec["consecutive_failures"] = rec.get("consecutive_failures", 0) + 1
        if new_jobs:
            rec["last_new_job"] = NOW_ISO
        rows.append((name, status, found, kept, new_jobs, note))
        print("%s: %s (links %d, kept %d, new %d) %s" % (name, status.upper(), found, kept, new_jobs, note),
              flush=True)

    done = enrich_jobs(jobs, fetcher, cfg)
    removed, archived = housekeeping(jobs, cfg)
    print("\nNotices read this run: %d | archived: %d | removed (older than a year): %d"
          % (done, archived, removed))

    new_list = sorted(jobs.values(), key=lambda j: j["first_seen"], reverse=True)
    lines = ["## Tripura Job Alert run (%s, %s)" % (args.mode, args.group),
             "", "| Source | Status | Links | Kept | New | Note |", "|---|---|---|---|---|---|"]
    for name, status, found, kept, new_jobs, note in rows:
        lines.append("| %s | %s | %d | %d | %d | %s |" % (name, status, found, kept, new_jobs, note))
    lines.append("")
    lines.append("Jobs stored: %d (active: %d)" % (len(new_list), sum(1 for j in new_list if not j["archived"])))
    write_step_summary(lines)

    if dry:
        print("\nDRY RUN: nothing was saved.")
        return

    if jobs_before != json.dumps(new_list, sort_keys=True):
        save_json(JOBS_FILE, {"updated": NOW_ISO, "jobs": new_list})
        print("Saved data/jobs.json")
    if health_sig(health) != health_before or hours_since(health_old_updated) >= 6:
        health["updated"] = NOW_ISO
        save_json(HEALTH_FILE, health)
        print("Saved data/health.json")
    if args.group == "all" and hours_since(state.get("last_keepalive")) >= cfg["keepalive_days"] * 24:
        state["last_keepalive"] = NOW_ISO           # keep-alive: forces a small commit
    if json.dumps(state, sort_keys=True) != state_before:
        state["updated"] = NOW_ISO
        save_json(STATE_FILE, state)
        print("Saved data/state.json")


# ----------------------------------------------------------------- self test (offline)

def selftest():
    results = []

    def check(name, got, want):
        ok = got == want
        results.append(ok)
        print(("PASS  " if ok else "FAIL  ") + name)
        if not ok:
            print("      got:  %r\n      want: %r" % (got, want))

    titles = [
        ("Advertisement for recruitment to the posts of Personal Assistant , Grade-II(PA-II) (Advt. No-25/2025)", "recruitment"),
        ("Recommendation list for the post of General Duty Medical Officer, Grade-IV of THS(Advt. No-07/2024)", "result"),
        ("Provisional Admission Certificate for written examination of Sr. Informatics Officer(Advt. No-11/2024)", "admit_card"),
        ("Notice inviting Quotation for 4(Four) nos. Commercial Maruti EECO Vehicle in TPSC", None),
        ("Notification regarding Tentative schedule of various recruitment process under TPSC", None),
        ("Recruitment of Constable of Tripura police on compassionate appointment (Die-in -harness scheme)", None),
        ("Notification of the merit list for recruitment of Police Constables (Men & Women) in Tripura Police.", "result"),
        ("Notice regarding downloading Interview letter for Personal Interaction Test in c.w. recruitment of Constables in Tripura Police", "admit_card"),
        ("Syllabus & Guidelines of Tripura Combined Competitive Examination for recruitment to Miscellaneous Posts.", None),
        ("Advertisement for recruitment to Miscellaneous posts though Tripura Combined Competitive Examination(Advt. No-18/2025)", "recruitment"),
        ("Corrigendum: extension of last date for Advt. No-21/2025", "extension"),
        ("Notice regarding written test for recruitment of Police Constables(Men and Women) in Tripura Police.", None),
        ("Score Summary of Deputy Manager(Technical)(Advt. No-03/2024)", "result"),
    ]
    for title, want in titles:
        check("classify: " + short(title, 60), classify(title), want)

    t = "Advertisement for recruitment to the posts of Personal Assistant , Grade-II(PA-II) (Advt. No-25/2025)"
    check("advt number", find_advt(t), "25/2025")
    check("post name", find_post(t), "Personal Assistant, Grade-II(PA-II)")
    check("date 15.12.2026", parse_date("15.12.2026"), date(2026, 12, 15))
    check("date 7th October 2026", parse_date("7th October 2026"), date(2026, 10, 7))

    t1 = ("Educational Qualification: Higher Secondary (10+2) passed from a recognised Board. "
          "Age limit: 18 to 40 years as on 01.01.2026. Age relaxation: 5 years for SC/ST. "
          "Pay Level-4: Rs. 25,500 - 81,100. Total vacancies: 100. "
          "Last date for online application: 15.12.2026.")
    check("last date", find_dates(t1), (None, date(2026, 12, 15)))
    age = find_age(t1)
    check("age limit", age.get("age_limit"), "18–40 years")
    check("age cutoff", age.get("age_cutoff"), "2026-01-01")
    check("age relaxation", (age.get("age_relaxation") or "")[:25], "relaxation: 5 years for S")
    check("pay", find_pay(t1), "Rs. 25,500 - 81,100")
    check("vacancies", find_vacancies("", t1), 100)
    check("levels (12th)", find_levels("", t1), ["12th"])
    check("stream not specified", find_stream(["12th"], t1), "not_specified")

    t2 = "Eligibility: Passed 10+2 (Science stream with Mathematics) from a recognised board."
    check("stream science", find_stream(find_levels("", t2), t2), "science")
    t3 = "Essential Qualification: 12th pass in Commerce stream."
    check("stream commerce", find_stream(find_levels("", t3), t3), "commerce")
    t4 = "Eligibility: Class X pass (Matriculation) from a recognised board."
    check("level 10th", find_levels("", t4), ["10th"])
    check("age 'up to'", find_age("Age limit: not exceeding 40 years as on 01.01.2026.").get("age_limit"),
          "Up to 40 years")
    t6 = "Online application can be submitted from 24.02.2025 to 21.03.2025."
    check("date range", find_dates(t6), (date(2025, 2, 24), date(2025, 3, 21)))

    html = (b'<ul><li><a href="/sites/default/files/a.pdf">PDF icon Notice regarding something long enough here</a></li>'
            b'<li><a href="/home">Home</a></li></ul>')
    check("link extraction", extract_links(html, "https://x.test/p"),
          [{"title": "Notice regarding something long enough here",
            "url": "https://x.test/sites/default/files/a.pdf"}])

    try:
        cfg = load_yaml("config.yaml")
        check("config.yaml loads", "http" in cfg and "alerts" in cfg, True)
        srcs = load_yaml("sources.yaml")["sources"]
        needed = ("name", "org", "url", "type", "sector", "trust", "frequency", "enabled")
        check("sources.yaml fields", all(all(k in s for k in needed) for s in srcs), True)
        check("trust values", all(s["trust"] in ("OFFICIAL", "AGGREGATOR") for s in srcs), True)
    except Exception as exc:
        check("config files load (%s)" % exc, False, True)
    sample = load_json(SAMPLE_FILE, {})
    check("sample_jobs.json loads", len(sample.get("jobs", [])) >= 5, True)

    failed = results.count(False)
    print("\n%d checks, %d failed" % (len(results), failed))
    return 1 if failed else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["real", "dry-run", "selftest"], default="dry-run")
    ap.add_argument("--group", choices=["all", "fast"], default="all")
    args = ap.parse_args()
    if args.mode == "selftest":
        sys.exit(selftest())
    run(args)


if __name__ == "__main__":
    main()

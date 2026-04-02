import os
import json

if not os.path.exists("filtered_snapshot.json"):
    with open("filtered_snapshot.json", "w") as f:
        json.dump([], f)
import time
import smtplib
import logging
import threading
from datetime import datetime, timezone, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText

from zoneinfo import ZoneInfo

import requests

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger(__name__)

# ── Credentials ───────────────────────────────────────────────────────────────
EMAIL_SENDER    = os.environ.get("EMAIL_SENDER", "")
EMAIL_PASSWORD  = os.environ.get("EMAIL_PASSWORD", "")
EMAIL_RECIPIENT = os.environ.get("EMAIL_RECIPIENT", "")

# ── IAPD endpoints ────────────────────────────────────────────────────────────
IAPD_SEARCH_URL  = "https://api.adviserinfo.sec.gov/search/firm"
IAPD_DETAIL_URL  = "https://api.adviserinfo.sec.gov/search/firm/{crd}"
IAPD_PROFILE_URL = "https://www.adviserinfo.sec.gov/firm/summary/{crd}"

IAPD_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json, */*",
    "Referer": "https://www.adviserinfo.sec.gov/",
}

# ── Storage ───────────────────────────────────────────────────────────────────
# filtered_snapshot.json — the filtered set from the PREVIOUS run.
#   {crd: {"firmName", "crd", "city", "state", "sourceLink", "matchReason"}}
# Delta = (current filtered set) minus (prior snapshot) → triggers email.
SNAPSHOT_FILE = "filtered_snapshot.json"

# ── API settings ──────────────────────────────────────────────────────────────
PAGE_SIZE     = 100
MAX_START     = 9900    # Elasticsearch hard cap
REQUEST_DELAY = 0.10    # seconds between sweep page calls

CHECK_INTERVAL = 60 * 60 * 24   # seconds between monitor cycles (24 hours)

# ── Sweep queries ─────────────────────────────────────────────────────────────
# Single-word terms for the IAPD full-text search. Together they ensure any
# firm that could pass the scoring filter is captured in at least one query.
# Institutional classification is done locally by the scoring filter.
SWEEP_QUERIES = [
    "capital", "management", "asset", "investment",
    "partners", "advisors", "adviser", "trading",
    "systematic", "investor", "solutions", "counsel",
    "ventures", "venture", "hedge", "alternative",
    "fund", "quant", "offshore", "arbitrage",
    "equity", "equities", "group",
]

# ── Exact-name whitelist ──────────────────────────────────────────────────────
# Firms here always pass the filter regardless of negative pattern matches.
POSITIVE_NAME_WHITELIST: list[str] = [
    "MY LEGACY ADVISORS, LLC",
    "PLACID SOUND CAPITAL MANAGEMENT, LLC",
    "WAVERTON INVESTMENT MANAGEMENT LIMITED",
    "SENSIBLE FINANCIAL PLANNING AND MANAGEMENT, LLC",
    "THE FINANCIAL ADVISORS, LLC",
]

# ── Strong institutional pattern whitelist ────────────────────────────────────
# Substring match in the normalised firm name → strong positive signal.
# Negative retail terms do NOT override a pattern-whitelist match unless the
# name is explicitly retail-branded (score drops below -15 after all penalties).
POSITIVE_PATTERN_WHITELIST: list[str] = [
    "asset management",
    "capital management",
    "investment management",
    "capital partners",
    "asset management llc",
    "asset management lp",
    "investment management limited",
    "capital management ltd",
    "capital management llc",
    "capital management lp",
    "partners lp",
    "partners llc",
    "partners llp",
    "capital llc",
    "capital lp",
    "capital ltd",
]

# ── Scoring tables (used when no whitelist entry matches) ─────────────────────
# Tier 1 (+15): unambiguous institutional phrases
_TIER1: dict[str, int] = {
    "asset management":             15,
    "capital management":           15,
    "investment management":        15,
    "capital partners":             15,
    "capital advisors":             15,
    "capital adviser":              15,
    "investment counsel":           15,
    "investor solutions":           15,
    "systematic trading":           15,
}

# Tier 2 (+10 or +15): institutional phrase + legal structure
_TIER2: dict[str, int] = {
    "asset management limited":     15,
    "investment management limited":15,
    "capital management limited":   15,
    "capital management lp":        15,
    "capital management llc":       15,
    "capital management llp":       15,
    "capital group":                10,
    "management limited":           10,
    "management lp":                10,
    "management llc":               10,
    "management ltd":               10,
    "management llp":               10,
    "partners lp":                  10,
    "partners llp":                 10,
    "partners limited":             10,
    "investments lp":               10,
    "investments llc":              10,
    "investments llp":              10,
    "capital llc":                  10,
    "capital lp":                   10,
    "capital ltd":                  10,
    "capital limited":              10,
    "capital ag":                   10,
}

# Supporting terms: whole-word matches, total capped at +8
_SUPPORT: dict[str, int] = {
    "capital":      4,
    "asset":        4,
    "investment":   4,
    "investor":     3,
    "management":   3,
    "partners":     3,
    "advisors":     2,
    "adviser":      2,
    "trading":      2,
    "systematic":   2,
    "solutions":    2,
    "counsel":      2,
    "group":        2,
    "investments":  2,
    "ltd":          2,
    "limited":      2,
    "lp":           2,
    "llp":          2,
    "llc":          2,
    "ag":           2,
}

# Negative patterns: each match deducts heavily
_NEGATIVE: dict[str, int] = {
    "wealth management":    -20,
    "financial planning":   -20,
    "financial advisors":   -20,
    "financial advisor":    -20,
    "retirement":           -15,
    "insurance":            -15,
    "brokerage":            -15,
    "personal financial":   -15,
    "private client":       -15,
    "family wealth":        -15,
    "mortgage":             -15,
    "tax planning":         -15,
}

RELEVANCE_THRESHOLD = 10


def _normalise(name: str) -> str:
    """Lower-case, expand abbreviations, strip punctuation."""
    import re
    n = name.lower()
    n = n.replace("l.p.", "lp").replace("l.l.c.", "llc").replace("l.l.p.", "llp")
    n = re.sub(r"[^\w\s]", " ", n)
    n = re.sub(r"\s+", " ", n).strip()
    return n


def _score_firm(firm_name: str) -> tuple[int, str]:
    """Return (raw_score, top_matched_pattern)."""
    n = _normalise(firm_name)
    total = 0
    top_pattern = ""

    for table in (_TIER2, _TIER1):
        for pat in sorted(table, key=len, reverse=True):
            if pat in n:
                total += table[pat]
                if not top_pattern:
                    top_pattern = pat

    for pat, pen in _NEGATIVE.items():
        if pat in n:
            total += pen

    support = 0
    words = set(n.split())
    for term, pts in _SUPPORT.items():
        if term in words:
            support += pts
    total += min(support, 8)

    return total, top_pattern


def _get_match_reason(firm_name: str) -> tuple[bool, int, str]:
    """Return (passes_filter, score, reason_string).

    Priority order:
    1. Exact name whitelist  → always passes, score=999
    2. Pattern whitelist     → passes unless strongly retail-branded (score < -15)
    3. Scoring filter        → passes if score >= RELEVANCE_THRESHOLD
    """
    n = _normalise(firm_name)

    # 1. Exact name whitelist
    for entry in POSITIVE_NAME_WHITELIST:
        if _normalise(entry) == n:
            return True, 999, f"Exact whitelist: {entry}"

    # 2. Pattern whitelist
    matched_pat = None
    for pat in sorted(POSITIVE_PATTERN_WHITELIST, key=len, reverse=True):
        if pat in n:
            matched_pat = pat
            break

    if matched_pat:
        score, _ = _score_firm(firm_name)
        if score < -15:
            # Name is explicitly retail-branded even with the institutional pattern
            neg_hits = [p for p in _NEGATIVE if p in n]
            return False, score, (
                f"Pattern '{matched_pat}' found but overridden by retail indicators: "
                + ", ".join(neg_hits)
            )
        return True, max(score, 10), f"Strong pattern: '{matched_pat}'"

    # 3. Standard scoring
    score, top_pat = _score_firm(firm_name)
    if score >= RELEVANCE_THRESHOLD:
        return True, score, f"Score {score}: {top_pat or 'supporting terms'}"
    neg_hits = [p for p in _NEGATIVE if p in n]
    return False, score, (
        f"Score {score} (threshold {RELEVANCE_THRESHOLD})"
        + (f" — retail indicators: {', '.join(neg_hits)}" if neg_hits else "")
    )


def find_matched_keyword(firm_name: str) -> str:
    """Return the match reason string (used in email body)."""
    _, _, reason = _get_match_reason(firm_name)
    return reason


def is_relevant(firm_name: str) -> bool:
    """Return True if the firm passes the institutional filter."""
    passes, _, _ = _get_match_reason(firm_name)
    return passes


# ── Persistence ───────────────────────────────────────────────────────────────

def load_json(path: str, default):
    if os.path.exists(path):
        try:
            with open(path) as f:
                return json.load(f)
        except (json.JSONDecodeError, IOError):
            log.warning("Could not read %s — starting fresh.", path)
    return default


def save_json(path: str, data) -> None:
    with open(path, "w") as f:
        json.dump(data, f, indent=2)


# ── IAPD helpers ──────────────────────────────────────────────────────────────

_rate_limited = False  # module-level flag set on first 429 in a cycle


def _get(url: str, params: dict, retries: int = 3) -> dict | None:
    global _rate_limited
    for attempt in range(1, retries + 1):
        try:
            r = requests.get(url, params=params, headers=IAPD_HEADERS, timeout=20)
            if r.status_code == 200:
                return r.json()
            if r.status_code == 429:
                if not _rate_limited:
                    log.warning("IAPD returned 429 (rate limited). "
                                "Cycle will yield 0 results; next check in %d s.",
                                CHECK_INTERVAL)
                    _rate_limited = True
                return None   # no point retrying immediately
        except requests.RequestException:
            pass
        time.sleep(0.5 * attempt)
    return None


_detail_debug_count = 0   # log full raw response for first 3 detail calls


def fetch_firm_detail(crd: str) -> dict:
    """Fetch firm detail via /search/firm/{crd}.

    Checks two SEC-level status sources in priority order:
      1. registrationStatus[]  where secJurisdiction=="SEC" and status=="Terminated"
      2. exemptReportingAdvisers[] where secJurisdiction=="SEC" and status=="ERA - Withdrawn"

    State-level entries, notice filings, and all other sections are ignored.
    The effectiveDate is taken only from whichever source matches.

    Returns:
      {
        "confirmed":     bool,  # True if either condition above is met
        "status":        str,   # The matched status string
        "effectiveDate": str,   # From the matched section only
        "statusType":    str,   # "Terminated" or "ERA - Withdrawn"
      }
    """
    global _detail_debug_count
    _not_found = {"confirmed": False, "status": "", "effectiveDate": "", "statusType": ""}

    url = IAPD_DETAIL_URL.format(crd=crd)
    try:
        r = requests.get(url, headers=IAPD_HEADERS, timeout=20)
    except requests.RequestException as exc:
        log.error("  [detail] Request failed for CRD %s: %s", crd, exc)
        return _not_found

    if r.status_code != 200:
        log.warning("  [detail] HTTP %d for CRD %s", r.status_code, crd)
        return _not_found

    hits = r.json().get("hits", {}).get("hits", [])
    if not hits:
        log.info("  [detail] No data returned for CRD %s", crd)
        return _not_found

    try:
        iacontent = json.loads(hits[0].get("_source", {}).get("iacontent", "{}"))
    except (json.JSONDecodeError, TypeError):
        iacontent = {}

    reg_list = iacontent.get("registrationStatus", [])
    era_list = iacontent.get("exemptReportingAdvisers", [])

    # Debug: log both sections for first 3 calls per cycle
    if _detail_debug_count < 3:
        _detail_debug_count += 1
        log.info(
            "  [detail debug #%d] CRD %s | registrationStatus: %s | exemptReportingAdvisers: %s",
            _detail_debug_count, crd, json.dumps(reg_list), json.dumps(era_list),
        )

    def _sec_entry(lst: list) -> dict | None:
        """Return the entry where secJurisdiction == 'SEC', or None."""
        return next((e for e in lst if e.get("secJurisdiction", "").upper() == "SEC"), None)

    # ── 1. Check SEC registration: must be exactly "Terminated" ──────────────
    reg_sec = _sec_entry(reg_list)
    if reg_sec:
        status = reg_sec.get("status", "")
        date   = reg_sec.get("effectiveDate", "")
        log.info("  [detail] CRD %s | SEC reg status: %r | date: %r", crd, status, date or "(not set)")
        if status == "Terminated":
            return {"confirmed": True, "status": status, "effectiveDate": date, "statusType": "Terminated"}
        log.info("  [detail] CRD %s | SEC reg status %r ≠ 'Terminated' — checking ERA …", crd, status)
    else:
        log.info("  [detail] CRD %s | No SEC entry in registrationStatus — checking ERA …", crd)

    # ── 2. Check ERA section: must be exactly "ERA - Withdrawn" ──────────────
    era_sec = _sec_entry(era_list)
    if era_sec:
        status = era_sec.get("status", "")
        date   = era_sec.get("effectiveDate", "")
        log.info("  [detail] CRD %s | SEC ERA status: %r | date: %r", crd, status, date or "(not set)")
        if status == "ERA - Withdrawn":
            return {"confirmed": True, "status": status, "effectiveDate": date, "statusType": "ERA - Withdrawn"}
        log.info("  [detail] CRD %s | SEC ERA status %r ≠ 'ERA - Withdrawn' → EXCLUDED", crd, status)
    else:
        log.info("  [detail] CRD %s | No SEC entry in ERA section → EXCLUDED", crd)

    return _not_found


def sweep_terminated() -> dict[str, dict]:
    """Paginate all sweep queries; return {crd: {name, city, state}}.

    Full sweep every run — no early stopping — so that newly appearing
    firms in any position of the result set are always captured.
    """
    all_crds: dict[str, dict] = {}

    for query in SWEEP_QUERIES:
        start       = 0
        query_total = None

        while start <= MAX_START:
            data = _get(IAPD_SEARCH_URL, {
                "query": query, "ct": "Terminated",
                "nrows": str(PAGE_SIZE), "start": str(start),
            })
            time.sleep(REQUEST_DELAY)
            if data is None:
                break

            hits_obj = data.get("hits") or {}
            hits     = hits_obj.get("hits") or []
            if query_total is None:
                query_total = hits_obj.get("total", 0)
            if not hits:
                break

            for h in hits:
                src = h.get("_source", {})
                if src.get("firm_ia_scope", "") != "INACTIVE":
                    continue
                crd = str(src.get("firm_source_id", ""))
                if not crd or crd in all_crds:
                    continue
                try:
                    addr = json.loads(
                        src.get("firm_ia_address_details", "{}")
                    ).get("officeAddress", {})
                except (json.JSONDecodeError, TypeError):
                    addr = {}
                all_crds[crd] = {
                    "name":  src.get("firm_name", "Unknown"),
                    "city":  addr.get("city", ""),
                    "state": addr.get("state", ""),
                }

            start += PAGE_SIZE
            if start > (query_total or 0):
                break

    return all_crds


# ── Email ─────────────────────────────────────────────────────────────────────

def send_email(subject: str, body: str) -> None:
    if not all([EMAIL_SENDER, EMAIL_PASSWORD, EMAIL_RECIPIENT]):
        log.warning("Email credentials not configured — skipping alert.")
        return
    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"]    = EMAIL_SENDER
    msg["To"]      = EMAIL_RECIPIENT
    msg.attach(MIMEText(body, "plain"))
    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as srv:
            srv.login(EMAIL_SENDER, EMAIL_PASSWORD)
            recipients = [r.strip() for r in EMAIL_RECIPIENT.split(",") if r.strip()]
            srv.sendmail(EMAIL_SENDER, recipients, msg.as_string())
        log.info("Email sent to %s", EMAIL_RECIPIENT)
    except smtplib.SMTPException as exc:
        log.error("Failed to send email: %s", exc)


def build_delta_email(confirmed_firms: list[dict], unconfirmed_firms: list[dict],
                      total_scanned: int, total_filtered: int) -> str:
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    total_new = len(confirmed_firms) + len(unconfirmed_firms)
    lines = [
        "IAPD Delta — Newly Appeared Terminated Advisers Matching Target Profile",
        f"Run at:                  {ts}",
        f"Total advisers scanned:  {total_scanned}",
        f"Passing filter:          {total_filtered}",
        f"Newly appeared:          {total_new}",
        f"  Confirmed terminated:  {len(confirmed_firms)}",
        f"  Unconfirmed (pending): {len(unconfirmed_firms)}",
        "",
    ]

    if confirmed_firms:
        lines += ["=" * 68, "CONFIRMED TERMINATIONS (detail endpoint verified)", "=" * 68, ""]
        for i, f in enumerate(confirmed_firms, 1):
            loc        = ", ".join(x for x in [f.get("city", ""), f.get("state", "")] if x)
            eff        = f.get("effectiveDate") or "—"
            status_lbl = f.get("statusType") or "Terminated"
            lines += [
                f"[{i}]  {f['firmName']}",
                f"      CRD:              {f['crd']}",
                f"      Status Type:      {status_lbl}",
                f"      Effective Date:   {eff}",
                f"      Location:         {loc or '—'}",
                f"      Match Reason:     {f['matchReason']}",
                f"      IAPD Link:        {f['sourceLink']}",
                "",
            ]

    if unconfirmed_firms:
        lines += ["", "=" * 68,
                  "POTENTIAL TERMINATIONS (appeared in IAPD search; detail status unclear)",
                  "=" * 68, ""]
        for i, f in enumerate(unconfirmed_firms, 1):
            loc = ", ".join(x for x in [f.get("city", ""), f.get("state", "")] if x)
            lines += [
                f"[{i}]  {f['firmName']}",
                f"      CRD:          {f['crd']}",
                f"      Location:     {loc or '—'}",
                f"      Match Reason: {f['matchReason']}",
                f"      IAPD Link:    {f['sourceLink']}",
                "",
            ]

    return "\n".join(lines)


# ── Core logic ────────────────────────────────────────────────────────────────

def build_filtered_set(sweep_results: dict) -> dict:
    """Apply the institutional filter to sweep results.

    Returns a dict keyed by CRD:
    {crd: {firmName, crd, city, state, sourceLink, matchReason}}
    """
    filtered: dict = {}
    for crd, data in sweep_results.items():
        name = data.get("name", "")
        passes, _score, reason = _get_match_reason(name)
        if passes:
            filtered[crd] = {
                "firmName":   name,
                "crd":        crd,
                "city":       data.get("city", ""),
                "state":      data.get("state", ""),
                "sourceLink": IAPD_PROFILE_URL.format(crd=crd),
                "matchReason": reason,
            }
    return filtered


def run_delta_cycle(prior_snapshot: dict) -> tuple[dict, list[dict], int]:
    """Run one full sweep + filter + diff.

    Returns (current_filtered_set, new_firms_list, total_scanned).
    new_firms_list contains entries present in current but absent from prior.
    Rate-limit retries: up to 12 × 5 min (1 hour) before giving up.
    """
    global _rate_limited
    RETRY_WAIT = 300

    sweep_results: dict = {}
    for attempt in range(1, 13):
        _rate_limited = False
        sweep_results = sweep_terminated()
        if not _rate_limited:
            break
        log.warning(
            "IAPD rate-limited on attempt %d/12 — retrying in %ds …",
            attempt, RETRY_WAIT,
        )
        time.sleep(RETRY_WAIT)

    total_scanned    = len(sweep_results)
    current_filtered = build_filtered_set(sweep_results)
    new_firms        = [
        data for crd, data in current_filtered.items()
        if crd not in prior_snapshot
    ]
    # Sort new firms alphabetically for a readable email
    new_firms.sort(key=lambda f: f["firmName"])
    return current_filtered, new_firms, total_scanned


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    log.info("SEC Investment Adviser Termination Monitor — snapshot-diff model.")
    log.info("Data source    : IAPD (adviserinfo.sec.gov)")
    log.info("Detection model: CRD delta vs %s", SNAPSHOT_FILE)
    log.info("Schedule       : daily at 02:00 AM Eastern Time — checking every 60 seconds")

    def _one_pass() -> None:
        """Run one complete sweep → filter → diff → email → snapshot cycle."""
        log.info("─" * 60)
        log.info("Script started — beginning daily IAPD sweep.")
        t0 = time.time()

        # Reload snapshot from disk each pass so consecutive cycles always
        # diff against the freshest saved state.
        snapshot    = load_json(SNAPSHOT_FILE, {})
        is_baseline = (len(snapshot) == 0)

        if is_baseline:
            log.info("No prior snapshot found — this is the baseline run.")
        else:
            log.info("Prior snapshot: %d firms", len(snapshot))

        current_filtered, new_firms, total_scanned = run_delta_cycle(snapshot)
        total_filtered = len(current_filtered)

        log.info("Data fetched — scanned: %d | passing filter: %d | newly appeared: %d",
                 total_scanned, total_filtered, len(new_firms) if not is_baseline else 0)

        if is_baseline:
            log.info("Baseline established: %d firms saved.", total_filtered)
            subject = "[IAPD] Baseline established — monitor is now active"
            body    = (
                f"The IAPD terminated-adviser monitor has started.\n\n"
                f"Baseline snapshot recorded: {total_filtered} institutional firms.\n"
                f"Total advisers scanned: {total_scanned}\n\n"
                f"Future daily emails will report any newly appeared firms."
            )
            send_email(subject, body)
        else:
            # ── Detail verification ───────────────────────────────────────────
            # For each candidate new firm, call the detail endpoint to confirm
            # "Terminated" status and retrieve effectiveDate.
            global _detail_debug_count
            _detail_debug_count = 0   # reset debug counter each cycle

            confirmed_firms = []
            unconfirmed_firms = []

            cutoff = datetime.now(timezone.utc) - timedelta(days=7)

            for f in new_firms:
                log.info("  CANDIDATE: %s [CRD %s] — %s",
                         f["firmName"], f["crd"], f["matchReason"])
                detail = fetch_firm_detail(f["crd"])
                time.sleep(0.3)   # be polite between detail calls

                if not detail["confirmed"]:
                    f["effectiveDate"] = ""
                    f["jurisdiction"]  = ""
                    unconfirmed_firms.append(f)
                    continue

                # Parse effectiveDate — IAPD format is "M/D/YYYY" (e.g. "3/17/2026")
                # strptime %m/%d/%Y handles both zero-padded and non-padded values.
                eff_str = detail.get("effectiveDate", "").strip()
                eff_date = None
                if eff_str:
                    try:
                        eff_date = datetime.strptime(eff_str, "%m/%d/%Y").replace(
                            tzinfo=timezone.utc
                        )
                    except ValueError:
                        log.warning("Could not parse effectiveDate %r for CRD %s", eff_str, f["crd"])

                if eff_date is None:
                    log.info("  EXCLUDED (no date): %s [CRD %s]", f["firmName"], f["crd"])
                    continue

                if eff_date < cutoff:
                    log.info(
                        "  EXCLUDED (too old): %s [CRD %s] — effectiveDate %s is older than 7 days",
                        f["firmName"], f["crd"], eff_str,
                    )
                    continue

                log.info(
                    "  INCLUDED: %s [CRD %s] — statusType=%s | effectiveDate=%s (within 7 days)",
                    f["firmName"], f["crd"], detail.get("statusType", "?"), eff_str,
                )
                f["effectiveDate"] = eff_str
                f["jurisdiction"]  = "SEC"
                f["statusType"]    = detail.get("statusType", "")
                confirmed_firms.append(f)

            log.info(
                "Detail verification: %d confirmed terminated | %d not confirmed",
                len(confirmed_firms), len(unconfirmed_firms),
            )

            if confirmed_firms or unconfirmed_firms:
                subject = "[IAPD DELTA] Newly appeared terminated advisers"
                body    = build_delta_email(
                    confirmed_firms, unconfirmed_firms, total_scanned, total_filtered
                )
            else:
                subject = "[IAPD DELTA] No new terminated funds found today"
                body    = (
                    f"Test run - no new firms found\n\n"
                    f"Daily IAPD sweep completed — no newly appeared terminated "
                    f"institutional advisers since the last run.\n\n"
                    f"Total advisers scanned: {total_scanned}\n"
                    f"Passing institutional filter: {total_filtered}\n"
                    f"Newly appeared: 0\n\n"
                    f"Run completed at {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}."
                )
            send_email(subject, body)

        save_json(SNAPSHOT_FILE, current_filtered)
        log.info("Snapshot saved: %d firms → %s (%.1f s)",
                 total_filtered, SNAPSHOT_FILE, time.time() - t0)

    EASTERN = ZoneInfo("America/New_York")
    last_scan_date = None

    log.info("=" * 60)
    log.info("IMMEDIATE RUN: executing scan now.")
    log.info("=" * 60)
    try:
        _one_pass()
    except Exception:
        log.exception("Unexpected error during immediate run.")
    log.info("=" * 60)
    log.info("IMMEDIATE RUN COMPLETE.")
    log.info("=" * 60)

    log.info("Entering main loop — checking time every 60 seconds.")
    _one_pass()



def _keep_alive() -> None:
    """Ping this Repl's own URL every 5 minutes to prevent it from sleeping."""
    domain = os.environ.get("REPLIT_DEV_DOMAIN", "")
    if not domain:
        log.warning("Keep-alive: REPLIT_DEV_DOMAIN not set — ping disabled.")
        return
    url = f"https://{domain}"
    log.info("Keep-alive thread started — pinging %s every 5 minutes.", url)
    while True:
        time.sleep(300)
        try:
            resp = requests.get(url, timeout=10)
            log.info("Keep-alive ping: %s → HTTP %d", url, resp.status_code)
        except Exception as exc:
            log.warning("Keep-alive ping failed: %s", exc)


if __name__ == "__main__":
    threading.Thread(target=_keep_alive, daemon=True, name="keep-alive").start()
    main()

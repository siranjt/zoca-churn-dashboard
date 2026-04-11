#!/usr/bin/env python3
"""
Zoca Churn Tool  (v3)
---------------------
Full-depth churn analyzer that builds an interactive Zoca-branded dashboard
backed by per-customer communication histories.

Outputs:
  /sessions/loving-vibrant-einstein/mnt/outputs/
    index.html          (dashboard, uses Zoca brand + logo)
    data/customers.json (compact customer metadata for main payload is inline
                         in index.html; this file is kept for completeness)
    data/comms/<entity_id>.json  (per-customer timeline + analytics, fetched
                                  on demand by the modal)
    zoca_logo.svg       (embedded via CSS)

Churn rule:
    A customer counts as churned only if they hold zero active-level
    subscriptions (active / non_renewing / in_trial / future / paused) at
    the customer level in Chargebee. Candidates come from BaseSheet
    churn_date and are re-validated each run.
"""

from __future__ import annotations

import base64
import csv
import io
import json
import os
import re
import shutil
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

CHARGEBEE_KEY = os.environ.get("CHARGEBEE_KEY") or "live_K26QwUdeX37fHKmMe1pkobqGOZ9jGHWF"
CHARGEBEE_SITE = "zoca"
CHARGEBEE_BASE = f"https://{CHARGEBEE_SITE}.chargebee.com/api/v2"

METABASE_TOKEN = os.environ.get("METABASE_TOKEN") or "mb_HMtn6VnGpYObdOeA7/W5IXEbExApEEWRW5E88bwTodE="

BASESHEET_URL = "https://metabase.zoca.ai/public/question/87763e8c-8084-442e-891a-df1b11e81b47.csv"

COMMS_URLS = {
    "app_chat":    "https://metabase.zoca.ai/public/question/10a52e37-04fa-4422-b840-803b66e033bf.csv",
    "email":       "https://metabase.zoca.ai/public/question/7a5aa1f6-9205-4e83-be51-3e585aa0f4a8.csv",
    "phone_call":  "https://metabase.zoca.ai/public/question/60797a27-c546-450d-b00b-a51b7e490143.csv",
    "video_call":  "https://metabase.zoca.ai/public/question/d95d9354-7c84-4a57-8af5-e700580c6ecb.csv",
    "sms":         "https://metabase.zoca.ai/public/question/bbaad2fb-5f9d-4249-af59-c7812851437c.csv",
}

ACTIVE_STATUSES = {"active", "non_renewing", "in_trial", "future", "paused"}

# Scope: only analyze churns from this date forward.
CHURN_SINCE = date(2026, 2, 1)
COMMS_HISTORY_DAYS = 120           # how far back to keep per-customer messages (covers Nov ramp-up)
COMMS_MESSAGE_CAP = 400            # cap per customer
BODY_TRUNCATE = 320                # cap per message body

# Paths can be overridden via env vars so the analyzer runs cleanly both
# inside the Cowork sandbox (default paths) and in GitHub Actions CI
# (where everything is relative to the checkout).
_DEFAULT_ROOT = Path("/sessions/loving-vibrant-einstein")
_ROOT = Path(os.environ.get("ZOCA_WORKDIR", str(_DEFAULT_ROOT)))
if not _ROOT.exists():
    _ROOT = Path.cwd()

OUTPUT_DIR = Path(os.environ.get("ZOCA_OUTPUT_DIR", str(_ROOT / "mnt" / "outputs")))
DATA_DIR = OUTPUT_DIR / "data"
COMMS_DIR = DATA_DIR / "comms"
CACHE_DIR = Path(os.environ.get("ZOCA_CACHE_DIR", str(_ROOT / "churn_cache")))
LOGO_SRC = Path(os.environ.get("ZOCA_LOGO_PATH", str(_ROOT / "zoca_logo.svg")))
TEMPLATE_PATH = Path(os.environ.get(
    "ZOCA_TEMPLATE_PATH", str(_ROOT / "churn_dashboard_template.html")
))

for d in (OUTPUT_DIR, DATA_DIR, COMMS_DIR, CACHE_DIR):
    d.mkdir(parents=True, exist_ok=True)

TODAY = datetime.now(timezone.utc).date()
# Back-compat alias — several helpers still refer to VALIDATE_CUTOFF.
VALIDATE_CUTOFF = CHURN_SINCE
DEFAULT_CUTOFF = CHURN_SINCE

STOPWORDS = {
    "the","a","an","and","or","but","is","are","was","were","be","been","being",
    "have","has","had","do","does","did","will","would","could","should","may",
    "might","must","can","this","that","these","those","i","you","he","she","it",
    "we","they","me","him","her","us","them","my","your","his","its","our","their",
    "to","of","in","on","at","for","with","by","from","as","into","about","up",
    "down","out","over","under","again","further","then","once","here","there",
    "when","where","why","how","all","any","both","each","few","more","most",
    "other","some","such","no","nor","not","only","own","same","so","than","too",
    "very","s","t","just","don","now","yes","hi","hello","thanks","thank","ok",
    "okay","hey","please","re","ve","ll","m","d","got","get","good","great",
    "team","zoca","like","let","know","one","two","back","also","sure","going",
    "need","want","take","make","made","day","days","week","message","sent",
    "received","call","email","number","said","say","time","really","actually",
    "bit","lot","thing","things","way","work","well","use","using","new","see",
    "today","tomorrow","yesterday","morning","evening","afternoon","night","yeah",
    "okk","k","ya","u","ur","plz","pls",
}

# ---------------------------------------------------------------------------
# Sentiment / intent keywords used by the churn-cause analysis
# ---------------------------------------------------------------------------

CANCEL_KEYWORDS = [
    "cancel", "cancellation", "cancelled", "cancelling", "terminate",
    "terminated", "termination", "discontinue", "discontinuing",
    "discontinued", "unsubscribe", "unsubscribed", "end the contract",
    "end contract", "end our contract", "end the subscription",
    "close the account", "close my account", "stop the service",
    "stop service", "no longer need", "no longer needed", "no longer interested",
    "don't want to continue", "dont want to continue", "not continuing",
    "won't be continuing", "wont be continuing", "cancel my subscription",
    "please cancel", "want to cancel", "need to cancel", "have to cancel",
    "request cancellation", "requesting cancellation", "shut down my account",
    "close down",
]

# Narrower + stronger complaint vocabulary. Removed broad terms like "issue",
# "problem", "error", "failed", "waiting for", "not getting" — those were
# generating false positives on operational messages ("no problem",
# "missed payment alert", "I'm still waiting for your response").
NEGATIVE_KEYWORDS = [
    "disappointed", "disappointing", "very unhappy", "unhappy with",
    "deeply frustrated", "extremely frustrated", "very frustrated",
    "angry", "upset with", "terrible", "awful", "horrible", "worst experience",
    "doesn't work", "doesnt work", "does not work", "not working at all",
    "completely broken", "useless", "waste of money", "waste of time",
    "unresponsive team", "no one is responding", "no one responds",
    "never heard back", "no reply from", "not happy with",
    "not satisfied", "dissatisfied", "doesn't help", "didn't help",
    "nothing is working", "not helpful at all", "poor service",
    "poor support", "bad service", "bad experience",
]

BILLING_KEYWORDS = [
    "card declined", "bank declined", "overcharged", "double charged",
    "double-charged", "didn't authorize", "didnt authorize",
    "ach failed", "ach declined", "payment failed", "chargeback",
    "dispute the charge", "disputing the charge", "money back",
    "refund my", "unauthorized charge", "unauthorized charges",
]

# Only explicit, unambiguous competitor language. Removed "alternative"
# (matched "alternative number"/"alternatively"), "going with" (matched
# "going with you"), and single-word "competitor" (matched product copy).
COMPETITOR_KEYWORDS = [
    "another agency", "different agency", "other agency",
    "switching to", "switch to another", "found another provider",
    "using another provider", "chose another", "went with another",
    "instead of zoca", "moving to another", "hired another agency",
    "new agency", "different marketing agency", "better agency",
    "replaced zoca",
]

# Results/ROI complaints — require clear client-side negative framing.
# Removed "dropped" (way too broad) and overly generic "no results".
RESULTS_COMPLAINT = [
    "not enough leads", "no new leads", "no new clients",
    "not getting clients", "not getting bookings",
    "no new bookings", "no new appointments", "no roi",
    "not worth it", "not worth the", "not seeing any value",
    "not seeing value", "don't see the value", "dont see the value",
    "not seeing results", "haven't seen results", "havent seen results",
    "no traffic", "not driving traffic", "no growth",
    "not generating", "no leads at all", "zero leads",
    "zero bookings", "zero results",
]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _log(msg: str) -> None:
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)

def http_get(url: str, headers: dict | None = None, timeout: int = 120) -> bytes:
    req = urllib.request.Request(url, headers=headers or {})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()

def chargebee_get(path: str, params: dict | None = None) -> dict:
    url = f"{CHARGEBEE_BASE}{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params, doseq=True)
    auth = base64.b64encode(f"{CHARGEBEE_KEY}:".encode()).decode()
    for attempt in range(4):
        try:
            body = http_get(url, headers={"Authorization": f"Basic {auth}"}, timeout=60)
            return json.loads(body)
        except urllib.error.HTTPError as e:
            if e.code in (429, 500, 502, 503, 504) and attempt < 3:
                time.sleep(1.5 * (attempt + 1))
                continue
            raise

def safe_float(v) -> float:
    try:
        return float(v or 0)
    except (TypeError, ValueError):
        return 0.0

def parse_date(s: str | None) -> date | None:
    if not s:
        return None
    s = s.strip()
    if not s:
        return None
    try:
        return datetime.fromisoformat(s[:19]).date()
    except ValueError:
        try:
            return datetime.strptime(s[:10], "%Y-%m-%d").date()
        except ValueError:
            return None

def month_key(d: date) -> str:
    return d.strftime("%Y-%m")

def months_between(a: date, b: date) -> int:
    return (b.year - a.year) * 12 + (b.month - a.month)

def classify_direction(channel: str, sender: str, member_type: str = "") -> str:
    """Return 'in' (client→Zoca) or 'out' (Zoca→client) or 'unknown'.

    Each Zoca comms channel uses a different sender convention:
      - email / sms ...... Sent_By_Client = in, Received_By_Client = out
      - phone_call ....... Initiated_By_Client = in, Initiated_By_Us = out
      - app_chat ......... Member Type column: User = in, Team Member = out
      - video_call ....... no sender recorded → unknown
    """
    s = (sender or "").strip()
    sl = s.lower()
    mt = (member_type or "").strip().lower()

    # 1) Member Type column (app_chat primary signal)
    if mt == "user":
        return "in"
    if mt in ("team member", "team", "agent", "bot", "system"):
        return "out"

    # 2) Channel-specific sender conventions
    if channel in ("email", "sms"):
        if s == "Sent_By_Client":
            return "in"
        if s == "Received_By_Client":
            return "out"

    if channel == "phone_call":
        if s == "Initiated_By_Client":
            return "in"
        if s == "Initiated_By_Us":
            return "out"

    # 3) Generic fallback
    if sl in ("user", "client", "customer"):
        return "in"
    if sl in ("team member", "team", "zoca", "agent", "bot", "system"):
        return "out"

    return "unknown"

def truncate(text: str, n: int = BODY_TRUNCATE) -> str:
    if not text:
        return ""
    t = text.replace("\r", " ").replace("\n", " ").strip()
    return t if len(t) <= n else t[:n] + "…"

# ---------------------------------------------------------------------------
# BaseSheet
# ---------------------------------------------------------------------------

def fetch_basesheet() -> list[dict]:
    cache = CACHE_DIR / "basesheet.csv"
    if cache.exists() and (time.time() - cache.stat().st_mtime) < 3600:
        data = cache.read_text()
    else:
        _log("Downloading BaseSheet…")
        data = http_get(BASESHEET_URL, headers={"Authorization": f"Bearer {METABASE_TOKEN}"}, timeout=180).decode(errors="replace")
        cache.write_text(data)
    rows = list(csv.DictReader(io.StringIO(data)))
    _log(f"BaseSheet: {len(rows)} rows")
    return rows

# ---------------------------------------------------------------------------
# Chargebee validation
# ---------------------------------------------------------------------------

def list_customer_subscriptions(customer_id: str) -> list[dict]:
    subs: list[dict] = []
    offset = None
    while True:
        params = {"customer_id[is]": customer_id, "limit": 100}
        if offset:
            params["offset"] = offset
        res = chargebee_get("/subscriptions", params)
        for item in res.get("list", []):
            subs.append(item["subscription"])
        offset = res.get("next_offset")
        if not offset:
            break
    return subs

def validate_churn(candidates: list[dict]) -> tuple[list[dict], list[dict]]:
    _log(f"Validating {len(candidates)} candidates against Chargebee…")
    churned: list[dict] = []
    retained: list[dict] = []

    def _check(row: dict) -> tuple[dict, list[dict]]:
        try:
            subs = list_customer_subscriptions(row["customer_id"].strip())
        except Exception as e:
            row["_cb_error"] = str(e)
            return row, []
        return row, subs

    with ThreadPoolExecutor(max_workers=8) as ex:
        futs = [ex.submit(_check, c) for c in candidates]
        done = 0
        for fut in as_completed(futs):
            row, subs = fut.result()
            done += 1
            if done % 50 == 0:
                _log(f"  validated {done}/{len(candidates)}")
            row["_sub_statuses"] = [s.get("status") for s in subs]
            row["_sub_count"] = len(subs)
            active = [s for s in subs if s.get("status") in ACTIVE_STATUSES]
            row["_active_sub_count"] = len(active)
            if active:
                retained.append(row)
            else:
                churned.append(row)

    _log(f"Confirmed churned: {len(churned)} | retained: {len(retained)}")
    return churned, retained

# ---------------------------------------------------------------------------
# Payment history (Chargebee — invoices + transactions + credit notes)
# ---------------------------------------------------------------------------

def _cb_list_all(path: str, params: dict, limit: int = 500) -> list[dict]:
    """Paginate a Chargebee list endpoint until exhausted or `limit` hit."""
    out: list[dict] = []
    p = dict(params)
    p.setdefault("limit", 100)
    offset = None
    while True:
        if offset:
            p["offset"] = offset
        res = chargebee_get(path, p)
        out.extend(res.get("list", []))
        offset = res.get("next_offset")
        if not offset or len(out) >= limit:
            break
    return out[:limit]


def _ts_iso(ts) -> str | None:
    if not ts:
        return None
    try:
        return datetime.utcfromtimestamp(int(ts)).strftime("%Y-%m-%d")
    except (TypeError, ValueError):
        return None


def fetch_customer_payment_history(customer_id: str) -> dict:
    """Fetch condensed Chargebee payment history for one customer.

    Returns a dict shaped for the dashboard modal:
      {
        customer_id, summary{}, monthly_paid[], signals[],
        invoices[], transactions[], subscriptions[],
      }
    Resilient — any API error is captured and returned under `error`.
    """
    out: dict = {
        "customer_id": customer_id,
        "summary": {},
        "monthly_paid": [],
        "signals": [],
        "invoices": [],
        "transactions": [],
        "subscriptions": [],
        "error": None,
    }
    try:
        # ---- Subscriptions (complete, including cancelled) ----
        subs_raw = _cb_list_all("/subscriptions", {"customer_id[is]": customer_id}, limit=50)
        subs = []
        for item in subs_raw:
            s = item.get("subscription", {}) or item
            subs.append({
                "id": s.get("id"),
                "status": s.get("status"),
                "plan_id": s.get("plan_id"),
                "plan_amount": (s.get("plan_amount") or 0) / 100.0,
                "mrr": (s.get("mrr") or s.get("plan_amount") or 0) / 100.0,
                "created_at": _ts_iso(s.get("created_at")),
                "started_at": _ts_iso(s.get("started_at")),
                "cancelled_at": _ts_iso(s.get("cancelled_at")),
                "cancel_reason": s.get("cancel_reason"),
                "cancel_reason_code": s.get("cancel_reason_code"),
                "auto_collection": s.get("auto_collection"),
                "billing_period_unit": s.get("billing_period_unit"),
            })
        out["subscriptions"] = subs

        # ---- Invoices (all statuses) ----
        invs_raw = _cb_list_all("/invoices", {"customer_id[is]": customer_id}, limit=300)
        invs = []
        for item in invs_raw:
            inv = item.get("invoice", {}) or item
            invs.append({
                "id": inv.get("id"),
                "status": inv.get("status"),
                "date": _ts_iso(inv.get("date")),
                "due_date": _ts_iso(inv.get("due_date")),
                "paid_at": _ts_iso(inv.get("paid_at")),
                "total": (inv.get("total") or 0) / 100.0,
                "amount_paid": (inv.get("amount_paid") or 0) / 100.0,
                "amount_due": (inv.get("amount_due") or 0) / 100.0,
                "subscription_id": inv.get("subscription_id"),
                "dunning_status": inv.get("dunning_status"),
            })
        out["invoices"] = invs

        # ---- Transactions (payments, failures, refunds) ----
        tx_raw = _cb_list_all("/transactions", {"customer_id[is]": customer_id}, limit=300)
        txs = []
        for item in tx_raw:
            tx = item.get("transaction", {}) or item
            txs.append({
                "id": tx.get("id"),
                "type": tx.get("type"),
                "status": tx.get("status"),
                "amount": (tx.get("amount") or 0) / 100.0,
                "date": _ts_iso(tx.get("date")),
                "payment_method": tx.get("payment_method"),
                "gateway": tx.get("gateway"),
                "error_code": tx.get("error_code"),
                "error_text": tx.get("error_text"),
            })
        out["transactions"] = txs

    except Exception as e:
        out["error"] = f"{type(e).__name__}: {e}"
        return out

    # ---- Derive summary ----
    paid = [i for i in invs if i["status"] == "paid"]
    unpaid = [i for i in invs if i["status"] in ("payment_due", "not_paid")]
    succ_tx = [t for t in txs if t["status"] == "success" and t["type"] == "payment"]
    fail_tx = [t for t in txs if t["status"] == "failure"]
    refund_tx = [t for t in txs if t["status"] == "success" and t["type"] == "refund"]

    lifetime_paid = sum(i["amount_paid"] for i in paid)
    outstanding = sum(i["amount_due"] for i in unpaid)
    refunded = sum(t["amount"] for t in refund_tx)

    # Avg days late: due_date → paid_at
    punct = []
    for i in paid:
        if i["due_date"] and i["paid_at"]:
            try:
                d1 = date.fromisoformat(i["due_date"])
                d2 = date.fromisoformat(i["paid_at"])
                punct.append((d2 - d1).days)
            except Exception:
                pass
    avg_days_late = round(sum(punct) / len(punct), 1) if punct else None

    # Oldest unpaid age
    oldest_unpaid = None
    for i in unpaid:
        if i["date"]:
            try:
                age = (TODAY - date.fromisoformat(i["date"])).days
                if oldest_unpaid is None or age > oldest_unpaid:
                    oldest_unpaid = age
            except Exception:
                pass

    last_success = max((t["date"] for t in succ_tx if t["date"]), default=None)
    last_failure = max((t["date"] for t in fail_tx if t["date"]), default=None)

    out["summary"] = {
        "lifetime_paid": round(lifetime_paid, 2),
        "lifetime_refunded": round(refunded, 2),
        "net_paid": round(lifetime_paid - refunded, 2),
        "outstanding_balance": round(outstanding, 2),
        "invoice_count": len(invs),
        "paid_invoice_count": len(paid),
        "unpaid_invoice_count": len(unpaid),
        "successful_payment_count": len(succ_tx),
        "failed_payment_count": len(fail_tx),
        "refund_count": len(refund_tx),
        "avg_days_to_pay": avg_days_late,
        "oldest_unpaid_age_days": oldest_unpaid,
        "first_invoice_date": min((i["date"] for i in invs if i["date"]), default=None),
        "last_invoice_date": max((i["date"] for i in invs if i["date"]), default=None),
        "last_successful_payment_date": last_success,
        "last_failed_payment_date": last_failure,
    }

    # ---- Monthly paid aggregation ----
    bkt: dict[str, dict] = defaultdict(lambda: {"paid": 0.0, "count": 0})
    for i in paid:
        if not i.get("paid_at"):
            continue
        m = i["paid_at"][:7]
        bkt[m]["paid"] += i["amount_paid"]
        bkt[m]["count"] += 1
    out["monthly_paid"] = [
        {"month": m, "paid": round(v["paid"], 2), "count": v["count"]}
        for m, v in sorted(bkt.items())
    ]

    # ---- Signals ----
    sigs: list[dict] = []
    s = out["summary"]
    if s["unpaid_invoice_count"] > 0:
        sigs.append({
            "severity": "high" if s["outstanding_balance"] >= 500 else "medium",
            "type": "outstanding_balance",
            "detail": f"${s['outstanding_balance']:.0f} across {s['unpaid_invoice_count']} unpaid invoice(s)" + (f"; oldest {s['oldest_unpaid_age_days']}d old" if s['oldest_unpaid_age_days'] is not None else ""),
        })
    if s["failed_payment_count"] >= 3:
        sigs.append({
            "severity": "high",
            "type": "repeated_payment_failures",
            "detail": f"{s['failed_payment_count']} failed payment attempts lifetime",
        })
    if s["avg_days_to_pay"] is not None and s["avg_days_to_pay"] >= 7:
        sigs.append({
            "severity": "medium",
            "type": "chronic_late_payer",
            "detail": f"Avg {s['avg_days_to_pay']}d past due before paying",
        })
    if s["refund_count"] > 0:
        sigs.append({
            "severity": "medium",
            "type": "refunds_issued",
            "detail": f"${s['lifetime_refunded']:.0f} refunded across {s['refund_count']} refund(s)",
        })
    # Trailing 90-day failures
    recent_fail = 0
    for t in txs:
        if t["status"] == "failure" and t.get("date"):
            try:
                age = (TODAY - date.fromisoformat(t["date"])).days
                if age <= 90:
                    recent_fail += 1
            except Exception:
                pass
    if recent_fail >= 2:
        sigs.append({
            "severity": "high",
            "type": "trailing_90d_failures",
            "detail": f"{recent_fail} failed payment(s) in last 90 days",
        })
    out["signals"] = sigs
    return out


def fetch_payment_histories(customer_ids: list[str], workers: int = 6) -> dict[str, dict]:
    """Parallel fetch of payment history for many customer IDs."""
    results: dict[str, dict] = {}
    if not customer_ids:
        return results
    _log(f"Fetching payment history for {len(customer_ids)} customer(s)…")
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futs = {ex.submit(fetch_customer_payment_history, cid): cid for cid in customer_ids}
        done = 0
        for fut in as_completed(futs):
            cid = futs[fut]
            try:
                results[cid] = fut.result()
            except Exception as e:
                results[cid] = {"customer_id": cid, "error": str(e), "summary": {}, "signals": [],
                                "invoices": [], "transactions": [], "subscriptions": [], "monthly_paid": []}
            done += 1
            if done % 25 == 0:
                _log(f"  payment history {done}/{len(customer_ids)}")
    _log(f"Payment history: fetched {len(results)}")
    return results


# ---------------------------------------------------------------------------
# Communications pipeline
# ---------------------------------------------------------------------------

def _download_comms_csv(channel: str, url: str) -> bytes | None:
    cache = CACHE_DIR / f"comms_{channel}.csv"
    if cache.exists() and (time.time() - cache.stat().st_mtime) < 3600:
        return cache.read_bytes()
    _log(f"Downloading comms [{channel}]…")
    try:
        data = http_get(url, headers={"Authorization": f"Bearer {METABASE_TOKEN}"}, timeout=300)
        cache.write_bytes(data)
        return data
    except Exception as e:
        _log(f"  failed: {e}")
        return None

def fetch_comms_detailed(churned_ids: set[str], active_ids: set[str]) -> tuple[dict, dict, dict]:
    """
    Returns:
        stats: {entity_id -> {last_contact, total_30d, total_90d, by_channel}}
        messages: {entity_id -> [{date, channel, direction, sender, body}, …]}
                  (only for churned_ids, sorted desc, capped)
        targets: set of all entity_ids observed
    """
    stats: dict[str, dict] = defaultdict(lambda: {
        "last_contact": None, "total_30d": 0, "total_90d": 0,
        "by_channel": defaultdict(int),
    })
    messages: dict[str, list[dict]] = defaultdict(list)

    all_ids = churned_ids | active_ids
    cutoff_30 = TODAY - timedelta(days=30)
    cutoff_90 = TODAY - timedelta(days=90)
    cutoff_history = TODAY - timedelta(days=COMMS_HISTORY_DAYS)

    for channel, url in COMMS_URLS.items():
        data = _download_comms_csv(channel, url)
        if not data:
            continue
        reader = csv.DictReader(io.StringIO(data.decode(errors="replace")))
        if not reader.fieldnames:
            continue
        date_col = next((n for n in ("Created At","created_at","Created_At") if n in reader.fieldnames), None)
        ent_col = next((n for n in ("Entity ID","entity_id","Entity_ID") if n in reader.fieldnames), None)
        body_col = next((n for n in ("Message Body","message_body","Message_Body") if n in reader.fieldnames), None)
        sender_col = next((n for n in ("Sender","sender") if n in reader.fieldnames), None)
        member_col = next((n for n in ("Member Type","member_type","Member_Type") if n in reader.fieldnames), None)
        if not date_col or not ent_col:
            _log(f"  skip {channel}: missing cols {reader.fieldnames}")
            continue

        matched = 0
        kept_messages = 0
        for row in reader:
            eid = (row.get(ent_col) or "").strip()
            if eid not in all_ids:
                continue
            d = parse_date(row.get(date_col) or "")
            if not d:
                continue

            rec = stats[eid]
            if rec["last_contact"] is None or d > rec["last_contact"]:
                rec["last_contact"] = d
            if d >= cutoff_90:
                rec["total_90d"] += 1
                rec["by_channel"][channel] += 1
            if d >= cutoff_30:
                rec["total_30d"] += 1
            matched += 1

            # For churned customers, keep full message record
            if eid in churned_ids and d >= cutoff_history:
                sender = row.get(sender_col) if sender_col else ""
                member_type = row.get(member_col) if member_col else ""
                body = row.get(body_col) if body_col else ""
                messages[eid].append({
                    "date": d.isoformat(),
                    "channel": channel,
                    "direction": classify_direction(channel, sender or "", member_type or ""),
                    "sender": (sender or "")[:60],
                    "body": truncate(body or "", BODY_TRUNCATE),
                })
                kept_messages += 1
        _log(f"  {channel}: matched {matched} (kept {kept_messages} messages)")

    # Cap + sort per entity
    for eid, lst in messages.items():
        lst.sort(key=lambda m: m["date"], reverse=True)
        if len(lst) > COMMS_MESSAGE_CAP:
            del lst[COMMS_MESSAGE_CAP:]

    # Convert stats to plain
    stats_out = {}
    for eid, rec in stats.items():
        stats_out[eid] = {
            "last_contact": rec["last_contact"].isoformat() if rec["last_contact"] else None,
            "total_90d": rec["total_90d"],
            "total_30d": rec["total_30d"],
            "by_channel": dict(rec["by_channel"]),
        }

    return stats_out, dict(messages), all_ids


# ---------------------------------------------------------------------------
# Per-customer communications analytics
# ---------------------------------------------------------------------------

WORD_RE = re.compile(r"[A-Za-z][A-Za-z']{2,}")

def compute_customer_comms_analytics(customer: dict, messages: list[dict]) -> dict:
    """
    Given all messages for a churned customer (desc-sorted), compute:
      - days_silent_at_churn
      - longest_gap_before_churn (days)
      - inbound / outbound counts in 90d before churn
      - dominant_channel in 90d before churn
      - weekly volumes for 13 weeks before churn (list of ints, week 0 = most recent)
      - decay_pct (recent 4 weeks avg vs older 8 weeks avg)
      - top_keywords (from last 30 inbound messages, simple term freq)
      - last_inbound_snippet
    """
    cd = parse_date(customer.get("churn_date"))
    today = cd or TODAY

    analytics: dict = {
        "days_silent_at_churn": None,
        "longest_gap_90d": None,
        "inbound_90d": 0,
        "outbound_90d": 0,
        "dominant_channel_90d": None,
        "weekly_volumes": [0] * 14,  # week 0 closest to churn
        "decay_pct": None,
        "top_keywords": [],
        "last_inbound_snippet": None,
        "last_inbound_date": None,
        "last_inbound_channel": None,
        "message_count_total": len(messages),
    }
    if not messages:
        return analytics

    msg_dates = [parse_date(m["date"]) for m in messages]
    msg_dates = [d for d in msg_dates if d is not None]

    if msg_dates:
        latest = max(msg_dates)
        analytics["days_silent_at_churn"] = (today - latest).days

    # Messages in 90 days before churn
    window_start = today - timedelta(days=90)
    in_window = []
    for m, d in zip(messages, msg_dates):
        if d and window_start <= d <= today:
            in_window.append((m, d))

    if in_window:
        # inbound/outbound
        by_channel: Counter = Counter()
        for m, d in in_window:
            if m["direction"] == "in":
                analytics["inbound_90d"] += 1
            elif m["direction"] == "out":
                analytics["outbound_90d"] += 1
            by_channel[m["channel"]] += 1
        if by_channel:
            analytics["dominant_channel_90d"] = by_channel.most_common(1)[0][0]

        # weekly volumes
        for m, d in in_window:
            wk = (today - d).days // 7
            if 0 <= wk < 14:
                analytics["weekly_volumes"][wk] += 1

        recent = sum(analytics["weekly_volumes"][0:4])
        older = sum(analytics["weekly_volumes"][4:12])
        if older > 0:
            analytics["decay_pct"] = round((recent / 4 - older / 8) / (older / 8) * 100, 1)

        # longest gap in 90d window
        sorted_dates = sorted({d for _, d in in_window})
        if len(sorted_dates) >= 2:
            gaps = [(sorted_dates[i+1] - sorted_dates[i]).days for i in range(len(sorted_dates)-1)]
            analytics["longest_gap_90d"] = max(gaps)
        else:
            analytics["longest_gap_90d"] = (today - sorted_dates[0]).days if sorted_dates else 90

    # Last inbound
    for m in messages:  # already desc
        if m["direction"] == "in" and m.get("body"):
            analytics["last_inbound_snippet"] = m["body"][:240]
            analytics["last_inbound_date"] = m["date"]
            analytics["last_inbound_channel"] = m["channel"]
            break

    # Top keywords from last 30 inbound bodies
    inbound_bodies = [m["body"] for m in messages if m["direction"] == "in" and m.get("body")][:30]
    words = Counter()
    for body in inbound_bodies:
        for tok in WORD_RE.findall(body.lower()):
            if tok in STOPWORDS:
                continue
            if len(tok) < 4:
                continue
            words[tok] += 1
    analytics["top_keywords"] = [w for w, _ in words.most_common(12)]

    return analytics


# ---------------------------------------------------------------------------
# Churn cause analysis — turns raw comms into a structured diagnosis
# ---------------------------------------------------------------------------

_WORD_BOUNDARY_CACHE: dict[tuple, object] = {}

def _contains_any(text: str, needles: list[str]) -> str | None:
    """Return the first matching needle, or None.

    Matches with word boundaries so "alternative" does not match "alternatively"
    and "going with" does not match "going with you". Multi-word needles are
    matched as a phrase with boundaries at both ends.
    """
    if not text:
        return None
    key = tuple(needles)
    rx = _WORD_BOUNDARY_CACHE.get(key)
    if rx is None:
        parts = []
        for n in needles:
            escaped = re.escape(n)
            parts.append(rf"\b{escaped}\b")
        rx = re.compile("|".join(parts), re.IGNORECASE)
        _WORD_BOUNDARY_CACHE[key] = rx
    m = rx.search(text)
    return m.group(0).lower() if m else None


def analyze_response_times(messages: list[dict]) -> dict:
    """
    Measure how quickly Zoca responded to inbound client messages.

    Dates are day-resolution only, so we report in days. For every inbound
    message we look forward for the next outbound within 14 days. Anything
    with no outbound response in 5+ days counts as "ignored".
    """
    asc = sorted(
        [m for m in messages if m.get("date")],
        key=lambda m: m["date"],
    )
    gaps: list[int] = []
    ignored: list[dict] = []
    for i, m in enumerate(asc):
        if m.get("direction") != "in":
            continue
        m_date = parse_date(m["date"])
        if not m_date:
            continue
        responded = False
        for j in range(i + 1, len(asc)):
            n = asc[j]
            n_date = parse_date(n["date"])
            if not n_date:
                continue
            delta = (n_date - m_date).days
            if delta > 14:
                break
            if n.get("direction") == "out":
                gaps.append(delta)
                responded = True
                break
        if not responded:
            # No outbound response within 14 days — count as ignored only if
            # the gap to "today" (or next outbound beyond 14d) is meaningful.
            next_out = None
            for j in range(i + 1, len(asc)):
                if asc[j].get("direction") == "out":
                    next_out = parse_date(asc[j]["date"])
                    break
            eff_gap = (next_out - m_date).days if next_out else 30
            if eff_gap >= 5:
                ignored.append({
                    "date": m["date"],
                    "channel": m.get("channel"),
                    "snippet": (m.get("body") or "")[:240],
                    "gap_days": eff_gap,
                })

    gaps.sort()
    median = gaps[len(gaps) // 2] if gaps else None
    mx = gaps[-1] if gaps else None
    avg = round(sum(gaps) / len(gaps), 1) if gaps else None

    return {
        "median_days": median,
        "max_days": mx,
        "avg_days": avg,
        "sample_count": len(gaps),
        "ignored_count": len(ignored),
        "ignored_examples": ignored[:3],
    }


def detect_critical_signals(customer: dict, messages: list[dict]) -> list[dict]:
    """
    Extract timestamped signals from a customer's history. Each signal
    carries enough context to be rendered in the dashboard timeline.
    """
    cd = parse_date(customer.get("churn_date"))
    asc = sorted(
        [m for m in messages if m.get("date")],
        key=lambda m: m["date"],
    )
    signals: list[dict] = []

    def days_before(d: date | None) -> int | None:
        return (cd - d).days if (cd and d) else None

    # Complaint-style signals only fire on client-authored (inbound) messages
    # so Zoca's own outbound apologies / operational alerts don't register
    # as client complaints. We also count inbound matches for an intensity
    # score that the classifier can use.
    neg_hits = 0
    results_hits = 0
    competitor_hits = 0

    # --- First negative sentiment (inbound only) ---
    for m in asc:
        if m.get("direction") != "in":
            continue
        body = m.get("body") or ""
        hit = _contains_any(body, NEGATIVE_KEYWORDS)
        if hit:
            neg_hits += 1
            if not any(s["type"] == "negative_sentiment_first" for s in signals):
                d = parse_date(m["date"])
                signals.append({
                    "type": "negative_sentiment_first",
                    "date": m["date"],
                    "channel": m.get("channel"),
                    "direction": "in",
                    "keyword": hit,
                    "snippet": body[:240],
                    "days_before_churn": days_before(d),
                })

    # --- Explicit cancellation request (inbound only) ---
    for m in asc:
        if m.get("direction") != "in":
            continue
        body = m.get("body") or ""
        hit = _contains_any(body, CANCEL_KEYWORDS)
        if hit:
            d = parse_date(m["date"])
            signals.append({
                "type": "cancellation_request",
                "date": m["date"],
                "channel": m.get("channel"),
                "direction": "in",
                "keyword": hit,
                "snippet": body[:240],
                "days_before_churn": days_before(d),
            })
            break

    # --- Results complaint ("no leads", "no results") — inbound only ---
    for m in asc:
        if m.get("direction") != "in":
            continue
        body = m.get("body") or ""
        hit = _contains_any(body, RESULTS_COMPLAINT)
        if hit:
            results_hits += 1
            if not any(s["type"] == "results_complaint" for s in signals):
                d = parse_date(m["date"])
                signals.append({
                    "type": "results_complaint",
                    "date": m["date"],
                    "channel": m.get("channel"),
                    "direction": "in",
                    "keyword": hit,
                    "snippet": body[:240],
                    "days_before_churn": days_before(d),
                })

    # --- Competitive switch mention (inbound only) ---
    for m in asc:
        if m.get("direction") != "in":
            continue
        body = m.get("body") or ""
        hit = _contains_any(body, COMPETITOR_KEYWORDS)
        if hit:
            competitor_hits += 1
            if not any(s["type"] == "competitive_mention" for s in signals):
                d = parse_date(m["date"])
                signals.append({
                    "type": "competitive_mention",
                    "date": m["date"],
                    "channel": m.get("channel"),
                    "direction": "in",
                    "keyword": hit,
                    "snippet": body[:240],
                    "days_before_churn": days_before(d),
                })

    # Stash intensity counts on the customer dict for the classifier
    customer["_neg_hits"] = neg_hits
    customer["_results_hits"] = results_hits
    customer["_competitor_hits"] = competitor_hits

    # --- Longest silence (≥21d) before churn ---
    if len(asc) >= 2:
        best = None
        for i in range(1, len(asc)):
            a = parse_date(asc[i - 1]["date"])
            b = parse_date(asc[i]["date"])
            if not a or not b:
                continue
            gap = (b - a).days
            if cd and a > cd:  # only count gaps up to the churn date
                continue
            if not best or gap > best[0]:
                best = (gap, asc[i - 1], asc[i])
        if best and best[0] >= 21:
            d = parse_date(best[1]["date"])
            signals.append({
                "type": "long_silence",
                "date": best[1]["date"],
                "end_date": best[2]["date"],
                "gap_days": best[0],
                "last_msg_before": (best[1].get("body") or "")[:240],
                "channel": best[1].get("channel"),
                "days_before_churn": days_before(d),
            })

    # --- Missed payments ---
    if customer.get("missed_m0", 0) > 0:
        signals.append({
            "type": "missed_payment_current",
            "amount": customer["missed_m0"],
            "label": "M0 (current month)",
        })
    if customer.get("missed_m1", 0) > 0:
        signals.append({
            "type": "missed_payment_prev",
            "amount": customer["missed_m1"],
            "label": "M-1",
        })

    # --- Unresolved support tickets ---
    if customer.get("unresolved_issues", 0) > 0:
        signals.append({
            "type": "unresolved_tickets",
            "count": customer["unresolved_issues"],
            "label": f"{customer['unresolved_issues']} unresolved in last 30d",
        })

    return signals


def classify_primary_cause(
    customer: dict, messages: list[dict], signals: list[dict], analytics: dict,
) -> str:
    """
    Assign a primary cause from a fixed taxonomy. Priority matters — earlier
    rules win. Keep this deterministic so the narrative matches the label.

    Signal quality rules:
      * Complaint-type signals are counted only on inbound messages.
      * Negative sentiment is classified as `service_complaint` only when the
        client surfaced it at least twice, OR once combined with an unresolved
        ticket. A single stray match is treated as noise.
    """
    has_missed = (
        (customer.get("missed_m0") or 0) > 0
        or (customer.get("missed_m1") or 0) > 0
        or (customer.get("missed_m2") or 0) > 0
    )
    has_cancel = any(s["type"] == "cancellation_request" for s in signals)
    has_negative = any(s["type"] == "negative_sentiment_first" for s in signals)
    has_results_complaint = any(s["type"] == "results_complaint" for s in signals)
    has_competitor = any(s["type"] == "competitive_mention" for s in signals)
    unresolved = customer.get("unresolved_issues", 0) > 0

    neg_hits = customer.get("_neg_hits", 0) or 0
    results_hits = customer.get("_results_hits", 0) or 0
    competitor_hits = customer.get("_competitor_hits", 0) or 0

    days_silent = analytics.get("days_silent_at_churn")
    inb = analytics.get("inbound_90d", 0) or 0
    outb = analytics.get("outbound_90d", 0) or 0
    tenure = customer.get("tenure_days", 0) or 0
    msg_count = analytics.get("message_count_total", 0) or 0

    # 1. Explicit cancellation request — the gold signal
    if has_cancel:
        return "explicit_cancellation"

    # 2. Results / ROI failure — client said "no leads / no bookings / no ROI"
    #    in their own words. This ranks above generic negative sentiment.
    if has_results_complaint and results_hits >= 1:
        return "results_failure"

    # 3. Service complaint — at least one client-authored negative message.
    #    With word-boundary matching + direction filtering, a single hit is
    #    a much stronger signal than before. Noise is acceptable here because
    #    "service_complaint" is an actionable bucket, not a penalty.
    if has_negative:
        return "service_complaint"

    # 4. Competitive switch — requires an unambiguous client-authored mention
    if has_competitor and competitor_hits >= 1:
        return "competitive_switch"

    # 5. Billing breakdown — real missed payments on record
    if has_missed:
        return "billing_breakdown"

    # 6. Ghost churn — no comms, or only a couple of outbound Zoca pings with
    #    zero client response. Functionally the customer was invisible.
    if msg_count == 0 or (msg_count <= 5 and inb == 0):
        return "ghost_churn"

    # 7. Silent drift — was talking, then went quiet for 30+ days before churn
    if days_silent is not None and days_silent >= 30:
        return "silent_drift"

    # 8. Reactive fade — Zoca kept reaching out, client stopped replying.
    #    Loosened from the original (outb>=3, inb<=1) to catch volume-ratio
    #    fades where the client went from engaged to barely responsive.
    if outb >= 5 and (inb == 0 or outb >= inb * 3):
        return "reactive_fade"

    # 9. Expectation gap — short-tenure customer with low engagement
    if tenure < 90 and msg_count < 15:
        return "expectation_gap"

    return "unknown"


CAUSE_LABELS = {
    "explicit_cancellation": "Explicit cancellation",
    "results_failure":       "Results / service failure",
    "service_complaint":     "Service complaint",
    "competitive_switch":    "Competitive switch",
    "billing_breakdown":     "Billing breakdown",
    "ghost_churn":           "Ghost churn (no touchpoints)",
    "expectation_gap":       "Expectation gap (early tenure)",
    "silent_drift":          "Silent drift",
    "reactive_fade":         "Reactive fade (one-way outreach)",
    "unknown":               "Unclassified",
}


def assess_preventability(
    cause: str, signals: list[dict], response_stats: dict, analytics: dict,
) -> tuple[str, int]:
    """
    Return (tier, score 0-100). High = Zoca had clear, actionable signals.
    Low = the churn would have been difficult to prevent given what was visible.
    """
    score = 0

    # Base by cause
    base = {
        "explicit_cancellation": 55,
        "results_failure":       80,
        "service_complaint":     70,
        "billing_breakdown":     65,
        "silent_drift":          60,
        "reactive_fade":         45,
        "expectation_gap":       50,
        "competitive_switch":    20,
        "ghost_churn":           15,
        "unknown":               35,
    }
    score += base.get(cause, 30)

    # Bonuses for clearly-actionable evidence
    if response_stats.get("ignored_count", 0) >= 1:
        score += 10
    if response_stats.get("median_days") is not None and response_stats["median_days"] >= 3:
        score += 8

    if any(s["type"] == "cancellation_request" and (s.get("days_before_churn") or 0) >= 7 for s in signals):
        score += 10  # We had a week's warning
    if any(s["type"] == "long_silence" and s.get("gap_days", 0) >= 30 for s in signals):
        score += 5

    score = max(0, min(100, score))
    if score >= 70:
        tier = "High"
    elif score >= 40:
        tier = "Medium"
    else:
        tier = "Low"
    return tier, score


def find_turning_point(signals: list[dict]) -> dict | None:
    dated = [s for s in signals if s.get("date") and s["type"] in
             ("cancellation_request", "negative_sentiment_first",
              "results_complaint", "competitive_mention", "long_silence")]
    if not dated:
        return None
    dated.sort(key=lambda s: s["date"])
    return dated[0]


def generate_narrative(
    customer: dict, cause: str, analytics: dict,
    signals: list[dict], response_stats: dict,
) -> str:
    biz = customer.get("biz_name") or "This customer"
    cd = customer.get("churn_date") or "an unknown date"
    tenure = customer.get("tenure_days", 0) or 0
    silent = analytics.get("days_silent_at_churn")
    inb = analytics.get("inbound_90d", 0) or 0
    outb = analytics.get("outbound_90d", 0) or 0
    msgs = analytics.get("message_count_total", 0) or 0

    parts = [f"{biz} churned on {cd} after {tenure} days with Zoca."]

    tp = find_turning_point(signals)
    if tp:
        ch = tp.get("channel") or "—"
        when = tp.get("date")
        dbc = tp.get("days_before_churn")
        if tp["type"] == "cancellation_request":
            parts.append(
                f"They sent an explicit cancellation request on {when} via {ch}"
                + (f" — {dbc} days before churn." if dbc is not None else ".")
            )
        elif tp["type"] == "negative_sentiment_first":
            parts.append(
                f"Sentiment turned negative on {when} ({ch}) "
                f"— first complaint keyword: \"{tp.get('keyword','')}\"."
            )
        elif tp["type"] == "results_complaint":
            parts.append(
                f"On {when} they raised a results concern "
                f"(\"{tp.get('keyword','')}\"), which was never fully resolved."
            )
        elif tp["type"] == "competitive_mention":
            parts.append(
                f"On {when} they mentioned an alternative provider "
                f"(\"{tp.get('keyword','')}\")."
            )
        elif tp["type"] == "long_silence":
            parts.append(
                f"Conversation collapsed into a {tp.get('gap_days')}-day silence "
                f"starting {when}."
            )

    if cause == "results_failure":
        parts.append("Classification: results/service failure — the client raised substantive complaints that were either unanswered or unresolved.")
    elif cause == "service_complaint":
        parts.append("Classification: service complaint. Negative signals appeared but no explicit cancellation request.")
    elif cause == "billing_breakdown":
        missed_bits = []
        for k, label in (("missed_m0","M0"),("missed_m1","M-1"),("missed_m2","M-2"),("missed_m3","M-3")):
            v = customer.get(k) or 0
            if v > 0:
                missed_bits.append(f"{label}=${int(v)}")
        parts.append(
            f"Classification: billing breakdown — payment failures ({', '.join(missed_bits)}) drove the cancellation."
            if missed_bits else "Classification: billing breakdown."
        )
    elif cause == "silent_drift":
        parts.append(
            f"Classification: silent drift — {silent} days silent at churn, "
            f"{inb} inbound vs {outb} outbound in the last 90d. No complaint on record; engagement simply faded."
        )
    elif cause == "ghost_churn":
        parts.append(
            "Classification: ghost churn. Zero communication on record in the comms window "
            "before churn — the customer was invisible long before the formal cancellation."
        )
    elif cause == "reactive_fade":
        parts.append(
            f"Classification: reactive fade — Zoca reached out {outb} times, but the client only replied {inb}. "
            "A one-sided monologue in the weeks before churn."
        )
    elif cause == "expectation_gap":
        parts.append(
            f"Classification: expectation gap. Early-tenure churn ({tenure}d) with concerns raised "
            "before the relationship stabilized — classic onboarding mismatch."
        )
    elif cause == "competitive_switch":
        parts.append("Classification: competitive switch. The client mentioned an alternative provider before cancelling.")
    elif cause == "explicit_cancellation":
        parts.append("Classification: explicit cancellation. The client formally asked to cancel; the question is whether a save attempt was made.")

    if response_stats.get("ignored_count", 0) >= 1:
        parts.append(
            f"{response_stats['ignored_count']} inbound message(s) went unanswered for 5+ days — "
            "this is the clearest operational failure on Zoca's side."
        )
    if response_stats.get("median_days") is not None and response_stats["median_days"] >= 3:
        parts.append(
            f"Median Zoca response time was {response_stats['median_days']:.1f} days, above the 24-hour expectation."
        )

    if not msgs and cause != "ghost_churn":
        parts.append("No communication history could be matched for this customer in the current comms dataset.")

    return " ".join(parts)


def generate_recommendations(
    customer: dict, cause: str, analytics: dict,
    signals: list[dict], response_stats: dict,
) -> list[str]:
    recs: list[str] = []

    def add(tag: str, text: str):
        recs.append(f"[{tag}] {text}")

    # Cause-specific playbook
    if cause == "explicit_cancellation":
        cs = next((s for s in signals if s["type"] == "cancellation_request"), None)
        if cs and (cs.get("days_before_churn") or 0) >= 3:
            add("Retention", f"Cancellation was signalled {cs['days_before_churn']} day(s) before churn via {cs.get('channel','—')}. Trigger an AM save call within 4 hours of any cancellation keyword — not a support response.")
        else:
            add("Retention", "Implement a 'cancellation keyword' realtime alert to AMs + Growth team. Today this signal is discovered only post-churn.")
        add("Offer", "Build a 3-tier retention offer ladder (pause / discount / scope change) so AMs have something concrete to counter with.")

    if cause == "results_failure":
        add("Product", "Customer raised results concerns (leads/bookings/ROI) — this is the highest-ROI churn to prevent. Establish a weekly 'performance check-in' for any customer whose core metric drops 20% vs prior 4 weeks.")
        add("Escalation", "Results complaints should auto-escalate to SP + AM within 24h with a written action plan shared back to the client.")

    if cause == "service_complaint":
        first = next((s for s in signals if s["type"] == "negative_sentiment_first"), None)
        if first:
            add("Escalation", f"First negative sentiment on {first['date']} via {first.get('channel','—')}. Triggering a same-day AM touchpoint on any negative keyword would have caught this.")
        add("Sentiment", "Add an automated sentiment alerting layer over app_chat/email that pages the AM when negative keywords appear.")
        if customer.get("unresolved_issues", 0) > 0:
            add("SLA", f"{customer['unresolved_issues']} unresolved ticket(s) at churn. Enforce a hard SLA: any ticket open >5 days auto-escalates to the team lead.")

    if cause == "billing_breakdown":
        add("Billing ops", "Run a payment-recovery sequence automatically within 48h of first dropped payment: email → SMS → call → AM outreach with offer.")
        add("Dunning", "A missed M0 alone isn't the churn cause — the absence of a recovery conversation is. Instrument the sequence and track recovery rate.")

    if cause == "silent_drift":
        add("Re-engagement", "Trigger automated re-engagement playbook when silence crosses 21 days. This customer was already past that threshold with no outreach logged.")
        add("Health score", "Silent drift is the most predictable churn type. Build an engagement-health score and alert AMs weekly on the bottom decile.")

    if cause == "reactive_fade":
        add("Engagement", "One-way outreach is a warning, not a save. Cap outreach at 5 attempts if no reply, then switch to a different channel or a different messenger (SP → AM → team lead) to break the pattern.")

    if cause == "ghost_churn":
        add("Onboarding", "Zero touchpoints in the comms window means the customer was effectively unowned. Audit onboarding handoff — how did this customer slip through the daily/weekly check routines?")
        add("Health score", "Define a minimum-contact SLA (e.g., ≥1 touchpoint every 14 days) and alert on violations.")

    if cause == "expectation_gap":
        add("Onboarding", "Early-tenure churn is an onboarding signal, not an account-management signal. Review kickoff content and the 30/60/90 day check-in for this customer's lead source segment.")

    if cause == "competitive_switch":
        comp = next((s for s in signals if s["type"] == "competitive_mention"), None)
        if comp:
            add("Competitive", f"Client mentioned a competitor on {comp['date']} — log this to Product + Sales for competitive positioning work.")

    # Operational hygiene bonuses (apply to all causes)
    if response_stats.get("ignored_count", 0) >= 1:
        add("SLA", f"{response_stats['ignored_count']} inbound message(s) went unanswered for 5+ days. Enforce a hard rule: every inbound gets a human response within 24h, every day of the week.")
        for ig in response_stats.get("ignored_examples", [])[:2]:
            add("SLA example", f"On {ig.get('date')} via {ig.get('channel')}, client wrote: \"{ig.get('snippet','')[:120]}…\" — no outbound response in {ig.get('gap_days')} days.")
    if response_stats.get("median_days") is not None and response_stats["median_days"] >= 3:
        add("SLA", f"Median response was {response_stats['median_days']:.1f} days. Target: <24h.")

    if not recs:
        add("Audit", "No single smoking gun. Worth a manual review to find non-obvious signals outside this data pipeline (Slack, account notes, AM memory).")

    return recs


def analyze_customer_churn_cause(customer: dict, messages: list[dict]) -> dict:
    """Run the full cause-analysis pipeline on one churned customer."""
    analytics = customer.get("comms_analytics") or {}
    response_stats = analyze_response_times(messages)
    signals = detect_critical_signals(customer, messages)
    cause = classify_primary_cause(customer, messages, signals, analytics)
    tier, prev_score = assess_preventability(cause, signals, response_stats, analytics)
    turning = find_turning_point(signals)
    narrative = generate_narrative(customer, cause, analytics, signals, response_stats)
    recommendations = generate_recommendations(customer, cause, analytics, signals, response_stats)
    return {
        "primary_cause": cause,
        "primary_cause_label": CAUSE_LABELS.get(cause, cause),
        "preventability_tier": tier,
        "preventability_score": prev_score,
        "turning_point": turning,
        "signals": signals,
        "response_stats": response_stats,
        "narrative": narrative,
        "recommendations": recommendations,
    }


# ---------------------------------------------------------------------------
# Customer row transform
# ---------------------------------------------------------------------------

def slim_customer(row: dict) -> dict:
    fpd = parse_date(row.get("first_payment_date"))
    cd = parse_date(row.get("churn_date"))
    return {
        "entity_id": (row.get("entity_id") or "").strip(),
        "biz_name": row.get("bizname") or "",
        "location_name": row.get("location_name") or "",
        "am": (row.get("am_name") or "").strip() or "Unassigned",
        "ae": (row.get("ae_name") or "").strip() or "Unassigned",
        "sp": (row.get("sp_name") or "").strip(),
        "state": (row.get("state") or "").strip() or "Unknown",
        "country": row.get("country") or "",
        "locality": row.get("locality") or "",
        "category": (row.get("primary_category") or "").strip() or "Unknown",
        "lead_source": (row.get("lead_source_group") or "").strip() or "Unknown",
        "lead_source_detail": row.get("lead_source") or "",
        "first_payment_date": fpd.isoformat() if fpd else None,
        "first_paid_month": row.get("first_paid_month") or "",
        "churn_date": cd.isoformat() if cd else None,
        "churn_month": row.get("churn_month") or "",
        "reason_category": row.get("reason_category") or "",
        "detailed_reason": row.get("detailed_reason") or "",
        "mrr": safe_float(row.get("total_monthly_revenue")),
        "tenure_days": int(safe_float(row.get("revenue_duration_in_days"))),
        "chrone_status": row.get("chrone_zoca_status") or "",
        "customer_id": (row.get("customer_id") or "").strip(),
        "missed_m0": safe_float(row.get("M0 Missed Payment")),
        "missed_m1": safe_float(row.get("M-1 Missed Payment")),
        "missed_m2": safe_float(row.get("M-2 Missed Payment")),
        "missed_m3": safe_float(row.get("M-3 Missed Payment")),
        "churn_potential_status": row.get("churn_potential_status") or "",
        "churn_potential_notes": row.get("churn_potential_notes") or "",
        "unresolved_issues": int(safe_float(row.get("unresolved_issues_last_30_days"))),
        "total_issues": int(safe_float(row.get("total_issues_last_30_days"))),
        "open_tickets": int(safe_float(row.get("open_tickets_last_30_days"))),
        "last_comms_date": row.get("last_comms_date") or "",
        "phone_number": row.get("phone_number") or "",
        "app_email": row.get("app_email") or "",
        "gbp_email": row.get("gbp_email") or "",
        "churn_potential_month": row.get("churn_potential_month") or "",
        "place_id": (row.get("place_id") or "").strip(),
        "map_link": (row.get("map_link") or "").strip(),
    }


def compute_at_risk_score(cust: dict, comms_stats: dict) -> dict:
    score = 0
    signals: list[str] = []

    if cust["missed_m0"] > 0:
        score += 4
        signals.append(f"M0 missed (${int(cust['missed_m0'])})")
    if cust["missed_m1"] > 0:
        score += 3
        signals.append("M-1 missed")
    if cust["missed_m2"] > 0:
        score += 2
        signals.append("M-2 missed")
    if cust["missed_m3"] > 0:
        score += 1
        signals.append("M-3 missed")

    cps = (cust.get("churn_potential_status") or "").upper()
    if cps == "CONFIRMED":
        score += 3
        signals.append("Churn potential: CONFIRMED")
    elif cps == "SUBSCRIPTION_STOPPED":
        score += 5
        signals.append("Subscription stopped")

    if cust["unresolved_issues"] > 0:
        bump = min(cust["unresolved_issues"], 3)
        score += bump
        signals.append(f"{cust['unresolved_issues']} unresolved issue(s)")

    last_contact = None
    rec = comms_stats.get(cust["entity_id"])
    if rec and rec.get("last_contact"):
        last_contact = parse_date(rec["last_contact"])
    elif cust.get("last_comms_date"):
        last_contact = parse_date(cust["last_comms_date"])

    if last_contact is None:
        score += 3
        signals.append("No comm on record")
    else:
        gap = (TODAY - last_contact).days
        if gap >= 90:
            score += 3; signals.append(f"Silent {gap}d")
        elif gap >= 45:
            score += 2; signals.append(f"Silent {gap}d")
        elif gap >= 30:
            score += 1; signals.append(f"Silent {gap}d")

    if score >= 6:
        tier = "High"
    elif score >= 3:
        tier = "Medium"
    elif score >= 1:
        tier = "Low"
    else:
        tier = "None"

    return {"score": score, "signals": signals, "tier": tier,
            "last_contact": last_contact.isoformat() if last_contact else None}


# ---------------------------------------------------------------------------
# Monthly rate
# ---------------------------------------------------------------------------

def build_monthly_churn_rate(customers: list[dict], months: int = 12) -> list[dict]:
    """Monthly churn rate, scoped from CHURN_SINCE forward only.

    Scope change (2026-04-11): we only analyze churns from Feb 2026 onward, so
    months prior to CHURN_SINCE are excluded from the output series entirely.
    """
    out = []
    # Walk from CHURN_SINCE through TODAY.
    month_list: list[tuple[int, int]] = []
    yr, mo = CHURN_SINCE.year, CHURN_SINCE.month
    while (yr, mo) <= (TODAY.year, TODAY.month):
        month_list.append((yr, mo))
        mo += 1
        if mo == 13:
            mo = 1; yr += 1

    parsed = [(parse_date(c.get("first_payment_date")), parse_date(c.get("churn_date"))) for c in customers]

    for (yr, mo) in month_list:
        mstart = date(yr, mo, 1)
        mend = date(yr + (1 if mo == 12 else 0), 1 if mo == 12 else mo + 1, 1)
        active_start = 0
        churned_in = 0
        for fpd, cd in parsed:
            if fpd is None or fpd >= mstart:
                continue
            if cd is None or cd >= mstart:
                active_start += 1
            if cd is not None and mstart <= cd < mend:
                churned_in += 1
        rate = (churned_in / active_start * 100) if active_start else 0.0
        out.append({"month": f"{yr}-{mo:02d}", "active_start": active_start, "churned": churned_in, "rate": round(rate, 2)})
    return out


# ---------------------------------------------------------------------------
# Comms insight aggregation
# ---------------------------------------------------------------------------

def aggregate_comms_insights(customers: list[dict]) -> dict:
    """Across validated-churned customers, compute aggregated comms signals."""
    churned = [c for c in customers if c.get("is_churned_validated")]
    silent_buckets = {"0-7d": 0, "8-30d": 0, "31-60d": 0, "61-90d": 0, "90d+": 0, "Unknown": 0}
    decay_buckets = {"Grew": 0, "Flat (±20%)": 0, "Declined 20-50%": 0, "Collapsed 50%+": 0, "Unknown": 0}
    channel_hist: Counter = Counter()
    inbound_total = 0
    outbound_total = 0
    word_totals: Counter = Counter()
    no_comms_at_all = 0
    silent_30_plus = 0
    avg_weekly_sum = [0] * 14
    avg_weekly_n = 0

    for c in churned:
        a = c.get("comms_analytics") or {}
        # Silent distribution
        d = a.get("days_silent_at_churn")
        if d is None:
            silent_buckets["Unknown"] += 1
            no_comms_at_all += 1
        else:
            if d >= 30:
                silent_30_plus += 1
            if d <= 7:
                silent_buckets["0-7d"] += 1
            elif d <= 30:
                silent_buckets["8-30d"] += 1
            elif d <= 60:
                silent_buckets["31-60d"] += 1
            elif d <= 90:
                silent_buckets["61-90d"] += 1
            else:
                silent_buckets["90d+"] += 1

        # Decay distribution
        dec = a.get("decay_pct")
        if dec is None:
            decay_buckets["Unknown"] += 1
        elif dec > 0:
            decay_buckets["Grew"] += 1
        elif dec >= -20:
            decay_buckets["Flat (±20%)"] += 1
        elif dec >= -50:
            decay_buckets["Declined 20-50%"] += 1
        else:
            decay_buckets["Collapsed 50%+"] += 1

        # Channel mix
        dc = a.get("dominant_channel_90d")
        if dc:
            channel_hist[dc] += 1

        inbound_total += a.get("inbound_90d") or 0
        outbound_total += a.get("outbound_90d") or 0

        for w in a.get("top_keywords") or []:
            word_totals[w] += 1

        wv = a.get("weekly_volumes") or []
        if wv:
            for i in range(min(14, len(wv))):
                avg_weekly_sum[i] += wv[i]
            avg_weekly_n += 1

    avg_weekly = [round(x / avg_weekly_n, 2) if avg_weekly_n else 0 for x in avg_weekly_sum]

    return {
        "silent_buckets": silent_buckets,
        "decay_buckets": decay_buckets,
        "channel_histogram": dict(channel_hist),
        "inbound_total": inbound_total,
        "outbound_total": outbound_total,
        "no_comms_at_all": no_comms_at_all,
        "silent_30_plus": silent_30_plus,
        "top_keywords": word_totals.most_common(30),
        "avg_weekly_volume": avg_weekly,
        "churned_with_comms": sum(1 for c in churned if (c.get("comms_analytics") or {}).get("message_count_total")),
        "churned_total": len(churned),
    }


def aggregate_cause_insights(customers: list[dict]) -> dict:
    """Aggregate the per-customer cause analysis into dashboard-level rollups.

    Returns cause breakdown, preventability distribution, response-time medians,
    top recommendation tags, and a 'priority saves' list (High preventability
    customers, sorted by MRR desc) suitable for a hit-list view.
    """
    churned = [c for c in customers if c.get("is_churned_validated") and c.get("cause_analysis")]

    cause_breakdown: Counter = Counter()
    preventability_breakdown: Counter = Counter({"High": 0, "Medium": 0, "Low": 0})
    rec_tag_counts: Counter = Counter()
    response_medians: list[float] = []
    ignored_counts: list[int] = []
    ignored_inbound_total = 0
    sample_inbound_total = 0
    mrr_by_cause: dict[str, float] = defaultdict(float)
    count_by_cause: Counter = Counter()

    priority_saves: list[dict] = []

    for c in churned:
        ca = c["cause_analysis"]
        cause = ca.get("primary_cause") or "unknown"
        cause_breakdown[cause] += 1
        count_by_cause[cause] += 1
        mrr_by_cause[cause] += float(c.get("mrr") or 0)

        tier = ca.get("preventability_tier") or "Low"
        preventability_breakdown[tier] += 1

        rs = ca.get("response_stats") or {}
        med = rs.get("median_days")
        if isinstance(med, (int, float)):
            response_medians.append(float(med))
        ic = rs.get("ignored_count") or 0
        sc = rs.get("sample_count") or 0
        ignored_counts.append(ic)
        ignored_inbound_total += ic
        sample_inbound_total += sc

        for rec in ca.get("recommendations") or []:
            # Extract the bracketed tag if present.
            text = rec if isinstance(rec, str) else str(rec)
            if text.startswith("[") and "]" in text:
                tag = text[1:text.index("]")]
                rec_tag_counts[tag] += 1

        if tier == "High":
            tp = ca.get("turning_point") or {}
            priority_saves.append({
                "entity_id": c.get("entity_id"),
                "biz_name": c.get("biz_name"),
                "am": c.get("am"),
                "mrr": c.get("mrr") or 0,
                "churn_date": c.get("churn_date"),
                "primary_cause": cause,
                "primary_cause_label": ca.get("primary_cause_label"),
                "preventability_score": ca.get("preventability_score") or 0,
                "turning_point_date": tp.get("date"),
                "turning_point_type": tp.get("type"),
                "narrative": ca.get("narrative"),
                "top_recommendations": (ca.get("recommendations") or [])[:3],
            })

    # Sort priority saves by MRR desc, then preventability score desc.
    priority_saves.sort(key=lambda r: (float(r["mrr"] or 0), r["preventability_score"]), reverse=True)

    # Median helper.
    def _median(xs: list[float]) -> float | None:
        if not xs:
            return None
        s = sorted(xs)
        n = len(s)
        mid = n // 2
        return round((s[mid] + s[-mid - 1]) / 2, 2)

    median_response = _median(response_medians)
    ignored_rate = round((ignored_inbound_total / sample_inbound_total * 100), 1) if sample_inbound_total else 0.0

    # Build ordered cause rows with $ at risk
    cause_rows = []
    for cause, count in cause_breakdown.most_common():
        cause_rows.append({
            "code": cause,
            "label": CAUSE_LABELS.get(cause, cause),
            "count": count,
            "mrr_lost": round(mrr_by_cause[cause], 2),
        })

    return {
        "cause_breakdown": cause_rows,
        "preventability_breakdown": dict(preventability_breakdown),
        "median_response_days": median_response,
        "ignored_inbound_rate_pct": ignored_rate,
        "ignored_inbound_total": ignored_inbound_total,
        "sample_inbound_total": sample_inbound_total,
        "top_recommendation_tags": rec_tag_counts.most_common(10),
        "priority_saves": priority_saves,
        "priority_save_count": len(priority_saves),
        "analyzed_count": len(churned),
    }


# ---------------------------------------------------------------------------
# Writing per-customer comms JSON
# ---------------------------------------------------------------------------

def write_customer_comms_files(customers: list[dict], messages_by_entity: dict, payment_histories: dict | None = None) -> int:
    """Write per-customer comms JSON sidecars for lazy-load by the dashboard.

    The mounted outputs directory (on the user's machine) doesn't permit unlink
    of files we didn't create in this session — it *does* allow overwrite. So
    instead of trying to delete stale files, we track which entity_ids we
    wrote fresh, then truncate any existing file for an out-of-scope entity
    to a minimal empty payload. That keeps the data directory consistent with
    the current scope even though we can't physically remove stragglers.
    """
    COMMS_DIR.mkdir(parents=True, exist_ok=True)
    payment_histories = payment_histories or {}

    fresh_ids: set[str] = set()
    written = 0
    for c in customers:
        if not c.get("is_churned_validated"):
            continue
        eid = c["entity_id"]
        if not eid:
            continue
        msgs = messages_by_entity.get(eid, [])
        ph = payment_histories.get((c.get("customer_id") or "").strip()) or {}
        payload = {
            "entity_id": eid,
            "biz_name": c.get("biz_name"),
            "churn_date": c.get("churn_date"),
            "am": c.get("am"),
            "mrr": c.get("mrr"),
            "tenure_days": c.get("tenure_days"),
            "place_id": c.get("place_id") or "",
            "map_link": c.get("map_link") or "",
            "analytics": c.get("comms_analytics") or {},
            "cause_analysis": c.get("cause_analysis") or {},
            "messages": msgs,
            "payment_history": ph,
        }
        (COMMS_DIR / f"{eid}.json").write_text(json.dumps(payload))
        fresh_ids.add(eid)
        written += 1

    # Neutralize stale files from prior runs: overwrite with an empty payload.
    # Try unlink first (works for files we created this run on permissive FS);
    # fall back to overwrite on the mount where unlink is blocked.
    stale = 0
    empty_payload = json.dumps({
        "entity_id": None,
        "biz_name": None,
        "churn_date": None,
        "analytics": {},
        "cause_analysis": {},
        "messages": [],
        "_stale": True,
    })
    for existing in COMMS_DIR.glob("*.json"):
        eid = existing.stem
        if eid in fresh_ids:
            continue
        try:
            existing.unlink()
            stale += 1
        except OSError:
            try:
                existing.write_text(empty_payload)
                stale += 1
            except OSError:
                pass

    if stale:
        _log(f"Neutralized {stale} stale comms JSON file(s) from prior runs")
    return written


# ---------------------------------------------------------------------------
# Main payload build
# ---------------------------------------------------------------------------

def build_payload(rows: list[dict]) -> dict:
    _log("Slimming BaseSheet customers…")
    customers = [slim_customer(r) for r in rows]

    # 1. Chargebee validation for candidates inside the validation window
    candidates_raw: list[dict] = []
    for r in rows:
        cd = parse_date(r.get("churn_date"))
        cid = (r.get("customer_id") or "").strip()
        if cd and cd >= VALIDATE_CUTOFF and cid:
            candidates_raw.append(r)
    _log(f"Validation candidates (churn ≥ {CHURN_SINCE}): {len(candidates_raw)}")
    churned_raw, retained_raw = validate_churn(candidates_raw)

    validated_ids = {(r.get("customer_id") or "").strip() for r in churned_raw}
    retained_ids = {(r.get("customer_id") or "").strip() for r in retained_raw}

    for c in customers:
        cd = parse_date(c.get("churn_date"))
        if cd and cd >= VALIDATE_CUTOFF:
            c["is_churned_validated"] = c["customer_id"] in validated_ids
            c["retained_override"] = c["customer_id"] in retained_ids
        else:
            c["is_churned_validated"] = False
            c["retained_override"] = False

    # 2. Fetch comms (stats for everyone, full messages for churned)
    churned_entity_ids = {c["entity_id"] for c in customers if c.get("is_churned_validated") and c["entity_id"]}
    active_entity_ids = {c["entity_id"] for c in customers
                         if c["entity_id"] and c.get("churn_date") is None and c.get("chrone_status") == "ZOCA"}
    _log(f"Comms: fetching history for {len(churned_entity_ids)} churned + stats for {len(active_entity_ids)} active")
    comms_stats, messages_by_entity, _ = fetch_comms_detailed(churned_entity_ids, active_entity_ids)

    # 3. Per-customer analytics and comms embedding
    _log("Computing per-customer comms analytics…")
    cause_counts: Counter = Counter()
    for c in customers:
        rec = comms_stats.get(c["entity_id"], {})
        c["comms_30d"] = rec.get("total_30d", 0)
        c["comms_90d"] = rec.get("total_90d", 0)
        c["comms_by_channel"] = rec.get("by_channel", {})
        c["last_contact"] = rec.get("last_contact")
        if c.get("is_churned_validated"):
            msgs = messages_by_entity.get(c["entity_id"], [])
            c["comms_analytics"] = compute_customer_comms_analytics(c, msgs)
            c["cause_analysis"] = analyze_customer_churn_cause(c, msgs)
            cause_counts[c["cause_analysis"]["primary_cause"]] += 1
        else:
            c["comms_analytics"] = None
            c["cause_analysis"] = None
    _log(f"Cause breakdown: {dict(cause_counts)}")

    # 4. At-risk scoring on active customers
    _log("Scoring at-risk customers…")
    for c in customers:
        if c.get("churn_date") is None:
            rs = compute_at_risk_score(c, comms_stats)
            c["risk_score"] = rs["score"]
            c["risk_tier"] = rs["tier"]
            c["risk_signals"] = rs["signals"]
            c["last_contact"] = rs["last_contact"]
        else:
            c["risk_score"] = 0
            c["risk_tier"] = "Churned" if c.get("is_churned_validated") else "Historical"
            c["risk_signals"] = []

    # 4.5 Payment history enrichment (Chargebee) — churned customers only
    churned_cust_ids = [
        (c.get("customer_id") or "").strip()
        for c in customers
        if c.get("is_churned_validated") and (c.get("customer_id") or "").strip()
    ]
    payment_histories = fetch_payment_histories(sorted(set(churned_cust_ids)), workers=6)

    # 5. Write per-customer JSON sidecars for the modal (comms + payment)
    n_files = write_customer_comms_files(customers, messages_by_entity, payment_histories)
    _log(f"Wrote {n_files} per-customer comms JSON files")

    # 6. Monthly rate + comms insights + cause insights
    monthly_rate = build_monthly_churn_rate(customers, months=12)
    comms_insights = aggregate_comms_insights(customers)
    cause_insights = aggregate_cause_insights(customers)

    # 7. Slim the inline payload: strip analytics + comms_analytics from non-churned
    inline_customers = []
    for c in customers:
        slim = dict(c)
        # Drop heavy fields from inline payload — per-customer JSON has full detail
        if not c.get("is_churned_validated"):
            slim.pop("comms_analytics", None)
            slim.pop("comms_by_channel", None)
        else:
            # Keep summary analytics inline so the main table can sort on them
            a = c.get("comms_analytics") or {}
            slim["days_silent_at_churn"] = a.get("days_silent_at_churn")
            slim["decay_pct"] = a.get("decay_pct")
            slim["longest_gap_90d"] = a.get("longest_gap_90d")
            slim["inbound_90d"] = a.get("inbound_90d", 0)
            slim["outbound_90d"] = a.get("outbound_90d", 0)
            slim["dominant_channel_90d"] = a.get("dominant_channel_90d")
            slim["last_inbound_snippet"] = a.get("last_inbound_snippet")
            slim["last_inbound_date"] = a.get("last_inbound_date")
            slim["top_keywords"] = a.get("top_keywords", [])
            # Attach compact cause summary for table/tab use; full narrative + recs live in sidecar
            ca = c.get("cause_analysis") or {}
            slim["primary_cause"] = ca.get("primary_cause")
            slim["primary_cause_label"] = ca.get("primary_cause_label")
            slim["preventability_tier"] = ca.get("preventability_tier")
            slim["preventability_score"] = ca.get("preventability_score")
            tp = ca.get("turning_point")
            slim["turning_point_date"] = tp.get("date") if tp else None
            slim["turning_point_type"] = tp.get("type") if tp else None
            rs = ca.get("response_stats") or {}
            slim["median_response_days"] = rs.get("median_days")
            slim["ignored_inbound_count"] = rs.get("ignored_count")
            slim.pop("comms_analytics", None)
            slim.pop("comms_by_channel", None)
            slim.pop("cause_analysis", None)
        inline_customers.append(slim)

    retained_list = []
    for r in retained_raw:
        cd = parse_date(r.get("churn_date"))
        retained_list.append({
            "biz_name": r.get("bizname") or "",
            "am": r.get("am_name") or "",
            "churn_date": cd.isoformat() if cd else "",
            "active_sub_count": r.get("_active_sub_count", 0),
            "statuses": ",".join(sorted(set(r.get("_sub_statuses") or []))),
        })

    ams = sorted({c["am"] for c in customers if c["am"]})
    states = sorted({c["state"] for c in customers if c["state"] and c["state"] != "Unknown"})
    categories = sorted({c["category"] for c in customers if c["category"] and c["category"] != "Unknown"})
    lead_sources = sorted({c["lead_source"] for c in customers if c["lead_source"] and c["lead_source"] != "Unknown"})

    payload = {
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "window": {
            "default_start": DEFAULT_CUTOFF.isoformat(),
            "default_end": TODAY.isoformat(),
            "validate_start": VALIDATE_CUTOFF.isoformat(),
            "validate_end": TODAY.isoformat(),
            "scope_label": "Feb 1, 2026 onward",
        },
        "customers": inline_customers,
        "retained": retained_list,
        "monthly_rate": monthly_rate,
        "comms_insights": comms_insights,
        "cause_insights": cause_insights,
        "filters": {
            "ams": ams, "states": states,
            "categories": categories, "lead_sources": lead_sources,
        },
    }

    validated_count = sum(1 for c in customers if c.get("is_churned_validated"))
    _log(f"Customers: {len(customers)} | churned: {validated_count} | retained: {len(retained_list)}")
    _log(f"Comms insights: silent30+={comms_insights['silent_30_plus']} no_comms={comms_insights['no_comms_at_all']}")
    _log(f"Cause insights: high_prev={cause_insights['preventability_breakdown'].get('High', 0)} "
         f"med_prev={cause_insights['preventability_breakdown'].get('Medium', 0)} "
         f"priority_saves={cause_insights['priority_save_count']}")

    return payload


# ---------------------------------------------------------------------------
# HTML rendering
# ---------------------------------------------------------------------------

def render_html(payload: dict) -> str:
    template = TEMPLATE_PATH.read_text()
    data_json = json.dumps(payload, default=str)
    data_json = data_json.replace("</", "<\\/")
    logo_svg = LOGO_SRC.read_text()
    return (template
            .replace("__DATA__", data_json)
            .replace("__LOGO_SVG__", logo_svg))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    _log("Starting Zoca churn tool (v4 — cause analysis)")
    _log(f"Churn scope: {CHURN_SINCE} → {TODAY} (analyzing churns on or after Feb 1, 2026)")

    rows = fetch_basesheet()
    payload = build_payload(rows)

    html = render_html(payload)
    out = OUTPUT_DIR / "index.html"
    out.write_text(html)
    (OUTPUT_DIR / "churn_dashboard.html").write_text(html)  # keep legacy filename too
    _log(f"Wrote dashboard → {out} ({len(html):,} chars)")

    (CACHE_DIR / "last_summary.json").write_text(json.dumps({
        "generated_at": payload["generated_at"],
        "customer_count": len(payload["customers"]),
        "validated_churn": sum(1 for c in payload["customers"] if c.get("is_churned_validated")),
        "retained": len(payload["retained"]),
        "comms_insights_summary": {
            "silent_30_plus": payload["comms_insights"]["silent_30_plus"],
            "no_comms_at_all": payload["comms_insights"]["no_comms_at_all"],
        },
    }, indent=2))
    _log("Done.")


if __name__ == "__main__":
    main()

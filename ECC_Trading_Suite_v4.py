#!/usr/bin/env python3
"""
ECC Trading Suite - Cloud Edition v4 (REBUILT)
================================================
Major rebuild addressing:
 1. Search now actually switches the chart/order screen to the searched stock
 2. Real dedicated Watchlist tab - add/remove symbols easily
 3. Real LIVE market prices (polled from Yahoo Finance every ~45s) instead of fake random walk
 4. Persistent state - trades/portfolio/watchlist saved to disk (ecc_state.json), survive restarts
 5. True background operation - a server-side thread runs the engine even with no browser open
 6. Web Push notifications (VAPID) - real alerts on your phone even if the site/app is closed
 7. Candlestick reversal pattern detection - Hammer, Shooting Star, Doji, Bullish/Bearish
    Engulfing, Morning Star, Evening Star - scanned automatically on your watchlist
 8. Much clearer candlestick chart rendering - bigger, readable, gridlines, price axis

HONESTY NOTES (read before deploying):
 - Render's FREE web service tier still sleeps after ~15 min with no web traffic. Use
   UptimeRobot (free) to ping /health every 5 minutes so it never sleeps.
 - Push notifications require you to tap "Enable Notifications" once per device.
 - iPhone Safari requires "Add to Home Screen" before push notifications work at all.
 - Real live prices are polled every ~45 seconds via Yahoo Finance (delayed, not tick data).

Install:  pip install flask yfinance requests pywebpush cryptography
Run:      python ECC_Trading_Suite_v4.py
Env vars to set on Render (Settings -> Environment):
   VAPID_PUBLIC_KEY   = BJv5-S4BOk1kVUOdrE9aBXfeguaMXveOunubj9wgaR9yiPXux3LbUVoVB4vnWtogRl9aiRWDDRN6Q2x6rm0CtXo
   VAPID_PRIVATE_KEY  = eBj8gbJ47L2unMAtK-HeM1XIxKfQlrgDhv62TfCH3vg
   VAPID_CLAIM_EMAIL  = mailto:you@example.com
"""
import csv, io, json, math, os, queue, random, re, threading, time
from datetime import datetime, timezone
from flask import Flask, Response, jsonify, request

try:
    import yfinance as yf
    HAS_YF = True
except ImportError:
    HAS_YF = False

try:
    import requests
    HAS_REQ = True
except ImportError:
    HAS_REQ = False

try:
    from pywebpush import webpush, WebPushException
    HAS_PUSH = True
except ImportError:
    HAS_PUSH = False

app = Flask(__name__)
PORT = int(os.environ.get("PORT", 5000))
INIT_CASH = 10000.0
AUTOFRAC = 0.20
MAXHIST = 800
MAXTRADES = 300
CHARTPTS = 150
MAXBT = 5000
SCANEVERY = 300
LIVE_INTERVAL = 45
STATE_FILE = os.environ.get("ECC_STATE_FILE", "ecc_state.json")

VAPID_PUBLIC_KEY = os.environ.get("VAPID_PUBLIC_KEY", "BJv5-S4BOk1kVUOdrE9aBXfeguaMXveOunubj9wgaR9yiPXux3LbUVoVB4vnWtogRl9aiRWDDRN6Q2x6rm0CtXo")
VAPID_PRIVATE_KEY = os.environ.get("VAPID_PRIVATE_KEY", "eBj8gbJ47L2unMAtK-HeM1XIxKfQlrgDhv62TfCH3vg")
VAPID_CLAIM_EMAIL = os.environ.get("VAPID_CLAIM_EMAIL", "mailto:ecc-trading@example.com")

DEFAULT_ASSETS = {
    "BTC-USD": {"name": "Bitcoin", "p0": 43500.0, "mu": 0.00020, "sigma": 0.025},
    "ETH-USD": {"name": "Ethereum", "p0": 2650.0, "mu": 0.00015, "sigma": 0.028},
    "AAPL": {"name": "Apple", "p0": 185.0, "mu": 0.00008, "sigma": 0.012},
    "TSLA": {"name": "Tesla", "p0": 235.0, "mu": 0.00010, "sigma": 0.032},
    "RELIANCE.NS": {"name": "Reliance", "p0": 2900.0, "mu": 0.00009, "sigma": 0.016},
    "NSEI": {"name": "Nifty 50", "p0": 24500.0, "mu": 0.00007, "sigma": 0.010},
}
ASSETS = dict(DEFAULT_ASSETS)

NSE_FNO_SET = {
    "RELIANCE","TCS","INFY","HDFCBANK","ICICIBANK","SBIN","AXISBANK","KOTAKBANK",
    "LT","ITC","HINDUNILVR","BHARTIARTL","MARUTI","TATAMOTORS","TATASTEEL","M&M",
    "SUNPHARMA","BAJFINANCE","BAJAJFINSV","ADANIENT","ADANIPORTS","ULTRACEMCO",
    "TITAN","WIPRO","HCLTECH","ONGC","NTPC","POWERGRID","COALINDIA","JSWSTEEL",
    "GRASIM","DRREDDY","CIPLA","DIVISLAB","EICHERMOT","HEROMOTOCO","BAJAJ-AUTO",
    "INDUSINDBK","HDFCLIFE","SBILIFE","TECHM","ASIANPAINT","NESTLEIND","BRITANNIA",
    "UPL","GAIL","VEDL","HINDALCO","APOLLOHOSP","PIDILITIND","DLF","SHREECEM",
    "TATACONSUM","BPCL","IOC","ZOMATO","PAYTM","IRCTC","PNB","BANKBARODA",
}

def is_indian_symbol(sym): return sym.upper().endswith((".NS",".BO")) or sym.upper() in ("NSEI","BSESN","BANKNIFTY")
def has_fno(sym):
    base = sym.upper().replace(".NS","").replace(".BO","")
    if base in ("NIFTY","NSEI","^NSEI","BANKNIFTY","NSEBANK","^NSEBANK"): return True
    return base in NSE_FNO_SET

def gbm(price, mu, sigma):
    return max(0.01, price*math.exp((mu-0.5*sigma*sigma)+sigma*random.gauss(0,1)))

def sma(vals, n):
    if n<=0 or len(vals)<n: return None
    return sum(vals[-n:])/n

def ema_series(vals, n):
    if len(vals) < n: return [None]*len(vals)
    k = 2/(n+1); out = [None]*(n-1); e = sum(vals[:n])/n; out.append(e)
    for v in vals[n:]:
        e = v*k + e*(1-k); out.append(e)
    return out

def macd(vals):
    if len(vals) < 26: return None, None
    e12 = ema_series(vals, 12); e26 = ema_series(vals, 26)
    line_vals = []
    for i in range(len(vals)):
        a = e12[i] if i < len(e12) else None
        b = e26[i] if i < len(e26) else None
        line_vals.append(a-b if (a is not None and b is not None) else None)
    clean = [x for x in line_vals if x is not None]
    if len(clean) < 9: return (clean[-1] if clean else None), None
    sig = ema_series(clean, 9)[-1]
    return clean[-1], sig

def bollinger(vals, n=20, k=2):
    if len(vals) < n: return None, None, None
    window = vals[-n:]; m = sum(window)/n
    var = sum((x-m)**2 for x in window)/n; sd = math.sqrt(var)
    return m-k*sd, m, m+k*sd

def rsi_val(vals, n=14):
    if len(vals) < n+1: return 50.0
    w = vals[-(n+1):]
    diffs = [w[i]-w[i-1] for i in range(1,len(w))]
    ag = sum(d for d in diffs if d>0)/n
    al = sum(-d for d in diffs if d<0)/n
    return 100.0 if al==0 else 100-(100/(1+ag/al))

def max_dd(hist):
    if not hist: return 0.0
    peak = hist[0]; worst = 0.0
    for v in hist:
        if v>peak: peak=v
        if peak>0: worst=max(worst, (peak-v)/peak)
    return worst

def _body(o,c): return abs(c-o)
def _range(h,l): return max(h-l, 1e-9)

def is_doji(o,h,l,c):
    return _body(o,c)/_range(h,l) < 0.1

def is_hammer(o,h,l,c):
    body = _body(o,c); lower = min(o,c)-l; upper = h-max(o,c)
    return body > 0 and lower > 2*body and upper < body*0.6 and (c >= o)

def is_hanging_man(o,h,l,c):
    body = _body(o,c); lower = min(o,c)-l; upper = h-max(o,c)
    return body > 0 and lower > 2*body and upper < body*0.6 and (c < o)

def is_shooting_star(o,h,l,c):
    body = _body(o,c); upper = h-max(o,c); lower = min(o,c)-l
    return body > 0 and upper > 2*body and lower < body*0.6

def is_bullish_engulf(o1,c1,o2,c2):
    return c1 < o1 and c2 > o2 and c2 >= o1 and o2 <= c1

def is_bearish_engulf(o1,c1,o2,c2):
    return c1 > o1 and c2 < o2 and c2 <= o1 and o2 >= c1

def is_morning_star(o1,c1,o2,c2,h2,l2,o3,c3):
    return c1 < o1 and _body(o2,c2)/_range(h2,l2) < 0.35 and c3 > o3 and c3 > (o1+c1)/2

def is_evening_star(o1,c1,o2,c2,h2,l2,o3,c3):
    return c1 > o1 and _body(o2,c2)/_range(h2,l2) < 0.35 and c3 < o3 and c3 < (o1+c1)/2

def detect_candle_patterns(ohlc):
    o, h, l, c = ohlc["o"], ohlc["h"], ohlc["l"], ohlc["c"]
    n = len(c)
    if n < 3: return []
    out = []
    i = n-1
    if is_doji(o[i],h[i],l[i],c[i]):
        out.append({"pattern": "Doji", "direction": "NEUTRAL", "index": i})
    if is_hammer(o[i],h[i],l[i],c[i]):
        out.append({"pattern": "Hammer", "direction": "BULLISH", "index": i})
    if is_hanging_man(o[i],h[i],l[i],c[i]):
        out.append({"pattern": "Hanging Man", "direction": "BEARISH", "index": i})
    if is_shooting_star(o[i],h[i],l[i],c[i]):
        out.append({"pattern": "Shooting Star", "direction": "BEARISH", "index": i})
    if n >= 2:
        if is_bullish_engulf(o[i-1],c[i-1],o[i],c[i]):
            out.append({"pattern": "Bullish Engulfing", "direction": "BULLISH", "index": i})
        if is_bearish_engulf(o[i-1],c[i-1],o[i],c[i]):
            out.append({"pattern": "Bearish Engulfing", "direction": "BEARISH", "index": i})
    if n >= 3:
        if is_morning_star(o[i-2],c[i-2],o[i-1],c[i-1],h[i-1],l[i-1],o[i],c[i]):
            out.append({"pattern": "Morning Star", "direction": "BULLISH", "index": i})
        if is_evening_star(o[i-2],c[i-2],o[i-1],c[i-1],h[i-1],l[i-1],o[i],c[i]):
            out.append({"pattern": "Evening Star", "direction": "BEARISH", "index": i})
    return out

INDICATOR_ALIASES = {"rsi":"RSI","price":"PRICE","close":"PRICE","vix":"VIX","volatility":"VIX",
                      "macd":"MACD","volume":"VOLUME","bollinger":"BOLL","bb":"BOLL"}

def parse_plain_english(text):
    text = text.lower().strip()
    action = "BUY" if "buy" in text else ("SELL" if "sell" in text else None)
    if action is None: return None, "Start your sentence with 'buy' or 'sell'."
    m = re.search(r"(rsi|price|vix|macd)\s*(below|under|less than|above|over|greater than)\s*(-?\d+(?:\.\d+)?)", text)
    if m:
        ind_raw, comp, val = m.group(1), m.group(2), float(m.group(3))
        ind = INDICATOR_ALIASES.get(ind_raw, ind_raw.upper())
        op = "<" if comp in ("below","under","less than") else ">"
        return [{"indicator": ind, "op": op, "value": val, "action": action}], None
    m2 = re.search(r"(\d+)\s*(?:sma|ema)?\s*crosses?\s*(above|below)\s*(\d+)\s*(?:sma|ema)?", text)
    if m2:
        fast, comp, slow = int(m2.group(1)), m2.group(2), int(m2.group(3))
        op = "cross_up" if comp=="above" else "cross_down"
        return [{"indicator":"SMA_CROSS","op":op,"fast":fast,"slow":slow,"action":action}], None
    m3 = re.search(r"bollinger|bb", text)
    if m3:
        op = "touch_lower" if ("lower" in text or "below" in text) else "touch_upper"
        return [{"indicator":"BOLL","op":op,"action":action}], None
    m4 = re.search(r"(hammer|doji|shooting star|engulfing|morning star|evening star|hanging man)", text)
    if m4:
        return [{"indicator":"PATTERN","pattern":m4.group(1).title(),"action":action}], None
    return None, ("Try: 'buy when rsi below 30', 'sell when price above 250', "
                  "'buy when 5 sma crosses above 20 sma', 'buy when bollinger lower band touched', "
                  "'buy when hammer pattern forms'.")

def eval_rule(rule, series, current_price, vix_val=None, patterns=None):
    ind = rule["indicator"]
    if ind == "RSI":
        r = rsi_val(series)
        return (r < rule["value"]) if rule["op"]=="<" else (r > rule["value"])
    if ind == "PRICE":
        return (current_price < rule["value"]) if rule["op"]=="<" else (current_price > rule["value"])
    if ind == "VIX":
        if vix_val is None: return False
        return (vix_val < rule["value"]) if rule["op"]=="<" else (vix_val > rule["value"])
    if ind == "MACD":
        m, s = macd(series)
        if m is None or s is None: return False
        return (m < s) if rule["op"]=="<" else (m > s)
    if ind == "BOLL":
        lo, mid, hi = bollinger(series)
        if lo is None: return False
        if rule["op"] == "touch_lower": return current_price <= lo
        if rule["op"] == "touch_upper": return current_price >= hi
        return False
    if ind == "PATTERN":
        if not patterns: return False
        return any(p["pattern"] == rule.get("pattern") for p in patterns)
    if ind == "SMA_CROSS":
        cf, cs = sma(series, rule["fast"]), sma(series, rule["slow"])
        pf, ps = sma(series[:-1], rule["fast"]), sma(series[:-1], rule["slow"])
        if None in (cf,cs,pf,ps): return False
        if rule["op"]=="cross_up": return pf<=ps and cf>cs
        else: return pf>=ps and cf<cs
    return False

VIX_CACHE = {"value": None, "ts": 0}
def get_india_vix():
    if not HAS_YF: return None
    now = time.time()
    if VIX_CACHE["value"] is not None and now-VIX_CACHE["ts"] < 60:
        return VIX_CACHE["value"]
    try:
        h = yf.Ticker("^INDIAVIX").history(period="1d", interval="5m")
        if not h.empty:
            VIX_CACHE["value"] = round(float(h["Close"].iloc[-1]), 2)
            VIX_CACHE["ts"] = now
    except Exception:
        pass
    return VIX_CACHE["value"]

def search_symbol(query):
    q = query.strip().upper()
    if not HAS_YF: return None, "yfinance not installed on server."
    candidates = [q]
    if not q.endswith((".NS",".BO")) and re.match(r"^[A-Z&]+$", q) and "-USD" not in q:
        candidates.append(q+".NS")
    for cand in candidates:
        try:
            h = yf.Ticker(cand).history(period="5d", interval="1d")
            if h is not None and not h.empty:
                last = float(h["Close"].iloc[-1])
                return {"symbol": cand, "last_price": round(last,4),
                        "is_indian": is_indian_symbol(cand), "has_fno": has_fno(cand)}, None
        except Exception:
            continue
    return None, f"Symbol '{query}' not found."

def fetch_ohlc(ticker, interval="1d", period="6mo"):
    if not HAS_YF: return None, "yfinance not installed"
    try:
        hist = yf.Ticker(ticker).history(period=period, interval=interval)
        hist = hist.dropna(subset=["Close"])
        if len(hist) < 5: return None, f"Only {len(hist)} bars"
        vol = hist["Volume"].tolist() if "Volume" in hist.columns else [0]*len(hist)
        return {"o": hist["Open"].tolist(), "h": hist["High"].tolist(),
                "l": hist["Low"].tolist(), "c": hist["Close"].tolist(),
                "v": vol, "t": [str(x) for x in hist.index]}, None
    except Exception as e:
        return None, str(e)[:150]

def fetch_last_price(ticker):
    if not HAS_YF: return None
    try:
        h = yf.Ticker(ticker).history(period="2d", interval="1m")
        if h is not None and not h.empty:
            return float(h["Close"].iloc[-1])
        h = yf.Ticker(ticker).history(period="5d", interval="1d")
        if h is not None and not h.empty:
            return float(h["Close"].iloc[-1])
    except Exception:
        pass
    return None

def chartink_screener(scan_clause_url_or_slug):
    if not HAS_REQ:
        return None, "requests library not installed on server."
    try:
        sess = requests.Session()
        slug = scan_clause_url_or_slug.strip().rstrip("/").split("/")[-1]
        page = sess.get(f"https://chartink.com/screener/{slug}", timeout=10)
        m = re.search(r'name="csrf-token" content="([^"]+)"', page.text)
        if not m:
            return None, "Could not read Chartink page (site structure may have changed)."
        csrf = m.group(1)
        m2 = re.search(r'"scan_clause"\s*:\s*"([^"]+)"', page.text.replace("\\/", "/"))
        scan_clause = m2.group(1) if m2 else None
        if not scan_clause:
            return None, "Could not find scan clause on page - screener slug may be wrong."
        resp = sess.post("https://chartink.com/screener/process",
                          data={"scan_clause": scan_clause},
                          headers={"x-csrf-token": csrf}, timeout=10)
        data = resp.json()
        rows = data.get("data", [])
        symbols = [r.get("nsecode") for r in rows if r.get("nsecode")]
        return symbols, None
    except Exception as e:
        return None, f"Chartink pull failed: {str(e)[:150]} (their site structure may have changed)"

def mk_state():
    return {
        "tick": 0, "mode": "GLOBAL",
        "prices": {k: v["p0"] for k, v in ASSETS.items()},
        "history": {k: [v["p0"]] for k, v in ASSETS.items()},
        "portfolio": {"cash": INIT_CASH, "pos": {k: {"qty":0.,"avg":0.,"sl":None,"tp":None} for k in ASSETS}},
        "trades": [], "nid": 1, "pending": [],
        "pvhist": [INIT_CASH],
        "strat": {"type":"manual","fast":5,"slow":20,"active":False,"rules":[],"rule_text":""},
        "watchlist": ["BTC-USD","ETH-USD","AAPL","TSLA","RELIANCE.NS","NSEI"],
        "chartink_symbols": [],
        "push_subs": [],
        "asset_meta": {},
        "seen_patterns": {},
    }

def save_state(s):
    try:
        s["asset_meta"] = {k: v for k, v in ASSETS.items()}
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(s, f)
        os.replace(tmp, STATE_FILE)
    except Exception as e:
        print("save_state error:", e)

def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE) as f:
                s = json.load(f)
            for k, v in s.get("asset_meta", {}).items():
                if k not in ASSETS: ASSETS[k] = v
            for a in ASSETS:
                s["prices"].setdefault(a, ASSETS[a]["p0"])
                s["history"].setdefault(a, [ASSETS[a]["p0"]])
                s["portfolio"]["pos"].setdefault(a, {"qty":0.,"avg":0.,"sl":None,"tp":None})
            s.setdefault("push_subs", [])
            s.setdefault("seen_patterns", {})
            s.setdefault("chartink_symbols", [])
            print(f"Loaded persisted state ({len(s.get('trades',[]))} trades, {len(s.get('watchlist',[]))} watchlist items)")
            return s
        except Exception as e:
            print("load_state failed, starting fresh:", e)
    return mk_state()

STATE = load_state()
LOCK = threading.Lock()
ALERTS = []
SSE_CLIENTS = []
ALERT_LOCK = threading.Lock()

def send_webpush_to_all(payload):
    if not HAS_PUSH: return
    dead = []
    with LOCK:
        subs = list(STATE.get("push_subs", []))
    for sub in subs:
        try:
            webpush(subscription_info=sub, data=json.dumps(payload),
                    vapid_private_key=VAPID_PRIVATE_KEY,
                    vapid_claims={"sub": VAPID_CLAIM_EMAIL})
        except WebPushException as e:
            if "410" in str(e) or "404" in str(e):
                dead.append(sub)
        except Exception:
            pass
    if dead:
        with LOCK:
            STATE["push_subs"] = [s for s in STATE.get("push_subs", []) if s not in dead]
            save_state(STATE)

def push_alert(asset, pattern, direction, price, detail=""):
    a = {"id": int(time.time()*1000), "time": datetime.now(timezone.utc).strftime("%H:%M UTC"),
         "asset": asset, "pattern": pattern, "direction": direction, "price": round(price,4), "detail": detail}
    with ALERT_LOCK:
        ALERTS.insert(0, a)
        if len(ALERTS) > 150: del ALERTS[150:]
        for q in SSE_CLIENTS:
            try: q.put_nowait(a)
            except Exception: pass
    send_webpush_to_all({"title": f"{asset} - {pattern}", "body": f"{direction} @ {price} ({detail})", "tag": asset+pattern})
    return a

def pv(s): return s["portfolio"]["cash"] + sum(p["qty"]*s["prices"].get(a,0) for a,p in s["portfolio"]["pos"].items())

def record(s, asset, side, qty, price, via, pnlval=None):
    t = {"id": s["nid"], "tick": s["tick"], "ts": datetime.now(timezone.utc).strftime("%H:%M"),
         "asset": asset, "side": side, "qty": round(qty,8), "price": round(price,4), "via": via,
         "pnl": round(pnlval,2) if pnlval is not None else None}
    s["nid"] += 1; s["trades"].insert(0, t)
    if len(s["trades"]) > MAXTRADES: del s["trades"][MAXTRADES:]

def ensure_asset(s, asset, price_hint=None):
    if asset not in ASSETS:
        ASSETS[asset] = {"name": asset, "p0": price_hint or 100.0, "mu": 0.0001, "sigma": 0.02}
    if asset not in s["prices"]:
        s["prices"][asset] = price_hint or ASSETS[asset]["p0"]
        s["history"][asset] = [s["prices"][asset]]
        s["portfolio"]["pos"][asset] = {"qty":0.,"avg":0.,"sl":None,"tp":None}

def exec_order(s, asset, side, qty, sl=None, tp=None, via="MARKET"):
    ensure_asset(s, asset)
    if side not in ("BUY","SELL"): return False, "Invalid side"
    if not qty or qty <= 0: return False, "Quantity must be positive"
    price = s["prices"][asset]; pos = s["portfolio"]["pos"][asset]
    if side == "BUY":
        cost = price*qty
        if s["portfolio"]["cash"] < cost-1e-9: return False, "Insufficient cash"
        nq = pos["qty"]+qty
        pos["avg"] = (pos["avg"]*pos["qty"]+price*qty)/nq if nq else 0
        pos["qty"] = nq; s["portfolio"]["cash"] -= cost
        if sl is not None: pos["sl"] = sl
        if tp is not None: pos["tp"] = tp
        record(s, asset, side, qty, price, via)
        return True, f"Bought {qty:g} {asset} @ {price:.4f}"
    else:
        if pos["qty"] < qty-1e-9: return False, "Insufficient position"
        pnlval = (price-pos["avg"])*qty
        pos["qty"] -= qty
        if pos["qty"] < 1e-9: pos.update(qty=0.,avg=0.,sl=None,tp=None)
        s["portfolio"]["cash"] += price*qty
        record(s, asset, side, qty, price, via, pnlval)
        return True, f"Sold {qty:g} {asset} @ {price:.4f}"

def engine_step(s, vix=None):
    s["tick"] += 1
    if vix is None: vix = get_india_vix()
    still = []
    for o in s["pending"]:
        p = s["prices"].get(o["asset"], 0)
        fill = (o["side"]=="BUY" and p<=o["lp"]) or (o["side"]=="SELL" and p>=o["lp"])
        if fill: exec_order(s, o["asset"], o["side"], o["qty"], via="LIMIT")
        else: still.append(o)
    s["pending"] = still
    for asset, pos in list(s["portfolio"]["pos"].items()):
        if pos["qty"] > 0:
            p = s["prices"].get(asset, 0)
            if pos["sl"] and p <= pos["sl"]: exec_order(s, asset, "SELL", pos["qty"], via="STOPLOSS")
            elif pos["tp"] and p >= pos["tp"]: exec_order(s, asset, "SELL", pos["qty"], via="TAKEPROFIT")
    st = s["strat"]
    if st.get("active"):
        for asset in list(ASSETS.keys()):
            h = s["history"].get(asset, [])
            if len(h) < 5: continue
            price = s["prices"][asset]; pos = s["portfolio"]["pos"][asset]
            sig = None
            if st["type"] == "sma":
                cf,cs = sma(h,st["fast"]), sma(h,st["slow"])
                pf,ps = sma(h[:-1],st["fast"]), sma(h[:-1],st["slow"])
                if None not in (cf,cs,pf,ps):
                    if pf<=ps and cf>cs: sig="BUY"
                    elif pf>=ps and cf<cs: sig="SELL"
            elif st["type"] == "rsi":
                r = rsi_val(h); sig = "BUY" if r<30 else ("SELL" if r>70 else None)
            elif st["type"] == "custom" and st.get("rules"):
                for rule in st["rules"]:
                    if eval_rule(rule, h, price, vix):
                        sig = rule["action"]; break
            if sig == "BUY" and s["portfolio"]["cash"] > 1:
                q = math.floor(s["portfolio"]["cash"]*AUTOFRAC/price*1e8)/1e8
                if q>0:
                    exec_order(s, asset, "BUY", q, via="AUTO")
                    push_alert(asset, "Strategy Signal", "BULLISH", price, "Auto BUY executed")
            elif sig == "SELL" and pos["qty"] > 0:
                exec_order(s, asset, "SELL", pos["qty"], via="AUTO")
                push_alert(asset, "Strategy Signal", "BEARISH", price, "Auto SELL executed")
    s["pvhist"].append(pv(s))
    if len(s["pvhist"]) > MAXHIST: del s["pvhist"][0]

def chart_pts(s, asset):
    h = s["history"].get(asset, [])
    fast, slow = s["strat"]["fast"], s["strat"]["slow"]
    start = max(0, len(h)-CHARTPTS)
    return [{"i": i, "p": round(h[i],4),
             "f": round(sma(h[:i+1],fast),4) if sma(h[:i+1],fast) else None,
             "s": round(sma(h[:i+1],slow),4) if sma(h[:i+1],slow) else None,
             "r": round(rsi_val(h[:i+1]),2)} for i in range(start, len(h))]

def win_rate(trades):
    s = [t for t in trades if t["side"]=="SELL" and t.get("pnl") is not None]
    if not s: return None
    return round(len([t for t in s if t["pnl"]>0])/len(s)*100, 1)

def snap(s):
    pos = {}
    for asset, p in s["portfolio"]["pos"].items():
        pr = s["prices"].get(asset, 0); mv = p["qty"]*pr
        pos[asset] = {"qty": round(p["qty"],8), "avg": round(p["avg"],4), "mv": round(mv,2),
                      "upnl": round((pr-p["avg"])*p["qty"],2) if p["qty"]>0 else 0., "sl": p["sl"], "tp": p["tp"]}
    tv = pv(s); pnl = tv-INIT_CASH
    return {"tick": s["tick"], "mode": s["mode"], "vix": get_india_vix(),
            "prices": {k: round(v,4) for k,v in s["prices"].items()},
            "cash": round(s["portfolio"]["cash"],2), "pos": pos,
            "tv": round(tv,2), "pnl": round(pnl,2), "pnlpct": round(pnl/INIT_CASH*100,2),
            "ddpct": round(max_dd(s["pvhist"])*100,2), "wr": win_rate(s["trades"]),
            "trades": s["trades"][:50], "pending": s["pending"], "strat": s["strat"],
            "pvhist": s["pvhist"][-CHARTPTS:],
            "charts": {a: chart_pts(s,a) for a in list(ASSETS.keys())[:12]},
            "assets": {k: v["name"] for k,v in ASSETS.items()}, "initcash": INIT_CASH,
            "watchlist": s["watchlist"], "chartink_symbols": s["chartink_symbols"],
            "has_push": HAS_PUSH, "vapid_public_key": VAPID_PUBLIC_KEY}

def backtest_real_or_sim(asset, strat, fast, slow, nticks, seed=None, rules=None):
    ohlc = None
    if HAS_YF:
        ohlc, _ = fetch_ohlc(asset, period="1y", interval="1d")
    if ohlc:
        closes = ohlc["c"][-nticks:] if nticks < len(ohlc["c"]) else ohlc["c"]
        highs = ohlc["h"][-len(closes):]; lows = ohlc["l"][-len(closes):]; opens = ohlc["o"][-len(closes):]
    else:
        rng = random.Random(seed) if seed is not None else random.Random()
        cfg = ASSETS.get(asset, {"p0":100.0,"mu":0.0001,"sigma":0.02})
        price = cfg["p0"]; closes = [price]
        for _ in range(nticks):
            price = max(0.01, price*math.exp((cfg["mu"]-0.5*cfg["sigma"]**2)+cfg["sigma"]*rng.gauss(0,1)))
            closes.append(price)
        highs = [c*1.002 for c in closes]; lows = [c*0.998 for c in closes]; opens = closes[:]
    cash = INIT_CASH; qty=0.; avg=0.; trades=[]; pvs=[cash]
    for i in range(1, len(closes)):
        hist = closes[:i+1]; price = closes[i]; sig = None
        if strat == "sma":
            cf,cs = sma(hist,fast), sma(hist,slow); pf,ps = sma(hist[:-1],fast), sma(hist[:-1],slow)
            if None not in (cf,cs,pf,ps):
                if pf<=ps and cf>cs: sig="BUY"
                elif pf>=ps and cf<cs: sig="SELL"
        elif strat == "rsi":
            r = rsi_val(hist); sig = "BUY" if r<30 else ("SELL" if r>70 else None)
        elif strat == "custom" and rules:
            for rule in rules:
                if eval_rule(rule, hist, price):
                    sig = rule["action"]; break
        if sig == "BUY" and cash>1:
            bq = math.floor(cash*AUTOFRAC/price*1e8)/1e8
            if bq>0:
                nq=qty+bq; avg=(avg*qty+price*bq)/nq if nq else 0; qty=nq; cash-=bq*price
                trades.append({"side":"BUY","price":price})
        elif sig == "SELL" and qty>0:
            cash += qty*price; trades.append({"side":"SELL","price":price,"avg":avg}); qty=0.; avg=0.
        pvs.append(cash+qty*price)
    fv = pvs[-1]; pnl = fv-INIT_CASH
    sells = [t for t in trades if t["side"]=="SELL"]
    wins = [t for t in sells if t["price"]>t.get("avg",0)]
    wr = round(len(wins)/len(sells)*100,1) if sells else None
    stride = max(1, len(closes)//150)
    return {"asset": asset, "strat": strat, "nticks": len(closes),
            "fv": round(fv,2), "pnl": round(pnl,2), "pnlpct": round(pnl/INIT_CASH*100,2),
            "ddpct": round(max_dd(pvs)*100,2), "ntrades": len(trades), "wr": wr,
            "o": [round(o,4) for o in opens[::stride]] if ohlc else None,
            "h": [round(h,4) for h in highs[::stride]] if ohlc else None,
            "l": [round(l,4) for l in lows[::stride]] if ohlc else None,
            "ph": [round(p,4) for p in closes[::stride]], "pvh": [round(v,2) for v in pvs[::stride]],
            "used_real_data": ohlc is not None}

SCAN_STATUS = {"running": False, "last": "Never", "nextin": SCANEVERY, "tickers": []}
SCAN_LOCK = threading.Lock()

def live_price_updater():
    while True:
        try:
            vix = get_india_vix()
            with LOCK:
                symbols = list(ASSETS.keys())
            for sym in symbols:
                real = fetch_last_price(sym) if HAS_YF else None
                with LOCK:
                    if real is not None:
                        STATE["prices"][sym] = real
                    else:
                        cfg = ASSETS[sym]
                        STATE["prices"][sym] = gbm(STATE["prices"].get(sym, cfg["p0"]), cfg["mu"], cfg["sigma"])
                    h = STATE["history"].setdefault(sym, [STATE["prices"][sym]])
                    h.append(STATE["prices"][sym])
                    if len(h) > MAXHIST: del h[0]
            with LOCK:
                engine_step(STATE, vix)
                save_state(STATE)
        except Exception as e:
            print("live_price_updater error:", e)
        time.sleep(LIVE_INTERVAL)

def background_scanner():
    while True:
        with LOCK:
            watchlist = list(STATE["watchlist"])
            seen = STATE.get("seen_patterns", {})
        with SCAN_LOCK:
            SCAN_STATUS["running"] = True; SCAN_STATUS["tickers"] = []
        for ticker in watchlist:
            ohlc, err = fetch_ohlc(ticker)
            with SCAN_LOCK:
                SCAN_STATUS["tickers"].append(f"{ticker}: {'scanned' if ohlc else 'skip('+str(err)+')'}")
            if ohlc:
                closes = ohlc["c"]
                r = rsi_val(closes)
                rsi_key = f"{ticker}_rsi_{len(closes)}"
                if (r < 30 or r > 70) and seen.get(rsi_key) != True:
                    push_alert(ticker, "RSI Extreme", "BULLISH" if r<30 else "BEARISH", closes[-1], f"RSI={r:.1f}")
                    seen[rsi_key] = True
                patterns = detect_candle_patterns(ohlc)
                for p in patterns:
                    pat_key = f"{ticker}_{p['pattern']}_{p['index']}"
                    if seen.get(pat_key) != True:
                        push_alert(ticker, p["pattern"] + " (reversal)", p["direction"], closes[-1],
                                    "Candlestick pattern detected")
                        seen[pat_key] = True
        with LOCK:
            STATE["seen_patterns"] = seen
            if len(STATE["seen_patterns"]) > 2000:
                STATE["seen_patterns"] = dict(list(STATE["seen_patterns"].items())[-1000:])
            save_state(STATE)
        with SCAN_LOCK:
            SCAN_STATUS["running"] = False; SCAN_STATUS["last"] = datetime.now(timezone.utc).strftime("%H:%M UTC")
            SCAN_STATUS["nextin"] = SCANEVERY
        for i in range(SCANEVERY, 0, -1):
            time.sleep(1)
            with SCAN_LOCK: SCAN_STATUS["nextin"] = i

threading.Thread(target=live_price_updater, daemon=True).start()
threading.Thread(target=background_scanner, daemon=True).start()

@app.route("/")
def index(): return MAIN_HTML

@app.route("/health")
def health(): return jsonify(ok=True, status="running", tick=STATE["tick"])

@app.route("/manifest.json")
def manifest():
    m = {"name":"ECC Trading Suite","short_name":"ECC","description":"Personal paper trading + scanner",
         "start_url":"/","display":"standalone","background_color":"#0d1117","theme_color":"#0d1117",
         "orientation":"portrait","icons":[{"src":"/icon.svg","sizes":"any","type":"image/svg+xml","purpose":"any maskable"}]}
    return Response(json.dumps(m), mimetype="application/json")

@app.route("/sw.js")
def service_worker():
    js = """
self.addEventListener('install', e => self.skipWaiting());
self.addEventListener('activate', e => self.clients.claim());
self.addEventListener('push', e => {
  let data = {title:'ECC Trading', body:'New alert'};
  try { data = e.data.json(); } catch(err) {}
  e.waitUntil(self.registration.showNotification(data.title, {
    body: data.body, tag: data.tag || 'ecc-alert', icon: '/icon.svg', badge: '/icon.svg'
  }));
});
self.addEventListener('notificationclick', e => {
  e.notification.close();
  e.waitUntil(clients.matchAll({type:'window'}).then(cl => {
    for (const c of cl) if ('focus' in c) return c.focus();
    if (clients.openWindow) return clients.openWindow('/');
  }));
});
"""
    return Response(js, mimetype="application/javascript")

@app.route("/icon.svg")
def app_icon():
    svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100"><rect width="100" height="100" rx="22" fill="#0d1117"/><polyline points="15,70 30,45 45,60 60,30 75,50 85,35" fill="none" stroke="#3fb950" stroke-width="7" stroke-linecap="round" stroke-linejoin="round"/><circle cx="85" cy="35" r="5" fill="#3fb950"/></svg>"""
    return Response(svg, mimetype="image/svg+xml")

@app.route("/api/state")
def api_state():
    with LOCK: return jsonify(ok=True, state=snap(STATE))

@app.route("/api/tick", methods=["POST"])
def api_tick():
    with LOCK:
        engine_step(STATE)
        save_state(STATE)
        return jsonify(ok=True, state=snap(STATE))

@app.route("/api/reset", methods=["POST"])
def api_reset():
    global STATE
    with LOCK:
        STATE = mk_state()
        save_state(STATE)
        return jsonify(ok=True, state=snap(STATE))

@app.route("/api/mode", methods=["POST"])
def api_mode():
    d = request.get_json(silent=True) or {}
    mode = d.get("mode","GLOBAL")
    if mode not in ("INDIA","GLOBAL"): return jsonify(ok=False, error="Invalid mode"), 400
    with LOCK:
        STATE["mode"] = mode
        default_wl = (["RELIANCE.NS","TCS.NS","INFY.NS","HDFCBANK.NS","NSEI","BANKNIFTY.NS"]
                       if mode=="INDIA" else ["BTC-USD","ETH-USD","AAPL","TSLA","EURUSD=X"])
        for sym in default_wl:
            ensure_asset(STATE, sym)
            if sym not in STATE["watchlist"]: STATE["watchlist"].append(sym)
        save_state(STATE)
        return jsonify(ok=True, state=snap(STATE))

@app.route("/api/search", methods=["POST"])
def api_search():
    d = request.get_json(silent=True) or {}
    q = d.get("query","")
    if not q: return jsonify(ok=False, error="Enter a symbol"), 400
    info, err = search_symbol(q)
    if err: return jsonify(ok=False, error=err), 400
    with LOCK:
        ensure_asset(STATE, info["symbol"], info["last_price"])
        if info["symbol"] not in STATE["watchlist"]: STATE["watchlist"].append(info["symbol"])
        save_state(STATE)
        s = snap(STATE)
    return jsonify(ok=True, info=info, state=s)

@app.route("/api/watchlist/add", methods=["POST"])
def api_watchlist_add():
    d = request.get_json(silent=True) or {}
    sym = (d.get("symbol") or "").strip().upper()
    if not sym: return jsonify(ok=False, error="Enter a symbol"), 400
    with LOCK:
        ensure_asset(STATE, sym)
        if sym not in STATE["watchlist"]: STATE["watchlist"].append(sym)
        save_state(STATE)
        return jsonify(ok=True, state=snap(STATE))

@app.route("/api/watchlist/remove", methods=["POST"])
def api_watchlist_remove():
    d = request.get_json(silent=True) or {}
    sym = (d.get("symbol") or "").strip().upper()
    with LOCK:
        STATE["watchlist"] = [w for w in STATE["watchlist"] if w != sym]
        save_state(STATE)
        return jsonify(ok=True, state=snap(STATE))

@app.route("/api/chartink", methods=["POST"])
def api_chartink():
    d = request.get_json(silent=True) or {}
    slug = d.get("slug","")
    if not slug: return jsonify(ok=False, error="Paste your Chartink screener URL or slug"), 400
    symbols, err = chartink_screener(slug)
    if err: return jsonify(ok=False, error=err), 400
    with LOCK:
        STATE["chartink_symbols"] = symbols
        for sym in symbols:
            nse_sym = sym if sym.endswith(".NS") else sym+".NS"
            ensure_asset(STATE, nse_sym)
            if nse_sym not in STATE["watchlist"]: STATE["watchlist"].append(nse_sym)
        save_state(STATE)
    return jsonify(ok=True, symbols=symbols)

@app.route("/api/order", methods=["POST"])
def api_order():
    d = request.get_json(silent=True) or {}
    asset = d.get("asset"); side = d.get("side"); otype = d.get("ordertype","MARKET")
    if not asset: return jsonify(ok=False, error="Missing asset"), 400
    if side not in ("BUY","SELL"): return jsonify(ok=False, error="Invalid side"), 400
    try: qty = float(d.get("qty"))
    except Exception: return jsonify(ok=False, error="Invalid quantity"), 400
    if not math.isfinite(qty) or qty<=0: return jsonify(ok=False, error="Quantity must be positive"), 400
    def pof(k):
        v = d.get(k)
        if v in (None,"","null"): return None
        try:
            f = float(v); return f if math.isfinite(f) else None
        except Exception: return None
    sl = pof("sl") if side=="BUY" else None
    tp = pof("tp") if side=="BUY" else None
    lp = pof("limitprice") if otype=="LIMIT" else None
    if otype=="LIMIT" and (lp is None or lp<=0): return jsonify(ok=False, error="Limit price must be positive"), 400
    with LOCK:
        ensure_asset(STATE, asset)
        pnow = STATE["prices"][asset]
        if sl is not None and sl>=pnow: return jsonify(ok=False, error="Stop-loss must be below current price"), 400
        if tp is not None and tp<=pnow: return jsonify(ok=False, error="Take-profit must be above current price"), 400
        if otype=="MARKET":
            ok, msg = exec_order(STATE, asset, side, qty, sl=sl, tp=tp)
        else:
            STATE["pending"].append({"id": int(time.time()*1000),"asset":asset,"side":side,"qty":qty,"lp":lp})
            ok, msg = True, f"Limit {side} {qty:g} {asset} @ {lp:.4f}"
        save_state(STATE)
        s = snap(STATE)
    if ok: return jsonify(ok=True, message=msg, state=s)
    return jsonify(ok=False, error=msg, state=s), 400

@app.route("/api/strategy", methods=["POST"])
def api_strategy():
    d = request.get_json(silent=True) or {}
    t = d.get("type","manual")
    if t not in ("manual","sma","rsi","custom"): return jsonify(ok=False, error="Invalid strategy"), 400
    with LOCK:
        if t == "custom":
            mode = d.get("input_mode","text")
            if mode == "text":
                rules, err = parse_plain_english(d.get("rule_text",""))
                if err: return jsonify(ok=False, error=err), 400
                STATE["strat"]["rule_text"] = d.get("rule_text","")
            else:
                rules = d.get("rules", [])
            STATE["strat"]["rules"] = rules
        try:
            fast = int(d.get("fast",5)); slow = int(d.get("slow",20))
        except Exception:
            return jsonify(ok=False, error="fast/slow must be integers"), 400
        STATE["strat"].update(type=t, fast=fast, slow=slow, active=bool(d.get("active", False)))
        save_state(STATE)
        return jsonify(ok=True, state=snap(STATE))

@app.route("/api/backtest", methods=["POST"])
def api_backtest():
    d = request.get_json(silent=True) or {}
    asset = d.get("asset","BTC-USD"); strat = d.get("strat","sma")
    try:
        fast = int(d.get("fast",5)); slow = int(d.get("slow",20)); nt = int(d.get("nt",500))
    except Exception:
        return jsonify(ok=False, error="Invalid parameters"), 400
    nt = max(10, min(nt, MAXBT))
    rules = d.get("rules")
    return jsonify(ok=True, result=backtest_real_or_sim(asset, strat, fast, slow, nt, rules=rules))

@app.route("/api/vix")
def api_vix(): return jsonify(ok=True, vix=get_india_vix())

@app.route("/api/alerts")
def api_alerts():
    with ALERT_LOCK: return jsonify(ok=True, alerts=list(ALERTS))

@app.route("/api/scanstatus")
def api_scanstatus():
    with SCAN_LOCK: return jsonify(ok=True, hasyf=HAS_YF, status=dict(SCAN_STATUS))

@app.route("/api/push/vapid_public_key")
def api_push_vapid():
    return jsonify(ok=True, key=VAPID_PUBLIC_KEY, enabled=HAS_PUSH)

@app.route("/api/push/subscribe", methods=["POST"])
def api_push_subscribe():
    sub = request.get_json(silent=True)
    if not sub or "endpoint" not in sub:
        return jsonify(ok=False, error="Invalid subscription"), 400
    with LOCK:
        if sub not in STATE["push_subs"]:
            STATE["push_subs"].append(sub)
            save_state(STATE)
    return jsonify(ok=True, enabled=HAS_PUSH)

@app.route("/api/push/unsubscribe", methods=["POST"])
def api_push_unsubscribe():
    sub = request.get_json(silent=True)
    with LOCK:
        STATE["push_subs"] = [s for s in STATE["push_subs"] if s.get("endpoint") != (sub or {}).get("endpoint")]
        save_state(STATE)
    return jsonify(ok=True)

@app.route("/api/events")
def api_events():
    def stream():
        q = queue.Queue()
        with ALERT_LOCK: SSE_CLIENTS.append(q)
        try:
            while True:
                try:
                    a = q.get(timeout=20)
                    yield f"data: {json.dumps(a)}\n\n"
                except queue.Empty:
                    yield ": ping\n\n"
        finally:
            with ALERT_LOCK:
                try: SSE_CLIENTS.remove(q)
                except Exception: pass
    return Response(stream(), mimetype="text/event-stream", headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})

@app.route("/api/export")
def api_export():
    with LOCK: trades = list(STATE["trades"])
    buf = io.StringIO(); w = csv.writer(buf)
    w.writerow(["id","tick","time","asset","side","qty","price","via","pnl"])
    for t in reversed(trades):
        w.writerow([t["id"],t["tick"],t["ts"],t["asset"],t["side"],t["qty"],t["price"],t["via"],t["pnl"]])
    return Response(buf.getvalue(), mimetype="text/csv", headers={"Content-Disposition":"attachment;filename=trades.csv"})

MAIN_HTML = r"""<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="theme-color" content="#0d1117">
<link rel="manifest" href="/manifest.json"><link rel="apple-touch-icon" href="/icon.svg">
<title>ECC Trading Suite v4</title>
<style>
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
body{background:#0d1117;color:#e6edf3;font-family:-apple-system,Segoe UI,Roboto,sans-serif;font-size:17px;margin:0;padding-bottom:80px}
.hdr{background:#161b22;border-bottom:1px solid #21262d;padding:14px 16px;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;z-index:100;gap:10px;flex-wrap:wrap}
.brand{font-size:17px;font-weight:700}
.hdr-val{font-size:22px;font-weight:700;font-family:ui-monospace,monospace}
.btn{padding:11px 18px;border-radius:22px;border:none;cursor:pointer;font-weight:700;font-size:15px;min-height:46px}
.btn-g{background:#1a5c30;color:#3fb950}.btn-a{background:#5c4a1a;color:#d29922}.btn-o{background:transparent;border:1px solid #30363d;color:#8b949e}.btn-b{background:#1a3a5c;color:#58a6ff}
.card{background:#161b22;border:1px solid #21262d;border-radius:14px;padding:16px;margin:14px}
.ctitle{font-weight:700;font-size:15px;color:#8b949e;text-transform:uppercase;letter-spacing:.5px;margin-bottom:10px}
.inp,select{width:100%;padding:12px;border-radius:10px;font-size:16px;border:1px solid #30363d;background:#0d1117;color:#e6edf3;margin-bottom:10px;min-height:46px}
.mode-tog{display:flex;gap:8px;margin:14px}
.mode-tog button{flex:1}
.chart-tog{display:flex;gap:6px;margin-bottom:8px}
.chart-tog button{flex:1;padding:8px;font-size:13px;min-height:38px}
.chart-tog button.sel{background:#1a3a5c;color:#58a6ff;border-radius:8px;border:1px solid #2a5a8c}
canvas{width:100%;display:block;border-radius:8px;background:#0a0d12}
.side-row{display:flex;gap:8px;margin-bottom:10px}
.side-btn{flex:1;padding:14px;border-radius:10px;border:1.5px solid #21262d;background:transparent;color:#8b949e;font-weight:700;font-size:16px}
.side-btn.buy{background:#1a5c30;color:#3fb950;border-color:#1a5c30}
.side-btn.sell{background:#5c1a1a;color:#f85149;border-color:#5c1a1a}
.exec-btn{width:100%;padding:16px;border-radius:12px;border:none;font-weight:700;font-size:17px}
.exec-btn.buy{background:#1a5c30;color:#3fb950}.exec-btn.sell{background:#5c1a1a;color:#f85149}
.tbl{width:100%;border-collapse:collapse;font-size:14px}
.tbl th{text-align:left;color:#6e7681;padding:6px 4px;font-size:12px}
.tbl td{padding:8px 4px;border-bottom:1px solid #1c2128}
.metrics{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-top:10px}
.metric{background:#0d1117;border-radius:10px;padding:12px;text-align:center}
.m-lbl{font-size:12px;color:#6e7681;margin-bottom:5px}
.m-val{font-size:19px;font-weight:700;font-family:ui-monospace,monospace}
.tab{display:none;padding:0}
.tab.active{display:block}
.bnav{position:fixed;bottom:0;left:0;right:0;background:#161b22;border-top:1px solid #21262d;display:flex;z-index:100}
.bnav-btn{flex:1;padding:10px 4px;border:none;background:transparent;color:#6e7681;font-size:11px;font-weight:600;min-height:62px}
.bnav-btn.active{color:#58a6ff}
.info-box{background:#161b22;border:1px solid #21262d;border-radius:12px;padding:14px;margin:14px}
.info-title{font-weight:700;font-size:15px;color:#58a6ff;margin-bottom:8px}
.info-text{font-size:14px;color:#8b949e;line-height:1.7}
code{background:#0d1117;padding:2px 6px;border-radius:4px;color:#d29922}
.vix-badge{font-size:13px;font-weight:700;padding:4px 10px;border-radius:12px;background:#1a3a5c;color:#58a6ff}
.toast{position:fixed;top:12px;left:50%;transform:translateX(-50%) translateY(-80px);padding:12px 20px;border-radius:20px;font-size:14px;font-weight:600;transition:transform .3s;z-index:200}
.toast.show{transform:translateX(-50%) translateY(0)}
.toast.ok{background:#1a5c30;color:#3fb950}.toast.err{background:#5c1a1a;color:#f85149}
.wl-row{display:flex;justify-content:space-between;align-items:center;padding:12px;border-bottom:1px solid #1c2128}
.wl-sym{font-weight:700;font-size:15px}
.wl-price{font-family:ui-monospace,monospace;color:#8b949e;font-size:14px}
.wl-remove{background:#5c1a1a;color:#f85149;border:none;border-radius:8px;padding:8px 12px;font-size:13px;font-weight:600}
.wl-select{background:#1a3a5c;color:#58a6ff;border:none;border-radius:8px;padding:8px 12px;font-size:13px;font-weight:600}
.pattern-badge{display:inline-block;font-size:10px;font-weight:700;padding:3px 8px;border-radius:8px;margin-left:6px}
.pattern-badge.bull{background:#1a5c30;color:#3fb950}
.pattern-badge.bear{background:#5c1a1a;color:#f85149}
.live-dot{width:8px;height:8px;border-radius:50%;display:inline-block;margin-right:5px}
.live-dot.on{background:#3fb950;box-shadow:0 0 6px #3fb950}
.live-dot.off{background:#6e7681}
</style></head><body>
<div id="toast" class="toast"></div>
<header class="hdr">
  <div><div class="brand">ECC Trading v4</div><div style="font-size:11px;color:#6e7681"><span class="live-dot on" id="liveDot"></span>Live background engine</div></div>
  <div style="text-align:center"><div id="hdrVal" class="hdr-val">$10,000.00</div><div id="hdrPnl" style="font-size:13px">0.00 (0.00%)</div></div>
  <div style="display:flex;gap:8px;align-items:center">
    <span id="vixBadge" class="vix-badge">VIX --</span>
    <button class="btn btn-o" onclick="resetBot()">Reset</button>
  </div>
</header>

<div class="mode-tog">
  <button id="modeIndia" class="btn btn-o" onclick="setMode('INDIA')">India Market</button>
  <button id="modeGlobal" class="btn btn-b" onclick="setMode('GLOBAL')">Global / Forex</button>
</div>

<div id="tab-trade" class="tab active">
  <div class="card">
    <div class="ctitle">Search any symbol</div>
    <input id="symSearch" class="inp" placeholder="e.g. RELIANCE, TCS, NIFTY, BTC-USD, EURUSD=X">
    <button class="btn btn-b" style="width:100%" onclick="doSearch()">Search, Add &amp; Open Chart</button>
    <div id="searchResult" style="font-size:13px;color:#8b949e;margin-top:8px"></div>
  </div>

  <div class="card">
    <select id="assetSel" class="inp" onchange="selectAsset()"></select>
    <div class="chart-tog">
      <button class="btn btn-o" id="ctLine" onclick="setChartType('line')">Line</button>
      <button class="btn btn-o" id="ctCandle" onclick="setChartType('candle')">Candle</button>
      <button class="btn btn-o" id="ctBar" onclick="setChartType('bar')">Bar</button>
    </div>
    <canvas id="priceChart" style="height:280px"></canvas>
    <div id="patternInfo" style="font-size:13px;margin-top:8px"></div>
  </div>

  <div class="card">
    <div class="ctitle">Place order</div>
    <div class="side-row">
      <button id="buyBtn" class="side-btn buy" onclick="setSide('BUY')">BUY</button>
      <button id="sellBtn" class="side-btn" onclick="setSide('SELL')">SELL</button>
    </div>
    <select id="oType" class="inp" onchange="updateOType()">
      <option value="MARKET">Market order</option><option value="LIMIT">Limit order</option>
    </select>
    <input id="qty" type="number" step="any" min="0" placeholder="Quantity" class="inp">
    <div id="limitRow" style="display:none"><input id="limitPx" type="number" step="any" placeholder="Limit price" class="inp"></div>
    <div id="slTpRow" style="display:flex;gap:8px">
      <input id="sl" type="number" step="any" placeholder="Stop-loss (optional)" class="inp">
      <input id="tp" type="number" step="any" placeholder="Take-profit (optional)" class="inp">
    </div>
    <button id="execBtn" class="exec-btn buy" onclick="placeOrder()">Execute BUY</button>
  </div>

  <div class="card"><div class="ctitle">Portfolio</div>
    <canvas id="portChart" style="height:100px"></canvas>
  </div>

  <div class="card"><div class="ctitle">Positions</div>
    <table class="tbl"><thead><tr><th>Asset</th><th>Qty</th><th>Value</th><th>uPnL</th></tr></thead><tbody id="posTbl"></tbody></table>
  </div>

  <div class="card"><div class="ctitle">Trade log</div>
    <table class="tbl"><thead><tr><th>Time</th><th>Asset</th><th>Side</th><th>Price</th><th>PnL</th></tr></thead><tbody id="tradeTbl"></tbody></table>
  </div>
</div>

<div id="tab-watch" class="tab">
  <div class="card">
    <div class="ctitle">Add to watchlist</div>
    <input id="wlAdd" class="inp" placeholder="e.g. INFY, HDFCBANK, ETH-USD">
    <button class="btn btn-g" style="width:100%" onclick="addToWatchlist()">Add Symbol</button>
  </div>
  <div class="card" style="padding:0;overflow:hidden">
    <div style="padding:14px;border-bottom:1px solid #21262d;font-weight:700">Your watchlist</div>
    <div id="wlList"></div>
  </div>
</div>

<div id="tab-strat" class="tab">
  <div class="card">
    <div class="ctitle">Quick strategies (no code)</div>
    <select id="stratType" class="inp" onchange="updateStratUI()">
      <option value="manual">Manual only</option>
      <option value="sma">SMA Crossover</option>
      <option value="rsi">RSI Mean Reversion</option>
      <option value="custom">Custom rule (English or dropdown)</option>
    </select>
    <div id="smaP" style="display:none;gap:8px" class="side-row">
      <input id="fast" type="number" min="2" max="50" class="inp" value="5" placeholder="Fast">
      <input id="slow" type="number" min="3" max="100" class="inp" value="20" placeholder="Slow">
    </div>
  </div>

  <div id="customBox" class="card" style="display:none">
    <div class="ctitle">Describe your strategy in plain English</div>
    <input id="ruleText" class="inp" placeholder="e.g. buy when rsi below 30">
    <button class="btn btn-b" style="width:100%;margin-bottom:12px" onclick="applyCustomText()">Apply English Rule</button>
    <div style="font-size:13px;color:#6e7681;margin-bottom:14px">
      Examples: <code>buy when rsi below 30</code> - <code>sell when price above 250</code> -
      <code>buy when 5 sma crosses above 20 sma</code> - <code>buy when hammer pattern forms</code>
    </div>
    <div class="ctitle">Or build with dropdowns</div>
    <select id="ddIndicator" class="inp">
      <option value="RSI">RSI</option><option value="PRICE">Price</option>
      <option value="VIX">India VIX</option><option value="MACD">MACD</option>
      <option value="SMA_CROSS">SMA Crossover</option><option value="BOLL">Bollinger Bands</option>
    </select>
    <select id="ddOp" class="inp">
      <option value="<">is below</option><option value=">">is above</option>
    </select>
    <input id="ddValue" type="number" class="inp" placeholder="Value (e.g. 30)">
    <select id="ddAction" class="inp"><option value="BUY">BUY</option><option value="SELL">SELL</option></select>
    <button class="btn btn-o" style="width:100%" onclick="applyDropdownRule()">Apply Dropdown Rule</button>
  </div>

  <div class="card" style="display:flex;justify-content:space-between;align-items:center">
    <label style="display:flex;gap:8px;align-items:center;font-size:15px"><input type="checkbox" id="stratActive" style="width:20px;height:20px"> Strategy Active (auto-trades, runs even when app closed)</label>
    <button class="btn btn-o" onclick="finalizeStrat()">Save</button>
  </div>
  <div id="stratHint" style="font-size:13px;color:#6e7681;margin:0 14px"></div>

  <div class="card"><div class="metrics">
    <div class="metric"><div class="m-lbl">Win rate</div><div id="mWin" class="m-val">--</div></div>
    <div class="metric"><div class="m-lbl">Total trades</div><div id="mTrades" class="m-val">0</div></div>
    <div class="metric"><div class="m-lbl">Max drawdown</div><div id="mDD" class="m-val">0%</div></div>
    <div class="metric"><div class="m-lbl">Cash left</div><div id="mCash" class="m-val">--</div></div>
  </div></div>
</div>

<div id="tab-scan" class="tab">
  <div class="card">
    <div class="ctitle">Chartink screener import</div>
    <input id="chartinkSlug" class="inp" placeholder="Paste your Chartink screener URL">
    <button class="btn btn-b" style="width:100%" onclick="pullChartink()">Pull Symbols into Watchlist</button>
    <div style="font-size:12px;color:#6e7681;margin-top:8px">Chartink has no official API - uses their public screener endpoint, may need a fix if they change their site.</div>
    <div id="chartinkResult" style="font-size:13px;color:#8b949e;margin-top:8px"></div>
  </div>
  <div class="card"><div class="ctitle">Scanner status</div>
    <div id="scanStatusTxt" style="font-size:14px">loading...</div>
    <div id="nextIn" style="color:#6e7681;font-size:12px;margin-top:6px"></div>
    <div style="font-size:12px;color:#6e7681;margin-top:8px">Scans watchlist every 5 min for RSI extremes AND candlestick reversal patterns (Hammer, Engulfing, Doji, Morning/Evening Star, Shooting Star). Runs in background even with the app closed, as long as the server is awake.</div>
  </div>
  <div class="card" style="padding:0;overflow:hidden">
    <div style="padding:14px;border-bottom:1px solid #21262d;display:flex;justify-content:space-between">
      <span style="font-weight:700">Detected signals</span>
      <button class="btn btn-o" style="padding:6px 12px;min-height:32px;font-size:12px" onclick="clearAlerts()">Clear</button>
    </div>
    <div id="alertList"></div>
    <div id="noAlerts" style="text-align:center;padding:30px;color:#6e7681">No signals yet.</div>
  </div>
</div>

<div id="tab-bt" class="tab">
  <div class="card">
    <div class="ctitle">Backtest settings</div>
    <input id="btAsset" class="inp" placeholder="Any symbol e.g. RELIANCE.NS, BTC-USD" value="RELIANCE.NS">
    <select id="btStrat" class="inp"><option value="sma">SMA Crossover</option><option value="rsi">RSI Mean Reversion</option></select>
    <div class="side-row"><input id="btFast" type="number" value="5" min="2" class="inp" placeholder="Fast"><input id="btSlow" type="number" value="20" min="3" class="inp" placeholder="Slow"></div>
    <input id="btTicks" type="number" value="500" min="10" max="5000" class="inp" placeholder="Bars">
    <button id="btBtn" class="btn btn-b" style="width:100%" onclick="runBT()">Run Backtest</button>
  </div>
  <div id="btResults" style="display:none">
    <div class="card"><div class="metrics">
      <div class="metric"><div class="m-lbl">Final value</div><div id="btFV" class="m-val">--</div></div>
      <div class="metric"><div class="m-lbl">P/L</div><div id="btPnl" class="m-val">--</div></div>
      <div class="metric"><div class="m-lbl">Max drawdown</div><div id="btDD" class="m-val">--</div></div>
      <div class="metric"><div class="m-lbl">Win rate</div><div id="btWR" class="m-val">--</div></div>
    </div></div>
    <div class="card"><canvas id="btPriceC" style="height:220px"></canvas></div>
    <div class="card"><canvas id="btPortC" style="height:100px"></canvas></div>
  </div>
</div>

<div id="tab-help" class="tab">
  <div class="info-box"><div class="info-title">Keep this running 24/7 (required)</div>
  <div class="info-text">Render's free tier sleeps after ~15 min idle. Use <b>UptimeRobot</b> (free) to ping
  <code>/health</code> every 5 minutes so background scanning + live prices + notifications never stop.<br><br>
  1. Sign up free at uptimerobot.com<br>2. New Monitor -&gt; HTTP(s)<br>3. URL: your-render-url/health<br>4. Interval: 5 minutes</div></div>

  <div class="info-box"><div class="info-title">Mobile notifications - enable once per device</div>
  <div class="info-text">Android/Chrome: tap Enable below, works directly, even with app fully closed.<br>
  iPhone/Safari: you MUST tap Share -&gt; Add to Home Screen FIRST, then open the app icon and tap Enable - this is an Apple restriction on regular browser tabs, not fixable by any website.</div>
  <button class="btn btn-b" style="margin-top:10px" onclick="enablePush()">Enable Background Notifications</button>
  <div id="pushStatus" style="font-size:12px;color:#6e7681;margin-top:8px"></div></div>

  <div class="info-box"><div class="info-title">Real live prices</div>
  <div class="info-text">Prices refresh from real market data roughly every 45 seconds via Yahoo Finance. This is delayed data, not exchange-grade tick data - fine for practice, not for real execution timing.</div></div>

  <div class="info-box"><div class="info-title">Data is now saved</div>
  <div class="info-text">Your trades, portfolio and watchlist are saved to the server disk and survive restarts/sleep cycles. They reset only if you deploy new code that wipes the state file.</div></div>

  <div class="info-box"><div class="info-title">Sensibull</div>
  <div class="info-text">Sensibull has no public/demo API for third-party apps. This site simulates paper trading internally instead.</div></div>
</div>

<nav class="bnav">
  <button class="bnav-btn active" onclick="showTab('trade',this)">Trade</button>
  <button class="bnav-btn" onclick="showTab('watch',this)">Watchlist</button>
  <button class="bnav-btn" onclick="showTab('strat',this)">Strategy</button>
  <button class="bnav-btn" onclick="showTab('scan',this)">Alerts</button>
  <button class="bnav-btn" onclick="showTab('bt',this)">Backtest</button>
  <button class="bnav-btn" onclick="showTab('help',this)">Help</button>
</nav>

<script>
let selAsset='BTC-USD', currentSide='BUY', lastState=null, chartType='candle', currentMode='GLOBAL', refreshTimer=null;

function showTab(id,btn){
  document.querySelectorAll('.tab').forEach(t=>t.classList.remove('active'));
  document.querySelectorAll('.bnav-btn').forEach(b=>b.classList.remove('active'));
  document.getElementById('tab-'+id).classList.add('active'); btn.classList.add('active');
  if(id==='scan'){loadAlerts();pollScanStatus();}
  if(id==='watch'){renderWatchlist();}
}
let toastT=null;
function toast(msg,cls='ok'){const el=document.getElementById('toast');el.textContent=msg;el.className='toast show '+cls;clearTimeout(toastT);toastT=setTimeout(()=>el.className='toast',3000);}
async function api(path,method='GET',body){
  const opts={method,headers:{}};
  if(body){opts.headers['Content-Type']='application/json';opts.body=JSON.stringify(body);}
  const res=await fetch(path,opts);
  let d; try{d=await res.json();}catch(e){d={};}
  if(!res.ok){d.ok=false;throw new Error(d.error||('Error '+res.status));}
  return d;
}
function setMode(m){
  currentMode=m;
  document.getElementById('modeIndia').className='btn '+(m==='INDIA'?'btn-b':'btn-o');
  document.getElementById('modeGlobal').className='btn '+(m==='GLOBAL'?'btn-b':'btn-o');
  api('/api/mode','POST',{mode:m}).then(d=>{lastState=d.state;render(d.state);}).catch(e=>toast(e.message,'err'));
}

async function doSearch(){
  const q=document.getElementById('symSearch').value;
  if(!q){toast('Enter a symbol','err');return;}
  try{
    const d=await api('/api/search','POST',{query:q});
    document.getElementById('searchResult').innerHTML=
      `Found <b>${d.info.symbol}</b> @ ${d.info.last_price} | F&amp;O available: ${d.info.has_fno?'YES':'NO'} | ${d.info.is_indian?'Indian market':'Global market'}`;
    toast('Added '+d.info.symbol+' - chart opened');
    lastState=d.state; render(d.state);
    selAsset=d.info.symbol;
    document.getElementById('assetSel').value=selAsset;
    renderChart();
  }catch(e){document.getElementById('searchResult').textContent=e.message;toast(e.message,'err');}
}
async function addToWatchlist(){
  const sym=document.getElementById('wlAdd').value.trim();
  if(!sym){toast('Enter a symbol','err');return;}
  try{
    const d=await api('/api/watchlist/add','POST',{symbol:sym});
    lastState=d.state; render(d.state); renderWatchlist();
    document.getElementById('wlAdd').value='';
    toast(sym.toUpperCase()+' added to watchlist');
  }catch(e){toast(e.message,'err');}
}
async function removeFromWatchlist(sym){
  try{
    const d=await api('/api/watchlist/remove','POST',{symbol:sym});
    lastState=d.state; render(d.state); renderWatchlist();
    toast(sym+' removed');
  }catch(e){toast(e.message,'err');}
}
function renderWatchlist(){
  if(!lastState)return;
  const list=document.getElementById('wlList');
  list.innerHTML='';
  (lastState.watchlist||[]).forEach(sym=>{
    const price=lastState.prices[sym];
    const div=document.createElement('div');div.className='wl-row';
    div.innerHTML=`<div><div class="wl-sym">${sym}</div><div class="wl-price">${price!=null?price:'--'}</div></div>
      <div style="display:flex;gap:6px">
        <button class="wl-select" onclick="jumpToAsset('${sym}')">Chart</button>
        <button class="wl-remove" onclick="removeFromWatchlist('${sym}')">Remove</button>
      </div>`;
    list.appendChild(div);
  });
}
function jumpToAsset(sym){
  selAsset=sym;
  showTab('trade', document.querySelector('.bnav-btn'));
  document.getElementById('assetSel').value=sym;
  renderChart();
}
async function pullChartink(){
  const slug=document.getElementById('chartinkSlug').value;
  if(!slug){toast('Paste a Chartink URL','err');return;}
  try{
    const d=await api('/api/chartink','POST',{slug});
    document.getElementById('chartinkResult').textContent='Pulled: '+d.symbols.join(', ');
    toast(d.symbols.length+' symbols added');
    refresh();
  }catch(e){document.getElementById('chartinkResult').textContent=e.message;toast(e.message,'err');}
}
function fmv(v){if(v==null||isNaN(v))return'--';const s=v<0?'-':'';const a=Math.abs(v);return s+(a>=10000?(a/1000).toFixed(2)+'k':a.toFixed(2));}
function fp(v){return v==null?'--':(v>0?'+':'')+v.toFixed(2);}

function drawChart(id,series,type='line'){
  const c=document.getElementById(id); if(!c)return;
  const dpr=window.devicePixelRatio||1,cw=c.clientWidth||300,ch=parseInt(c.style.height)||150;
  c.width=Math.round(cw*dpr);c.height=Math.round(ch*dpr);
  const ctx=c.getContext('2d');ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,cw,ch);
  if(!series||!series.length)return;
  let allVals=[];
  series.forEach(pt=>{['p','o','h','l','c'].forEach(k=>{if(pt[k]!=null)allVals.push(pt[k]);});});
  if(allVals.length<2)return;
  let mn=Math.min(...allVals),mx=Math.max(...allVals);
  if(mn===mx){mn-=1;mx+=1;}
  const pad=(mx-mn)*0.1;mn-=pad;mx+=pad;
  const lp=56,rp=8,tp=10,bp=10,pw=cw-lp-rp,ph=ch-tp-bp;
  ctx.strokeStyle='#1c2530';ctx.fillStyle='#6e7681';ctx.font='11px ui-monospace,monospace';ctx.lineWidth=1;
  for(let i=0;i<=4;i++){const y=tp+ph*i/4,val=mx-(mx-mn)*i/4;ctx.beginPath();ctx.moveTo(lp,y);ctx.lineTo(cw-rp,y);ctx.stroke();ctx.fillText(fmv(val),4,y+4);}
  const n=series.length;
  const xAt=i=> lp + pw*(i/(Math.max(n-1,1)));
  const yAt=v=> tp + ph*(1-(v-mn)/(mx-mn));
  if(type==='line'){
    ctx.beginPath();ctx.strokeStyle='#3fb950';ctx.lineWidth=2.5;
    series.forEach((pt,i)=>{const v=pt.p??pt.c;if(v==null)return;const x=xAt(i),y=yAt(v);i===0?ctx.moveTo(x,y):ctx.lineTo(x,y);});
    ctx.stroke();
  } else if(type==='candle'){
    const bw=Math.max(4,Math.min(18,pw/n*0.7));
    series.forEach((pt,i)=>{
      const o=pt.o??pt.p,h=pt.h??pt.p,l=pt.l??pt.p,cl=pt.c??pt.p; if(o==null)return;
      const x=xAt(i),up=cl>=o;ctx.strokeStyle=up?'#3fb950':'#f85149';ctx.fillStyle=up?'#3fb950':'#f85149';
      ctx.lineWidth=1.5;
      ctx.beginPath();ctx.moveTo(x,yAt(h));ctx.lineTo(x,yAt(l));ctx.stroke();
      const yo=yAt(o),yc=yAt(cl);
      const bodyH=Math.max(2,Math.abs(yo-yc));
      ctx.fillRect(x-bw/2,Math.min(yo,yc),bw,bodyH);
    });
  } else if(type==='bar'){
    const bw=Math.max(3,Math.min(14,pw/n*0.6));
    series.forEach((pt,i)=>{const v=pt.p??pt.c;if(v==null)return;const x=xAt(i),y=yAt(v);ctx.fillStyle='#58a6ff';ctx.fillRect(x-bw/2,y,bw,ch-bp-y);});
  }
}
function setChartType(t){
  chartType=t;
  ['ctLine','ctCandle','ctBar'].forEach(id=>document.getElementById(id).classList.remove('sel'));
  document.getElementById('ct'+t.charAt(0).toUpperCase()+t.slice(1)).classList.add('sel');
  renderChart();
}
function renderChart(){
  if(!lastState)return;
  const series=lastState.charts&&lastState.charts[selAsset]?lastState.charts[selAsset]:[];
  drawChart('priceChart',series,chartType);
  drawChart('portChart',(lastState.pvhist||[]).map(v=>({p:v})),'line');
}
setChartType('candle');

let pushSub=null;
async function enablePush(){
  if(!('Notification' in window)||!('serviceWorker' in navigator)){toast('Not supported in this browser','err');return;}
  const perm=await Notification.requestPermission();
  if(perm!=='granted'){toast('Denied - enable in browser settings','err');return;}
  try{
    const reg=await navigator.serviceWorker.register('/sw.js');
    await navigator.serviceWorker.ready;
    const keyData=await api('/api/push/vapid_public_key');
    if(!keyData.enabled){document.getElementById('pushStatus').textContent='Server push not configured yet (pywebpush missing) - ask admin to install it.';toast('Push not fully configured on server','err');return;}
    const key=urlBase64ToUint8Array(keyData.key);
    const sub=await reg.pushManager.subscribe({userVisibleOnly:true,applicationServerKey:key});
    await api('/api/push/subscribe','POST',sub.toJSON());
    document.getElementById('pushStatus').textContent='Enabled! You will get alerts even when this app is closed.';
    toast('Background notifications enabled');
  }catch(e){document.getElementById('pushStatus').textContent='Error: '+e.message;toast(e.message,'err');}
}
function urlBase64ToUint8Array(base64String){
  const padding='='.repeat((4-base64String.length%4)%4);
  const base64=(base64String+padding).replace(/-/g,'+').replace(/_/g,'/');
  const raw=atob(base64);const out=new Uint8Array(raw.length);
  for(let i=0;i<raw.length;++i)out[i]=raw.charCodeAt(i);
  return out;
}

function fireLocalNotif(a){
  if(typeof Notification==='undefined'||Notification.permission!=='granted')return;
  const bull=a.direction.includes('BULL');
  new Notification((bull?'BULLISH ':'BEARISH ')+a.asset+' '+a.pattern,{body:a.direction+' @ '+a.price+' '+a.time,tag:a.asset+a.pattern});
}
function connectSSE(){
  const es=new EventSource('/api/events');
  es.onmessage=e=>{const a=JSON.parse(e.data);fireLocalNotif(a);addAlert(a);toast(a.asset+' '+a.pattern);};
  es.onerror=()=>{setTimeout(connectSSE,5000);es.close();};
}
connectSSE();
function addAlert(a){
  const list=document.getElementById('alertList');document.getElementById('noAlerts').style.display='none';
  const bull=a.direction.includes('BULL');
  const div=document.createElement('div');div.style.padding='12px';div.style.borderBottom='1px solid #21262d';
  div.innerHTML=`<b>${a.asset}</b> - ${a.pattern} <span class="pattern-badge ${bull?'bull':'bear'}">${a.direction}</span><br><span style="color:#6e7681;font-size:12px">${a.time} @ ${a.price} ${a.detail||''}</span>`;
  list.insertBefore(div,list.firstChild);
  if(list.children.length>80)list.lastChild.remove();
}
async function loadAlerts(){
  try{const d=await api('/api/alerts');if(d.alerts.length)document.getElementById('noAlerts').style.display='none';
  document.getElementById('alertList').innerHTML='';d.alerts.slice().reverse().forEach(addAlert);}catch(e){}
}
function clearAlerts(){document.getElementById('alertList').innerHTML='';document.getElementById('noAlerts').style.display='block';}
async function pollScanStatus(){
  try{const d=await api('/api/scanstatus');const s=d.status;
    const txt=document.getElementById('scanStatusTxt');
    if(!d.hasyf)txt.textContent='yfinance not installed - install for live scanning';
    else if(s.running)txt.textContent='Scanning...';
    else txt.textContent='Last scan: '+s.last;
    document.getElementById('nextIn').textContent='Next scan in '+Math.round(s.nextin/60)+' min';
  }catch(e){}
}
setInterval(()=>{if(document.getElementById('tab-scan').classList.contains('active'))pollScanStatus();},10000);

function setSide(s){
  currentSide=s;
  document.getElementById('buyBtn').className='side-btn'+(s==='BUY'?' buy':'');
  document.getElementById('sellBtn').className='side-btn'+(s==='SELL'?' sell':'');
  document.getElementById('execBtn').className='exec-btn '+(s==='BUY'?'buy':'sell');
  document.getElementById('execBtn').textContent='Execute '+s;
  document.getElementById('slTpRow').style.display=s==='BUY'?'flex':'none';
}
setSide('BUY');
function updateOType(){document.getElementById('limitRow').style.display=document.getElementById('oType').value==='LIMIT'?'block':'none';}

function selectAsset(){selAsset=document.getElementById('assetSel').value;renderChart();}
function updateAssetSelect(){
  const sel=document.getElementById('assetSel');
  const assets=lastState?Object.keys(lastState.assets):[];
  const cur=sel.value;
  sel.innerHTML=assets.map(a=>`<option value="${a}">${a} - ${lastState.assets[a]}</option>`).join('');
  if(assets.includes(cur)){sel.value=cur;} else if(assets.includes(selAsset)){sel.value=selAsset;} else if(assets.length){selAsset=assets[0];sel.value=selAsset;}
}

function updateStratUI(){
  const t=document.getElementById('stratType').value;
  document.getElementById('smaP').style.display=t==='sma'?'flex':'none';
  document.getElementById('customBox').style.display=t==='custom'?'block':'none';
}
async function applyCustomText(){
  try{
    const d=await api('/api/strategy','POST',{type:'custom',input_mode:'text',rule_text:document.getElementById('ruleText').value,active:document.getElementById('stratActive').checked});
    lastState=d.state;render(d.state);toast('English rule applied');
  }catch(e){toast(e.message,'err');}
}
async function applyDropdownRule(){
  const rule={indicator:document.getElementById('ddIndicator').value,op:document.getElementById('ddOp').value,
    value:parseFloat(document.getElementById('ddValue').value)||0,action:document.getElementById('ddAction').value};
  try{
    const d=await api('/api/strategy','POST',{type:'custom',input_mode:'dropdown',rules:[rule],active:document.getElementById('stratActive').checked});
    lastState=d.state;render(d.state);toast('Dropdown rule applied');
  }catch(e){toast(e.message,'err');}
}
async function finalizeStrat(){
  const t=document.getElementById('stratType').value;
  try{
    const body={type:t,fast:parseInt(document.getElementById('fast').value),slow:parseInt(document.getElementById('slow').value),active:document.getElementById('stratActive').checked};
    const d=await api('/api/strategy','POST',body);lastState=d.state;render(d.state);toast('Strategy saved - runs in background');
  }catch(e){toast(e.message,'err');}
}
updateStratUI();

async function placeOrder(){
  const qty=parseFloat(document.getElementById('qty').value);
  if(!qty||qty<=0){toast('Enter a valid quantity','err');return;}
  const otype=document.getElementById('oType').value;
  const body={asset:selAsset,side:currentSide,ordertype:otype,qty};
  if(currentSide==='BUY'){body.sl=document.getElementById('sl').value||null;body.tp=document.getElementById('tp').value||null;}
  if(otype==='LIMIT')body.limitprice=document.getElementById('limitPx').value||null;
  try{
    const d=await api('/api/order','POST',body);lastState=d.state;render(d.state);toast(d.message);
    ['qty','sl','tp','limitPx'].forEach(id=>{const el=document.getElementById(id);if(el)el.value='';});
  }catch(e){toast(e.message,'err');}
}

async function runBT(){
  const body={asset:document.getElementById('btAsset').value,strat:document.getElementById('btStrat').value,
    fast:parseInt(document.getElementById('btFast').value),slow:parseInt(document.getElementById('btSlow').value),
    nt:parseInt(document.getElementById('btTicks').value)};
  try{
    const d=await api('/api/backtest','POST',body);const r=d.result;
    document.getElementById('btResults').style.display='block';
    document.getElementById('btFV').textContent=fmv(r.fv);
    document.getElementById('btPnl').textContent=fp(r.pnl)+' ('+fp(r.pnlpct)+'%)';
    document.getElementById('btDD').textContent=r.ddpct+'%';
    document.getElementById('btWR').textContent=(r.wr==null?'--':r.wr+'%');
    drawChart('btPriceC',r.ph.map((p,i)=>({p, o:r.o?r.o[i]:null,h:r.h?r.h[i]:null,l:r.l?r.l[i]:null,c:p})),r.used_real_data?'candle':'line');
    drawChart('btPortC',r.pvh.map(v=>({p:v})),'line');
    toast(r.used_real_data?'Backtest ran on real historical data':'Backtest ran on simulated data (symbol not found live)');
  }catch(e){toast(e.message,'err');}
}

function render(s){
  document.getElementById('hdrVal').textContent='$'+fmv(s.tv);
  document.getElementById('hdrPnl').textContent=fp(s.pnl)+' ('+fp(s.pnlpct)+'%)';
  document.getElementById('hdrPnl').style.color=s.pnl>=0?'#3fb950':'#f85149';
  document.getElementById('vixBadge').textContent='VIX '+(s.vix??'--');
  updateAssetSelect();
  const posTbl=document.getElementById('posTbl');posTbl.innerHTML='';
  Object.entries(s.pos).forEach(([a,p])=>{if(p.qty>0)posTbl.innerHTML+=`<tr><td>${a}</td><td>${p.qty}</td><td>$${fmv(p.mv)}</td><td style="color:${p.upnl>=0?'#3fb950':'#f85149'}">${fp(p.upnl)}</td></tr>`;});
  const tt=document.getElementById('tradeTbl');tt.innerHTML='';
  s.trades.slice(0,15).forEach(t=>{tt.innerHTML+=`<tr><td>${t.ts}</td><td>${t.asset}</td><td>${t.side}</td><td>${t.price}</td><td style="color:${(t.pnl||0)>=0?'#3fb950':'#f85149'}">${t.pnl??'--'}</td></tr>`;});
  document.getElementById('mWin').textContent=(s.wr==null?'--':s.wr+'%');
  document.getElementById('mTrades').textContent=s.trades.length;
  document.getElementById('mDD').textContent=s.ddpct+'%';
  document.getElementById('mCash').textContent='$'+fmv(s.cash);
  if(document.getElementById('tab-watch').classList.contains('active'))renderWatchlist();
  renderChart();
}
async function refresh(){try{const d=await api('/api/state');lastState=d.state;render(d.state);}catch(e){}}
refreshTimer=setInterval(refresh, 5000);
refresh();
</script>
</body></html>"""

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=PORT, debug=False)

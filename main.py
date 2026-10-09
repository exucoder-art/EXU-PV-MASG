import hashlib, hmac, os, time, json, threading, sqlite3, secrets, re, base64
import sys, unicodedata, io, html
import urllib.request, urllib.error, socket, ipaddress
from urllib.parse import urlparse, urljoin, quote

from flask import Flask, request, jsonify, Response, send_file
from werkzeug.security import generate_password_hash, check_password_hash
from flask_socketio import SocketIO, join_room, emit, leave_room

# ─────────────────────────────── CONFIG ────────────────────────────────
ADMIN_PASS = "npm run dev"          # <-- change this
SITE_NAME  = "EXU CHAT"
GROUP_NAME = "Main Group"
# Files next to main.py:
#   group.png / group.jpg / group.jpeg / group.webp / group.gif
#   group_bg.png / group_bg.jpg / group_bg.jpeg / group_bg.webp / group_bg.gif
# DB:  chat.db
# Port: 8080

_HERE = os.path.dirname(os.path.abspath(__file__))
DB    = os.path.join(_HERE, "chat.db")

def _load_img(base):
    for ext, mime in ((".png","image/png"),(".jpg","image/jpeg"),
                      (".jpeg","image/jpeg"),(".webp","image/webp"),
                      (".gif","image/gif")):
        p = os.path.join(_HERE, base + ext)
        if os.path.isfile(p):
            try:
                with open(p,"rb") as f:
                    return f.read(), mime
            except OSError:
                return None, None
    return None, None

GROUP_PIC, GROUP_PIC_MIME = _load_img("group")
GROUP_BG,  GROUP_BG_MIME  = _load_img("group_bg")

def _load_file(name, mime_default="image/png"):
    """Load a static file next to main.py into memory."""
    for n in (name,):
        p = os.path.join(_HERE, n)
        if os.path.isfile(p):
            try:
                with open(p, "rb") as f:
                    return f.read(), mime_default
            except OSError:
                pass
    return None, None

FAVICON_ICO, _ = _load_file("favicon.ico", "image/x-icon")
FAVICON_PNG, _ = _load_file("favicon.png", "image/png")
if not FAVICON_PNG:
    FAVICON_PNG, _ = _load_file("favicon-32.png", "image/png")
APPLE_TOUCH, _ = _load_file("apple-touch-icon.png", "image/png")
# fallback: use group logo as favicon if dedicated files missing
if not FAVICON_PNG and GROUP_PIC:
    FAVICON_PNG, _ = GROUP_PIC, (GROUP_PIC_MIME or "image/png")
if not FAVICON_ICO and FAVICON_PNG:
    FAVICON_ICO = FAVICON_PNG  # browsers accept PNG at /favicon.ico sometimes

# ─────────────────────────────── APP ───────────────────────────────────
app = Flask(__name__)
app.config["SECRET_KEY"] = secrets.token_hex(32)
socketio = SocketIO(app, async_mode="threading", cors_allowed_origins="*",
                    ping_interval=10, ping_timeout=25)

lock = threading.RLock()

users      = {}   # sid -> {uid, name, room}
history    = {}   # room_key -> [msg,...]
calls      = {}   # room_key -> call dict
_seen      = {}
_hits      = {}

ROOM_DEFAULT = "g:default"

# ─────────────────────────────── DB ────────────────────────────────────
def db():
    c = sqlite3.connect(DB, timeout=15)
    c.row_factory = sqlite3.Row
    return c

with db() as _c:
    try: _c.execute("pragma journal_mode=wal")
    except sqlite3.DatabaseError: pass
    _c.executescript("""
    create table if not exists users(
        id integer primary key, username text unique, pw text,
        name text, avatar text, ts integer, seen integer);
    create table if not exists sess(token text primary key, uid integer);

    create table if not exists friends(
        a integer, b integer, status text, ts integer,
        primary key(a,b));
    create index if not exists friends_b on friends(b);

    create table if not exists groups(
        id integer primary key autoincrement,
        name text, pic text, owner integer, private integer default 0,
        ts integer, default_g integer default 0);
    create table if not exists members(
        gid integer, uid integer, ts integer,
        primary key(gid,uid));
    create index if not exists members_uid on members(uid);

    create table if not exists msgs(
        seq integer primary key autoincrement,
        room text, mid text, cid text, name text, text text, ts integer,
        pv text, au integer, dur integer, wv text, cl text, im integer);

    create index if not exists msgs_room on msgs(room,seq);

    create table if not exists reactions(
        mid text, uid integer, emoji text, ts integer,
        primary key(mid,uid));

    create table if not exists audio(
        id integer primary key autoincrement, mime text, data blob);

    create table if not exists images(
        id integer primary key autoincrement, mime text, data blob);

    create table if not exists dels(n integer primary key autoincrement, mid text);

    create table if not exists bans(
        uname text primary key, uid integer, name text, ts integer);
    """)

# Ensure `im` column exists (for users upgrading from old DB)
with db() as _c:
    try:
        cols = [r["name"] for r in _c.execute("pragma table_info(msgs)").fetchall()]
        if "im" not in cols:
            _c.execute("alter table msgs add column im integer")
    except sqlite3.DatabaseError:
        pass

# Ensure `verified` column exists on users
with db() as _c:
    try:
        cols = [r["name"] for r in _c.execute("pragma table_info(users)").fetchall()]
        if "verified" not in cols:
            _c.execute("alter table users add column verified integer default 0")
    except sqlite3.DatabaseError:
        pass

# ensure default group exists
with db() as _c:
    r = _c.execute("select id from groups where default_g=1").fetchone()
    if not r:
        _c.execute(
            "insert into groups(name,pic,owner,private,ts,default_g) values(?,?,?,?,?,1)",
            (GROUP_NAME, None, 0, 0, int(time.time()*1000)))
        gid = _c.execute("select id from groups where default_g=1").fetchone()["id"]
    else:
        gid = r["id"]
DEFAULT_GID = gid

def room_of(gid):       return "g:%d" % gid
def dm_room(a, b):
    a, b = sorted((int(a), int(b)))
    return "d:%d:%d" % (a, b)

# ─────────────────────────────── HELPERS ───────────────────────────────
def _int(v, d=0):
    try: return int(v)
    except (TypeError, ValueError): return d

def _client_ip():
    xf = request.headers.get("X-Forwarded-For","")
    return (xf.split(",")[-1].strip() if xf else request.remote_addr) or "?"

def _blocked(key, limit, window):
    now = time.time()
    if len(_hits) > 5000: _hits.clear()
    fresh = [t for t in _hits.get(key,[]) if now - t < window]
    _hits[key] = fresh
    return len(fresh) >= limit

def _hit(key):
    _hits.setdefault(key,[]).append(time.time())

def me_json(r):
    return {"id": r["id"], "username": r["username"],
            "name": r["name"] or r["username"], "av": bool(r["avatar"]),
            "verified": bool(r["verified"]) if "verified" in r.keys() else False}

def user_is_verified(uid):
    """Return True if user id is verified."""
    try:
        with db() as c:
            row = c.execute("select verified from users where id=?", (_int(uid),)).fetchone()
        return bool(row and row["verified"])
    except Exception:
        return False

def users_verified_map(uids):
    """Map of str(uid) -> bool for a batch of user ids."""
    ids = []
    for u in uids:
        try:
            ids.append(int(u))
        except (TypeError, ValueError):
            pass
    if not ids:
        return {}
    out = {}
    try:
        with db() as c:
            q = "select id, verified from users where id in (%s)" % (",".join("?" * len(ids)))
            for row in c.execute(q, ids):
                out[str(row["id"])] = bool(row["verified"])
    except Exception:
        pass
    return out

def user_by_token(t):
    if not t: return None
    with db() as c:
        return c.execute(
            "select u.* from sess s join users u on u.id=s.uid "
            "where s.token=? and lower(u.username) not in (select uname from bans)",
            (t,)).fetchone()

def new_session(uid):
    t = secrets.token_urlsafe(32)
    with db() as c:
        c.execute("insert into sess values(?,?)",(t,uid))
    return t

def is_admin():
    try:
        exp, sig = request.cookies.get("exu_adm","").split(".",1)
        return int(exp) > time.time() and secrets.compare_digest(
            sig, _adm_token(int(exp)).split(".",1)[1])
    except Exception:
        return False

# ── history cache
def load_hist(room):
    with db() as c:
        rows = c.execute("select * from msgs where room=? order by seq desc limit 500",
                         (room,)).fetchall()
        rxs = {}
        for x in c.execute(
                "select r.mid, r.uid, r.emoji, coalesce(nullif(u.name,''),u.username) n "
                "from reactions r join users u on u.id=r.uid "
                "where r.mid in (select mid from msgs where room=?) order by r.ts",
                (room,)):
            rxs.setdefault(x["mid"],[]).append([str(x["uid"]),x["emoji"],x["n"]])
    out = []
    for r in reversed(rows):
        m = {"mid":r["mid"],"cid":r["cid"],"name":r["name"],
             "text":r["text"],"ts":r["ts"],"seq":r["seq"]}
        if r["pv"]:
            try: m["pv"] = json.loads(r["pv"])
            except Exception: pass
        if r["au"]:
            m["au"], m["dur"] = r["au"], r["dur"] or 0
            if r["wv"]: m["wv"] = r["wv"]
        if r["cl"]:
            try: m["cl"] = json.loads(r["cl"])
            except Exception: pass
        try:
            if r["im"]: m["im"] = r["im"]
        except (IndexError, KeyError):
            pass
        if rxs.get(r["mid"]): m["rx"] = rxs[r["mid"]]
        out.append(m)
    # Attach verified flags for message authors
    vmap = users_verified_map(m["cid"] for m in out)
    for m in out:
        if vmap.get(str(m["cid"])):
            m["verified"] = True
    return out

def get_hist(room):
    with lock:
        if room not in history:
            history[room] = load_hist(room)
        return history[room]

# ── room membership
def is_member(uid, gid):
    with db() as c:
        return bool(c.execute("select 1 from members where gid=? and uid=?",
                              (gid,uid)).fetchone())

def can_access(uid, room):
    if room.startswith("d:"):
        try:
            _, a, b = room.split(":")
            a, b = int(a), int(b)
        except ValueError:
            return False
        if uid not in (a, b): return False
        with db() as c:
            x, y = sorted((a,b))
            return bool(c.execute(
                "select 1 from friends where a=? and b=? and status='ok'",
                (x,y)).fetchone())
    if room.startswith("g:"):
        gid = _int(room[2:])
        with db() as c:
            r = c.execute("select default_g,private,owner from groups where id=?",
                          (gid,)).fetchone()
        if not r: return False
        if r["default_g"]: return True
        if r["owner"] == uid: return True
        return is_member(uid, gid)
    return False

def room_users(room):
    seen, out = set(), []
    for s,u in list(users.items()):
        if u["room"] == room and u["uid"] not in seen:
            seen.add(u["uid"])
            out.append({"id": s, "name": u["name"], "uid": u["uid"]})
    return out

def touch(uid):
    uid = _int(uid)
    if not uid: return
    now = time.time()
    if now - _seen.get(uid,0) < 20: return
    _seen[uid] = now
    try:
        with db() as c:
            c.execute("update users set seen=? where id=?",(int(now*1000),uid))
    except Exception:
        pass

# ── admin token
_ADM_KEY = None
def _adm_key():
    global _ADM_KEY
    if _ADM_KEY is None:
        _ADM_KEY = (ADMIN_PASS + "|" + app.config["SECRET_KEY"]).encode()
    return _ADM_KEY

def _adm_token(exp):
    return "%d.%s" % (exp, hmac.new(_adm_key(), str(exp).encode(),
                                    hashlib.sha256).hexdigest())

def _adm_json(data, code=200):
    r = jsonify(data); r.status_code = code
    r.headers["Cache-Control"] = "no-store"
    return r

# ── link previews (SSRF-safe)
URL_RE = re.compile(r"https?://[^\s<]+")

class _NoRedir(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*a,**k): return None
_opener = urllib.request.build_opener(_NoRedir)

def safe_fetch(url, limit=400000):
    for _ in range(4):
        p = urlparse(url)
        if p.scheme not in ("http","https") or not p.hostname: return None
        try:
            for ai in socket.getaddrinfo(p.hostname, None):
                if not ipaddress.ip_address(ai[4][0]).is_global: return None
        except Exception:
            return None
        req = urllib.request.Request(url, headers={
            "User-Agent":"facebookexternalhit/1.1","Accept-Language":"en"})
        try:
            r = _opener.open(req, timeout=6)
            return r.geturl(), r.read(limit).decode("utf-8","ignore")
        except urllib.error.HTTPError as e:
            if e.code in (301,302,303,307,308):
                url = urljoin(url, e.headers.get("Location","")); continue
            return None
        except Exception:
            return None
    return None

def get_preview(url):
    host = (urlparse(url).hostname or "").replace("www.","")
    pv = {"url":url, "site":host}
    oe = None
    if host.endswith("tiktok.com"):
        oe = "https://www.tiktok.com/oembed?url=" + quote(url, safe="")
    elif host.endswith("youtube.com") or host == "youtu.be":
        oe = "https://www.youtube.com/oembed?format=json&url=" + quote(url, safe="")
    if oe:
        r = safe_fetch(oe)
        try:
            d = json.loads(r[1])
            pv.update(title=d.get("title"), image=d.get("thumbnail_url"),
                      site=d.get("provider_name") or host, desc=d.get("author_name"))
        except Exception: pass
    if not pv.get("title"):
        r = safe_fetch(url)
        if r:
            h = r[1]
            def og(k):
                m = (re.search(r'<meta[^>]+(?:property|name)=["\']%s["\'][^>]*content=["\']([^"\']*)' % k, h, re.I)
                     or re.search(r'<meta[^>]+content=["\']([^"\']*)["\'][^>]+(?:property|name)=["\']%s["\']' % k, h, re.I))
                return html.unescape(m.group(1)) if m else None
            pv["title"] = og("og:title") or og("twitter:title")
            pv["image"] = og("og:image") or og("twitter:image")
            pv["site"]  = og("og:site_name") or host
            pv["desc"]  = og("og:description")
            if not pv["title"]:
                t = re.search(r"<title[^>]*>(.*?)</title>", h, re.I|re.S)
                pv["title"] = html.unescape(t.group(1).strip()) if t else None
    for k in ("title","desc","site"):
        if pv.get(k): pv[k] = str(pv[k])[:160]
    if pv.get("image") and not str(pv["image"]).startswith("http"):
        pv["image"] = None
    return pv

def make_preview(room, m, url):
    try: pv = get_preview(url)
    except Exception: pv = {"url":url,"site":urlparse(url).hostname or ""}
    m["pv"] = pv
    try:
        with db() as c:
            c.execute("update msgs set pv=? where seq=?",(json.dumps(pv),m["seq"]))
    except Exception: pass
    socketio.emit("preview",{"mid":m["mid"],"pv":pv}, to=room)

def del_sync(dv, fresh):
    with db() as c:
        if fresh:
            return [], c.execute("select coalesce(max(n),0) from dels").fetchone()[0]
        rows = c.execute("select n, mid from dels where n>? order by n limit 500",
                         (dv,)).fetchall()
    return [r["mid"] for r in rows], (rows[-1]["n"] if rows else dv)

def rx_map(room):
    return {m["mid"]: m["rx"] for m in get_hist(room) if m.get("rx")}

# ── calls
def cstate(room):
    c = calls.get(room)
    if not c: return None
    return {"video":c["video"],"starter":c["starter_name"],
            "starter_id":c["starter"],"ringing":not c["connected"],
            "parts":[{"id":s,"name":users[s]["name"]} for s in c["parts"] if s in users]}

def push_state(room):
    socketio.emit("call_state", cstate(room), to=room)

def _fmt_dur(s):
    s = max(0,int(s)); h,m,sec = s//3600, s%3600//60, s%60
    return f"{h}:{m:02d}:{sec:02d}" if h else f"{m:02d}:{sec:02d}"

def log_call(room, c, reason):
    try:
        video = bool(c["video"])
        if c["connected"]:
            res, dur = "done", int(time.time() - (c.get("t0") or time.time()))
        elif reason == "declined": res, dur = "declined", 0
        elif reason == "no_answer": res, dur = "missed", 0
        else: res, dur = "cancel", 0
        kind = "video" if video else "voice"
        text = f"{kind.capitalize()} call · {_fmt_dur(dur)}" if res=="done" else f"Missed {kind} call"
        cl = {"v":video,"r":res,"d":dur}
        ts = int(time.time()*1000); mid = secrets.token_hex(6)
        with lock:
            h = get_hist(room)
            with db() as cx:
                seq = cx.execute(
                    "insert into msgs(room,mid,cid,name,text,ts,cl) values(?,?,?,?,?,?,?)",
                    (room,mid,c["starter_cid"],c["starter_name"],text,ts,json.dumps(cl))
                ).lastrowid
            m = {"mid":mid,"cid":c["starter_cid"],"name":c["starter_name"],
                 "text":text,"ts":ts,"seq":seq,"cl":cl}
            h.append(m)
            socketio.emit("msg", m, to=room)
    except Exception: pass

def end_call(room, reason):
    c = calls.pop(room, None)
    if not c: return
    socketio.emit("call_ended",{"reason":reason}, to=room)
    push_state(room)
    log_call(room, c, reason)

def leave_call(sid):
    u = users.get(sid)
    if not u: return
    room = u["room"]
    with lock:
        c = calls.get(room)
        if not c or sid not in c["parts"]: return
        c["parts"].discard(sid)
        socketio.emit("call_left", sid, to=room)
        if not c["parts"] or (c["connected"] and len(c["parts"])<=1) or \
           (not c["connected"] and sid == c["starter"]):
            end_call(room,"ended")
        else:
            push_state(room)

def ring_timeout(room, c):
    time.sleep(45)
    with lock:
        if calls.get(room) is c and not c["connected"]:
            end_call(room,"no_answer")

def ice_servers():
    return [{"urls":"stun:stun.l.google.com:19302"},
            {"urls":"stun:stun1.l.google.com:19302"}]

# ═══════════════════════════ REST ROUTES ═══════════════════════════════
@app.after_request
def _safe_headers(r):
    r.headers.setdefault("X-Content-Type-Options","nosniff")
    return r

@app.get("/api/config")
def api_config():
    return jsonify(
        site=SITE_NAME,
        group=GROUP_NAME,
        gid=DEFAULT_GID,
        hasPic=bool(GROUP_PIC),
        hasBg=bool(GROUP_BG),
    )

@app.post("/api/register")
def api_register():
    if _blocked("reg:"+_client_ip(), 60, 3600):
        return jsonify(error="Too many sign-ups from this network. Try again later."), 429
    d = request.get_json(silent=True) or {}
    u = re.sub(r"\s+"," ",(d.get("username") or "").strip())
    p = d.get("password") or ""
    if not re.fullmatch(r"[A-Za-z0-9_.]{3,20}", u):
        return jsonify(error="Username: 3-20 letters, numbers, . or _"), 400
    if len(p) < 6:
        return jsonify(error="Password must be at least 6 characters"), 400
    name = re.sub(r"\s+"," ",(d.get("name") or "").strip())[:40] or u
    try:
        with db() as c:
            if c.execute("select 1 from bans where uname=lower(?)",(u,)).fetchone():
                return jsonify(error="banned"), 403
            if c.execute("select 1 from users where lower(username)=lower(?)",(u,)).fetchone():
                return jsonify(error="Username already taken"), 400
            now = int(time.time()*1000)
            cur = c.execute(
                "insert into users(username,pw,name,ts,seen) values(?,?,?,?,?)",
                (u, generate_password_hash(p), name, now, now))
            uid = cur.lastrowid
            c.execute("insert or ignore into members(gid,uid,ts) values(?,?,?)",
                      (DEFAULT_GID, uid, now))
    except sqlite3.IntegrityError:
        return jsonify(error="Username already taken"), 400
    _hit("reg:"+_client_ip())
    tok = new_session(uid)
    return jsonify(token=tok, me=me_json(user_by_token(tok)))

@app.post("/api/login")
def api_login():
    d = request.get_json(silent=True) or {}
    ip = _client_ip() + ":" + re.sub(r"\s+"," ",str(d.get("username") or "").strip()).lower()[:20]
    if _blocked("login:"+ip, 10, 600):
        return jsonify(error="Too many attempts. Try again in a few minutes."), 429
    with db() as c:
        r = c.execute("select * from users where lower(username)=lower(?)",
                      (re.sub(r"\s+"," ",(d.get("username") or "").strip()),)).fetchone()
    if not r or not check_password_hash(r["pw"], str(d.get("password") or "")):
        _hit("login:"+ip)
        return jsonify(error="Wrong username or password"), 400
    with db() as c:
        if c.execute("select 1 from bans where uname=lower(?)",(r["username"],)).fetchone():
            return jsonify(error="banned"), 403
        c.execute("update users set seen=? where id=?",(int(time.time()*1000),r["id"]))
        c.execute("insert or ignore into members(gid,uid,ts) values(?,?,?)",
                  (DEFAULT_GID, r["id"], int(time.time()*1000)))
    tok = new_session(r["id"])
    return jsonify(token=tok, me=me_json(r))

@app.post("/api/me")
def api_me():
    r = user_by_token((request.get_json(silent=True) or {}).get("token"))
    return (jsonify(me=me_json(r)), 200) if r else (jsonify(error="auth"), 401)

@app.post("/api/logout")
def api_logout():
    with db() as c:
        c.execute("delete from sess where token=?",
                  ((request.get_json(silent=True) or {}).get("token"),))
    return jsonify(ok=True)

# ── PROFILE (name + avatar upload + avatar removal) ──
@app.post("/api/profile")
def api_profile():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401

    name = (d.get("name") or "").strip()[:24] or r["username"]

    av_update = None       # None → don't touch avatar
    if d.get("remove_avatar"):
        av_update = ""     # empty string → clear avatar
    else:
        av = d.get("avatar")
        if isinstance(av, str) and 0 < len(av) <= 200000 and \
           re.match(r"data:image/(png|jpeg|webp|gif);base64,", av):
            try:
                base64.b64decode(av.split(",", 1)[1], validate=True)
                av_update = av
            except Exception:
                pass

    with db() as c:
        if av_update is None:
            c.execute("update users set name=? where id=?", (name, r["id"]))
        else:
            c.execute("update users set name=?, avatar=? where id=?",
                      (name, av_update or None, r["id"]))
    return jsonify(me=me_json(user_by_token(d.get("token"))))

@app.get("/avatar/<int:uid>")
def avatar(uid):
    with db() as c:
        r = c.execute("select avatar from users where id=?",(uid,)).fetchone()
    if not r or not r["avatar"]: return "", 404
    head, b64 = r["avatar"].split(",",1)
    mime = head[5:].split(";")[0]
    if mime not in ("image/png","image/jpeg","image/webp","image/gif"): return "", 404
    try: raw = base64.b64decode(b64)
    except Exception: return "", 404
    return Response(raw, mimetype=mime, headers={"Cache-Control":"public, max-age=120"})

# ── USER SEARCH ──
@app.get("/api/search/users")
def api_search_users():
    r = user_by_token(request.args.get("t"))
    if not r: return jsonify(error="auth"), 401
    q = (request.args.get("q") or "").strip().lower()
    if len(q) < 1:
        return jsonify(users=[])
    like = f"%{q}%"
    with db() as c:
        rows = c.execute(
            "select id, username, name, avatar, coalesce(verified,0) verified from users "
            "where id != ? "
            "  and lower(username) not in (select uname from bans) "
            "  and (lower(username) like ? or lower(coalesce(name,'')) like ?) "
            "order by username limit 30",
            (r["id"], like, like)
        ).fetchall()
    return jsonify(users=[{
        "id": x["id"], "username": x["username"],
        "name": x["name"] or x["username"],
        "av": bool(x["avatar"]),
        "verified": bool(x["verified"])
    } for x in rows])

# ── IMAGE MESSAGE ──
MAX_IMG = 2_000_000
@app.post("/api/image")
def api_image():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    room = (d.get("room") or "").strip()
    if not can_access(r["id"], room):
        return jsonify(error="not a member"), 403
    img = d.get("image") or ""
    if not isinstance(img, str) or len(img) > MAX_IMG:
        return jsonify(error="Image too large (max 2MB)"), 413
    m = re.match(r"data:image/(png|jpeg|webp|gif);base64,", img)
    if not m: return jsonify(error="Invalid image"), 400
    try:
        raw = base64.b64decode(img.split(",", 1)[1], validate=True)
    except Exception:
        return jsonify(error="Invalid image"), 400
    if len(raw) > MAX_IMG:
        return jsonify(error="Image too large (max 2MB)"), 413
    mime = "image/" + m.group(1)
    cid = str(r["id"]); name = (r["name"] or r["username"])[:20]
    with lock:
        h = get_hist(room)
        ts = int(time.time()*1000)
        mid = secrets.token_hex(6)
        with db() as c:
            iid = c.execute("insert into images(mime,data) values(?,?)",
                            (mime, raw)).lastrowid
            seq = c.execute(
                "insert into msgs(room,mid,cid,name,text,ts,im) "
                "values(?,?,?,?,?,?,?)",
                (room, mid, cid, name, "", ts, iid)).lastrowid
        msg = {"mid": mid, "cid": cid, "name": name, "text": "",
               "ts": ts, "seq": seq, "im": iid}
        h.append(msg)
    socketio.emit("msg", msg, to=room)
    return jsonify(ok=True, seq=seq)

@app.get("/img/<int:iid>")
def img_file(iid):
    with db() as c:
        a = c.execute("select mime, data from images where id=?",(iid,)).fetchone()
    if not a: return "", 404
    return send_file(io.BytesIO(a["data"]), mimetype=a["mime"],
                     conditional=True, max_age=31536000)

# ── VOICE ──
MAX_AUDIO = 4000000
@app.post("/api/voice")
def api_voice():
    r = user_by_token(request.headers.get("X-Token"))
    if not r: return jsonify(error="auth"), 401
    mime = (request.mimetype or "").lower()
    if not mime.startswith("audio/"): return jsonify(error="Invalid audio"), 400
    if (request.content_length or 0) > MAX_AUDIO:
        return jsonify(error="Voice message too long"), 413
    data = request.get_data()
    if not data or len(data) > MAX_AUDIO:
        return jsonify(error="Voice message too long"), 413
    room = (request.headers.get("X-Room") or "").strip()
    if not can_access(r["id"], room):
        return jsonify(error="not a member"), 403
    mid = (request.headers.get("X-Mid") or "")[:64] or secrets.token_hex(6)
    try: dur = max(0, min(int(float(request.headers.get("X-Dur") or 0)), 600))
    except ValueError: dur = 0
    wv = request.headers.get("X-Wave") or ""
    if re.fullmatch(r"[0-9]{1,3}(,[0-9]{1,3}){0,79}", wv):
        wv = ",".join(str(min(100,int(x))) for x in wv.split(","))
    else: wv = ""
    cid = str(r["id"]); name = (r["name"] or r["username"])[:20]
    with lock:
        h = get_hist(room)
        dup = next((m for m in h if m["mid"]==mid), None)
        if dup: return jsonify(ok=True, seq=dup["seq"])
        ts = int(time.time()*1000)
        with db() as c:
            aid = c.execute("insert into audio(mime,data) values(?,?)",
                            (mime,data)).lastrowid
            seq = c.execute(
                "insert into msgs(room,mid,cid,name,text,ts,au,dur,wv) "
                "values(?,?,?,?,?,?,?,?,?)",
                (room,mid,cid,name,"",ts,aid,dur,wv)).lastrowid
        m = {"mid":mid,"cid":cid,"name":name,"text":"","ts":ts,"seq":seq,
             "au":aid,"dur":dur}
        if wv: m["wv"] = wv
        h.append(m)
    socketio.emit("msg", m, to=room)
    return jsonify(ok=True, seq=seq)

@app.get("/audio/<int:aid>")
def audio_file(aid):
    r = user_by_token(request.args.get("t"))
    if not r: return "", 403
    with db() as c:
        a = c.execute("select mime, data from audio where id=?",(aid,)).fetchone()
    if not a: return "", 404
    return send_file(io.BytesIO(a["data"]), mimetype=a["mime"],
                     conditional=True, max_age=31536000)

@app.get("/gpic")
def gpic():
    if not GROUP_PIC: return "", 404
    return Response(GROUP_PIC, mimetype=GROUP_PIC_MIME,
                    headers={"Cache-Control":"public, max-age=86400"})

@app.get("/gbg")
def gbg():
    if not GROUP_BG: return "", 404
    return Response(GROUP_BG, mimetype=GROUP_BG_MIME,
                    headers={"Cache-Control":"public, max-age=86400"})

@app.get("/gpic/<int:gid>")
def gpic_of(gid):
    with db() as c:
        r = c.execute("select pic from groups where id=?",(gid,)).fetchone()
    if not r or not r["pic"]: return "", 404
    head, b64 = r["pic"].split(",",1)
    mime = head[5:].split(";")[0]
    if mime not in ("image/png","image/jpeg","image/webp","image/gif"): return "", 404
    try: raw = base64.b64decode(b64)
    except Exception: return "", 404
    return Response(raw, mimetype=mime, headers={"Cache-Control":"public, max-age=120"})

# ── friends
@app.get("/api/friends")
def api_friends():
    r = user_by_token(request.args.get("t"))
    if not r: return jsonify(error="auth"), 401
    uid = r["id"]
    with db() as c:
        rows = c.execute(
            "select f.status, "
            "case when f.a=? then f.b else f.a end as oid, f.a, f.b "
            "from friends f where f.a=? or f.b=?",(uid,uid,uid)).fetchall()
        out = {"friends":[], "incoming":[], "outgoing":[]}
        for x in rows:
            o = c.execute("select id, username, name, avatar, verified from users where id=?",
                          (x["oid"],)).fetchone()
            if not o: continue
            item = {"id":o["id"],"username":o["username"],
                    "name":o["name"] or o["username"],
                    "av": bool(o["avatar"]),
                    "verified": bool(o["verified"]) if "verified" in o.keys() else False}
            if x["status"] == "ok":
                out["friends"].append(item)
            elif x["status"] == "pend":
                (out["outgoing"] if x["a"] == uid else out["incoming"]).append(item)
    return jsonify(out)

@app.post("/api/friend/request")
def api_friend_request():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    uname = re.sub(r"\s+"," ",(d.get("username") or "").strip())
    if not uname: return jsonify(error="Username required"), 400
    with db() as c:
        o = c.execute("select * from users where lower(username)=lower(?)",
                      (uname,)).fetchone()
        if not o: return jsonify(error="No such user"), 404
        if o["id"] == r["id"]: return jsonify(error="That's you"), 400
        a, b = sorted((r["id"], o["id"]))
        ex = c.execute("select status from friends where a=? and b=?",(a,b)).fetchone()
        if ex:
            if ex["status"] == "ok": return jsonify(error="Already friends"), 400
            c.execute("update friends set status='ok', ts=? where a=? and b=?",
                      (int(time.time()*1000),a,b))
            st = "ok"
        else:
            c.execute("insert into friends(a,b,status,ts) values(?,?,?,?)",
                      (a,b,"pend",int(time.time()*1000)))
            st = "pend"
    socketio.emit("friend_update", {"for":o["id"]}, to=("u:%d" % o["id"]))
    socketio.emit("friend_update", {"for":r["id"]}, to=("u:%d" % r["id"]))
    return jsonify(ok=True, status=st)

@app.post("/api/friend/accept")
def api_friend_accept():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    oid = _int(d.get("uid"))
    a, b = sorted((r["id"], oid))
    with db() as c:
        row = c.execute("select status from friends where a=? and b=?",(a,b)).fetchone()
        if not row or row["status"] != "pend":
            return jsonify(error="No pending request"), 400
        c.execute("update friends set status='ok', ts=? where a=? and b=?",
                  (int(time.time()*1000),a,b))
    socketio.emit("friend_update", {"for":oid}, to=("u:%d" % oid))
    socketio.emit("friend_update", {"for":r["id"]}, to=("u:%d" % r["id"]))
    return jsonify(ok=True)

@app.post("/api/friend/remove")
def api_friend_remove():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    oid = _int(d.get("uid"))
    a, b = sorted((r["id"], oid))
    with db() as c:
        c.execute("delete from friends where a=? and b=?",(a,b))
    socketio.emit("friend_update", {"for":oid}, to=("u:%d" % oid))
    socketio.emit("friend_update", {"for":r["id"]}, to=("u:%d" % r["id"]))
    return jsonify(ok=True)

# ── groups
@app.get("/api/groups")
def api_groups():
    r = user_by_token(request.args.get("t"))
    if not r: return jsonify(error="auth"), 401
    uid = r["id"]
    with db() as c:
        mine = c.execute(
            "select g.id,g.name,g.private,g.owner,g.default_g, "
            "(select count(*) from members m where m.gid=g.id) n "
            "from groups g join members me on me.gid=g.id "
            "where me.uid=? order by g.default_g desc, g.ts desc",(uid,)).fetchall()
        discover = c.execute(
            "select g.id,g.name,g.private,g.owner,g.default_g, "
            "(select count(*) from members m where m.gid=g.id) n "
            "from groups g where g.private=0 and g.default_g=0 "
            "and g.id not in (select gid from members where uid=?) "
            "order by g.ts desc limit 100",(uid,)).fetchall()
    def pack(rows):
        return [{"id":x["id"],"name":x["name"],"private":bool(x["private"]),
                 "owner":x["owner"],"default":bool(x["default_g"]),"n":x["n"]}
                for x in rows]
    return jsonify(mine=pack(mine), discover=pack(discover))

@app.post("/api/group/create")
def api_group_create():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    name = (d.get("name") or "").strip()[:40]
    if not name: return jsonify(error="Name required"), 400
    private = 1 if d.get("private") else 0
    if private and not is_admin():
        return jsonify(error="Only admin can create private groups"), 403
    pic = d.get("pic")
    if pic and (not isinstance(pic,str) or len(pic) > 200000 or
                not re.match(r"data:image/(png|jpeg|webp|gif);base64,", pic)):
        pic = None
    ts = int(time.time()*1000)
    with db() as c:
        gid = c.execute(
            "insert into groups(name,pic,owner,private,ts,default_g) "
            "values(?,?,?,?,?,0)",
            (name, pic, r["id"], private, ts)).lastrowid
        c.execute("insert into members(gid,uid,ts) values(?,?,?)",(gid,r["id"],ts))
    return jsonify(ok=True, gid=gid)

@app.post("/api/group/join")
def api_group_join():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    gid = _int(d.get("gid"))
    with db() as c:
        g = c.execute("select * from groups where id=?",(gid,)).fetchone()
        if not g: return jsonify(error="No such group"), 404
        if g["private"]:
            return jsonify(error="This group is private"), 403
        c.execute("insert or ignore into members(gid,uid,ts) values(?,?,?)",
                  (gid, r["id"], int(time.time()*1000)))
    socketio.emit("group_update", {"for":r["id"]}, to=("u:%d" % r["id"]))
    return jsonify(ok=True)

@app.post("/api/group/leave")
def api_group_leave():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    gid = _int(d.get("gid"))
    with db() as c:
        g = c.execute("select default_g,owner from groups where id=?",(gid,)).fetchone()
        if not g: return jsonify(error="No such group"), 404
        if g["default_g"]: return jsonify(error="Can't leave main group"), 400
        c.execute("delete from members where gid=? and uid=?",(gid,r["id"]))
    socketio.emit("group_update", {"for":r["id"]}, to=("u:%d" % r["id"]))
    return jsonify(ok=True)

@app.post("/api/group/delete")
def api_group_delete():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    gid = _int(d.get("gid"))
    with db() as c:
        g = c.execute("select default_g,owner from groups where id=?",(gid,)).fetchone()
        if not g: return jsonify(error="No such group"), 404
        if g["default_g"]: return jsonify(error="Can't delete main group"), 400
        if g["owner"] != r["id"] and not is_admin():
            return jsonify(error="Not allowed"), 403
        mids = [x["mid"] for x in c.execute(
            "select mid from msgs where room=?",(room_of(gid),)).fetchall()]
        c.execute("delete from groups where id=?",(gid,))
        c.execute("delete from members where gid=?",(gid,))
        c.execute("delete from msgs where room=?",(room_of(gid),))
        for mid in mids:
            c.execute("delete from reactions where mid=?",(mid,))
            c.execute("insert into dels(mid) values(?)",(mid,))
    with lock:
        history.pop(room_of(gid), None)
    socketio.emit("group_deleted", {"gid":gid}, to=room_of(gid))
    return jsonify(ok=True)

@app.post("/api/group/add_member")
def api_group_add_member():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    gid = _int(d.get("gid"))
    uname = re.sub(r"\s+"," ",(d.get("username") or "").strip())
    with db() as c:
        g = c.execute("select * from groups where id=?",(gid,)).fetchone()
        if not g: return jsonify(error="No such group"), 404
        if g["owner"] != r["id"] and not is_admin():
            return jsonify(error="Not allowed"), 403
        o = c.execute("select id from users where lower(username)=lower(?)",
                      (uname,)).fetchone()
        if not o: return jsonify(error="No such user"), 404
        c.execute("insert or ignore into members(gid,uid,ts) values(?,?,?)",
                  (gid, o["id"], int(time.time()*1000)))
    socketio.emit("group_update", {"for":o["id"]}, to=("u:%d" % o["id"]))
    return jsonify(ok=True)

@app.post("/api/group/remove_member")
def api_group_remove_member():
    d = request.get_json(silent=True) or {}
    r = user_by_token(d.get("token"))
    if not r: return jsonify(error="auth"), 401
    gid = _int(d.get("gid")); uid = _int(d.get("uid"))
    with db() as c:
        g = c.execute("select * from groups where id=?",(gid,)).fetchone()
        if not g: return jsonify(error="No such group"), 404
        if g["owner"] != r["id"] and not is_admin():
            return jsonify(error="Not allowed"), 403
        if g["default_g"]: return jsonify(error="Can't modify main group"), 400
        c.execute("delete from members where gid=? and uid=?",(gid,uid))
    socketio.emit("group_update", {"for":uid}, to=("u:%d" % uid))
    return jsonify(ok=True)

@app.get("/api/group/members/<int:gid>")
def api_group_members(gid):
    r = user_by_token(request.args.get("t"))
    if not r: return jsonify(error="auth"), 401
    if not can_access(r["id"], room_of(gid)):
        return jsonify(error="Not allowed"), 403
    with db() as c:
        rows = c.execute(
            "select u.id,u.username,u.name,u.avatar, coalesce(u.verified,0) verified from members m "
            "join users u on u.id=m.uid where m.gid=? order by u.name",
            (gid,)).fetchall()
    return jsonify([{"id":x["id"],"username":x["username"],
                     "name":x["name"] or x["username"],
                     "av":bool(x["avatar"]),
                     "verified":bool(x["verified"])} for x in rows])

# ═══════════════════════════ SOCKET.IO ════════════════════════════════
@socketio.on("join")
def on_join(data):
    data = data or {}
    r = user_by_token(data.get("token"))
    if not r:
        emit("auth_error"); return
    name = (r["name"] or r["username"])[:20]
    uid = r["id"]
    room = (data.get("room") or ROOM_DEFAULT).strip()
    if not can_access(uid, room):
        room = ROOM_DEFAULT
    old = users.get(request.sid)
    if old and old["room"] != room:
        try: leave_room(old["room"])
        except Exception: pass
    rejoin = request.sid in users
    users[request.sid] = {"name":name,"room":room,"uid":uid}
    join_room(room)
    join_room("u:%d" % uid)
    last = _int(data.get("last"))
    msgs = [m for m in get_hist(room) if m["seq"] > last]
    dl, dv = del_sync(_int(data.get("dv")), last == 0)
    touch(uid)
    emit("joined", {"id":request.sid,"room":room,"msgs":msgs,
                    "call":cstate(room),"rx":rx_map(room),
                    "dels":dl,"dv":dv})
    if not rejoin:
        emit("users", room_users(room), to=room)
        emit("system", {"text": f"{name} joined"}, to=room)

@socketio.on("switch_room")
def on_switch(data):
    u = users.get(request.sid)
    if not u: return {"err":"no"}
    data = data or {}
    room = (data.get("room") or "").strip()
    uid = u["uid"]
    if not can_access(uid, room): return {"err":"no"}
    old = u["room"]
    if old == room:
        return {"ok":True, "msgs": [], "call": cstate(room)}
    try: leave_room(old)
    except Exception: pass
    u["room"] = room
    join_room(room)
    emit("users", room_users(old), to=old)
    emit("users", room_users(room), to=room)
    return {"ok":True,
            "msgs":[m for m in get_hist(room) if m["seq"] > _int(data.get("last"))],
            "call":cstate(room)}

@socketio.on("sync")
def on_sync(data):
    u = users.get(request.sid)
    if not u: return {"msgs":[],"call":None,"rejoin":True}
    touch(u["uid"])
    last = _int((data or {}).get("last"))
    dl, dv = del_sync(_int((data or {}).get("dv")), last == 0)
    return {"msgs":[m for m in get_hist(u["room"]) if m["seq"] > last],
            "call":cstate(u["room"]),"rx":rx_map(u["room"]),
            "dels":dl,"dv":dv}

@socketio.on("msg")
def on_msg(data):
    data = data or {}
    u = users.get(request.sid)
    text = (data.get("text") or "").strip()[:1000]
    mid = str(data.get("mid") or "")[:64]
    if not u or not text: return {"ok":False}
    room = u["room"]
    mid = mid or secrets.token_hex(6)
    with lock:
        h = get_hist(room)
        dup = next((m for m in h if m["mid"]==mid), None)
        if dup: return {"ok":True, "seq":dup["seq"]}
        ts = int(time.time()*1000)
        with db() as c:
            seq = c.execute(
                "insert into msgs(room,mid,cid,name,text,ts) values(?,?,?,?,?,?)",
                (room,mid,str(u["uid"]),u["name"],text,ts)).lastrowid
        m = {"mid":mid,"cid":str(u["uid"]),"name":u["name"],
             "text":text,"ts":ts,"seq":seq}
        if user_is_verified(u["uid"]):
            m["verified"] = True
        h.append(m)
    # BROADCAST to the entire room (including sender — dedup by mid on client)
    emit("msg", m, to=room)
    print(f"[msg] room={room} mid={mid} from={u['name']} users_in_room={len([x for x in users.values() if x['room']==room])}")
    url = URL_RE.search(text)
    if url:
        socketio.start_background_task(make_preview, room, m, url.group(0))
    return {"ok":True, "seq":m["seq"]}

@socketio.on("del")
def on_del(data):
    u = users.get(request.sid)
    mid = str((data or {}).get("mid") or "")[:64]
    if not u or not mid: return {"ok":False}
    room = u["room"]
    with lock:
        with db() as c:
            r = c.execute("select seq, cid, au from msgs where room=? and mid=?",
                          (room,mid)).fetchone()
            if not r or r["cid"] != str(u["uid"]): return {"ok":False}
            c.execute("delete from msgs where seq=?",(r["seq"],))
            if r["au"]: c.execute("delete from audio where id=?",(r["au"],))
            c.execute("delete from reactions where mid=?",(mid,))
            c.execute("insert into dels(mid) values(?)",(mid,))
        h = get_hist(room)
        h[:] = [m for m in h if m["mid"] != mid]
    emit("del", {"mid":mid}, to=room)
    return {"ok":True}

@socketio.on("react")
def on_react(data):
    u = users.get(request.sid); d = data or {}
    mid = str(d.get("mid") or "")[:64]
    em  = str(d.get("emoji") or "").strip()
    if not u or not mid or not em or len(em) > 16 or \
       re.search(r"[A-Za-z0-9\s<>&\"']", em):
        return {"ok":False}
    room, uid = u["room"], u["uid"]
    with lock:
        with db() as c:
            if not c.execute("select 1 from msgs where room=? and mid=?",
                             (room,mid)).fetchone():
                return {"ok":False}
            cur = c.execute("select emoji from reactions where mid=? and uid=?",
                            (mid,uid)).fetchone()
            if cur and cur["emoji"] == em:
                c.execute("delete from reactions where mid=? and uid=?",(mid,uid))
            else:
                c.execute("insert or replace into reactions values(?,?,?,?)",
                          (mid,uid,em,int(time.time()*1000)))
            rows = c.execute(
                "select r.uid, r.emoji, coalesce(nullif(u.name,''),u.username) n "
                "from reactions r join users u on u.id=r.uid "
                "where r.mid=? order by r.ts",(mid,)).fetchall()
        rx = [[str(x["uid"]),x["emoji"],x["n"]] for x in rows]
        m = next((x for x in get_hist(room) if x["mid"]==mid), None)
        if m is not None:
            if rx: m["rx"] = rx
            else: m.pop("rx",None)
    emit("rx", {"mid":mid,"rx":rx}, to=room)
    return {"ok":True}

@socketio.on("typing")
def on_typing(data):
    u = users.get(request.sid)
    if not u: return
    d = data or {}
    emit("typing", {
        "uid": u["uid"],
        "name": u["name"],
        "room": u["room"],
        "on": bool(d.get("on"))
    }, to=u["room"], skip_sid=request.sid)

@socketio.on("call_start")
def on_call_start(data):
    data = data or {}
    u = users.get(request.sid)
    if not u: return {"err":"nouser"}
    room = u["room"]
    with lock:
        if room in calls: return {"err":"busy"}
        c = {"video":bool(data.get("video")),"starter":request.sid,
             "starter_name":u["name"],"parts":{request.sid},
             "declined":set(),"connected":False,
             "starter_cid":str(u["uid"]),"t0":0}
        calls[room] = c
    push_state(room)
    emit("call_incoming", {"from":u["name"],"video":c["video"]},
         to=room, skip_sid=request.sid)
    socketio.start_background_task(ring_timeout, room, c)
    return {"ok":True}

@socketio.on("call_accept")
def on_call_accept():
    u = users.get(request.sid)
    if not u: return
    room = u["room"]
    with lock:
        c = calls.get(room)
        if not c: return
        others = [s for s in c["parts"] if s != request.sid]
        c["parts"].add(request.sid)
        if not c["connected"]: c["t0"] = time.time()
        c["connected"] = True
    emit("call_peers", others)
    push_state(room)

@socketio.on("call_decline")
def on_call_decline():
    u = users.get(request.sid)
    if not u: return
    room = u["room"]
    with lock:
        c = calls.get(room)
        if not c: return
        c["declined"].add(request.sid)
        invitees = {s for s,x in users.items() if x["room"]==room} - c["parts"]
        if not c["connected"] and invitees <= c["declined"]:
            end_call(room,"declined")

@socketio.on("call_leave")
def on_call_leave():
    leave_call(request.sid)

@socketio.on("signal")
def on_signal(data):
    data = data or {}
    u = users.get(request.sid); t = users.get(data.get("to"))
    if u and t and u["room"] == t["room"]:
        emit("signal", {"from":request.sid,"data":data.get("data")},
             to=data["to"])

@socketio.on("disconnect")
def on_disconnect():
    leave_call(request.sid)
    u = users.pop(request.sid, None)
    if not u: return
    touch(u["uid"])
    emit("users", room_users(u["room"]), to=u["room"])
    if not any(v["uid"]==u["uid"] and v["room"]==u["room"]
               for v in users.values()):
        emit("system", {"text": f"{u['name']} left"}, to=u["room"])

# ═══════════════════════════ PAGE ROUTES ══════════════════════════════
def _read_page(name):
    p = os.path.join(_HERE, name)
    try:
        with open(p,"r",encoding="utf-8") as f:
            return f.read()
    except OSError:
        return "<h1>%s not found</h1>" % name


@app.get("/favicon.ico")
def favicon_ico():
    data = FAVICON_ICO or FAVICON_PNG
    if not data:
        return "", 404
    mime = "image/x-icon" if FAVICON_ICO else "image/png"
    return Response(data, mimetype=mime,
                    headers={"Cache-Control": "public, max-age=86400"})

@app.get("/favicon.png")
def favicon_png():
    if not FAVICON_PNG:
        return "", 404
    return Response(FAVICON_PNG, mimetype="image/png",
                    headers={"Cache-Control": "public, max-age=86400"})

@app.get("/apple-touch-icon.png")
def apple_touch_icon():
    data = APPLE_TOUCH or FAVICON_PNG or GROUP_PIC
    if not data:
        return "", 404
    return Response(data, mimetype="image/png",
                    headers={"Cache-Control": "public, max-age=86400"})

@app.route("/")
def index():
    return Response(_read_page("index.html"), mimetype="text/html",
                    headers={"Cache-Control":"no-store"})

@app.route("/admin")
@app.route("/admin/")
def admin_page():
    return Response(_read_page("admin.html"), mimetype="text/html",
                    headers={"Cache-Control":"no-store",
                             "X-Robots-Tag":"noindex, nofollow"})

# ═══════════════════════════ ADMIN API ════════════════════════════════
_adm_fail = {}

@app.post("/admin/api/login")
def admin_login():
    ip = _client_ip(); now = time.time()
    f = _adm_fail.get(ip)
    if f and now - f[1] > 600:
        _adm_fail.pop(ip, None); f = None
    if f and f[0] >= 5:
        return _adm_json({"error":"Too many attempts. Try again later."}, 429)
    p = str((request.get_json(silent=True) or {}).get("password") or "")
    if not secrets.compare_digest(p.encode(), ADMIN_PASS.encode()):
        _adm_fail[ip] = [(f[0] if f else 0)+1, f[1] if f else now]
        time.sleep(1)
        return _adm_json({"error":"Wrong admin password"}, 401)
    _adm_fail.pop(ip, None)
    r = _adm_json({"ok":True})
    secure = request.is_secure or request.headers.get("X-Forwarded-Proto","") == "https"
    r.set_cookie("exu_adm", _adm_token(int(now)+8*3600), max_age=8*3600,
                 path="/", httponly=True, samesite="Strict", secure=secure)
    return r

@app.post("/admin/api/logout")
def admin_logout():
    r = _adm_json({"ok":True})
    r.delete_cookie("exu_adm", path="/")
    return r

@app.get("/admin/api/data")
def admin_data():
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    with db() as c:
        n_msgs  = c.execute("select count(*) from msgs").fetchone()[0]
        n_voice = c.execute("select count(*) from msgs where au is not null and au>0").fetchone()[0]
        us = c.execute(
            "select u.id,u.username,u.name,u.ts,u.seen, coalesce(u.verified,0) verified, "
            "(select count(*) from msgs m where m.cid=cast(u.id as text)) n, "
            "exists(select 1 from bans b where b.uname=lower(u.username)) banned "
            "from users u order by coalesce(u.seen,0) desc, u.id desc limit 1000").fetchall()
        bn = c.execute("select b.uname,b.name,b.ts,u.id uid,u.username "
                       "from bans b left join users u on lower(u.username)=b.uname "
                       "order by b.ts desc").fetchall()
        ms = c.execute("select mid,cid,name,text,ts,au,room from msgs "
                       "order by seq desc limit 200").fetchall()
        grs = c.execute(
            "select g.id,g.name,g.private,g.owner,g.default_g, "
            "(select count(*) from members m where m.gid=g.id) n, "
            "(select count(*) from msgs x where x.room='g:'||g.id) mc "
            "from groups g order by g.default_g desc, g.ts desc").fetchall()
    try: size = os.path.getsize(DB)
    except OSError: size = 0
    with lock:
        on = {u["uid"] for u in users.values()}
    return _adm_json({
        "group": GROUP_NAME, "site": SITE_NAME,
        "now": int(time.time()*1000), "online": len(on),
        "users_total": len(us), "msgs_total": n_msgs, "voice_total": n_voice,
        "db_mb": round(size/1048576, 2), "banned_total": len(bn),
        "users": [{"id":u["id"],"username":u["username"],
                   "name":u["name"] or u["username"],"ts":u["ts"],
                   "seen":u["seen"],"msgs":u["n"],"banned":bool(u["banned"]),
                   "online":u["id"] in on,
                   "verified": bool(u["verified"])} for u in us],
        "bans": [{"uname":b["username"] or b["uname"],"name":b["name"],
                  "ts":b["ts"],"uid":b["uid"]} for b in bn],
        "msgs": [{"mid":m["mid"],"cid":m["cid"],"name":m["name"],
                  "text":m["text"],"ts":m["ts"],"voice":bool(m["au"]),
                  "room":m["room"]} for m in ms],
        "groups": [{"id":g["id"],"name":g["name"],"private":bool(g["private"]),
                    "owner":g["owner"],"default":bool(g["default_g"]),
                    "n":g["n"],"msgs":g["mc"]} for g in grs],
    })

def _adm_delete_mids(mids):
    mids = [m for m in mids if m]
    if not mids: return 0
    with lock:
        with db() as c:
            for mid in mids:
                r = c.execute("select au from msgs where mid=?",(mid,)).fetchone()
                if not r: continue
                c.execute("delete from msgs where mid=?",(mid,))
                if r["au"]: c.execute("delete from audio where id=?",(r["au"],))
                c.execute("delete from reactions where mid=?",(mid,))
                c.execute("insert into dels(mid) values(?)",(mid,))
        gone = set(mids)
        for room in list(history.keys()):
            history[room][:] = [m for m in history[room] if m["mid"] not in gone]
    for mid in mids:
        socketio.emit("del", {"mid":mid}, broadcast=True)
    return len(mids)

@app.post("/admin/api/ban")
def admin_ban():
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    d = request.get_json(silent=True) or {}
    uname = re.sub(r"\s+"," ",(d.get("username") or "").strip())
    if not re.fullmatch(r"[A-Za-z0-9_.]{3,20}", uname):
        return _adm_json({"error":"Invalid username"}, 400)
    key = uname.lower()
    with db() as c:
        u = c.execute("select id,username,name from users where lower(username)=?",
                      (key,)).fetchone()
        c.execute("insert or replace into bans(uname,uid,name,ts) values(?,?,?,?)",
                  (key, u["id"] if u else None,
                   (u["name"] or u["username"]) if u else uname,
                   int(time.time()*1000)))
        if u: c.execute("delete from sess where uid=?",(u["id"],))
    deleted = 0
    if u:
        with lock:
            sids = [sid for sid,x in users.items() if x["uid"] == u["id"]]
            for sid in sids:
                leave_call(sid); users.pop(sid, None)
        for sid in sids:
            socketio.emit("banned", {}, to=sid)
        if d.get("delete_msgs"):
            with db() as c:
                mids = [r["mid"] for r in c.execute(
                    "select mid from msgs where cid=?",(str(u["id"]),)).fetchall()]
            deleted = _adm_delete_mids(mids)
    return _adm_json({"ok":True, "deleted":deleted, "existing":bool(u)})

@app.post("/admin/api/unban")
def admin_unban():
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    key = re.sub(r"\s+"," ",str((request.get_json(silent=True) or {})
                 .get("username") or "").strip()).lower()
    with db() as c:
        c.execute("delete from bans where uname=?",(key,))
    return _adm_json({"ok":True})

@app.post("/admin/api/verify")
def admin_verify():
    """Toggle verified badge for a user. Body: {username, verified: true|false}"""
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    d = request.get_json(silent=True) or {}
    uname = re.sub(r"\s+"," ",(d.get("username") or "").strip())
    if not re.fullmatch(r"[A-Za-z0-9_.]{3,20}", uname):
        return _adm_json({"error":"Invalid username"}, 400)
    flag = 1 if d.get("verified") in (True, 1, "1", "true", "True") else 0
    with db() as c:
        u = c.execute("select id, username, name from users where lower(username)=lower(?)",
                      (uname,)).fetchone()
        if not u:
            return _adm_json({"error":"User not found"}, 404)
        c.execute("update users set verified=? where id=?", (flag, u["id"]))
        uid = u["id"]
    # Notify online sessions of this user so UI can refresh
    try:
        socketio.emit("verified", {"uid": uid, "verified": bool(flag)},
                      to="u:%d" % uid)
        socketio.emit("verified", {"uid": uid, "verified": bool(flag)},
                      broadcast=True)
    except Exception:
        pass
    return _adm_json({"ok":True, "username": uname, "verified": bool(flag), "uid": uid})

@app.post("/admin/api/delete_msg")
def admin_delete_msg():
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    mid = str((request.get_json(silent=True) or {}).get("mid") or "")[:64]
    return _adm_json({"ok":True, "deleted":_adm_delete_mids([mid])})

@app.post("/admin/api/clear_msgs")
def admin_clear_msgs():
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    if (request.get_json(silent=True) or {}).get("confirm") != "DELETE":
        return _adm_json({"error":"Not confirmed"}, 400)
    with db() as c:
        mids = [r["mid"] for r in c.execute("select mid from msgs").fetchall()]
    return _adm_json({"ok":True, "deleted":_adm_delete_mids(mids)})

@app.post("/admin/api/group/create")
def admin_group_create():
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    d = request.get_json(silent=True) or {}
    name = (d.get("name") or "").strip()[:40]
    if not name: return _adm_json({"error":"Name required"}, 400)
    ts = int(time.time()*1000)
    with db() as c:
        gid = c.execute(
            "insert into groups(name,pic,owner,private,ts,default_g) "
            "values(?,?,?,?,?,0)",
            (name, None, 0, 1 if d.get("private") else 0, ts)).lastrowid
    return _adm_json({"ok":True, "gid":gid})

@app.post("/admin/api/group/delete")
def admin_group_delete():
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    gid = _int((request.get_json(silent=True) or {}).get("gid"))
    with db() as c:
        g = c.execute("select default_g from groups where id=?",(gid,)).fetchone()
        if not g: return _adm_json({"error":"No such group"}, 404)
        if g["default_g"]: return _adm_json({"error":"Can't delete main group"}, 400)
        mids = [x["mid"] for x in c.execute(
            "select mid from msgs where room=?",(room_of(gid),)).fetchall()]
        c.execute("delete from groups where id=?",(gid,))
        c.execute("delete from members where gid=?",(gid,))
        c.execute("delete from msgs where room=?",(room_of(gid),))
        for mid in mids:
            c.execute("delete from reactions where mid=?",(mid,))
            c.execute("insert into dels(mid) values(?)",(mid,))
    with lock: history.pop(room_of(gid), None)
    socketio.emit("group_deleted", {"gid":gid}, to=room_of(gid))
    return _adm_json({"ok":True})

@app.post("/admin/api/group/rename")
def admin_group_rename():
    if not is_admin(): return _adm_json({"error":"auth"}, 401)
    d = request.get_json(silent=True) or {}
    gid = _int(d.get("gid")); name = (d.get("name") or "").strip()[:40]
    if not name: return _adm_json({"error":"Name required"}, 400)
    with db() as c:
        c.execute("update groups set name=? where id=?",(name,gid))
    socketio.emit("group_renamed", {"gid":gid,"name":name}, to=room_of(gid))
    return _adm_json({"ok":True})

# ═══════════════════════════ ENTRY ════════════════════════════════════
if __name__ == "__main__":
    print("EXU CHAT  →  http://0.0.0.0:8080")
    print("Admin     →  http://0.0.0.0:8080/admin")
    socketio.run(app, host="0.0.0.0", port=8080, allow_unsafe_werkzeug=True)

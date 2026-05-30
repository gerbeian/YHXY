import os
import sqlite3
import hashlib
import threading
import time
import re
import json
import base64
import secrets
import urllib.parse
import random
from datetime import datetime, timedelta
from flask import Flask, render_template, request, redirect, url_for, session, jsonify, g, make_response
from werkzeug.utils import secure_filename
from functools import wraps
import psutil
import platform
import requests
from Crypto.PublicKey import RSA
from Crypto.Cipher import PKCS1_v1_5
from collections import defaultdict

app = Flask(__name__)
app.secret_key = 'your-super-secret-key-change-in-production'
app.config['UPLOAD_FOLDER'] = 'static/uploads'
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=30)
app.config['MAX_CONTENT_LENGTH'] = 100 * 1024 * 1024
os.makedirs(app.config['UPLOAD_FOLDER'], exist_ok=True)

DATABASE = 'chat.db'

# ======================= 安全增强模块 =======================
request_log = defaultdict(list)
fail_log = defaultdict(list)
blocked_ips = set()
blocked_until = {}
MAX_CONCURRENT = 100
semaphore = threading.BoundedSemaphore(MAX_CONCURRENT)
RATE_LIMIT = 60
FAIL_LIMIT = 10
BLOCK_DURATION = 300
WHITELIST_IPS = {'127.0.0.1', '::1'}

CDN_VIA_KEYWORDS = ['cloudflare', 'aliyun', 'akamai', 'fastly', 'cachefly', 'cdn', 'edgecast', 'incapsula']

def is_whitelisted(ip):
    return ip in WHITELIST_IPS

def is_using_proxy():
    suspicious_headers = ['HTTP_VIA', 'HTTP_PROXY_CONNECTION', 'HTTP_X_PROXY_ID', 'HTTP_X_PROXY']
    for header in suspicious_headers:
        val = request.headers.get(header)
        if val:
            if header == 'HTTP_VIA' and any(kw in val.lower() for kw in CDN_VIA_KEYWORDS):
                continue
            return True
    return False

def is_blocked(ip):
    if ip in blocked_until:
        if time.time() < blocked_until[ip]:
            return True
        else:
            del blocked_until[ip]
            blocked_ips.discard(ip)
    return False

def check_rate_limit(ip):
    if is_whitelisted(ip):
        return True
    now = time.time()
    window_start = now - 60
    request_log[ip] = [t for t in request_log[ip] if t > window_start]
    if len(request_log[ip]) >= RATE_LIMIT:
        return False
    request_log[ip].append(now)
    return True

def record_failure(ip):
    if is_whitelisted(ip):
        return
    now = time.time()
    window_start = now - 60
    fail_log[ip] = [t for t in fail_log[ip] if t > window_start]
    fail_log[ip].append(now)
    if len(fail_log[ip]) >= FAIL_LIMIT:
        blocked_until[ip] = now + BLOCK_DURATION
        blocked_ips.add(ip)

def get_online_users_count():
    db = get_db()
    cutoff = datetime.now() - timedelta(minutes=5)
    count = db.execute('SELECT COUNT(*) FROM users WHERE last_activity IS NOT NULL AND last_activity >= ?', (cutoff,)).fetchone()[0]
    return count

# ======================= 数据库操作 =======================
def get_db():
    db = getattr(g, '_database', None)
    if db is None:
        db = g._database = sqlite3.connect(DATABASE)
        db.row_factory = sqlite3.Row
    return db

@app.teardown_appcontext
def close_connection(exception):
    db = getattr(g, '_database', None)
    if db is not None:
        db.close()

def init_db():
    with app.app_context():
        db = get_db()
        db.executescript('''
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                uid TEXT UNIQUE NOT NULL,
                username TEXT UNIQUE NOT NULL,
                password TEXT NOT NULL,
                mobile TEXT UNIQUE NOT NULL,
                qq TEXT UNIQUE NOT NULL,
                avatar TEXT DEFAULT '/static/default_avatar.png',
                remember_token TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                last_login TIMESTAMP,
                last_ip TEXT,
                last_device TEXT,
                last_location TEXT,
                is_online BOOLEAN DEFAULT 0,
                theme TEXT DEFAULT 'light',
                last_activity TIMESTAMP,
                vvvip_expire TIMESTAMP,
                query_credit INTEGER DEFAULT 0,
                sign_last_date TEXT
            );
            CREATE TABLE IF NOT EXISTS friends (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                friend_id INTEGER NOT NULL,
                status TEXT DEFAULT 'pending',
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY(user_id) REFERENCES users(id),
                FOREIGN KEY(friend_id) REFERENCES users(id),
                UNIQUE(user_id, friend_id)
            );
            CREATE TABLE IF NOT EXISTS messages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                sender_id INTEGER,
                receiver_id INTEGER,
                content TEXT,
                image TEXT,
                file TEXT,
                is_recalled BOOLEAN DEFAULT 0,
                sent_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                read_at TIMESTAMP,
                deleted BOOLEAN DEFAULT 0,
                FOREIGN KEY(sender_id) REFERENCES users(id),
                FOREIGN KEY(receiver_id) REFERENCES users(id)
            );
            CREATE TABLE IF NOT EXISTS admin (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE NOT NULL,
                password TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS announcements (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                content TEXT NOT NULL,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            CREATE TABLE IF NOT EXISTS image_uploads (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                filename TEXT NOT NULL,
                url TEXT NOT NULL,
                expire_at TIMESTAMP NOT NULL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY(user_id) REFERENCES users(id)
            );
            CREATE TABLE IF NOT EXISTS upload_rate (
                user_id INTEGER PRIMARY KEY,
                upload_count INTEGER DEFAULT 0,
                last_reset TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            CREATE TABLE IF NOT EXISTS private_group_members (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL UNIQUE,
                added_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY(user_id) REFERENCES users(id)
            );
            CREATE TABLE IF NOT EXISTS card_keys (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                code TEXT UNIQUE NOT NULL,
                card_type TEXT NOT NULL,
                value INTEGER NOT NULL,
                used INTEGER DEFAULT 0,
                used_by INTEGER,
                used_at TIMESTAMP,
                created_by TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            CREATE TABLE IF NOT EXISTS sensitive_words (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                word TEXT UNIQUE NOT NULL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            CREATE INDEX IF NOT EXISTS idx_messages_read_at ON messages(read_at);
            CREATE INDEX IF NOT EXISTS idx_image_uploads_expire_at ON image_uploads(expire_at);
            CREATE INDEX IF NOT EXISTS idx_messages_receiver_sent ON messages(receiver_id, sent_at);
        ''')
        # 兼容旧表添加字段（若已存在则忽略）
        for col in ['last_activity', 'vvvvip_expire', 'query_credit', 'sign_last_date']:
            try:
                db.execute(f'ALTER TABLE users ADD COLUMN {col} TEXT')
            except:
                pass
        # 确保 query_credit 为 INTEGER（如果之前是 TEXT，转换）
        try:
            db.execute('UPDATE users SET query_credit = CAST(query_credit AS INTEGER)')
        except:
            pass
        db.commit()

        # 插入默认管理员
        admin_pwd = hashlib.md5('admin123'.encode()).hexdigest()
        db.execute('INSERT OR IGNORE INTO admin (username, password) VALUES (?, ?)', ('admin', admin_pwd))
        db.execute('INSERT OR IGNORE INTO announcements (id, content) VALUES (1, "欢迎使用沐风通讯！所有消息均通过 HTTPS 加密传输。")')
        # 插入默认敏感词
        default_words = ["王会军", "王易阳", "云凯翔", "杨宏源"]
        for word in default_words:
            db.execute('INSERT OR IGNORE INTO sensitive_words (word) VALUES (?)', (word,))
        db.commit()

        # 创建默认头像
        if not os.path.exists('static/default_avatar.png'):
            try:
                from PIL import Image, ImageDraw
                os.makedirs('static', exist_ok=True)
                img = Image.new('RGB', (128, 128), color=(59, 130, 246))
                draw = ImageDraw.Draw(img)
                draw.text((50, 50), 'U', fill='white')
                img.save('static/default_avatar.png')
            except:
                pass

init_db()

# ======================= 信号量释放 =======================
@app.teardown_request
def release_semaphore(exception=None):
    if hasattr(g, 'semaphore_acquired') and g.semaphore_acquired:
        semaphore.release()
        g.semaphore_acquired = False

# ======================= 全局安全中间件 =======================
@app.before_request
def security_middleware():
    ip = request.remote_addr
    if is_blocked(ip):
        return render_template('blocked.html', reason="IP 已被临时封禁，因检测到异常流量"), 403
    if is_using_proxy():
        record_failure(ip)
        return render_template('blocked.html', reason="检测到使用 VPN 或代理伪装，为保障安全已阻止访问"), 403
    if not check_rate_limit(ip):
        record_failure(ip)
        return render_template('blocked.html', reason="访问频率过高，疑似攻击行为，请稍后再试"), 429
    allowed_endpoints = ['login', 'register', 'admin_login', 'static', 'get_captcha', 'proxy_query']
    if 'user_id' not in session and (request.endpoint not in allowed_endpoints):
        online_count = get_online_users_count()
        if online_count > 150:
            return render_template('blocked.html', reason="当前服务器在线人数已满（超过150人），请稍后再试"), 503
    if not semaphore.acquire(blocking=False):
        return render_template('blocked.html', reason="当前访问量过大，服务器繁忙，请稍后重试"), 503
    g.semaphore_acquired = True
    if 'user_id' in session:
        db = get_db()
        db.execute('UPDATE users SET last_activity = ? WHERE id = ?', (datetime.now(), session['user_id']))
        db.commit()

@app.after_request
def log_failure(response):
    if response.status_code >= 400:
        record_failure(request.remote_addr)
    return response

# ======================= 辅助函数 =======================
def generate_uid():
    with app.app_context():
        db = get_db()
        while True:
            uid = str(int(time.time() * 1000))[-8:]
            exists = db.execute('SELECT id FROM users WHERE uid = ?', (uid,)).fetchone()
            if not exists:
                return uid

def get_qq_avatar(qq):
    url = f"https://q1.qlogo.cn/g?b=qq&nk={qq}&s=640"
    try:
        resp = requests.get(url, timeout=10)
        if resp.status_code == 200:
            filename = f"qq_{qq}.png"
            filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
            with open(filepath, 'wb') as f:
                f.write(resp.content)
            return f"/static/uploads/{filename}"
    except:
        pass
    return '/static/default_avatar.png'

def validate_qq(qq):
    return re.match(r'^[1-9]\d{4,11}$', qq) is not None

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'user_id' not in session:
            token = request.cookies.get('remember_token')
            if token:
                db = get_db()
                user = db.execute('SELECT * FROM users WHERE remember_token = ?', (token,)).fetchone()
                if user:
                    session.permanent = True
                    session['user_id'] = user['id']
                    session['username'] = user['username']
                    session['avatar'] = user['avatar']
                    session['uid'] = user['uid']
                    return f(*args, **kwargs)
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

def admin_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not session.get('is_admin'):
            return redirect(url_for('admin_login'))
        db = get_db()
        admin = db.execute('SELECT id FROM admin WHERE username = ?', ('admin',)).fetchone()
        if not admin:
            session.pop('is_admin', None)
            return redirect(url_for('admin_login'))
        return f(*args, **kwargs)
    return decorated_function

def cleanup_expired_messages():
    with app.app_context():
        db = get_db()
        expired = db.execute('''
            SELECT id, image, file FROM messages 
            WHERE deleted=0 AND read_at IS NOT NULL AND datetime(read_at) <= datetime('now', '-30 minutes')
        ''').fetchall()
        for msg in expired:
            if msg['image'] and os.path.exists(msg['image'].lstrip('/')):
                try: os.remove(msg['image'].lstrip('/'))
                except: pass
            if msg['file'] and os.path.exists(msg['file'].lstrip('/')):
                try: os.remove(msg['file'].lstrip('/'))
                except: pass
            db.execute('UPDATE messages SET deleted=1 WHERE id=?', (msg['id'],))
        db.commit()
        seven_days_ago = datetime.now() - timedelta(days=7)
        db.execute('DELETE FROM messages WHERE receiver_id = -1 AND sent_at <= ?', (seven_days_ago,))
        db.commit()

def cleanup_expired_images():
    with app.app_context():
        db = get_db()
        expired = db.execute('SELECT id, filename, url FROM image_uploads WHERE expire_at <= datetime("now")').fetchall()
        for img in expired:
            filepath = os.path.join(app.config['UPLOAD_FOLDER'], img['filename'])
            if os.path.exists(filepath):
                try: os.remove(filepath)
                except: pass
            db.execute('DELETE FROM image_uploads WHERE id = ?', (img['id'],))
        db.commit()

def start_cleanup_scheduler():
    def run():
        while True:
            time.sleep(60)
            cleanup_expired_messages()
            cleanup_expired_images()
    threading.Thread(target=run, daemon=True).start()

start_cleanup_scheduler()

def check_upload_rate(user_id):
    db = get_db()
    now = datetime.now()
    reset_time = now.replace(hour=0, minute=0, second=0, microsecond=0)
    record = db.execute('SELECT upload_count, last_reset FROM upload_rate WHERE user_id = ?', (user_id,)).fetchone()
    if not record:
        db.execute('INSERT INTO upload_rate (user_id, upload_count, last_reset) VALUES (?, 0, ?)', (user_id, reset_time))
        db.commit()
        return True
    last_reset = datetime.strptime(record['last_reset'], '%Y-%m-%d %H:%M:%S')
    if last_reset < reset_time:
        db.execute('UPDATE upload_rate SET upload_count = 0, last_reset = ? WHERE user_id = ?', (reset_time, user_id))
        db.commit()
        return True
    if record['upload_count'] >= 50:
        return False
    return True

def increment_upload_count(user_id):
    db = get_db()
    db.execute('UPDATE upload_rate SET upload_count = upload_count + 1 WHERE user_id = ?', (user_id,))
    db.commit()

# ---------- 卡密与权限函数 ----------
def has_query_permission(user_id):
    db = get_db()
    user = db.execute('SELECT vvvip_expire, query_credit FROM users WHERE id = ?', (user_id,)).fetchone()
    if not user:
        return False, "用户不存在"
    if user['vvvvip_expire']:
        try:
            expire = datetime.strptime(user['vvvvip_expire'], '%Y-%m-%d %H:%M:%S')
            if expire > datetime.now():
                return True, "vvvvip"
        except:
            pass
    if user['query_credit'] and user['query_credit'] > 0:
        return True, "credit"
    return False, None

def consume_credit(user_id):
    db = get_db()
    db.execute('UPDATE users SET query_credit = CAST(COALESCE(query_credit, 0) AS INTEGER) - 1 WHERE id = ? AND query_credit > 0', (user_id,))
    db.commit()

# ---------- 工具函数 ----------
def tool_gx_social_security(id_card):
    pub_key = "MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQCnUs9BxN1vawplBJI/uttk3bNyl/mFbvL555EhriFkgOBfQ4J1tyIUatItIp4gvl2cDDeyrmmKOzYPrzcChVv4Bg0Y94Wx4dSddCxQ172NyXXWV4MEPYkvwMucHeJjSrdchPqw+SRlYj2tmuRs56RXaf1r4eiyI0MzArHfSArejwIDAQAB"
    PUBLIC_KEY = f"-----BEGIN PUBLIC KEY-----\n{pub_key}\n-----END PUBLIC KEY-----"
    def rsa_encrypt(text):
        key = RSA.importKey(PUBLIC_KEY)
        cipher = PKCS1_v1_5.new(key)
        return base64.b64encode(cipher.encrypt(text.encode())).decode()
    if len(id_card) != 18:
        return {"success": False, "message": "身份证号必须18位"}
    url = "https://www.gx12333.net/mobile/ehrss-si-person/api/public/apply/scrz/scrzPersonnel"
    headers = {"SIAK":"SIA_V1","Content-Type":"application/json","Referer":"https://www.gx12333.net/wechat/html/zgrz/zgrz.html","User-Agent":"Mozilla/5.0","X-Requested-With":"com.tencent.mm"}
    data = {"aac002": rsa_encrypt(id_card), "src": "3"}
    try:
        resp = requests.post(url, headers=headers, json=data, verify=False, timeout=15)
        result = resp.json()
        if not result.get("result") or not result["result"].get("listPrc_p_gettreatmentinfo"):
            return {"success": False, "message": "未查询到人员信息"}
        info = result["result"]["listPrc_p_gettreatmentinfo"][0]
        name = info.get("name","未知")
        mobile = info.get("mobile","未知")
        address = info.get("personAddress","未知")
        birth_year = int(id_card[6:10])
        birth_month = int(id_card[10:12])
        birth_day = int(id_card[12:14])
        today = datetime.now()
        age = today.year - birth_year
        if (today.month, today.day) < (birth_month, birth_day):
            age -= 1
        gender = "男" if int(id_card[16]) % 2 == 1 else "女"
        msg = f"姓名: {name}\n性别: {gender}\n年龄: {age}\n手机号: {mobile}\n住址: {address}"
        return {"success": True, "message": msg}
    except Exception as e:
        return {"success": False, "message": str(e)}

def tool_lawyer_query(id_card):
    url = "http://180.101.234.37:10009/accept/lawyer/getLawyerInfoByIdCard"
    headers = {"Host":"180.101.234.37:10009","Accept":"application/json","User-Agent":"Mozilla/5.0"}
    params = {"cardnum": id_card}
    try:
        resp = requests.get(url, headers=headers, params=params, timeout=15)
        data = resp.json()
        if isinstance(data, list) and len(data) > 0:
            info = data[0]
            msg = f"姓名: {info.get('username','')}\n性别: {'男' if info.get('sex')=='1' else '女'}\n电话: {info.get('tel','')}\n执业证号: {info.get('workcardnumber','')}"
            return {"success": True, "message": msg}
        else:
            return {"success": False, "message": "未查询到律师信息"}
    except Exception as e:
        return {"success": False, "message": str(e)}

def tool_wechat_two_factor(name, wechat_id):
    URL = "https://fws.xuanyanmeng.com/fwszs/api/wechat/updataInfo"
    VERIFY_URL = "https://fws.xuanyanmeng.com/fwszs/api/wechat/xcx_register"
    HEADERS = {
        'token': 'e0d1692f29a8bef1f3f132bb3c30d88b',
        'Content-Type': 'application/json;charset=UTF-8',
        'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 16_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/16.0 Mobile/15E148 Safari/604.1'
    }
    request_data = {
        "tid": "1",
        "code_type": 1,
        "id": "18",
        "code": "1okkqlalla",
        "type": 2,
        "person_name": name,
        "name": "91",
        "wx_code": wechat_id
    }
    try:
        res2 = requests.post(VERIFY_URL, headers=HEADERS, json=request_data, timeout=10)
        if res2.status_code != 200:
            return {"success": False, "message": f"请求失败，状态码: {res2.status_code}"}
        result = res2.json()
        msg = result.get("msg", "")
        if 'code参数无效' in msg:
            return {"success": True, "message": f"核验成功：{name} 与微信号 {wechat_id} 一致"}
        elif '登录超时' in msg or '超时' in msg:
            return {"success": False, "message": "接口登录超时，可能是 token 已过期，请更新工具中的 token"}
        else:
            return {"success": False, "message": f"核验失败：{msg}"}
    except requests.exceptions.Timeout:
        return {"success": False, "message": "请求超时，请检查网络后重试"}
    except Exception as e:
        return {"success": False, "message": str(e)}

def tool_i66wan_two_factor(name, id_card):
    encoded_name = urllib.parse.quote(name)
    url = f"https://www.i66wan.com/game/idcard?gameId=33041&channelId=ios.cjdfw&version=102371&platType=5&platId=undefined&name={encoded_name}&idNum={id_card}&ai={id_card}"
    headers = {"Host":"www.i66wan.com","User-Agent":"hello_world-mobile/1.1","Accept":"*/*"}
    try:
        resp = requests.get(url, headers=headers, timeout=10)
        data = resp.json()
        if data.get("success") is True and data.get("data",{}).get("code") == 0:
            return {"success": True, "message": f"核验成功：{name} 与身份证 {id_card} 一致"}
        else:
            return {"success": False, "message": "核验失败，姓名与身份证不一致"}
    except Exception as e:
        return {"success": False, "message": str(e)}

def tool_fugitive_query(keyword):
    url = "http://www.zhuataofan.com/plus/advancedsearch.php"
    data = {"mid":"1","dopost":"search","body":keyword}
    headers = {"User-Agent":"Mozilla/5.0","Content-Type":"application/x-www-form-urlencoded"}
    try:
        resp = requests.post(url, headers=headers, data=data, timeout=15)
        if resp.status_code == 200:
            if "身份证号码" in resp.text:
                return {"success": True, "message": f"找到与 {keyword} 相关的在逃信息，请查看详情页面"}
            else:
                return {"success": False, "message": "未找到相关在逃记录"}
        else:
            return {"success": False, "message": "请求失败"}
    except Exception as e:
        return {"success": False, "message": str(e)}

def tool_double_call(mobile):
    url1 = "https://wskh.swsc.com.cn/swscFunc/151002"
    headers1 = {"Host":"wskh.swsc.com.cn","Content-Type":"application/x-www-form-urlencoded","User-Agent":"Mozilla/5.0"}
    data1 = f"mphone={mobile}&imageCode=&smsType=6"
    try:
        r1 = requests.post(url1, headers=headers1, data=data1, timeout=10)
        url2 = "https://epassport.diditaxi.com.cn/passport/login/v5/codeMT"
        headers2 = {"Host":"epassport.diditaxi.com.cn","content-type":"application/x-www-form-urlencoded"}
        data2 = f'{{"api_version":"1.0.1","appid":35011,"cell":"{mobile}","country_calling_code":"+86","code_type":1,"scene":1}}'
        payload = {"q": data2}
        r2 = requests.post(url2, headers=headers2, data=payload, timeout=10)
        return {"success": True, "message": f"呼叫接口已触发，手机号 {mobile}"}
    except Exception as e:
        return {"success": False, "message": str(e)}

# ---------- 前端路由 ----------
@app.route('/')
def index():
    if 'user_id' in session:
        return redirect(url_for('chat'))
    return redirect(url_for('login'))

@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == 'POST':
        identifier = request.form['identifier'].strip()
        password = hashlib.md5(request.form['password'].encode()).hexdigest()
        remember = request.form.get('remember') == 'on'
        captcha = request.form.get('captcha', '').strip()
        if not captcha or session.get('captcha_result') != captcha:
            return render_template('login.html', error='验证码错误')
        session.pop('captcha_result', None)
        
        db = get_db()
        user = db.execute('SELECT * FROM users WHERE username=? OR mobile=? OR qq=?',
                          (identifier, identifier, identifier)).fetchone()
        if user and user['password'] == password:
            ip = request.headers.get('X-Forwarded-For', request.remote_addr)
            session.permanent = remember
            session['user_id'] = user['id']
            session['username'] = user['username']
            session['avatar'] = user['avatar']
            session['uid'] = user['uid']
            db.execute('UPDATE users SET last_login=CURRENT_TIMESTAMP, last_ip=?, is_online=1, last_activity=? WHERE id=?', 
                       (ip, datetime.now(), user['id']))
            db.commit()
            resp = make_response(redirect(url_for('chat')))
            if remember:
                token = secrets.token_urlsafe(32)
                db.execute('UPDATE users SET remember_token=? WHERE id=?', (token, user['id']))
                db.commit()
                resp.set_cookie('remember_token', token, max_age=30*24*3600, httponly=True, secure=False)
            return resp
        else:
            return render_template('login.html', error='用户名/手机号/QQ号或密码错误')
    return render_template('login.html')

@app.route('/register', methods=['GET', 'POST'])
def register():
    if request.method == 'POST':
        username = request.form['username'].strip()
        password_raw = request.form['password']
        qq = request.form.get('qq', '').strip()
        mobile = request.form.get('mobile', '').strip()
        captcha = request.form.get('captcha', '').strip()
        if not captcha or session.get('captcha_result') != captcha:
            return render_template('register.html', error='验证码错误')
        session.pop('captcha_result', None)
        
        if len(username) < 3:
            return render_template('register.html', error='用户名至少3个字符')
        if not qq or not validate_qq(qq):
            return render_template('register.html', error='QQ号格式不正确')
        if not mobile or not re.match(r'^1[3-9]\d{9}$', mobile):
            return render_template('register.html', error='手机号格式不正确')
        db = get_db()
        if db.execute('SELECT id FROM users WHERE username=? OR qq=? OR mobile=?',
                      (username, qq, mobile)).fetchone():
            return render_template('register.html', error='用户名、QQ号或手机号已被注册')
        avatar = get_qq_avatar(qq)
        password = hashlib.md5(password_raw.encode()).hexdigest()
        uid = generate_uid()
        try:
            db.execute('''
                INSERT INTO users (uid, username, password, mobile, qq, avatar, last_activity) 
                VALUES (?, ?, ?, ?, ?, ?, ?)
            ''', (uid, username, password, mobile, qq, avatar, datetime.now()))
            db.commit()
            return redirect(url_for('login'))
        except:
            return render_template('register.html', error='注册失败')
    return render_template('register.html')

@app.route('/chat')
@login_required
def chat():
    partner_icons = []
    for f in ['partner1.webp', 'partner2.webp', 'partner3.png', 'partner4.webp']:
        path = os.path.join('static', 'partners', f)
        if os.path.exists(path):
            partner_icons.append(f'/static/partners/{f}')
    db = get_db()
    user = db.execute('SELECT theme FROM users WHERE id = ?', (session['user_id'],)).fetchone()
    theme = user['theme'] if user else 'light'
    return render_template('chat.html', username=session['username'], avatar=session['avatar'],
                           user_id=session['user_id'], uid=session['uid'], partner_icons=partner_icons, theme=theme)

@app.route('/profile')
@login_required
def profile():
    db = get_db()
    user = db.execute('SELECT id, uid, username, mobile, qq, avatar FROM users WHERE id = ?',
                      (session['user_id'],)).fetchone()
    return render_template('profile.html', user=user)

@app.route('/kubu')
@login_required
def kubu():
    return render_template('kubu.html')

@app.route('/help')
@login_required
def help_page():
    return render_template('help.html')

@app.route('/info_query')
@login_required
def info_query():
    return render_template('info_query.html')

# ---------- 算术验证码 API ----------
@app.route('/api/get_captcha', methods=['GET'])
def get_captcha():
    a = random.randint(1, 10)
    b = random.randint(1, 10)
    if random.choice([True, False]):
        result = a + b
        question = f"{a} + {b} = ?"
    else:
        if a < b:
            a, b = b, a
        result = a - b
        question = f"{a} - {b} = ?"
    session['captcha_result'] = str(result)
    return jsonify({'question': question})

# ---------- 代理查询 API ----------
@app.route('/api/proxy_query', methods=['POST'])
@login_required
def proxy_query():
    data = request.get_json()
    query = data.get('query')
    if not query:
        return jsonify({'success': False, 'message': '缺少查询内容'}), 400
    API_URL = 'http://qilange.518721.xyz/qy/xxw.php'
    API_KEY = '666'
    params = {'cx': query, 'key': API_KEY}
    try:
        resp = requests.get(API_URL, params=params, timeout=15)
        if resp.status_code != 200:
            resp = requests.post(API_URL, data=params, timeout=15)
        return resp.text, 200, {'Content-Type': 'text/plain; charset=utf-8'}
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)}), 500

# ---------- API 路由 ----------
@app.route('/api/send', methods=['POST'])
@login_required
def send_message():
    target_id = request.form.get('target_id')
    if target_id is None:
        return jsonify({'error': 'missing target_id'}), 400
    try:
        target_id = int(target_id)
    except ValueError:
        return jsonify({'error': 'invalid target_id'}), 400

    content = request.form.get('content', '').strip()
    image_url = None
    file_url = None

    if 'image' in request.files:
        img = request.files['image']
        if img and img.filename:
            orig = secure_filename(img.filename)
            if not orig:
                ext = img.filename.rsplit('.', 1)[-1].lower() if '.' in img.filename else 'jpg'
                orig = f"img_{secrets.token_hex(8)}.{ext}"
            timestamp = int(time.time())
            unique = secrets.token_hex(4)
            filename = f"{session['user_id']}_{timestamp}_{unique}_{orig}"
            filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
            try:
                img.save(filepath)
                image_url = f"/static/uploads/{filename}"
            except Exception as e:
                return jsonify({'error': 'image save failed'}), 500

    if 'file' in request.files:
        f = request.files['file']
        if f and f.filename:
            orig = secure_filename(f.filename)
            if not orig:
                ext = f.filename.rsplit('.', 1)[-1].lower() if '.' in f.filename else 'bin'
                orig = f"file_{secrets.token_hex(8)}.{ext}"
            timestamp = int(time.time())
            unique = secrets.token_hex(4)
            filename = f"{session['user_id']}_{timestamp}_{unique}_{orig}"
            filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
            try:
                f.save(filepath)
                file_url = f"/static/uploads/{filename}"
            except Exception as e:
                return jsonify({'error': 'file save failed'}), 500

    if not (content or image_url or file_url):
        return jsonify({'error': 'empty message'}), 400

    db = get_db()
    try:
        if target_id == 0:
            db.execute('INSERT INTO messages (sender_id, content, image, file) VALUES (?, ?, ?, ?)',
                       (session['user_id'], content, image_url, file_url))
        elif target_id == -1:
            member = db.execute('SELECT 1 FROM private_group_members WHERE user_id = ?', (session['user_id'],)).fetchone()
            if not member:
                return jsonify({'error': '您无权在私密群中发言'}), 403
            db.execute('INSERT INTO messages (sender_id, receiver_id, content, image, file) VALUES (?, ?, ?, ?, ?)',
                       (session['user_id'], -1, content, image_url, file_url))
        else:
            db.execute('INSERT INTO messages (sender_id, receiver_id, content, image, file) VALUES (?, ?, ?, ?, ?)',
                       (session['user_id'], target_id, content, image_url, file_url))
        db.commit()
        return '', 204
    except Exception as e:
        print(f"发送消息失败: {e}")
        return jsonify({'error': str(e)}), 500

@app.route('/api/private_messages')
@login_required
def get_private_messages():
    db = get_db()
    my_id = session['user_id']
    member = db.execute('SELECT 1 FROM private_group_members WHERE user_id = ?', (my_id,)).fetchone()
    if not member:
        return jsonify({'error': '无权限访问私密群'}), 403
    msgs = db.execute('''
        SELECT m.id, m.sender_id, u.username, u.avatar, m.content, m.image, m.file, m.is_recalled, m.sent_at, m.read_at
        FROM messages m JOIN users u ON m.sender_id = u.id
        WHERE m.receiver_id = -1 AND m.deleted=0
        ORDER BY m.sent_at ASC LIMIT 200
    ''').fetchall()
    db.execute('UPDATE messages SET read_at = COALESCE(read_at, CURRENT_TIMESTAMP) WHERE receiver_id = -1 AND deleted=0 AND read_at IS NULL')
    db.commit()
    return jsonify([dict(m) for m in msgs])

@app.route('/api/private_messages/send', methods=['POST'])
@login_required
def send_private_message():
    content = request.form.get('content', '').strip()
    image_url = None
    file_url = None

    if 'image' in request.files:
        img = request.files['image']
        if img and img.filename:
            orig = secure_filename(img.filename)
            if not orig:
                ext = img.filename.rsplit('.', 1)[-1].lower() if '.' in img.filename else 'jpg'
                orig = f"img_{secrets.token_hex(8)}.{ext}"
            timestamp = int(time.time())
            unique = secrets.token_hex(4)
            filename = f"{session['user_id']}_{timestamp}_{unique}_{orig}"
            filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
            try:
                img.save(filepath)
                image_url = f"/static/uploads/{filename}"
            except Exception as e:
                return jsonify({'error': 'image save failed'}), 500

    if 'file' in request.files:
        f = request.files['file']
        if f and f.filename:
            orig = secure_filename(f.filename)
            if not orig:
                ext = f.filename.rsplit('.', 1)[-1].lower() if '.' in f.filename else 'bin'
                orig = f"file_{secrets.token_hex(8)}.{ext}"
            timestamp = int(time.time())
            unique = secrets.token_hex(4)
            filename = f"{session['user_id']}_{timestamp}_{unique}_{orig}"
            filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
            try:
                f.save(filepath)
                file_url = f"/static/uploads/{filename}"
            except Exception as e:
                return jsonify({'error': 'file save failed'}), 500

    if not (content or image_url or file_url):
        return jsonify({'error': 'empty message'}), 400

    db = get_db()
    member = db.execute('SELECT 1 FROM private_group_members WHERE user_id = ?', (session['user_id'],)).fetchone()
    if not member:
        return jsonify({'error': '您无权在私密群中发言'}), 403

    db.execute('INSERT INTO messages (sender_id, receiver_id, content, image, file) VALUES (?, ?, ?, ?, ?)',
               (session['user_id'], -1, content, image_url, file_url))
    db.commit()
    return '', 204

@app.route('/api/messages/<int:target_id>')
@login_required
def get_messages(target_id):
    db = get_db()
    my_id = session['user_id']
    if target_id == 0:
        msgs = db.execute('''
            SELECT m.id, m.sender_id, u.username, u.avatar, m.content, m.image, m.file, m.is_recalled, m.sent_at, m.read_at
            FROM messages m JOIN users u ON m.sender_id = u.id
            WHERE m.receiver_id IS NULL AND m.deleted=0
            ORDER BY m.sent_at ASC LIMIT 200
        ''').fetchall()
        db.execute('UPDATE messages SET read_at = COALESCE(read_at, CURRENT_TIMESTAMP) WHERE receiver_id IS NULL AND deleted=0 AND read_at IS NULL')
        db.commit()
        return jsonify([dict(m) for m in msgs])
    elif target_id == -1:
        member = db.execute('SELECT 1 FROM private_group_members WHERE user_id = ?', (my_id,)).fetchone()
        if not member:
            return jsonify({'error': '无权限访问私密群'}), 403
        msgs = db.execute('''
            SELECT m.id, m.sender_id, u.username, u.avatar, m.content, m.image, m.file, m.is_recalled, m.sent_at, m.read_at
            FROM messages m JOIN users u ON m.sender_id = u.id
            WHERE m.receiver_id = -1 AND m.deleted=0
            ORDER BY m.sent_at ASC LIMIT 200
        ''').fetchall()
        db.execute('UPDATE messages SET read_at = COALESCE(read_at, CURRENT_TIMESTAMP) WHERE receiver_id = -1 AND deleted=0 AND read_at IS NULL')
        db.commit()
        return jsonify([dict(m) for m in msgs])
    else:
        msgs = db.execute('''
            SELECT m.id, m.sender_id, u.username, u.avatar, m.content, m.image, m.file, m.is_recalled, m.sent_at, m.read_at
            FROM messages m JOIN users u ON m.sender_id = u.id
            WHERE ((m.sender_id=? AND m.receiver_id=?) OR (m.sender_id=? AND m.receiver_id=?))
              AND m.deleted=0
            ORDER BY m.sent_at ASC LIMIT 200
        ''', (my_id, target_id, target_id, my_id)).fetchall()
        db.execute('UPDATE messages SET read_at = COALESCE(read_at, CURRENT_TIMESTAMP) WHERE receiver_id=? AND sender_id=? AND deleted=0 AND read_at IS NULL', (my_id, target_id))
        db.commit()
        return jsonify([dict(m) for m in msgs])

@app.route('/api/recall_message', methods=['POST'])
@login_required
def recall_message():
    data = request.get_json()
    message_id = data.get('message_id')
    if not message_id:
        return jsonify({'success': False, 'message': '缺少消息ID'})
    db = get_db()
    msg = db.execute('SELECT sender_id, sent_at FROM messages WHERE id = ?', (message_id,)).fetchone()
    if not msg:
        return jsonify({'success': False, 'message': '消息不存在'})
    if msg['sender_id'] != session['user_id']:
        return jsonify({'success': False, 'message': '只能撤回自己的消息'})
    sent_time = datetime.strptime(msg['sent_at'], '%Y-%m-%d %H:%M:%S')
    if (datetime.now() - sent_time).seconds > 120:
        return jsonify({'success': False, 'message': '超过2分钟无法撤回'})
    db.execute('UPDATE messages SET content = "[消息已撤回]", is_recalled = 1 WHERE id = ?', (message_id,))
    db.commit()
    return jsonify({'success': True})

@app.route('/api/generate_qrcode')
@login_required
def generate_qrcode():
    import qrcode
    from io import BytesIO
    qr_data = json.dumps({'type': 'add_friend', 'uid': session['uid'], 'username': session['username']})
    qr = qrcode.QRCode(version=1, box_size=10, border=4)
    qr.add_data(qr_data)
    qr.make(fit=True)
    img = qr.make_image(fill_color='#3b82f6', back_color='white')
    buffered = BytesIO()
    img.save(buffered, format='PNG')
    img_base64 = base64.b64encode(buffered.getvalue()).decode().replace('\n', '')
    return jsonify({'qrcode': img_base64})

@app.route('/api/add_friend', methods=['POST'])
@login_required
def add_friend():
    data = request.get_json()
    friend_uid = data.get('uid')
    if not friend_uid:
        return jsonify({'success': False, 'message': '请提供好友UID'})
    db = get_db()
    target = db.execute('SELECT id, username FROM users WHERE uid = ?', (friend_uid,)).fetchone()
    if not target:
        return jsonify({'success': False, 'message': '用户不存在'})
    if target['id'] == session['user_id']:
        return jsonify({'success': False, 'message': '不能添加自己为好友'})
    existing = db.execute('SELECT * FROM friends WHERE (user_id=? AND friend_id=?) OR (user_id=? AND friend_id=?)',
                          (session['user_id'], target['id'], target['id'], session['user_id'])).fetchone()
    if existing:
        if existing['status'] == 'accepted':
            return jsonify({'success': False, 'message': '已经是好友了'})
        elif existing['status'] == 'pending':
            return jsonify({'success': False, 'message': '已发送过好友请求'})
    db.execute('INSERT INTO friends (user_id, friend_id, status) VALUES (?, ?, ?)',
               (session['user_id'], target['id'], 'pending'))
    db.commit()
    return jsonify({'success': True, 'message': f'已向 {target["username"]} 发送好友请求'})

@app.route('/api/friend_requests')
@login_required
def get_friend_requests():
    db = get_db()
    reqs = db.execute('''
        SELECT f.id, f.user_id, u.username, u.avatar, u.uid, f.created_at
        FROM friends f JOIN users u ON f.user_id = u.id
        WHERE f.friend_id = ? AND f.status = 'pending'
    ''', (session['user_id'],)).fetchall()
    return jsonify([dict(r) for r in reqs])

@app.route('/api/accept_friend', methods=['POST'])
@login_required
def accept_friend():
    data = request.get_json()
    request_id = data.get('request_id')
    db = get_db()
    friend_req = db.execute('SELECT * FROM friends WHERE id = ? AND friend_id = ? AND status = "pending"',
                            (request_id, session['user_id'])).fetchone()
    if not friend_req:
        return jsonify({'success': False, 'message': '好友请求不存在'})
    db.execute('UPDATE friends SET status = "accepted", updated_at = CURRENT_TIMESTAMP WHERE id = ?', (request_id,))
    db.commit()
    return jsonify({'success': True, 'message': '已添加好友'})

@app.route('/api/friends')
@login_required
def get_friends():
    db = get_db()
    friends = db.execute('''
        SELECT u.id, u.username, u.avatar, u.uid, u.is_online
        FROM friends f JOIN users u ON (f.user_id = u.id OR f.friend_id = u.id)
        WHERE (f.user_id = ? OR f.friend_id = ?) AND f.status = "accepted" AND u.id != ?
    ''', (session['user_id'], session['user_id'], session['user_id'])).fetchall()
    return jsonify([dict(f) for f in friends])

@app.route('/api/update_online', methods=['POST'])
@login_required
def update_online():
    db = get_db()
    db.execute('UPDATE users SET is_online = 1, last_activity = ? WHERE id = ?', (datetime.now(), session['user_id']))
    db.commit()
    return '', 204

@app.route('/api/update_theme', methods=['POST'])
@login_required
def update_theme():
    data = request.get_json()
    theme = data.get('theme')
    if theme not in ['light', 'dark', 'blue', 'green']:
        theme = 'light'
    db = get_db()
    db.execute('UPDATE users SET theme = ? WHERE id = ?', (theme, session['user_id']))
    db.commit()
    return jsonify({'success': True})

@app.route('/api/announcement')
def get_announcement():
    db = get_db()
    ann = db.execute('SELECT content FROM announcements ORDER BY updated_at DESC LIMIT 1').fetchone()
    content = ann['content'] if ann else '欢迎使用沐风通讯！'
    return jsonify({'content': content})

@app.route('/api/logout', methods=['POST'])
@login_required
def api_logout():
    db = get_db()
    db.execute('UPDATE users SET is_online = 0 WHERE id = ?', (session['user_id'],))
    db.commit()
    session.clear()
    resp = jsonify({'success': True})
    resp.set_cookie('remember_token', '', expires=0)
    return resp

@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('login'))

# ---------- 图床 API ----------
@app.route('/api/upload_image', methods=['POST'])
@login_required
def upload_image():
    user_id = session['user_id']
    if not check_upload_rate(user_id):
        return jsonify({'success': False, 'message': '今日上传次数已达上限（50张）'})
    if 'image' not in request.files:
        return jsonify({'success': False, 'message': '没有文件'}), 400
    file = request.files['image']
    if file.filename == '':
        return jsonify({'success': False, 'message': '文件名为空'}), 400
    expire_months = request.form.get('expire', '1')
    try:
        expire_months = int(expire_months)
        if expire_months not in [0, 1, 3, 6, 12, 24]:
            expire_months = 1
    except:
        expire_months = 1
    if expire_months == 0:
        expire_date = datetime(9999, 12, 31, 23, 59, 59)
    else:
        expire_date = datetime.now() + timedelta(days=expire_months*30)
    ext = file.filename.rsplit('.', 1)[-1].lower()
    if ext not in ['jpg', 'jpeg', 'png', 'gif', 'webp']:
        return jsonify({'success': False, 'message': '不支持的图片格式'}), 400
    filename = f"img_{secrets.token_hex(8)}.{ext}"
    filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
    try:
        file.save(filepath)
        url = f"/static/uploads/{filename}"
        db = get_db()
        db.execute('INSERT INTO image_uploads (user_id, filename, url, expire_at) VALUES (?, ?, ?, ?)',
                   (user_id, filename, url, expire_date.strftime('%Y-%m-%d %H:%M:%S')))
        increment_upload_count(user_id)
        db.commit()
        expire_display = "永久" if expire_months == 0 else expire_date.strftime('%Y-%m-%d')
        return jsonify({'success': True, 'url': url, 'expire_at': expire_display})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)}), 500

# ---------- 私密群成员检查 API ----------
@app.route('/api/is_private_member')
@login_required
def is_private_member():
    db = get_db()
    member = db.execute('SELECT 1 FROM private_group_members WHERE user_id = ?', (session['user_id'],)).fetchone()
    return jsonify({'is_member': member is not None})

# ---------- 卡密相关 API ----------
@app.route('/api/activate_card', methods=['POST'])
@login_required
def activate_card():
    data = request.get_json()
    code = data.get('code', '').strip()
    if not code:
        return jsonify({'success': False, 'message': '请输入卡密'})
    db = get_db()
    card = db.execute('SELECT * FROM card_keys WHERE code = ? AND used = 0', (code,)).fetchone()
    if not card:
        return jsonify({'success': False, 'message': '卡密无效或已使用'})
    user_id = session['user_id']
    print(f"[激活卡密] 用户ID: {user_id}, 卡密类型: {card['card_type']}, 值: {card['value']}")
    if card['card_type'] == 'vvvvip':
        days = card['value']
        current = db.execute('SELECT vvvip_expire FROM users WHERE id = ?', (user_id,)).fetchone()
        new_expire = datetime.now() + timedelta(days=days)
        if current and current['vvvvip_expire']:
            try:
                old_expire = datetime.strptime(current['vvvvip_expire'], '%Y-%m-%d %H:%M:%S')
                if old_expire > datetime.now():
                    new_expire = old_expire + timedelta(days=days)
            except:
                pass
        db.execute('UPDATE users SET vvvip_expire = ? WHERE id = ?', (new_expire.strftime('%Y-%m-%d %H:%M:%S'), user_id))
        msg = f'激活成功！获得VIP {days} 天'
    else:
        credits = card['value']
        # 使用 CAST 确保数值运算
        db.execute('UPDATE users SET query_credit = CAST(COALESCE(query_credit, 0) AS INTEGER) + ? WHERE id = ?', (credits, user_id))
        msg = f'激活成功！获得 {credits} 次查询次数'
    db.execute('UPDATE card_keys SET used = 1, used_by = ?, used_at = CURRENT_TIMESTAMP WHERE id = ?', (user_id, card['id']))
    db.commit()
    # 打印后确认
    after = db.execute('SELECT query_credit FROM users WHERE id = ?', (user_id,)).fetchone()
    print(f"[激活后] 用户 {user_id} 次数: {after['query_credit'] if after else 'None'}")
    return jsonify({'success': True, 'message': msg})

@app.route('/api/user_query_info')
@login_required
def user_query_info():
    try:
        db = get_db()
        user = db.execute('SELECT vvvip_expire, query_credit, sign_last_date FROM users WHERE id = ?', (session['user_id'],)).fetchone()
        if not user:
            return jsonify({'type': 'credit', 'credits': 0, 'sign_last_date': None})
        result = {}
        if user['vvvvip_expire']:
            try:
                expire = datetime.strptime(user['vvvvip_expire'], '%Y-%m-%d %H:%M:%S')
                if expire > datetime.now():
                    result['type'] = 'vvvvip'
                    result['vip_remaining_days'] = (expire - datetime.now()).days
                    result['vip_total_days'] = 365
                    result['credits'] = -1
                    result['sign_last_date'] = user['sign_last_date']
                    return jsonify(result)
            except Exception as e:
                print(f"VIP解析错误: {e}")
        result['type'] = 'credit'
        result['credits'] = user['query_credit'] if user['query_credit'] is not None else 0
        result['sign_last_date'] = user['sign_last_date']
        return jsonify(result)
    except Exception as e:
        print(f"/api/user_query_info 出错: {e}")
        import traceback
        traceback.print_exc()
        return jsonify({'type': 'credit', 'credits': 0, 'sign_last_date': None})

@app.route('/api/consume_query', methods=['POST'])
@login_required
def consume_query():
    allowed, type_ = has_query_permission(session['user_id'])
    if not allowed:
        return jsonify({'success': False, 'message': '无查询次数'})
    if type_ == 'credit':
        db = get_db()
        user_id = session['user_id']
        db.execute('UPDATE users SET query_credit = CAST(COALESCE(query_credit, 0) AS INTEGER) - 1 WHERE id = ? AND query_credit > 0', (user_id,))
        db.commit()
    return jsonify({'success': True})

@app.route('/api/daily_sign', methods=['POST'])
@login_required
def daily_sign():
    db = get_db()
    user_id = session['user_id']
    today = datetime.now().strftime('%Y-%m-%d')
    user = db.execute('SELECT sign_last_date, query_credit FROM users WHERE id = ?', (user_id,)).fetchone()
    if not user:
        return jsonify({'success': False, 'message': '用户不存在'})
    if user['sign_last_date'] == today:
        return jsonify({'success': False, 'message': '今天已经签到过了'})
    print(f"[签到前] 用户 {user_id} 次数: {user['query_credit']}")
    db.execute('UPDATE users SET query_credit = CAST(COALESCE(query_credit, 0) AS INTEGER) + 1, sign_last_date = ? WHERE id = ?', (today, user_id))
    db.commit()
    after = db.execute('SELECT query_credit FROM users WHERE id = ?', (user_id,)).fetchone()
    print(f"[签到后] 用户 {user_id} 次数: {after['query_credit']}")
    return jsonify({'success': True, 'message': '签到成功，获得1次查询次数'})

# ---------- 敏感词 API ----------
@app.route('/api/sensitive_words', methods=['GET'])
@login_required
def get_sensitive_words():
    db = get_db()
    words = db.execute('SELECT word FROM sensitive_words').fetchall()
    return jsonify([w['word'] for w in words])

# ---------- 工具 API ----------
@app.route('/api/tool/<tool_id>', methods=['POST'])
@login_required
def run_tool(tool_id):
    data = request.get_json() or {}
    tool_map = {
        'gx_social_security': tool_gx_social_security,
        'lawyer_query': tool_lawyer_query,
        'wechat_two_factor': tool_wechat_two_factor,
        'i66wan_two_factor': tool_i66wan_two_factor,
        'fugitive_query': tool_fugitive_query,
        'double_call': tool_double_call,
    }
    if tool_id not in tool_map:
        return jsonify({'success': False, 'message': '工具不存在'})
    try:
        result = tool_map[tool_id](**data)
        return jsonify(result)
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

# ---------- 管理员后台 ----------
@app.route('/admin/login', methods=['GET', 'POST'])
def admin_login():
    if request.method == 'POST':
        username = request.form['username'].strip()
        password = hashlib.md5(request.form['password'].encode()).hexdigest()
        db = get_db()
        admin = db.execute('SELECT * FROM admin WHERE username = ? AND password = ?', (username, password)).fetchone()
        if admin:
            session['is_admin'] = True
            return redirect(url_for('admin_dashboard'))
        else:
            return render_template('admin_login.html', error='用户名或密码错误')
    return render_template('admin_login.html')

@app.route('/admin')
@admin_required
def admin_dashboard():
    return render_template('admin_dashboard.html')

@app.route('/admin/api/users')
@admin_required
def admin_get_users():
    db = get_db()
    users = db.execute('SELECT id, uid, username, mobile, qq, avatar, created_at, last_login, last_ip, last_device, last_location, is_online FROM users ORDER BY id DESC').fetchall()
    return jsonify([dict(u) for u in users])

@app.route('/admin/api/search_users')
@admin_required
def admin_search_users():
    keyword = request.args.get('q', '')
    db = get_db()
    users = db.execute('SELECT id, uid, username, mobile, qq, avatar, created_at, last_login, last_ip, last_device, last_location, is_online FROM users WHERE username LIKE ? OR mobile LIKE ? OR qq LIKE ? OR uid LIKE ? ORDER BY id DESC',
                       (f'%{keyword}%', f'%{keyword}%', f'%{keyword}%', f'%{keyword}%')).fetchall()
    return jsonify([dict(u) for u in users])

@app.route('/admin/api/update_password', methods=['POST'])
@admin_required
def admin_update_password():
    data = request.get_json()
    new_password = data.get('password')
    if not new_password or len(new_password) < 6:
        return jsonify({'success': False, 'message': '密码至少6位'})
    hashed = hashlib.md5(new_password.encode()).hexdigest()
    db = get_db()
    db.execute('UPDATE admin SET password = ? WHERE username = "admin"', (hashed,))
    db.commit()
    return jsonify({'success': True, 'message': '密码已更新'})

@app.route('/admin/api/delete_user', methods=['POST'])
@admin_required
def admin_delete_user():
    data = request.get_json()
    user_id = data.get('user_id')
    if not user_id:
        return jsonify({'success': False, 'message': '缺少用户ID'})
    db = get_db()
    db.execute('DELETE FROM friends WHERE user_id = ? OR friend_id = ?', (user_id, user_id))
    db.execute('DELETE FROM messages WHERE sender_id = ? OR receiver_id = ?', (user_id, user_id))
    db.execute('DELETE FROM users WHERE id = ?', (user_id,))
    db.commit()
    return jsonify({'success': True, 'message': '用户已删除'})

@app.route('/admin/api/update_user_uid', methods=['POST'])
@admin_required
def admin_update_user_uid():
    data = request.get_json()
    user_id = data.get('user_id')
    new_uid = data.get('new_uid')
    if not user_id or not new_uid:
        return jsonify({'success': False, 'message': '参数不完整'})
    if not new_uid.isdigit() or len(new_uid) != 8:
        return jsonify({'success': False, 'message': 'UID必须为8位数字'})
    db = get_db()
    existing = db.execute('SELECT id FROM users WHERE uid = ? AND id != ?', (new_uid, user_id)).fetchone()
    if existing:
        return jsonify({'success': False, 'message': 'UID已存在'})
    db.execute('UPDATE users SET uid = ? WHERE id = ?', (new_uid, user_id))
    db.commit()
    return jsonify({'success': True, 'message': 'UID已更新'})

@app.route('/admin/api/reset_user_password', methods=['POST'])
@admin_required
def admin_reset_user_password():
    data = request.get_json()
    user_id = data.get('user_id')
    new_password = data.get('new_password', '123456')
    if not user_id:
        return jsonify({'success': False, 'message': '缺少用户ID'})
    hashed = hashlib.md5(new_password.encode()).hexdigest()
    db = get_db()
    db.execute('UPDATE users SET password = ? WHERE id = ?', (hashed, user_id))
    db.commit()
    return jsonify({'success': True, 'message': f'密码已重置为 {new_password}'})

@app.route('/admin/api/update_user_mobile', methods=['POST'])
@admin_required
def admin_update_user_mobile():
    data = request.get_json()
    user_id = data.get('user_id')
    new_mobile = data.get('new_mobile')
    if not user_id or not new_mobile:
        return jsonify({'success': False, 'message': '参数不完整'})
    if not re.match(r'^1[3-9]\d{9}$', new_mobile):
        return jsonify({'success': False, 'message': '手机号格式不正确'})
    db = get_db()
    existing = db.execute('SELECT id FROM users WHERE mobile = ? AND id != ?', (new_mobile, user_id)).fetchone()
    if existing:
        return jsonify({'success': False, 'message': '手机号已被占用'})
    db.execute('UPDATE users SET mobile = ? WHERE id = ?', (new_mobile, user_id))
    db.commit()
    return jsonify({'success': True, 'message': '手机号已更新'})

@app.route('/admin/api/update_user_qq', methods=['POST'])
@admin_required
def admin_update_user_qq():
    data = request.get_json()
    user_id = data.get('user_id')
    new_qq = data.get('new_qq')
    if not user_id or not new_qq:
        return jsonify({'success': False, 'message': '参数不完整'})
    if not re.match(r'^[1-9]\d{4,11}$', new_qq):
        return jsonify({'success': False, 'message': 'QQ号格式不正确'})
    db = get_db()
    existing = db.execute('SELECT id FROM users WHERE qq = ? AND id != ?', (new_qq, user_id)).fetchone()
    if existing:
        return jsonify({'success': False, 'message': 'QQ号已被占用'})
    db.execute('UPDATE users SET qq = ? WHERE id = ?', (new_qq, user_id))
    db.commit()
    return jsonify({'success': True, 'message': 'QQ号已更新'})

@app.route('/admin/api/announcement', methods=['GET', 'POST'])
@admin_required
def admin_announcement():
    db = get_db()
    if request.method == 'GET':
        ann = db.execute('SELECT content FROM announcements ORDER BY updated_at DESC LIMIT 1').fetchone()
        return jsonify({'content': ann['content'] if ann else ''})
    else:
        data = request.get_json()
        content = data.get('content', '').strip()
        if not content:
            return jsonify({'success': False, 'message': '公告内容不能为空'})
        db.execute('UPDATE announcements SET content = ?, updated_at = CURRENT_TIMESTAMP WHERE id = 1')
        if db.rowcount == 0:
            db.execute('INSERT INTO announcements (id, content) VALUES (1, ?)', (content,))
        db.commit()
        return jsonify({'success': True, 'message': '公告已更新'})

@app.route('/admin/api/system_stats')
@admin_required
def system_stats():
    cpu_percent = psutil.cpu_percent(interval=1)
    cpu_count = psutil.cpu_count()
    mem = psutil.virtual_memory()
    disk = psutil.disk_usage('/')
    net_io = psutil.net_io_counters()
    load_avg = psutil.getloadavg()
    boot_time = datetime.fromtimestamp(psutil.boot_time()).strftime('%Y-%m-%d %H:%M:%S')
    return jsonify({
        'cpu_percent': cpu_percent,
        'cpu_count': cpu_count,
        'memory_total': mem.total,
        'memory_used': mem.used,
        'memory_percent': mem.percent,
        'disk_total': disk.total,
        'disk_used': disk.used,
        'disk_percent': disk.percent,
        'net_sent': net_io.bytes_sent,
        'net_recv': net_io.bytes_recv,
        'load_avg': load_avg,
        'boot_time': boot_time,
        'platform': platform.platform()
    })

# ---------- 私密群成员管理 API（管理员） ----------
@app.route('/admin/api/private_members')
@admin_required
def admin_private_members():
    db = get_db()
    members = db.execute('''
        SELECT u.id, u.username, u.uid, u.mobile, u.qq, pm.added_at
        FROM private_group_members pm
        JOIN users u ON pm.user_id = u.id
        ORDER BY pm.added_at DESC
    ''').fetchall()
    return jsonify([dict(m) for m in members])

@app.route('/admin/api/private_members/add', methods=['POST'])
@admin_required
def admin_private_members_add():
    data = request.get_json()
    identifier = data.get('identifier', '').strip()
    if not identifier:
        return jsonify({'success': False, 'message': '请输入用户名/UID/手机号/QQ'})
    db = get_db()
    user = db.execute('SELECT id FROM users WHERE username=? OR uid=? OR mobile=? OR qq=?',
                      (identifier, identifier, identifier, identifier)).fetchone()
    if not user:
        return jsonify({'success': False, 'message': '用户不存在'})
    try:
        db.execute('INSERT INTO private_group_members (user_id) VALUES (?)', (user['id'],))
        db.commit()
        return jsonify({'success': True, 'message': '已添加至私密群'})
    except sqlite3.IntegrityError:
        return jsonify({'success': False, 'message': '该用户已在私密群中'})

@app.route('/admin/api/private_members/remove', methods=['POST'])
@admin_required
def admin_private_members_remove():
    data = request.get_json()
    user_id = data.get('user_id')
    if not user_id:
        return jsonify({'success': False, 'message': '缺少用户ID'})
    db = get_db()
    db.execute('DELETE FROM private_group_members WHERE user_id = ?', (user_id,))
    db.commit()
    return jsonify({'success': True, 'message': '已移出私密群'})

# ---------- 卡密管理 API（管理员） ----------
@app.route('/admin/api/card_keys', methods=['GET'])
@admin_required
def admin_get_card_keys():
    db = get_db()
    cards = db.execute('SELECT * FROM card_keys ORDER BY created_at DESC').fetchall()
    return jsonify([dict(c) for c in cards])

@app.route('/admin/api/card_keys/generate', methods=['POST'])
@admin_required
def admin_generate_card():
    data = request.get_json()
    card_type = data.get('type')
    value = int(data.get('value'))
    count = int(data.get('count', 1))
    if card_type not in ('vvvvip', 'credit'):
        return jsonify({'success': False, 'message': '类型错误'})
    if value <= 0:
        return jsonify({'success': False, 'message': '天数/次数必须大于0'})
    if count <= 0 or count > 100:
        return jsonify({'success': False, 'message': '数量需在1-100之间'})
    db = get_db()
    codes = []
    for _ in range(count):
        code = secrets.token_hex(16).upper()
        db.execute('INSERT INTO card_keys (code, card_type, value, created_by) VALUES (?, ?, ?, ?)',
                   (code, card_type, value, 'admin'))
        codes.append(code)
    db.commit()
    return jsonify({'success': True, 'codes': codes})

# ---------- 敏感词管理 API（管理员） ----------
@app.route('/admin/api/sensitive_words', methods=['GET'])
@admin_required
def admin_get_sensitive_words():
    db = get_db()
    words = db.execute('SELECT id, word, created_at FROM sensitive_words ORDER BY created_at DESC').fetchall()
    return jsonify([dict(w) for w in words])

@app.route('/admin/api/sensitive_words/add', methods=['POST'])
@admin_required
def admin_add_sensitive_word():
    data = request.get_json()
    word = data.get('word', '').strip()
    if not word:
        return jsonify({'success': False, 'message': '敏感词不能为空'})
    db = get_db()
    try:
        db.execute('INSERT INTO sensitive_words (word) VALUES (?)', (word,))
        db.commit()
        return jsonify({'success': True})
    except sqlite3.IntegrityError:
        return jsonify({'success': False, 'message': '敏感词已存在'})

@app.route('/admin/api/sensitive_words/delete', methods=['POST'])
@admin_required
def admin_delete_sensitive_word():
    data = request.get_json()
    word_id = data.get('id')
    if not word_id:
        return jsonify({'success': False, 'message': '缺少ID'})
    db = get_db()
    db.execute('DELETE FROM sensitive_words WHERE id = ?', (word_id,))
    db.commit()
    return jsonify({'success': True})

@app.route('/admin/logout')
@admin_required
def admin_logout():
    session.pop('is_admin', None)
    return redirect(url_for('admin_login'))

@app.after_request
def add_ngrok_header(response):
    response.headers['ngrok-skip-browser-warning'] = 'true'
    return response

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=8080, debug=True)
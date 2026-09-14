"""
Pomken — 食事記録ビューワー

Google Drive の「食事画像」フォルダから写真を取り込み、Gemini で説明文を付けて
Google Photos 風ギャラリーで閲覧・検索するだけのアプリ。

2026-09-14 に食事記録専用へ縮小。ナレッジ画像（metadata.json / uploads / .thumb_cache/ss_*）は
book-capture が参照するためデータはそのまま残しているが、このアプリからは触らない。
体重記録・カロリー計算・Sheets 同期は廃止（weight_data.json はローカルのみ）。
縮小前の全機能版は app.py.bak-20260914-full と git 履歴にある。

起動: python -m streamlit run app.py --server.headless=true
"""
from __future__ import annotations

import hashlib
import hmac
import html
import io
import json
import logging
import os
import re
import shutil
import subprocess
import threading
import time
import uuid
from datetime import datetime, date
from pathlib import Path

import streamlit as st
from PIL import Image
from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload

import food_search as _fs

# ---------------------------------------------------------------------------
# ログ・定数
# ---------------------------------------------------------------------------
ROOT = Path(__file__).resolve().parent
_LOG_PATH = ROOT / "app_debug.log"
logging.basicConfig(
    filename=str(_LOG_PATH),
    level=logging.INFO,
    format="%(asctime)s %(message)s",
    encoding="utf-8",
)
_log = logging.getLogger("pomken")

IMAGE_MIME_TYPES = ["image/jpeg", "image/png"]
SCOPES = ["https://www.googleapis.com/auth/drive"]

WEIGHT_DATA_PATH = ROOT / "weight_data.json"          # 食事写真の台帳（名前は歴史的経緯）
FOOD_IMAGES_PROCESSED_PATH = ROOT / "food_images_processed.json"
WEIGHT_UPLOADS_DIR = ROOT / "weight_uploads"
THUMB_CACHE_DIR = ROOT / ".thumb_cache"
BACKUP_DIR = ROOT / "backups"
_AUTH_STATE_PATH = ROOT / ".auth_state"

FOOD_SCAN_INTERVAL = 300      # 自動取り込みの間隔（秒）
MAX_FOOD_SCAN_IMAGES = 10     # 自動取り込み 1 回あたりの上限
MANUAL_SCAN_LIMIT = 30        # 手動取り込み 1 回あたりの上限
FOOD_INDEX_BATCH = 20         # 「🧠 索引」ボタン 1 回あたりの枚数
BACKUP_KEEP = 7               # 日次バックアップの保持数
_MAX_LOGIN_ATTEMPTS = 5
_LOGIN_COOLDOWN_SECONDS = 60
_AUTO_PUSH_INTERVAL = 60      # 秒

GALLERY_PAGE_SIZE = 60
GALLERY_COLS = 3
_MONTH_LABELS_JA = ["1月", "2月", "3月", "4月", "5月", "6月",
                    "7月", "8月", "9月", "10月", "11月", "12月"]
_WEEKDAY_LABELS_JA = ["月", "火", "水", "木", "金", "土", "日"]

_file_write_lock = threading.Lock()
_auto_push_started = False


# ---------------------------------------------------------------------------
# 認証
# ---------------------------------------------------------------------------
def _make_auth_token(username: str, pw_hash: str) -> str:
    return hmac.new(pw_hash.encode(), username.encode(), "sha256").hexdigest()


def _save_token_to_storage(username: str, token: str) -> None:
    """ブラウザの localStorage にログイントークンを保存する。"""
    import streamlit.components.v1 as components
    safe_token = json.dumps(token)
    safe_user = json.dumps(username)
    components.html(
        f"""<script>
        try {{
            localStorage.setItem('ckb_auth_token', {safe_token});
            localStorage.setItem('ckb_auth_user', {safe_user});
        }} catch(e) {{}}
        </script>""",
        height=0,
    )


def _inject_auto_login_script() -> None:
    """localStorage にトークンがあれば URL パラメータに付けて自動ログイン。"""
    import streamlit.components.v1 as components
    components.html(
        """<script>
        try {
            var token = localStorage.getItem('ckb_auth_token');
            if (token && !window.location.search.includes('token=')) {
                var url = new URL(window.parent.location.href);
                url.searchParams.set('token', token);
                window.parent.location.href = url.toString();
            }
        } catch(e) {}
        </script>""",
        height=0,
    )


def _clear_auth_storage() -> None:
    import streamlit.components.v1 as components
    components.html(
        """<script>
        try {
            localStorage.removeItem('ckb_auth_token');
            localStorage.removeItem('ckb_auth_user');
        } catch(e) {}
        </script>""",
        height=0,
    )


def _save_auth_to_file(username: str, token: str) -> None:
    try:
        _AUTH_STATE_PATH.write_text(json.dumps({"user": username, "token": token}),
                                    encoding="utf-8")
    except OSError:
        pass


def _load_auth_from_file() -> tuple[str, str] | None:
    try:
        if _AUTH_STATE_PATH.exists():
            data = json.loads(_AUTH_STATE_PATH.read_text(encoding="utf-8"))
            u, t = data.get("user", ""), data.get("token", "")
            if u and t:
                return (u, t)
    except (OSError, json.JSONDecodeError):
        pass
    return None


def _clear_auth_file() -> None:
    try:
        _AUTH_STATE_PATH.unlink(missing_ok=True)
    except OSError:
        pass


def _check_auth() -> bool:
    """ログイン認証。認証済みなら True、未認証ならログイン画面を表示して False。"""
    if st.session_state.get("authenticated"):
        return True

    try:
        auth_users = dict(st.secrets["auth"]["users"])
    except (KeyError, FileNotFoundError):
        return True  # 認証設定なし → フリーアクセス

    file_auth = _load_auth_from_file()
    if file_auth:
        f_user, f_token = file_auth
        if f_user in auth_users and f_token == _make_auth_token(f_user, auth_users[f_user]):
            st.session_state["authenticated"] = True
            st.session_state["auth_user"] = f_user
            return True
        _clear_auth_file()

    token = st.query_params.get("token")
    if token:
        for uname, stored_hash in auth_users.items():
            expected_token = _make_auth_token(uname, stored_hash)
            if token == expected_token:
                st.session_state["authenticated"] = True
                st.session_state["auth_user"] = uname
                _save_token_to_storage(uname, expected_token)
                _save_auth_to_file(uname, expected_token)
                try:
                    del st.query_params["token"]
                except (KeyError, AttributeError):
                    pass
                return True
    else:
        _inject_auto_login_script()

    st.markdown("<h1 style='text-align:center; margin-top:60px;'>🐻 Pomken</h1>",
                unsafe_allow_html=True)
    st.markdown("<p style='text-align:center; color:#b0b0b0;'>アクセスするにはログインが必要です</p>",
                unsafe_allow_html=True)
    _, col_form, _ = st.columns([1, 2, 1])
    with col_form:
        with st.form("login_form"):
            username = st.text_input("ユーザー名", placeholder="ユーザー名を入力")
            password = st.text_input("パスワード", type="password", placeholder="パスワードを入力")
            submitted = st.form_submit_button("🔐 ログイン", type="primary", width="stretch")

        if submitted:
            if not username or not password:
                st.error("ユーザー名とパスワードを入力してください。")
                return False
            fail_count = st.session_state.get("_login_fail_count", 0)
            last_fail_time = st.session_state.get("_login_last_fail", 0)
            now = time.time()
            if fail_count >= _MAX_LOGIN_ATTEMPTS:
                remaining = _LOGIN_COOLDOWN_SECONDS - (now - last_fail_time)
                if remaining > 0:
                    st.error(f"ログイン試行回数が上限に達しました。{int(remaining)}秒後に再度お試しください。")
                    return False
                st.session_state["_login_fail_count"] = 0
                fail_count = 0

            pw_hash = hashlib.sha256(password.encode()).hexdigest()
            if username in auth_users and auth_users[username] == pw_hash:
                st.session_state["_login_fail_count"] = 0
                st.session_state["authenticated"] = True
                st.session_state["auth_user"] = username
                auth_token = _make_auth_token(username, pw_hash)
                _save_token_to_storage(username, auth_token)
                _save_auth_to_file(username, auth_token)
                st.rerun()
            else:
                st.session_state["_login_fail_count"] = fail_count + 1
                st.session_state["_login_last_fail"] = now
                remaining_attempts = _MAX_LOGIN_ATTEMPTS - (fail_count + 1)
                if remaining_attempts > 0:
                    st.error(f"ユーザー名またはパスワードが正しくありません。（残り{remaining_attempts}回）")
                else:
                    st.error(f"ログイン試行回数が上限に達しました。{_LOGIN_COOLDOWN_SECONDS}秒後に再度お試しください。")
    return False


def _logout() -> None:
    _clear_auth_storage()
    _clear_auth_file()
    st.session_state["authenticated"] = False
    st.session_state.pop("auth_user", None)
    if "token" in st.query_params:
        del st.query_params["token"]
    st.rerun()


# ---------------------------------------------------------------------------
# ローカル JSON（Sheets 同期なし）
# ---------------------------------------------------------------------------
def _atomic_json_write(path: Path, data) -> bool:
    """JSON をアトミックに書き込む（tmp → rename）。"""
    tmp = path.with_suffix(".tmp")
    try:
        with _file_write_lock:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
                f.flush()
                os.fsync(f.fileno())
            tmp.replace(path)
        return True
    except (OSError, TypeError, ValueError) as e:
        _log.warning(f"ファイル書き込み失敗: {path.name}: {e}")
        try:
            tmp.unlink(missing_ok=True)
        except OSError:
            pass
        return False


def _load_json(path: Path, default):
    if not path.exists():
        return default
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        _log.warning(f"{path.name} 読み込み失敗: {e}")
        return default


def _daily_backup(path: Path) -> None:
    """保存前に 1 日 1 回だけ backups/ にコピーを残す（BACKUP_KEEP 世代）。"""
    try:
        if not path.exists():
            return
        BACKUP_DIR.mkdir(exist_ok=True)
        stamp = date.today().strftime("%Y%m%d")
        dst = BACKUP_DIR / f"{path.stem}-{stamp}{path.suffix}"
        if dst.exists():
            return
        shutil.copy2(path, dst)
        olds = sorted(BACKUP_DIR.glob(f"{path.stem}-*{path.suffix}"))
        for p in olds[:-BACKUP_KEEP]:
            p.unlink(missing_ok=True)
    except OSError as e:
        _log.warning(f"バックアップ失敗 {path.name}: {e}")


def load_weight_data() -> dict:
    """食事写真の台帳を読む。{"records": {日付: {"items": [...]}}} の形。"""
    ck = "_cache_weight_data"
    if ck in st.session_state:
        return st.session_state[ck]
    data = _load_json(WEIGHT_DATA_PATH, {"goals": {}, "records": {}})
    if not isinstance(data, dict):
        data = {"goals": {}, "records": {}}
    data.setdefault("records", {})
    st.session_state[ck] = data
    return data


def save_weight_data(weight_data: dict) -> bool:
    st.session_state["_cache_weight_data"] = weight_data
    _daily_backup(WEIGHT_DATA_PATH)
    return _atomic_json_write(WEIGHT_DATA_PATH, weight_data)


def load_food_processed() -> dict:
    ck = "_cache_food_processed"
    if ck in st.session_state:
        return st.session_state[ck]
    data = _load_json(FOOD_IMAGES_PROCESSED_PATH, {})
    if not isinstance(data, dict):
        data = {}
    st.session_state[ck] = data
    return data


def save_food_processed(data: dict) -> bool:
    st.session_state["_cache_food_processed"] = data
    return _atomic_json_write(FOOD_IMAGES_PROCESSED_PATH, data)


# ---------------------------------------------------------------------------
# Git 自動 push（バックアップ用。ローカル環境のみ）
# ---------------------------------------------------------------------------
def _is_local_env() -> bool:
    if not (ROOT / ".git").exists():
        return False
    try:
        r = subprocess.run(["git", "status"], cwd=str(ROOT),
                           capture_output=True, text=True, timeout=5)
        return r.returncode == 0
    except Exception:
        return False


def _auto_push_loop():
    target_files = [
        "app.py", "food_search.py", "scan_food_images.py", "build_food_search_index.py",
        "requirements.txt", ".gitignore",
        "metadata.json", "weight_data.json", "food_images_processed.json",
        "food_search_index.json",
    ]
    while True:
        time.sleep(_AUTO_PUSH_INTERVAL)
        try:
            with _file_write_lock:
                r = subprocess.run(["git", "status", "--porcelain"] + target_files,
                                   cwd=str(ROOT), capture_output=True, text=True, timeout=15)
                if not r.stdout.strip():
                    continue
                subprocess.run(["git", "add"] + target_files,
                               cwd=str(ROOT), capture_output=True, text=True, timeout=15)
                ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                subprocess.run(["git", "commit", "-m", f"auto: {ts}"],
                               cwd=str(ROOT), capture_output=True, text=True, timeout=30)
            subprocess.run(["git", "push", "origin", "main"],
                           cwd=str(ROOT), capture_output=True, text=True, timeout=60)
        except Exception as e:
            _log.warning(f"[auto_push] エラー: {type(e).__name__}: {e}")


def start_auto_push():
    global _auto_push_started
    if _auto_push_started:
        return
    _auto_push_started = True
    if not _is_local_env():
        return
    threading.Thread(target=_auto_push_loop, daemon=True).start()


# ---------------------------------------------------------------------------
# Google Drive / Gemini
# ---------------------------------------------------------------------------
@st.cache_resource(show_spinner="Google Drive に接続中...")
def get_drive_service():
    try:
        creds = service_account.Credentials.from_service_account_info(
            st.secrets["gcp_service_account"], scopes=SCOPES)
        return build("drive", "v3", credentials=creds)
    except KeyError as e:
        st.error(f"認証情報が見つかりません: {e}\n\n"
                 "`.streamlit/secrets.toml` に `[gcp_service_account]` を設定してください。")
        st.stop()
    except Exception as e:
        _log.error(f"Google Drive 認証失敗: {e}")
        st.error("Google Drive への認証に失敗しました。")
        st.stop()


@st.cache_data(ttl=300, show_spinner=False, max_entries=100)
def download_image(_service, file_id: str) -> bytes:
    """Drive からファイルをダウンロードする（3 回リトライ）。"""
    if not re.match(r"^[a-zA-Z0-9_\-]+$", file_id):
        _log.warning(f"[download_image] 不正な file_id: {file_id!r}")
        return b""
    for attempt in range(3):
        try:
            request = _service.files().get_media(fileId=file_id)
            buffer = io.BytesIO()
            downloader = MediaIoBaseDownload(buffer, request)
            done = False
            while not done:
                _, done = downloader.next_chunk()
            return buffer.getvalue()
        except Exception:
            if attempt < 2:
                time.sleep(2)
                continue
            raise
    return b""


def get_food_folder_id() -> str | None:
    """食事画像フォルダの Drive ID。

    secrets.toml のトップレベル → [gcp_service_account] 内（旧版が末尾に追記したため
    このセクションに入っている）→ folder_id 配下の「食事画像」フォルダ検索、の順で解決。
    """
    cached = st.session_state.get("_food_folder_id_cache")
    if cached:
        return cached
    fid = ""
    try:
        fid = st.secrets.get("food_images_folder_id", "") or ""
        if not fid:
            fid = dict(st.secrets.get("gcp_service_account", {})).get("food_images_folder_id", "") or ""
    except (KeyError, FileNotFoundError):
        fid = ""
    if not fid:
        try:
            parent = st.secrets.get("folder_id", "")
            if parent:
                service = get_drive_service()
                q = (f"'{parent}' in parents and name='食事画像' "
                     f"and mimeType='application/vnd.google-apps.folder' and trashed=false")
                res = service.files().list(q=q, fields="files(id)", pageSize=5).execute()
                files = res.get("files", [])
                if files:
                    fid = files[0]["id"]
        except Exception as e:
            _log.warning(f"食事画像フォルダ検索失敗: {e}")
    if fid:
        st.session_state["_food_folder_id_cache"] = fid
    return fid or None


def get_gemini_api_key() -> str | None:
    try:
        api_key = st.secrets["GOOGLE_API_KEY"]
        if not api_key or api_key == "YOUR_GEMINI_API_KEY":
            return None
        return api_key
    except KeyError:
        return None


# ---------------------------------------------------------------------------
# 画像ユーティリティ
# ---------------------------------------------------------------------------
def _extract_exif_datetime(image_bytes: bytes) -> datetime | None:
    try:
        img = Image.open(io.BytesIO(image_bytes))
        exif = img._getexif()
        if exif is None:
            return None
        for tag_id in (36867, 36868):  # DateTimeOriginal, DateTimeDigitized
            dt_str = exif.get(tag_id)
            if dt_str:
                return datetime.strptime(dt_str, "%Y:%m:%d %H:%M:%S")
    except (AttributeError, ValueError, OSError):
        pass
    return None


def _make_thumb_bytes(raw: bytes, max_px: int = 400, quality: int = 70) -> bytes | None:
    if not raw:
        return None
    try:
        img = Image.open(io.BytesIO(raw))
        img.thumbnail((max_px, max_px))
        buf = io.BytesIO()
        img.convert("RGB").save(buf, format="JPEG", quality=quality, optimize=True)
        return buf.getvalue()
    except Exception:
        return None


def _food_thumb_path(image_id: str) -> Path:
    return THUMB_CACHE_DIR / f"food_{image_id}.jpg"


def _save_food_thumb(image_id: str, raw_bytes: bytes) -> bool:
    cache_path = _food_thumb_path(image_id)
    if cache_path.exists():
        return True
    thumb = _make_thumb_bytes(raw_bytes)
    if not thumb:
        return False
    try:
        THUMB_CACHE_DIR.mkdir(exist_ok=True)
        cache_path.write_bytes(thumb)
        return True
    except Exception:
        return False


@st.cache_data(ttl=86400, show_spinner=False, max_entries=2000)
def _load_food_thumbnail_bytes(image_id: str, ext: str, drive_file_id: str = "") -> bytes | None:
    """サムネ（最大 400px JPEG）。ディスクキャッシュ → ローカル原本 → Drive の順。"""
    cache_path = _food_thumb_path(image_id)
    if cache_path.exists():
        try:
            return cache_path.read_bytes()
        except Exception:
            pass
    raw = _load_food_full_bytes(image_id, ext, drive_file_id)
    if not raw:
        return None
    thumb = _make_thumb_bytes(raw)
    if thumb:
        try:
            THUMB_CACHE_DIR.mkdir(exist_ok=True)
            cache_path.write_bytes(thumb)
        except Exception:
            pass
        return thumb
    return raw


def _load_food_full_bytes(image_id: str, ext: str, drive_file_id: str = "") -> bytes | None:
    img_path = WEIGHT_UPLOADS_DIR / f"{image_id}.{ext}"
    if img_path.exists():
        return img_path.read_bytes()
    if drive_file_id:
        try:
            service = get_drive_service()
            if service:
                return download_image(service, drive_file_id)
        except Exception:
            pass
    return None


# ---------------------------------------------------------------------------
# 取り込み（Drive の食事画像フォルダ → ローカル + 索引）
# ---------------------------------------------------------------------------
def scan_food_images(service, food_folder_id: str, api_key: str | None = None,
                     manual: bool = False) -> int:
    if st.session_state.get("_food_scan_running"):
        return 0
    st.session_state["_food_scan_running"] = True
    try:
        return _scan_food_images_inner(service, food_folder_id, manual, api_key)
    finally:
        st.session_state["_food_scan_running"] = False


def _list_food_drive_files(service, food_folder_id: str) -> list[dict]:
    mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
    query = f"'{food_folder_id}' in parents and ({mime_query}) and trashed=false"
    files: list[dict] = []
    page_token = None
    while True:
        params = dict(q=query, orderBy="modifiedTime desc", pageSize=100,
                      fields="nextPageToken, files(id, name, mimeType, createdTime, modifiedTime)")
        if page_token:
            params["pageToken"] = page_token
        results = service.files().list(**params).execute()
        files.extend(results.get("files", []))
        page_token = results.get("nextPageToken")
        if not page_token:
            break
    return files


def _scan_food_images_inner(service, food_folder_id: str, manual: bool,
                            api_key: str | None) -> int:
    if not manual:
        now = time.time()
        if now - st.session_state.get("food_scan_last", 0) < FOOD_SCAN_INTERVAL:
            return 0
        st.session_state["food_scan_last"] = now

    processed = load_food_processed()
    try:
        all_files = _list_food_drive_files(service, food_folder_id)
    except Exception as e:
        _log.error(f"Google Drive 読み取り失敗: {e}")
        if manual:
            st.error("Google Drive の読み取りに失敗しました。")
        return 0

    new_files = [f for f in all_files if f["id"] not in processed]
    if not new_files:
        return 0
    total_candidates = len(new_files)
    new_files = new_files[:MANUAL_SCAN_LIMIT if manual else MAX_FOOD_SCAN_IMAGES]

    weight_data = load_weight_data()
    records = weight_data.setdefault("records", {})

    progress = progress_text = None
    if manual:
        progress_text = st.empty()
        progress = st.progress(0.0)
        progress_text.caption(f"📷 {len(new_files)} / {total_candidates} 枚を処理中…")

    count = 0
    for idx, file_info in enumerate(new_files):
        if progress is not None:
            progress.progress(idx / max(len(new_files), 1))
        file_id = file_info["id"]
        file_name = file_info.get("name", file_id)
        try:
            img_bytes = download_image(service, file_id)
            if not img_bytes:
                continue

            photo_dt = _extract_exif_datetime(img_bytes)
            if photo_dt is None:
                mod = file_info.get("modifiedTime", "")
                if mod:
                    try:
                        photo_dt = datetime.fromisoformat(mod.replace("Z", "+00:00"))
                    except (ValueError, TypeError):
                        pass
            if photo_dt is None:
                photo_dt = datetime.now()
            date_key = photo_dt.strftime("%Y-%m-%d")

            WEIGHT_UPLOADS_DIR.mkdir(exist_ok=True)
            img_id = f"wm_{uuid.uuid4().hex[:12]}"
            ext = file_name.rsplit(".", 1)[-1].lower() if "." in file_name else "png"
            if ext not in ("jpg", "jpeg", "png"):
                ext = "png"
            (WEIGHT_UPLOADS_DIR / f"{img_id}.{ext}").write_bytes(img_bytes)
            _save_food_thumb(img_id, img_bytes)

            day_data = records.setdefault(date_key, {"items": []})
            existing_fids = {x.get("drive_file_id") for x in day_data.get("items", [])}
            if file_id not in existing_fids:
                item_names: list[str] = []
                if api_key:
                    try:
                        ix_entry = _fs.index_image(img_id, img_bytes, api_key)
                    except Exception as ix_err:
                        _log.warning(f"[food index] {img_id} 失敗: {ix_err}")
                        ix_entry = None
                    if ix_entry and ix_entry.get("items"):
                        item_names = list(ix_entry["items"])
                day_data.setdefault("items", []).append({
                    "id": f"item_{uuid.uuid4().hex[:12]}",
                    "name": "・".join(item_names) if item_names else file_name,
                    "items_extracted": item_names,
                    "image_id": img_id,
                    "image_ext": ext,
                    "drive_file_id": file_id,
                })
                count += 1

            processed[file_id] = {"date": date_key, "file_name": file_name,
                                  "processed_at": datetime.now().isoformat(), "status": "ok"}
        except Exception as e:
            _log.error(f"ファイル処理失敗 {file_name}: {e}")
            if manual:
                st.warning(f"⚠️ {html.escape(file_name)} の処理に失敗しました。")
            processed[file_id] = {"date": "", "file_name": file_name,
                                  "processed_at": datetime.now().isoformat(),
                                  "status": "error", "error": str(e)}

    if count > 0:
        save_weight_data(weight_data)
        try:
            _load_food_index_cached.clear()
        except Exception:
            pass
    save_food_processed(processed)

    if progress is not None:
        progress.empty()
    if progress_text is not None:
        if total_candidates > len(new_files):
            progress_text.info(f"✅ {len(new_files)} 枚を処理しました"
                               f"（残り {total_candidates - len(new_files)} 枚は次回クリックで処理）")
        else:
            progress_text.empty()
    return count


# ---------------------------------------------------------------------------
# 検索索引
# ---------------------------------------------------------------------------
@st.cache_data(show_spinner=False)
def _load_food_index_cached(mtimes: tuple[float, float]):
    """索引（説明文 + 埋め込み）をファイル更新時刻をキーに読み込む。
    引数名にアンダースコアを付けるとキャッシュキーから外れるので付けない。"""
    index = _fs.load_index()
    ids, mat = _fs.load_embeddings()
    return index, ids, mat


def _get_food_index():
    return _load_food_index_cached(_fs.file_mtimes())


_FILENAME_RE = re.compile(r"\.(jpe?g|png|heic)$", re.IGNORECASE)


def _build_food_entries(weight_data: dict, index: dict | None = None) -> list[dict]:
    """食事画像のエントリを日付降順で返す。同じ image_id の行は 1 枚にまとめる。"""
    index = index or {}
    entries: list[dict] = []
    records = weight_data.get("records", {}) or {}
    for date_key in sorted(records.keys(), reverse=True):
        day = records[date_key] or {}
        grouped: dict[str, dict] = {}
        order: list[str] = []
        for it in day.get("items", []) or []:
            iid = it.get("image_id")
            if not iid:
                continue
            if iid not in grouped:
                grouped[iid] = {"ext": it.get("image_ext", "jpg"),
                                "drive_file_id": it.get("drive_file_id", ""),
                                "names": [], "extras": []}
                order.append(iid)
            g = grouped[iid]
            name = it.get("name", "")
            name = name if isinstance(name, str) else str(name or "")
            if name and name not in g["names"]:
                g["names"].append(name)
            for x in it.get("items_extracted") or []:
                sx = str(x)
                if sx and sx not in g["extras"]:
                    g["extras"].append(sx)

        for iid in order:
            g = grouped[iid]
            items_extracted = g["names"] + [x for x in g["extras"] if x not in g["names"]]
            ix = index.get(iid) or {}
            real_names = [x for x in items_extracted if not _FILENAME_RE.search(x)]
            # 「品目なし」: 取り込み時の品目が無い、または索引で品目が空と判定された画像
            no_items = (not real_names) or (bool(ix) and not ix.get("items"))
            if not real_names and ix.get("items"):
                real_names = [str(x) for x in ix["items"] if x]
                items_extracted = real_names + [x for x in items_extracted if x not in real_names]
            if real_names:
                title = real_names[0]
            elif ix.get("description"):
                title = str(ix["description"])[:40]
            else:
                title = items_extracted[0] if items_extracted else ""
            search_text = _fs.normalize_text(" ".join(items_extracted))
            if ix.get("search_text"):
                search_text = f"{ix['search_text']} {search_text}"
            entries.append({
                "fid": iid, "ext": g["ext"], "drive_file_id": g["drive_file_id"],
                "ts": date_key, "title": title, "items_extracted": items_extracted,
                "search_text": search_text, "desc": ix.get("description", ""),
                "indexed": bool(ix.get("search_text")), "no_items": no_items,
            })
    return entries


def _food_hybrid_search(entries: list[dict], query: str, api_key: str | None) -> dict:
    """キーワード直接一致（AND）+ 意味検索（埋め込み候補 → Gemini 判定）。

    特別キーワード: 「品目なし」= 品目が取れなかった画像、「未索引」= 説明文索引が無い画像。
    """
    special = {"品目なし": "no_items", "品目無し": "no_items", "未索引": "unindexed"}
    q_tokens = [t for t in (query or "").split() if t]
    flags = {special[t] for t in q_tokens if t in special}
    rest = " ".join(t for t in q_tokens if t not in special)
    if "no_items" in flags:
        entries = [e for e in entries if e.get("no_items")]
    if "unindexed" in flags:
        entries = [e for e in entries if not e.get("indexed")]
    if flags and not rest.strip():
        return {"keyword": entries, "semantic": [], "semantic_ok": False}
    query = rest

    groups = _fs.keyword_groups(query, api_key, expand=False)
    kw: list[dict] = []
    for e in entries:
        text = e.get("search_text", "")
        if _fs.keyword_match(text, groups):
            e2 = dict(e)
            # どの語で一致したかをカードに出す（グループごとに最初に当たった語）
            e2["matched"] = [next(t for t in sorted(g) if t in text) for g in groups]
            kw.append(e2)
    kw_ids = {e["fid"] for e in kw}

    sem: list[dict] = []
    semantic_ok = False
    index, ids, mat = _get_food_index()
    if api_key and len(ids) and query.strip():
        qv = _fs.cached_query_embedding(query, api_key)
        if qv is not None:
            semantic_ok = True
            scores = _fs.semantic_scores(qv, ids, mat)
            by_id = {e["fid"]: e for e in entries}
            cands = [(iid, sc) for iid, sc in _fs.select_candidates(scores, exclude=kw_ids)
                     if iid in by_id]
            picked = _fs.rerank_with_llm(
                query, [(iid, (index.get(iid) or {}).get("embed_text", "")) for iid, _ in cands],
                api_key)
            keep = set(picked) if picked is not None else {iid for iid, _ in cands}
            for iid, sc in cands:
                if iid in keep:
                    e2 = dict(by_id[iid])
                    e2["score"] = sc
                    sem.append(e2)
    return {"keyword": kw, "semantic": sem, "semantic_ok": semantic_ok}


def _run_food_index_batch(entries: list[dict], api_key: str) -> int:
    """未索引の食事画像を FOOD_INDEX_BATCH 枚まで説明文化・埋め込みする。"""
    targets = [e for e in entries if not e.get("indexed")][:FOOD_INDEX_BATCH]
    if not targets:
        return 0
    index = _fs.load_index()
    pending: dict = {}
    prog_text = st.empty()
    prog = st.progress(0.0)
    done = 0
    for i, e in enumerate(targets):
        prog.progress(i / len(targets))
        prog_text.caption(f"🧠 {i + 1} / {len(targets)} 枚を説明文化中…")
        raw = _load_food_full_bytes(e["fid"], e.get("ext", "jpg"), e.get("drive_file_id", "")) \
            or _load_food_thumbnail_bytes(e["fid"], e.get("ext", "jpg"), e.get("drive_file_id", ""))
        if not raw:
            continue
        try:
            entry = _fs.index_image(e["fid"], raw, api_key,
                                    extra_names=e.get("items_extracted") or [],
                                    index=index, embed=False)
            if entry:
                pending[e["fid"]] = entry
                done += 1
        except _fs.GeminiRateLimited:
            st.warning("⚠️ Gemini のレート制限に達しました。しばらくしてから再実行してください。")
            break
        except Exception as ex:
            _log.warning(f"[food index] {e['fid']} 失敗: {ex}")
        time.sleep(0.5)
    index = _fs.merge_save_index(pending)
    try:
        _fs.embed_pending(index, api_key)
    except Exception as ex:
        _log.warning(f"[food index] 埋め込み失敗: {ex}")
    prog.empty()
    prog_text.empty()
    if done:
        st.toast(f"🧠 {done} 枚を索引に追加しました", icon="🧠")
    return done


# ---------------------------------------------------------------------------
# ギャラリー UI
# ---------------------------------------------------------------------------
def _inject_gallery_css():
    st.markdown("""
    <style>
    .g-month {
        position: sticky; top: 0; z-index: 10;
        background: rgba(15,15,20,0.95); backdrop-filter: blur(6px);
        padding: 10px 4px 6px; font-size: 18px; font-weight: 700;
        color: #e0e0e0; border-bottom: 1px solid #333; margin: 12px 0 4px;
    }
    .g-day { font-size: 13px; color: #b0b0b0; padding: 8px 4px 4px; font-weight: 500; }
    .g-empty { text-align: center; padding: 60px 20px; color: #888; font-size: 14px; }
    .g-placeholder {
        aspect-ratio: 1/1; background: #2a2a2a; border-radius: 4px;
        display: flex; align-items: center; justify-content: center;
        color: #888; font-size: 24px;
    }
    .g-caption {
        font-size: 11px; color: #d0d0d0; padding: 2px 4px 0; margin-top: 2px;
        line-height: 1.35; max-height: 5.4em; overflow: hidden;
        display: -webkit-box; -webkit-line-clamp: 4; -webkit-box-orient: vertical;
        word-break: break-word;
    }
    .g-caption-top { margin-top: 4px; }
    .g-day-card { padding: 4px 4px 2px; font-size: 13px; font-weight: 600; color: #e0e0e0; }
    .g-day-card .g-day-year { font-size: 11px; font-weight: 400; color: #999; margin-left: 6px; }
    .g-caption .g-chip-date { background: rgba(255,255,255,0.10); color: #e0e0e0; }
    .g-caption .g-chip-hit { background: rgba(72,199,116,0.18); color: #7ee2a1; font-weight: 600; }
    .g-caption .g-chip-rel { background: rgba(80,160,255,0.18); color: #9cc7ff; font-weight: 600; }
    .g-caption .g-chip {
        display: inline-block; margin: 1px 3px 1px 0; padding: 1px 6px;
        border-radius: 8px; background: rgba(255,122,60,0.15);
        color: #ffb27a; font-size: 10.5px; white-space: nowrap;
    }
    [data-testid="stHorizontalBlock"] { gap: 4px !important; }
    [data-testid="column"] { padding: 0 2px !important; }
    [data-testid="stHorizontalBlock"] [data-testid="stImage"] img {
        aspect-ratio: 1/1; object-fit: contain; background: #1a1a1a; border-radius: 4px;
    }
    @media (max-width: 600px) {
        [data-testid="stHorizontalBlock"] { flex-wrap: wrap !important; }
        [data-testid="column"] { flex: 0 0 50% !important; max-width: 50% !important; }
    }
    @media (min-width: 1200px) {
        [data-testid="column"] { flex: 0 0 25% !important; max-width: 25% !important; }
    }
    </style>
    """, unsafe_allow_html=True)


def _fmt_month(ts_month: str) -> str:
    if not ts_month or len(ts_month) < 7:
        return "日付不明"
    try:
        return f"{ts_month[:4]}年 {_MONTH_LABELS_JA[int(ts_month[5:7]) - 1]}"
    except (ValueError, IndexError):
        return ts_month


def _fmt_day(ts_day: str) -> str:
    if not ts_day or len(ts_day) < 10:
        return "日付不明"
    try:
        d = datetime.strptime(ts_day[:10], "%Y-%m-%d").date()
        return f"{d.month}月{d.day}日 ({_WEEKDAY_LABELS_JA[d.weekday()]})"
    except ValueError:
        return ts_day


def _render_food_reanalyze(entry: dict, img_bytes: bytes | None) -> None:
    """拡大画面: 索引の品目・説明文を表示し、ヒント付きで再解析できる。"""
    fid = entry["fid"]
    index, _, _ = _get_food_index()
    ix = index.get(fid) or {}
    if ix.get("items"):
        chips = "".join(f'<span class="g-chip">{html.escape(str(x))}</span>' for x in ix["items"])
        st.markdown(f'<div class="g-caption">🧠 {chips}</div>', unsafe_allow_html=True)
    if ix.get("description"):
        st.markdown(f"🧠 {html.escape(str(ix['description']))}")
    if ix.get("hint"):
        st.caption(f"補足として「{ix['hint']}」を使って解析")
    elif not ix:
        st.caption("この写真はまだ説明文の索引がありません。")

    with st.expander("🔁 再解析（読み取れなかったときはヒントを添えて）", expanded=not ix.get("items")):
        with st.form(f"reanalyze_{fid}", clear_on_submit=False):
            hint = st.text_input("ヒント（任意）", value=ix.get("hint", ""), key=f"dlg_hint_{fid}",
                                 placeholder="例: ビニール袋に入った食べ物です / 手前は自作の弁当")
            go = st.form_submit_button("🔁 この写真を再解析", type="primary", use_container_width=True)
        if go:
            api_key = get_gemini_api_key()
            if not api_key:
                st.warning("Gemini API キーが設定されていません。")
                return
            raw = img_bytes or _load_food_thumbnail_bytes(fid, entry.get("ext", "jpg"),
                                                          entry.get("drive_file_id", ""))
            if not raw:
                st.warning("画像を読み込めませんでした。")
                return
            with st.spinner("再解析中…"):
                try:
                    new = _fs.index_image(fid, raw, api_key,
                                          extra_names=entry.get("items_extracted") or [], hint=hint)
                except Exception as e:
                    _log.warning(f"[reanalyze] {fid} 失敗: {e}")
                    new = None
            if new is None:
                st.error("再解析に失敗しました。時間をおいて再試行してください。")
                return
            try:
                _load_food_index_cached.clear()
            except Exception:
                pass
            st.toast(f"🧠 再解析しました: {'、'.join(new.get('items') or []) or '（品目なし）'}", icon="🧠")
            st.rerun()


@st.dialog("画像", width="large")
def _open_photo_dialog(entry: dict):
    img_bytes = _load_food_full_bytes(entry["fid"], entry.get("ext", "jpg"),
                                      entry.get("drive_file_id", ""))
    if img_bytes:
        st.image(img_bytes, use_container_width=True)
    else:
        st.warning("画像の読み込みに失敗しました。")
    if entry.get("ts"):
        st.caption(entry["ts"][:10])
    _render_food_reanalyze(entry, img_bytes)


def _render_photo_gallery(entries: list[dict], key_prefix: str, fetch_thumb_fn,
                          group_by_date: bool = True) -> None:
    """日付グループ化された写真グリッド。group_by_date=False は渡された順（類似度順）。"""
    if not entries:
        st.markdown('<div class="g-empty">画像がまだありません。</div>', unsafe_allow_html=True)
        return

    state_key = f"{key_prefix}_loaded"
    loaded = min(st.session_state.get(state_key, GALLERY_PAGE_SIZE), len(entries))
    visible = entries[:loaded]

    # 検索結果（一致 / 関連）は日付が飛び飛びなので、行見出しではなく各カードの上に日付を出す
    search_mode = any(("matched" in e) or ("score" in e) for e in visible[:1])

    if search_mode or not group_by_date:
        rows = [visible[i:i + GALLERY_COLS] for i in range(0, len(visible), GALLERY_COLS)]
    else:
        # 通常表示: 日付が変わるところで行を折り返し、行見出しが常に全画像に当てはまるようにする
        rows = []
        cur: list[dict] = []
        for e in visible:
            if cur and ((e.get("ts") or "")[:10] != (cur[0].get("ts") or "")[:10]
                        or len(cur) >= GALLERY_COLS):
                rows.append(cur)
                cur = []
            cur.append(e)
        if cur:
            rows.append(cur)

    cur_month = cur_day = None
    for row in rows:
        if group_by_date and not search_mode:
            ts = row[0].get("ts") or ""
            m, d = ts[:7], ts[:10]
            if m != cur_month:
                cur_month = m
                st.markdown(f'<div class="g-month">{_fmt_month(m)}</div>', unsafe_allow_html=True)
            if d != cur_day:
                cur_day = d
                st.markdown(f'<div class="g-day">{_fmt_day(d)}</div>', unsafe_allow_html=True)
        cols = st.columns(GALLERY_COLS)
        for ci, e in enumerate(row):
            with cols[ci]:
                if search_mode and e.get("ts"):
                    st.markdown(f'<div class="g-day g-day-card">{_fmt_day(e["ts"][:10])}'
                                f'<span class="g-day-year">{html.escape(e["ts"][:4])}年</span></div>',
                                unsafe_allow_html=True)
                try:
                    thumb = fetch_thumb_fn(e)
                except Exception:
                    thumb = None
                if thumb:
                    st.image(thumb, use_container_width=True)
                else:
                    st.markdown('<div class="g-placeholder">🖼️</div>', unsafe_allow_html=True)

                items_ext = [x for x in (e.get("items_extracted") or [])
                             if not _FILENAME_RE.search(str(x))]
                # 検索中: 全カードに「日付 + 一致した語 / 関連」の 1 行目を必ず出す
                if e.get("matched") or "score" in e:
                    date_chip = ""
                    if e.get("matched"):
                        label = ('<span class="g-chip g-chip-hit">✅ 一致: '
                                 + html.escape(" ".join(e["matched"])) + "</span>")
                    else:
                        label = '<span class="g-chip g-chip-rel">🔎 関連（説明文が近い）</span>'
                    st.markdown(f'<div class="g-caption g-caption-top">{date_chip}{label}</div>',
                                unsafe_allow_html=True)
                if e.get("desc") and (not items_ext or e.get("no_items")):
                    # 索引が「品目なし」と判定した写真は旧タグより説明文を優先
                    st.markdown(f'<div class="g-caption">🧠 {html.escape(str(e["desc"])[:60])}</div>',
                                unsafe_allow_html=True)
                elif items_ext:
                    chips = "".join(f'<span class="g-chip">{html.escape(str(x))}</span>'
                                    for x in items_ext)
                    st.markdown(f'<div class="g-caption">{chips}</div>', unsafe_allow_html=True)
                elif e.get("title"):
                    st.markdown(f'<div class="g-caption">{html.escape(e["title"])}</div>',
                                unsafe_allow_html=True)
                if st.button("🔍", key=f"{key_prefix}_btn_{e['fid']}",
                             use_container_width=True, help="拡大表示"):
                    _open_photo_dialog(e)

    if loaded < len(entries):
        if st.button(f"もっと見る ({loaded} / {len(entries)})", key=f"{key_prefix}_more",
                     use_container_width=True, type="primary"):
            st.session_state[state_key] = loaded + GALLERY_PAGE_SIZE
            st.rerun()


def page_food_gallery():
    _inject_gallery_css()
    st.markdown("## 🍽️ 食事")

    weight_data = load_weight_data()
    index, _ids, _mat = _get_food_index()
    entries = _build_food_entries(weight_data, index)
    api_key = get_gemini_api_key()

    q_left, q_right = st.columns([5, 1])
    with q_left:
        query = st.text_input(
            "🔍 品目・カテゴリ・雰囲気で検索", key="food_gal_search",
            placeholder="例: 揚げ物 / 麺 野菜 / コンビニの夜食 / さっぱりしたもの",
            help=("スペース区切りは AND 検索（例: 「肉 野菜」）。"
                  "キーワードで外れても、説明文の意味が近い画像は「関連」として下に表示されます。"
                  "「品目なし」で品目が取れなかった画像、「未索引」で説明文がまだ無い画像を一覧できます。"),
            label_visibility="collapsed",
        )
    n_unindexed = sum(1 for e in entries if not e.get("indexed"))
    with q_right:
        if n_unindexed and api_key:
            if st.button(f"🧠 索引 +{min(n_unindexed, FOOD_INDEX_BATCH)}", key="food_gal_index",
                         help=f"未索引 {n_unindexed} 枚のうち {FOOD_INDEX_BATCH} 枚を説明文化する",
                         use_container_width=True):
                _run_food_index_batch(entries, api_key)
                st.rerun()

    def _fetch(e):
        return _load_food_thumbnail_bytes(e["fid"], e.get("ext", "jpg"), e.get("drive_file_id", ""))

    if not query:
        cap = f"全 {len(entries)} 件"
        if n_unindexed:
            cap += f"（説明文つき索引: {len(entries) - n_unindexed} / {len(entries)}）"
        st.caption(cap)
        _render_photo_gallery(entries, "food_gal", _fetch)
        return

    with st.spinner("検索中..."):
        res = _food_hybrid_search(entries, query, api_key)
    kw, sem = res["keyword"], res["semantic"]
    cap = f"🔍 「{query}」: 一致 {len(kw)} 件"
    if res["semantic_ok"]:
        cap += f" ＋ 関連 {len(sem)} 件"
    elif not len(_ids):
        cap += "（意味検索は索引作成後に有効）"
    st.caption(cap)

    if kw:
        st.markdown(f'<div class="g-month">✅ 一致した画像（{len(kw)} 件・日付順）</div>',
                    unsafe_allow_html=True)
        _render_photo_gallery(kw, "food_gal", _fetch)
    elif not sem:
        st.markdown('<div class="g-empty">一致する画像がありません。</div>', unsafe_allow_html=True)
    if sem:
        st.markdown(f'<div class="g-month">🔎 関連しそうな画像（{len(sem)} 件・類似度順）'
                    f'<span style="font-size:12px;font-weight:400;color:#9cc7ff;margin-left:8px">'
                    f'キーワードは含まないが説明文の意味が近い写真</span></div>',
                    unsafe_allow_html=True)
        _render_photo_gallery(sem, "food_gal_rel", _fetch, group_by_date=False)


# ---------------------------------------------------------------------------
# 設定
# ---------------------------------------------------------------------------
def page_settings():
    st.markdown("## ⚙️ 設定")

    auto_val = st.toggle("自動取り込み（開いている間、5 分ごとに Drive の新着写真を取り込む）",
                         value=st.session_state.get("auto_scan_enabled", True),
                         key="auto_scan_toggle_settings")
    st.session_state["auto_scan_enabled"] = auto_val

    weight_data = load_weight_data()
    index, ids, _ = _get_food_index()
    n_images = sum(1 for d in weight_data.get("records", {}).values()
                   for it in (d or {}).get("items", []) if it.get("image_id"))
    n_img_unique = len({it.get("image_id") for d in weight_data.get("records", {}).values()
                        for it in (d or {}).get("items", []) if it.get("image_id")})
    st.caption(f"📷 写真 {n_img_unique} 枚 ／ 🧠 説明文つき索引 {len(index)} 枚 ／ 意味検索 {len(ids)} 枚")
    if not get_food_folder_id():
        st.warning("secrets.toml に food_images_folder_id が設定されていません。取り込みは動きません。")
    if not get_gemini_api_key():
        st.warning("secrets.toml に GOOGLE_API_KEY が設定されていません。説明文と検索の一部が動きません。")

    auth_user = st.session_state.get("auth_user")
    if auth_user:
        st.caption(f"👤 {auth_user}")

    st.markdown("---")
    if st.button("🔄 今すぐ取り込み（手動）", key="manual_scan_settings", width="stretch"):
        st.session_state["manual_scan_running"] = True
        st.rerun()
    st.caption("PC を閉じている間は、Windows のタスク pomken_food_scan が同じ取り込みを定期実行します。")

    with st.expander("🔧 詳細"):
        st.caption("データはすべてローカル JSON（weight_data.json / food_search_index.json）。"
                   "保存時に backups/ へ日次コピー、60 秒ごとに GitHub へ自動 push。")
        if st.button("🧹 サムネのメモリキャッシュを消す", key="clear_thumb_cache", width="stretch"):
            _load_food_thumbnail_bytes.clear()
            st.toast("🧹 クリアしました")
        if auth_user and st.button("🚪 ログアウト", key="sys_logout", width="stretch"):
            _logout()


# ---------------------------------------------------------------------------
# メイン
# ---------------------------------------------------------------------------
TAB_FOOD = "🍽️ 食事"
TAB_SETTINGS = "⚙️ 設定"
TAB_NAMES = [TAB_FOOD, TAB_SETTINGS]


def main():
    st.set_page_config(page_title="Pomken", page_icon="🐻", layout="wide",
                       initial_sidebar_state="collapsed")
    if not _check_auth():
        return
    start_auto_push()

    st.markdown(
        "<link href='https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700&display=swap' rel='stylesheet'>",
        unsafe_allow_html=True)
    st.markdown("""<style>
    .loading-banner {
        background: linear-gradient(90deg, #FF6B35, #F7931E);
        color: white; padding: 14px 20px; border-radius: 10px;
        font-size: 17px; font-weight: bold; text-align: center;
        animation: loading-pulse 1.5s ease-in-out infinite;
        margin-bottom: 12px; box-shadow: 0 2px 12px rgba(255,107,53,0.3);
    }
    @keyframes loading-pulse { 0%,100%{opacity:1;} 50%{opacity:0.65;} }
    </style>""", unsafe_allow_html=True)

    if st.session_state.get("active_tab") not in TAB_NAMES:
        st.session_state["active_tab"] = TAB_FOOD

    home_clicked = st.button("🐻 Pomken", key="home_btn")
    st.markdown("""<style>
        div[data-testid="stMainBlockContainer"] > div:nth-child(2) button {
            font-family: 'Playfair Display', serif !important;
            font-size: 28px !important; font-weight: 700 !important;
            border: none !important; padding: 4px 0 !important;
            background: transparent !important; box-shadow: none !important;
            color: inherit !important; cursor: pointer !important;
        }
        div[data-testid="stMainBlockContainer"] > div:nth-child(2) button:hover { opacity: 0.7; }
        </style>""", unsafe_allow_html=True)
    if home_clicked:
        st.session_state["active_tab"] = TAB_FOOD
        st.session_state.pop("food_gal_loaded", None)
        st.session_state.pop("food_gal_rel_loaded", None)
        st.rerun()

    _TABNAV_SCOPE = ('[data-testid="stElementContainer"]:has(.pomken-tabnav-anchor) '
                     '+ [data-testid="stElementContainer"]')
    _css_tpl = """<style>
__SCOPE__ [data-testid="stHorizontalBlock"] { background: rgba(255,255,255,0.04); border: 1px solid rgba(255,255,255,0.08); border-radius: 14px; padding: 4px !important; gap: 2px !important; margin: 6px 0 22px !important; backdrop-filter: blur(6px); }
__SCOPE__ [data-testid="stColumn"] { padding: 0 !important; }
__SCOPE__ [data-testid="stButton"] { margin: 0 !important; }
__SCOPE__ button { border: none !important; background: transparent !important; border-radius: 10px !important; padding: 10px 4px !important; font-size: 14px !important; font-weight: 500 !important; letter-spacing: 0.01em !important; transition: background 160ms ease, color 160ms ease, transform 120ms ease !important; color: rgba(255,255,255,0.55) !important; box-shadow: none !important; min-height: 0 !important; width: 100% !important; }
__SCOPE__ button:hover { background: rgba(255,255,255,0.06) !important; color: rgba(255,255,255,0.95) !important; transform: none !important; }
__SCOPE__ button:active { transform: scale(0.97) !important; }
__SCOPE__ button[kind="primary"], __SCOPE__ button[kind="primaryFormSubmit"] { background: linear-gradient(135deg, #FF7A3C 0%, #F7931E 100%) !important; color: #fff !important; box-shadow: 0 2px 10px rgba(255,107,53,0.28) !important; font-weight: 600 !important; }
__SCOPE__ button[kind="primary"]:hover { background: linear-gradient(135deg, #FF8A4C 0%, #FFA32E 100%) !important; color: #fff !important; }
</style>
<div class="pomken-tabnav-anchor"></div>"""
    st.markdown(_css_tpl.replace("__SCOPE__", _TABNAV_SCOPE), unsafe_allow_html=True)
    tab_cols = st.columns(len(TAB_NAMES))
    for i, tab_name in enumerate(TAB_NAMES):
        is_active = st.session_state["active_tab"] == tab_name
        if tab_cols[i].button(tab_name, key=f"tab_btn_{tab_name}", width="stretch",
                              type="primary" if is_active else "secondary"):
            st.session_state["active_tab"] = tab_name
            st.rerun()

    # コールドスタート直後は自動取り込みを走らせない（起動を軽くする）
    if "_cold_start_done" not in st.session_state:
        st.session_state["_cold_start_done"] = True
        st.session_state["food_scan_last"] = time.time()
    if "auto_scan_enabled" not in st.session_state:
        st.session_state["auto_scan_enabled"] = True

    # 手動取り込み
    if st.session_state.pop("manual_scan_running", False):
        banner = st.empty()
        banner.markdown('<div class="loading-banner">🔄 取り込み中です… しばらくお待ちください</div>',
                        unsafe_allow_html=True)
        try:
            fid = get_food_folder_id()
            if fid:
                n = scan_food_images(get_drive_service(), fid, api_key=get_gemini_api_key(), manual=True)
                st.toast(f"🍽️ 食事 {n} 枚を取り込みました" if n else "新しい写真はありませんでした",
                         icon="🍽️")
            else:
                st.warning("food_images_folder_id が未設定です。")
        except Exception as e:
            _log.error(f"[手動取り込み] {type(e).__name__}: {e}")
            st.warning("⚠️ 取り込み中にエラーが発生しました。")
        finally:
            banner.empty()
        st.session_state["food_scan_last"] = time.time()
    # 自動取り込み（5 分間隔）
    elif st.session_state.get("auto_scan_enabled", True):
        try:
            fid = get_food_folder_id()
            if fid:
                n = scan_food_images(get_drive_service(), fid, api_key=get_gemini_api_key())
                if n > 0:
                    st.toast(f"🔔 食事 {n} 枚を自動取り込みしました", icon="📷")
                    st.rerun()
        except Exception as e:
            _log.error(f"[自動取り込み] {type(e).__name__}: {e}")

    if st.session_state["active_tab"] == TAB_SETTINGS:
        page_settings()
    else:
        page_food_gallery()


if __name__ == "__main__":
    main()

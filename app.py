"""
Pomken - Phase 4: チャット検索(Q&A)付き画像ビューワー

Google Driveの指定フォルダ内にある医療関連スクリーンショットを
ブラウザ上で閲覧し、Gemini 2.0 Flash で内容を自動解析する。
解析結果はユーザー（医師）が手動で修正・追記し、確定情報として保存できる。
蓄積された知識に対して、チャット形式で自然言語による質問・検索が可能。

認証方式: Google サービスアカウント (Drive API)
AI解析/チャット: Gemini 2.0 Flash (REST API)
"""

# --- glibc malloc arena 制限（pyarrow malloc corruption 対策） ---
import os as _os
_os.environ.setdefault("MALLOC_ARENA_MAX", "2")

import base64
import copy
import hashlib
import hmac
import html
import io
import json
import logging
import random
import re
import subprocess
import threading
import time
import uuid
from datetime import datetime, date, timedelta
from pathlib import Path

import requests
import streamlit as st
from PIL import Image
from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload
from googleapiclient.errors import HttpError
import gspread

# デバッグログ設定
_LOG_PATH = Path(__file__).parent / "app_debug.log"
logging.basicConfig(
    filename=str(_LOG_PATH),
    level=logging.INFO,
    format="%(asctime)s %(message)s",
    encoding="utf-8",
)
_log = logging.getLogger("ckb")

# ---------------------------------------------------------------------------
# 定数
# ---------------------------------------------------------------------------
IMAGE_MIME_TYPES = ["image/jpeg", "image/png"]
SCOPES = [
    "https://www.googleapis.com/auth/drive",
    "https://www.googleapis.com/auth/spreadsheets",
]
METADATA_PATH = Path(__file__).parent / "metadata.json"
FOLDERS_PATH = Path(__file__).parent / "folders.json"
UPLOADS_DIR = Path(__file__).parent / "uploads"
WEIGHT_DATA_PATH = Path(__file__).parent / "weight_data.json"
WEIGHT_UPLOADS_DIR = Path(__file__).parent / "weight_uploads"
THUMB_CACHE_DIR = Path(__file__).parent / ".thumb_cache"
OCR_BACKFILL_PENDING_PATH = Path(__file__).parent / ".ocr_backfill_pending.json"
FOOD_IMAGES_PROCESSED_PATH = Path(__file__).parent / "food_images_processed.json"
_AUTH_STATE_PATH = Path(__file__).parent / ".auth_state"
FOOD_SCAN_INTERVAL = 300  # 食事画像スキャン間隔（秒）
MAX_FOOD_SCAN_IMAGES = 10  # 1回のスキャンで処理する最大画像数
_MAX_LOGIN_ATTEMPTS = 5   # ログイン試行上限
_LOGIN_COOLDOWN_SECONDS = 60  # クールダウン秒数
DEFAULT_FOLDER = "未分類"
PATIENT_DATA_FOLDER = "患者データ"
IMAGES_PER_PAGE = 10  # グリッド表示で1ページに表示する画像数
PER_PAGE_OPTIONS = [10, 20, 30]  # 表示件数の選択肢

# ステータス定数
STATUS_AUTO = "auto_generated"
STATUS_REVIEWED = "reviewed"
STATUS_BLOCKED = "blocked"  # Gemini に永続ブロックされ解析できない画像

# ソース識別子
SOURCE_PATIENT_DATA = "patient_data"
SOURCE_UPLOAD = "upload"

# ---------------------------------------------------------------------------
# 認証
# ---------------------------------------------------------------------------
def _validate_file_id(file_id: str) -> str:
    """ファイルIDが安全な文字のみで構成されていることを検証する。
    パストラバーサル防止用。"""
    if not re.match(r'^[a-zA-Z0-9_\-]+$', file_id):
        raise ValueError("Invalid file_id: contains unsafe characters")
    return file_id


def _make_auth_token(username: str, pw_hash: str) -> str:
    """ユーザー名とパスワードハッシュからログイントークンを生成する。"""
    return hmac.new(pw_hash.encode(), username.encode(), "sha256").hexdigest()


def _check_auth() -> bool:
    """ログイン認証。認証済みならTrue、未認証ならログイン画面を表示してFalse。"""
    if st.session_state.get("authenticated"):
        return True

    # secrets.toml に [auth.users] がなければ認証スキップ（開発用）
    try:
        auth_users = dict(st.secrets["auth"]["users"])
    except (KeyError, FileNotFoundError):
        return True  # 認証設定なし → フリーアクセス

    # (1) ファイルベースの認証復元（プライマリ）
    file_auth = _load_auth_from_file()
    if file_auth:
        f_user, f_token = file_auth
        if f_user in auth_users:
            expected = _make_auth_token(f_user, auth_users[f_user])
            if f_token == expected:
                st.session_state["authenticated"] = True
                st.session_state["auth_user"] = f_user
                return True
        _clear_auth_file()  # 無効トークン → 削除

    # (2) URLのquery paramにtokenがあれば自動ログイン
    token = st.query_params.get("token")
    if token:
        for uname, stored_hash in auth_users.items():
            expected_token = _make_auth_token(uname, stored_hash)
            if token == expected_token:
                st.session_state["authenticated"] = True
                st.session_state["auth_user"] = uname
                _save_token_to_storage(uname, expected_token)
                _save_auth_to_file(uname, expected_token)
                # URLからトークンを即削除（履歴・ログへの漏洩防止）
                try:
                    del st.query_params["token"]
                except (KeyError, AttributeError):
                    pass
                return True

    # (3) localStorageからトークンを復元（フォールバック）
    if not token:
        _inject_auto_login_script()

    # ログイン画面
    st.markdown(
        "<h1 style='text-align:center; margin-top:60px;'>🐻 Pomken</h1>",
        unsafe_allow_html=True,
    )
    st.markdown(
        "<p style='text-align:center; color:#b0b0b0;'>アクセスするにはログインが必要です</p>",
        unsafe_allow_html=True,
    )

    # 中央寄せ用カラム
    _, col_form, _ = st.columns([1, 2, 1])
    with col_form:
        with st.form("login_form"):
            username = st.text_input("ユーザー名", placeholder="ユーザー名を入力")
            password = st.text_input("パスワード", type="password", placeholder="パスワードを入力")
            submitted = st.form_submit_button("🔐 ログイン", type="primary", width="stretch")

        if submitted:
            if not username or not password:
                st.error("ユーザー名とパスワードを入力してください。")
            else:
                # --- ログイン試行回数制限 ---
                fail_count = st.session_state.get("_login_fail_count", 0)
                last_fail_time = st.session_state.get("_login_last_fail", 0)
                now = time.time()
                if fail_count >= _MAX_LOGIN_ATTEMPTS:
                    remaining = _LOGIN_COOLDOWN_SECONDS - (now - last_fail_time)
                    if remaining > 0:
                        st.error(f"ログイン試行回数が上限に達しました。{int(remaining)}秒後に再度お試しください。")
                        return False
                    else:
                        st.session_state["_login_fail_count"] = 0
                        fail_count = 0

                pw_hash = hashlib.sha256(password.encode()).hexdigest()
                if username in auth_users and auth_users[username] == pw_hash:
                    st.session_state["_login_fail_count"] = 0
                    st.session_state["authenticated"] = True
                    st.session_state["auth_user"] = username
                    auth_token = _make_auth_token(username, pw_hash)
                    # localStorage + ファイルにトークンを保存
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


def _save_token_to_storage(username: str, token: str) -> None:
    """ブラウザの localStorage にログイントークンを保存する。"""
    import streamlit.components.v1 as components
    # json.dumps で JS 文字列リテラルとして安全にエスケープ（XSS防止）
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
    """localStorage にトークンがあればURLパラメータに付与して自動リダイレクト。"""
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
    """ログアウト時に localStorage のトークンをクリアする。"""
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
    """認証状態をファイルに保存する（サーバーサイド永続化）。"""
    try:
        _AUTH_STATE_PATH.write_text(
            json.dumps({"user": username, "token": token}),
            encoding="utf-8",
        )
    except OSError:
        pass


def _load_auth_from_file() -> tuple[str, str] | None:
    """ファイルから認証状態を読み込む。"""
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
    """ログアウト時に認証状態ファイルを削除する。"""
    try:
        _AUTH_STATE_PATH.unlink(missing_ok=True)
    except OSError:
        pass


# 画像解析プロンプト（タイトル + キーワードのみ。要約は不要）
ANALYSIS_PROMPT = """あなたは臨床経験豊富な専門医レベルの医療アシスタントです。
この画像を解析し、医師が後から検索しやすい形で、以下のJSON形式で出力してください。
JSON以外のテキストは一切含めないでください。

【重要】画像内の言語が英語やその他の言語であっても、出力はすべて日本語に翻訳してください。
専門用語は日本語の医学用語を使用し、必要に応じて括弧内に英語の原語を併記してください。
例: "大腿骨頭壊死（AVN）"、"磁気共鳴画像（MRI）"

{
  "title": "具体的で臨床的に有用なタイトル（疾患名・部位・画像種別を含む、日本語、30〜60文字程度）",
  "keywords": ["疾患名", "解剖学的部位", "画像モダリティ", "臨床所見1", "臨床所見2", "鑑別診断", "関連する検査・治療"]
}

【キーワードの指針】6〜8個を目安に、以下のカテゴリから幅広くタグ付けしてください：
- 疾患名・病態（例: 大腿骨頭壊死、肺塞栓症）
- 解剖学的部位（例: 股関節、右下葉）
- 画像モダリティ（例: MRI T2強調、単純CT）
- 主要所見（例: 骨髄浮腫、すりガラス影）
- 鑑別疾患（例: 化膿性関節炎、関節リウマチ）
- 関連する臨床情報（例: ステロイド内服歴、緊急手術適応）"""

OCR_EXTRACT_PROMPT = """画像内に表示されているすべてのテキストを正確に読み取り、
そのまま改行区切りのプレーンテキストとして出力してください。
図表のラベル、数値、注釈、タイトル等もすべて含めてください。
テキストが存在しない場合は空文字を返してください。
JSON等のフォーマットは不要です。読み取ったテキストのみ出力してください。"""


# ---------------------------------------------------------------------------
# Google Sheets 永続化
# ---------------------------------------------------------------------------
_SHEETS_CHUNK_SIZE = 49000  # 1セル上限50,000文字の安全マージン
_CACHE_TTL = 300  # 5分（save時はキャッシュ直接更新するため再取得間隔のみ影響）

_file_write_lock = threading.Lock()


def _atomic_json_write(path: Path, data) -> bool:
    """JSON をアトミックに書き込む（tmp → rename）。"""
    tmp = path.with_suffix(".tmp")
    try:
        with _file_write_lock:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
                f.flush()
                _os.fsync(f.fileno())
            tmp.replace(path)
        return True
    except (OSError, TypeError, ValueError) as e:
        _log.warning(f"ファイル書き込み失敗: {path.name}: {e}")
        try:
            tmp.unlink(missing_ok=True)
        except OSError:
            pass
        return False


def _new_sheets_connection():
    """gspread クライアントを新規作成して返す。失敗時はNone。"""
    try:
        spreadsheet_id = st.secrets.get("spreadsheet_id", "")
        if not spreadsheet_id:
            _log.info("[Sheets] spreadsheet_id が未設定です")
            st.session_state["_save_error_detail"] = "spreadsheet_id が未設定"
            return None
        creds = service_account.Credentials.from_service_account_info(
            st.secrets["gcp_service_account"],
            scopes=SCOPES,
        )
        gc = gspread.authorize(creds)
        sh = gc.open_by_key(spreadsheet_id)
        _log.info(f"[Sheets] 接続成功: {sh.title}")
        return sh
    except Exception as e:
        err = f"接続失敗: {type(e).__name__}: {e}"
        _log.error(f"[Sheets] {err}")
        st.session_state["_save_error_detail"] = err
        return None


def get_sheets_client():
    """gspread クライアントを取得する。
    rerun内で同じ接続を再利用（TTLキャッシュ）。Noneはキャッシュしない。"""
    ck = "_sheets_conn"
    ts_key = "_sheets_conn_ts"
    if ck in st.session_state and st.session_state[ck] is not None:
        if (time.time() - st.session_state.get(ts_key, 0)) < 60:
            return st.session_state[ck]
    sh = _new_sheets_connection()
    if sh is not None:
        st.session_state[ck] = sh
        st.session_state[ts_key] = time.time()
    return sh


def _read_json_from_sheet(sh, worksheet_name: str):
    """ワークシートのA列を結合してJSONオブジェクトに復元する。"""
    try:
        ws = sh.worksheet(worksheet_name)
        all_values = ws.col_values(1)
        if not all_values:
            _log.info(f"[Sheets] {worksheet_name}: 空です")
            return None
        json_str = "".join(all_values)
        data = json.loads(json_str)
        _log.info(f"[Sheets] {worksheet_name}: 読み込み成功 ({len(json_str)} chars)")
        return data
    except Exception as e:
        _log.error(f"[Sheets] {worksheet_name} 読み込みエラー: {e}")
        return None


def _write_json_to_sheet(sh, worksheet_name: str, data) -> bool:
    """JSONデータをチャンク分割してワークシートに書き込む。
    失敗時は最大3回リトライ（待機時間を段階的に増加）。
    429 (quota) → 長め待機、401/403 (auth) → 接続リセット後リトライ。
    API呼び出し回数を最小化するため batch_update を使用。"""
    last_err = ""
    for attempt in range(3):
        try:
            try:
                ws = sh.worksheet(worksheet_name)
            except gspread.exceptions.WorksheetNotFound:
                ws = sh.add_worksheet(title=worksheet_name, rows=100, cols=1)
                _log.info(f"[Sheets] ワークシート '{worksheet_name}' を自動作成しました")
            json_str = json.dumps(data, ensure_ascii=False)
            chunks = []
            for i in range(0, len(json_str), _SHEETS_CHUNK_SIZE):
                chunks.append(json_str[i:i + _SHEETS_CHUNK_SIZE])
            if not chunks:
                chunks = ["{}"]
            # 行数が足りなければ拡張 (resize + clear + update = 3 API calls)
            needed_rows = len(chunks) + 5
            if ws.row_count < needed_rows:
                ws.resize(rows=needed_rows, cols=max(ws.col_count, 1))
                time.sleep(1)
            ws.clear()
            time.sleep(0.5)
            cells = [gspread.Cell(row=idx + 1, col=1, value=chunk)
                     for idx, chunk in enumerate(chunks)]
            ws.update_cells(cells)
            _log.info(f"[Sheets] {worksheet_name}: 書き込み成功 ({len(json_str)} chars, {len(chunks)} chunks)")
            return True
        except gspread.exceptions.APIError as e:
            status = getattr(e, "response", None)
            status_code = getattr(status, "status_code", 0) if status else 0
            last_err = f"APIError({status_code}): {e}"
            _log.warning(f"[Sheets] {worksheet_name} attempt {attempt+1}: {last_err}")
            if attempt < 2:
                if status_code == 429:
                    # quota超過 → 長めに待つ
                    wait = 10 * (attempt + 1)
                    _log.info(f"[Sheets] 429 quota — {wait}秒待機")
                    time.sleep(wait)
                elif status_code in (401, 403):
                    # 認証エラー → 接続をリセットしてリトライ
                    _log.info("[Sheets] 認証エラー — 接続リセット")
                    st.session_state.pop("_sheets_conn", None)
                    new_sh = _new_sheets_connection()
                    if new_sh is not None:
                        sh = new_sh
                    time.sleep(3)
                else:
                    time.sleep(5 * (attempt + 1))
                continue
            st.session_state["_save_error_detail"] = last_err
            return False
        except Exception as e:
            last_err = f"{type(e).__name__}: {e}"
            _log.warning(f"[Sheets] {worksheet_name} attempt {attempt+1}: {last_err}")
            if attempt < 2:
                time.sleep(5 * (attempt + 1))
                continue
            st.session_state["_save_error_detail"] = last_err
            return False
    st.session_state["_save_error_detail"] = last_err
    return False


def _is_cache_valid(cache_key: str) -> bool:
    """session_state キャッシュが有効（TTL以内）か判定する。"""
    ts_key = f"{cache_key}_ts"
    if cache_key not in st.session_state:
        return False
    if ts_key not in st.session_state:
        return False
    return (time.time() - st.session_state[ts_key]) < _CACHE_TTL


def _set_cache(cache_key: str, data):
    """session_state にデータとタイムスタンプをセットする。"""
    st.session_state[cache_key] = data
    st.session_state[f"{cache_key}_ts"] = time.time()


def _invalidate_cache(*cache_keys: str):
    """指定したキャッシュのみ無効化する。キー未指定なら全キャッシュを破棄。"""
    targets = cache_keys if cache_keys else (
        "_cache_metadata", "_cache_folders",
        "_cache_weight_data", "_cache_food_processed",
    )
    for ck in targets:
        st.session_state.pop(ck, None)
        st.session_state.pop(f"{ck}_ts", None)


def _invalidate_all_caches():
    """全データキャッシュを無効化し、次回読み込みでSheetsから再取得させる。"""
    _invalidate_cache()


# ---------------------------------------------------------------------------
# メタデータ管理
# ---------------------------------------------------------------------------
def load_metadata() -> dict:
    """メタデータを読み込む。session_state → Sheets+ローカルマージ → ローカルの順。"""
    ck = "_cache_metadata"
    if _is_cache_valid(ck):
        return st.session_state[ck]

    sheets_data = None
    local_data = None
    sh = get_sheets_client()
    _log.info(f"[load_metadata] get_sheets_client() = {sh is not None}")

    # Sheets から読み込み
    if sh is not None:
        sheets_data = _read_json_from_sheet(sh, "metadata")
        _log.info(f"[load_metadata] Sheets entries = {len(sheets_data) if sheets_data else 0}")

    # ローカルから読み込み
    if METADATA_PATH.exists():
        try:
            with open(METADATA_PATH, "r", encoding="utf-8") as f:
                local_data = json.load(f)
            _log.info(f"[load_metadata] Local entries = {len(local_data)}")
        except (json.JSONDecodeError, IOError):
            pass

    # マージ: Sheets をベースに、ローカルにしかないエントリを補完
    if sheets_data is not None and local_data is not None:
        merged = dict(sheets_data)
        new_from_local = 0
        for fid, meta in local_data.items():
            if fid not in merged:
                merged[fid] = meta
                new_from_local += 1
        if new_from_local > 0:
            _log.info(f"[load_metadata] ローカルから {new_from_local} 件を補完 → Sheets再同期")
            # Sheets に統合データを書き戻す
            try:
                _write_json_to_sheet(sh, "metadata", merged)
            except Exception as e:
                _log.warning(f"[load_metadata] マージ後のSheets書き戻し失敗: {e}")
        data = merged
    elif sheets_data is not None:
        data = sheets_data
    elif local_data is not None:
        _log.info("[load_metadata] ローカルフォールバック使用")
        data = local_data
    else:
        data = {}

    _set_cache(ck, data)
    # ローカルファイルも同期更新
    _atomic_json_write(METADATA_PATH, data)
    return data


def save_metadata(metadata: dict) -> bool:
    """メタデータを保存する。session_state + Sheets + ローカル（バックアップ）。
    Sheetsへの書き込み成否を返す（未接続の場合もFalse）。
    失敗時は session_state にペンディングデータを保持し次回再試行。"""
    _log.info(f"[save_metadata] 保存開始 entries={len(metadata)}")
    _set_cache("_cache_metadata", metadata)
    sheets_ok = False
    sh = None
    try:
        sh = get_sheets_client()
        if sh is not None:
            sheets_ok = _write_json_to_sheet(sh, "metadata", metadata)
            # キャッシュ接続で失敗 → 新規接続でリトライ
            if not sheets_ok:
                _log.warning("[save_metadata] キャッシュ接続で失敗、新規接続でリトライ")
                st.session_state.pop("_sheets_conn", None)
                sh2 = _new_sheets_connection()
                if sh2 is not None:
                    sheets_ok = _write_json_to_sheet(sh2, "metadata", metadata)
            _log.info(f"[save_metadata] Sheets書き込み結果: {sheets_ok}")
            if not sheets_ok:
                if "_save_error_detail" not in st.session_state:
                    st.session_state["_save_error_detail"] = "write_json_to_sheet が False を返却"
        else:
            _log.warning("[save_metadata] Sheets未接続")
            st.session_state["_save_error_detail"] = "Sheets未接続 (get_sheets_client=None)"
    except Exception as e:
        err = f"{type(e).__name__}: {e}"
        _log.error(f"[save_metadata] 例外: {err}")
        st.session_state["_save_error_detail"] = err
    _atomic_json_write(METADATA_PATH, metadata)
    _sync_err = ""
    if not sheets_ok and sh is not None:
        # 次回 rerun で再試行するためペンディングデータを保持
        st.session_state["_pending_metadata"] = metadata
        try:
            _sync_err = st.session_state.pop("_save_error_detail", "")
            msg = "⚠️ Sheetsへの保存に失敗しました。次回アクセス時に再試行します。"
            if _sync_err:
                msg += f"\n({_sync_err})"
            st.toast(msg, icon="⚠️")
        except Exception:
            pass
    elif sheets_ok:
        # 成功したらペンディングをクリア
        st.session_state.pop("_pending_metadata", None)
    # --- 同期ステータス記録 ---
    _record_sync_status("metadata", sheets_ok, count=len(metadata),
                        error=_sync_err, attempted=(sh is not None))
    return sheets_ok


def _record_sync_status(data_type: str, success: bool, count: int = 0,
                        error: str = "", attempted: bool = True):
    """各データタイプの Sheets 同期ステータスを session_state に記録する。
    attempted=False は Sheets 未接続のため同期を試みなかったことを示す。"""
    key = "_sync_status"
    if key not in st.session_state:
        st.session_state[key] = {}
    st.session_state[key][data_type] = {
        "success": success,
        "attempted": attempted,
        "count": count,
        "error": error,
        "timestamp": datetime.now().isoformat(),
    }


_SYNC_HEALTH_INTERVAL = 300  # 5分


def _check_sync_health():
    """ローカルとSheetsの件数を比較し、差異を session_state に記録する。
    5分間隔でのみ実行。Sheets 未接続時はスキップ。"""
    last_check = st.session_state.get("_sync_health_ts", 0)
    if time.time() - last_check < _SYNC_HEALTH_INTERVAL:
        return
    st.session_state["_sync_health_ts"] = time.time()

    sh = get_sheets_client()
    if sh is None:
        # Sheets 未接続 — ヘルスチェック不要（差異表示しない）
        st.session_state["_sync_health"] = {}
        st.session_state["_sheets_connected"] = False
        st.session_state["_sheets_error"] = st.session_state.get(
            "_save_error_detail", "不明")
        return

    st.session_state["_sheets_connected"] = True
    health = {}

    # メタデータ
    try:
        local_meta = {}
        if METADATA_PATH.exists():
            with open(METADATA_PATH, "r", encoding="utf-8") as f:
                local_meta = json.load(f)
        sheets_meta_count = 0
        sheets_data = _read_json_from_sheet(sh, "metadata")
        if sheets_data and isinstance(sheets_data, dict):
            sheets_meta_count = len(sheets_data)
        health["metadata"] = {
            "local": len(local_meta), "sheets": sheets_meta_count,
            "diff": len(local_meta) - sheets_meta_count,
        }
    except Exception as e:
        _log.warning(f"[sync_health] metadata チェック失敗: {e}")
        health["metadata"] = {"local": 0, "sheets": 0, "diff": 0, "error": str(e)}

    # 体重データ
    try:
        local_wt = {}
        if WEIGHT_DATA_PATH.exists():
            with open(WEIGHT_DATA_PATH, "r", encoding="utf-8") as f:
                local_wt = json.load(f)
        sheets_wt_count = 0
        sheets_wt = _read_json_from_sheet(sh, "weight_data")
        if sheets_wt and isinstance(sheets_wt, dict):
            sheets_wt_count = len(sheets_wt)
        health["weight_data"] = {
            "local": len(local_wt), "sheets": sheets_wt_count,
            "diff": len(local_wt) - sheets_wt_count,
        }
    except Exception as e:
        _log.warning(f"[sync_health] weight_data チェック失敗: {e}")
        health["weight_data"] = {"local": 0, "sheets": 0, "diff": 0, "error": str(e)}

    # 食事画像処理済み
    try:
        local_fp = {}
        if FOOD_IMAGES_PROCESSED_PATH.exists():
            with open(FOOD_IMAGES_PROCESSED_PATH, "r", encoding="utf-8") as f:
                local_fp = json.load(f)
        sheets_fp_count = 0
        sheets_fp = _read_json_from_sheet(sh, "food_processed")
        if sheets_fp and isinstance(sheets_fp, dict):
            sheets_fp_count = len(sheets_fp)
        health["food_processed"] = {
            "local": len(local_fp), "sheets": sheets_fp_count,
            "diff": len(local_fp) - sheets_fp_count,
        }
    except Exception as e:
        _log.warning(f"[sync_health] food_processed チェック失敗: {e}")
        health["food_processed"] = {"local": 0, "sheets": 0, "diff": 0, "error": str(e)}

    st.session_state["_sync_health"] = health
    total_diff = sum(abs(v.get("diff", 0)) for v in health.values())
    if total_diff > 0:
        _log.info(f"[sync_health] 差異検出: {health}")


_AUTO_SYNC_COOLDOWN = 600  # 10分


def _auto_resolve_sync_diff():
    """ヘルスチェックで差異が検出された場合、ローカルとSheetsを自動マージする。
    双方にしかないデータを統合し、競合はローカル優先。クールダウン付き。"""
    health = st.session_state.get("_sync_health", {})
    total_diff = sum(abs(v.get("diff", 0)) for v in health.values())
    if total_diff == 0:
        return

    # クールダウンチェック
    last_auto = st.session_state.get("_auto_sync_ts", 0)
    if time.time() - last_auto < _AUTO_SYNC_COOLDOWN:
        return

    sh = get_sheets_client()
    if sh is None:
        return

    st.session_state["_auto_sync_ts"] = time.time()
    _log.info(f"[auto_sync] 差異自動マージ開始 (total_diff={total_diff})")

    _SYNC_TARGETS = [
        ("metadata", METADATA_PATH, "_cache_metadata"),
        ("weight_data", WEIGHT_DATA_PATH, "_cache_weight_data"),
        ("food_processed", FOOD_IMAGES_PROCESSED_PATH, "_cache_food_processed"),
    ]

    synced_types = []
    for dtype, path, cache_key in _SYNC_TARGETS:
        h = health.get(dtype, {})
        if h.get("diff", 0) == 0 and not h.get("error"):
            continue  # 差異なし — スキップ
        try:
            # ローカルデータ読み込み
            local_data = {}
            if path.exists():
                with open(path, "r", encoding="utf-8") as f:
                    local_data = json.load(f)

            # Sheetsデータ読み込み
            sheets_data = _read_json_from_sheet(sh, dtype)
            if not isinstance(sheets_data, dict):
                sheets_data = {}

            # マージ: Sheets をベースに、ローカルで上書き（ローカル優先）
            merged = dict(sheets_data)
            for k, v in local_data.items():
                merged[k] = v

            merged_count = len(merged)
            local_count = len(local_data)
            sheets_count = len(sheets_data)
            new_from_sheets = merged_count - local_count
            new_from_local = merged_count - sheets_count

            # 変化がある場合のみ書き込み
            if merged_count != local_count:
                _atomic_json_write(path, merged)
                _set_cache(cache_key, merged)
                _log.info(f"[auto_sync] {dtype}: ローカル更新 "
                          f"({local_count}→{merged_count}, Sheetsから+{new_from_sheets})")

            if merged_count != sheets_count:
                ok = _write_json_to_sheet(sh, dtype, merged)
                if ok:
                    _record_sync_status(dtype, True, count=merged_count, attempted=True)
                    _log.info(f"[auto_sync] {dtype}: Sheets更新 "
                              f"({sheets_count}→{merged_count}, ローカルから+{new_from_local})")
                else:
                    _record_sync_status(dtype, False, count=merged_count,
                                        error="auto_sync write failed", attempted=True)
                    _log.warning(f"[auto_sync] {dtype}: Sheets書き込み失敗")
                time.sleep(1)  # API rate limit 対策

            synced_types.append(dtype)
        except Exception as e:
            _log.warning(f"[auto_sync] {dtype} マージ失敗: {type(e).__name__}: {e}")

    if synced_types:
        # ヘルスチェックを即再実行して差異表示を更新
        st.session_state["_sync_health_ts"] = 0
        _log.info(f"[auto_sync] 完了: {', '.join(synced_types)}")


def _force_sync_local_to_sheets() -> dict:
    """ローカルの全データ（metadata, weight_data, food_processed）を
    Sheetsに一括書き込みする。結果を返す。"""
    results = {}
    sh = get_sheets_client()
    if sh is None:
        return {"error": "Sheets未接続"}

    # metadata
    try:
        if METADATA_PATH.exists():
            with open(METADATA_PATH, "r", encoding="utf-8") as f:
                meta = json.load(f)
            ok = _write_json_to_sheet(sh, "metadata", meta)
            results["metadata"] = {"success": ok, "count": len(meta)}
            _record_sync_status("metadata", ok, count=len(meta))
            time.sleep(2)  # rate limit対策
        else:
            results["metadata"] = {"success": True, "count": 0, "note": "ファイルなし"}
    except Exception as e:
        results["metadata"] = {"success": False, "error": str(e)}

    # weight_data
    try:
        if WEIGHT_DATA_PATH.exists():
            with open(WEIGHT_DATA_PATH, "r", encoding="utf-8") as f:
                wt = json.load(f)
            ok = _write_json_to_sheet(sh, "weight_data", wt)
            results["weight_data"] = {"success": ok, "count": len(wt)}
            _record_sync_status("weight_data", ok, count=len(wt))
            time.sleep(2)
        else:
            results["weight_data"] = {"success": True, "count": 0, "note": "ファイルなし"}
    except Exception as e:
        results["weight_data"] = {"success": False, "error": str(e)}

    # food_processed
    try:
        if FOOD_IMAGES_PROCESSED_PATH.exists():
            with open(FOOD_IMAGES_PROCESSED_PATH, "r", encoding="utf-8") as f:
                fp = json.load(f)
            ok = _write_json_to_sheet(sh, "food_processed", fp)
            results["food_processed"] = {"success": ok, "count": len(fp)}
            _record_sync_status("food_processed", ok, count=len(fp))
        else:
            results["food_processed"] = {"success": True, "count": 0, "note": "ファイルなし"}
    except Exception as e:
        results["food_processed"] = {"success": False, "error": str(e)}

    return results


def _force_sync_sheets_to_local() -> dict:
    """SheetsのデータをローカルJSONに強制上書きする。結果を返す。"""
    results = {}
    sh = get_sheets_client()
    if sh is None:
        return {"error": "Sheets未接続"}

    # metadata
    try:
        data = _read_json_from_sheet(sh, "metadata")
        if data and isinstance(data, dict):
            _atomic_json_write(METADATA_PATH, data)
            _set_cache("_cache_metadata", data)
            results["metadata"] = {"success": True, "count": len(data)}
        else:
            results["metadata"] = {"success": False, "note": "Sheetsにデータなし"}
    except Exception as e:
        results["metadata"] = {"success": False, "error": str(e)}

    # weight_data
    try:
        data = _read_json_from_sheet(sh, "weight_data")
        if data and isinstance(data, dict):
            _atomic_json_write(WEIGHT_DATA_PATH, data)
            _set_cache("_cache_weight_data", data)
            results["weight_data"] = {"success": True, "count": len(data)}
        else:
            results["weight_data"] = {"success": False, "note": "Sheetsにデータなし"}
    except Exception as e:
        results["weight_data"] = {"success": False, "error": str(e)}

    # food_processed
    try:
        data = _read_json_from_sheet(sh, "food_processed")
        if data and isinstance(data, dict):
            _atomic_json_write(FOOD_IMAGES_PROCESSED_PATH, data)
            _set_cache("_cache_food_processed", data)
            results["food_processed"] = {"success": True, "count": len(data)}
        else:
            results["food_processed"] = {"success": False, "note": "Sheetsにデータなし"}
    except Exception as e:
        results["food_processed"] = {"success": False, "error": str(e)}

    return results


def _retry_pending_saves() -> None:
    """前回失敗した Sheets 書き込みを再試行する。"""
    # metadata のリトライ
    pending_meta = st.session_state.get("_pending_metadata")
    if pending_meta is not None:
        _log.info(f"[retry] pending metadata: {len(pending_meta)} entries")
        sh = get_sheets_client()
        if sh is not None:
            ok = _write_json_to_sheet(sh, "metadata", pending_meta)
            if ok:
                _log.info("[retry] metadata Sheets書き込み成功")
                st.session_state.pop("_pending_metadata", None)
            else:
                _log.warning("[retry] metadata Sheets書き込み再失敗")

    # weight_data のリトライ
    pending_wd = st.session_state.get("_pending_weight_data")
    if pending_wd is not None:
        _log.info("[retry] pending weight_data")
        sh = get_sheets_client()
        if sh is not None:
            ok = _write_json_to_sheet(sh, "weight_data", pending_wd)
            if ok:
                _log.info("[retry] weight_data Sheets書き込み成功")
                st.session_state.pop("_pending_weight_data", None)
            else:
                _log.warning("[retry] weight_data Sheets書き込み再失敗")

    # folders のリトライ
    pending_folders = st.session_state.get("_pending_folders")
    if pending_folders is not None:
        _log.info("[retry] pending folders")
        sh = get_sheets_client()
        if sh is not None:
            ok = _write_json_to_sheet(sh, "folders", {"folders": pending_folders})
            if ok:
                _log.info("[retry] folders Sheets書き込み成功")
                st.session_state.pop("_pending_folders", None)
            else:
                _log.warning("[retry] folders Sheets書き込み再失敗")


def get_status(meta: dict) -> str:
    """メタデータからステータスを取得する。"""
    return meta.get("status", STATUS_AUTO)


def get_status_icon(meta: dict) -> str:
    """ステータスに応じたアイコンを返す。"""
    s = get_status(meta)
    if s == STATUS_REVIEWED:
        return "✅"
    if s == STATUS_BLOCKED:
        return "🚫"
    return "🆕"


def is_patient_data(meta: dict) -> bool:
    """メタデータが患者データ由来かどうかを判定する。"""
    return meta.get("source") == SOURCE_PATIENT_DATA


def get_summary_label(meta: dict) -> str:
    """メタデータソースに応じて要約フィールドのラベルを返す。"""
    if is_patient_data(meta):
        return "検査所見"
    return "要約"


# ---------------------------------------------------------------------------
# フォルダ管理
# ---------------------------------------------------------------------------
def load_folders() -> list[str]:
    """フォルダ名リストを読み込む。session_state → Sheets → ローカルの順。"""
    ck = "_cache_folders"
    if _is_cache_valid(ck):
        return st.session_state[ck]
    sh = get_sheets_client()
    if sh is not None:
        data = _read_json_from_sheet(sh, "folders")
        if data is not None:
            folders = data.get("folders", []) if isinstance(data, dict) else data
            if DEFAULT_FOLDER not in folders:
                folders.insert(0, DEFAULT_FOLDER)
            _set_cache(ck, folders)
            _atomic_json_write(FOLDERS_PATH, {"folders": folders})
            return folders
    if FOLDERS_PATH.exists():
        try:
            with open(FOLDERS_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                folders = data.get("folders", [])
                if DEFAULT_FOLDER not in folders:
                    folders.insert(0, DEFAULT_FOLDER)
                _set_cache(ck, folders)
                return folders
        except (json.JSONDecodeError, IOError):
            pass
    result = [DEFAULT_FOLDER]
    _set_cache(ck, result)
    return result


def save_folders(folders: list[str]) -> None:
    """フォルダ名リストを保存する。session_state + Sheets + ローカル。"""
    if DEFAULT_FOLDER not in folders:
        folders.insert(0, DEFAULT_FOLDER)
    _set_cache("_cache_folders", folders)
    sheets_ok = False
    sh = get_sheets_client()
    if sh is not None:
        sheets_ok = _write_json_to_sheet(sh, "folders", {"folders": folders})
    _atomic_json_write(FOLDERS_PATH, {"folders": folders})
    if not sheets_ok and sh is not None:
        st.session_state["_pending_folders"] = folders
    elif sheets_ok:
        st.session_state.pop("_pending_folders", None)


def get_folder(meta: dict) -> str:
    """メタデータからフォルダ名を取得する。"""
    return meta.get("folder", DEFAULT_FOLDER)


def get_all_folders_from_metadata(metadata: dict) -> list[str]:
    """メタデータ内で使用されている全フォルダ名を取得する。"""
    saved_folders = load_folders()
    used = set()
    for meta in metadata.values():
        used.add(get_folder(meta))
    all_folders = list(saved_folders)
    for f in sorted(used):
        if f not in all_folders:
            all_folders.append(f)
    return all_folders


# ---------------------------------------------------------------------------
# 体重管理データ管理
# ---------------------------------------------------------------------------
def load_weight_data() -> dict:
    """体重管理データを読み込む。Sheets+ローカルをマージ。"""
    ck = "_cache_weight_data"
    if _is_cache_valid(ck):
        return st.session_state[ck]

    default = {"goals": {}, "records": {}}
    sheets_data = None
    local_data = None
    sh = get_sheets_client()

    # Sheets から読み込み
    if sh is not None:
        try:
            sheets_data = _read_json_from_sheet(sh, "weight_data")
        except gspread.exceptions.GSpreadException:
            pass

    # ローカルから読み込み
    if WEIGHT_DATA_PATH.exists():
        try:
            with open(WEIGHT_DATA_PATH, "r", encoding="utf-8") as f:
                local_data = json.load(f)
        except (json.JSONDecodeError, IOError):
            pass

    # マージ: records レベルで補完
    if sheets_data is not None and local_data is not None:
        merged = dict(sheets_data)
        s_records = merged.setdefault("records", {})
        l_records = local_data.get("records", {})
        new_from_local = 0
        for dk, day in l_records.items():
            if dk not in s_records:
                s_records[dk] = day
                new_from_local += 1
            else:
                # 日付は存在するが items が少ない場合、ローカルの items を補完
                s_items_ids = {it.get("id") for it in s_records[dk].get("items", []) if it.get("id")}
                for it in day.get("items", []):
                    if it.get("id") and it["id"] not in s_items_ids:
                        s_records[dk].setdefault("items", []).append(it)
                        new_from_local += 1
                # weight フィールドも補完（Sheets に weight がなくローカルにある場合）
                if not s_records[dk].get("weight") and day.get("weight"):
                    s_records[dk]["weight"] = day["weight"]
                    if day.get("weight_recorded_at"):
                        s_records[dk]["weight_recorded_at"] = day["weight_recorded_at"]
                    new_from_local += 1
                # total_calories もローカルの方が大きければ補完
                if day.get("total_calories", 0) > s_records[dk].get("total_calories", 0):
                    s_records[dk]["total_calories"] = day["total_calories"]
        # goals はローカルが新しければ上書き
        if not merged.get("goals") and local_data.get("goals"):
            merged["goals"] = local_data["goals"]
        if new_from_local > 0:
            _log.info(f"[load_weight_data] ローカルから {new_from_local} 件を補完")
            try:
                _write_json_to_sheet(sh, "weight_data", merged)
            except gspread.exceptions.GSpreadException:
                pass
        data = merged
    elif sheets_data is not None:
        data = sheets_data
    elif local_data is not None:
        data = local_data
    else:
        data = default

    _set_cache(ck, data)
    _atomic_json_write(WEIGHT_DATA_PATH, data)
    return data


def save_weight_data(weight_data: dict, show_error: bool = True) -> bool:
    """体重管理データを保存する。session_state + Sheets + ローカルJSON。"""
    _set_cache("_cache_weight_data", weight_data)
    sheets_ok = False
    sh = get_sheets_client()
    if sh is not None:
        try:
            sheets_ok = _write_json_to_sheet(sh, "weight_data", weight_data)
        except gspread.exceptions.GSpreadException:
            try:
                st.session_state.pop("_sheets_conn", None)
                sh2 = _new_sheets_connection()
                if sh2 is not None:
                    sheets_ok = _write_json_to_sheet(sh2, "weight_data", weight_data)
            except gspread.exceptions.GSpreadException:
                pass
    _atomic_json_write(WEIGHT_DATA_PATH, weight_data)
    _sync_err = ""
    if not sheets_ok and sh is not None:
        st.session_state["_pending_weight_data"] = weight_data
        if show_error:
            _sync_err = st.session_state.pop("_save_error_detail", "")
            msg = "⚠️ Sheetsへの保存に失敗しました。次回アクセス時に再試行します。"
            if _sync_err:
                msg += f"\n({_sync_err})"
            st.toast(msg, icon="⚠️")
    elif sheets_ok:
        st.session_state.pop("_pending_weight_data", None)
    # --- 同期ステータス記録 ---
    _record_sync_status("weight_data", sheets_ok, count=len(weight_data),
                        error=_sync_err, attempted=(sh is not None))
    return sheets_ok


def format_relative_time(iso_str: str) -> str:
    """ISO形式の日時文字列を相対時間（例: '5分前'）に変換する。"""
    try:
        dt = datetime.fromisoformat(iso_str)
        delta = datetime.now() - dt
        seconds = delta.total_seconds()
        if seconds < 60:
            return "たった今"
        elif seconds < 3600:
            return f"{int(seconds // 60)}分前"
        elif seconds < 86400:
            return f"{int(seconds // 3600)}時間前"
        else:
            return f"{int(seconds // 86400)}日前"
    except (ValueError, TypeError):
        return ""


# ---------------------------------------------------------------------------
# 認証・API初期化
# ---------------------------------------------------------------------------
@st.cache_resource(show_spinner="Google Drive に接続中...")
def get_drive_service():
    """サービスアカウント認証を行い、Drive APIクライアントを返す。"""
    try:
        creds = service_account.Credentials.from_service_account_info(
            st.secrets["gcp_service_account"],
            scopes=SCOPES,
        )
        return build("drive", "v3", credentials=creds)
    except KeyError as e:
        st.error(
            f"認証情報が見つかりません: {e}\n\n"
            "`.streamlit/secrets.toml` に `[gcp_service_account]` セクションが"
            "正しく設定されているか確認してください。"
        )
        st.stop()
    except Exception as e:
        _log.error(f"Google Drive 認証失敗: {e}")
        st.error("Google Drive への認証に失敗しました。管理者にお問い合わせください。")
        st.stop()


def get_folder_id() -> str:
    """secrets.toml から対象フォルダIDを取得する。"""
    try:
        folder_id = st.secrets["folder_id"]
        if not folder_id:
            raise ValueError("folder_id が空です")
        return folder_id
    except KeyError:
        st.error(
            "`folder_id` が `.streamlit/secrets.toml` に設定されていません。\n\n"
            "テンプレートを参考に設定してください。"
        )
        st.stop()


def get_patient_folder_id() -> str | None:
    """secrets.toml から患者データフォルダIDを取得する。未設定なら None。"""
    try:
        fid = st.secrets.get("patient_folder_id", "")
        if not fid:
            return None
        return fid
    except (KeyError, FileNotFoundError):
        return None


def get_food_folder_id() -> str | None:
    """食事画像フォルダIDを取得する。未設定なら自動作成して返す。"""
    # 1. secrets.toml から取得を試みる
    try:
        fid = st.secrets.get("food_images_folder_id", "")
        if fid:
            return fid
    except (KeyError, FileNotFoundError):
        pass

    # 2. session_state にキャッシュがあればそれを使う（secrets書き込み後の再起動前対策）
    cached = st.session_state.get("_food_folder_id_cache")
    if cached:
        return cached

    # 3. clinical-kb フォルダ内に自動作成
    try:
        service = get_drive_service()
        parent_id = get_folder_id()  # clinical-kb フォルダ

        # clinical-kb 内の既存「食事画像」フォルダを検索
        query = (
            f"'{parent_id}' in parents and name='食事画像' "
            f"and mimeType='application/vnd.google-apps.folder' and trashed=false"
        )
        results = service.files().list(q=query, fields="files(id, name)", pageSize=5).execute()
        existing = results.get("files", [])
        if existing:
            new_fid = existing[0]["id"]
        else:
            # clinical-kb 内に新規作成
            file_metadata = {
                "name": "食事画像",
                "mimeType": "application/vnd.google-apps.folder",
                "parents": [parent_id],
            }
            folder = service.files().create(body=file_metadata, fields="id").execute()
            new_fid = folder["id"]

        # secrets.toml に追記
        secrets_path = Path(__file__).parent / ".streamlit" / "secrets.toml"
        if secrets_path.exists():
            content = secrets_path.read_text(encoding="utf-8")
            if "food_images_folder_id" not in content:
                with open(secrets_path, "a", encoding="utf-8") as f:
                    f.write(f'\n# 食事画像フォルダID（自動作成）\nfood_images_folder_id = "{new_fid}"\n')

        st.session_state["_food_folder_id_cache"] = new_fid
        return new_fid
    except Exception as e:
        import logging
        logging.warning(f"食事画像フォルダの自動作成に失敗: {e}")
        return None


def load_food_processed() -> dict:
    """処理済み食事画像IDの辞書を読み込む。Sheets+ローカルをマージ。"""
    ck = "_cache_food_processed"
    if _is_cache_valid(ck):
        return st.session_state[ck]

    sheets_data = None
    local_data = None
    sh = get_sheets_client()

    if sh is not None:
        try:
            sheets_data = _read_json_from_sheet(sh, "food_processed")
        except gspread.exceptions.GSpreadException:
            pass

    try:
        if FOOD_IMAGES_PROCESSED_PATH.exists():
            with open(FOOD_IMAGES_PROCESSED_PATH, "r", encoding="utf-8") as f:
                local_data = json.load(f)
    except (OSError, json.JSONDecodeError):
        pass

    # マージ: Sheets をベースに、ローカルにしかないエントリを補完
    if sheets_data is not None and local_data is not None:
        merged = dict(sheets_data)
        new_from_local = 0
        for fid, meta in local_data.items():
            if fid not in merged:
                merged[fid] = meta
                new_from_local += 1
        if new_from_local > 0:
            _log.info(f"[load_food_processed] ローカルから {new_from_local} 件を補完 → Sheets再同期")
            try:
                _write_json_to_sheet(sh, "food_processed", merged)
            except gspread.exceptions.GSpreadException:
                pass
        data = merged
    elif sheets_data is not None:
        data = sheets_data
    elif local_data is not None:
        data = local_data
    else:
        data = {}

    _set_cache(ck, data)
    _atomic_json_write(FOOD_IMAGES_PROCESSED_PATH, data)
    return data


def save_food_processed(data: dict) -> None:
    """処理済み食事画像IDの辞書を保存する。Sheets + ローカル。"""
    _set_cache("_cache_food_processed", data)
    sheets_ok = False
    sh = get_sheets_client()
    if sh is not None:
        try:
            sheets_ok = _write_json_to_sheet(sh, "food_processed", data)
        except gspread.exceptions.GSpreadException:
            try:
                st.session_state.pop("_sheets_conn", None)
                sh2 = _new_sheets_connection()
                if sh2 is not None:
                    sheets_ok = _write_json_to_sheet(sh2, "food_processed", data)
            except gspread.exceptions.GSpreadException:
                pass
    _atomic_json_write(FOOD_IMAGES_PROCESSED_PATH, data)
    # --- 同期ステータス記録 ---
    _sync_err = st.session_state.pop("_save_error_detail", "") if not sheets_ok else ""
    _record_sync_status("food_processed", sheets_ok, count=len(data),
                        error=_sync_err, attempted=(sh is not None))


def get_gemini_api_key() -> str | None:
    """secrets.toml から Gemini APIキーを取得する。未設定なら None。"""
    try:
        api_key = st.secrets["GOOGLE_API_KEY"]
        if not api_key or api_key == "YOUR_GEMINI_API_KEY":
            return None
        return api_key
    except KeyError:
        return None


# ---------------------------------------------------------------------------
# Google Drive 操作
# ---------------------------------------------------------------------------
def _list_drive_images_impl(_service, folder_id: str, *,
                             show_errors: bool = True) -> list[dict]:
    """Drive フォルダの画像一覧を取得する内部実装（リトライ・ページネーション対応）。"""
    mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
    query = f"'{folder_id}' in parents and ({mime_query}) and trashed=false"
    all_files: list[dict] = []
    page_token = None
    for _ in range(1000):  # ページ数の上限（無限ループ防止）
        for attempt in range(3):
            try:
                params = dict(
                    q=query,
                    fields="nextPageToken, files(id, name, mimeType, createdTime, modifiedTime, thumbnailLink)",
                    orderBy="modifiedTime desc",
                    pageSize=100,
                )
                if page_token:
                    params["pageToken"] = page_token
                results = _service.files().list(**params).execute()
                all_files.extend(results.get("files", []))
                page_token = results.get("nextPageToken")
                break
            except HttpError as e:
                if e.resp.status == 404:
                    if show_errors:
                        st.error(
                            "指定されたフォルダが見つかりません。\n\n"
                            "`folder_id` が正しいか、サービスアカウントにフォルダが"
                            "共有されているか確認してください。"
                        )
                    return []
                if attempt < 2:
                    time.sleep(2)
                    continue
                if show_errors:
                    st.warning("⚠️ Google Driveとの通信に失敗しました。ページを再読み込みしてください。")
                return all_files
            except Exception:
                if attempt < 2:
                    time.sleep(2)
                    continue
                if show_errors:
                    st.warning("⚠️ Google Driveとの通信に失敗しました。ページを再読み込みしてください。")
                return all_files
        else:
            return all_files
        if not page_token:
            break
    return all_files


@st.cache_data(ttl=120, show_spinner="ファイル一覧を取得中...")
def list_images(_service, folder_id: str) -> list[dict]:
    """指定フォルダ内の画像ファイル一覧を取得する（2分キャッシュ）。"""
    return _list_drive_images_impl(_service, folder_id)


@st.cache_data(ttl=120, show_spinner="患者データを取得中...")
def list_patient_images(_service, patient_folder_id: str) -> list[dict]:
    """患者データフォルダ内の画像ファイル一覧を取得する（2分キャッシュ）。"""
    return _list_drive_images_impl(_service, patient_folder_id, show_errors=False)


def list_all_images(_service, folder_id: str, metadata: dict,
                    patient_folder_id: str | None = None) -> list[dict]:
    """Google Drive画像 + 患者データ画像 + ローカルアップロード画像を統合した一覧を返す。"""
    images = list_images(_service, folder_id)
    drive_ids = {img["id"] for img in images}

    # 患者データフォルダの画像を追加
    if patient_folder_id:
        patient_imgs = list_patient_images(_service, patient_folder_id)
        for img in patient_imgs:
            if img["id"] not in drive_ids:
                images.append(img)
                drive_ids.add(img["id"])

    # メタデータにあるがDrive一覧にないローカル画像を追加
    if UPLOADS_DIR.exists():
        for fid, meta in metadata.items():
            if fid not in drive_ids and meta.get("source") == SOURCE_UPLOAD:
                # ローカルファイルが存在するか確認
                exists = any(
                    (UPLOADS_DIR / f"{fid}.{ext}").exists()
                    for ext in ("png", "jpg", "jpeg")
                )
                if exists:
                    images.append({
                        "id": fid,
                        "name": meta.get("title", fid),
                        "mimeType": "image/png",
                    })
    return images


@st.cache_data(ttl=300, show_spinner=False, max_entries=100)
def download_image(_service, file_id: str) -> bytes:
    """画像をバイト列で返す。ローカルアップロード画像を優先し、なければGoogle Driveから取得。"""
    # ローカルアップロード画像を確認（パストラバーサル防止）
    try:
        _validate_file_id(file_id)
    except ValueError:
        _log.warning(f"[download_image] 不正なfile_id: {file_id!r}")
        return b""
    for ext in ("png", "jpg", "jpeg"):
        local_path = UPLOADS_DIR / f"{file_id}.{ext}"
        if local_path.exists():
            return local_path.read_bytes()

    # Google Drive からダウンロード
    max_retries = 3
    for attempt in range(max_retries):
        try:
            request = _service.files().get_media(fileId=file_id)
            buffer = io.BytesIO()
            downloader = MediaIoBaseDownload(buffer, request)
            done = False
            while not done:
                _, done = downloader.next_chunk()
            return buffer.getvalue()
        except Exception:
            if attempt < max_retries - 1:
                time.sleep(2)
                continue
            raise


@st.cache_data(ttl=86400, show_spinner=False, max_entries=2000)
def download_thumbnail(_service, file_id: str, max_px: int = 400,
                       quality: int = 70) -> bytes:
    """サムネイル用に軽量化した画像を返す（既定: 最大400px, JPEG 70%）。
    ギャラリー用に大きく綺麗な画像が必要な場合は max_px=800, quality=88 等を指定する。

    永続ディスクキャッシュ (.thumb_cache/{file_id}_{max_px}.jpg) で
    Drive ダウンロード + リサイズの繰り返しを回避する。
    """
    cache_path = THUMB_CACHE_DIR / f"ss_{file_id}_{max_px}.jpg"
    if cache_path.exists():
        try:
            return cache_path.read_bytes()
        except Exception:
            pass

    raw = download_image(_service, file_id)
    if not raw:
        return raw
    try:
        img = Image.open(io.BytesIO(raw))
        img.thumbnail((max_px, max_px))
        buf = io.BytesIO()
        img.convert("RGB").save(buf, format="JPEG", quality=quality, optimize=True)
        thumb_bytes = buf.getvalue()
        try:
            THUMB_CACHE_DIR.mkdir(exist_ok=True)
            cache_path.write_bytes(thumb_bytes)
        except Exception:
            pass
        return thumb_bytes
    except Exception:
        return raw  # リサイズ失敗時はフル画像を返す


# ---------------------------------------------------------------------------
# Gemini AI (REST API 直接呼び出し)
# ---------------------------------------------------------------------------
_GEMINI_MODEL = "gemini-2.5-flash"
_GEMINI_API_URL = (
    "https://generativelanguage.googleapis.com/v1beta/models/"
    "{model}:generateContent?key={key}"
)


class GeminiBlockedError(RuntimeError):
    """Gemini が永続的にプロンプトをブロックした状態。再試行不可。

    safetySettings で抑えられない OTHER / PROHIBITED_CONTENT 等の判定で発生する。
    呼び出し側で「以後スキャン対象から外す」マークを残すために通常エラーと区別する。
    """

    def __init__(self, reason: str):
        super().__init__(f"Gemini API: プロンプトがブロックされました ({reason})")
        self.reason = reason


def _gemini_generate(api_key: str, contents: list, model: str | None = None) -> str:
    """Gemini REST API を呼び出してテキスト応答を返す。

    contents は Gemini API の ``parts`` 形式のリスト。
    テキストのみの場合: [{"text": "..."}]
    画像付きの場合: [{"text": "..."}, {"inline_data": {"mime_type": "...", "data": "..."}}]
    """
    url = _GEMINI_API_URL.format(model=model or _GEMINI_MODEL, key=api_key)
    payload = {
        "contents": [{"parts": contents}],
        "safetySettings": [
            {"category": "HARM_CATEGORY_HARASSMENT", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_HATE_SPEECH", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_SEXUALLY_EXPLICIT", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_DANGEROUS_CONTENT", "threshold": "BLOCK_NONE"},
        ],
    }
    resp = requests.post(url, json=payload, timeout=120)
    try:
        data = resp.json()
    except ValueError:
        raise RuntimeError(
            f"Gemini API: 非JSONレスポンス (status={resp.status_code}, body={resp.text[:200]})"
        )

    # Gemini はエラー時 200 以外でも JSON body にエラー詳細を入れる
    if isinstance(data, dict) and "error" in data:
        err = data["error"] or {}
        msg = err.get("message", "不明なエラー")
        status = err.get("status", "")
        raise RuntimeError(f"Gemini API エラー [{resp.status_code} {status}]: {msg}")

    candidates = data.get("candidates") if isinstance(data, dict) else None
    if not candidates:
        feedback = (data.get("promptFeedback") if isinstance(data, dict) else None) or {}
        block_reason = feedback.get("blockReason")
        if block_reason:
            raise GeminiBlockedError(block_reason)
        raise RuntimeError(
            f"Gemini API: candidates が空 (status={resp.status_code}, body={str(data)[:300]})"
        )

    cand = candidates[0] or {}
    parts = (cand.get("content") or {}).get("parts")
    if not parts:
        finish = cand.get("finishReason", "")
        raise RuntimeError(f"Gemini API: 応答テキストが空 (finishReason={finish})")

    return parts[0].get("text", "")


# ---------------------------------------------------------------------------
# Gemini AI 解析（画像）
# ---------------------------------------------------------------------------
def analyze_image_with_gemini(image_bytes: bytes, api_key: str, correction_hint: str = "",
                              ocr_hint: str = "") -> dict | None:
    """Gemini 2.0 Flash で画像を解析し、結果辞書を返す。

    correction_hint が指定された場合、プロンプトに修正指示を追加する。
    ocr_hint には事前にOCR抽出したテキストを渡すとタイトル/キーワード精度が上がる。
    """
    try:
        # 画像の MIME タイプを判定
        pil_image = Image.open(io.BytesIO(image_bytes))
        fmt = pil_image.format or "PNG"
        mime_type = f"image/{fmt.lower()}"
        if mime_type == "image/jpg":
            mime_type = "image/jpeg"
        b64_data = base64.b64encode(image_bytes).decode("utf-8")

        prompt = ANALYSIS_PROMPT
        if ocr_hint.strip():
            # OCR テキストを参考情報として渡す（長すぎる場合は切り詰め）
            ocr_excerpt = ocr_hint.strip()
            if len(ocr_excerpt) > 4000:
                ocr_excerpt = ocr_excerpt[:4000] + "...(以下略)"
            prompt += (
                "\n\n【参考：画像内テキスト（OCR抽出）】\n"
                "以下は画像から自動抽出したテキストです。タイトルやキーワード生成の参考にしてください。"
                "誤読が含まれる可能性があるので、画像本体の情報を優先してください。\n"
                f"---\n{ocr_excerpt}\n---"
            )
        if correction_hint.strip():
            prompt += (
                "\n\n【修正指示】\n"
                "前回の解析で以下の問題が指摘されました。この指示を最優先で反映してください：\n"
                f"{correction_hint.strip()}"
            )

        parts = [
            {"text": prompt},
            {"inline_data": {"mime_type": mime_type, "data": b64_data}},
        ]
        response_text = _gemini_generate(api_key, parts).strip()

        # ```json ... ``` コードブロック対応
        if response_text.startswith("```"):
            lines = response_text.split("\n")
            json_lines = []
            inside_block = False
            for line in lines:
                if line.startswith("```") and not inside_block:
                    inside_block = True
                    continue
                elif line.startswith("```") and inside_block:
                    break
                elif inside_block:
                    json_lines.append(line)
            response_text = "\n".join(json_lines)

        result = json.loads(response_text)
        required_keys = {"title", "keywords"}
        if not required_keys.issubset(result.keys()):
            st.warning("AI解析の結果に必要な項目が不足しています。再度お試しください。")
            return None
        # 要約は使わないので念のため落としておく
        result.pop("summary", None)
        result["status"] = STATUS_AUTO
        return result

    except GeminiBlockedError:
        # 永続ブロックは呼び出し側でスキップマーカーを登録するため伝播させる
        raise
    except json.JSONDecodeError:
        st.error("AI解析の結果をJSONとして解析できませんでした。再度お試しください。")
        return None
    except Exception as e:
        _log.error(f"AI解析エラー: {e}")
        st.error(f"AI解析中にエラーが発生しました: {e}")
        return None


# ---------------------------------------------------------------------------
# 食事画像: 品目名のみ抽出（カロリー/栄養素は扱わない）
# ---------------------------------------------------------------------------
_FOOD_ITEM_NAME_PROMPT = """この食事の画像に写っている料理・食品の名前だけを日本語で抽出してください。
カロリー、栄養素、量などは一切不要です。料理名・食品名のみを以下のJSON形式で返してください。
複数の料理が写っている場合は全て列挙してください。
JSON以外のテキストは含めないでください。

出力形式:
{"items": ["品目1", "品目2"]}

例: {"items": ["ご飯", "焼き鮭", "味噌汁"]}
"""


def extract_food_item_names(image_bytes: bytes, api_key: str) -> list[str]:
    """食事画像から品目名のみ抽出する。失敗時は空リスト。"""
    try:
        pil_image = Image.open(io.BytesIO(image_bytes))
        fmt = pil_image.format or "PNG"
        mime_type = f"image/{fmt.lower()}"
        if mime_type == "image/jpg":
            mime_type = "image/jpeg"
        b64_data = base64.b64encode(image_bytes).decode("utf-8")
        parts = [
            {"text": _FOOD_ITEM_NAME_PROMPT},
            {"inline_data": {"mime_type": mime_type, "data": b64_data}},
        ]
        response_text = _gemini_generate(api_key, parts)
        parsed = _parse_gemini_json(response_text) or {}
        items = parsed.get("items", [])
        return [str(x).strip() for x in items if str(x).strip()]
    except Exception as e:
        _log.warning(f"[food item extract] 失敗: {e}")
        return []


# ---------------------------------------------------------------------------
# 体重管理 AI 解析
# ---------------------------------------------------------------------------
def _parse_gemini_json(response_text: str) -> dict | None:
    """Gemini レスポンスから JSON を抽出してパースする。"""
    text = response_text.strip()
    if text.startswith("```"):
        lines = text.split("\n")
        json_lines = []
        inside = False
        for line in lines:
            if line.startswith("```") and not inside:
                inside = True
                continue
            elif line.startswith("```") and inside:
                break
            elif inside:
                json_lines.append(line)
        text = "\n".join(json_lines)
    return json.loads(text)


def _generate_weight_comment(day_data: dict, goals: dict) -> str:
    """目標に対する日次コメントを生成する（ルールベース）。"""
    comments = []
    target_wt = goals.get("target_weight_kg")
    target_date_str = goals.get("target_date")
    weight = day_data.get("weight")

    if target_wt and target_wt > 0 and weight:
        wt_diff = round(weight - target_wt, 1)
        if wt_diff > 0:
            comments.append(f"目標体重まであと **{wt_diff} kg** です。")
        elif wt_diff == 0:
            comments.append("🎉 目標体重を達成しています！")
        else:
            comments.append(f"🎉 目標体重を **{abs(wt_diff)} kg** 下回っています！")

    if target_date_str:
        try:
            target_dt = datetime.strptime(target_date_str, "%Y-%m-%d").date()
            remaining_days = (target_dt - date.today()).days
            if remaining_days > 0:
                comments.append(f"目標期日まであと **{remaining_days}日** です。")
                if weight and target_wt and weight > target_wt:
                    need_loss = round(weight - target_wt, 1)
                    daily_loss = round(need_loss / remaining_days, 2)
                    comments.append(f"1日あたり約 **{daily_loss} kg** のペースが必要です。")
            elif remaining_days == 0:
                comments.append("今日が目標期日です！")
            else:
                comments.append(f"⚠️ 目標期日を **{abs(remaining_days)}日** 過ぎています。")
        except (ValueError, TypeError):
            pass

    if not comments:
        comments.append("🎯 目標体重を設定すると進捗コメントが表示されます。")

    return "  \n".join(comments)


def _extract_exif_datetime(image_bytes: bytes) -> datetime | None:
    """画像のEXIFから撮影日時を取得する。"""
    try:
        img = Image.open(io.BytesIO(image_bytes))
        exif = img._getexif()
        if exif is None:
            return None
        # 36867 = DateTimeOriginal, 36868 = DateTimeDigitized
        for tag_id in (36867, 36868):
            dt_str = exif.get(tag_id)
            if dt_str:
                return datetime.strptime(dt_str, "%Y:%m:%d %H:%M:%S")
    except (AttributeError, ValueError, OSError):
        pass
    return None


def _get_day_items(day_data: dict) -> list[dict]:
    """新旧どちらのデータ形式でも品目リストを返す。

    新形式: day_data["items"] — フラットな品目リスト
    旧形式: day_data["meals"] — 食事単位のリスト → 展開してフラット化
    quantityがないデータには "ふつう" を補完する。
    """
    if "items" in day_data:
        items = day_data["items"]
    else:
        # 旧形式: meals[] から展開
        items = []
        for meal in day_data.get("meals", []):
            # 画像情報を取得（複数画像対応 + 旧形式互換）
            meal_images = meal.get("images", [])
            if not meal_images:
                old_id = meal.get("image_id")
                if old_id:
                    meal_images = [{"id": old_id, "ext": meal.get("image_ext", "png")}]
            img = meal_images[0] if meal_images else {}
            for it in meal.get("items", []):
                item = {"name": it["name"], "calories": it["calories"]}
                if img:
                    item["image_id"] = img.get("id", "")
                    item["image_ext"] = img.get("ext", "png")
                items.append(item)
    # quantity 補完（旧データ互換）
    for it in items:
        if "quantity" not in it:
            it["quantity"] = "ふつう"
    return items


_NDLOCR_AVAILABLE: bool | None = None  # None=未確認, True/False=確認済み
_NDLOCR_ARGS_TEMPLATE = None  # argparse.Namespace のテンプレ（初回呼び出し時に構築）
_NDLOCR_MODEL_CACHE: dict = {}  # ('detector'|'recognizer', weights_path, device) -> インスタンス
_NDLOCR_PATCHED = False


def _patch_ndlocr_model_cache():
    """ocr.get_detector / ocr.get_recognizer をモンキーパッチして
    検出器・認識器のロード結果をキャッシュする（毎回 15 秒のロードを回避）。"""
    global _NDLOCR_PATCHED
    if _NDLOCR_PATCHED:
        return
    try:
        import ocr as _ocr_mod
    except Exception:
        return
    orig_get_detector = _ocr_mod.get_detector
    orig_get_recognizer = _ocr_mod.get_recognizer

    def cached_get_detector(args):
        key = ("detector", getattr(args, "det_weights", ""), getattr(args, "device", "cpu"))
        if key not in _NDLOCR_MODEL_CACHE:
            _NDLOCR_MODEL_CACHE[key] = orig_get_detector(args)
        return _NDLOCR_MODEL_CACHE[key]

    def cached_get_recognizer(args, weights_path=None):
        wp = weights_path or getattr(args, "rec_weights", "")
        key = ("recognizer", wp, getattr(args, "device", "cpu"))
        if key not in _NDLOCR_MODEL_CACHE:
            if weights_path:
                _NDLOCR_MODEL_CACHE[key] = orig_get_recognizer(args=args, weights_path=weights_path)
            else:
                _NDLOCR_MODEL_CACHE[key] = orig_get_recognizer(args=args)
        return _NDLOCR_MODEL_CACHE[key]

    _ocr_mod.get_detector = cached_get_detector
    _ocr_mod.get_recognizer = cached_get_recognizer
    _NDLOCR_PATCHED = True


def _ndlocr_available() -> bool:
    """NDLOCR-Lite (ocr モジュール) が import 可能か返す（結果はキャッシュ）。"""
    global _NDLOCR_AVAILABLE
    if _NDLOCR_AVAILABLE is not None:
        return _NDLOCR_AVAILABLE
    try:
        import ocr  # noqa: F401
        _NDLOCR_AVAILABLE = True
        _patch_ndlocr_model_cache()
    except Exception:
        _NDLOCR_AVAILABLE = False
    return _NDLOCR_AVAILABLE


def _build_ndlocr_args(sourceimg: str, output_dir: str):
    """NDLOCR-Lite ocr.process() に渡す argparse.Namespace を組み立てる。"""
    global _NDLOCR_ARGS_TEMPLATE
    import argparse
    import ocr as _ocr_mod
    if _NDLOCR_ARGS_TEMPLATE is None:
        base = Path(_ocr_mod.__file__).parent
        _NDLOCR_ARGS_TEMPLATE = {
            "det_weights": str(base / "model" / "deim-s-1024x1024.onnx"),
            "det_classes": str(base / "config" / "ndl.yaml"),
            "det_score_threshold": 0.2,
            "det_conf_threshold": 0.25,
            "det_iou_threshold": 0.2,
            "simple_mode": False,
            "rec_weights30": str(base / "model" / "parseq-ndl-16x256-30-tiny-192epoch-tegaki3.onnx"),
            "rec_weights50": str(base / "model" / "parseq-ndl-16x384-50-tiny-146epoch-tegaki2.onnx"),
            "rec_weights": str(base / "model" / "parseq-ndl-16x768-100-tiny-165epoch-tegaki2.onnx"),
            "rec_classes": str(base / "config" / "NDLmoji.yaml"),
            "device": "cpu",
            "viz": False,
        }
    return argparse.Namespace(
        sourcedir=None,
        sourceimg=sourceimg,
        output=output_dir,
        **_NDLOCR_ARGS_TEMPLATE,
    )


def _extract_ocr_text_ndlocr(image_bytes: bytes) -> str:
    """NDLOCR-Lite で画像内テキストを抽出。失敗時は空文字。

    バイト列を tempfile に書き出し → ocr.process() で OCR → 出力 .txt を読む。
    """
    if not _ndlocr_available():
        return ""
    import tempfile
    import ocr as _ocr_mod
    # 画像形式判定（NDLOCR は JPG/PNG/TIFF/JP2/BMP 対応）
    try:
        pil_image = Image.open(io.BytesIO(image_bytes))
        ext = (pil_image.format or "PNG").lower()
        if ext == "jpeg":
            ext = "jpg"
        if ext not in ("jpg", "png", "tiff", "tif", "jp2", "bmp"):
            # 未対応形式は PNG に正規化
            buf = io.BytesIO()
            pil_image.convert("RGB").save(buf, format="PNG")
            image_bytes = buf.getvalue()
            ext = "png"
    except Exception:
        ext = "png"

    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)
        in_path = tdp / f"in.{ext}"
        out_dir = tdp / "out"
        out_dir.mkdir(exist_ok=True)
        in_path.write_bytes(image_bytes)
        args = _build_ndlocr_args(str(in_path), str(out_dir))
        try:
            _ocr_mod.process(args)
        except Exception as e:
            _log.warning(f"[ndlocr] process失敗: {e}")
            return ""
        # 出力 .txt を探して読む（in.txt またはサブディレクトリ内）
        texts: list[str] = []
        for txt in out_dir.rglob("*.txt"):
            try:
                t = txt.read_text(encoding="utf-8", errors="replace").strip()
                if t:
                    texts.append(t)
            except Exception:
                continue
        return "\n".join(texts).strip()


def extract_ocr_text(image_bytes: bytes, api_key: str) -> str:
    """画像内のテキストをOCR抽出する。NDLOCR-Lite 優先・Gemini フォールバック。

    臨床画像（教科書、スライド、検査レポート等）に含まれるテキストを読み取り、
    プレーンテキストとして返す。テキストがない場合やエラー時は空文字を返す。
    """
    # 1) NDLOCR-Lite が使えればそちらを使う
    if _ndlocr_available():
        try:
            txt = _extract_ocr_text_ndlocr(image_bytes)
            if txt:
                return txt
        except Exception as e:
            _log.warning(f"[ocr] NDLOCR失敗、Geminiフォールバック: {e}")

    # 2) Gemini フォールバック
    try:
        pil_image = Image.open(io.BytesIO(image_bytes))
        fmt = pil_image.format or "PNG"
        mime_type = f"image/{fmt.lower()}"
        if mime_type == "image/jpg":
            mime_type = "image/jpeg"
        b64_data = base64.b64encode(image_bytes).decode("utf-8")

        parts = [
            {"text": OCR_EXTRACT_PROMPT},
            {"inline_data": {"mime_type": mime_type, "data": b64_data}},
        ]
        result = _gemini_generate(api_key, parts).strip()
        return result
    except Exception as e:
        _log.error(f"OCRテキスト抽出エラー: {e}")
        return ""


# ---------------------------------------------------------------------------
# 新着画像の自動検知 & AI解析
# ---------------------------------------------------------------------------
AUTO_SCAN_INTERVAL = 300  # 秒（5分おき）


def _analyze_and_register_screenshot(service, fid: str, api_key: str,
                                     metadata: dict) -> dict | None:
    """1枚のスクショ画像をAI解析し metadata に登録する。失敗時 None。

    フロー: ① OCR(NDLOCR-Lite優先) → ② OCRテキストを文脈として Gemini で
    タイトル/キーワード生成 → ③ ocr_text を full-text 検索用に保存。
    呼び出し側で save_metadata を一括実行する想定。
    """
    try:
        image_bytes = download_image(service, fid)
    except Exception as e:
        _log.error(f"画像ダウンロード失敗 fid={fid}: {e}")
        return None

    # 取り込み時に即サムネを生成（後の表示を瞬時にする）
    try:
        _save_ss_thumb(fid, image_bytes)
    except Exception:
        pass

    # ① 先に OCR テキストを抽出
    ocr_text = ""
    try:
        ocr_text = extract_ocr_text(image_bytes, api_key)
    except Exception as e:
        _log.warning(f"[analyze] OCR失敗 fid={fid}: {e}")

    # ② OCR テキストを参考情報として Gemini にタイトル/キーワードを生成させる
    result = analyze_image_with_gemini(image_bytes, api_key, ocr_hint=ocr_text)
    if not result:
        return None
    result["status"] = STATUS_REVIEWED
    result["folder"] = DEFAULT_FOLDER

    # ③ OCR テキストは全文検索用に保存（UI には表示しない）
    if ocr_text:
        result["ocr_text"] = ocr_text

    metadata[fid] = result
    return result


def auto_scan_new_images(service, folder_id: str, api_key: str) -> None:
    """Google Driveの新着画像を検知し、自動でAI解析・認証・フォルダ分類まで行う。

    5分間隔でチェックし、未解析の画像があればバックグラウンド的に解析する。
    自動取り込み画像は認証手続き（レビュー）を省略し、既存フォルダへ自動分類する。
    患者データフォルダを先にスキャンし、メインフォルダのスキャンと重複しないようにする。
    """
    if not api_key:
        return

    now = time.time()
    last_scan = st.session_state.get("auto_scan_last", 0)
    if now - last_scan < AUTO_SCAN_INTERVAL:
        return  # クールダウン中

    st.session_state["auto_scan_last"] = now

    # キャッシュをクリアして最新の Drive 状態を取得
    list_images.clear()
    list_patient_images.clear()

    # 一度に解析する上限（タイムアウト防止）
    MAX_AUTO_ANALYZE = 5

    # --- ★ 患者データフォルダを先にスキャン（AI解析なし） ---
    patient_registered_ids: set[str] = set()
    patient_folder_id = get_patient_folder_id()
    if patient_folder_id:
        try:
            mime_query_p = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
            query_p = f"'{patient_folder_id}' in parents and ({mime_query_p}) and trashed=false"
            results_p = (
                service.files()
                .list(q=query_p, fields="files(id, name, mimeType)", pageSize=100)
                .execute()
            )
            patient_images = results_p.get("files", [])
        except Exception:
            patient_images = []

        # 患者データフォルダにあるファイルIDを記録（メインスキャンで除外用）
        patient_registered_ids = {img["id"] for img in patient_images}

        metadata = load_metadata()
        new_patient = [img for img in patient_images if img["id"] not in metadata]

        if new_patient:
            folders = load_folders()
            if PATIENT_DATA_FOLDER not in folders:
                folders.append(PATIENT_DATA_FOLDER)
                save_folders(folders)

            p_count = 0
            for img in new_patient[:MAX_AUTO_ANALYZE]:
                fid = img["id"]
                fname = img.get("name", fid)
                metadata[fid] = {
                    "title": fname,
                    "summary": "",
                    "keywords": [],
                    "status": STATUS_REVIEWED,
                    "folder": PATIENT_DATA_FOLDER,
                    "source": SOURCE_PATIENT_DATA,
                }
                p_count += 1
            if p_count > 0:
                save_metadata(metadata)
                _invalidate_all_caches()
                st.toast(
                    f"🏥 患者データ {p_count} 件を自動登録しました",
                    icon="🏥",
                )

    # --- メインフォルダの新着画像スキャン ---
    try:
        mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
        query = f"'{folder_id}' in parents and ({mime_query}) and trashed=false"
        results = (
            service.files()
            .list(
                q=query,
                fields="files(id, name, mimeType)",
                pageSize=100,
            )
            .execute()
        )
        drive_images = results.get("files", [])
    except Exception:
        return

    if drive_images:
        metadata = load_metadata()
        # 患者データフォルダにあるファイルはメインスキャンから除外
        new_images = [
            img for img in drive_images
            if img["id"] not in metadata
            and img["id"] not in patient_registered_ids
        ]

        if new_images:
            batch = new_images[:MAX_AUTO_ANALYZE]
            remaining = len(new_images) - len(batch)

            success_count = 0
            for img in batch:
                fid = img["id"]
                try:
                    if _analyze_and_register_screenshot(service, fid, api_key, metadata):
                        success_count += 1
                except Exception:
                    continue

            if success_count > 0:
                save_metadata(metadata)
                _invalidate_all_caches()
                list_images.clear()
                list_patient_images.clear()
                msg = f"✅ 新着 {success_count} 件を自動登録"
                if remaining > 0:
                    msg += f"（残り {remaining} 件は次回処理）"
                st.toast(msg, icon="✅")


def _run_manual_scan(service, folder_id: str, api_key: str) -> None:
    """手動スキャン: メイン画面にリアルタイム進捗を表示しながら新着画像を解析する。

    患者データフォルダを先にスキャンし、メインフォルダとの重複を防ぐ。
    """
    st.markdown("---")
    st.subheader("🔄 新着画像スキャン")

    status_text = st.empty()
    status_text.info("📡 Google Drive を確認中...")

    # キャッシュをクリアして最新の Drive 状態を取得
    list_images.clear()
    list_patient_images.clear()

    # --- ★ 患者データフォルダを先にスキャン（AI解析なし） ---
    patient_registered_ids: set[str] = set()
    patient_folder_id = get_patient_folder_id()
    if patient_folder_id:
        try:
            mime_query_p = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
            query_p = f"'{patient_folder_id}' in parents and ({mime_query_p}) and trashed=false"
            results_p = (
                service.files()
                .list(q=query_p, fields="files(id, name, mimeType)", pageSize=100)
                .execute()
            )
            patient_images = results_p.get("files", [])
        except Exception:
            patient_images = []

        # 患者データフォルダにあるファイルIDを記録（メインスキャンで除外用）
        patient_registered_ids = {img["id"] for img in patient_images}

        metadata = load_metadata()
        new_patient = [img for img in patient_images if img["id"] not in metadata]

        if new_patient:
            folders = load_folders()
            if PATIENT_DATA_FOLDER not in folders:
                folders.append(PATIENT_DATA_FOLDER)
                save_folders(folders)

            p_count = 0
            for img in new_patient:
                fid = img["id"]
                fname = img.get("name", fid)
                metadata[fid] = {
                    "title": fname,
                    "summary": "",
                    "keywords": [],
                    "status": STATUS_REVIEWED,
                    "folder": PATIENT_DATA_FOLDER,
                    "source": SOURCE_PATIENT_DATA,
                }
                p_count += 1
            if p_count > 0:
                save_metadata(metadata)
                _invalidate_all_caches()
                st.success(f"🏥 患者データ {p_count} 件を登録しました（AI解析なし・手動入力用）")

    # --- メインフォルダの新着画像スキャン ---
    try:
        mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
        query = f"'{folder_id}' in parents and ({mime_query}) and trashed=false"
        results = (
            service.files()
            .list(
                q=query,
                fields="files(id, name, mimeType)",
                pageSize=100,
            )
            .execute()
        )
        drive_images = results.get("files", [])
    except Exception as e:
        status_text.error(f"⚠️ Google Drive への接続に失敗しました: {e}")
        return

    metadata = load_metadata()
    # 患者データフォルダにあるファイルはメインスキャンから除外
    new_images = [
        img for img in drive_images
        if img["id"] not in metadata
        and img["id"] not in patient_registered_ids
    ]

    if not new_images:
        status_text.success("✅ 新着画像はありません。すべて解析済みです。")
        st.caption(f"Google Drive: {len(drive_images)} 件 / 解析済み: {len(metadata)} 件")
    else:
        status_text.info(
            f"🆕 新着 **{len(new_images)}** 件を検出！ AI解析・自動登録を開始します..."
        )

        progress_bar = st.progress(0, text="準備中...")
        results_container = st.container()
        success_count = 0
        fail_count = 0
        total = len(new_images)

        for i, img in enumerate(new_images):
            fid = img["id"]
            fname = img.get("name", fid)

            progress_bar.progress(
                (i) / total,
                text=f"解析中... ({i + 1}/{total}) {fname}",
            )

            try:
                result = _analyze_and_register_screenshot(service, fid, api_key, metadata)
                if result:
                    success_count += 1
                    with results_container:
                        st.markdown(
                            f"✅ **{html.escape(result.get('title', fname))}**  \n"
                            f"<span style='color:#b0b0b0;font-size:12px;'>"
                            f"{', '.join(html.escape(k) for k in result.get('keywords', [])[:4])}</span>",
                            unsafe_allow_html=True,
                        )
                else:
                    fail_count += 1
                    with results_container:
                        st.markdown(f"⚠️ {fname} — 解析失敗")
            except Exception as e:
                fail_count += 1
                with results_container:
                    st.markdown(f"⚠️ {fname} — エラー: {e}")

        progress_bar.progress(1.0, text="完了！ Sheets に保存中...")

        if success_count > 0:
            # API Rate Limit 回避のため少し待機
            time.sleep(2)
            sheets_ok = save_metadata(metadata)
            _invalidate_all_caches()
            list_images.clear()
            list_patient_images.clear()
            if sheets_ok:
                sync_msg = "（Google Sheets に同期済み）"
            else:
                detail = st.session_state.pop("_save_error_detail", "不明")
                sync_msg = f"（⚠️ Sheets同期失敗: {detail}）"
            status_text.success(
                f"🎉 スキャン完了！ **{success_count}** 件を新しく解析しました{sync_msg}"
                + (f"（{fail_count} 件失敗）" if fail_count else "")
            )
            st.balloons()
        else:
            status_text.warning("⚠️ 新着画像の解析に失敗しました。再度お試しください。")


# ---------------------------------------------------------------------------
# Google Drive 食事画像自動取り込み
# ---------------------------------------------------------------------------


def scan_food_images(service, food_folder_id: str, api_key: str | None = None,
                     manual: bool = False) -> int:
    """Google Driveの食事画像フォルダをスキャンし、未処理画像をローカルに取り込む。

    api_key があれば Gemini で品目名のみ抽出する（カロリー/栄養素は扱わない）。
    api_key=None なら品目名抽出はスキップし、ファイル名のみ保存。
    """
    if st.session_state.get("_food_scan_running"):
        return 0
    st.session_state["_food_scan_running"] = True
    try:
        return _scan_food_images_inner(service, food_folder_id, manual, api_key)
    finally:
        st.session_state["_food_scan_running"] = False


def _scan_food_images_inner(service, food_folder_id: str,
                            manual: bool = False,
                            api_key: str | None = None) -> int:
    """scan_food_images の内部実装（品目名のみ AI 抽出、カロリー/栄養素なし）。"""
    if not manual:
        now = time.time()
        last_scan = st.session_state.get("food_scan_last", 0)
        if now - last_scan < FOOD_SCAN_INTERVAL:
            return 0
        st.session_state["food_scan_last"] = now

    processed = load_food_processed()

    all_files: list[dict] = []
    try:
        mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
        query = f"'{food_folder_id}' in parents and ({mime_query}) and trashed=false"
        _page_token = None
        while True:
            params = dict(
                q=query,
                fields="nextPageToken, files(id, name, mimeType, createdTime, modifiedTime)",
                orderBy="modifiedTime desc",
                pageSize=100,
            )
            if _page_token:
                params["pageToken"] = _page_token
            results = service.files().list(**params).execute()
            all_files.extend(results.get("files", []))
            _page_token = results.get("nextPageToken")
            if not _page_token:
                break
    except Exception as e:
        if manual:
            _log.error(f"Google Drive読み取り失敗: {e}")
            st.error("Google Driveの読み取りに失敗しました。")
        if not all_files:
            return 0

    new_files = [f for f in all_files if f["id"] not in processed]
    if not new_files:
        return 0

    _MANUAL_SCAN_LIMIT = 30
    _total_candidates = len(new_files)
    if manual:
        new_files = new_files[:_MANUAL_SCAN_LIMIT]
    else:
        new_files = new_files[:MAX_FOOD_SCAN_IMAGES]

    weight_data = load_weight_data()
    records = weight_data.setdefault("records", {})

    _progress = None
    _progress_text = None
    if manual:
        _progress_text = st.empty()
        _progress = st.progress(0.0)
        _progress_text.caption(
            f"📷 {len(new_files)} / {_total_candidates} 枚を処理中…"
        )

    count = 0
    for _idx, file_info in enumerate(new_files):
        if _progress is not None:
            _progress.progress((_idx) / max(len(new_files), 1))
        file_id = file_info["id"]
        file_name = file_info.get("name", file_id)

        try:
            img_bytes = download_image(service, file_id)
            if not img_bytes:
                continue

            photo_dt = _extract_exif_datetime(img_bytes)
            if photo_dt is None:
                mod_time_str = file_info.get("modifiedTime", "")
                if mod_time_str:
                    try:
                        photo_dt = datetime.fromisoformat(
                            mod_time_str.replace("Z", "+00:00")
                        )
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
            # 取り込み時に即サムネを生成しておく（後の表示を瞬時にする）
            _save_food_thumb(img_id, img_bytes)

            day_data = records.setdefault(date_key, {"items": []})
            existing_fids = {x.get("drive_file_id") for x in day_data.get("items", [])}
            if file_id not in existing_fids:
                item_names: list[str] = []
                if api_key:
                    item_names = extract_food_item_names(img_bytes, api_key)
                display_name = "・".join(item_names) if item_names else file_name
                day_data.setdefault("items", []).append({
                    "id": f"item_{uuid.uuid4().hex[:12]}",
                    "name": display_name,
                    "items_extracted": item_names,
                    "image_id": img_id,
                    "image_ext": ext,
                    "drive_file_id": file_id,
                })
                count += 1

            processed[file_id] = {
                "date": date_key,
                "file_name": file_name,
                "processed_at": datetime.now().isoformat(),
                "status": "ok",
            }

        except Exception as e:
            if manual:
                _log.error(f"ファイル処理失敗 {file_name}: {e}")
                st.warning(f"⚠️ {html.escape(file_name)} の処理に失敗しました。")
            processed[file_id] = {
                "date": "",
                "file_name": file_name,
                "processed_at": datetime.now().isoformat(),
                "status": "error",
                "error": str(e),
            }

    if count > 0:
        save_weight_data(weight_data)
    save_food_processed(processed)

    if _progress is not None:
        _progress.progress(1.0)
        _progress.empty()
    if _progress_text is not None:
        if manual and _total_candidates > len(new_files):
            _progress_text.info(
                f"✅ {len(new_files)} 枚を処理しました（残り {_total_candidates - len(new_files)} 枚は次回クリックで処理）"
            )
        else:
            _progress_text.empty()

    return count


# ---------------------------------------------------------------------------
# 検索フィルタリング
# ---------------------------------------------------------------------------
def render_summary(summary: str) -> None:
    """要約テキストを箇条書きとして整形表示する。"""
    if not summary:
        return
    # "\\n" リテラルを実改行に
    text = summary.replace("\\n", "\n")
    # 「• 」「・」の前で改行を挿入（1行に詰まっている場合の分割用）
    # ただし「• 【」のようにセットの場合はまとめて1項目にする
    text = re.sub(r"\s*[•・]\s*【", "\n【", text)
    text = re.sub(r"\s*[•・]\s*", "\n", text)

    lines = [ln.strip() for ln in text.split("\n") if ln.strip()]
    md_lines = []
    for ln in lines:
        # 先頭の残った記号を除去
        clean = re.sub(r"^[•・\-]\s*", "", ln)
        if not clean:
            continue
        md_lines.append(f"- {clean}")
    st.markdown("\n".join(md_lines))


# UI部品: キーワードタグ表示
# ---------------------------------------------------------------------------
def render_keyword_tags(keywords: list[str]) -> None:
    """キーワードをタグ形式で表示する。"""
    if not keywords:
        return
    tag_html = " ".join(
        f'<span style="background-color:#1a5276; color:#d6eaf8; padding:4px 12px; '
        f'border-radius:16px; margin:2px 4px; display:inline-block; '
        f'font-size:0.9em; border:1px solid #2980b9;">{html.escape(kw)}</span>'
        for kw in keywords
    )
    st.markdown(tag_html, unsafe_allow_html=True)


# ---------------------------------------------------------------------------
# UI部品: チェックボックス一括選択ヘルパー
# ---------------------------------------------------------------------------
def _apply_batch_checkbox(batch_key: str, items_keys: list[str]) -> None:
    """ボタンで設定されたバッチ選択フラグを、チェックボックス描画前に適用する。

    batch_key: session_state に保存されたフラグのキー
    items_keys: 対象チェックボックスのキー一覧
    """
    batch_val = st.session_state.pop(batch_key, None)
    if batch_val is None:
        return
    if isinstance(batch_val, dict):
        for k in items_keys:
            st.session_state[k] = batch_val.get(k, False)
    else:
        for k in items_keys:
            st.session_state[k] = bool(batch_val)


def _set_batch_checkbox(batch_key: str, value) -> None:
    """バッチ選択フラグをセットして rerun する。"""
    st.session_state[batch_key] = value
    st.rerun()


# ---------------------------------------------------------------------------
# UI部品: ページネーション
# ---------------------------------------------------------------------------
def _paginate(items: list, page_key: str, per_page: int = IMAGES_PER_PAGE) -> tuple[list, int, int]:
    """リストをページ分割し、現在ページの要素・現在ページ番号・総ページ数を返す。

    page_key: session_state に保存するページ番号のキー名。
    戻り値: (現在ページの要素リスト, 現在ページ番号(0始まり), 総ページ数)
    """
    total = len(items)
    if total == 0:
        return [], 0, 0
    total_pages = max(1, (total + per_page - 1) // per_page)
    current = st.session_state.get(page_key, 0)
    if current >= total_pages:
        current = total_pages - 1
    if current < 0:
        current = 0
    st.session_state[page_key] = current
    start = current * per_page
    end = min(start + per_page, total)
    return items[start:end], current, total_pages


def _render_pagination_controls(page_key: str, current: int, total_pages: int, total_items: int) -> None:
    """ページ送りボタンを描画する。"""
    if total_pages <= 1:
        st.caption(f"全 {total_items} 件")
        return
    nav1, nav2, nav3 = st.columns([1, 2, 1])
    with nav1:
        if st.button("⬅️ 前へ", disabled=(current == 0), key=f"{page_key}_prev"):
            st.session_state[page_key] = current - 1
            st.rerun()
    with nav2:
        st.markdown(
            f"<div style='text-align:center;'>ページ <b>{current + 1}</b> / {total_pages}（全 {total_items} 件）</div>",
            unsafe_allow_html=True,
        )
    with nav3:
        if st.button("次へ ➡️", disabled=(current >= total_pages - 1), key=f"{page_key}_next"):
            st.session_state[page_key] = current + 1
            st.rerun()


# ---------------------------------------------------------------------------
# UI部品: 表示件数・ソート選択
# ---------------------------------------------------------------------------
_SORT_OPTIONS = ["新しい順", "古い順", "タイトル順"]


def _render_display_options(
    page_key: str, per_page_key: str, sort_key: str
) -> tuple[int, str]:
    """表示件数と並び順の selectbox を横並びで描画し、(per_page, sort_order) を返す。

    件数 or 並び順が変更された場合はページ番号を 0 にリセットする。
    """
    col_pp, col_so = st.columns(2)
    with col_pp:
        per_page = st.selectbox(
            "表示件数",
            PER_PAGE_OPTIONS,
            index=PER_PAGE_OPTIONS.index(
                st.session_state.get(per_page_key, IMAGES_PER_PAGE)
            ),
            key=per_page_key,
        )
    with col_so:
        sort_order = st.selectbox(
            "並び順",
            _SORT_OPTIONS,
            index=_SORT_OPTIONS.index(
                st.session_state.get(sort_key, _SORT_OPTIONS[0])
            ),
            key=sort_key,
        )

    # 前回値と比較してページリセット
    prev_pp_key = f"_prev_{per_page_key}"
    prev_so_key = f"_prev_{sort_key}"
    prev_pp = st.session_state.get(prev_pp_key)
    prev_so = st.session_state.get(prev_so_key)

    if prev_pp is not None and prev_pp != per_page:
        st.session_state[page_key] = 0
    if prev_so is not None and prev_so != sort_order:
        st.session_state[page_key] = 0

    st.session_state[prev_pp_key] = per_page
    st.session_state[prev_so_key] = sort_order

    return per_page, sort_order


def _sort_images(
    images: list, sort_order: str, metadata: dict
) -> list:
    """画像リストを指定の並び順でソートして返す（元リストは変更しない）。

    - "新しい順": modifiedTime 降順（デフォルト）
    - "古い順"  : modifiedTime 昇順
    - "タイトル順": metadata[id]["title"] の五十音順
    modifiedTime が無い画像は末尾に配置。
    """
    if sort_order == "タイトル順":
        def _title_key(img):
            m = metadata.get(img["id"], {})
            return m.get("title", img.get("name", ""))
        return sorted(images, key=_title_key)

    reverse = sort_order != "古い順"

    def _time_key(img):
        t = img.get("modifiedTime", "")
        return t if t else ("" if reverse else "9999")

    return sorted(images, key=_time_key, reverse=reverse)


# ---------------------------------------------------------------------------
# UI部品: 編集フォーム
# ---------------------------------------------------------------------------
def display_edit_form(file_id: str, meta: dict, metadata: dict) -> None:
    """解析結果の編集フォームを表示し、保存処理を行う。"""
    st.markdown("---")

    _is_pd_edit = is_patient_data(meta)
    summary_label = get_summary_label(meta)

    status = get_status(meta)
    if _is_pd_edit:
        st.info("🏥 患者データ — 検査所見を手動で入力してください")
    elif status == STATUS_REVIEWED:
        st.success("✅ 確認済み")
    else:
        st.warning("📝 未確認 — AIが自動生成した情報です。内容を確認・修正してください")

    # 前回保存結果の通知（rerun後に表示）
    if st.session_state.pop(f"_saved_ok_{file_id}", False):
        st.success("✅ 保存しました！（Google Sheets に同期済み）")
    if st.session_state.pop(f"_saved_fail_{file_id}", False):
        err_detail = st.session_state.pop("_save_error_detail", "不明")
        _log.error(f"Sheets同期失敗: {err_detail}")
        st.error("⚠️ Google Sheets への同期に失敗しました。再度お試しください。")

    form_heading = "📝 検査所見の編集" if _is_pd_edit else "📝 解析結果の編集"
    st.subheader(form_heading)

    with st.form(key=f"edit_form_{file_id}"):
        edited_title = st.text_input(
            "タイトル",
            value=meta.get("title", ""),
            placeholder="画像のタイトルを入力...",
        )
        edited_summary = st.text_area(
            summary_label,
            value=meta.get("summary", ""),
            height=120,
            placeholder="検査所見を入力..." if _is_pd_edit else "医学的ポイントの要約を入力...",
        )
        edited_keywords_str = st.text_input(
            "キーワード（カンマ区切り）",
            value=", ".join(meta.get("keywords", [])),
            placeholder="例: 心筋梗塞, 心電図, ST上昇",
        )

        col_save, col_status = st.columns([1, 2])
        with col_save:
            save_btn_label = (
                "💾 保存して検査所見を確定する" if _is_pd_edit
                else "💾 保存して知識として確定する"
            )
            submitted = st.form_submit_button(
                save_btn_label,
                type="primary",
            )
        with col_status:
            if get_status(meta) == STATUS_REVIEWED:
                st.caption("ステータス: ✅ 確認済み")
            else:
                st.caption("ステータス: 📝 未確認")

    if submitted:
        new_keywords = [
            kw.strip()
            for kw in edited_keywords_str.split(",")
            if kw.strip()
        ]
        _log.info(f"[display_edit_form] submit: file_id={file_id}, edited_keywords_str='{edited_keywords_str}', new_keywords={new_keywords}")

        # 渡されたmetadata（現在のセッションのもの）を直接更新してsave
        # ※ load し直すとAPI呼び出しが増えレート制限に当たる可能性があるため
        existing = metadata.get(file_id, {})
        existing.update({
            "title": edited_title,
            "summary": edited_summary,
            "keywords": new_keywords,
            "status": STATUS_REVIEWED,
        })
        metadata[file_id] = existing
        try:
            sheets_ok = save_metadata(metadata)
        except Exception as e:
            sheets_ok = False
            st.session_state["_save_error_detail"] = f"save例外: {type(e).__name__}: {e}"
        _log.info(f"[display_edit_form] 保存完了: {file_id}, keywords={new_keywords}, sheets_ok={sheets_ok}")
        if sheets_ok:
            st.session_state[f"_saved_ok_{file_id}"] = True
        else:
            st.session_state[f"_saved_fail_{file_id}"] = True
        st.session_state.pop("editing_file_id", None)
        _invalidate_all_caches()
        st.rerun()


# ---------------------------------------------------------------------------
# 検索機能: 全文検索結果表示
# ---------------------------------------------------------------------------





# ===========================================================================
# Git 自動 push（バックグラウンド）
# ===========================================================================
_AUTO_PUSH_INTERVAL = 60  # 秒
_auto_push_started = False


def _auto_push_loop():
    """バックグラウンドで定期的に git commit & push を実行する。"""
    repo_dir = str(Path(__file__).parent)
    target_files = [
        "app.py", "requirements.txt", ".gitignore",
        "metadata.json", "weight_data.json", "food_images_processed.json",
    ]

    while True:
        time.sleep(_AUTO_PUSH_INTERVAL)
        try:
            # ファイル書き込みとの競合を防止（status/add/commit はロック内）
            with _file_write_lock:
                # 変更があるかチェック
                result = subprocess.run(
                    ["git", "status", "--porcelain"] + target_files,
                    cwd=repo_dir, capture_output=True, text=True, timeout=15,
                )
                if not result.stdout.strip():
                    continue  # 変更なし

                # git add
                subprocess.run(
                    ["git", "add"] + target_files,
                    cwd=repo_dir, capture_output=True, text=True, timeout=15,
                )

                # git commit
                timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                subprocess.run(
                    ["git", "commit", "-m", f"auto: {timestamp}"],
                    cwd=repo_dir, capture_output=True, text=True, timeout=30,
                )

            # git push はロック外（長時間かかるため）
            subprocess.run(
                ["git", "push", "origin", "main"],
                cwd=repo_dir, capture_output=True, text=True, timeout=60,
            )
        except Exception as e:
            _log.warning(f"[auto_push] エラー: {type(e).__name__}: {e}")


def _is_local_env() -> bool:
    """ローカル環境かどうかを判定する（Streamlit Cloud上では動かさない）。"""
    repo_dir = Path(__file__).parent
    if not (repo_dir / ".git").exists():
        return False
    try:
        result = subprocess.run(
            ["git", "status"],
            cwd=str(repo_dir), capture_output=True, text=True, timeout=5,
        )
        return result.returncode == 0
    except Exception:
        return False


def start_auto_push():
    """自動pushスレッドを1回だけ起動する（ローカル環境のみ）。"""
    global _auto_push_started
    if _auto_push_started:
        return
    _auto_push_started = True
    if not _is_local_env():
        return  # Streamlit Cloud等では何もしない
    t = threading.Thread(target=_auto_push_loop, daemon=True)
    t.start()


# ===========================================================================
# ローカル → Google Sheets 移行
# ===========================================================================
def _migrate_local_to_sheets():
    """ローカルJSONファイルからGoogle Sheetsにデータを一括移行する。"""
    sh = get_sheets_client()
    if sh is None:
        st.error("Google Sheets に接続できません。spreadsheet_id を確認してください。")
        return

    migrated = []
    # metadata
    if METADATA_PATH.exists():
        try:
            with open(METADATA_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if _write_json_to_sheet(sh, "metadata", data):
                migrated.append(f"metadata ({len(data)}件)")
        except Exception as e:
            st.warning(f"metadata移行失敗: {e}")
    # folders
    if FOLDERS_PATH.exists():
        try:
            with open(FOLDERS_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if _write_json_to_sheet(sh, "folders", data):
                migrated.append("folders")
        except Exception as e:
            st.warning(f"folders移行失敗: {e}")
    # weight_data
    if WEIGHT_DATA_PATH.exists():
        try:
            with open(WEIGHT_DATA_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if _write_json_to_sheet(sh, "weight_data", data):
                migrated.append("weight_data")
        except Exception as e:
            st.warning(f"weight_data移行失敗: {e}")

    if migrated:
        st.success(f"✅ 移行完了: {', '.join(migrated)}")
        # キャッシュクリア
        for ck in ["_cache_metadata", "_cache_folders", "_cache_weight_data"]:
            st.session_state.pop(ck, None)
            st.session_state.pop(f"{ck}_ts", None)
    else:
        st.warning("移行するローカルデータがありませんでした。")


# ===========================================================================
# 写真ギャラリー（Google Photos 風 — 患者データ / 食事画像）
# ===========================================================================
GALLERY_PAGE_SIZE = 60
GALLERY_COLS = 3
_MONTH_LABELS_JA = ["1月", "2月", "3月", "4月", "5月", "6月",
                    "7月", "8月", "9月", "10月", "11月", "12月"]
_WEEKDAY_LABELS_JA = ["月", "火", "水", "木", "金", "土", "日"]


def _inject_gallery_css():
    """Google Photos 風ギャラリーの CSS を注入する。"""
    st.markdown("""
    <style>
    .g-month {
        position: sticky; top: 0; z-index: 10;
        background: rgba(15,15,20,0.95);
        backdrop-filter: blur(6px);
        padding: 10px 4px 6px;
        font-size: 18px; font-weight: 700;
        color: #e0e0e0; border-bottom: 1px solid #333;
        margin: 12px 0 4px;
    }
    .g-day {
        font-size: 13px; color: #b0b0b0;
        padding: 8px 4px 4px; font-weight: 500;
    }
    .g-empty {
        text-align: center; padding: 60px 20px;
        color: #888; font-size: 14px;
    }
    .g-placeholder {
        aspect-ratio: 1/1; background: #2a2a2a;
        border-radius: 4px; display: flex;
        align-items: center; justify-content: center;
        color: #888; font-size: 24px;
    }
    .g-caption {
        font-size: 11px; color: #d0d0d0;
        padding: 2px 4px 0; margin-top: 2px;
        line-height: 1.35; max-height: 5.4em;
        overflow: hidden;
        display: -webkit-box; -webkit-line-clamp: 4;
        -webkit-box-orient: vertical;
        word-break: break-word;
    }
    .g-caption .g-chip {
        display: inline-block; margin: 1px 3px 1px 0;
        padding: 1px 6px; border-radius: 8px;
        background: rgba(255,122,60,0.15);
        color: #ffb27a; font-size: 10.5px;
        white-space: nowrap;
    }
    .g-badge {
        position: absolute; top: 4px; left: 4px;
        background: rgba(220,53,69,0.85);
        color: #fff; font-size: 10px;
        padding: 1px 6px; border-radius: 6px;
        z-index: 2;
        pointer-events: none;
    }
    .g-thumb-wrap { position: relative; }
    .g-search {
        margin: 4px 0 10px;
    }
    [data-testid="stHorizontalBlock"] { gap: 4px !important; }
    [data-testid="column"] { padding: 0 2px !important; }
    [data-testid="stHorizontalBlock"] [data-testid="stImage"] img {
        aspect-ratio: 1/1;
        object-fit: contain;
        background: #1a1a1a;
        border-radius: 4px;
    }
    @media (max-width: 600px) {
        [data-testid="stHorizontalBlock"] { flex-wrap: wrap !important; }
        [data-testid="column"] {
            flex: 0 0 50% !important;
            max-width: 50% !important;
        }
    }
    @media (min-width: 1200px) {
        [data-testid="column"] {
            flex: 0 0 25% !important;
            max-width: 25% !important;
        }
    }
    </style>
    """, unsafe_allow_html=True)


def _fmt_month(ts_month: str) -> str:
    """'2026-04' → '2026年 4月'"""
    if not ts_month or len(ts_month) < 7:
        return "日付不明"
    try:
        y, m = ts_month[:4], int(ts_month[5:7])
        return f"{y}年 {_MONTH_LABELS_JA[m-1]}"
    except (ValueError, IndexError):
        return ts_month


def _fmt_day(ts_day: str) -> str:
    """'2026-04-30' → '4月30日 (木)'"""
    if not ts_day or len(ts_day) < 10:
        return "日付不明"
    try:
        d = datetime.strptime(ts_day[:10], "%Y-%m-%d").date()
        wd = _WEEKDAY_LABELS_JA[d.weekday()]
        return f"{d.month}月{d.day}日 ({wd})"
    except ValueError:
        return ts_day


def _make_thumb_bytes(raw: bytes, max_px: int = 400, quality: int = 70) -> bytes | None:
    """生画像バイトを JPEG サムネに変換。失敗時 None。"""
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


def _ss_thumb_path(file_id: str, max_px: int = 800) -> Path:
    return THUMB_CACHE_DIR / f"ss_{file_id}_{max_px}.jpg"


def _save_food_thumb(image_id: str, raw_bytes: bytes) -> bool:
    """食事画像のサムネを永続キャッシュに保存。既存なら何もしない。"""
    cache_path = _food_thumb_path(image_id)
    if cache_path.exists():
        return True
    thumb = _make_thumb_bytes(raw_bytes, max_px=400, quality=70)
    if not thumb:
        return False
    try:
        THUMB_CACHE_DIR.mkdir(exist_ok=True)
        cache_path.write_bytes(thumb)
        return True
    except Exception:
        return False


def _save_ss_thumb(file_id: str, raw_bytes: bytes, max_px: int = 800,
                   quality: int = 88) -> bool:
    """スクショ/ナレッジ画像のサムネを永続キャッシュに保存。既存なら何もしない。"""
    cache_path = _ss_thumb_path(file_id, max_px)
    if cache_path.exists():
        return True
    thumb = _make_thumb_bytes(raw_bytes, max_px=max_px, quality=quality)
    if not thumb:
        return False
    try:
        THUMB_CACHE_DIR.mkdir(exist_ok=True)
        cache_path.write_bytes(thumb)
        return True
    except Exception:
        return False


_THUMB_BACKFILL_STARTED = False


def _bg_get_drive_service():
    """バックグラウンドスレッド安全な Drive サービス取得（st.error/stop なし）。"""
    try:
        creds = service_account.Credentials.from_service_account_info(
            st.secrets["gcp_service_account"],
            scopes=SCOPES,
        )
        return build("drive", "v3", credentials=creds)
    except Exception as e:
        _log.warning(f"[bg] Drive 認証失敗: {e}")
        return None


def _bg_load_metadata_local() -> dict:
    """バックグラウンド用にローカル metadata.json を直接読み込む（Sheets/セッションを触らない）。"""
    if not METADATA_PATH.exists():
        return {}
    try:
        with open(METADATA_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _bg_append_ocr_pending(fid: str, ocr_text: str) -> None:
    """バックグラウンドで抽出した OCR テキストを保留ファイルに追記する。
    main() 起動時にメインスレッドが取り込んで save_metadata で永続化する。"""
    if not ocr_text:
        return
    try:
        pending: dict = {}
        if OCR_BACKFILL_PENDING_PATH.exists():
            try:
                with open(OCR_BACKFILL_PENDING_PATH, "r", encoding="utf-8") as f:
                    pending = json.load(f)
                if not isinstance(pending, dict):
                    pending = {}
            except Exception:
                pending = {}
        pending[fid] = ocr_text
        tmp = OCR_BACKFILL_PENDING_PATH.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(pending, f, ensure_ascii=False)
        tmp.replace(OCR_BACKFILL_PENDING_PATH)
    except Exception as e:
        _log.warning(f"[bg_ocr] pending書き込み失敗: {e}")


def _backfill_thumbs_worker():
    """既存画像のサムネ＋OCRテキストをバックグラウンドで生成する。

    - 食事画像: weight_uploads/ 配下を走査し、対応する .thumb_cache/food_*.jpg が
      無いものを生成する（ローカルディスク読み込みのみ・高速）
    - ナレッジ/スクショ画像: metadata の各 fid について .thumb_cache/ss_*_800.jpg
      が無いものを Drive から取得して生成。さらに ocr_text が空のものは NDLOCR で
      抽出して .ocr_backfill_pending.json に保留する（次回 main() で metadata に反映）

    1セッションにつき 1 回だけ走らせる。失敗は握り潰す。
    バックグラウンドスレッドのため st.session_state には触らない。
    """
    try:
        # --- 食事画像（ローカルディスク・高速） ---
        try:
            if WEIGHT_UPLOADS_DIR.exists():
                for img_path in WEIGHT_UPLOADS_DIR.iterdir():
                    if not img_path.is_file():
                        continue
                    image_id = img_path.stem
                    cache_path = THUMB_CACHE_DIR / f"food_{image_id}.jpg"
                    if cache_path.exists():
                        continue
                    try:
                        raw = img_path.read_bytes()
                        _save_food_thumb(image_id, raw)
                    except Exception:
                        continue
        except Exception as e:
            _log.warning(f"[thumb_backfill] food失敗: {e}")

        # --- ナレッジ/スクショ画像（Drive 取得＋OCR・低速） ---
        try:
            service = _bg_get_drive_service()
            if service is None:
                return
            metadata = _bg_load_metadata_local()
            ndlocr_ok = _ndlocr_available()

            # 処理対象を列挙（サムネ未生成 or OCR未実施）
            todo: list[tuple[str, bool, bool]] = []  # (fid, need_thumb, need_ocr)
            for fid, meta in metadata.items():
                if not isinstance(meta, dict):
                    continue
                thumb_path = THUMB_CACHE_DIR / f"ss_{fid}_800.jpg"
                need_thumb = not thumb_path.exists()
                need_ocr = ndlocr_ok and not (meta.get("ocr_text") or "").strip()
                if need_thumb or need_ocr:
                    todo.append((fid, need_thumb, need_ocr))

            for i, (fid, need_thumb, need_ocr) in enumerate(todo):
                try:
                    raw = download_image(service, fid)
                    if not raw:
                        continue
                    if need_thumb:
                        try:
                            _save_ss_thumb(fid, raw)
                        except Exception:
                            pass
                    if need_ocr:
                        try:
                            ocr_text = _extract_ocr_text_ndlocr(raw)
                            if ocr_text:
                                _bg_append_ocr_pending(fid, ocr_text)
                        except Exception:
                            pass
                except Exception:
                    continue
                # 100件ごとに少し休む（Drive API 制限対策）
                if i > 0 and i % 100 == 0:
                    time.sleep(1.0)
        except Exception as e:
            _log.warning(f"[thumb_backfill] ss失敗: {e}")
    except Exception:
        pass


def _apply_pending_ocr_backfill() -> None:
    """バックグラウンドが抽出した OCR テキストを metadata に取り込む（メインスレッド専用）。

    main() 開始時に呼ぶ。保留ファイルがあれば内容を metadata にマージし
    save_metadata（Sheets同期含む）した後、保留ファイルを削除する。
    """
    if not OCR_BACKFILL_PENDING_PATH.exists():
        return
    try:
        with open(OCR_BACKFILL_PENDING_PATH, "r", encoding="utf-8") as f:
            pending = json.load(f)
        if not isinstance(pending, dict) or not pending:
            try:
                OCR_BACKFILL_PENDING_PATH.unlink()
            except Exception:
                pass
            return

        metadata = load_metadata()
        changed = 0
        for fid, ocr_text in pending.items():
            if not isinstance(ocr_text, str) or not ocr_text.strip():
                continue
            entry = metadata.get(fid)
            if not isinstance(entry, dict):
                continue
            if (entry.get("ocr_text") or "").strip():
                continue  # 既に OCR 済み
            entry["ocr_text"] = ocr_text
            metadata[fid] = entry
            changed += 1

        if changed > 0:
            save_metadata(metadata)
            _invalidate_all_caches()
            _log.info(f"[ocr_backfill] {changed} 件の OCR テキストを metadata に反映")

        try:
            OCR_BACKFILL_PENDING_PATH.unlink()
        except Exception:
            pass
    except Exception as e:
        _log.warning(f"[ocr_backfill] 取り込み失敗: {e}")


def start_thumb_backfill():
    """既存画像のサムネ事前生成をバックグラウンドで1回だけ起動する。"""
    global _THUMB_BACKFILL_STARTED
    if _THUMB_BACKFILL_STARTED:
        return
    _THUMB_BACKFILL_STARTED = True
    try:
        t = threading.Thread(target=_backfill_thumbs_worker, daemon=True)
        t.start()
    except Exception:
        pass


@st.cache_data(ttl=86400, show_spinner=False, max_entries=2000)
def _load_food_thumbnail_bytes(image_id: str, ext: str,
                               drive_file_id: str = "") -> bytes | None:
    """食事画像のサムネイル（最大400px JPEG q70）。

    永続ディスクキャッシュ (.thumb_cache/{image_id}.jpg) + Streamlit メモリキャッシュ。
    一度生成すれば次回以降は即時にディスク読み込みで返す。
    """
    cache_path = THUMB_CACHE_DIR / f"food_{image_id}.jpg"
    if cache_path.exists():
        try:
            return cache_path.read_bytes()
        except Exception:
            pass

    raw = None
    img_path = WEIGHT_UPLOADS_DIR / f"{image_id}.{ext}"
    if img_path.exists():
        raw = img_path.read_bytes()
    elif drive_file_id:
        try:
            service = get_drive_service()
            if service:
                raw = download_image(service, drive_file_id)
        except Exception:
            pass
    if not raw:
        return None
    try:
        img = Image.open(io.BytesIO(raw))
        img.thumbnail((400, 400))
        buf = io.BytesIO()
        img.convert("RGB").save(buf, format="JPEG", quality=70, optimize=True)
        thumb_bytes = buf.getvalue()
        # 永続キャッシュに書き出し
        try:
            THUMB_CACHE_DIR.mkdir(exist_ok=True)
            cache_path.write_bytes(thumb_bytes)
        except Exception:
            pass
        return thumb_bytes
    except Exception:
        return raw


def _load_food_full_bytes(image_id: str, ext: str,
                          drive_file_id: str = "") -> bytes | None:
    """食事画像のフルサイズバイト。"""
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


def _meta_search_text(meta: dict) -> str:
    """メタデータから検索対象テキストを連結して返す（小文字化）。

    title / ocr_text / keywords を連結。古い summary 残骸も拾えるよう一応含める。
    list で入っている古いエントリにも対応。
    """
    def _stringify(v) -> str:
        if v is None:
            return ""
        if isinstance(v, str):
            return v
        if isinstance(v, (list, tuple)):
            return " ".join(_stringify(x) for x in v)
        if isinstance(v, dict):
            return " ".join(_stringify(x) for x in v.values())
        return str(v)

    parts = [
        _stringify(meta.get("title")),
        _stringify(meta.get("ocr_text")),
        _stringify(meta.get("keywords")),
        _stringify(meta.get("summary")),  # 後方互換: 既存データから検索
    ]
    return " ".join(parts).lower()


def _build_screenshot_entries(metadata: dict, drive_files: list[dict]) -> list[dict]:
    """ナレッジ画像（患者データ含む）のエントリを modifiedTime 降順で返す。

    search_text フィールドに title/summary/ocr_text/keywords を連結して入れ、
    あいまい検索の対象にする。
    """
    entries: list[dict] = []
    seen_ids: set[str] = set()
    for f in drive_files:
        fid = f.get("id")
        if not fid:
            continue
        meta = metadata.get(fid, {})
        ts = f.get("modifiedTime") or f.get("createdTime") or ""
        title = meta.get("title") or f.get("name", "")
        entries.append({
            "fid": fid,
            "title": title,
            "ts": ts,
            "kind": "screenshot",
            "is_patient": is_patient_data(meta),
            "search_text": _meta_search_text(meta) + " " + (f.get("name", "") or "").lower(),
        })
        seen_ids.add(fid)
    # ローカルアップロードのスクショもフォールバック
    for fid, meta in metadata.items():
        if fid in seen_ids:
            continue
        ts = ""
        for ext in ("png", "jpg", "jpeg"):
            p = UPLOADS_DIR / f"{fid}.{ext}"
            if p.exists():
                ts = datetime.fromtimestamp(p.stat().st_mtime).isoformat() + "Z"
                break
        if not ts:
            continue
        entries.append({
            "fid": fid,
            "title": meta.get("title") or fid,
            "ts": ts,
            "kind": "screenshot",
            "is_patient": is_patient_data(meta),
            "search_text": _meta_search_text(meta),
        })
    entries.sort(key=lambda x: x["ts"] or "", reverse=True)
    return entries


def _build_food_entries(weight_data: dict) -> list[dict]:
    """食事画像のエントリを日付降順で返す。

    同じ image_id を持つ複数の item 行は 1 つの画像エントリにまとめ、
    各 name を items_extracted（品目リスト）として表示する。
    """
    entries: list[dict] = []
    records = weight_data.get("records", {}) or {}
    for date_key in sorted(records.keys(), reverse=True):
        day = records[date_key] or {}
        # image_id ごとに集約（最初に出てきた item の ext/drive_file_id を採用）
        grouped: dict[str, dict] = {}
        order: list[str] = []
        for it in day.get("items", []) or []:
            iid = it.get("image_id")
            if not iid:
                continue
            if iid not in grouped:
                grouped[iid] = {
                    "ext": it.get("image_ext", "jpg"),
                    "drive_file_id": it.get("drive_file_id", ""),
                    "names": [],
                    "extras": [],
                }
                order.append(iid)
            g = grouped[iid]
            raw_name = it.get("name", "")
            name = raw_name if isinstance(raw_name, str) else str(raw_name or "")
            if name and name not in g["names"]:
                g["names"].append(name)
            ie = it.get("items_extracted")
            if isinstance(ie, list):
                for x in ie:
                    sx = str(x)
                    if sx and sx not in g["extras"]:
                        g["extras"].append(sx)

        for iid in order:
            g = grouped[iid]
            items_extracted = g["names"] + [x for x in g["extras"] if x not in g["names"]]
            title = items_extracted[0] if items_extracted else ""
            search_text = " ".join(s.lower() for s in items_extracted)
            entries.append({
                "fid": iid,
                "ext": g["ext"],
                "drive_file_id": g["drive_file_id"],
                "ts": date_key,
                "title": title,
                "items_extracted": items_extracted,
                "kind": "food",
                "search_text": search_text,
            })
    return entries


def _fuzzy_filter_entries(entries: list[dict], query: str) -> list[dict]:
    """エントリの search_text にクエリの全トークン（空白区切り）が含まれるものを返す。

    あいまい検索: 大小文字無視、部分一致、複数トークンは AND。
    """
    q = (query or "").strip().lower()
    if not q:
        return entries
    tokens = [t for t in q.split() if t]
    if not tokens:
        return entries
    out = []
    for e in entries:
        st_text = e.get("search_text", "") or ""
        if all(t in st_text for t in tokens):
            out.append(e)
    return out


def _get_synonyms_cached(token: str, kind: str = "food") -> set[str]:
    """単語の類義語・関連語を Gemini で取得し session_state にキャッシュ。

    kind="food" の場合は料理関連のみ、それ以外は一般的な類義語。
    Gemini が呼べない／失敗の場合は空集合を返す（呼び出し側で元語のみ使用）。
    """
    cache_key = f"_synonyms_{kind}_{token}"
    cached = st.session_state.get(cache_key)
    if cached is not None:
        return cached

    api_key = ""
    try:
        api_key = st.secrets.get("gemini_api_key", "") or ""
    except Exception:
        api_key = ""
    if not api_key:
        st.session_state[cache_key] = set()
        return set()

    if kind == "food":
        prompt = (
            f"「{token}」の関連する日本語の料理名・食べ物名を5〜20個、カンマ区切りで挙げてください。"
            f"・上位カテゴリ(例: 「パスタ」→ パスタ全般), 下位の具体名(例: ナポリタン, カルボナーラ), "
            f"同義語(例: スパゲッティ) を含む。"
            f"・料理・食材と無関係な単語の場合は何も返さない。"
            f"・説明や前置きは一切不要、純粋にカンマ区切りの単語のみ。\n"
            f"入力例「パスタ」→ 出力例: スパゲッティ,ナポリタン,カルボナーラ,ペペロンチーノ,ボロネーゼ,ラザニア,マカロニ\n"
            f"入力例「肉」→ 出力例: ステーキ,焼肉,ハンバーグ,鶏肉,豚肉,牛肉,唐揚げ,生姜焼き"
        )
    else:
        prompt = (
            f"「{token}」の関連語・類義語を5〜10個、カンマ区切りで挙げてください。"
            f"説明や前置きは一切不要、純粋にカンマ区切りの単語のみ。"
        )

    synonyms: set[str] = set()
    try:
        text = _gemini_generate(api_key, [{"text": prompt}])
        for raw in (text or "").replace("\n", ",").split(","):
            s = raw.strip().lower()
            # 余分な接頭辞/記号を弾く
            s = s.lstrip("・- 　").rstrip("。 　")
            if s and 1 <= len(s) <= 30 and s != token:
                synonyms.add(s)
    except Exception as e:
        _log.warning(f"[synonyms] Gemini呼び出し失敗 token={token}: {e}")
        synonyms = set()

    st.session_state[cache_key] = synonyms
    return synonyms


def _fuzzy_filter_entries_semantic(entries: list[dict], query: str,
                                   kind: str = "food") -> tuple[list[dict], list[set[str]]]:
    """類義語展開つきあいまい検索。

    各トークンを Gemini で類義語展開し、グループ間 AND・グループ内 OR でマッチさせる。
    返り値: (フィルタ済みエントリ, 拡張されたトークン群)
    """
    q = (query or "").strip().lower()
    if not q:
        return entries, []
    tokens = [t for t in q.split() if t]
    if not tokens:
        return entries, []

    # 各トークンを類義語セットに拡張
    expanded: list[set[str]] = []
    for token in tokens:
        synonyms = _get_synonyms_cached(token, kind)
        group = {token} | synonyms
        expanded.append(group)

    out = []
    for e in entries:
        st_text = e.get("search_text", "") or ""
        if all(any(s in st_text for s in group) for group in expanded):
            out.append(e)
    return out, expanded


@st.dialog("画像", width="large")
def _open_photo_dialog(entry: dict):
    """画像をモーダルで拡大表示する。ナレッジ画像はタイトル/要約/キーワードを直接編集できる。"""
    img_bytes: bytes | None = None
    is_knowledge = entry.get("kind") in ("patient", "screenshot")
    if is_knowledge:
        try:
            service = get_drive_service()
            if service:
                img_bytes = download_image(service, entry["fid"])
        except Exception:
            img_bytes = None
    else:
        img_bytes = _load_food_full_bytes(
            entry["fid"], entry.get("ext", "jpg"),
            entry.get("drive_file_id", ""),
        )
    if img_bytes:
        st.image(img_bytes, use_container_width=True)
    else:
        st.warning("画像の読み込みに失敗しました。")
    if entry.get("ts"):
        st.caption(entry["ts"][:10])

    if not is_knowledge:
        return

    fid = entry["fid"]
    metadata = load_metadata()
    meta = metadata.get(fid, {})

    cur_title = meta.get("title") or entry.get("title", "")
    cur_kws = meta.get("keywords") or []
    if not isinstance(cur_kws, list):
        cur_kws = []
    cur_kws_str = ", ".join(str(k) for k in cur_kws)

    st.markdown("---")
    st.markdown("**📝 タイトル・キーワード**")
    with st.form(f"edit_form_{fid}", clear_on_submit=False):
        new_title = st.text_input(
            "タイトル",
            value=cur_title,
            key=f"dlg_title_{fid}",
            placeholder="例: 心電図 ST上昇 V1-V4",
        )
        new_kws_str = st.text_input(
            "キーワード（カンマ区切り）",
            value=cur_kws_str,
            key=f"dlg_kws_{fid}",
            placeholder="例: 心筋梗塞, 心電図, ST上昇",
        )
        submitted = st.form_submit_button("💾 保存", type="primary", use_container_width=True)

    if submitted:
        new_keywords = [k.strip() for k in new_kws_str.split(",") if k.strip()]
        existing = metadata.get(fid, {})
        existing.update({
            "title": new_title.strip(),
            "keywords": new_keywords,
            "status": STATUS_REVIEWED,
        })
        metadata[fid] = existing
        try:
            ok = save_metadata(metadata)
        except Exception as e:
            ok = False
            _log.exception(f"[photo_dialog] save_metadata失敗 fid={fid}: {e}")
        if ok:
            st.toast("✅ 保存しました", icon="✅")
        else:
            st.toast("⚠️ ローカルには保存されました（Sheetsは後で再試行）", icon="⚠️")
        st.rerun()


def _render_photo_gallery(entries: list[dict], key_prefix: str,
                          fetch_thumb_fn) -> None:
    """日付グループ化された写真グリッドを描画する。"""
    if not entries:
        st.markdown(
            '<div class="g-empty">画像がまだありません。</div>',
            unsafe_allow_html=True,
        )
        return

    state_key = f"{key_prefix}_loaded"
    loaded = st.session_state.get(state_key, GALLERY_PAGE_SIZE)
    if loaded > len(entries):
        loaded = len(entries)
    visible = entries[:loaded]

    cur_month = None
    cur_day = None
    for row_start in range(0, len(visible), GALLERY_COLS):
        row = visible[row_start:row_start + GALLERY_COLS]
        first = row[0]
        ts = first.get("ts") or ""
        m, d = ts[:7], ts[:10]
        if m != cur_month:
            cur_month = m
            st.markdown(
                f'<div class="g-month">{_fmt_month(m)}</div>',
                unsafe_allow_html=True,
            )
        if d != cur_day:
            cur_day = d
            st.markdown(
                f'<div class="g-day">{_fmt_day(d)}</div>',
                unsafe_allow_html=True,
            )
        cols = st.columns(GALLERY_COLS)
        for ci, e in enumerate(row):
            with cols[ci]:
                try:
                    thumb = fetch_thumb_fn(e)
                except Exception:
                    thumb = None
                if thumb:
                    st.image(thumb, use_container_width=True)
                else:
                    st.markdown(
                        '<div class="g-placeholder">🖼️</div>',
                        unsafe_allow_html=True,
                    )
                if e.get("kind") == "food":
                    items_ext = e.get("items_extracted") or []
                    if items_ext:
                        chips = "".join(
                            f'<span class="g-chip">{html.escape(str(x))}</span>'
                            for x in items_ext
                        )
                        st.markdown(
                            f'<div class="g-caption">{chips}</div>',
                            unsafe_allow_html=True,
                        )
                    elif e.get("title"):
                        st.markdown(
                            f'<div class="g-caption">{html.escape(e["title"])}</div>',
                            unsafe_allow_html=True,
                        )
                else:
                    title = e.get("title", "")
                    if title:
                        prefix = "🏥 " if e.get("is_patient") else ""
                        st.markdown(
                            f'<div class="g-caption">{prefix}{html.escape(title)}</div>',
                            unsafe_allow_html=True,
                        )
                if st.button("🔍", key=f"{key_prefix}_btn_{e['fid']}",
                             use_container_width=True,
                             help="拡大表示"):
                    _open_photo_dialog(e)

    if loaded < len(entries):
        if st.button(f"もっと見る ({loaded} / {len(entries)})",
                     key=f"{key_prefix}_more",
                     use_container_width=True,
                     type="primary"):
            st.session_state[state_key] = loaded + GALLERY_PAGE_SIZE
            st.rerun()


def page_food_gallery():
    """食事画像の Google Photos 風ギャラリー（類義語展開つきあいまい検索）。"""
    _inject_gallery_css()
    st.markdown("## 🍽️ 食事")

    weight_data = load_weight_data()
    entries = _build_food_entries(weight_data)

    query = st.text_input(
        "🔍 品目で検索（関連語も自動でヒット: パスタ → ナポリタン等）",
        key="food_gal_search",
        placeholder="例: 肉 野菜  ← スペース区切りで複数キーワード絞り込み",
        help="スペースで区切ると複数キーワードの AND 検索になります（例: 「肉 野菜」で両方を含む画像）。各語は関連語にも自動展開されます。",
        label_visibility="collapsed",
    )

    if query:
        with st.spinner("関連語を展開中..."):
            filtered, expanded = _fuzzy_filter_entries_semantic(entries, query, kind="food")
        # 展開された語を表示（デバッグ・透明性のため）
        if expanded:
            term_strs = []
            for group in expanded:
                terms = sorted(group)
                if len(terms) > 6:
                    term_strs.append(" / ".join(terms[:6]) + f" 他{len(terms)-6}語")
                else:
                    term_strs.append(" / ".join(terms))
            st.caption(
                f"🔍 「{query}」→ {' & '.join(term_strs)}: "
                f"{len(filtered)} / {len(entries)} 件"
            )
        else:
            st.caption(f"🔍 「{query}」: {len(filtered)} / {len(entries)} 件")
    else:
        filtered = entries
        st.caption(f"全 {len(entries)} 件")

    def _fetch(e):
        return _load_food_thumbnail_bytes(
            e["fid"], e.get("ext", "jpg"), e.get("drive_file_id", "")
        )

    _render_photo_gallery(filtered, "food_gal", _fetch)


def page_screenshot_gallery():
    """ナレッジ画像（clinical-kb + 患者データ）の Google Photos 風ギャラリー。

    タイトル/要約/OCR/キーワードを横断したあいまい検索付き。
    """
    _inject_gallery_css()
    st.markdown("## 📖 ナレッジ")

    metadata = load_metadata()
    service = get_drive_service()
    if not service:
        st.error("Google Driveに接続できませんでした。設定を確認してください。")
        return

    folder_id = get_folder_id()
    patient_fid = get_patient_folder_id()
    drive_files = list_all_images(service, folder_id, metadata, patient_fid)
    entries = _build_screenshot_entries(metadata, drive_files)

    sc_left, sc_right = st.columns([5, 1])
    with sc_left:
        query = st.text_input(
            "🔍 タイトル・OCR・キーワードで検索",
            key="ss_gal_search",
            placeholder="例: 心電図 ST上昇  ← スペース区切りで複数キーワード絞り込み",
            help="スペースで区切ると複数キーワードの AND 検索になります（例: 「心電図 ST上昇」で両方を含む画像）。タイトル・キーワード・OCR テキストすべてを横断検索します。",
            label_visibility="collapsed",
        )
    with sc_right:
        if st.button("🔄 再取得", key="ss_gal_refresh", help="Drive 一覧キャッシュをクリアして再取得"):
            try:
                list_images.clear()
                list_patient_images.clear()
            except Exception:
                pass
            st.rerun()
    filtered = _fuzzy_filter_entries(entries, query)

    n_patient = sum(1 for e in entries if e.get("is_patient"))
    n_main = len(entries) - n_patient
    base_caption = f"全 {len(entries)} 件"
    if n_patient:
        base_caption += f"（うち 🏥 患者データ {n_patient} 件）"
    if query:
        st.caption(f"🔍 「{query}」: {len(filtered)} / {len(entries)} 件")
    else:
        st.caption(base_caption)
    if n_main == 0 and n_patient > 0:
        st.info("📚 ナレッジ画像（clinical-kb）が0件です。Drive 一覧取得が失敗した可能性があるので「🔄 再取得」をお試しください。")

    def _fetch(e):
        try:
            return download_thumbnail(service, e["fid"], max_px=800, quality=88)
        except Exception:
            return None

    _render_photo_gallery(filtered, "ss_gal", _fetch)


# ===========================================================================
# 統合ページ: 設定（最小構成）
# ===========================================================================
def page_settings_all():
    """設定ページ — 最小構成。基本動作は自動取り込み + バックグラウンド同期。"""
    st.markdown("## ⚙️ 設定")

    _auto_val = st.toggle(
        "自動取り込み（バックグラウンドで新着画像を取得）",
        value=st.session_state.get("auto_scan_enabled", True),
        key="auto_scan_toggle_settings",
    )
    st.session_state["auto_scan_enabled"] = _auto_val

    health = st.session_state.get("_sync_health", {})
    _is_sheets_connected = st.session_state.get("_sheets_connected", None)
    if _is_sheets_connected is False:
        st.caption("☁️ Sheets 未接続（ローカル保存のみ）")
    elif health:
        total_diff = sum(abs(h.get("diff", 0)) for h in health.values())
        if total_diff == 0:
            st.caption("☁️ Google Sheets と同期済み")
        else:
            st.caption(f"☁️ 同期差異 {total_diff} 件（バックグラウンドで自動解決中）")

    auth_user = st.session_state.get("auth_user")
    if auth_user:
        st.caption(f"👤 {auth_user}")

    st.markdown("---")

    with st.expander("🔧 詳細操作"):
        st.caption("通常は触る必要はありません。")

        if st.button("🔄 今すぐ取り込み（手動）", key="manual_scan_settings",
                     width="stretch"):
            st.session_state["manual_scan_running"] = True
            list_images.clear()
            st.rerun()

        if st.button("📤 Local → Sheets 強制同期", key="force_sync_l2s",
                     width="stretch"):
            with st.spinner("Sheets へ同期中..."):
                _force_sync_local_to_sheets()
            st.session_state["_sync_health_ts"] = 0
            st.toast("☁️ Sheets へ同期しました")
            st.rerun()

        if st.button("📥 Sheets → Local 復元", key="force_sync_s2l",
                     width="stretch"):
            with st.spinner("ローカルに復元中..."):
                _force_sync_sheets_to_local()
            st.session_state["_sync_health_ts"] = 0
            st.toast("📥 ローカルに復元しました")
            st.rerun()

        if st.button("🔍 ヘルスチェック再実行", key="manual_health_check",
                     width="stretch"):
            st.session_state["_sync_health_ts"] = 0
            _check_sync_health()
            st.rerun()

        if auth_user and st.button("🚪 ログアウト", key="sys_logout",
                                    width="stretch"):
            _clear_auth_storage()
            _clear_auth_file()
            st.session_state["authenticated"] = False
            st.session_state.pop("auth_user", None)
            if "token" in st.query_params:
                del st.query_params["token"]
            st.rerun()


# ===========================================================================
# 体重管理ページ
# ===========================================================================
def _inject_wm_css():
    """体重ページ専用 CSS。refined dark card + orange accent。"""
    st.markdown("""
    <style>
    .wm-card {
        background: linear-gradient(160deg, #1d2030 0%, #14161f 100%);
        border: 1px solid rgba(255,255,255,0.06);
        border-radius: 18px;
        padding: 22px 20px 18px;
        color: #e6e6ec;
        margin: 8px 0 14px;
        box-shadow: 0 6px 24px rgba(0,0,0,0.25);
        position: relative;
        overflow: hidden;
    }
    .wm-card::before {
        content: "";
        position: absolute; top: -40px; right: -40px;
        width: 120px; height: 120px;
        background: radial-gradient(closest-side, rgba(255,122,60,0.18), transparent 70%);
        pointer-events: none;
    }
    .wm-card .wm-label {
        font-size: 12px; letter-spacing: 0.08em;
        text-transform: uppercase; color: rgba(255,255,255,0.55);
    }
    .wm-card .wm-value {
        font-size: 48px; font-weight: 700; line-height: 1.1;
        margin: 6px 0 2px;
        background: linear-gradient(135deg, #FFB47A, #FF7A3C);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        background-clip: text;
    }
    .wm-card .wm-value .wm-unit {
        font-size: 16px; color: rgba(255,255,255,0.45);
        -webkit-text-fill-color: rgba(255,255,255,0.45);
        margin-left: 4px;
    }
    .wm-card .wm-value .wm-trend { font-size: 22px; margin-left: 6px; }
    .wm-card .wm-sub { font-size: 13px; color: rgba(255,255,255,0.6); }
    .wm-card .wm-goalbar-wrap {
        margin-top: 14px; height: 6px;
        background: rgba(255,255,255,0.06);
        border-radius: 4px; overflow: hidden;
    }
    .wm-card .wm-goalbar {
        height: 100%; border-radius: 4px;
        background: linear-gradient(90deg, #FF7A3C, #FFB47A);
        transition: width 320ms ease;
    }
    .wm-trend-down { color: #5fd28b; }
    .wm-trend-up { color: #ff7a7a; }
    .wm-trend-flat { color: rgba(255,255,255,0.4); }
    .wm-input-display {
        text-align: center; font-size: 44px; font-weight: 700;
        line-height: 1.1;
        background: linear-gradient(135deg, #FFB47A, #FF7A3C);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        background-clip: text;
    }
    .wm-input-display.wm-pending {
        background: linear-gradient(135deg, #ffd28a, #ffb84a);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
    }
    .wm-input-display .wm-unit {
        font-size: 16px;
        -webkit-text-fill-color: rgba(255,255,255,0.5);
        margin-left: 4px;
    }
    </style>
    """, unsafe_allow_html=True)


def _get_weight_trend(records: dict) -> str:
    """直近2つの体重記録を比較して傾向を返す。 'down' / 'up' / 'flat' / 'none'"""
    weight_entries = []
    for dk in sorted(records.keys(), reverse=True):
        w = records[dk].get("weight")
        if w:
            weight_entries.append(w)
        if len(weight_entries) >= 2:
            break
    if len(weight_entries) < 2:
        return "none"
    if weight_entries[0] < weight_entries[1]:
        return "down"
    elif weight_entries[0] > weight_entries[1]:
        return "up"
    return "flat"


def _render_date_navigation():
    """MoneyForward風の日付ナビゲーション。◀ 前日 | カレンダー | 翌日 ▶ | 今日

    wm_selected_date を唯一の真実として扱い、date_input widget の key は毎回 dynamic に
    変える事で widget internal state の残留による日付バウンス問題を回避する。
    """
    if "wm_selected_date" not in st.session_state:
        st.session_state["wm_selected_date"] = date.today()

    sel = st.session_state["wm_selected_date"]

    def _set_date(new_d):
        st.session_state["wm_selected_date"] = new_d
        st.rerun()

    col_prev, col_date, col_next, col_today = st.columns([1, 4, 1, 1.5])
    with col_prev:
        if st.button("◀", key="wm_prev_day", width="stretch"):
            _set_date(sel - timedelta(days=1))
    with col_date:
        # key を sel に紐付けると sel が変わった時に新規widgetとして再生成されるため
        # 内部stateの残留バウンス問題が起きない
        picked = st.date_input(
            "日付を選択",
            value=sel,
            key=f"wm_date_picker_{sel.isoformat()}",
            label_visibility="collapsed",
        )
        if picked != sel:
            _set_date(picked)
    with col_next:
        if st.button("▶", key="wm_next_day", width="stretch"):
            _set_date(sel + timedelta(days=1))
    with col_today:
        if sel != date.today():
            if st.button("今日", key="wm_today_btn", width="stretch"):
                _set_date(date.today())


def _render_dashboard_card(d: dict, goals: dict, records: dict):
    """体重ダッシュボードカード — refined dark + orange accent。"""
    weight = d.get("weight")
    target_wt = goals.get("target_weight_kg")

    trend = _get_weight_trend(records)
    trend_html = ""
    if weight:
        trend_arrow = {"down": "↓", "up": "↑", "flat": "→"}.get(trend, "")
        trend_class = {"down": "wm-trend-down", "up": "wm-trend-up",
                       "flat": "wm-trend-flat"}.get(trend, "wm-trend-flat")
        if trend_arrow:
            trend_html = f'<span class="wm-trend {trend_class}">{trend_arrow}</span>'

    w_display = f"{weight}" if weight else "--"

    sub_html = ""
    goalbar_html = ""
    if weight and target_wt:
        diff = round(weight - target_wt, 1)
        if diff > 0:
            sub_html = f"🎯 目標まで残り <b>{abs(diff)}</b> kg"
        elif diff == 0:
            sub_html = "🎉 目標達成中"
        else:
            sub_html = f"🎯 目標を <b>{abs(diff)}</b> kg 下回り中"

        baseline_wts = []
        for dk in sorted(records.keys()):
            w = records[dk].get("weight")
            if w:
                baseline_wts.append(w)
        baseline = baseline_wts[0] if baseline_wts else weight
        if baseline != target_wt:
            total = baseline - target_wt
            achieved = baseline - weight
            pct = max(0.0, min(100.0, (achieved / total) * 100)) if total else 0.0
            goalbar_html = (
                f'<div class="wm-goalbar-wrap">'
                f'<div class="wm-goalbar" style="width:{pct:.1f}%;"></div>'
                f'</div>'
            )
    elif target_wt:
        sub_html = f"🎯 目標 {target_wt} kg"
    elif weight:
        sub_html = "目標を設定すると進捗が表示されます"
    else:
        sub_html = "本日の体重を記録してください"

    st.markdown(f"""
    <div class="wm-card">
        <div class="wm-label">本日の体重</div>
        <div class="wm-value">{w_display}<span class="wm-unit">kg</span>{trend_html}</div>
        <div class="wm-sub">{sub_html}</div>
        {goalbar_html}
    </div>
    """, unsafe_allow_html=True)




def _render_weight_history(records: dict, goals: dict):
    """体重履歴一覧。"""
    try:
        _render_weight_history_inner(records, goals)
    except Exception as e:
        _log.exception("体重履歴の描画でエラー")
        st.error(f"履歴表示でエラーが発生しました: {type(e).__name__}: {e}")
        st.caption("ページ再読み込みまたは期間を変更してお試しください。")


def _render_weight_history_inner(records: dict, goals: dict):
    """履歴一覧 内部実装（体重のみ）。"""
    if not records:
        st.info("まだ記録がありません。「📝 記録」タブから体重を入力してください。")
        return

    period = st.selectbox("表示期間", ["直近7日", "直近30日", "全期間"], key="wm_hist_period")
    today = date.today()
    if period == "直近7日":
        cutoff = today - timedelta(days=7)
    elif period == "直近30日":
        cutoff = today - timedelta(days=30)
    else:
        cutoff = None

    sorted_dates = sorted(records.keys(), reverse=True)
    if cutoff:
        sorted_dates = [d for d in sorted_dates if d >= cutoff.strftime("%Y-%m-%d")]

    if not sorted_dates:
        st.caption("この期間のデータはありません。")
        return

    _weight_entries = []
    for dk in sorted(sorted_dates):
        w = records[dk].get("weight")
        if w:
            _weight_entries.append((dk, w))

    sc1, sc2 = st.columns(2)
    with sc1:
        st.metric("記録日数", f"{len(_weight_entries)} 日")
    with sc2:
        if len(_weight_entries) >= 2:
            wt_change = round(_weight_entries[-1][1] - _weight_entries[0][1], 1)
            sign = "+" if wt_change > 0 else ""
            st.metric("体重変化", f"{sign}{wt_change} kg")
        else:
            st.metric("体重変化", "---")

    st.markdown("### 📋 日別記録")
    for dk in sorted_dates:
        try:
            dt = datetime.strptime(dk, "%Y-%m-%d")
        except ValueError:
            continue
        day = records.get(dk) or {}
        if not isinstance(day, dict):
            continue
        w = day.get("weight")
        if not w:
            continue
        weekday = ["月", "火", "水", "木", "金", "土", "日"][dt.weekday()]
        st.markdown(
            f"📅 {dt.month}/{dt.day}（{weekday}）　⚖️ **{w} kg**"
        )


def page_weight_management():
    """体重管理ページ。"""
    try:
        _page_weight_management_inner()
    except Exception as e:
        _log.exception("体重ページでエラー")
        st.error("体重ページでエラーが発生しました。ページを再読み込みしてください。")


def _page_weight_management_inner():
    """体重管理ページ内部実装（体重のみ）。"""
    _inject_wm_css()
    st.markdown("## ⚖️ 体重")

    weight_data = load_weight_data()
    records = weight_data.setdefault("records", {})
    goals = weight_data.get("goals", {})

    # 前のrunでセットされた「次回表示タブ」を反映（widget描画前に書き込む必要あり）
    if "_wm_next_tab" in st.session_state:
        st.session_state["wm_active_tab"] = st.session_state.pop("_wm_next_tab")

    _TAB_OPTIONS = ["📝 記録", "📊 履歴"]
    if st.session_state.get("wm_active_tab") not in _TAB_OPTIONS:
        st.session_state["wm_active_tab"] = "📝 記録"
    active_tab = st.radio(
        "タブ",
        _TAB_OPTIONS,
        horizontal=True,
        label_visibility="collapsed",
        key="wm_active_tab",
    )

    if active_tab == "📊 履歴":
        _render_weight_history(records, goals)
        return

    # ===== 以下 "📝 記録" タブ =====
    _render_date_navigation()
    selected_date = st.session_state.get("wm_selected_date", date.today())
    date_key = selected_date.strftime("%Y-%m-%d")
    day_data = records.setdefault(date_key, {})

    _render_dashboard_card(day_data, goals, records)

    st.markdown("### ⚖️ 体重を入力")

    # ベースライン: 当日の体重 → 直近記録 → 60.0
    _wt_temp_key = f"wm_weight_temp_{date_key}"
    if _wt_temp_key not in st.session_state:
        _base_wt = day_data.get("weight")
        if not _base_wt:
            for _dk in sorted(records.keys(), reverse=True):
                _w = records[_dk].get("weight")
                if _w:
                    _base_wt = _w
                    break
        st.session_state[_wt_temp_key] = _base_wt or 60.0

    _cur_wt = st.session_state[_wt_temp_key]

    def _adjust_and_save(delta: float):
        new_wt = round(max(0.1, _cur_wt + delta), 1)
        st.session_state[_wt_temp_key] = new_wt
        day_data["weight"] = new_wt
        day_data["weight_recorded_at"] = datetime.now().isoformat()
        save_weight_data(weight_data)
        st.toast(f"✅ {new_wt} kg を記録")
        st.rerun()

    # ±ボタン行（押下時に即保存）
    _wc1, _wc2, _wc3, _wc4, _wc5 = st.columns([1, 1, 2, 1, 1])
    with _wc1:
        if st.button("▼0.5", key=f"wm_wt_m5_{date_key}", use_container_width=True):
            _adjust_and_save(-0.5)
    with _wc2:
        if st.button("▼0.1", key=f"wm_wt_m1_{date_key}", use_container_width=True):
            _adjust_and_save(-0.1)
    with _wc3:
        _is_saved = bool(day_data.get("weight"))
        _cls = "wm-input-display" if _is_saved else "wm-input-display wm-pending"
        st.markdown(
            f"<div class='{_cls}'>{_cur_wt:.1f}"
            f"<span class='wm-unit'>kg</span></div>",
            unsafe_allow_html=True,
        )
    with _wc4:
        if st.button("▲0.1", key=f"wm_wt_p1_{date_key}", use_container_width=True):
            _adjust_and_save(0.1)
    with _wc5:
        if st.button("▲0.5", key=f"wm_wt_p5_{date_key}", use_container_width=True):
            _adjust_and_save(0.5)

    with st.expander("⌨️ 数値を直接入力"):
        with st.form(key=f"wm_weight_form_{date_key}"):
            input_weight = st.number_input(
                "体重 (kg)", min_value=0.0, max_value=300.0,
                value=float(_cur_wt), step=0.1, format="%.1f",
            )
            weight_submitted = st.form_submit_button("💾 体重を記録", type="primary")
        if weight_submitted:
            if input_weight > 0:
                day_data["weight"] = round(input_weight, 1)
                day_data["weight_recorded_at"] = datetime.now().isoformat()
                save_weight_data(weight_data)
                st.session_state[_wt_temp_key] = round(input_weight, 1)
                st.toast(f"✅ 体重 {input_weight} kg を記録しました")
                st.rerun()
            else:
                st.warning("0 より大きい値を入力してください。")

    comment = _generate_weight_comment(day_data, goals)
    st.info(comment)

    with st.expander("🎯 目標体重を設定"):
        cur_target_wt = goals.get("target_weight_kg", 0.0)
        cur_target_date = goals.get("target_date", "")

        current_weight = day_data.get("weight")
        if not current_weight:
            for dk in sorted(records.keys(), reverse=True):
                w = records[dk].get("weight")
                if w:
                    current_weight = w
                    break

        default_target_date = date.today()
        if cur_target_date:
            try:
                parsed_td = datetime.strptime(cur_target_date, "%Y-%m-%d").date()
                default_target_date = max(parsed_td, date.today())
            except (ValueError, TypeError):
                pass
        if "wm_goal_date" in st.session_state:
            try:
                _cached_gd = st.session_state["wm_goal_date"]
                if hasattr(_cached_gd, "date"):
                    _cached_gd = _cached_gd.date()
                if not isinstance(_cached_gd, date) or _cached_gd < date.today():
                    del st.session_state["wm_goal_date"]
            except Exception:
                st.session_state.pop("wm_goal_date", None)

        with st.form(key="wm_goal_form"):
            new_target_wt = st.number_input(
                "目標体重 (kg)", min_value=0.0, max_value=300.0,
                value=float(cur_target_wt), step=0.1, format="%.1f",
            )
            new_target_date = st.date_input(
                "いつまでに達成？", value=default_target_date,
            )
            goal_submitted = st.form_submit_button("💾 目標を保存", type="primary")

        if goal_submitted:
            if new_target_date < date.today():
                new_target_date = date.today()
            new_goals = {
                "target_weight_kg": round(new_target_wt, 1),
                "target_date": new_target_date.strftime("%Y-%m-%d"),
            }
            if current_weight:
                new_goals["current_weight_kg"] = current_weight
            weight_data["goals"] = new_goals
            save_weight_data(weight_data)
            st.toast("✅ 目標を保存しました")
            st.rerun()





# ===========================================================================
# メインエントリポイント
# ===========================================================================
def main():
    st.set_page_config(
        page_title="Pomken",
        page_icon="🐻",
        layout="wide",
        initial_sidebar_state="collapsed",
    )

    # ★ 認証チェック（未認証ならログイン画面のみ表示）
    if not _check_auth():
        return

    # Git自動push開始（バックグラウンド、60秒間隔）
    start_auto_push()

    # バックグラウンドが抽出した OCR テキストを metadata に反映（あれば）
    try:
        _apply_pending_ocr_backfill()
    except Exception:
        pass

    # 既存画像のサムネ+OCR事前生成（バックグラウンド・1回限り）
    start_thumb_backfill()

    st.markdown(
        "<link href='https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700&display=swap' rel='stylesheet'>",
        unsafe_allow_html=True,
    )
    # グローバル: ローディングバナーCSS
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

    # アクティブタブの管理（4タブ構成）
    TAB_NAMES = ["📖 ナレッジ", "🍽️ 食事", "⚖️ 体重", "⚙️ 設定"]
    if "active_tab" not in st.session_state:
        st.session_state["active_tab"] = TAB_NAMES[0]
    # 旧タブ名からのマイグレーション
    old_tab_map = {
        "🏥 患者データ": TAB_NAMES[0],
        "📱 スクショ": TAB_NAMES[0],
        "📚 ライブラリ": TAB_NAMES[0],
        "💬 チャット": TAB_NAMES[0],
        "💬 チャット検索": TAB_NAMES[0],
        "📸 画像ライブラリ": TAB_NAMES[0],
        "📸 画像管理": TAB_NAMES[0],
        "📂 手動整理": TAB_NAMES[0],
        "🤖 AI整理": TAB_NAMES[0],
        "🧠 クイズ": TAB_NAMES[0],
        "🍽️ 食事画像": TAB_NAMES[1],
        "🍽️ 食事記録": TAB_NAMES[1],
        "⚖️ 体重・カロリー": TAB_NAMES[2],
        "⚖️ 体重管理": TAB_NAMES[2],
        "⚡ 取り込み・解析": TAB_NAMES[3],
        "⚡ 一括解析": TAB_NAMES[3],
        "🗂️ フォルダ設定": TAB_NAMES[3],
        "🗑️ ゴミ箱": TAB_NAMES[3],
        "⚙️ 設定": TAB_NAMES[3],
    }
    if st.session_state["active_tab"] in old_tab_map:
        st.session_state["active_tab"] = old_tab_map[st.session_state["active_tab"]]

    home_clicked = st.button("🐻 Pomken", key="home_btn")
    st.markdown(
        """<style>
        div[data-testid="stMainBlockContainer"] > div:nth-child(2) button {
            font-family: 'Playfair Display', serif !important;
            font-size: 28px !important;
            font-weight: 700 !important;
            border: none !important;
            padding: 4px 0 !important;
            background: transparent !important;
            box-shadow: none !important;
            color: inherit !important;
            cursor: pointer !important;
        }
        div[data-testid="stMainBlockContainer"] > div:nth-child(2) button:hover {
            opacity: 0.7;
        }
        </style>""",
        unsafe_allow_html=True,
    )
    if home_clicked:
        st.session_state["active_tab"] = TAB_NAMES[0]
        st.session_state.pop("lib_selected_id", None)
        st.session_state.pop("last_upload_id", None)
        st.session_state.pop("pat_gal_loaded", None)
        st.session_state.pop("food_gal_loaded", None)
        st.session_state.pop("ss_gal_loaded", None)
        st.rerun()

    # ─── ページ切り替えボタン（refined pill nav）───
    # NOTE: Streamlit は各要素を独自 stElementContainer でラップするため
    # anchor とカラムが直接の兄弟にならず `+ div` では届かない。
    # `:has()` で anchor を含むコンテナ → その直後のコンテナをトラバースする。
    _TABNAV_SCOPE = (
        '[data-testid="stElementContainer"]:has(.pomken-tabnav-anchor) '
        '+ [data-testid="stElementContainer"]'
    )
    # NOTE: markdown は行頭インデントを code-block 扱いするので flush-left で書く必要がある
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
    tab_cols = st.columns(4)
    for i, tab_name in enumerate(TAB_NAMES):
        is_active = st.session_state["active_tab"] == tab_name
        if tab_cols[i].button(
            tab_name,
            key=f"tab_btn_{tab_name}",
            width="stretch",
            type="primary" if is_active else "secondary",
        ):
            st.session_state["active_tab"] = tab_name
            st.rerun()

    # ─── コールドスタート時は重い同期/スキャンをスキップ ───
    # 初回レンダリングで Sheets×3・Drive×2・Gemini×5 が同期発火し
    # 起動が 30-60秒遅れる問題への対処。各機能の cooldown タイムスタンプを
    # "現在時刻" に揃えることで、cooldown 内として自然に短絡させる。
    if "_cold_start_done" not in st.session_state:
        st.session_state["_cold_start_done"] = True
        _cs_now = time.time()
        st.session_state["_sync_health_ts"] = _cs_now
        st.session_state["_auto_sync_ts"] = _cs_now
        st.session_state["auto_scan_last"] = _cs_now
        st.session_state["food_scan_last"] = _cs_now

    # ─── 前回失敗した Sheets 書き込みを再試行 ───
    _retry_pending_saves()

    # ─── 同期ヘルスチェック（5分間隔）＋差異自動マージ ───
    _check_sync_health()
    _auto_resolve_sync_diff()

    # ─── 自動取り込みのデフォルト値 ───
    if "auto_scan_enabled" not in st.session_state:
        st.session_state["auto_scan_enabled"] = True

    # --- 手動スキャン（リアルタイム進捗表示） ---
    if st.session_state.pop("manual_scan_running", False):
        st.markdown(
            '<div class="loading-banner">🔄 スキャン中です… しばらくお待ちください</div>',
            unsafe_allow_html=True,
        )
        try:
            _scan_service = get_drive_service()
            _scan_folder_id = get_folder_id()
            _scan_api_key = get_gemini_api_key()
            if _scan_api_key:
                _run_manual_scan(_scan_service, _scan_folder_id, _scan_api_key)
            _food_fid = get_food_folder_id()
            if _food_fid:
                _fc = scan_food_images(_scan_service, _food_fid,
                                       api_key=_scan_api_key, manual=True)
                if _fc > 0:
                    st.toast(f"🍽️ 食事 {_fc} 枚を取り込みました", icon="🍽️")
        except Exception:
            st.warning("⚠️ スキャン中にエラーが発生しました。")
        st.session_state["auto_scan_last"] = time.time()
        st.session_state["food_scan_last"] = time.time()

    # --- 自動スキャン（バックグラウンド） ---
    elif st.session_state.get("auto_scan_enabled", True):
        try:
            _scan_service = get_drive_service()
            _scan_folder_id = get_folder_id()
            _scan_api_key = get_gemini_api_key()
            auto_scan_new_images(_scan_service, _scan_folder_id, _scan_api_key)
        except Exception as e:
            _log.error(f"[自動スキャン] エラー: {type(e).__name__}: {e}")

    # --- 食事画像自動取り込み（Google Driveフォルダ） ---
    try:
        _food_fid = get_food_folder_id()
        if _food_fid:
            _food_service = get_drive_service()
            _food_api_key = get_gemini_api_key()
            _food_count = scan_food_images(_food_service, _food_fid,
                                           api_key=_food_api_key)
            if _food_count > 0:
                st.toast(f"🔔 食事 {_food_count} 枚を自動取り込みしました", icon="📷")
                st.rerun()
    except Exception as e:
        _log.error(f"[食事画像自動取り込み] エラー: {type(e).__name__}: {e}")

    # ─── ページ表示 ───
    active = st.session_state["active_tab"]
    if active == TAB_NAMES[0]:
        page_screenshot_gallery()
    elif active == TAB_NAMES[1]:
        page_food_gallery()
    elif active == TAB_NAMES[2]:
        page_weight_management()
    elif active == TAB_NAMES[3]:
        page_settings_all()



if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        _log.exception("アプリケーションエラー")
        st.error("アプリケーションエラーが発生しました。ページを再読み込みしてください。")

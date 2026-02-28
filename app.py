"""
Clinical Knowledge Base - Phase 4: チャット検索(Q&A)付き画像ビューワー

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
import hashlib
import hmac
import io
import json
import logging
import random
import re
import ssl
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
CHAT_SESSIONS_PATH = Path(__file__).parent / "chat_sessions.json"
TRASH_PATH = Path(__file__).parent / "trash.json"
IGNORE_LIST_PATH = Path(__file__).parent / "ignore_list.json"
FOLDERS_PATH = Path(__file__).parent / "folders.json"
UPLOADS_DIR = Path(__file__).parent / "uploads"
WEIGHT_DATA_PATH = Path(__file__).parent / "weight_data.json"
WEIGHT_UPLOADS_DIR = Path(__file__).parent / "weight_uploads"
FOOD_IMAGES_PROCESSED_PATH = Path(__file__).parent / "food_images_processed.json"
FOOD_SCAN_INTERVAL = 300  # 食事画像スキャン間隔（秒）
MAX_FOOD_SCAN_IMAGES = 10  # 1回のスキャンで処理する最大画像数
TRASH_RETENTION_DAYS = 30  # ゴミ箱の保持日数
DEFAULT_FOLDER = "未分類"
PATIENT_DATA_FOLDER = "患者データ"
IMAGES_PER_PAGE = 10  # グリッド表示で1ページに表示する画像数

# ステータス定数
STATUS_AUTO = "auto_generated"
STATUS_REVIEWED = "reviewed"

# ソース識別子
SOURCE_PATIENT_DATA = "patient_data"
SOURCE_UPLOAD = "upload"

# ホーム画面の名言
QUOTES = [
    ("医術が愛されるところには、人間愛もまた存在する。", "ヒポクラテス"),
    ("良い医者は病気を治療し、偉大な医者は病気を持つ患者を治療する。", "ウィリアム・オスラー"),
    ("医学は不確実性の科学であり、確率の芸術である。", "ウィリアム・オスラー"),
    ("最良の医者は、最も少ない薬を処方する。", "ベンジャミン・フランクリン"),
    ("人の命を救うことにおいて、人は最も神に近づく。", "キケロ"),
    ("人生は短く、術の道は長い。", "ヒポクラテス"),
    ("書物なしに医学を学ぶことは、海図なき航海に出るようなものだ。", "ウィリアム・オスラー"),
    ("疑いは不快な状態だが、確信は愚かである。", "ヴォルテール"),
    ("観察こそが、人生における最も永続的な喜びである。", "ジョージ・メレディス"),
    ("医者は病気ではなく、病気に苦しむ患者を治療すべきである。", "マイモニデス"),
    ("偉大な仕事をする唯一の方法は、自分のやることを愛することだ。", "スティーブ・ジョブズ"),
    ("知ることが少ないから断言し、多くを学ぶほど慎重になる。", "モンテーニュ"),
    ("最大の栄光は一度も失敗しないことではなく、倒れるたびに起き上がることだ。", "孔子"),
    ("無知を恐れるな、偽りの知識を恐れよ。", "ブレーズ・パスカル"),
    ("学びて思わざれば則ち罔し、思いて学ばざれば則ち殆し。", "孔子"),
]


# ---------------------------------------------------------------------------
# 認証
# ---------------------------------------------------------------------------
def _make_auth_token(username: str, pw_hash: str) -> str:
    """ユーザー名とパスワードハッシュからログイントークンを生成する。"""
    return hmac.new(pw_hash.encode(), username.encode(), "sha256").hexdigest()[:16]


def _check_auth() -> bool:
    """ログイン認証。認証済みならTrue、未認証ならログイン画面を表示してFalse。"""
    if st.session_state.get("authenticated"):
        return True

    # secrets.toml に [auth.users] がなければ認証スキップ（開発用）
    try:
        auth_users = dict(st.secrets["auth"]["users"])
    except (KeyError, FileNotFoundError):
        return True  # 認証設定なし → フリーアクセス

    # URLのquery paramにtokenがあれば自動ログイン
    token = st.query_params.get("token")
    if token:
        for uname, stored_hash in auth_users.items():
            expected_token = _make_auth_token(uname, stored_hash)
            if token == expected_token:
                st.session_state["authenticated"] = True
                st.session_state["auth_user"] = uname
                # localStorageにトークンを保存（ブラウザ再起動後も有効）
                _save_token_to_storage(uname, expected_token)
                return True

    # localStorageからトークンを復元（tokenパラメータがない場合）
    if not token:
        _inject_auto_login_script()

    # ログイン画面
    st.markdown(
        "<h1 style='text-align:center; margin-top:60px;'>🧸 Clinical Knowledge Base</h1>",
        unsafe_allow_html=True,
    )
    st.markdown(
        "<p style='text-align:center; color:#888;'>アクセスするにはログインが必要です</p>",
        unsafe_allow_html=True,
    )

    # 中央寄せ用カラム
    _, col_form, _ = st.columns([1, 2, 1])
    with col_form:
        with st.form("login_form"):
            username = st.text_input("ユーザー名", placeholder="ユーザー名を入力")
            password = st.text_input("パスワード", type="password", placeholder="パスワードを入力")
            submitted = st.form_submit_button("🔐 ログイン", type="primary", use_container_width=True)

        if submitted:
            if not username or not password:
                st.error("ユーザー名とパスワードを入力してください。")
            else:
                pw_hash = hashlib.sha256(password.encode()).hexdigest()
                if username in auth_users and auth_users[username] == pw_hash:
                    st.session_state["authenticated"] = True
                    st.session_state["auth_user"] = username
                    auth_token = _make_auth_token(username, pw_hash)
                    st.query_params["token"] = auth_token
                    # localStorageにトークンを保存
                    _save_token_to_storage(username, auth_token)
                    st.rerun()
                else:
                    st.error("ユーザー名またはパスワードが正しくありません。")

    return False


def _save_token_to_storage(username: str, token: str) -> None:
    """ブラウザの localStorage にログイントークンを保存する。"""
    import streamlit.components.v1 as components
    components.html(
        f"""<script>
        try {{
            localStorage.setItem('ckb_auth_token', '{token}');
            localStorage.setItem('ckb_auth_user', '{username}');
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


# 画像解析プロンプト
ANALYSIS_PROMPT = """あなたは臨床経験豊富な専門医レベルの医療アシスタントです。
この画像を解析し、医師が臨床現場ですぐに活用できる形で、以下のJSON形式で出力してください。
JSON以外のテキストは一切含めないでください。

【重要】画像内の言語が英語やその他の言語であっても、出力はすべて日本語に翻訳してください。
専門用語は日本語の医学用語を使用し、必要に応じて括弧内に英語の原語を併記してください。
例: "大腿骨頭壊死（AVN）"、"磁気共鳴画像（MRI）"

{
  "title": "具体的で臨床的に有用なタイトル（疾患名・部位・画像種別を含む、日本語、30〜60文字程度）",
  "summary": "臨床上重要なポイントを5項目の箇条書きで抽出（各項目は具体的な所見・数値・診断名を含む1〜2文）。以下の形式で出力：\\n• 【所見】具体的な画像所見（部位・範囲・性状を明記）\\n• 【診断】最も考えられる診断と主要な鑑別疾患\\n• 【臨床的意義】見逃した場合のリスクや緊急度\\n• 【次のアクション】追加検査・コンサルト・治療方針\\n• 【ピットフォール】注意すべき落とし穴や類似所見との鑑別ポイント",
  "keywords": ["疾患名", "解剖学的部位", "画像モダリティ", "臨床所見1", "臨床所見2", "鑑別診断", "関連する検査・治療"]
}

【キーワードの指針】6〜8個を目安に、以下のカテゴリから幅広くタグ付けしてください：
- 疾患名・病態（例: 大腿骨頭壊死、肺塞栓症）
- 解剖学的部位（例: 股関節、右下葉）
- 画像モダリティ（例: MRI T2強調、単純CT）
- 主要所見（例: 骨髄浮腫、すりガラス影）
- 鑑別疾患（例: 化膿性関節炎、関節リウマチ）
- 関連する臨床情報（例: ステロイド内服歴、緊急手術適応）"""

# ---------------------------------------------------------------------------
# 体重管理用 Gemini プロンプト
# ---------------------------------------------------------------------------
QUANTITY_OPTIONS = ["少なめ", "ふつう", "多め"]

# 食事タイプ（MoneyForward風カテゴリ分類）
MEAL_TYPE_ORDER = ["breakfast", "lunch", "dinner", "snack"]
MEAL_TYPE_LABELS = {
    "breakfast": "🌅 朝食",
    "lunch": "🌞 昼食",
    "dinner": "🌙 夕食",
    "snack": "🍪 間食",
}
MEAL_TYPE_COLORS = {
    "breakfast": "#FF9800",
    "lunch": "#2196F3",
    "dinner": "#673AB7",
    "snack": "#4CAF50",
}

FOOD_ANALYSIS_PROMPT = """あなたは管理栄養士です。この食事の画像（1枚または複数枚）を解析してください。

写っている料理の品目名、推定量、それぞれの推定カロリー（kcal）を日本語で出力してください。
複数の画像がある場合は、全ての画像に写っている品目をまとめて1つのリストで出力してください。
JSON以外のテキストは一切含めないでください。

出力形式:
{
    "items": [
        {"name": "品目名", "quantity": "推定量", "calories": 推定カロリー数値},
        {"name": "品目名", "quantity": "推定量", "calories": 推定カロリー数値}
    ],
    "total_calories": 合計カロリー数値
}

【ルール】
- 品目名は日本語で記載
- quantityは「少なめ」「ふつう」「多め」のいずれかで推定
- 量が判断できない場合は「ふつう」とする
- caloriesはquantityを考慮した整数値（kcalの数値のみ、単位は不要）
- 「少なめ」は標準の約0.6倍、「多め」は標準の約1.5倍のカロリー
- 見える範囲の全ての品目を列挙
- total_caloriesはitemsのcaloriesの合計と一致させること
- 飲み物が見える場合はそれも含めること
- 同じ料理が複数画像に写っている場合は重複カウントしないこと

また、各品目ごとに主要栄養素の推定値を「nutrients」オブジェクトとして追加してください。

拡張出力形式:
{
    "items": [
        {
            "name": "品目名",
            "quantity": "推定量",
            "calories": 推定カロリー数値,
            "nutrients": {
                "protein": たんぱく質(g),
                "fat": 脂質(g),
                "carbs": 炭水化物(g),
                "fiber": 食物繊維(g),
                "salt": 食塩相当量(g),
                "calcium": カルシウム(mg),
                "iron": 鉄(mg),
                "vitamin_a": ビタミンA(μgRAE),
                "vitamin_c": ビタミンC(mg),
                "vitamin_d": ビタミンD(μg)
            }
        }
    ],
    "total_calories": 合計カロリー数値
}

【栄養素ルール】
- 全ての栄養素は数値（小数可）で出力。単位は付けない
- quantityに応じて栄養素もスケーリングすること（少なめ=0.6倍、多め=1.5倍）
- 推定が困難な場合は0とする
- 日本食品標準成分表の値を参考に推定すること"""

WEIGHT_SCALE_PROMPT = """この画像は体重計の表示画面です。
表示されている体重の数値を読み取ってください。
JSON以外のテキストは一切含めないでください。

出力形式:
{
    "weight_kg": 数値（kg単位、小数第1位まで）,
    "confidence": "high" または "low"
}

【ルール】
- 数値が明瞭に読み取れる場合は confidence: "high"
- ぼやけていたり読み取りにくい場合は confidence: "low"
- 数値が全く読み取れない場合は weight_kg: null, confidence: "none"
- kg単位で出力（lbの場合はkgに変換）"""

CALORIE_RECALC_PROMPT = """以下の食品・料理名と量のリストについて、それぞれのカロリー（kcal）と栄養素を推定してください。
量を考慮してカロリーと栄養素を計算してください。
JSON以外のテキストは一切含めないでください。

入力:
{items_json}

出力形式:
{{"items": [{{"name": "品目名", "quantity": "量", "calories": 推定カロリー数値, "nutrients": {{"protein": たんぱく質(g), "fat": 脂質(g), "carbs": 炭水化物(g), "fiber": 食物繊維(g), "salt": 食塩相当量(g), "calcium": カルシウム(mg), "iron": 鉄(mg), "vitamin_a": ビタミンA(μgRAE), "vitamin_c": ビタミンC(mg), "vitamin_d": ビタミンD(μg)}}}}, ...]}}

【ルール】
- カロリーは整数値（kcalの数値のみ）
- 栄養素は数値（小数可）で出力。単位は付けない
- caloriesと栄養素はquantityを考慮した値にすること（少なめ=標準の約0.6倍、多め=標準の約1.5倍）
- 入力の品目名と量をそのまま返すこと（変更しない）
- 入力の順番を維持すること
- 推定が困難な栄養素は0とする
- 日本食品標準成分表の値を参考に推定すること"""

# ---------------------------------------------------------------------------
# 栄養素目標値（日本人の食事摂取基準 2020年版 — 成人男性18-64歳 目安）
# target = 推奨量/目安量, upper = 耐容上限量 (None = 設定なし)
# ---------------------------------------------------------------------------
DEFAULT_NUTRIENT_TARGETS: dict[str, dict] = {
    "protein":   {"label": "たんぱく質", "unit": "g",     "target": 65,   "upper": 130},
    "fat":       {"label": "脂質",       "unit": "g",     "target": 65,   "upper": 90},
    "carbs":     {"label": "炭水化物",   "unit": "g",     "target": 320,  "upper": 420},
    "fiber":     {"label": "食物繊維",   "unit": "g",     "target": 21,   "upper": None},
    "salt":      {"label": "食塩相当量", "unit": "g",     "target": None, "upper": 7.5},
    "calcium":   {"label": "カルシウム", "unit": "mg",    "target": 750,  "upper": 2500},
    "iron":      {"label": "鉄",         "unit": "mg",    "target": 7.5,  "upper": 50},
    "vitamin_a": {"label": "ビタミンA",  "unit": "μgRAE", "target": 850,  "upper": 2700},
    "vitamin_c": {"label": "ビタミンC",  "unit": "mg",    "target": 100,  "upper": None},
    "vitamin_d": {"label": "ビタミンD",  "unit": "μg",    "target": 8.5,  "upper": 100},
}

# PFC（三大栄養素）のキー
_PFC_KEYS = ["protein", "fat", "carbs"]
# 微量栄養素のキー（PFC・食塩以外）
_MICRO_KEYS = ["fiber", "calcium", "iron", "vitamin_a", "vitamin_c", "vitamin_d"]


def _get_nutrient_targets(goals: dict) -> dict[str, dict]:
    """ユーザー設定のある栄養素目標を返す。未設定ならデフォルト値。"""
    user_targets = goals.get("nutrient_targets", {})
    merged = {}
    for key, default in DEFAULT_NUTRIENT_TARGETS.items():
        merged[key] = {**default}
        if key in user_targets:
            if "target" in user_targets[key]:
                merged[key]["target"] = user_targets[key]["target"]
            if "upper" in user_targets[key]:
                merged[key]["upper"] = user_targets[key]["upper"]
    return merged

# チャット用システムプロンプト（知識ベース検索）
CHAT_SYSTEM_PROMPT = """あなたは臨床経験20年以上の指導医です。
質問者は初期研修医〜後期研修医レベルの若手医師です。
一般人向けの噛み砕いた説明は一切不要です。

以下の【保存された知識】のみに基づいて回答してください。

## 回答フォーマット（厳守）
回答は必ず**箇条書き**で要点のみを簡潔に書いてください。
冗長な文章は禁止です。各項目は具体的な所見・数値・薬剤名を含む1〜2文にしてください。

### 該当する知識が複数ある場合
項目ごとにセクションを分け、各セクション内を箇条書きで記載。

**出力例:**
## 項目名A [ID: xxxxx]
- **所見**: 具体的な画像所見（部位・範囲・性状）
- **診断**: 最も考えられる診断、鑑別
- **対応**: 追加検査・治療方針

## 項目名B [ID: yyyyy]
- **所見**: ...
- **診断**: ...
- **対応**: ...

### 該当する知識が1つの場合
以下の項目で箇条書き：
- **所見**: 画像所見の要点
- **診断**: 診断名と根拠
- **鑑別**: 除外すべき疾患
- **対応**: 次のアクション（検査・治療・コンサルト）
- **注意**: ピットフォールやRed flags

### 該当する知識がない場合
「保存された知識にはありません」とだけ答えてください。

## ルール
1. 根拠となる「ID」を必ず明記（例: [ID: xxxxx]）
2. 専門用語をそのまま使用し英語略語を併記（例: AVN、DWI）
3. 画像の要約・キーワードに含まれる具体的所見・数値をそのまま反映
4. 類義語・関連疾患・同一臓器系も広く検索
5. 地の文（段落）は書かない。箇条書きのみ。

【保存された知識】
{knowledge_context}
"""



# ---------------------------------------------------------------------------
# Google Sheets 永続化
# ---------------------------------------------------------------------------
_SHEETS_CHUNK_SIZE = 49000  # 1セル上限50,000文字の安全マージン
_SHEETS_WORKSHEETS = ["metadata", "folders", "chat_sessions", "trash", "weight_data", "food_processed"]
_CACHE_TTL = 30  # 秒


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


def _invalidate_all_caches():
    """全データキャッシュを無効化し、次回読み込みでSheetsから再取得させる。"""
    for ck in ["_cache_metadata", "_cache_trash", "_cache_ignore_list", "_cache_folders", "_cache_chat_sessions", "_cache_weight_data", "_cache_food_processed"]:
        st.session_state.pop(ck, None)
        st.session_state.pop(f"{ck}_ts", None)


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
    try:
        with open(METADATA_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except IOError:
        pass
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
    try:
        with open(METADATA_PATH, "w", encoding="utf-8") as f:
            json.dump(metadata, f, ensure_ascii=False, indent=2)
    except IOError:
        pass
    if not sheets_ok and sh is not None:
        # 次回 rerun で再試行するためペンディングデータを保持
        st.session_state["_pending_metadata"] = metadata
        try:
            detail = st.session_state.pop("_save_error_detail", "")
            msg = "⚠️ Sheetsへの保存に失敗しました。次回アクセス時に再試行します。"
            if detail:
                msg += f"\n({detail})"
            st.toast(msg, icon="⚠️")
        except Exception:
            pass
    elif sheets_ok:
        # 成功したらペンディングをクリア
        st.session_state.pop("_pending_metadata", None)
    return sheets_ok


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


def get_status(meta: dict) -> str:
    """メタデータからステータスを取得する。"""
    return meta.get("status", STATUS_AUTO)


def get_status_icon(meta: dict) -> str:
    """ステータスに応じたアイコンを返す。"""
    s = get_status(meta)
    if s == STATUS_REVIEWED:
        return "✅"
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
# ゴミ箱管理
# ---------------------------------------------------------------------------
def load_trash() -> list:
    """ゴミ箱データを読み込む。session_state → Sheets → ローカルの順。"""
    ck = "_cache_trash"
    if _is_cache_valid(ck):
        return st.session_state[ck]
    sh = get_sheets_client()
    if sh is not None:
        data = _read_json_from_sheet(sh, "trash")
        if data is not None:
            items = data.get("items", []) if isinstance(data, dict) else data
            _set_cache(ck, items)
            try:
                with open(TRASH_PATH, "w", encoding="utf-8") as f:
                    json.dump({"items": items}, f, ensure_ascii=False, indent=2)
            except IOError:
                pass
            return items
    if TRASH_PATH.exists():
        try:
            with open(TRASH_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                items = data.get("items", [])
                _set_cache(ck, items)
                return items
        except (json.JSONDecodeError, IOError):
            pass
    _set_cache(ck, [])
    return []


def save_trash(items: list) -> None:
    """ゴミ箱データを保存する。session_state + Sheets + ローカル。"""
    _set_cache("_cache_trash", items)
    sh = get_sheets_client()
    if sh is not None:
        _write_json_to_sheet(sh, "trash", {"items": items})
    try:
        with open(TRASH_PATH, "w", encoding="utf-8") as f:
            json.dump({"items": items}, f, ensure_ascii=False, indent=2)
    except IOError:
        pass


# ---------------------------------------------------------------------------
# 無視リスト管理（削除した画像の再取り込み防止）
# ---------------------------------------------------------------------------
def load_ignore_list() -> set[str]:
    """無視リストを読み込む。session_state → Sheets → ローカルの順。"""
    ck = "_cache_ignore_list"
    if _is_cache_valid(ck):
        return st.session_state[ck]
    sh = get_sheets_client()
    if sh is not None:
        data = _read_json_from_sheet(sh, "ignore_list")
        if data is not None:
            ids = set(data.get("ids", []) if isinstance(data, dict) else data)
            _set_cache(ck, ids)
            try:
                with open(IGNORE_LIST_PATH, "w", encoding="utf-8") as f:
                    json.dump({"ids": sorted(ids)}, f, ensure_ascii=False, indent=2)
            except IOError:
                pass
            return ids
    if IGNORE_LIST_PATH.exists():
        try:
            with open(IGNORE_LIST_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                ids = set(data.get("ids", []))
                _set_cache(ck, ids)
                return ids
        except (json.JSONDecodeError, IOError):
            pass
    _set_cache(ck, set())
    return set()


def save_ignore_list(ids: set[str]) -> None:
    """無視リストを保存する。session_state + Sheets + ローカル。"""
    _set_cache("_cache_ignore_list", ids)
    sh = get_sheets_client()
    if sh is not None:
        _write_json_to_sheet(sh, "ignore_list", {"ids": sorted(ids)})
    try:
        with open(IGNORE_LIST_PATH, "w", encoding="utf-8") as f:
            json.dump({"ids": sorted(ids)}, f, ensure_ascii=False, indent=2)
    except IOError:
        pass


def add_to_ignore_list(file_ids: list[str]) -> None:
    """指定されたファイルIDを無視リストに追加する。"""
    ids = load_ignore_list()
    ids.update(file_ids)
    save_ignore_list(ids)


def remove_from_ignore_list(file_ids: list[str]) -> None:
    """指定されたファイルIDを無視リストから除去する。"""
    ids = load_ignore_list()
    ids.difference_update(file_ids)
    save_ignore_list(ids)


def move_to_trash(file_ids: list[str], metadata: dict) -> int:
    """指定されたファイルIDの解析データをゴミ箱に移動する。移動した件数を返す。
    同時に無視リストにも追加し、再スキャンで再取り込みされないようにする。"""
    trash = load_trash()
    moved = 0
    moved_ids: list[str] = []
    for fid in file_ids:
        if fid in metadata:
            trash.append({
                "file_id": fid,
                "metadata": metadata[fid].copy(),
                "deleted_at": datetime.now().isoformat(),
            })
            del metadata[fid]
            moved_ids.append(fid)
            moved += 1
    save_metadata(metadata)
    save_trash(trash)
    # 無視リストに追加して再スキャン時の再取り込みを防止
    if moved_ids:
        add_to_ignore_list(moved_ids)
    return moved


def restore_from_trash(indices: list[int]) -> int:
    """ゴミ箱の指定インデックスのアイテムを復元する。復元した件数を返す。"""
    trash = load_trash()
    metadata = load_metadata()
    restored = 0
    restored_ids: list[str] = []
    # インデックスを降順にソートして削除時にずれないようにする
    for idx in sorted(indices, reverse=True):
        if 0 <= idx < len(trash):
            item = trash.pop(idx)
            fid = item["file_id"]
            metadata[fid] = item["metadata"]
            restored_ids.append(fid)
            restored += 1
    save_metadata(metadata)
    save_trash(trash)
    # 無視リストからも除去して再スキャン対象に戻す
    if restored_ids:
        remove_from_ignore_list(restored_ids)
    return restored


def purge_old_trash() -> int:
    """保持期間を過ぎたゴミ箱アイテムを完全削除する。削除した件数を返す。"""
    trash = load_trash()
    now = datetime.now()
    remaining = []
    purged = 0
    for item in trash:
        try:
            deleted_at = datetime.fromisoformat(item["deleted_at"])
            if (now - deleted_at).days < TRASH_RETENTION_DAYS:
                remaining.append(item)
            else:
                purged += 1
        except (ValueError, KeyError):
            remaining.append(item)
    if purged > 0:
        save_trash(remaining)
    return purged


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
            try:
                with open(FOLDERS_PATH, "w", encoding="utf-8") as f:
                    json.dump({"folders": folders}, f, ensure_ascii=False, indent=2)
            except IOError:
                pass
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
    sh = get_sheets_client()
    if sh is not None:
        _write_json_to_sheet(sh, "folders", {"folders": folders})
    try:
        with open(FOLDERS_PATH, "w", encoding="utf-8") as f:
            json.dump({"folders": folders}, f, ensure_ascii=False, indent=2)
    except IOError:
        pass


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
# チャットセッション管理
# ---------------------------------------------------------------------------
def load_chat_sessions() -> dict:
    """チャットセッションを読み込む。session_state → Sheets → ローカルの順。"""
    ck = "_cache_chat_sessions"
    if _is_cache_valid(ck):
        return st.session_state[ck]
    sh = get_sheets_client()
    if sh is not None:
        data = _read_json_from_sheet(sh, "chat_sessions")
        if data is not None:
            sessions = data.get("sessions", {}) if isinstance(data, dict) else data
            _set_cache(ck, sessions)
            try:
                with open(CHAT_SESSIONS_PATH, "w", encoding="utf-8") as f:
                    json.dump({"sessions": sessions}, f, ensure_ascii=False, indent=2)
            except IOError:
                pass
            return sessions
    if CHAT_SESSIONS_PATH.exists():
        try:
            with open(CHAT_SESSIONS_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                sessions = data.get("sessions", {})
                _set_cache(ck, sessions)
                return sessions
        except (json.JSONDecodeError, IOError):
            pass
    _set_cache(ck, {})
    return {}


def save_chat_sessions(sessions: dict) -> None:
    """チャットセッションを保存する。session_state + Sheets + ローカル。"""
    _set_cache("_cache_chat_sessions", sessions)
    sh = get_sheets_client()
    if sh is not None:
        _write_json_to_sheet(sh, "chat_sessions", {"sessions": sessions})
    try:
        with open(CHAT_SESSIONS_PATH, "w", encoding="utf-8") as f:
            json.dump({"sessions": sessions}, f, ensure_ascii=False, indent=2)
    except IOError:
        pass


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
        except Exception:
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
        # goals はローカルが新しければ上書き
        if not merged.get("goals") and local_data.get("goals"):
            merged["goals"] = local_data["goals"]
        if new_from_local > 0:
            _log.info(f"[load_weight_data] ローカルから {new_from_local} 件を補完")
            try:
                _write_json_to_sheet(sh, "weight_data", merged)
            except Exception:
                pass
        data = merged
    elif sheets_data is not None:
        data = sheets_data
    elif local_data is not None:
        data = local_data
    else:
        data = default

    _set_cache(ck, data)
    try:
        with open(WEIGHT_DATA_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except IOError:
        pass
    return data


def save_weight_data(weight_data: dict, show_error: bool = True) -> bool:
    """体重管理データを保存する。session_state + Sheets + ローカルJSON。"""
    _set_cache("_cache_weight_data", weight_data)
    sheets_ok = False
    sh = get_sheets_client()
    if sh is not None:
        try:
            sheets_ok = _write_json_to_sheet(sh, "weight_data", weight_data)
        except Exception:
            try:
                st.session_state.pop("_sheets_conn", None)
                sh2 = _new_sheets_connection()
                if sh2 is not None:
                    sheets_ok = _write_json_to_sheet(sh2, "weight_data", weight_data)
            except Exception:
                pass
    try:
        with open(WEIGHT_DATA_PATH, "w", encoding="utf-8") as f:
            json.dump(weight_data, f, ensure_ascii=False, indent=2)
    except IOError:
        pass
    if not sheets_ok and sh is not None:
        st.session_state["_pending_weight_data"] = weight_data
        if show_error:
            detail = st.session_state.pop("_save_error_detail", "")
            msg = "⚠️ Sheetsへの保存に失敗しました。次回アクセス時に再試行します。"
            if detail:
                msg += f"\n({detail})"
            st.toast(msg, icon="⚠️")
    elif sheets_ok:
        st.session_state.pop("_pending_weight_data", None)
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
        st.error(f"Google Drive への認証に失敗しました: {e}")
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
    except Exception:
        return None


def get_food_folder_id() -> str | None:
    """食事画像フォルダIDを取得する。未設定なら自動作成して返す。"""
    # 1. secrets.toml から取得を試みる
    try:
        fid = st.secrets.get("food_images_folder_id", "")
        if fid:
            return fid
    except Exception:
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
        except Exception:
            pass

    try:
        if FOOD_IMAGES_PROCESSED_PATH.exists():
            with open(FOOD_IMAGES_PROCESSED_PATH, "r", encoding="utf-8") as f:
                local_data = json.load(f)
    except Exception:
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
            except Exception:
                pass
        data = merged
    elif sheets_data is not None:
        data = sheets_data
    elif local_data is not None:
        data = local_data
    else:
        data = {}

    _set_cache(ck, data)
    try:
        with open(FOOD_IMAGES_PROCESSED_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except IOError:
        pass
    return data


def save_food_processed(data: dict) -> None:
    """処理済み食事画像IDの辞書を保存する。Sheets + ローカル。"""
    _set_cache("_cache_food_processed", data)
    sh = get_sheets_client()
    if sh is not None:
        try:
            _write_json_to_sheet(sh, "food_processed", data)
        except Exception:
            try:
                st.session_state.pop("_sheets_conn", None)
                sh2 = _new_sheets_connection()
                if sh2 is not None:
                    _write_json_to_sheet(sh2, "food_processed", data)
            except Exception:
                pass
    try:
        with open(FOOD_IMAGES_PROCESSED_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


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
@st.cache_data(ttl=120, show_spinner="ファイル一覧を取得中...")
def list_images(_service, folder_id: str) -> list[dict]:
    """指定フォルダ内の画像ファイル一覧を取得する（2分キャッシュ、ページネーション対応）。"""
    mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
    query = f"'{folder_id}' in parents and ({mime_query}) and trashed=false"
    all_files: list[dict] = []
    page_token = None
    max_retries = 3
    while True:
        for attempt in range(max_retries):
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
                break  # 成功 → ページループ次へ
            except HttpError as e:
                if e.resp.status == 404:
                    st.error(
                        "指定されたフォルダが見つかりません。\n\n"
                        "`folder_id` が正しいか、サービスアカウントにフォルダが"
                        "共有されているか確認してください。"
                    )
                    return []
                if attempt < max_retries - 1:
                    time.sleep(2)
                    continue
                st.warning("⚠️ Google Driveとの通信に失敗しました。ページを再読み込みしてください。")
                return all_files  # 取得済み分を返す
            except Exception:
                if attempt < max_retries - 1:
                    time.sleep(2)
                    continue
                st.warning("⚠️ Google Driveとの通信に失敗しました。ページを再読み込みしてください。")
                return all_files
        else:
            # for ループの else = 全リトライ失敗
            return all_files
        if not page_token:
            break
    return all_files


@st.cache_data(ttl=120, show_spinner="患者データを取得中...")
def list_patient_images(_service, patient_folder_id: str) -> list[dict]:
    """患者データフォルダ内の画像ファイル一覧を取得する（2分キャッシュ、ページネーション対応）。"""
    mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
    query = f"'{patient_folder_id}' in parents and ({mime_query}) and trashed=false"
    all_files: list[dict] = []
    page_token = None
    max_retries = 3
    while True:
        for attempt in range(max_retries):
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
                    return []
                if attempt < max_retries - 1:
                    time.sleep(2)
                    continue
                return all_files
            except Exception:
                if attempt < max_retries - 1:
                    time.sleep(2)
                    continue
                return all_files
        else:
            return all_files
        if not page_token:
            break
    return all_files


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


@st.cache_data(ttl=300, show_spinner=False, max_entries=50)
def download_image(_service, file_id: str) -> bytes:
    """画像をバイト列で返す。ローカルアップロード画像を優先し、なければGoogle Driveから取得。"""
    # ローカルアップロード画像を確認
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



# ---------------------------------------------------------------------------
# Gemini AI (REST API 直接呼び出し)
# ---------------------------------------------------------------------------
_GEMINI_MODEL = "gemini-2.0-flash"
_GEMINI_API_URL = (
    "https://generativelanguage.googleapis.com/v1beta/models/"
    "{model}:generateContent?key={key}"
)


def _gemini_generate(api_key: str, contents: list, model: str | None = None) -> str:
    """Gemini REST API を呼び出してテキスト応答を返す。

    contents は Gemini API の ``parts`` 形式のリスト。
    テキストのみの場合: [{"text": "..."}]
    画像付きの場合: [{"text": "..."}, {"inline_data": {"mime_type": "...", "data": "..."}}]
    """
    url = _GEMINI_API_URL.format(model=model or _GEMINI_MODEL, key=api_key)
    payload = {"contents": [{"parts": contents}]}
    resp = requests.post(url, json=payload, timeout=120)
    resp.raise_for_status()
    data = resp.json()
    return data["candidates"][0]["content"]["parts"][0]["text"]


# ---------------------------------------------------------------------------
# Gemini AI 解析（画像）
# ---------------------------------------------------------------------------
def analyze_image_with_gemini(image_bytes: bytes, api_key: str, correction_hint: str = "") -> dict | None:
    """Gemini 2.0 Flash で画像を解析し、結果辞書を返す。

    correction_hint が指定された場合、プロンプトに修正指示を追加する。
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
        required_keys = {"title", "summary", "keywords"}
        if not required_keys.issubset(result.keys()):
            st.warning("AI解析の結果に必要な項目が不足しています。再度お試しください。")
            return None

        result["status"] = STATUS_AUTO
        return result

    except json.JSONDecodeError:
        st.error("AI解析の結果をJSONとして解析できませんでした。再度お試しください。")
        return None
    except Exception as e:
        st.error(f"AI解析中にエラーが発生しました: {e}")
        return None


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


def analyze_food_image(image_bytes: bytes, api_key: str) -> dict | None:
    """食事画像を Gemini で解析し、品目とカロリーを推定する。"""
    return analyze_food_images([image_bytes], api_key)


def analyze_food_images(images_bytes_list: list[bytes], api_key: str) -> dict | None:
    """複数の食事画像をまとめて Gemini で解析し、品目とカロリーを推定する。"""
    try:
        parts = [{"text": FOOD_ANALYSIS_PROMPT}]
        for img_bytes in images_bytes_list:
            pil_image = Image.open(io.BytesIO(img_bytes))
            fmt = pil_image.format or "PNG"
            mime_type = f"image/{fmt.lower()}"
            if mime_type == "image/jpg":
                mime_type = "image/jpeg"
            b64_data = base64.b64encode(img_bytes).decode("utf-8")
            parts.append({"inline_data": {"mime_type": mime_type, "data": b64_data}})
        response_text = _gemini_generate(api_key, parts)
        result = _parse_gemini_json(response_text)
        if "items" not in result:
            return None
        return result
    except (json.JSONDecodeError, KeyError):
        st.error("食事画像の解析結果をJSONとして読み取れませんでした。")
        return None
    except Exception as e:
        st.error(f"食事画像の解析中にエラーが発生しました: {e}")
        return None


def analyze_weight_scale_image(image_bytes: bytes, api_key: str) -> dict | None:
    """体重計の画像から Gemini で数値を読み取る。"""
    try:
        pil_image = Image.open(io.BytesIO(image_bytes))
        fmt = pil_image.format or "PNG"
        mime_type = f"image/{fmt.lower()}"
        if mime_type == "image/jpg":
            mime_type = "image/jpeg"
        b64_data = base64.b64encode(image_bytes).decode("utf-8")
        parts = [
            {"text": WEIGHT_SCALE_PROMPT},
            {"inline_data": {"mime_type": mime_type, "data": b64_data}},
        ]
        response_text = _gemini_generate(api_key, parts)
        result = _parse_gemini_json(response_text)
        return result
    except (json.JSONDecodeError, KeyError):
        st.error("体重計の読み取り結果をJSONとして解析できませんでした。")
        return None
    except Exception as e:
        st.error(f"体重計の読み取り中にエラーが発生しました: {e}")
        return None


def _generate_weight_comment(day_data: dict, goals: dict) -> str:
    """目標に対する日次コメントを生成する（ルールベース）。"""
    comments = []
    target_cal = goals.get("daily_calorie_target")
    target_wt = goals.get("target_weight_kg")
    target_date_str = goals.get("target_date")
    total_cal = day_data.get("total_calories", 0)
    weight = day_data.get("weight")

    # カロリー目標コメント
    if target_cal and target_cal > 0:
        diff = target_cal - total_cal
        if diff > 0:
            comments.append(f"あと **{diff} kcal** 摂取できます。")
        elif diff == 0:
            comments.append("目標カロリーぴったりです！")
        else:
            comments.append(f"⚠️ 目標カロリーを **{abs(diff)} kcal** オーバーしています。")

    # 体重目標コメント
    if target_wt and target_wt > 0 and weight:
        wt_diff = round(weight - target_wt, 1)
        if wt_diff > 0:
            comments.append(f"目標体重まであと **{wt_diff} kg** です。")
        elif wt_diff == 0:
            comments.append("🎉 目標体重を達成しています！")
        else:
            comments.append(f"🎉 目標体重を **{abs(wt_diff)} kg** 下回っています！")

    # 目標期日コメント
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
        comments.append("🎯 目標を設定すると進捗コメントが表示されます。")

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
    except Exception:
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


def _aggregate_day_nutrients(day_data: dict) -> dict[str, float]:
    """1日の全品目から栄養素を合算して返す。

    Returns:
        {"protein": 合計g, "fat": 合計g, ...}  キーがない場合は0。
    """
    totals: dict[str, float] = {}
    for item in _get_day_items(day_data):
        nuts = item.get("nutrients", {})
        for key, val in nuts.items():
            if isinstance(val, (int, float)):
                totals[key] = totals.get(key, 0) + val
    return totals


def _guess_meal_type(hour: int | None = None) -> str:
    """時刻から食事タイプを推定する。hourが省略された場合は現在時刻を使用。"""
    if hour is None:
        hour = datetime.now().hour
    if 4 <= hour < 10:
        return "breakfast"
    elif 10 <= hour < 15:
        return "lunch"
    elif 15 <= hour < 21:
        return "dinner"
    else:
        return "snack"


def _guess_meal_type_from_dt(dt: datetime) -> str:
    """datetime から食事タイプを推定する。"""
    return _guess_meal_type(dt.hour)


def _group_items_by_meal(items: list[dict]) -> dict:
    """品目リストを meal_type でグループ化。OrderedDict で MEAL_TYPE_ORDER 順に返す。"""
    from collections import OrderedDict
    groups = OrderedDict()
    for mt in MEAL_TYPE_ORDER:
        groups[mt] = []
    unset = []
    for it in items:
        mt = it.get("meal_type")
        if mt in groups:
            groups[mt].append(it)
        else:
            unset.append(it)
    if unset:
        groups["unset"] = unset
    return groups


def _recalc_calories(items_for_recalc: list[dict], api_key: str) -> list[dict] | None:
    """品目名+量リストからGeminiでカロリーと栄養素を再推定する。

    items_for_recalc: [{"name": "品目名", "quantity": "ふつう"}, ...]
    Returns: [{"calories": int, "nutrients": dict}, ...] or None
    """
    try:
        items_json = json.dumps(items_for_recalc, ensure_ascii=False)
        prompt = CALORIE_RECALC_PROMPT.replace("{items_json}", items_json)
        parts = [{"text": prompt}]
        response_text = _gemini_generate(api_key, parts)
        result = _parse_gemini_json(response_text)
        if result and "items" in result:
            return [
                {
                    "calories": it.get("calories", 0),
                    "nutrients": it.get("nutrients", {}),
                }
                for it in result["items"]
            ]
    except Exception:
        pass
    return None


def generate_keywords_with_gemini(image_bytes: bytes, api_key: str, title: str = "") -> list[str] | None:
    """Gemini で画像からキーワード（タグ）のみを生成する。

    患者データ用：フル解析ではなくキーワード抽出のみ。
    """
    try:
        pil_image = Image.open(io.BytesIO(image_bytes))
        fmt = pil_image.format or "PNG"
        mime_type = f"image/{fmt.lower()}"
        if mime_type == "image/jpg":
            mime_type = "image/jpeg"
        b64_data = base64.b64encode(image_bytes).decode("utf-8")

        title_hint = f"\nこの画像のタイトル: 「{title}」" if title else ""
        prompt = (
            "あなたは臨床経験豊富な専門医です。\n"
            "この医療画像に適切なキーワード（タグ）を6〜8個生成してください。\n"
            f"{title_hint}\n\n"
            "以下のカテゴリから幅広くタグ付けしてください：\n"
            "- 疾患名・病態\n"
            "- 解剖学的部位\n"
            "- 画像モダリティ（MRI、CT、X線など）\n"
            "- 主要所見\n"
            "- 鑑別疾患\n"
            "- 関連する臨床情報\n\n"
            "【重要】出力はJSON配列のみ。他のテキストは一切不要。\n"
            '例: ["大腿骨頭壊死", "股関節", "MRI T2強調", "骨髄浮腫", "ステロイド内服歴"]'
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
        if isinstance(result, list):
            return [str(k) for k in result if k]
        return None

    except Exception as e:
        st.error(f"AIキーワード生成中にエラーが発生しました: {e}")
        return None


# ---------------------------------------------------------------------------
# 新着画像の自動検知 & AI解析
# ---------------------------------------------------------------------------
AUTO_SCAN_INTERVAL = 300  # 秒（5分おき）


def _auto_classify_folder(meta: dict, api_key: str, folders: list[str]) -> str:
    """AI解析結果のメタデータから、既存フォルダの中で最適なものを返す。

    該当するフォルダがなければ DEFAULT_FOLDER（未分類）を返す。
    フォルダが未分類しかない場合もそのまま未分類を返す。
    """
    # 未分類以外のフォルダが存在しなければ分類しない
    real_folders = [f for f in folders if f != DEFAULT_FOLDER]
    if not real_folders:
        return DEFAULT_FOLDER

    title = meta.get("title", "")
    summary = meta.get("summary", "")
    keywords = ", ".join(meta.get("keywords", []))
    folder_names = ", ".join(real_folders)

    prompt = (
        f"以下の医療画像を最も適切なフォルダに分類してください。\n\n"
        f"タイトル: {title}\n要約: {summary}\nキーワード: {keywords}\n\n"
        f"選択肢: {folder_names}\n\n"
        f"どの選択肢にも当てはまらない場合は「{DEFAULT_FOLDER}」と出力してください。\n"
        f"フォルダ名のみを1つだけ出力してください。"
    )

    try:
        result = _gemini_generate(api_key, [{"text": prompt}]).strip()
        # フォルダ名リストから最も近いものを選択
        for f in folders:
            if f in result or result in f:
                return f
        return DEFAULT_FOLDER
    except Exception:
        return DEFAULT_FOLDER


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
        ignore_p = load_ignore_list()
        new_patient = [img for img in patient_images if img["id"] not in metadata and img["id"] not in ignore_p]

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
                st.sidebar.info(
                    f"🏥 患者データ {p_count} 件を自動登録しました（AI解析なし）"
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
        ignore = load_ignore_list()
        # 患者データフォルダにあるファイルはメインスキャンから除外
        new_images = [
            img for img in drive_images
            if img["id"] not in metadata
            and img["id"] not in ignore
            and img["id"] not in patient_registered_ids
        ]

        if new_images:
            batch = new_images[:MAX_AUTO_ANALYZE]
            remaining = len(new_images) - len(batch)

            folders = load_folders()

            success_count = 0
            classified_count = 0
            scan_placeholder = st.sidebar.empty()
            scan_placeholder.info(
                f"🔄 新着画像 {len(new_images)} 件を検知。自動解析・登録中..."
            )

            for img in batch:
                fid = img["id"]
                try:
                    image_bytes = download_image(service, fid)

                    result = analyze_image_with_gemini(image_bytes, api_key)
                    if result:
                        result["status"] = STATUS_REVIEWED
                        assigned_folder = _auto_classify_folder(result, api_key, folders)
                        result["folder"] = assigned_folder
                        if assigned_folder != DEFAULT_FOLDER:
                            classified_count += 1
                        metadata[fid] = result
                        success_count += 1
                except Exception:
                    continue

            if success_count > 0:
                save_metadata(metadata)
                _invalidate_all_caches()
                list_images.clear()
                list_patient_images.clear()
                msg = f"✅ 新着 {success_count} 件を自動登録しました！"
                if classified_count > 0:
                    msg += f"\n（{classified_count} 件をフォルダに自動分類）"
                if remaining > 0:
                    msg += f"\n（残り {remaining} 件は次回スキャン時に処理）"
                scan_placeholder.success(msg)
            else:
                scan_placeholder.empty()


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
        ignore_p = load_ignore_list()
        new_patient = [img for img in patient_images if img["id"] not in metadata and img["id"] not in ignore_p]

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
    ignore = load_ignore_list()
    # 患者データフォルダにあるファイルはメインスキャンから除外
    new_images = [
        img for img in drive_images
        if img["id"] not in metadata
        and img["id"] not in ignore
        and img["id"] not in patient_registered_ids
    ]

    if not new_images:
        status_text.success("✅ 新着画像はありません。すべて解析済みです。")
        st.caption(f"Google Drive: {len(drive_images)} 件 / 解析済み: {len(metadata)} 件")
    else:
        status_text.info(
            f"🆕 新着 **{len(new_images)}** 件を検出！ AI解析・自動登録を開始します..."
        )

        folders = load_folders()

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
                image_bytes = download_image(service, fid)

                result = analyze_image_with_gemini(image_bytes, api_key)
                if result:
                    result["status"] = STATUS_REVIEWED
                    assigned_folder = _auto_classify_folder(result, api_key, folders)
                    result["folder"] = assigned_folder
                    metadata[fid] = result
                    success_count += 1
                    folder_label = f" → 📁 {assigned_folder}" if assigned_folder != DEFAULT_FOLDER else ""
                    with results_container:
                        st.markdown(
                            f"✅ **{result.get('title', fname)}**{folder_label}  \n"
                            f"<span style='color:#888;font-size:12px;'>"
                            f"{', '.join(result.get('keywords', [])[:4])}</span>",
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


def scan_food_images(service, food_folder_id: str, api_key: str,
                     manual: bool = False) -> int:
    """Google Driveの食事画像フォルダをスキャンし、未処理画像をAI解析して仮登録する。

    Args:
        service: Google Drive API クライアント
        food_folder_id: 食事画像フォルダID
        api_key: Gemini API キー
        manual: True=手動スキャン（件数制限なし）, False=自動スキャン

    Returns:
        処理した画像数
    """
    if not manual:
        # 自動スキャン: クールダウンチェック
        now = time.time()
        last_scan = st.session_state.get("food_scan_last", 0)
        if now - last_scan < FOOD_SCAN_INTERVAL:
            return 0
        st.session_state["food_scan_last"] = now

    # 処理済みリスト読み込み
    processed = load_food_processed()

    # Google Driveから画像一覧を取得（ページネーション対応）
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
            st.error(f"Google Driveの読み取りに失敗しました: {e}")
        if not all_files:
            return 0

    # 未処理画像を抽出（手動スキャン時はAI解析失敗分も再処理）
    if manual:
        new_files = [
            f for f in all_files
            if f["id"] not in processed
            or processed.get(f["id"], {}).get("status") in ("no_items", "error")
        ]
    else:
        new_files = [f for f in all_files if f["id"] not in processed]
    if not new_files:
        return 0

    # 件数制限（自動スキャン時のみ）
    if not manual:
        new_files = new_files[:MAX_FOOD_SCAN_IMAGES]

    # weight_data を読み込み
    weight_data = load_weight_data()
    records = weight_data.setdefault("records", {})

    count = 0
    for file_info in new_files:
        file_id = file_info["id"]
        file_name = file_info.get("name", file_id)

        try:
            # 画像をダウンロード
            img_bytes = download_image(service, file_id)
            if not img_bytes:
                continue

            # EXIF日時を取得 → フォールバック: Driveの modifiedTime → 今日
            photo_dt = _extract_exif_datetime(img_bytes)
            if photo_dt is None:
                # Drive の modifiedTime を使用
                mod_time_str = file_info.get("modifiedTime", "")
                if mod_time_str:
                    try:
                        # ISO 8601 format: 2026-02-26T09:12:43.000Z
                        photo_dt = datetime.fromisoformat(
                            mod_time_str.replace("Z", "+00:00")
                        )
                    except (ValueError, TypeError):
                        pass
            if photo_dt is None:
                photo_dt = datetime.now()

            date_key = photo_dt.strftime("%Y-%m-%d")

            # 画像をローカル保存
            WEIGHT_UPLOADS_DIR.mkdir(exist_ok=True)
            img_id = f"wm_{uuid.uuid4().hex[:12]}"
            ext = file_name.rsplit(".", 1)[-1].lower() if "." in file_name else "png"
            if ext not in ("jpg", "jpeg", "png"):
                ext = "png"
            (WEIGHT_UPLOADS_DIR / f"{img_id}.{ext}").write_bytes(img_bytes)

            # AI解析
            result = analyze_food_images([img_bytes], api_key)
            if result and "items" in result and result["items"]:
                day_data = records.setdefault(date_key, {"items": [], "total_calories": 0})
                for it in result["items"]:
                    item_entry = {
                        "id": f"item_{uuid.uuid4().hex[:12]}",
                        "name": it.get("name", "不明"),
                        "quantity": it.get("quantity", "ふつう"),
                        "calories": it.get("calories", 0),
                        "nutrients": it.get("nutrients", {}),
                        "meal_type": _guess_meal_type_from_dt(photo_dt),
                        "image_id": img_id,
                        "image_ext": ext,
                        "drive_file_id": file_id,
                    }
                    day_data["items"].append(item_entry)

                # 合計カロリー再計算
                all_items = _get_day_items(day_data)
                day_data["total_calories"] = sum(
                    it.get("calories", 0) for it in all_items
                )

                processed[file_id] = {
                    "date": date_key,
                    "file_name": file_name,
                    "processed_at": datetime.now().isoformat(),
                    "status": "ok",
                }
                count += 1
            else:
                # AI解析で品目が検出できなかった（食事以外の画像など）
                processed[file_id] = {
                    "date": date_key,
                    "file_name": file_name,
                    "processed_at": datetime.now().isoformat(),
                    "status": "no_items",
                }
                if manual:
                    st.warning(f"⚠️ {file_name}: 食事の品目を検出できませんでした")

        except Exception as e:
            if manual:
                st.warning(f"⚠️ {file_name} の処理に失敗: {e}")
            processed[file_id] = {
                "date": "",
                "file_name": file_name,
                "processed_at": datetime.now().isoformat(),
                "status": "error",
                "error": str(e),
            }

    # 保存
    if count > 0:
        save_weight_data(weight_data)
    save_food_processed(processed)

    return count


# ---------------------------------------------------------------------------
# 検索フィルタリング
# ---------------------------------------------------------------------------
def filter_images_by_keyword(
    images: list[dict], keyword: str, metadata: dict
) -> list[dict]:
    """キーワードでタイトル・要約・タグ・ファイル名を部分一致検索。"""
    if not keyword:
        return images
    keyword_lower = keyword.lower()
    filtered = []
    for img in images:
        file_id = img["id"]
        file_name = img["name"].lower()
        if file_id in metadata:
            meta = metadata[file_id]
            title = meta.get("title", "").lower()
            summary = meta.get("summary", "").lower()
            keywords = [kw.lower() for kw in meta.get("keywords", [])]
            if (
                keyword_lower in title
                or keyword_lower in summary
                or any(keyword_lower in kw for kw in keywords)
                or keyword_lower in file_name
            ):
                filtered.append(img)
        else:
            if keyword_lower in file_name:
                filtered.append(img)
    return filtered


# ---------------------------------------------------------------------------
# UI部品: 要約表示（箇条書き整形）
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
        f'font-size:0.9em; border:1px solid #2980b9;">{kw}</span>'
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
        st.error(f"⚠️ Google Sheets への同期に失敗しました。\n\nエラー: {err_detail}")

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
# チャット機能: コンテキスト生成
# ---------------------------------------------------------------------------
def build_knowledge_context(metadata: dict) -> str:
    """metadata.json の全データをテキスト化し、チャット用コンテキストを作成する。

    各エントリを「---」で区切り、ID・タイトル・要約・キーワードを明記する。
    """
    if not metadata:
        return "（保存された知識はまだありません）"

    entries = []
    for file_id, meta in metadata.items():
        title = meta.get("title", "不明")
        summary_label = get_summary_label(meta)
        summary = meta.get("summary", "") or "未入力"
        keywords = ", ".join(meta.get("keywords", []))
        s = get_status(meta)
        status = "確認済み" if s == STATUS_REVIEWED else "未確認"
        source_note = "（患者データ）" if is_patient_data(meta) else ""

        entry = (
            f"ID: {file_id}\n"
            f"タイトル: {title}{source_note}\n"
            f"{summary_label}: {summary}\n"
            f"キーワード: {keywords}\n"
            f"ステータス: {status}"
        )
        entries.append(entry)

    return "\n---\n".join(entries)


# ---------------------------------------------------------------------------
# チャット機能: 回答からIDを抽出
# ---------------------------------------------------------------------------
def extract_file_ids(text: str, metadata: dict) -> list[str]:
    """AI回答テキストから [ID: xxx] パターンでファイルIDを抽出する。

    metadata に存在するIDのみ返す。
    """
    # [ID: xxxxx] パターンをすべて抽出
    pattern = r"\[ID:\s*([^\]]+)\]"
    matches = re.findall(pattern, text)

    # メタデータに存在するIDだけをフィルタリング
    valid_ids = []
    for match in matches:
        match = match.strip()
        if match in metadata:
            valid_ids.append(match)

    # 重複を除去して順序を保持
    seen = set()
    unique_ids = []
    for fid in valid_ids:
        if fid not in seen:
            seen.add(fid)
            unique_ids.append(fid)

    return unique_ids


# ---------------------------------------------------------------------------
# チャット機能: Gemini で回答生成
# ---------------------------------------------------------------------------
def generate_chat_response(
    user_message: str, metadata: dict, api_key: str, chat_history: list[dict]
) -> str:
    """ユーザーの質問に対して、蓄積された知識をもとにGeminiで回答を生成する。"""
    try:
        # コンテキスト（知識）を生成
        knowledge_context = build_knowledge_context(metadata)
        system_prompt = CHAT_SYSTEM_PROMPT.format(
            knowledge_context=knowledge_context
        )

        # 会話履歴を構築（直近10往復まで）
        contents = [system_prompt]
        recent_history = chat_history[-20:]  # 直近20メッセージ（10往復）
        for msg in recent_history:
            role_label = "ユーザー" if msg["role"] == "user" else "アシスタント"
            contents.append(f"{role_label}: {msg['content']}")

        # 今回のユーザー質問
        contents.append(f"ユーザー: {user_message}")

        # Gemini に送信
        full_prompt = "\n\n".join(contents)
        return _gemini_generate(api_key, [{"text": full_prompt}]).strip()

    except Exception as e:
        return f"回答の生成中にエラーが発生しました: {e}"



# ---------------------------------------------------------------------------
# チャット機能: 参照画像の表示
# ---------------------------------------------------------------------------
def display_referenced_images(
    file_ids: list[str], metadata: dict, service
) -> None:
    """回答で参照されたIDの画像をコンパクトに表示する。

    サムネイル表示 + 「拡大表示」ボタンで全幅表示に切り替え可能。
    """
    if not file_ids:
        return

    st.markdown("**📎 参照元の画像:**")

    for fid in file_ids:
        meta = metadata.get(fid, {})
        title = meta.get("title", "不明")

        with st.expander(f"🖼️ {title}  (ID: {fid[:12]}...)", expanded=False):
            try:
                image_bytes = download_image(service, fid)
                st.image(image_bytes, width="stretch")

                if meta.get("summary"):
                    st.caption(meta["summary"])
            except Exception:
                st.warning(f"画像を読み込めませんでした (ID: {fid})")


def display_kb_response_with_images(
    text: str, metadata: dict, service, key_suffix: str = ""
) -> None:
    """参照画像をまとめて上部に表示し、本文中のIDはタイトル名に置換する。"""
    if not text:
        return

    pattern = r"\[ID:\s*([^\]]+)\]"

    # --- ID抽出（順序保持・重複除去） ---
    found_ids: list[str] = []
    seen: set[str] = set()
    for m in re.finditer(pattern, text):
        fid = m.group(1).strip()
        if fid not in seen and fid in metadata:
            seen.add(fid)
            found_ids.append(fid)

    # --- 上部: 参照画像をまとめてグリッド表示 ---
    if found_ids:
        cols = st.columns(min(len(found_ids), 3))
        for idx, fid in enumerate(found_ids):
            meta = metadata[fid]
            title = meta.get("title", "不明")
            with cols[idx % 3]:
                try:
                    img_bytes = download_image(service, fid)
                    st.image(img_bytes, caption=f"📷 {title}", width="stretch")
                except Exception:
                    st.caption(f"📷 {title}（読込失敗）")
                if st.button(
                    "📝 詳細を見る",
                    key=f"kb_detail_{fid}{key_suffix}",
                    use_container_width=True,
                ):
                    st.session_state["lib_selected_id"] = fid
                    st.session_state["lib_back_tab"] = st.session_state.get("active_tab")
                    st.session_state["active_tab"] = "📸 画像ライブラリ"
                    st.rerun()
        st.markdown("---")

    # --- 下部: 本文（IDをタイトル名に置換して表示） ---
    clean_text = text
    for fid in found_ids:
        title = metadata[fid].get("title", "不明")
        # [ID: xxx] → 「タイトル名」 に置換
        clean_text = re.sub(
            rf"\[ID:\s*{re.escape(fid)}\s*\]",
            f"**「{title}」**",
            clean_text,
        )
    # メタデータにないIDは単純に除去
    clean_text = re.sub(pattern, "", clean_text)
    # 空括弧を除去
    clean_text = re.sub(r"[\(（]\s*[\)）]", "", clean_text)
    clean_text = clean_text.strip()
    if clean_text:
        st.markdown(clean_text)


# ---------------------------------------------------------------------------
# チャット機能: セッション送信処理
# ---------------------------------------------------------------------------
def handle_chat_submit(
    user_input: str,
    sessions: dict,
    metadata: dict,
    api_key: str,
) -> None:
    """質問の送信を処理し、セッションを作成または更新する。"""
    active_id = st.session_state.get("active_session_id")

    # アクティブなセッションがなければ新規作成
    if active_id is None:
        active_id = str(uuid.uuid4())
        title = user_input[:30] + ("..." if len(user_input) > 30 else "")
        sessions[active_id] = {
            "id": active_id,
            "title": title,
            "created_at": datetime.now().isoformat(),
            "updated_at": datetime.now().isoformat(),
            "messages": [],
        }
        st.session_state["active_session_id"] = active_id

    # ユーザーメッセージを追加
    st.session_state["chat_messages"].append(
        {"role": "user", "content": user_input}
    )

    # AI回答を生成（知識ベースのみ）
    with st.spinner("知識ベースを検索中..."):
        history = st.session_state["chat_messages"][:-1]
        kb_response = generate_chat_response(
            user_input, metadata, api_key, history
        )
        ref_ids = extract_file_ids(kb_response, metadata)

    # アシスタントメッセージを追加
    st.session_state["chat_messages"].append(
        {
            "role": "assistant",
            "content": kb_response,
            "ref_ids": ref_ids,
        }
    )

    # ファイルに永続化
    sessions[active_id]["messages"] = st.session_state["chat_messages"].copy()
    sessions[active_id]["updated_at"] = datetime.now().isoformat()
    save_chat_sessions(sessions)

    st.rerun()


# ---------------------------------------------------------------------------
# チャット機能: ホーム画面
# ---------------------------------------------------------------------------
def render_home_screen(knowledge_count: int, metadata: dict, service) -> None:
    """アクティブな会話がないときにホーム画面を表示する。"""

    # 中央寄せの余白
    st.markdown("")
    st.markdown("")
    st.markdown("")

    # 名言をランダム選択
    quote_text, quote_author = random.choice(QUOTES)

    # 中央カラムでレイアウト
    col1, col2, col3 = st.columns([1, 3, 1])
    with col2:
        st.markdown(
            "<h1 style='text-align:center; font-size:56px; margin-bottom:8px;'>🧸</h1>",
            unsafe_allow_html=True,
        )
        st.markdown(
            f"<p style='text-align:center; color:#888; font-size:14px; "
            f"font-style:italic; line-height:1.6;'>"
            f"\"{quote_text}\"<br>"
            f"<span style='color:#666; font-size:13px;'>— {quote_author}</span></p>",
            unsafe_allow_html=True,
        )

    st.markdown("")

    # 新着画像カード（最大3枚）— クリックで詳細画面に遷移
    if metadata:
        # メタデータの末尾（最新登録順）から最大3件を取得
        all_ids = list(metadata.keys())
        recent_ids = list(reversed(all_ids))[:3]
        display_count = len(recent_ids)

        st.markdown(
            "<p style='text-align:center;color:#888;font-size:13px;"
            "margin-bottom:4px;'>🆕 新着画像</p>",
            unsafe_allow_html=True,
        )

        cols = st.columns(display_count)
        for col, fid in zip(cols, recent_ids):
            meta = metadata.get(fid, {})
            title = meta.get("title", "不明")
            keywords = meta.get("keywords", [])
            with col:
                try:
                    img_bytes = download_image(service, fid)
                    st.image(img_bytes, width="stretch")
                except Exception:
                    st.markdown(
                        "<div style='height:150px;background:#222;border-radius:8px;"
                        "display:flex;align-items:center;justify-content:center;"
                        "color:#666;'>🖼️ 読み込み失敗</div>",
                        unsafe_allow_html=True,
                    )
                st.markdown(
                    f"<p style='text-align:center;font-size:13px;font-weight:600;"
                    f"margin:4px 0 2px;'>{title}</p>",
                    unsafe_allow_html=True,
                )
                if keywords:
                    tags_html = " ".join(
                        f"<span style='background:#1a3a5c;color:#7eb8da;"
                        f"padding:2px 8px;border-radius:10px;font-size:11px;"
                        f"margin:2px;display:inline-block;'>{kw}</span>"
                        for kw in keywords[:3]
                    )
                    st.markdown(
                        f"<p style='text-align:center;'>{tags_html}</p>",
                        unsafe_allow_html=True,
                    )
                if st.button(
                    "🔍 詳細を見る",
                    key=f"home_img_{fid}",
                    width="stretch",
                ):
                    st.session_state["lib_selected_id"] = fid
                    st.session_state["lib_back_tab"] = st.session_state.get("active_tab")
                    st.session_state["active_tab"] = "📸 画像ライブラリ"
                    st.rerun()

    # 知識件数バッジ
    st.markdown("")
    st.markdown(
        f"<p style='text-align:center;'>"
        f"<span style='background:#1a3a5c; color:#7eb8da; padding:6px 18px;"
        f"border-radius:20px; font-size:14px;'>"
        f"📚 {knowledge_count}件 の知識を収録</span></p>",
        unsafe_allow_html=True,
    )


# ---------------------------------------------------------------------------
# チャット機能: サイドバー
# ---------------------------------------------------------------------------
def render_chat_sidebar(sessions: dict, metadata: dict) -> None:
    """チャットタブ用のサイドバー（セッション一覧 + 知識ベース情報）。"""
    # --- 新しい会話ボタン ---
    if st.sidebar.button(
        "➕ 新しい会話", type="primary", width="stretch"
    ):
        st.session_state["active_session_id"] = None
        st.session_state["chat_messages"] = []
        st.rerun()

    st.sidebar.markdown("---")

    # --- 知識ベース情報 ---
    st.sidebar.header("📚 知識ベース情報")
    knowledge_count = len(metadata)
    reviewed_count = sum(
        1 for m in metadata.values() if get_status(m) == STATUS_REVIEWED
    )
    st.sidebar.write(f"📚 全知識: **{knowledge_count}** 件")
    st.sidebar.write(f"✅ 確認済み: **{reviewed_count}** 件")

    # --- 過去の会話一覧 ---
    sorted_sessions = sorted(
        sessions.values(),
        key=lambda s: s.get("updated_at", ""),
        reverse=True,
    )

    if sorted_sessions:
        st.sidebar.markdown("---")
        st.sidebar.header("💬 過去の会話")

        active_id = st.session_state.get("active_session_id")

        for session in sorted_sessions:
            sid = session["id"]
            title = session["title"]
            is_active = active_id == sid
            relative = format_relative_time(session.get("updated_at", ""))

            # アクティブなセッションはハイライト
            if is_active:
                label = f"▶ {title}"
            else:
                label = f"　{title}"

            if st.sidebar.button(
                label,
                key=f"session_{sid}",
                width="stretch",
                type="primary" if is_active else "secondary",
            ):
                st.session_state["active_session_id"] = sid
                st.session_state["chat_messages"] = session["messages"].copy()
                st.rerun()

            if relative:
                st.sidebar.caption(f"　　{relative}")

    # --- アクティブなセッションの削除ボタン ---
    active_id = st.session_state.get("active_session_id")
    if active_id and active_id in sessions:
        st.sidebar.markdown("---")
        if st.sidebar.button("🗑️ この会話を削除", width="stretch"):
            del sessions[active_id]
            save_chat_sessions(sessions)
            st.session_state["active_session_id"] = None
            st.session_state["chat_messages"] = []
            st.rerun()


# ===========================================================================
# ページ: 画像管理
# ===========================================================================
def page_image_manager():
    """画像管理ページ（Phase 1-3 の機能）。"""
    service = get_drive_service()
    folder_id = get_folder_id()
    api_key = get_gemini_api_key()
    metadata = load_metadata()

    images = list_all_images(service, folder_id, metadata, get_patient_folder_id())
    if not images:
        st.info(
            "画像が見つかりませんでした。\n\n"
            "Google Driveに画像を追加するか、チャット画面から画像を貼り付けて取り込んでください。"
        )
        return

    # --- サイドバー ---
    st.sidebar.header("🔍 検索・フィルタ")
    search_keyword = st.sidebar.text_input(
        "キーワード検索",
        placeholder="タイトル、要約、タグで検索...",
    )
    filtered_images = filter_images_by_keyword(images, search_keyword, metadata)

    # フォルダフィルタ
    all_folders = get_all_folders_from_metadata(metadata)
    if len(all_folders) > 1:
        folder_filter = st.sidebar.selectbox(
            "📂 フォルダで絞り込み",
            ["すべて"] + all_folders,
            key="img_folder_filter",
        )
        if folder_filter != "すべて":
            filtered_images = [
                img for img in filtered_images
                if img["id"] in metadata and get_folder(metadata[img["id"]]) == folder_filter
            ]

    if st.sidebar.button("🔄 一覧を更新"):
        list_images.clear()
        list_patient_images.clear()
        download_image.clear()
        st.rerun()

    st.sidebar.markdown("---")
    if api_key:
        st.sidebar.success("🤖 Gemini API: 接続済み")
    else:
        st.sidebar.warning(
            "🤖 Gemini API: 未設定\n\n"
            "`GOOGLE_API_KEY` を secrets.toml に設定してください。"
        )

    st.sidebar.markdown("---")
    total = len(images)
    analyzed = sum(1 for img in images if img["id"] in metadata)
    reviewed_count = sum(
        1 for img in images
        if img["id"] in metadata
        and get_status(metadata[img["id"]]) == STATUS_REVIEWED
    )
    st.sidebar.caption(
        f"📊 全 {total} 件 | 解析済 {analyzed} 件 | ✅確認済み {reviewed_count} 件"
    )

    if not filtered_images:
        st.warning("検索条件に一致する画像がありません。")
        return

    # --- 選択中の画像ID ---
    if "selected_image_id" not in st.session_state:
        st.session_state["selected_image_id"] = None

    selected_fid = st.session_state["selected_image_id"]

    # =======================================================================
    # 詳細表示モード（画像が選択されている場合）
    # =======================================================================
    if selected_fid is not None:
        # 選択された画像を探す
        selected_file = None
        for img in filtered_images:
            if img["id"] == selected_fid:
                selected_file = img
                break

        if selected_file is None:
            st.session_state["selected_image_id"] = None
            st.rerun()
            return

        file_id = selected_file["id"]

        # 戻るボタン
        if st.button("⬅️ 一覧に戻る", key="back_to_grid"):
            st.session_state["selected_image_id"] = None
            st.session_state.pop("editing_file_id", None)
            st.rerun()

        # --- 画像読み込み ---
        image_bytes = None
        try:
            image_bytes = download_image(service, file_id)
        except HttpError as e:
            st.error(f"画像の読み込みに失敗しました: {e}")
            return
        except Exception as e:
            st.error(f"画像の表示中にエラーが発生しました: {e}")
            return

        meta = metadata.get(file_id, {})

        # --- 横並びレイアウト: 画像（左）+ 情報サマリー（右） ---
        col_img, col_info = st.columns([1, 1])
        with col_img:
            st.image(image_bytes, width="stretch")

        with col_info:
            # タイトル
            title = meta.get("title", selected_file["name"])
            st.subheader(title)
            # 患者データバッジ
            if is_patient_data(meta):
                st.markdown(
                    '<span style="background-color:#2e7d32; color:#c8e6c9; padding:3px 10px; '
                    'border-radius:12px; font-size:0.85em;">🏥 患者データ</span>',
                    unsafe_allow_html=True,
                )
            # ステータス
            if file_id in metadata and not is_patient_data(meta):
                s = get_status(meta)
                if s == STATUS_REVIEWED:
                    st.success("✅ 確認済み")
                else:
                    st.warning("📝 未確認")
            # 要約/検査所見
            _sl = get_summary_label(meta)
            summary_text = meta.get("summary", "")
            if summary_text:
                st.markdown(f"**{_sl}:**")
                render_summary(summary_text)
            elif is_patient_data(meta):
                st.info("検査所見が未入力です。編集から入力してください。")
            # キーワード
            keywords = meta.get("keywords", [])
            if keywords:
                render_keyword_tags(keywords)

        # --- 編集フォーム（折りたたみ） ---
        if file_id in metadata:
            _is_pd = is_patient_data(metadata[file_id])
            edit_label = "📝 検査所見を編集" if _is_pd else "📝 編集"
            with st.expander(edit_label, expanded=_is_pd):
                display_edit_form(file_id, metadata[file_id], metadata)
            if _is_pd:
                st.info("🏥 患者データ: AI解析は行いません。手動で検査所見を入力してください。")
            elif api_key:
                if st.button("🤖 AIで再解析する", key=f"reanalyze_{file_id}"):
                    with st.spinner("Gemini で再解析中..."):
                        result = analyze_image_with_gemini(image_bytes, api_key)
                        if result:
                            old = metadata.get(file_id, {})
                            for keep_key in ("folder", "source"):
                                if keep_key in old:
                                    result[keep_key] = old[keep_key]
                            metadata[file_id] = result
                            save_metadata(metadata)
                            st.session_state.pop("editing_file_id", None)
                            st.success("再解析が完了しました！")
                            st.rerun()
        else:
            st.markdown("---")
            if api_key:
                st.info("この画像はまだAI解析されていません。")
                if st.button(
                    "🤖 AI解析を実行",
                    key=f"analyze_{file_id}",
                    type="primary",
                ):
                    with st.spinner("Gemini 2.0 Flash で解析中..."):
                        result = analyze_image_with_gemini(image_bytes, api_key)
                        if result:
                            old = metadata.get(file_id, {})
                            for keep_key in ("folder", "source"):
                                if keep_key in old:
                                    result[keep_key] = old[keep_key]
                            metadata[file_id] = result
                            save_metadata(metadata)
                            st.success("解析が完了しました！")
                            st.rerun()
            else:
                st.warning(
                    "AI解析を使用するには `GOOGLE_API_KEY` を "
                    "`.streamlit/secrets.toml` に設定してください。"
                )
        return

    # =======================================================================
    # グリッド一覧表示モード（デフォルト）— サムネイルで高速表示
    # =======================================================================

    # 削除モード切り替え
    if "img_delete_mode" not in st.session_state:
        st.session_state["img_delete_mode"] = False

    # ページネーション
    page_items, cur_page, total_pages = _paginate(filtered_images, "img_grid_page")
    _render_pagination_controls("img_grid_page", cur_page, total_pages, len(filtered_images))

    header_col1, header_col2 = st.columns([3, 1])
    with header_col1:
        st.caption(f"**{len(filtered_images)}** / {len(images)} 件中を表示")
    with header_col2:
        if st.session_state["img_delete_mode"]:
            if st.button("✖ 削除モード終了", key="exit_delete_mode", width="stretch"):
                st.session_state["img_delete_mode"] = False
                # チェック状態クリア
                for img in filtered_images:
                    st.session_state.pop(f"img_del_{img['id']}", None)
                st.rerun()
        else:
            if st.button("🗑️ 削除モード", key="enter_delete_mode", width="stretch"):
                st.session_state["img_delete_mode"] = True
                st.rerun()

    # 削除モード時: 全選択/全解除
    delete_ids = []
    if st.session_state["img_delete_mode"]:
        del_c1, del_c2, del_c3 = st.columns([1, 1, 4])
        with del_c1:
            if st.button("☑️ 全選択", key="img_del_all"):
                for img in filtered_images:
                    if img["id"] in metadata:
                        st.session_state[f"img_del_{img['id']}"] = True
                st.rerun()
        with del_c2:
            if st.button("☐ 全解除", key="img_del_none"):
                for img in filtered_images:
                    st.session_state.pop(f"img_del_{img['id']}", None)
                st.rerun()

    cols_per_row = 4
    for row_start in range(0, len(page_items), cols_per_row):
        cols = st.columns(cols_per_row)
        for col_idx in range(cols_per_row):
            img_idx = row_start + col_idx
            if img_idx >= len(page_items):
                break
            img = page_items[img_idx]
            fid = img["id"]

            with cols[col_idx]:
                # 削除モード以外: 画像+タイトルをまとめてボタン化
                if not st.session_state["img_delete_mode"]:
                    # サムネイル表示
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        st.markdown(
                            '<div style="background:#333;border-radius:8px;'
                            'height:80px;display:flex;align-items:center;'
                            'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                            unsafe_allow_html=True,
                        )
                    # タイトル
                    if fid in metadata:
                        meta = metadata[fid]
                        title = meta.get("title", img["name"])
                        status = get_status(meta)
                        icon = get_status_icon(meta)
                        pd_badge = " 🏥" if is_patient_data(meta) else ""
                        st.caption(f"{icon}{pd_badge} {title}")
                    else:
                        st.caption(f"📄 {img['name']}")
                    # クリックで詳細
                    if st.button("🔍 詳細を見る", key=f"grid_open_{fid}", width="stretch"):
                        st.session_state["selected_image_id"] = fid
                        st.rerun()
                else:
                    # 削除モード
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        st.markdown(
                            '<div style="background:#333;border-radius:8px;'
                            'height:80px;display:flex;align-items:center;'
                            'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                            unsafe_allow_html=True,
                        )
                    if fid in metadata:
                        meta = metadata[fid]
                        title = meta.get("title", img["name"])
                        st.caption(title)
                        checked = st.checkbox(
                            "削除",
                            value=st.session_state.get(f"img_del_{fid}", False),
                            key=f"img_del_{fid}",
                        )
                        if checked:
                            delete_ids.append(fid)
                    else:
                        st.caption(f"📄 {img['name']}（未解析）")

    # 削除モード時: ゴミ箱移動エリア
    if st.session_state["img_delete_mode"]:
        st.markdown("---")
        del_count = len(delete_ids)
        if del_count > 0:
            st.warning(f"🗑️ **{del_count} 件**の解析データをゴミ箱に移動します（{TRASH_RETENTION_DAYS}日後に完全削除）。")
            st.caption("💡 削除した画像は再スキャンしても再取り込みされません。ゴミ箱から復元すると再取り込み対象に戻ります。")
        if st.button(
            f"🗑️ 選択した {del_count} 件をゴミ箱へ",
            type="primary",
            key="img_grid_delete_run",
            disabled=(del_count == 0),
        ):
            moved = move_to_trash(delete_ids, metadata)
            for fid in delete_ids:
                st.session_state.pop(f"img_del_{fid}", None)
            st.session_state["img_delete_mode"] = False
            st.success(f"✅ {moved} 件をゴミ箱に移動しました。「🗑️ ゴミ箱」ページから復元できます。")
            st.rerun()


# ===========================================================================
# ページ: 一括解析
# ===========================================================================
def _ensure_patient_data_folder(metadata: dict) -> bool:
    """患者データのfolder値が正しいか確認し、修正があればTrueを返す。"""
    fixed = False
    for fid, meta in metadata.items():
        if is_patient_data(meta) and get_folder(meta) != PATIENT_DATA_FOLDER:
            meta["folder"] = PATIENT_DATA_FOLDER
            fixed = True
    if fixed:
        save_metadata(metadata)
        _invalidate_all_caches()
        # フォルダリストにも追加
        folders = load_folders()
        if PATIENT_DATA_FOLDER not in folders:
            folders.append(PATIENT_DATA_FOLDER)
            save_folders(folders)
    return fixed


def page_batch_analyze():
    """一括解析ページ — AI解析・再解析・レビュー・削除をまとめて行う。"""
    service = get_drive_service()
    folder_id = get_folder_id()
    api_key = get_gemini_api_key()
    metadata = load_metadata()

    # 患者データのfolder値を自動修正（「未分類」→「患者データ」）
    _ensure_patient_data_folder(metadata)

    images = list_all_images(service, folder_id, metadata, get_patient_folder_id())
    if not images:
        st.info("フォルダ内に画像が見つかりませんでした。")
        return

    if not api_key:
        st.warning(
            "一括解析を使用するには `GOOGLE_API_KEY` を "
            "`.streamlit/secrets.toml` に設定してください。"
        )
        return

    # --- 画像の分類（患者データはAI解析対象外） ---
    unanalyzed = [
        img for img in images
        if img["id"] not in metadata
        and not is_patient_data(metadata.get(img["id"], {}))
    ]
    unreviewed = [
        img for img in images
        if img["id"] in metadata
        and not is_patient_data(metadata[img["id"]])
        and get_status(metadata[img["id"]]) == STATUS_AUTO
    ]
    reviewed = [
        img for img in images
        if img["id"] in metadata
        and not is_patient_data(metadata[img["id"]])
        and get_status(metadata[img["id"]]) == STATUS_REVIEWED
    ]
    analyzed_all = [
        img for img in images
        if img["id"] in metadata
        and not is_patient_data(metadata[img["id"]])
    ]
    # 患者データ一覧
    patient_data_images = [
        img for img in images
        if img["id"] in metadata
        and is_patient_data(metadata[img["id"]])
    ]

    # --- サイドバー: 統計 ---
    st.sidebar.header("📊 処理状況")
    st.sidebar.write(f"📄 未解析: **{len(unanalyzed)}** 件")
    st.sidebar.write(f"📝 未確認: **{len(unreviewed)}** 件")
    st.sidebar.write(f"✅ 確認済み: **{len(reviewed)}** 件")
    if patient_data_images:
        st.sidebar.write(f"🏥 患者データ: **{len(patient_data_images)}** 件")
    st.sidebar.write(f"合計: **{len(images)}** 件")

    # プログレスバー
    if images:
        done_count = len(reviewed)
        progress = done_count / len(images)
        st.sidebar.progress(progress, text=f"確認済み: {done_count}/{len(images)}")

    # --- モード切り替え ---
    if "batch_mode" not in st.session_state:
        st.session_state["batch_mode"] = "新規解析"

    mode = st.radio(
        "操作を選択",
        ["新規解析", "一括再解析", "指示付き再解析", "患者データ編集",
         "レビュー", "一括レビュー済みに変更", "解析データの削除"],
        horizontal=True,
        key="batch_mode",
    )

    st.markdown("---")

    # =======================================================================
    # モード: 新規解析
    # =======================================================================
    if mode == "新規解析":
        st.subheader("🔬 未解析画像の一括AI解析")

        if not unanalyzed:
            st.success("すべての画像が解析済みです ✅")
            return

        st.info(f"**{len(unanalyzed)} 件**の未解析画像があります。解析する画像を選択してください。")

        sel_col1, sel_col2, sel_col3 = st.columns([1, 1, 3])
        _apply_batch_checkbox("_batch_sel_flag", [f"batch_sel_{img['id']}" for img in unanalyzed])
        with sel_col1:
            if st.button("☑️ 全選択", key="batch_select_all"):
                _set_batch_checkbox("_batch_sel_flag", True)
        with sel_col2:
            if st.button("☐ 全解除", key="batch_deselect_all"):
                _set_batch_checkbox("_batch_sel_flag", False)

        # ページネーション
        batch_page_items, batch_cur, batch_total_pages = _paginate(unanalyzed, "batch_new_page")
        _render_pagination_controls("batch_new_page", batch_cur, batch_total_pages, len(unanalyzed))

        selected_ids = []
        cols_per_row = 4
        for row_start in range(0, len(batch_page_items), cols_per_row):
            cols = st.columns(cols_per_row)
            for col_idx in range(cols_per_row):
                img_idx = row_start + col_idx
                if img_idx >= len(batch_page_items):
                    break
                img = batch_page_items[img_idx]
                fid = img["id"]
                with cols[col_idx]:
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        st.markdown(
                            '<div style="background:#333;border-radius:8px;'
                            'height:80px;display:flex;align-items:center;'
                            'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                            unsafe_allow_html=True,
                        )
                    st.caption(f"📄 {img['name']}")
                    if st.checkbox("解析する", value=st.session_state.get(f"batch_sel_{fid}", False), key=f"batch_sel_{fid}"):
                        selected_ids.append(fid)

        st.markdown("---")
        selected_count = len(selected_ids)
        if st.button(
            f"🤖 選択した {selected_count} 件を解析",
            type="primary",
            key="batch_run_selected",
            disabled=(selected_count == 0),
        ):
            target = [img for img in unanalyzed if img["id"] in selected_ids]
            _run_batch_analyze(service, target, metadata, api_key)

    # =======================================================================
    # モード: 一括再解析
    # =======================================================================
    elif mode == "一括再解析":
        st.subheader("🔄 解析済み画像の一括再解析")
        st.caption("プロンプト改善後などに、解析済みの画像をまとめて再解析できます。")

        if not analyzed_all:
            st.info("解析済みの画像がありません。")
            return

        # フィルタ
        filter_choice = st.radio(
            "対象を絞る",
            ["すべて", "未確認のみ（📝）", "確認済みのみ（✅）"],
            horizontal=True,
            key="reanalyze_filter",
        )
        if filter_choice == "未確認のみ（📝）":
            target_list = unreviewed
        elif filter_choice == "確認済みのみ（✅）":
            target_list = reviewed
        else:
            target_list = analyzed_all

        if not target_list:
            st.info("該当する画像がありません。")
            return

        st.info(f"**{len(target_list)} 件**の画像が対象です。除外したい画像のチェックを外してください。")

        rc1, rc2, rc3 = st.columns([1, 1, 3])
        _apply_batch_checkbox("_reanalyze_sel_flag", [f"reanalyze_sel_{img['id']}" for img in target_list])
        with rc1:
            if st.button("☑️ 全選択", key="reanalyze_sel_all"):
                _set_batch_checkbox("_reanalyze_sel_flag", True)
        with rc2:
            if st.button("☐ 全解除", key="reanalyze_sel_none"):
                _set_batch_checkbox("_reanalyze_sel_flag", False)

        # ページネーション
        ra_page_items, ra_cur, ra_total_pages = _paginate(target_list, "batch_reanalyze_page")
        _render_pagination_controls("batch_reanalyze_page", ra_cur, ra_total_pages, len(target_list))

        reanalyze_ids = []
        cols_per_row = 4
        for row_start in range(0, len(ra_page_items), cols_per_row):
            cols = st.columns(cols_per_row)
            for col_idx in range(cols_per_row):
                img_idx = row_start + col_idx
                if img_idx >= len(ra_page_items):
                    break
                img = ra_page_items[img_idx]
                fid = img["id"]
                meta = metadata[fid]
                title = meta.get("title", img["name"])
                status = get_status(meta)
                status_icon = get_status_icon(meta)
                with cols[col_idx]:
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        st.markdown(
                            '<div style="background:#333;border-radius:8px;'
                            'height:80px;display:flex;align-items:center;'
                            'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                            unsafe_allow_html=True,
                        )
                    st.caption(f"{status_icon} {title}")
                    if st.checkbox("再解析", value=st.session_state.get(f"reanalyze_sel_{fid}", True), key=f"reanalyze_sel_{fid}"):
                        reanalyze_ids.append(fid)

        st.markdown("---")
        reanalyze_count = len(reanalyze_ids)
        if reanalyze_count > 0:
            st.warning("⚠️ 再解析すると現在の解析データ（タイトル・要約・キーワード）が上書きされます。ステータスも未確認に戻ります。")
        if st.button(
            f"🔄 選択した {reanalyze_count} 件を再解析",
            type="primary",
            key="reanalyze_run",
            disabled=(reanalyze_count == 0),
        ):
            target = [img for img in target_list if img["id"] in reanalyze_ids]
            _run_batch_analyze(service, target, metadata, api_key, is_reanalyze=True)

    # =======================================================================
    # モード: 指示付き再解析
    # =======================================================================
    elif mode == "指示付き再解析":
        st.subheader("📝 指示付き再解析")
        st.caption(
            "AIの解析結果が間違っている画像を選択し、修正指示を入力してまとめて再解析できます。"
        )

        if not analyzed_all:
            st.info("解析済みの画像がありません。まず「新規解析」を実行してください。")
            return

        # フィルタ
        hint_filter = st.radio(
            "対象を絞る",
            ["すべて", "未確認のみ（📝）", "確認済みのみ（✅）"],
            horizontal=True,
            key="hint_reanalyze_filter",
        )
        if hint_filter == "未確認のみ（📝）":
            hint_target_list = unreviewed
        elif hint_filter == "確認済みのみ（✅）":
            hint_target_list = reviewed
        else:
            hint_target_list = analyzed_all

        if not hint_target_list:
            st.info("該当する画像がありません。")
            return

        st.info(f"**{len(hint_target_list)} 件**の画像が対象です。修正したい画像を選択してください。")

        hc1, hc2, hc3 = st.columns([1, 1, 3])
        _apply_batch_checkbox("_hint_sel_flag", [f"hint_sel_{img['id']}" for img in hint_target_list])
        with hc1:
            if st.button("☑️ 全選択", key="hint_sel_all"):
                _set_batch_checkbox("_hint_sel_flag", True)
        with hc2:
            if st.button("☐ 全解除", key="hint_sel_none"):
                _set_batch_checkbox("_hint_sel_flag", False)

        # ページネーション
        hint_page_items, hint_cur, hint_total_pages = _paginate(hint_target_list, "batch_hint_page")
        _render_pagination_controls("batch_hint_page", hint_cur, hint_total_pages, len(hint_target_list))

        hint_ids = []
        cols_per_row = 4
        for row_start in range(0, len(hint_page_items), cols_per_row):
            cols = st.columns(cols_per_row)
            for col_idx in range(cols_per_row):
                img_idx = row_start + col_idx
                if img_idx >= len(hint_page_items):
                    break
                img = hint_page_items[img_idx]
                fid = img["id"]
                meta = metadata[fid]
                title = meta.get("title", img["name"])
                status_icon = get_status_icon(meta)
                kw = meta.get("keywords", [])
                with cols[col_idx]:
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        st.markdown(
                            '<div style="background:#333;border-radius:8px;'
                            'height:80px;display:flex;align-items:center;'
                            'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                            unsafe_allow_html=True,
                        )
                    st.caption(f"{status_icon} {title}")
                    if kw:
                        st.caption(" ".join(f"`{k}`" for k in kw[:5]))
                    if st.checkbox(
                        "修正する",
                        value=st.session_state.get(f"hint_sel_{fid}", False),
                        key=f"hint_sel_{fid}",
                    ):
                        hint_ids.append(fid)

        st.markdown("---")

        # 修正指示の入力
        correction_hint = st.text_area(
            "🔧 修正指示（選択した全画像に共通で適用されます）",
            placeholder=(
                "例:\n"
                "・「骨折」ではなく「ストレス骨折」が正しいです\n"
                "・キーワードに「シンスプリント」を追加してください\n"
                "・この画像はMRIではなくCTです"
            ),
            height=120,
            key="correction_hint_text",
        )

        hint_count = len(hint_ids)
        if hint_count > 0 and not correction_hint.strip():
            st.warning("⚠️ 修正指示を入力してください。指示なしの再解析は「一括再解析」モードをお使いください。")

        can_run = hint_count > 0 and bool(correction_hint.strip())
        if st.button(
            f"🤖 選択した {hint_count} 件を指示付きで再解析",
            type="primary",
            key="hint_reanalyze_run",
            disabled=(not can_run),
        ):
            target = [img for img in hint_target_list if img["id"] in hint_ids]
            _run_batch_analyze(
                service, target, metadata, api_key,
                is_reanalyze=True, correction_hint=correction_hint,
            )

    # =======================================================================
    # モード: 患者データ編集
    # =======================================================================
    elif mode == "患者データ編集":
        st.subheader("🏥 患者データの一括編集")

        # 保存成功メッセージの表示（rerun後にも表示されるように session_state を使用）
        if st.session_state.get("_pd_save_success"):
            st.success(st.session_state["_pd_save_success"])
            del st.session_state["_pd_save_success"]

        if not patient_data_images:
            st.info("🏥 患者データはまだ取り込まれていません。")
        else:
            st.info(
                f"🏥 **{len(patient_data_images)} 件**の患者データがあります。"
            )

            # ===============================================================
            # 一括操作パネル
            # ===============================================================
            with st.expander("⚡ 一括操作", expanded=True):
                bulk_tab1, bulk_tab2 = st.tabs(["📌 一括タイトル入力", "🤖 一括AIキーワード生成"])

                # --- 一括タイトル入力 ---
                with bulk_tab1:
                    st.caption(
                        "各行に「画像番号（1始まり）: タイトル」を入力してください。\n"
                        "例:\n```\n1: 右膝関節MRI\n2: 腰椎X線\n3: 頸椎CT\n```"
                    )
                    # デフォルトテキストを生成（現在の画像リスト）
                    default_lines = []
                    for i, img in enumerate(patient_data_images):
                        m = metadata.get(img["id"], {})
                        current_title = m.get("title", img.get("name", ""))
                        default_lines.append(f"{i + 1}: {current_title}")
                    bulk_titles_text = st.text_area(
                        "タイトル一覧",
                        value="\n".join(default_lines),
                        height=min(300, 30 + 25 * len(patient_data_images)),
                        key="pd_bulk_titles",
                    )
                    if st.button("💾 タイトルを一括保存", key="pd_bulk_title_save",
                                 type="primary", use_container_width=True):
                        saved_count = 0
                        for line in bulk_titles_text.strip().split("\n"):
                            line = line.strip()
                            if not line or ":" not in line and "：" not in line:
                                continue
                            # 「番号: タイトル」or「番号：タイトル」
                            sep = "：" if "：" in line else ":"
                            parts = line.split(sep, 1)
                            try:
                                idx_str = parts[0].strip()
                                # 数字以外の文字を除去
                                idx_num = int("".join(c for c in idx_str if c.isdigit()))
                                title_val = parts[1].strip()
                            except (ValueError, IndexError):
                                continue
                            if 1 <= idx_num <= len(patient_data_images):
                                target_fid = patient_data_images[idx_num - 1]["id"]
                                if target_fid in metadata:
                                    metadata[target_fid]["title"] = title_val
                                    saved_count += 1
                        if saved_count > 0:
                            save_metadata(metadata)
                            _invalidate_all_caches()
                            st.session_state["_pd_save_success"] = (
                                f"✅ {saved_count} 件のタイトルを一括保存しました"
                            )
                            st.rerun()
                        else:
                            st.warning("保存するタイトルがありませんでした。")

                # --- 一括AIキーワード生成 ---
                with bulk_tab2:
                    # キーワード未設定の件数
                    no_kw_count = sum(
                        1 for img in patient_data_images
                        if not metadata.get(img["id"], {}).get("keywords")
                    )
                    all_count = len(patient_data_images)
                    st.caption(
                        f"全 {all_count} 件中、キーワード未設定: **{no_kw_count} 件**"
                    )
                    ai_target = st.radio(
                        "対象",
                        ["キーワード未設定のみ", "すべて（上書き）"],
                        horizontal=True,
                        key="pd_ai_target",
                    )
                    if st.button(
                        f"🤖 一括AIキーワード生成（{no_kw_count if ai_target == 'キーワード未設定のみ' else all_count} 件）",
                        key="pd_bulk_ai_kw",
                        type="primary",
                        use_container_width=True,
                    ):
                        if not api_key:
                            st.warning("Gemini API キーが必要です。")
                        else:
                            target_imgs = []
                            for img in patient_data_images:
                                m = metadata.get(img["id"], {})
                                if ai_target == "キーワード未設定のみ" and m.get("keywords"):
                                    continue
                                target_imgs.append(img)
                            if not target_imgs:
                                st.info("対象の画像がありません。")
                            else:
                                progress_bar = st.progress(0, text="AIキーワード生成中...")
                                generated = 0
                                for i, img in enumerate(target_imgs):
                                    fid = img["id"]
                                    m = metadata.get(fid, {})
                                    progress_bar.progress(
                                        (i + 1) / len(target_imgs),
                                        text=f"🤖 {i + 1}/{len(target_imgs)}: {m.get('title', img.get('name', '')[:20])}...",
                                    )
                                    try:
                                        ib = download_image(service, fid)
                                        kws = generate_keywords_with_gemini(
                                            ib, api_key, title=m.get("title", ""),
                                        )
                                        if kws:
                                            metadata[fid]["keywords"] = kws
                                            generated += 1
                                    except Exception:
                                        pass
                                progress_bar.empty()
                                if generated > 0:
                                    save_metadata(metadata)
                                    _invalidate_all_caches()
                                    st.session_state["_pd_save_success"] = (
                                        f"🤖 {generated} 件のAIキーワードを生成しました"
                                    )
                                    st.rerun()
                                else:
                                    st.warning("キーワードを生成できませんでした。")

            st.markdown("---")

            # ===============================================================
            # 個別編集（ページネーション）
            # ===============================================================
            st.subheader("📝 個別編集")

            # ページネーション
            page_items, current_page, total_pages = _paginate(
                patient_data_images, "batch_patient_page"
            )
            _render_pagination_controls(
                "batch_patient_page", current_page, total_pages, len(patient_data_images)
            )

            # 各画像を編集フォーム付きで表示
            for idx, img in enumerate(page_items):
                fid = img["id"]
                meta = metadata.get(fid, {})
                fname = img.get("name", fid)
                # ページ内の通し番号（全体の番号）
                global_idx = (current_page - 1) * IMAGES_PER_PAGE + idx + 1
                status_icon = "✅" if meta.get("status") == STATUS_REVIEWED else "✏️"
                kw_preview = ", ".join(meta.get("keywords", [])[:3])
                if kw_preview:
                    kw_preview = f" 🏷️{kw_preview}"

                with st.expander(
                    f"{global_idx}. {meta.get('title', fname)} {status_icon}{kw_preview}",
                    expanded=False,
                ):
                    col_img, col_form = st.columns([1, 2])
                    with col_img:
                        try:
                            img_bytes = download_image(service, fid)
                            st.image(img_bytes, use_container_width=True)
                        except Exception:
                            st.caption("（画像を読み込めません）")
                            img_bytes = None

                    with col_form:
                        # --- 編集フォーム ---
                        with st.form(key=f"pd_edit_{fid}_{current_page}"):
                            new_title = st.text_input(
                                "📌 タイトル",
                                value=meta.get("title", fname),
                                key=f"pd_title_{fid}_{current_page}",
                            )
                            new_summary = st.text_area(
                                "📝 検査所見（任意）",
                                value=meta.get("summary", ""),
                                height=80,
                                placeholder="所見があれば入力（空欄でもOK）",
                                key=f"pd_summary_{fid}_{current_page}",
                            )
                            new_keywords = st.text_input(
                                "🏷️ キーワード（カンマ区切り）",
                                value=", ".join(meta.get("keywords", [])),
                                key=f"pd_kw_{fid}_{current_page}",
                            )
                            submitted = st.form_submit_button(
                                "💾 保存", type="primary", use_container_width=True,
                            )
                            if submitted:
                                kw_list = [
                                    k.strip()
                                    for k in new_keywords.replace("、", ",").split(",")
                                    if k.strip()
                                ]
                                metadata[fid]["title"] = new_title
                                metadata[fid]["summary"] = new_summary
                                metadata[fid]["keywords"] = kw_list
                                metadata[fid]["status"] = STATUS_REVIEWED
                                save_metadata(metadata)
                                _invalidate_all_caches()
                                st.session_state["_pd_save_success"] = (
                                    f"✅ 「{new_title}」を保存しました"
                                )
                                st.rerun()

    # =======================================================================
    # モード: レビュー（1枚ずつ）
    # =======================================================================
    elif mode == "レビュー":
        st.subheader("📝 レビュー（確認・編集）")

        metadata = load_metadata()
        unreviewed_now = [
            img for img in images
            if img["id"] in metadata
            and get_status(metadata[img["id"]]) == STATUS_AUTO
        ]

        if not unreviewed_now:
            if reviewed:
                st.success("すべての画像がレビュー済みです 🎉")
            else:
                st.info("まず「新規解析」で一括AI解析を実行してください。")
            return

        st.info(f"**{len(unreviewed_now)} 件**の未確認画像があります。順番に確認してください。")

        if "review_index" not in st.session_state:
            st.session_state["review_index"] = 0
        if st.session_state["review_index"] >= len(unreviewed_now):
            st.session_state["review_index"] = 0

        current_idx = st.session_state["review_index"]
        current_img = unreviewed_now[current_idx]
        current_fid = current_img["id"]
        current_meta = metadata[current_fid]

        nav_col1, nav_col2, nav_col3 = st.columns([1, 2, 1])
        with nav_col1:
            if st.button("⬅️ 前へ", disabled=(current_idx == 0), key="rev_prev"):
                st.session_state["review_index"] = current_idx - 1
                st.session_state.pop("editing_file_id", None)
                st.rerun()
        with nav_col2:
            st.write(f"**{current_idx + 1} / {len(unreviewed_now)}** 件目")
        with nav_col3:
            if st.button("次へ ➡️", disabled=(current_idx >= len(unreviewed_now) - 1), key="rev_next"):
                st.session_state["review_index"] = current_idx + 1
                st.session_state.pop("editing_file_id", None)
                st.rerun()

        st.markdown("---")
        try:
            image_bytes = download_image(service, current_fid)
        except Exception as e:
            st.error(f"画像の読み込みに失敗しました: {e}")
            return

        # --- 横並びレイアウト: 画像（左）+ 要約（右） ---
        rev_col_img, rev_col_info = st.columns([1, 1])
        with rev_col_img:
            st.image(image_bytes, width="stretch")
        with rev_col_info:
            title = current_meta.get("title", current_img.get("name", "不明"))
            st.subheader(title)
            render_summary(current_meta.get("summary", ""))
            keywords = current_meta.get("keywords", [])
            if keywords:
                render_keyword_tags(keywords)

        display_edit_form(current_fid, current_meta, metadata)

        st.markdown("---")
        if st.button("⏭️ この画像をスキップして次へ", key="rev_skip"):
            if current_idx < len(unreviewed_now) - 1:
                st.session_state["review_index"] = current_idx + 1
            else:
                st.session_state["review_index"] = 0
            st.session_state.pop("editing_file_id", None)
            st.rerun()

    # =======================================================================
    # モード: 一括レビュー済みに変更
    # =======================================================================
    elif mode == "一括レビュー済みに変更":
        st.subheader("✅ 一括ステータス変更")
        st.caption("未確認の画像をまとめて確認済みに変更、または確認済みを未確認に戻せます。")

        metadata = load_metadata()

        # 対象選択
        review_filter = st.radio(
            "対象",
            ["未確認→確認済み（📝→✅）", "確認済み→未確認に戻す（✅→📝）"],
            horizontal=True,
            key="bulk_review_filter",
        )

        if review_filter == "未確認→確認済み（📝→✅）":
            target_list = [
                img for img in images
                if img["id"] in metadata
                and get_status(metadata[img["id"]]) == STATUS_AUTO
            ]
            action_label = "確認済みにする"
            action_key_prefix = "bulkrev"
        else:
            target_list = [
                img for img in images
                if img["id"] in metadata
                and get_status(metadata[img["id"]]) == STATUS_REVIEWED
            ]
            action_label = "未確認に戻す"
            action_key_prefix = "bulkunrev"

        if not target_list:
            st.success("該当する画像がありません。")
            return

        st.info(f"**{len(target_list)} 件**が対象です。")

        bc1, bc2, bc3 = st.columns([1, 1, 3])
        with bc1:
            if st.button("☑️ 全選択", key=f"{action_key_prefix}_sel_all"):
                for img in target_list:
                    st.session_state[f"{action_key_prefix}_{img['id']}"] = True
                st.rerun()
        with bc2:
            if st.button("☐ 全解除", key=f"{action_key_prefix}_sel_none"):
                for img in target_list:
                    st.session_state[f"{action_key_prefix}_{img['id']}"] = False
                st.rerun()

        # ページネーション
        br_page_items, br_cur, br_total_pages = _paginate(target_list, "batch_bulkreview_page")
        _render_pagination_controls("batch_bulkreview_page", br_cur, br_total_pages, len(target_list))

        action_ids = []
        cols_per_row = 4
        for row_start in range(0, len(br_page_items), cols_per_row):
            cols = st.columns(cols_per_row)
            for col_idx in range(cols_per_row):
                img_idx = row_start + col_idx
                if img_idx >= len(br_page_items):
                    break
                img = br_page_items[img_idx]
                fid = img["id"]
                meta = metadata[fid]
                title = meta.get("title", img["name"])
                status = get_status(meta)
                status_icon = get_status_icon(meta)
                with cols[col_idx]:
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        st.markdown(
                            '<div style="background:#333;border-radius:8px;'
                            'height:80px;display:flex;align-items:center;'
                            'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                            unsafe_allow_html=True,
                        )
                    st.caption(f"{status_icon} {title}")
                    kw = meta.get("keywords", [])
                    if kw:
                        st.caption(" ".join(f"`{k}`" for k in kw[:3]))
                    if st.checkbox(action_label, value=st.session_state.get(f"{action_key_prefix}_{fid}", False), key=f"{action_key_prefix}_{fid}"):
                        action_ids.append(fid)

        st.markdown("---")
        action_count = len(action_ids)

        if review_filter == "未確認→確認済み（📝→✅）":
            if st.button(
                f"✅ 選択した {action_count} 件を確認済みにする",
                type="primary",
                key="bulk_review_run",
                disabled=(action_count == 0),
            ):
                for fid in action_ids:
                    if fid in metadata:
                        metadata[fid]["status"] = STATUS_REVIEWED
                save_metadata(metadata)
                for fid in action_ids:
                    st.session_state.pop(f"{action_key_prefix}_{fid}", None)
                st.success(f"✅ {action_count} 件を確認済みにしました。")
                st.rerun()
        else:
            if st.button(
                f"🆕 選択した {action_count} 件を未確認に戻す",
                type="primary",
                key="bulk_unreview_run",
                disabled=(action_count == 0),
            ):
                for fid in action_ids:
                    if fid in metadata:
                        metadata[fid]["status"] = STATUS_AUTO
                save_metadata(metadata)
                for fid in action_ids:
                    st.session_state.pop(f"{action_key_prefix}_{fid}", None)
                st.success(f"🆕 {action_count} 件を未確認に戻しました。")
                st.rerun()

    # =======================================================================
    # モード: 解析データの削除
    # =======================================================================
    elif mode == "解析データの削除":
        st.subheader("🗑️ 解析データの削除")

        metadata = load_metadata()
        analyzed_images = [img for img in images if img["id"] in metadata]

        if not analyzed_images:
            st.info("解析済みの画像データはありません。")
            return

        st.warning(
            f"**{len(analyzed_images)} 件**の解析済みデータがあります。"
            "削除するとタイトル・要約・キーワードが消去され、未解析の状態に戻ります。"
        )

        # 削除方法の選択
        del_method = st.radio(
            "削除方法",
            ["🗑️ ゴミ箱に移動（再取り込み不可）", "🔄 メタデータのみ削除（再取り込み可能）"],
            key="del_method",
            horizontal=True,
        )

        if del_method == "🔄 メタデータのみ削除（再取り込み可能）":
            st.info(
                "💡 画像ファイルはDriveに残ります。メタデータのみ削除するので、"
                "別フォルダに移動してから再スキャンすると再取り込みできます。"
            )

        del_col1, del_col2, del_col3 = st.columns([1, 1, 3])
        _apply_batch_checkbox("_del_sel_flag", [f"del_sel_{img['id']}" for img in analyzed_images])
        with del_col1:
            if st.button("☑️ 全選択", key="del_select_all"):
                _set_batch_checkbox("_del_sel_flag", True)
        with del_col2:
            if st.button("☐ 全解除", key="del_deselect_all"):
                _set_batch_checkbox("_del_sel_flag", False)

        # ページネーション
        del_page_items, del_cur, del_total_pages = _paginate(analyzed_images, "batch_delete_page")
        _render_pagination_controls("batch_delete_page", del_cur, del_total_pages, len(analyzed_images))

        delete_ids = []
        cols_per_row = 4
        for row_start in range(0, len(del_page_items), cols_per_row):
            cols = st.columns(cols_per_row)
            for col_idx in range(cols_per_row):
                img_idx = row_start + col_idx
                if img_idx >= len(del_page_items):
                    break
                img = del_page_items[img_idx]
                fid = img["id"]
                meta = metadata[fid]
                title = meta.get("title", img["name"])
                status = get_status(meta)
                status_icon = get_status_icon(meta)
                with cols[col_idx]:
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        st.markdown(
                            '<div style="background:#333;border-radius:8px;'
                            'height:80px;display:flex;align-items:center;'
                            'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                            unsafe_allow_html=True,
                        )
                    st.caption(f"{status_icon} {title}")
                    if st.checkbox("削除する", value=st.session_state.get(f"del_sel_{fid}", False), key=f"del_sel_{fid}"):
                        delete_ids.append(fid)

        st.markdown("---")
        delete_count = len(delete_ids)

        if del_method == "🗑️ ゴミ箱に移動（再取り込み不可）":
            if delete_count > 0:
                st.warning(f"🗑️ **{delete_count} 件**の解析データをゴミ箱に移動します（{TRASH_RETENTION_DAYS}日後に完全削除）。")
                st.caption("💡 削除した画像は再スキャンしても再取り込みされません。ゴミ箱から復元すると再取り込み対象に戻ります。")
            if st.button(
                f"🗑️ 選択した {delete_count} 件をゴミ箱へ",
                type="primary",
                key="batch_delete_run",
                disabled=(delete_count == 0),
            ):
                moved = move_to_trash(delete_ids, metadata)
                for fid in delete_ids:
                    st.session_state.pop(f"del_sel_{fid}", None)
                st.success(f"✅ {moved} 件をゴミ箱に移動しました。「🗑️ ゴミ箱」ページから復元できます。")
                st.rerun()
        else:
            # メタデータのみ削除（無視リスト追加なし・ゴミ箱なし）
            if delete_count > 0:
                st.info(
                    f"🔄 **{delete_count} 件**のメタデータを削除します。\n"
                    "画像ファイルはDriveに残り、再スキャンで再取り込みできます。"
                )
            if st.button(
                f"🔄 選択した {delete_count} 件のメタデータを削除",
                type="primary",
                key="batch_meta_delete_run",
                disabled=(delete_count == 0),
            ):
                removed = 0
                for fid in delete_ids:
                    if fid in metadata:
                        del metadata[fid]
                        removed += 1
                    st.session_state.pop(f"del_sel_{fid}", None)
                # 無視リストからも除去（念のため）
                remove_from_ignore_list(delete_ids)
                save_metadata(metadata)
                _invalidate_all_caches()
                st.success(
                    f"✅ {removed} 件のメタデータを削除しました。\n"
                    "Driveで患者データフォルダに移動してからスキャンすると再取り込みされます。"
                )
                st.rerun()


def _run_batch_analyze(service, target_images, metadata, api_key, is_reanalyze=False, correction_hint=""):
    """一括解析 / 一括再解析の共通実行処理。

    新規解析の場合: 確認済み（STATUS_REVIEWED）として登録し、既存フォルダへ自動分類する。
    再解析の場合: 既存のfolder, sourceを保持する。
    correction_hint が指定された場合、AIに修正指示を渡す。
    """
    total = len(target_images)
    label = "指示付き再解析" if correction_hint else ("再解析" if is_reanalyze else "解析・登録")
    progress_bar = st.progress(0, text="解析を開始...")
    success_count = 0
    fail_count = 0
    folders = load_folders()

    for i, img in enumerate(target_images):
        fid = img["id"]
        fname = img["name"]
        # 患者データはAI解析をスキップ
        if fid in metadata and is_patient_data(metadata[fid]):
            continue
        progress_bar.progress(
            i / total,
            text=f"{label}中... ({i + 1}/{total}) {fname}",
        )

        try:
            image_bytes = download_image(service, fid)

            result = analyze_image_with_gemini(image_bytes, api_key, correction_hint=correction_hint)
            if result:
                if is_reanalyze and fid in metadata:
                    # 再解析: 既存のfolder, sourceを保持
                    old = metadata[fid]
                    for keep_key in ("folder", "source"):
                        if keep_key in old:
                            result[keep_key] = old[keep_key]
                else:
                    # 新規解析: 確認済みとして登録 & フォルダ自動分類
                    result["status"] = STATUS_REVIEWED
                    assigned_folder = _auto_classify_folder(result, api_key, folders)
                    result["folder"] = assigned_folder
                metadata[fid] = result
                save_metadata(metadata)
                success_count += 1
            else:
                fail_count += 1
        except Exception as e:
            st.warning(f"⚠️ {fname} の解析に失敗: {e}")
            fail_count += 1

        if i < total - 1:
            time.sleep(1)

    progress_bar.progress(1.0, text="完了！")
    action_name = "再解析" if is_reanalyze else "一括解析・登録"
    st.success(f"{action_name}が完了しました！ 成功: {success_count} 件 / 失敗: {fail_count} 件")
    st.rerun()


# ===========================================================================
# ページ: ゴミ箱
# ===========================================================================
def page_trash():
    """ゴミ箱ページ — 削除した解析データの復元・完全削除を行う。"""
    # 起動時に古いアイテムを自動パージ
    purged = purge_old_trash()
    if purged > 0:
        st.toast(f"🧹 {purged} 件の期限切れデータを自動削除しました")

    trash = load_trash()

    # --- サイドバー ---
    st.sidebar.header("🗑️ ゴミ箱")
    st.sidebar.write(f"ゴミ箱内: **{len(trash)}** 件")
    ignore_count = len(load_ignore_list())
    if ignore_count > 0:
        st.sidebar.caption(f"🚫 再取り込み防止中: {ignore_count} 件")
    st.sidebar.caption(f"削除後 {TRASH_RETENTION_DAYS} 日で自動的に完全削除されます")

    if not trash:
        st.info("ゴミ箱は空です。")
        return

    # --- 全選択 / 全解除 ---
    _apply_batch_checkbox("_trash_sel_flag", [f"trash_sel_{i}" for i in range(len(trash))])
    act_col1, act_col2, act_col3 = st.columns([1, 1, 4])
    with act_col1:
        if st.button("☑️ 全選択", key="trash_sel_all"):
            _set_batch_checkbox("_trash_sel_flag", True)
    with act_col2:
        if st.button("☐ 全解除", key="trash_sel_none"):
            _set_batch_checkbox("_trash_sel_flag", False)

    # --- アイテム一覧 ---
    selected_indices = []

    cols_per_row = 3
    for row_start in range(0, len(trash), cols_per_row):
        cols = st.columns(cols_per_row)
        for col_idx in range(cols_per_row):
            item_idx = row_start + col_idx
            if item_idx >= len(trash):
                break
            item = trash[item_idx]
            meta = item["metadata"]
            fid = item["file_id"]
            title = meta.get("title", fid[:20])
            keywords = meta.get("keywords", [])
            status = get_status(meta)
            status_icon = "✅" if status == STATUS_REVIEWED else "🆕"

            # 残り日数を計算
            try:
                deleted_at = datetime.fromisoformat(item["deleted_at"])
                remaining_days = TRASH_RETENTION_DAYS - (datetime.now() - deleted_at).days
                time_label = f"あと {remaining_days} 日"
            except (ValueError, KeyError):
                time_label = "不明"

            with cols[col_idx]:
                # カード風表示
                kw_html = ""
                if keywords:
                    kw_tags = " ".join(
                        f'<span style="background:#1a5276;color:#d6eaf8;'
                        f'padding:2px 8px;border-radius:10px;font-size:11px;'
                        f'margin:1px 2px;display:inline-block;">{kw}</span>'
                        for kw in keywords[:3]
                    )
                    kw_html = f'<div style="margin-top:6px;">{kw_tags}</div>'

                st.markdown(
                    f'<div style="border:2px solid #e74c3c;border-radius:10px;'
                    f'padding:14px;margin-bottom:8px;min-height:100px;'
                    f'opacity:0.8;">'
                    f'<p style="font-size:13px;font-weight:600;margin:0 0 4px 0;'
                    f'line-height:1.3;">{status_icon} {title}</p>'
                    f'<p style="font-size:11px;color:#e74c3c;margin:0;">⏳ {time_label}</p>'
                    f'{kw_html}'
                    f'</div>',
                    unsafe_allow_html=True,
                )

                checked = st.checkbox(
                    "選択",
                    value=st.session_state.get(f"trash_sel_{item_idx}", False),
                    key=f"trash_sel_{item_idx}",
                )
                if checked:
                    selected_indices.append(item_idx)

    # --- 操作ボタン ---
    st.markdown("---")
    sel_count = len(selected_indices)

    btn_col1, btn_col2 = st.columns(2)
    with btn_col1:
        if st.button(
            f"♻️ 選択した {sel_count} 件を復元",
            type="primary",
            key="trash_restore",
            disabled=(sel_count == 0),
        ):
            restored = restore_from_trash(selected_indices)
            for i in range(len(trash)):
                st.session_state.pop(f"trash_sel_{i}", None)
            st.success(f"✅ {restored} 件を復元しました。")
            st.rerun()

    with btn_col2:
        if sel_count > 0:
            st.error(f"⚠️ {sel_count} 件を完全削除すると元に戻せません。")
        if st.button(
            f"🔥 選択した {sel_count} 件を完全削除",
            key="trash_purge",
            disabled=(sel_count == 0),
        ):
            trash_items = load_trash()
            for idx in sorted(selected_indices, reverse=True):
                if 0 <= idx < len(trash_items):
                    trash_items.pop(idx)
            save_trash(trash_items)
            for i in range(len(trash)):
                st.session_state.pop(f"trash_sel_{i}", None)
            st.success(f"🔥 {sel_count} 件を完全削除しました。")
            st.rerun()


# ===========================================================================
# ページ: フォルダ設定
# ===========================================================================
def page_folder_settings():
    """フォルダの追加・名前変更・削除を行う管理ページ。"""
    metadata = load_metadata()
    folders = load_folders()

    st.subheader("🗂️ フォルダ設定")
    st.caption("フォルダの追加・名前変更・削除ができます。")

    # --- フォルダ新規作成 ---
    st.markdown("#### ➕ フォルダを追加")
    add_c1, add_c2 = st.columns([4, 1])
    with add_c1:
        new_folder_name = st.text_input(
            "新しいフォルダ名",
            placeholder="例: 股関節、脊椎、心臓...",
            key="fs_new_folder",
            label_visibility="collapsed",
        )
    with add_c2:
        if st.button("➕ 作成", key="fs_create_btn", width="stretch"):
            name = new_folder_name.strip()
            if not name:
                st.warning("フォルダ名を入力してください。")
            elif name in folders:
                st.warning(f"「{name}」は既に存在します。")
            else:
                folders.append(name)
                save_folders(folders)
                st.success(f"「{name}」を作成しました！")
                st.rerun()

    st.markdown("---")

    # --- フォルダ一覧（件数・名前変更・削除） ---
    st.markdown("#### 📁 フォルダ一覧")

    # 件数集計
    folder_counts = {}
    for meta in metadata.values():
        f = get_folder(meta)
        folder_counts[f] = folder_counts.get(f, 0) + 1

    if not folders:
        st.info("フォルダがありません。上の入力欄から作成してください。")
        return

    for i, fname in enumerate(folders):
        cnt = folder_counts.get(fname, 0)
        is_default = fname == DEFAULT_FOLDER

        with st.container():
            col_icon, col_name, col_count, col_rename, col_del = st.columns(
                [0.5, 3, 1, 1.5, 1]
            )

            with col_icon:
                st.markdown(f"### 📁")

            with col_name:
                st.markdown(f"**{fname}**")
                if is_default:
                    st.caption("（デフォルト — 削除不可）")

            with col_count:
                st.metric("画像数", cnt)

            with col_rename:
                if not is_default:
                    if st.button("✏️ 名前変更", key=f"fs_rename_btn_{i}", width="stretch"):
                        st.session_state["fs_renaming"] = fname
                        st.rerun()

            with col_del:
                if not is_default:
                    if st.button("🗑️ 削除", key=f"fs_del_btn_{i}", width="stretch"):
                        st.session_state["fs_deleting"] = fname
                        st.rerun()

        # --- 名前変更ダイアログ ---
        if st.session_state.get("fs_renaming") == fname:
            with st.container():
                st.markdown(f"**「{fname}」の名前を変更:**")
                rc1, rc2, rc3 = st.columns([3, 1, 1])
                with rc1:
                    new_name = st.text_input(
                        "新しい名前",
                        value=fname,
                        key=f"fs_rename_input_{i}",
                        label_visibility="collapsed",
                    )
                with rc2:
                    if st.button("✅ 変更", key=f"fs_rename_ok_{i}", width="stretch"):
                        new_name = new_name.strip()
                        if not new_name:
                            st.error("名前を入力してください。")
                        elif new_name == fname:
                            st.session_state.pop("fs_renaming", None)
                            st.rerun()
                        elif new_name in folders:
                            st.error(f"「{new_name}」は既に存在します。")
                        else:
                            # フォルダ名を更新
                            idx = folders.index(fname)
                            folders[idx] = new_name
                            save_folders(folders)
                            # メタデータ内のフォルダ名も更新
                            for fid, meta in metadata.items():
                                if get_folder(meta) == fname:
                                    meta["folder"] = new_name
                            save_metadata(metadata)
                            st.session_state.pop("fs_renaming", None)
                            st.success(f"「{fname}」→「{new_name}」に変更しました！")
                            st.rerun()
                with rc3:
                    if st.button("キャンセル", key=f"fs_rename_cancel_{i}", width="stretch"):
                        st.session_state.pop("fs_renaming", None)
                        st.rerun()

        # --- 削除確認 ---
        if st.session_state.get("fs_deleting") == fname:
            with st.container():
                if cnt > 0:
                    st.warning(
                        f"「{fname}」には **{cnt} 件**の画像があります。"
                        f"削除すると画像は「{DEFAULT_FOLDER}」に移動されます。"
                    )
                else:
                    st.info(f"「{fname}」を削除しますか？（画像はありません）")
                dc1, dc2 = st.columns(2)
                with dc1:
                    if st.button("🗑️ 削除する", key=f"fs_del_ok_{i}", type="primary", width="stretch"):
                        # 画像を未分類に移動
                        for fid, meta in metadata.items():
                            if get_folder(meta) == fname:
                                meta["folder"] = DEFAULT_FOLDER
                        save_metadata(metadata)
                        folders.remove(fname)
                        save_folders(folders)
                        st.session_state.pop("fs_deleting", None)
                        st.success(f"「{fname}」を削除しました。")
                        st.rerun()
                with dc2:
                    if st.button("キャンセル", key=f"fs_del_cancel_{i}", width="stretch"):
                        st.session_state.pop("fs_deleting", None)
                        st.rerun()

        st.markdown("---")


# ===========================================================================
# ページ: フォルダ整理（手動）
# ===========================================================================
def page_folder_manual():
    """手動フォルダ整理ページ — 画像を自分でフォルダに分類する。"""
    service = get_drive_service()
    folder_id = get_folder_id()
    metadata = load_metadata()
    folders = load_folders()

    images = list_all_images(service, folder_id, metadata, get_patient_folder_id())
    if not images:
        st.info("フォルダ内に画像が見つかりませんでした。")
        return

    analyzed = [img for img in images if img["id"] in metadata]
    if not analyzed:
        st.info("解析済みの画像がありません。先に画像をAI解析してください。")
        return

    # --- サイドバー: フォルダ管理 ---
    st.sidebar.header("📂 フォルダ管理")

    # 新規フォルダ作成
    new_folder = st.sidebar.text_input("新しいフォルダ名", placeholder="例: 股関節、脊椎...")
    if st.sidebar.button("➕ フォルダ作成", width="stretch") and new_folder.strip():
        fname = new_folder.strip()
        if fname not in folders:
            folders.append(fname)
            save_folders(folders)
            st.sidebar.success(f"「{fname}」を作成しました")
            st.rerun()
        else:
            st.sidebar.warning("同名のフォルダが既にあります")

    st.sidebar.markdown("---")

    # フォルダ一覧 + 件数
    st.sidebar.subheader("📊 フォルダ別件数")
    folder_counts = {}
    for img in analyzed:
        f = get_folder(metadata[img["id"]])
        folder_counts[f] = folder_counts.get(f, 0) + 1
    # folders リストに含まれるフォルダ + メタデータに存在するフォルダの両方を表示
    display_folders = list(folders)
    for f in sorted(folder_counts.keys()):
        if f not in display_folders:
            display_folders.append(f)
    for f in display_folders:
        cnt = folder_counts.get(f, 0)
        icon = "🏥" if f == PATIENT_DATA_FOLDER else "📁"
        st.sidebar.write(f"{icon} {f}: **{cnt}** 件")

    # フォルダ削除
    st.sidebar.markdown("---")
    deletable = [f for f in folders if f not in (DEFAULT_FOLDER, PATIENT_DATA_FOLDER)]
    if deletable:
        del_folder = st.sidebar.selectbox("フォルダを削除", ["---"] + deletable, key="del_folder_sel")
        if st.sidebar.button("🗑️ このフォルダを削除", width="stretch") and del_folder != "---":
            # フォルダ内の画像を「未分類」に移動
            for fid, meta in metadata.items():
                if get_folder(meta) == del_folder:
                    meta["folder"] = DEFAULT_FOLDER
            save_metadata(metadata)
            folders.remove(del_folder)
            save_folders(folders)
            st.sidebar.success(f"「{del_folder}」を削除し、画像を「{DEFAULT_FOLDER}」に移動しました")
            st.rerun()

    # --- メイン画面: フォルダ選択 → 画像を移動 ---
    st.subheader("📂 手動フォルダ整理")
    st.caption("移動先フォルダを選んでから、画像をチェックして移動してください。")

    # 移動先フォルダ選択
    dest_folder = st.selectbox(
        "移動先フォルダ",
        folders,
        key="manual_dest_folder",
    )

    # フィルタ: 表示するフォルダ
    all_folders = get_all_folders_from_metadata(metadata)
    show_folder = st.selectbox(
        "表示するフォルダ",
        ["すべて"] + all_folders,
        key="manual_show_folder",
    )

    # 対象画像をフィルタ
    if show_folder == "すべて":
        display_images = analyzed
    else:
        display_images = [
            img for img in analyzed
            if get_folder(metadata[img["id"]]) == show_folder
        ]

    if not display_images:
        st.info("表示対象の画像がありません。")
        return

    # ページネーション
    mf_page_items, mf_cur, mf_total_pages = _paginate(display_images, "manual_folder_page")
    _render_pagination_controls("manual_folder_page", mf_cur, mf_total_pages, len(display_images))

    # 全選択/全解除
    _apply_batch_checkbox("_mf_sel_flag", [f"mf_sel_{img['id']}" for img in display_images])
    mc1, mc2, mc3 = st.columns([1, 1, 4])
    with mc1:
        if st.button("☑️ 全選択", key="mf_sel_all"):
            _set_batch_checkbox("_mf_sel_flag", True)
    with mc2:
        if st.button("☐ 全解除", key="mf_sel_none"):
            _set_batch_checkbox("_mf_sel_flag", False)

    # グリッド表示
    move_ids = []
    cols_per_row = 4
    for row_start in range(0, len(mf_page_items), cols_per_row):
        cols = st.columns(cols_per_row)
        for col_idx in range(cols_per_row):
            img_idx = row_start + col_idx
            if img_idx >= len(mf_page_items):
                break
            img = mf_page_items[img_idx]
            fid = img["id"]
            meta = metadata[fid]
            title = meta.get("title", img["name"])
            cur_folder = get_folder(meta)

            with cols[col_idx]:
                try:
                    thumb_bytes = download_image(service, fid)
                    st.image(thumb_bytes, width="stretch")
                except Exception:
                    st.markdown(
                        '<div style="background:#333;border-radius:8px;'
                        'height:80px;display:flex;align-items:center;'
                        'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                        unsafe_allow_html=True,
                    )
                st.caption(f"📁 {cur_folder}")
                st.caption(title)

                checked = st.checkbox(
                    "選択",
                    value=st.session_state.get(f"mf_sel_{fid}", False),
                    key=f"mf_sel_{fid}",
                )
                if checked:
                    move_ids.append(fid)

    # 移動ボタン
    st.markdown("---")
    move_count = len(move_ids)
    if st.button(
        f"📁 選択した {move_count} 件を「{dest_folder}」に移動",
        type="primary",
        key="mf_move_run",
        disabled=(move_count == 0),
    ):
        for fid in move_ids:
            if fid in metadata:
                metadata[fid]["folder"] = dest_folder
        save_metadata(metadata)
        for fid in move_ids:
            st.session_state.pop(f"mf_sel_{fid}", None)
        st.success(f"✅ {move_count} 件を「{dest_folder}」に移動しました。")
        st.rerun()


# ===========================================================================
# ページ: フォルダ整理（AI自動）
# ===========================================================================
def page_folder_ai():
    """AI自動フォルダ整理ページ — Geminiが画像をフォルダに自動分類する。"""
    service = get_drive_service()
    folder_id = get_folder_id()
    api_key = get_gemini_api_key()
    metadata = load_metadata()
    folders = load_folders()

    images = list_all_images(service, folder_id, metadata, get_patient_folder_id())
    if not images:
        st.info("フォルダ内に画像が見つかりませんでした。")
        return

    if not api_key:
        st.warning("AI整理を使用するには `GOOGLE_API_KEY` を設定してください。")
        return

    analyzed = [img for img in images if img["id"] in metadata]
    if not analyzed:
        st.info("解析済みの画像がありません。先に画像をAI解析してください。")
        return

    # --- サイドバー ---
    st.sidebar.header("🤖 AI整理")
    if "ai_view_folder" not in st.session_state:
        st.session_state["ai_view_folder"] = None

    # 「分類画面に戻る」ボタン（フォルダ表示中のみ）
    if st.session_state["ai_view_folder"] is not None:
        if st.sidebar.button("⬅️ 分類画面に戻る", key="ai_back_to_main", width="stretch"):
            st.session_state["ai_view_folder"] = None
            st.session_state.pop("folder_detail_id", None)
            st.rerun()

    # --- メイン画面 ---
    # フォルダ表示モード（サイドバーでフォルダをクリックした場合）
    if st.session_state["ai_view_folder"] is not None:
        view_folder = st.session_state["ai_view_folder"]
        folder_images = [
            img for img in analyzed
            if img["id"] in metadata and get_folder(metadata[img["id"]]) == view_folder
        ]

        # 詳細表示用の state
        if "folder_detail_id" not in st.session_state:
            st.session_state["folder_detail_id"] = None

        # --- フォルダ内画像の詳細表示モード ---
        detail_fid = st.session_state["folder_detail_id"]
        if detail_fid is not None:
            # 選択された画像を探す
            detail_file = None
            for img in folder_images:
                if img["id"] == detail_fid:
                    detail_file = img
                    break

            if detail_file is None:
                st.session_state["folder_detail_id"] = None
                st.rerun()
                return

            file_id = detail_file["id"]

            if st.button("⬅️ フォルダ一覧に戻る", key="back_to_folder_grid"):
                st.session_state["folder_detail_id"] = None
                st.session_state.pop("editing_file_id", None)
                st.rerun()

            st.caption(f"📁 {view_folder}")

            # --- 画像読み込み ---
            image_bytes = None
            try:
                image_bytes = download_image(service, file_id)
            except Exception as e:
                st.error(f"画像の表示中にエラーが発生しました: {e}")
                return

            meta = metadata.get(file_id, {})

            # --- 横並びレイアウト: 画像（左）+ 情報サマリー（右） ---
            col_img, col_info = st.columns([1, 1])
            with col_img:
                st.image(image_bytes, width="stretch")

            with col_info:
                title = meta.get("title", detail_file["name"])
                st.subheader(title)
                if file_id in metadata:
                    s = get_status(meta)
                    if s == STATUS_REVIEWED:
                        st.success("✅ 確認済み")
                    else:
                        st.warning("📝 未確認")
                render_summary(meta.get("summary", ""))
                keywords = meta.get("keywords", [])
                if keywords:
                    render_keyword_tags(keywords)
                fmt = detail_file["mimeType"].split("/")[-1].upper()
                st.caption(f"形式: {fmt}")

            # --- 編集フォーム（折りたたみ） ---
            if file_id in metadata:
                _is_pd_f = is_patient_data(metadata[file_id])
                edit_label_f = "📝 検査所見を編集" if _is_pd_f else "📝 編集"
                with st.expander(edit_label_f, expanded=_is_pd_f):
                    display_edit_form(file_id, metadata[file_id], metadata)
                if _is_pd_f:
                    st.info("🏥 患者データ: AI解析は行いません。手動で検査所見を入力してください。")
                elif api_key:
                    if st.button("🤖 AIで再解析する", key=f"folder_reanalyze_{file_id}"):
                        with st.spinner("Gemini で再解析中..."):
                            image_bytes = download_image(service, file_id)
                            result = analyze_image_with_gemini(image_bytes, api_key)
                            if result:
                                old = metadata.get(file_id, {})
                                for keep_key in ("folder", "source"):
                                    if keep_key in old:
                                        result[keep_key] = old[keep_key]
                                metadata[file_id] = result
                                save_metadata(metadata)
                                st.session_state.pop("editing_file_id", None)
                                st.success("再解析が完了しました！")
                                st.rerun()
            return

        # --- フォルダ内グリッド一覧 ---
        folder_icon = "🏥" if view_folder == PATIENT_DATA_FOLDER else "📁"
        st.subheader(f"{folder_icon} {view_folder}")
        if not folder_images:
            st.info("このフォルダには画像がありません。")
            return

        # --- 削除モード切替 ---
        if "folder_delete_mode" not in st.session_state:
            st.session_state["folder_delete_mode"] = False

        fd_btn_c1, fd_btn_c2, fd_btn_c3 = st.columns([1, 1, 4])
        with fd_btn_c1:
            if st.session_state["folder_delete_mode"]:
                if st.button("✖ 削除モード終了", key="fd_exit_del", width="stretch"):
                    st.session_state["folder_delete_mode"] = False
                    for img in folder_images:
                        st.session_state.pop(f"fd_del_{img['id']}", None)
                    st.rerun()
            else:
                if st.button("🗑️ 削除モード", key="fd_enter_del", width="stretch"):
                    st.session_state["folder_delete_mode"] = True
                    st.rerun()
        with fd_btn_c2:
            st.caption(f"{len(folder_images)} 件")

        # 削除モード: 全選択/全解除
        if st.session_state["folder_delete_mode"]:
            fd_sel_c1, fd_sel_c2, fd_sel_c3 = st.columns([1, 1, 4])
            with fd_sel_c1:
                if st.button("☑️ 全選択", key="fd_del_sel_all"):
                    for img in folder_images:
                        st.session_state[f"fd_del_{img['id']}"] = True
                    st.rerun()
            with fd_sel_c2:
                if st.button("☐ 全解除", key="fd_del_desel_all"):
                    for img in folder_images:
                        st.session_state[f"fd_del_{img['id']}"] = False
                    st.rerun()

        # ページネーション
        fd_page_items, fd_cur, fd_total_pages = _paginate(folder_images, "ai_folder_grid_page")
        _render_pagination_controls("ai_folder_grid_page", fd_cur, fd_total_pages, len(folder_images))

        fd_delete_ids = []
        cols_per_row = 4
        for row_start in range(0, len(fd_page_items), cols_per_row):
            cols = st.columns(cols_per_row)
            for col_idx in range(cols_per_row):
                img_idx = row_start + col_idx
                if img_idx >= len(fd_page_items):
                    break
                img = fd_page_items[img_idx]
                fid = img["id"]
                meta = metadata[fid]
                title = meta.get("title", img["name"])

                with cols[col_idx]:
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        st.markdown(
                            '<div style="background:#333;border-radius:8px;'
                            'height:80px;display:flex;align-items:center;'
                            'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                            unsafe_allow_html=True,
                        )
                    icon = get_status_icon(meta)
                    st.caption(f"{icon} {title}")
                    kw = meta.get("keywords", [])
                    if kw:
                        st.caption(" ".join(f"`{k}`" for k in kw[:3]))

                    if st.session_state["folder_delete_mode"]:
                        if st.checkbox(
                            "削除する", value=st.session_state.get(f"fd_del_{fid}", False),
                            key=f"fd_del_{fid}",
                        ):
                            fd_delete_ids.append(fid)
                    else:
                        if st.button("🔍 詳細を見る", key=f"folder_open_{fid}", width="stretch"):
                            st.session_state["folder_detail_id"] = fid
                            st.rerun()

        # --- 削除実行エリア ---
        if st.session_state["folder_delete_mode"]:
            st.markdown("---")
            fd_del_count = len(fd_delete_ids)

            fd_del_method = st.radio(
                "削除方法",
                ["🗑️ ゴミ箱に移動（再取り込み不可）", "🔄 メタデータのみ削除（再取り込み可能）"],
                key="fd_del_method",
                horizontal=True,
            )

            if fd_del_method == "🗑️ ゴミ箱に移動（再取り込み不可）":
                if st.button(
                    f"🗑️ 選択した {fd_del_count} 件をゴミ箱へ",
                    type="primary",
                    key="fd_del_trash_run",
                    disabled=(fd_del_count == 0),
                ):
                    moved = move_to_trash(fd_delete_ids, metadata)
                    for fid in fd_delete_ids:
                        st.session_state.pop(f"fd_del_{fid}", None)
                    st.session_state["folder_delete_mode"] = False
                    _invalidate_all_caches()
                    st.success(f"✅ {moved} 件をゴミ箱に移動しました。")
                    st.rerun()
            else:
                if st.button(
                    f"🔄 選択した {fd_del_count} 件のメタデータを削除",
                    type="primary",
                    key="fd_del_meta_run",
                    disabled=(fd_del_count == 0),
                ):
                    removed = 0
                    for fid in fd_delete_ids:
                        if fid in metadata:
                            del metadata[fid]
                            removed += 1
                        st.session_state.pop(f"fd_del_{fid}", None)
                    remove_from_ignore_list(fd_delete_ids)
                    save_metadata(metadata)
                    st.session_state["folder_delete_mode"] = False
                    _invalidate_all_caches()
                    st.success(f"✅ {removed} 件のメタデータを削除しました。")
                    st.rerun()
        return

    st.subheader("🤖 AI自動フォルダ整理")

    # --- 整理方針の指示 ---
    st.markdown("#### 📝 整理方針")
    st.caption("AIにどのような観点で整理してほしいかを自由に指示できます。空欄の場合はAIが自動判断します。")
    user_instruction = st.text_area(
        "整理の指示（任意）",
        value=st.session_state.get("ai_folder_instruction", ""),
        placeholder="例:\n・解剖学的部位（頭部、胸部、腹部…）で分けて\n・疾患カテゴリ（骨折、腫瘍、感染症…）で分類して\n・画像モダリティ（CT、MRI、X線…）ごとに整理して\n・整形外科の観点で分けてほしい",
        height=100,
        key="ai_folder_instruction",
    )

    st.markdown("---")

    # ステップ1: フォルダ名をAIに提案させる or 既存フォルダを使う
    st.markdown("#### ① フォルダ設定")
    mode = st.radio(
        "フォルダの決め方",
        ["既存フォルダを使う", "AIに新しいフォルダを提案させる"],
        key="ai_folder_mode",
        horizontal=True,
    )

    if mode == "AIに新しいフォルダを提案させる":
        if st.button("🤖 フォルダ名を提案", key="ai_suggest_folders"):
            with st.spinner("AIがフォルダ構成を考えています..."):
                try:
                    # 全画像のタイトル・キーワードを集約
                    summaries = []
                    for img in analyzed:
                        meta = metadata[img["id"]]
                        t = meta.get("title", "")
                        kw = ", ".join(meta.get("keywords", []))
                        summaries.append(f"- {t} [{kw}]")

                    instruction_part = ""
                    if user_instruction.strip():
                        instruction_part = (
                            f"\n\n【ユーザーからの整理方針】\n{user_instruction.strip()}\n"
                            "上記の方針に従ってフォルダ名を提案してください。"
                        )
                    else:
                        instruction_part = (
                            "\n解剖学的部位、疾患カテゴリ、画像モダリティなどで分類してください。"
                        )

                    prompt = (
                        "以下は医療画像の解析データ一覧です。\n"
                        + "\n".join(summaries)
                        + f"\n\nこれらを整理するための最適なフォルダ名を5〜10個提案してください。"
                        + instruction_part
                        + "\nフォルダ名のみをカンマ区切りで出力してください。日本語で。"
                    )
                    resp_text = _gemini_generate(api_key, [{"text": prompt}])
                    suggested = [s.strip() for s in resp_text.strip().split(",") if s.strip()]
                    st.session_state["ai_suggested_folders"] = suggested
                except Exception as e:
                    st.error(f"フォルダ提案に失敗しました: {e}")

        if "ai_suggested_folders" in st.session_state:
            suggested = st.session_state["ai_suggested_folders"]
            st.markdown("**AIの提案（編集できます）:**")

            # 各フォルダ名を編集可能なテキスト入力で表示
            edited_folders = []
            remove_idx = None
            for i, fname in enumerate(suggested):
                ec1, ec2 = st.columns([5, 1])
                with ec1:
                    edited = st.text_input(
                        f"フォルダ {i + 1}",
                        value=fname,
                        key=f"ai_edit_folder_{i}",
                        label_visibility="collapsed",
                    )
                with ec2:
                    if st.button("✖", key=f"ai_remove_folder_{i}"):
                        remove_idx = i
                if edited.strip():
                    edited_folders.append(edited.strip())

            # 削除処理（ループ完了後にまとめて実行）
            if remove_idx is not None:
                # 編集済みの値を反映してから削除
                new_suggested = []
                for i in range(len(suggested)):
                    val = st.session_state.get(f"ai_edit_folder_{i}", suggested[i]).strip()
                    if i != remove_idx and val:
                        new_suggested.append(val)
                # 古いキーをすべてクリア
                for i in range(len(suggested)):
                    st.session_state.pop(f"ai_edit_folder_{i}", None)
                st.session_state["ai_suggested_folders"] = new_suggested
                st.rerun()

            # フォルダ追加ボタン
            ac1, ac2 = st.columns([5, 1])
            with ac1:
                new_name = st.text_input(
                    "追加するフォルダ名",
                    placeholder="フォルダ名を入力…",
                    key="ai_add_folder_input",
                    label_visibility="collapsed",
                )
            with ac2:
                if st.button("➕", key="ai_add_folder_btn") and new_name.strip():
                    # 編集済みの値を反映してから追加
                    new_suggested = []
                    for i in range(len(suggested)):
                        val = st.session_state.get(f"ai_edit_folder_{i}", suggested[i]).strip()
                        if val:
                            new_suggested.append(val)
                    new_suggested.append(new_name.strip())
                    for i in range(len(suggested)):
                        st.session_state.pop(f"ai_edit_folder_{i}", None)
                    st.session_state["ai_suggested_folders"] = new_suggested
                    st.rerun()

            if st.button("✅ これらのフォルダを作成して使用", key="ai_create_suggested"):
                for f in edited_folders:
                    if f not in folders:
                        folders.append(f)
                save_folders(folders)
                # キーをクリア
                for i in range(len(suggested)):
                    st.session_state.pop(f"ai_edit_folder_{i}", None)
                st.success(f"フォルダを作成しました！（{len(edited_folders)} 件）")
                st.session_state.pop("ai_suggested_folders", None)
                st.rerun()

    # 使用するフォルダ一覧を表示
    folders = load_folders()
    st.markdown("**現在のフォルダ:**")
    st.write(" / ".join(f"📁 {f}" for f in folders))

    # ステップ2: AIが各画像をフォルダに分類
    st.markdown("---")
    st.markdown("#### ② AI自動分類を実行")

    # 対象選択
    target_choice = st.radio(
        "分類対象",
        ["未分類の画像のみ", "すべての画像（再分類）"],
        key="ai_target",
        horizontal=True,
    )

    if target_choice == "未分類の画像のみ":
        targets = [img for img in analyzed if get_folder(metadata[img["id"]]) == DEFAULT_FOLDER]
    else:
        targets = analyzed

    st.write(f"対象: **{len(targets)}** 件")

    if not targets:
        st.success("分類対象の画像がありません。")
        return

    if st.button(
        f"🤖 {len(targets)} 件をAIで自動分類",
        type="primary",
        key="ai_classify_run",
    ):
        folder_names = ", ".join(folders)

        progress_bar = st.progress(0, text="AI分類を開始...")
        classified = 0
        errors = 0

        for i, img in enumerate(targets):
            fid = img["id"]
            meta = metadata[fid]
            title = meta.get("title", "")
            summary = meta.get("summary", "")
            keywords = ", ".join(meta.get("keywords", []))

            progress_bar.progress(
                i / len(targets),
                text=f"分類中... ({i + 1}/{len(targets)}) {title}",
            )

            instruction_hint = ""
            if user_instruction.strip():
                instruction_hint = (
                    f"\n【整理方針】{user_instruction.strip()}\n"
                    "上記の方針を考慮して最適なフォルダを選んでください。\n"
                )

            prompt = (
                f"以下の医療画像を最も適切なフォルダに分類してください。\n\n"
                f"タイトル: {title}\n要約: {summary}\nキーワード: {keywords}\n\n"
                f"選択肢: {folder_names}\n"
                f"{instruction_hint}\n"
                f"必ず上記の選択肢の中から1つだけ選び、フォルダ名のみを出力してください。選択肢にないフォルダ名は絶対に使わないでください。"
            )

            try:
                result = _gemini_generate(api_key, [{"text": prompt}]).strip()
                # フォルダ名リストから最も近いものを選択（一致しなければ未分類）
                matched = None
                for f in folders:
                    if f in result or result in f:
                        matched = f
                        break
                if matched is None:
                    matched = DEFAULT_FOLDER

                metadata[fid]["folder"] = matched
                classified += 1
            except Exception:
                errors += 1

            if i < len(targets) - 1:
                time.sleep(0.5)

        save_metadata(metadata)
        progress_bar.progress(1.0, text="完了！")
        st.success(f"✅ 分類完了！ 成功: {classified} 件 / 失敗: {errors} 件")
        st.rerun()

    # ステップ3: 結果プレビュー
    st.markdown("---")
    st.markdown("#### ③ 分類結果")
    metadata = load_metadata()
    folders = load_folders()
    for folder_name in folders:
        folder_images = [
            img for img in analyzed
            if img["id"] in metadata and get_folder(metadata[img["id"]]) == folder_name
        ]
        if not folder_images:
            continue
        with st.expander(f"📁 {folder_name}（{len(folder_images)} 件）", expanded=False):
            pk = f"ai_result_{folder_name}_page"
            fi_page, fi_cur, fi_tp = _paginate(folder_images, pk)
            _render_pagination_controls(pk, fi_cur, fi_tp, len(folder_images))
            cols = st.columns(4)
            for idx, img in enumerate(fi_page):
                fid = img["id"]
                meta = metadata[fid]
                title = meta.get("title", img["name"])
                with cols[idx % 4]:
                    try:
                        thumb_bytes = download_image(service, fid)
                        st.image(thumb_bytes, width="stretch")
                    except Exception:
                        pass
                    st.caption(title)


# ===========================================================================
# ページ: チャット検索 (Q&A)
# ===========================================================================
def page_chat():
    """チャット検索ページ — 蓄積された知識に対して自然言語で質問する。"""
    api_key = get_gemini_api_key()
    metadata = load_metadata()
    service = get_drive_service()
    sessions = load_chat_sessions()
    knowledge_count = len(metadata)

    # --- session_state 初期化 ---
    if "active_session_id" not in st.session_state:
        st.session_state["active_session_id"] = None
    if "chat_messages" not in st.session_state:
        st.session_state["chat_messages"] = []

    # --- 既存の未保存メッセージがあればセッションに移行 ---
    if (
        st.session_state["chat_messages"]
        and st.session_state["active_session_id"] is None
    ):
        new_id = str(uuid.uuid4())
        first_msg = st.session_state["chat_messages"][0]
        title = first_msg.get("content", "以前の会話")[:30]
        sessions[new_id] = {
            "id": new_id,
            "title": title,
            "created_at": datetime.now().isoformat(),
            "updated_at": datetime.now().isoformat(),
            "messages": st.session_state["chat_messages"].copy(),
        }
        save_chat_sessions(sessions)
        st.session_state["active_session_id"] = new_id

    # --- サイドバー ---
    render_chat_sidebar(sessions, metadata)

    # --- メイン画面 ---
    if not api_key:
        st.warning(
            "チャット機能を使用するには `GOOGLE_API_KEY` を "
            "`.streamlit/secrets.toml` に設定してください。"
        )
        return

    # --- 入力欄（常に上部に表示 / Enterキーで送信） ---
    with st.form(key="chat_form", clear_on_submit=True):
        user_input = st.text_input(
            "質問を入力",
            placeholder="臨床知識について質問してください...",
            label_visibility="collapsed",
        )
        send_clicked = st.form_submit_button("🔍 検索する", type="primary")

    # --- 📷 画像取り込み ---
    with st.expander("📷 画像を取り込む", expanded=False):
        # pib() と file_uploader をタブで分離（モバイル互換性のため）
        upload_tab1, upload_tab2 = st.tabs(["📁 ファイル選択", "📋 クリップボード（PC）"])

        img_bytes = None
        img_name = "image.png"

        with upload_tab1:
            uploaded_file = st.file_uploader(
                "画像ファイルを選択",
                type=["png", "jpg", "jpeg"],
                key="chat_image_upload",
                label_visibility="collapsed",
            )
            if uploaded_file is not None:
                img_bytes = uploaded_file.getvalue()
                img_name = uploaded_file.name

        with upload_tab2:
            try:
                from streamlit_paste_button import paste_image_button as pib
                st.caption("スクショをコピーしてボタンで貼り付け:")
                paste_result = pib(
                    label="📋 クリップボードから画像を貼り付け",
                    text_color="#5b8def",
                    background_color="transparent",
                    hover_background_color="rgba(91,139,239,0.1)",
                )
                if paste_result and paste_result.image_data is not None:
                    buf = io.BytesIO()
                    paste_result.image_data.save(buf, format="PNG")
                    img_bytes = buf.getvalue()
                    img_name = f"paste_{datetime.now().strftime('%H%M%S')}.png"
            except Exception:
                st.caption("📋 クリップボード貼り付けはPC版でのみ利用可能です")

        if img_bytes:
            # 既に取り込み済みの画像がある場合は詳細表示
            last_upload_id = st.session_state.get("last_upload_id")
            if last_upload_id and last_upload_id in metadata:
                meta = metadata[last_upload_id]
                st.success("✅ 取り込み完了！")
                col_img, col_info = st.columns([1, 2])
                with col_img:
                    try:
                        saved_bytes = download_image(service, last_upload_id)
                        st.image(saved_bytes, width=250)
                    except Exception:
                        st.image(img_bytes, width=250)
                with col_info:
                    st.markdown(f"### {meta.get('title', '不明')}")
                    status = get_status(meta)
                    if status == STATUS_REVIEWED:
                        st.markdown("✅ **確認済み**")
                    else:
                        st.markdown("📝 **未確認**")
                    kw = meta.get("keywords", [])
                    if kw:
                        st.markdown(" ".join(f"`{k}`" for k in kw))
                # 要約（箇条書き）
                render_summary(meta.get("summary", ""))
                # アクションボタン
                btn_c1, btn_c2, btn_c3 = st.columns(3)
                with btn_c1:
                    if status != STATUS_REVIEWED:
                        if st.button("✅ レビュー認証", key="upload_review", type="primary", width="stretch"):
                            existing = metadata.get(last_upload_id, {})
                            existing["status"] = STATUS_REVIEWED
                            metadata[last_upload_id] = existing
                            save_metadata(metadata)
                            st.rerun()
                    else:
                        st.button("✅ 認証済み", key="upload_reviewed", disabled=True, width="stretch")
                with btn_c2:
                    if st.button("📝 詳細編集", key="upload_detail", width="stretch"):
                        st.session_state["lib_back_tab"] = st.session_state.get("active_tab")
                        st.session_state["active_tab"] = "📸 画像ライブラリ"
                        st.session_state["lib_selected_id"] = last_upload_id
                        st.session_state.pop("last_upload_id", None)
                        st.rerun()
                with btn_c3:
                    if st.button("🗑️ 削除", key="upload_delete", width="stretch"):
                        move_to_trash([last_upload_id], metadata)
                        # ローカル画像ファイルも削除
                        for ext in ("png", "jpg", "jpeg"):
                            p = UPLOADS_DIR / f"{last_upload_id}.{ext}"
                            if p.exists():
                                p.unlink()
                        st.session_state.pop("last_upload_id", None)
                        st.success("🗑️ ゴミ箱に移動しました")
                        st.rerun()
                # 新しい画像を取り込むボタン
                if st.button("📷 別の画像を取り込む", key="upload_another"):
                    st.session_state.pop("last_upload_id", None)
                    st.rerun()
            else:
                # 未取り込み：プレビューと取り込みボタン
                col_preview, col_action = st.columns([1, 1])
                with col_preview:
                    st.image(img_bytes, width=300, caption=img_name)
                with col_action:
                    st.markdown(f"**サイズ:** {len(img_bytes) / 1024:.0f} KB")
                    if not api_key:
                        st.warning("AI解析には `GOOGLE_API_KEY` の設定が必要です。")
                    else:
                        if st.button(
                            "🤖 AI解析して知識ベースに取り込む",
                            key="btn_upload_analyze",
                            type="primary",
                            width="stretch",
                        ):
                            with st.spinner("AI解析中..."):
                                result = analyze_image_with_gemini(img_bytes, api_key)
                            if result:
                                # ローカルに画像を保存
                                UPLOADS_DIR.mkdir(exist_ok=True)
                                file_id = f"upload_{uuid.uuid4().hex[:12]}"
                                ext = img_name.rsplit(".", 1)[-1].lower() if "." in img_name else "png"
                                save_path = UPLOADS_DIR / f"{file_id}.{ext}"
                                save_path.write_bytes(img_bytes)
                                # メタデータに保存
                                result["folder"] = DEFAULT_FOLDER
                                result["source"] = "upload"
                                metadata[file_id] = result
                                save_metadata(metadata)
                                st.session_state["last_upload_id"] = file_id
                                st.balloons()
                                st.rerun()

    if knowledge_count == 0 and not st.session_state.get("chat_messages"):
        st.info(
            "まだ知識が登録されていません。\n\n"
            "上の📷から画像を取り込むか、「⚡ 取り込み・解析」タブで画像をAI解析して知識を蓄積してください。"
        )

    # 質問例クリックからの送信処理
    pending = st.session_state.pop("pending_question", None)
    if pending:
        handle_chat_submit(pending, sessions, metadata, api_key)

    # 送信処理
    if send_clicked and user_input:
        handle_chat_submit(user_input, sessions, metadata, api_key)

    # --- 表示エリア ---
    if not st.session_state["chat_messages"]:
        render_home_screen(knowledge_count, metadata, service)
        return

    # --- 最新の回答を表示 ---
    messages = st.session_state["chat_messages"]

    latest_q = None
    latest_a = None
    for msg in reversed(messages):
        if msg["role"] == "assistant" and latest_a is None:
            latest_a = msg
        elif msg["role"] == "user" and latest_q is None:
            latest_q = msg
        if latest_q and latest_a:
            break

    if latest_q:
        st.markdown(
            f"<p style='background:#1a3a5c; border-radius:12px; "
            f"padding:12px 18px; color:#e0e0e0; font-size:15px;'>"
            f"💬 {latest_q['content']}</p>",
            unsafe_allow_html=True,
        )

    if latest_a:
        display_kb_response_with_images(
            latest_a.get("content", ""), metadata, service
        )

    # --- 過去の履歴（折りたたみ） ---
    past_pairs = []
    i = 0
    while i < len(messages) - 2:
        if (
            messages[i]["role"] == "user"
            and i + 1 < len(messages)
            and messages[i + 1]["role"] == "assistant"
        ):
            past_pairs.append((messages[i], messages[i + 1]))
            i += 2
        else:
            i += 1

    if past_pairs:
        st.markdown("---")
        with st.expander(f"📜 過去の質問履歴（{len(past_pairs)}件）", expanded=False):
            for hist_idx, (q_msg, a_msg) in enumerate(reversed(past_pairs)):
                st.markdown(
                    f"<p style='background:#1a3a5c; border-radius:10px; "
                    f"padding:10px 14px; color:#e0e0e0; font-size:14px;'>"
                    f"💬 {q_msg['content']}</p>",
                    unsafe_allow_html=True,
                )
                display_kb_response_with_images(
                    a_msg.get("content", ""), metadata, service,
                    key_suffix=f"_hist{hist_idx}",
                )
                st.markdown("---")


# ===========================================================================
# Git 自動 push（バックグラウンド）
# ===========================================================================
_AUTO_PUSH_INTERVAL = 60  # 秒
_auto_push_started = False


def _auto_push_loop():
    """バックグラウンドで定期的に git commit & push を実行する。"""
    repo_dir = str(Path(__file__).parent)
    target_files = ["app.py", "requirements.txt", ".gitignore"]

    while True:
        time.sleep(_AUTO_PUSH_INTERVAL)
        try:
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

            # git push
            subprocess.run(
                ["git", "push", "origin", "main"],
                cwd=repo_dir, capture_output=True, text=True, timeout=60,
            )
        except Exception:
            pass  # エラーが出ても静かに続行


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
    # chat_sessions
    if CHAT_SESSIONS_PATH.exists():
        try:
            with open(CHAT_SESSIONS_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if _write_json_to_sheet(sh, "chat_sessions", data):
                migrated.append("chat_sessions")
        except Exception as e:
            st.warning(f"chat_sessions移行失敗: {e}")
    # trash
    if TRASH_PATH.exists():
        try:
            with open(TRASH_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if _write_json_to_sheet(sh, "trash", data):
                migrated.append("trash")
        except Exception as e:
            st.warning(f"trash移行失敗: {e}")
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
        for ck in ["_cache_metadata", "_cache_folders", "_cache_chat_sessions", "_cache_trash", "_cache_weight_data"]:
            st.session_state.pop(ck, None)
            st.session_state.pop(f"{ck}_ts", None)
    else:
        st.warning("移行するローカルデータがありませんでした。")


# ===========================================================================
# 統合ページ: 📸 画像ライブラリ（画像管理 + 手動整理 + フォルダ表示 統合）
# ===========================================================================
def page_image_library():
    """画像ライブラリページ — 全画像の閲覧・検索・移動・削除を1つのページに統合。"""
    service = get_drive_service()
    folder_id = get_folder_id()
    api_key = get_gemini_api_key()
    metadata = load_metadata()
    folders = load_folders()

    images = list_all_images(service, folder_id, metadata, get_patient_folder_id())
    if not images:
        st.info(
            "画像が見つかりませんでした。\n\n"
            "Google Driveに画像を追加するか、チャット画面から画像を貼り付けて取り込んでください。"
        )
        return

    # --- サイドバー ---
    st.sidebar.header("🔍 検索・フィルタ")
    search_keyword = st.sidebar.text_input(
        "キーワード検索",
        placeholder="タイトル、要約、タグで検索...",
        key="lib_search",
    )

    # フォルダ選択（ラジオボタンスタイル）
    all_folders = get_all_folders_from_metadata(metadata)
    folder_options = ["すべて"] + all_folders
    selected_folder = st.sidebar.radio(
        "📂 フォルダ",
        folder_options,
        key="lib_folder_filter",
    )

    if st.sidebar.button("🔄 一覧を更新", key="lib_refresh"):
        list_images.clear()
        list_patient_images.clear()
        download_image.clear()
        st.rerun()

    # --- フィルタ適用 ---
    filtered_images = filter_images_by_keyword(images, search_keyword, metadata)
    if selected_folder != "すべて":
        filtered_images = [
            img for img in filtered_images
            if img["id"] in metadata and get_folder(metadata[img["id"]]) == selected_folder
        ]

    # --- サイドバー統計 ---
    st.sidebar.markdown("---")
    total = len(images)
    analyzed = sum(1 for img in images if img["id"] in metadata)
    reviewed_count = sum(
        1 for img in images
        if img["id"] in metadata
        and get_status(metadata[img["id"]]) == STATUS_REVIEWED
    )
    st.sidebar.caption(
        f"📊 全 {total} 件 | 解析済 {analyzed} 件 | ✅確認済み {reviewed_count} 件"
    )

    if not filtered_images:
        st.warning("検索条件に一致する画像がありません。")
        return

    # --- 選択中の画像ID（詳細表示用） ---
    if "lib_selected_id" not in st.session_state:
        st.session_state["lib_selected_id"] = None

    selected_fid = st.session_state["lib_selected_id"]

    # =======================================================================
    # 詳細表示モード（画像が選択されている場合）
    # =======================================================================
    if selected_fid is not None:
        selected_file = None
        for img in filtered_images:
            if img["id"] == selected_fid:
                selected_file = img
                break
        # フィルタ外の場合は全画像から探す
        if selected_file is None:
            for img in images:
                if img["id"] == selected_fid:
                    selected_file = img
                    break

        if selected_file is None:
            st.session_state["lib_selected_id"] = None
            st.rerun()
            return

        file_id = selected_file["id"]

        # 遷移元のページがあればそちらに戻る、なければ一覧に戻る
        back_tab = st.session_state.get("lib_back_tab")
        back_label = "⬅️ チャットに戻る" if back_tab == "💬 チャット" else "⬅️ 一覧に戻る"
        if st.button(back_label, key="lib_back_to_grid"):
            st.session_state["lib_selected_id"] = None
            st.session_state.pop("editing_file_id", None)
            if back_tab and back_tab != "📸 画像ライブラリ":
                st.session_state["active_tab"] = back_tab
                st.session_state.pop("lib_back_tab", None)
            st.rerun()

        # --- 画像読み込み ---
        image_bytes = None
        try:
            image_bytes = download_image(service, file_id)
        except Exception as e:
            st.error(f"画像の表示中にエラーが発生しました: {e}")
            return

        meta = metadata.get(file_id, {})

        # --- 横並びレイアウト ---
        col_img, col_info = st.columns([1, 1])
        with col_img:
            st.image(image_bytes, width="stretch")
        with col_info:
            title = meta.get("title", selected_file["name"])
            st.subheader(title)
            if is_patient_data(meta):
                st.markdown(
                    '<span style="background-color:#2e7d32; color:#c8e6c9; padding:3px 10px; '
                    'border-radius:12px; font-size:0.85em;">🏥 患者データ</span>',
                    unsafe_allow_html=True,
                )
            if file_id in metadata and not is_patient_data(meta):
                s = get_status(meta)
                if s == STATUS_REVIEWED:
                    st.success("✅ 確認済み")
                else:
                    st.warning("📝 未確認")
            _sl = get_summary_label(meta)
            summary_text = meta.get("summary", "")
            if summary_text:
                st.markdown(f"**{_sl}:**")
                render_summary(summary_text)
            elif is_patient_data(meta):
                st.info("検査所見が未入力です。編集から入力してください。")
            keywords = meta.get("keywords", [])
            if keywords:
                render_keyword_tags(keywords)
            # フォルダ表示
            cur_f = get_folder(meta)
            f_icon = "🏥" if cur_f == PATIENT_DATA_FOLDER else "📁"
            st.caption(f"{f_icon} {cur_f}")

        # --- 編集フォーム ---
        if file_id in metadata:
            _is_pd = is_patient_data(metadata[file_id])
            edit_label = "📝 検査所見を編集" if _is_pd else "📝 編集"
            with st.expander(edit_label, expanded=_is_pd):
                display_edit_form(file_id, metadata[file_id], metadata)
            if _is_pd:
                st.info("🏥 患者データ: AI解析は行いません。手動で検査所見を入力してください。")
            elif api_key:
                if st.button("🤖 AIで再解析する", key=f"lib_reanalyze_{file_id}"):
                    with st.spinner("Gemini で再解析中..."):
                        result = analyze_image_with_gemini(image_bytes, api_key)
                        if result:
                            old = metadata.get(file_id, {})
                            for keep_key in ("folder", "source"):
                                if keep_key in old:
                                    result[keep_key] = old[keep_key]
                            metadata[file_id] = result
                            save_metadata(metadata)
                            st.session_state.pop("editing_file_id", None)
                            st.success("再解析が完了しました！")
                            st.rerun()
        else:
            st.markdown("---")
            if api_key:
                st.info("この画像はまだAI解析されていません。")
                if st.button("🤖 AI解析を実行", key=f"lib_analyze_{file_id}", type="primary"):
                    with st.spinner("Gemini 2.0 Flash で解析中..."):
                        result = analyze_image_with_gemini(image_bytes, api_key)
                        if result:
                            old = metadata.get(file_id, {})
                            for keep_key in ("folder", "source"):
                                if keep_key in old:
                                    result[keep_key] = old[keep_key]
                            metadata[file_id] = result
                            save_metadata(metadata)
                            st.success("解析が完了しました！")
                            st.rerun()
        return

    # =======================================================================
    # グリッド一覧表示（デフォルト）
    # =======================================================================
    # フォルダ名 + 件数ヘッダー
    if selected_folder != "すべて":
        folder_icon = "🏥" if selected_folder == PATIENT_DATA_FOLDER else "📁"
        st.subheader(f"{folder_icon} {selected_folder}")
    else:
        st.subheader("📸 画像ライブラリ")

    # モード切替ボタン
    if "lib_mode" not in st.session_state:
        st.session_state["lib_mode"] = "browse"  # browse / delete / move

    mode_c1, mode_c2, mode_c3, mode_c4 = st.columns([1, 1, 1, 3])
    with mode_c1:
        if st.session_state["lib_mode"] != "browse":
            if st.button("✖ モード終了", key="lib_exit_mode", width="stretch"):
                st.session_state["lib_mode"] = "browse"
                # チェック状態クリア
                for img in filtered_images:
                    st.session_state.pop(f"lib_sel_{img['id']}", None)
                st.rerun()
    with mode_c2:
        if st.session_state["lib_mode"] != "delete":
            if st.button("🗑️ 削除モード", key="lib_enter_delete", width="stretch"):
                st.session_state["lib_mode"] = "delete"
                st.rerun()
    with mode_c3:
        if st.session_state["lib_mode"] != "move":
            if st.button("📂 移動モード", key="lib_enter_move", width="stretch"):
                st.session_state["lib_mode"] = "move"
                st.rerun()

    st.caption(f"{len(filtered_images)} 件")

    # 移動モード: 移動先フォルダ選択
    if st.session_state["lib_mode"] == "move":
        dest_folder = st.selectbox(
            "移動先フォルダ",
            folders,
            key="lib_dest_folder",
        )

    # 削除モード: 削除方法の選択
    if st.session_state["lib_mode"] == "delete":
        del_method = st.radio(
            "削除方法",
            ["🗑️ ゴミ箱に移動（再取り込み不可）", "🔄 メタデータのみ削除（再取り込み可能）"],
            key="lib_del_method",
            horizontal=True,
        )

    # 全選択/全解除（削除・移動モード時）
    if st.session_state["lib_mode"] in ("delete", "move"):
        _apply_batch_checkbox("_lib_sel_flag", [f"lib_sel_{img['id']}" for img in filtered_images if img["id"] in metadata])
        sel_c1, sel_c2, sel_c3 = st.columns([1, 1, 4])
        with sel_c1:
            if st.button("☑️ 全選択", key="lib_sel_all"):
                _set_batch_checkbox("_lib_sel_flag", True)
        with sel_c2:
            if st.button("☐ 全解除", key="lib_sel_none"):
                _set_batch_checkbox("_lib_sel_flag", False)

    # ページネーション
    page_items, cur_page, total_pages = _paginate(filtered_images, "lib_grid_page")
    _render_pagination_controls("lib_grid_page", cur_page, total_pages, len(filtered_images))

    # グリッド表示
    selected_ids = []
    cols_per_row = 4
    for row_start in range(0, len(page_items), cols_per_row):
        cols = st.columns(cols_per_row)
        for col_idx in range(cols_per_row):
            img_idx = row_start + col_idx
            if img_idx >= len(page_items):
                break
            img = page_items[img_idx]
            fid = img["id"]

            with cols[col_idx]:
                try:
                    thumb_bytes = download_image(service, fid)
                    st.image(thumb_bytes, width="stretch")
                except Exception:
                    st.markdown(
                        '<div style="background:#333;border-radius:8px;'
                        'height:80px;display:flex;align-items:center;'
                        'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                        unsafe_allow_html=True,
                    )

                if fid in metadata:
                    meta = metadata[fid]
                    title = meta.get("title", img["name"])
                    icon = get_status_icon(meta)
                    pd_badge = " 🏥" if is_patient_data(meta) else ""
                    cur_folder = get_folder(meta)
                    st.caption(f"{icon}{pd_badge} {title}")
                    if selected_folder == "すべて":
                        f_icon = "🏥" if cur_folder == PATIENT_DATA_FOLDER else "📁"
                        st.caption(f"{f_icon} {cur_folder}")
                else:
                    st.caption(f"📄 {img['name']}")

                if st.session_state["lib_mode"] == "browse":
                    if st.button("🔍 詳細を見る", key=f"lib_open_{fid}", width="stretch"):
                        st.session_state["lib_selected_id"] = fid
                        st.session_state.pop("lib_back_tab", None)
                        st.rerun()
                else:
                    # 削除/移動モード: チェックボックス
                    if fid in metadata:
                        action_label = "削除" if st.session_state["lib_mode"] == "delete" else "選択"
                        if st.checkbox(
                            action_label,
                            value=st.session_state.get(f"lib_sel_{fid}", False),
                            key=f"lib_sel_{fid}",
                        ):
                            selected_ids.append(fid)

    # --- アクションボタン ---
    if st.session_state["lib_mode"] == "delete":
        st.markdown("---")
        del_count = len(selected_ids)
        if del_method == "🗑️ ゴミ箱に移動（再取り込み不可）":
            if del_count > 0:
                st.warning(f"🗑️ **{del_count} 件**をゴミ箱に移動します。")
            if st.button(
                f"🗑️ 選択した {del_count} 件をゴミ箱へ",
                type="primary", key="lib_del_trash_run",
                disabled=(del_count == 0),
            ):
                moved = move_to_trash(selected_ids, metadata)
                for fid in selected_ids:
                    st.session_state.pop(f"lib_sel_{fid}", None)
                st.session_state["lib_mode"] = "browse"
                _invalidate_all_caches()
                st.success(f"✅ {moved} 件をゴミ箱に移動しました。")
                st.rerun()
        else:
            if del_count > 0:
                st.info(f"🔄 **{del_count} 件**のメタデータを削除します。")
            if st.button(
                f"🔄 選択した {del_count} 件のメタデータを削除",
                type="primary", key="lib_del_meta_run",
                disabled=(del_count == 0),
            ):
                removed = 0
                for fid in selected_ids:
                    if fid in metadata:
                        del metadata[fid]
                        removed += 1
                    st.session_state.pop(f"lib_sel_{fid}", None)
                remove_from_ignore_list(selected_ids)
                save_metadata(metadata)
                st.session_state["lib_mode"] = "browse"
                _invalidate_all_caches()
                st.success(f"✅ {removed} 件のメタデータを削除しました。")
                st.rerun()

    elif st.session_state["lib_mode"] == "move":
        st.markdown("---")
        move_count = len(selected_ids)
        if st.button(
            f"📁 選択した {move_count} 件を「{dest_folder}」に移動",
            type="primary", key="lib_move_run",
            disabled=(move_count == 0),
        ):
            for fid in selected_ids:
                if fid in metadata:
                    metadata[fid]["folder"] = dest_folder
            save_metadata(metadata)
            for fid in selected_ids:
                st.session_state.pop(f"lib_sel_{fid}", None)
            st.session_state["lib_mode"] = "browse"
            _invalidate_all_caches()
            st.success(f"✅ {move_count} 件を「{dest_folder}」に移動しました。")
            st.rerun()


# ---------------------------------------------------------------------------
# ヘルパー: 患者データのタイトル一括保存
# ---------------------------------------------------------------------------
def _save_all_patient_titles(patient_data_images: list, metadata: dict) -> int:
    """session_state の pd_title_{fid} からタイトルを読み取り metadata に保存。

    変更があった件数を返す。
    """
    changed = 0
    for img in patient_data_images:
        fid = img["id"]
        key = f"pd_title_{fid}"
        if key in st.session_state:
            new_title = st.session_state[key].strip()
            m = metadata.get(fid, {})
            old_title = m.get("title", img.get("name", ""))
            if new_title and new_title != old_title:
                if fid not in metadata:
                    metadata[fid] = {}
                metadata[fid]["title"] = new_title
                changed += 1
    return changed


# ===========================================================================
# 統合ページ: ⚡ 取り込み・解析（一括解析 + AI整理の分類 + 患者データ 統合）
# ===========================================================================
def page_import_analyze():
    """取り込み・解析ページ — 3つのサブタブで構成。"""
    service = get_drive_service()
    folder_id = get_folder_id()
    api_key = get_gemini_api_key()
    metadata = load_metadata()

    _ensure_patient_data_folder(metadata)

    images = list_all_images(service, folder_id, metadata, get_patient_folder_id())
    if not images:
        st.info("フォルダ内に画像が見つかりませんでした。")
        return

    if not api_key:
        st.warning(
            "この機能を使用するには `GOOGLE_API_KEY` を "
            "`.streamlit/secrets.toml` に設定してください。"
        )
        return

    # --- 画像分類 ---
    unanalyzed = [
        img for img in images
        if img["id"] not in metadata
        and not is_patient_data(metadata.get(img["id"], {}))
    ]
    unreviewed = [
        img for img in images
        if img["id"] in metadata
        and not is_patient_data(metadata[img["id"]])
        and get_status(metadata[img["id"]]) == STATUS_AUTO
    ]
    reviewed = [
        img for img in images
        if img["id"] in metadata
        and not is_patient_data(metadata[img["id"]])
        and get_status(metadata[img["id"]]) == STATUS_REVIEWED
    ]
    analyzed_all = [
        img for img in images
        if img["id"] in metadata
        and not is_patient_data(metadata[img["id"]])
    ]
    patient_data_images = [
        img for img in images
        if img["id"] in metadata
        and is_patient_data(metadata[img["id"]])
    ]

    # --- サイドバー: 統計 ---
    st.sidebar.header("📊 処理状況")
    st.sidebar.write(f"📄 未解析: **{len(unanalyzed)}** 件")
    st.sidebar.write(f"📝 未確認: **{len(unreviewed)}** 件")
    st.sidebar.write(f"✅ 確認済み: **{len(reviewed)}** 件")
    if patient_data_images:
        st.sidebar.write(f"🏥 患者データ: **{len(patient_data_images)}** 件")
    st.sidebar.write(f"合計: **{len(images)}** 件")
    if images:
        done_count = len(reviewed)
        progress = done_count / len(images)
        st.sidebar.progress(progress, text=f"確認済み: {done_count}/{len(images)}")

    # --- 3つのサブタブ ---
    sub_tab1, sub_tab2, sub_tab3 = st.tabs([
        "📥 新規取り込み", "🏥 患者データ", "🔧 詳細操作"
    ])

    # =======================================================================
    # サブタブ1: 📥 新規取り込み
    # =======================================================================
    with sub_tab1:
        st.subheader("📥 新規取り込み")

        # 処理状況サマリー
        sum_c1, sum_c2, sum_c3 = st.columns(3)
        with sum_c1:
            st.metric("未解析", f"{len(unanalyzed)} 件")
        with sum_c2:
            st.metric("未確認", f"{len(unreviewed)} 件")
        with sum_c3:
            st.metric("確認済み", f"{len(reviewed)} 件")

        st.markdown("---")

        # スキャン＆解析
        if not unanalyzed:
            st.success("すべての画像が解析済みです ✅")
        else:
            st.info(f"**{len(unanalyzed)} 件**の未解析画像があります。")

            _apply_batch_checkbox("_imp_sel_flag", [f"imp_sel_{img['id']}" for img in unanalyzed])
            sel_col1, sel_col2, sel_col3 = st.columns([1, 1, 3])
            with sel_col1:
                if st.button("☑️ 全選択", key="imp_sel_all"):
                    _set_batch_checkbox("_imp_sel_flag", True)
            with sel_col2:
                if st.button("☐ 全解除", key="imp_desel_all"):
                    _set_batch_checkbox("_imp_sel_flag", False)

            batch_page_items, batch_cur, batch_total_pages = _paginate(unanalyzed, "imp_new_page")
            _render_pagination_controls("imp_new_page", batch_cur, batch_total_pages, len(unanalyzed))

            selected_ids = []
            cols_per_row = 4
            for row_start in range(0, len(batch_page_items), cols_per_row):
                cols = st.columns(cols_per_row)
                for col_idx in range(cols_per_row):
                    img_idx = row_start + col_idx
                    if img_idx >= len(batch_page_items):
                        break
                    img = batch_page_items[img_idx]
                    fid = img["id"]
                    with cols[col_idx]:
                        try:
                            thumb_bytes = download_image(service, fid)
                            st.image(thumb_bytes, width="stretch")
                        except Exception:
                            st.markdown(
                                '<div style="background:#333;border-radius:8px;'
                                'height:80px;display:flex;align-items:center;'
                                'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                                unsafe_allow_html=True,
                            )
                        st.caption(f"📄 {img['name']}")
                        if st.checkbox("解析する", value=st.session_state.get(f"imp_sel_{fid}", False), key=f"imp_sel_{fid}"):
                            selected_ids.append(fid)

            st.markdown("---")
            selected_count = len(selected_ids)
            if st.button(
                f"🤖 選択した {selected_count} 件を解析",
                type="primary", key="imp_run",
                disabled=(selected_count == 0),
            ):
                target = [img for img in unanalyzed if img["id"] in selected_ids]
                _run_batch_analyze(service, target, metadata, api_key)

    # =======================================================================
    # サブタブ2: 🏥 患者データ
    # =======================================================================
    with sub_tab2:
        st.subheader(f"🏥 患者データ管理（{len(patient_data_images)} 件）")

        # --- 成功メッセージ表示 ---
        if st.session_state.get("_pd_save_success"):
            st.success(st.session_state["_pd_save_success"])
            del st.session_state["_pd_save_success"]

        if not patient_data_images:
            st.info("🏥 患者データはまだ取り込まれていません。")
        else:
            # --- 選択ヘルパーボタン ---
            _pd_sel_keys = [f"pd_sel_{img['id']}" for img in patient_data_images]
            _apply_batch_checkbox("_pd_sel_flag", _pd_sel_keys)

            sel_c1, sel_c2, sel_c3, sel_c4 = st.columns([1, 1, 1.5, 3.5])
            with sel_c1:
                if st.button("☑️ 全選択", key="pd_sel_all"):
                    _set_batch_checkbox("_pd_sel_flag", True)
            with sel_c2:
                if st.button("☐ 全解除", key="pd_desel_all"):
                    _set_batch_checkbox("_pd_sel_flag", False)
            with sel_c3:
                no_kw_imgs = [
                    img for img in patient_data_images
                    if not metadata.get(img["id"], {}).get("keywords")
                ]
                if st.button(f"🏷️ タグなし({len(no_kw_imgs)})", key="pd_sel_no_kw"):
                    batch_map = {}
                    for img in patient_data_images:
                        has_kw = bool(metadata.get(img["id"], {}).get("keywords"))
                        batch_map[f"pd_sel_{img['id']}"] = not has_kw
                    _set_batch_checkbox("_pd_sel_flag", batch_map)

            # --- サムネイルグリッド（4列 × 2行 = 8件/ページ） ---
            pd_page_items, pd_cur, pd_total_pages = _paginate(
                patient_data_images, "pd_grid_page", per_page=8
            )
            _render_pagination_controls(
                "pd_grid_page", pd_cur, pd_total_pages, len(patient_data_images)
            )

            cols_per_row = 4
            for row_start in range(0, len(pd_page_items), cols_per_row):
                cols = st.columns(cols_per_row)
                for col_idx in range(cols_per_row):
                    img_idx = row_start + col_idx
                    if img_idx >= len(pd_page_items):
                        break
                    img = pd_page_items[img_idx]
                    fid = img["id"]
                    m = metadata.get(fid, {})
                    fname = img.get("name", fid)
                    current_title = m.get("title", fname)
                    kws = m.get("keywords", [])

                    with cols[col_idx]:
                        # サムネイル
                        try:
                            thumb = download_image(service, fid)
                            st.image(thumb, width="stretch")
                        except Exception:
                            st.markdown(
                                '<div style="background:#333;border-radius:8px;'
                                'height:80px;display:flex;align-items:center;'
                                'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                                unsafe_allow_html=True,
                            )
                        # AI解析チェックボックス — session_state にデフォルト設定
                        if f"pd_sel_{fid}" not in st.session_state:
                            st.session_state[f"pd_sel_{fid}"] = False
                        st.checkbox("AI解析", key=f"pd_sel_{fid}")
                        # タイトル入力 — session_state にデフォルト設定
                        if f"pd_title_{fid}" not in st.session_state:
                            st.session_state[f"pd_title_{fid}"] = current_title
                        st.text_input(
                            "タイトル",
                            key=f"pd_title_{fid}",
                            label_visibility="collapsed",
                            placeholder="タイトルを入力",
                        )
                        # キーワード表示
                        if kws:
                            st.caption(f"🏷️ {', '.join(kws[:4])}")
                        else:
                            st.caption("🏷️ ---")

            st.markdown("---")

            # --- アクションボタン ---
            selected_count = sum(
                1 for img in patient_data_images
                if st.session_state.get(f"pd_sel_{img['id']}", False)
            )
            btn_c1, btn_c2 = st.columns(2)
            with btn_c1:
                if st.button("💾 タイトルを一括保存", key="pd_save_titles",
                             use_container_width=True):
                    saved = _save_all_patient_titles(patient_data_images, metadata)
                    if saved > 0:
                        save_metadata(metadata)
                        _invalidate_all_caches()
                        # session_state のタイトルキーをクリア（再読み込みのため）
                        for img in patient_data_images:
                            st.session_state.pop(f"pd_title_{img['id']}", None)
                        st.session_state["_pd_save_success"] = (
                            f"✅ {saved} 件のタイトルを保存しました"
                        )
                        st.rerun()
                    else:
                        st.info("変更されたタイトルはありません。")

            with btn_c2:
                if st.button(
                    f"💾 保存 & 🤖 AI一括タグ付け（{selected_count} 件）",
                    key="pd_save_and_ai", type="primary",
                    use_container_width=True,
                    disabled=(selected_count == 0),
                ):
                    # まずタイトルを保存
                    title_saved = _save_all_patient_titles(patient_data_images, metadata)

                    # 選択された画像のAIキーワード生成
                    target_imgs = [
                        img for img in patient_data_images
                        if st.session_state.get(f"pd_sel_{img['id']}", False)
                    ]
                    if not api_key:
                        st.warning("Gemini API キーが必要です。")
                    elif not target_imgs:
                        st.info("AI解析する画像が選択されていません。")
                    else:
                        progress_bar = st.progress(0, text="🤖 AIタグ付け中...")
                        generated = 0
                        for i, img in enumerate(target_imgs):
                            fid = img["id"]
                            m = metadata.get(fid, {})
                            progress_bar.progress(
                                (i + 1) / len(target_imgs),
                                text=f"🤖 {i + 1}/{len(target_imgs)}: {m.get('title', img.get('name', '')[:20])}...",
                            )
                            try:
                                ib = download_image(service, fid)
                                kws = generate_keywords_with_gemini(
                                    ib, api_key, title=m.get("title", ""),
                                )
                                if kws:
                                    if fid not in metadata:
                                        metadata[fid] = {}
                                    metadata[fid]["keywords"] = kws
                                    generated += 1
                            except Exception:
                                pass
                        progress_bar.empty()

                        if title_saved > 0 or generated > 0:
                            save_metadata(metadata)
                            _invalidate_all_caches()
                            # session_state クリーンアップ
                            for img in patient_data_images:
                                st.session_state.pop(f"pd_title_{img['id']}", None)
                                st.session_state.pop(f"pd_sel_{img['id']}", None)
                            parts = []
                            if title_saved > 0:
                                parts.append(f"タイトル {title_saved} 件保存")
                            if generated > 0:
                                parts.append(f"AIタグ {generated} 件生成")
                            st.session_state["_pd_save_success"] = f"✅ {' / '.join(parts)}"
                            st.rerun()
                        else:
                            st.warning("変更やキーワード生成がありませんでした。")

            # --- 個別の検査所見を編集 ---
            with st.expander("📝 個別の検査所見を編集", expanded=False):
                if not patient_data_images:
                    st.info("患者データがありません。")
                else:
                    # ドロップダウンで画像を選択
                    pd_options = []
                    for i, img in enumerate(patient_data_images):
                        m = metadata.get(img["id"], {})
                        title = m.get("title", img.get("name", img["id"]))
                        kw_tag = " 🏷️" if m.get("keywords") else ""
                        pd_options.append(f"{i + 1}. {title}{kw_tag}")

                    selected_idx = st.selectbox(
                        "画像を選択",
                        range(len(pd_options)),
                        format_func=lambda i: pd_options[i],
                        key="pd_detail_select",
                    )
                    sel_img = patient_data_images[selected_idx]
                    sel_fid = sel_img["id"]
                    sel_meta = metadata.get(sel_fid, {})
                    sel_fname = sel_img.get("name", sel_fid)

                    detail_col_img, detail_col_form = st.columns([1, 2])
                    with detail_col_img:
                        try:
                            detail_bytes = download_image(service, sel_fid)
                            st.image(detail_bytes, width="stretch")
                        except Exception:
                            st.caption("（画像を読み込めません）")

                    with detail_col_form:
                        with st.form(key=f"pd_detail_edit_{sel_fid}"):
                            new_title = st.text_input(
                                "📌 タイトル",
                                value=sel_meta.get("title", sel_fname),
                                key=f"pd_det_title_{sel_fid}",
                            )
                            new_summary = st.text_area(
                                "📝 検査所見（任意）",
                                value=sel_meta.get("summary", ""),
                                height=80,
                                placeholder="所見があれば入力（空欄でもOK）",
                                key=f"pd_det_summary_{sel_fid}",
                            )
                            new_keywords = st.text_input(
                                "🏷️ キーワード（カンマ区切り）",
                                value=", ".join(sel_meta.get("keywords", [])),
                                key=f"pd_det_kw_{sel_fid}",
                            )
                            submitted = st.form_submit_button(
                                "💾 保存", type="primary", use_container_width=True,
                            )
                            if submitted:
                                kw_list = [
                                    k.strip()
                                    for k in new_keywords.replace("、", ",").split(",")
                                    if k.strip()
                                ]
                                if sel_fid not in metadata:
                                    metadata[sel_fid] = {}
                                metadata[sel_fid]["title"] = new_title
                                metadata[sel_fid]["summary"] = new_summary
                                metadata[sel_fid]["keywords"] = kw_list
                                metadata[sel_fid]["status"] = STATUS_REVIEWED
                                save_metadata(metadata)
                                _invalidate_all_caches()
                                st.session_state["_pd_save_success"] = (
                                    f"✅ 「{new_title}」を保存しました"
                                )
                                st.rerun()

    # =======================================================================
    # サブタブ3: 🔧 詳細操作
    # =======================================================================
    with sub_tab3:
        st.subheader("🔧 詳細操作")

        adv_mode = st.selectbox(
            "操作を選択",
            ["一括再解析", "指示付き再解析", "AI自動フォルダ分類",
             "レビュー（1枚ずつ確認）", "一括レビュー済みに変更"],
            key="imp_adv_mode",
        )

        st.markdown("---")

        # --- 一括再解析 ---
        if adv_mode == "一括再解析":
            st.caption("プロンプト改善後などに、解析済みの画像をまとめて再解析できます。")
            if not analyzed_all:
                st.info("解析済みの画像がありません。")
            else:
                filter_choice = st.radio(
                    "対象を絞る",
                    ["すべて", "未確認のみ（📝）", "確認済みのみ（✅）"],
                    horizontal=True, key="imp_reanalyze_filter",
                )
                if filter_choice == "未確認のみ（📝）":
                    target_list = unreviewed
                elif filter_choice == "確認済みのみ（✅）":
                    target_list = reviewed
                else:
                    target_list = analyzed_all

                if not target_list:
                    st.info("該当する画像がありません。")
                else:
                    st.info(f"**{len(target_list)} 件**が対象です。")
                    _apply_batch_checkbox("_imp_ra_sel_flag", [f"imp_ra_sel_{img['id']}" for img in target_list])
                    rc1, rc2, rc3 = st.columns([1, 1, 3])
                    with rc1:
                        if st.button("☑️ 全選択", key="imp_ra_sel_all"):
                            _set_batch_checkbox("_imp_ra_sel_flag", True)
                    with rc2:
                        if st.button("☐ 全解除", key="imp_ra_sel_none"):
                            _set_batch_checkbox("_imp_ra_sel_flag", False)

                    ra_page_items, ra_cur, ra_total_pages = _paginate(target_list, "imp_reanalyze_page")
                    _render_pagination_controls("imp_reanalyze_page", ra_cur, ra_total_pages, len(target_list))

                    reanalyze_ids = []
                    cols_per_row = 4
                    for row_start in range(0, len(ra_page_items), cols_per_row):
                        cols = st.columns(cols_per_row)
                        for col_idx in range(cols_per_row):
                            img_idx = row_start + col_idx
                            if img_idx >= len(ra_page_items):
                                break
                            img = ra_page_items[img_idx]
                            fid = img["id"]
                            meta = metadata[fid]
                            title = meta.get("title", img["name"])
                            status_icon = get_status_icon(meta)
                            with cols[col_idx]:
                                try:
                                    thumb_bytes = download_image(service, fid)
                                    st.image(thumb_bytes, width="stretch")
                                except Exception:
                                    st.markdown(
                                        '<div style="background:#333;border-radius:8px;'
                                        'height:80px;display:flex;align-items:center;'
                                        'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                                        unsafe_allow_html=True,
                                    )
                                st.caption(f"{status_icon} {title}")
                                if st.checkbox("再解析", value=st.session_state.get(f"imp_ra_sel_{fid}", True), key=f"imp_ra_sel_{fid}"):
                                    reanalyze_ids.append(fid)

                    st.markdown("---")
                    reanalyze_count = len(reanalyze_ids)
                    if reanalyze_count > 0:
                        st.warning("⚠️ 再解析すると現在の解析データが上書きされます。")
                    if st.button(
                        f"🔄 選択した {reanalyze_count} 件を再解析",
                        type="primary", key="imp_reanalyze_run",
                        disabled=(reanalyze_count == 0),
                    ):
                        target = [img for img in target_list if img["id"] in reanalyze_ids]
                        _run_batch_analyze(service, target, metadata, api_key, is_reanalyze=True)

        # --- 指示付き再解析 ---
        elif adv_mode == "指示付き再解析":
            st.caption("修正指示を入力してまとめて再解析できます。")
            if not analyzed_all:
                st.info("解析済みの画像がありません。")
            else:
                hint_filter = st.radio(
                    "対象を絞る",
                    ["すべて", "未確認のみ（📝）", "確認済みのみ（✅）"],
                    horizontal=True, key="imp_hint_filter",
                )
                if hint_filter == "未確認のみ（📝）":
                    hint_target_list = unreviewed
                elif hint_filter == "確認済みのみ（✅）":
                    hint_target_list = reviewed
                else:
                    hint_target_list = analyzed_all

                if not hint_target_list:
                    st.info("該当する画像がありません。")
                else:
                    st.info(f"**{len(hint_target_list)} 件**が対象です。")
                    _apply_batch_checkbox("_imp_hint_sel_flag", [f"imp_hint_sel_{img['id']}" for img in hint_target_list])
                    hc1, hc2, hc3 = st.columns([1, 1, 3])
                    with hc1:
                        if st.button("☑️ 全選択", key="imp_hint_sel_all"):
                            _set_batch_checkbox("_imp_hint_sel_flag", True)
                    with hc2:
                        if st.button("☐ 全解除", key="imp_hint_sel_none"):
                            _set_batch_checkbox("_imp_hint_sel_flag", False)

                    hint_page_items, hint_cur, hint_total_pages = _paginate(hint_target_list, "imp_hint_page")
                    _render_pagination_controls("imp_hint_page", hint_cur, hint_total_pages, len(hint_target_list))

                    hint_ids = []
                    cols_per_row = 4
                    for row_start in range(0, len(hint_page_items), cols_per_row):
                        cols = st.columns(cols_per_row)
                        for col_idx in range(cols_per_row):
                            img_idx = row_start + col_idx
                            if img_idx >= len(hint_page_items):
                                break
                            img = hint_page_items[img_idx]
                            fid = img["id"]
                            meta = metadata[fid]
                            title = meta.get("title", img["name"])
                            status_icon = get_status_icon(meta)
                            kw = meta.get("keywords", [])
                            with cols[col_idx]:
                                try:
                                    thumb_bytes = download_image(service, fid)
                                    st.image(thumb_bytes, width="stretch")
                                except Exception:
                                    st.markdown(
                                        '<div style="background:#333;border-radius:8px;'
                                        'height:80px;display:flex;align-items:center;'
                                        'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                                        unsafe_allow_html=True,
                                    )
                                st.caption(f"{status_icon} {title}")
                                if kw:
                                    st.caption(" ".join(f"`{k}`" for k in kw[:5]))
                                if st.checkbox(
                                    "修正する",
                                    value=st.session_state.get(f"imp_hint_sel_{fid}", False),
                                    key=f"imp_hint_sel_{fid}",
                                ):
                                    hint_ids.append(fid)

                    st.markdown("---")
                    correction_hint = st.text_area(
                        "🔧 修正指示（選択した全画像に共通で適用）",
                        placeholder="例:\n・「骨折」ではなく「ストレス骨折」が正しいです\n・キーワードに「シンスプリント」を追加してください",
                        height=120, key="imp_correction_hint",
                    )
                    hint_count = len(hint_ids)
                    if hint_count > 0 and not correction_hint.strip():
                        st.warning("⚠️ 修正指示を入力してください。")
                    can_run = hint_count > 0 and bool(correction_hint.strip())
                    if st.button(
                        f"🤖 選択した {hint_count} 件を指示付きで再解析",
                        type="primary", key="imp_hint_run",
                        disabled=(not can_run),
                    ):
                        target = [img for img in hint_target_list if img["id"] in hint_ids]
                        _run_batch_analyze(
                            service, target, metadata, api_key,
                            is_reanalyze=True, correction_hint=correction_hint,
                        )

        # --- AI自動フォルダ分類 ---
        elif adv_mode == "AI自動フォルダ分類":
            folders = load_folders()
            analyzed = [img for img in images if img["id"] in metadata]
            if not analyzed:
                st.info("解析済みの画像がありません。先に画像をAI解析してください。")
            else:
                # 整理方針
                st.markdown("#### 📝 整理方針")
                st.caption("AIにどのような観点で整理してほしいかを指示できます。空欄の場合はAIが自動判断します。")
                user_instruction = st.text_area(
                    "整理の指示（任意）",
                    value=st.session_state.get("imp_ai_folder_instruction", ""),
                    placeholder="例:\n・解剖学的部位で分けて\n・疾患カテゴリで分類して",
                    height=100, key="imp_ai_folder_instruction",
                )

                st.markdown("---")
                st.markdown("#### ① フォルダ設定")
                mode = st.radio(
                    "フォルダの決め方",
                    ["既存フォルダを使う", "AIに新しいフォルダを提案させる"],
                    key="imp_ai_folder_mode", horizontal=True,
                )

                if mode == "AIに新しいフォルダを提案させる":
                    if st.button("🤖 フォルダ名を提案", key="imp_ai_suggest"):
                        with st.spinner("AIがフォルダ構成を考えています..."):
                            try:
                                summaries = []
                                for img in analyzed:
                                    meta = metadata[img["id"]]
                                    t = meta.get("title", "")
                                    kw = ", ".join(meta.get("keywords", []))
                                    summaries.append(f"- {t} [{kw}]")
                                instruction_part = ""
                                if user_instruction.strip():
                                    instruction_part = (
                                        f"\n\n【ユーザーからの整理方針】\n{user_instruction.strip()}\n"
                                        "上記の方針に従ってフォルダ名を提案してください。"
                                    )
                                else:
                                    instruction_part = "\n解剖学的部位、疾患カテゴリ、画像モダリティなどで分類してください。"
                                prompt = (
                                    "以下は医療画像の解析データ一覧です。\n"
                                    + "\n".join(summaries)
                                    + f"\n\nこれらを整理するための最適なフォルダ名を5〜10個提案してください。"
                                    + instruction_part
                                    + "\nフォルダ名のみをカンマ区切りで出力してください。日本語で。"
                                )
                                resp_text = _gemini_generate(api_key, [{"text": prompt}])
                                suggested = [s.strip() for s in resp_text.strip().split(",") if s.strip()]
                                st.session_state["imp_ai_suggested_folders"] = suggested
                            except Exception as e:
                                st.error(f"フォルダ提案に失敗しました: {e}")

                    if "imp_ai_suggested_folders" in st.session_state:
                        suggested = st.session_state["imp_ai_suggested_folders"]
                        st.markdown("**AIの提案（編集できます）:**")
                        edited_folders = []
                        remove_idx = None
                        for i, fname in enumerate(suggested):
                            ec1, ec2 = st.columns([5, 1])
                            with ec1:
                                edited = st.text_input(
                                    f"フォルダ {i + 1}", value=fname,
                                    key=f"imp_ai_edit_folder_{i}", label_visibility="collapsed",
                                )
                            with ec2:
                                if st.button("✖", key=f"imp_ai_remove_folder_{i}"):
                                    remove_idx = i
                            if edited.strip():
                                edited_folders.append(edited.strip())

                        if remove_idx is not None:
                            new_suggested = []
                            for i in range(len(suggested)):
                                val = st.session_state.get(f"imp_ai_edit_folder_{i}", suggested[i]).strip()
                                if i != remove_idx and val:
                                    new_suggested.append(val)
                            for i in range(len(suggested)):
                                st.session_state.pop(f"imp_ai_edit_folder_{i}", None)
                            st.session_state["imp_ai_suggested_folders"] = new_suggested
                            st.rerun()

                        ac1, ac2 = st.columns([5, 1])
                        with ac1:
                            new_name = st.text_input(
                                "追加するフォルダ名", placeholder="フォルダ名を入力…",
                                key="imp_ai_add_folder_input", label_visibility="collapsed",
                            )
                        with ac2:
                            if st.button("➕", key="imp_ai_add_folder_btn") and new_name.strip():
                                new_suggested = []
                                for i in range(len(suggested)):
                                    val = st.session_state.get(f"imp_ai_edit_folder_{i}", suggested[i]).strip()
                                    if val:
                                        new_suggested.append(val)
                                new_suggested.append(new_name.strip())
                                for i in range(len(suggested)):
                                    st.session_state.pop(f"imp_ai_edit_folder_{i}", None)
                                st.session_state["imp_ai_suggested_folders"] = new_suggested
                                st.rerun()

                        if st.button("✅ これらのフォルダを作成して使用", key="imp_ai_create_suggested"):
                            for f in edited_folders:
                                if f not in folders:
                                    folders.append(f)
                            save_folders(folders)
                            for i in range(len(suggested)):
                                st.session_state.pop(f"imp_ai_edit_folder_{i}", None)
                            st.success(f"フォルダを作成しました！（{len(edited_folders)} 件）")
                            st.session_state.pop("imp_ai_suggested_folders", None)
                            st.rerun()

                folders = load_folders()
                st.markdown("**現在のフォルダ:**")
                st.write(" / ".join(f"📁 {f}" for f in folders))

                st.markdown("---")
                st.markdown("#### ② AI自動分類を実行")
                target_choice = st.radio(
                    "分類対象",
                    ["未分類の画像のみ", "すべての画像（再分類）"],
                    key="imp_ai_target", horizontal=True,
                )
                if target_choice == "未分類の画像のみ":
                    targets = [img for img in analyzed if get_folder(metadata[img["id"]]) == DEFAULT_FOLDER]
                else:
                    targets = analyzed

                st.write(f"対象: **{len(targets)}** 件")
                if not targets:
                    st.success("分類対象の画像がありません。")
                elif st.button(
                    f"🤖 {len(targets)} 件をAIで自動分類",
                    type="primary", key="imp_ai_classify_run",
                ):
                    folder_names = ", ".join(folders)
                    progress_bar = st.progress(0, text="AI分類を開始...")
                    classified = 0
                    errors = 0
                    for i, img in enumerate(targets):
                        fid = img["id"]
                        meta = metadata[fid]
                        title = meta.get("title", "")
                        summary = meta.get("summary", "")
                        keywords = ", ".join(meta.get("keywords", []))
                        progress_bar.progress(i / len(targets), text=f"分類中... ({i + 1}/{len(targets)}) {title}")

                        instruction_hint = ""
                        if user_instruction.strip():
                            instruction_hint = (
                                f"\n【整理方針】{user_instruction.strip()}\n"
                                "上記の方針を考慮して最適なフォルダを選んでください。\n"
                            )
                        prompt = (
                            f"以下の医療画像を最も適切なフォルダに分類してください。\n\n"
                            f"タイトル: {title}\n要約: {summary}\nキーワード: {keywords}\n\n"
                            f"選択肢: {folder_names}\n{instruction_hint}\n"
                            f"必ず上記の選択肢の中から1つだけ選び、フォルダ名のみを出力してください。"
                        )
                        try:
                            result = _gemini_generate(api_key, [{"text": prompt}]).strip()
                            matched = None
                            for f in folders:
                                if f in result or result in f:
                                    matched = f
                                    break
                            if matched is None:
                                matched = DEFAULT_FOLDER
                            metadata[fid]["folder"] = matched
                            classified += 1
                        except Exception:
                            errors += 1
                        if i < len(targets) - 1:
                            time.sleep(0.5)

                    save_metadata(metadata)
                    progress_bar.progress(1.0, text="完了！")
                    st.success(f"✅ 分類完了！ 成功: {classified} 件 / 失敗: {errors} 件")
                    st.rerun()

        # --- レビュー ---
        elif adv_mode == "レビュー（1枚ずつ確認）":
            metadata = load_metadata()
            unreviewed_now = [
                img for img in images
                if img["id"] in metadata
                and get_status(metadata[img["id"]]) == STATUS_AUTO
            ]
            if not unreviewed_now:
                if reviewed:
                    st.success("すべての画像がレビュー済みです 🎉")
                else:
                    st.info("まず「新規取り込み」で一括AI解析を実行してください。")
            else:
                st.info(f"**{len(unreviewed_now)} 件**の未確認画像があります。")
                if "imp_review_index" not in st.session_state:
                    st.session_state["imp_review_index"] = 0
                if st.session_state["imp_review_index"] >= len(unreviewed_now):
                    st.session_state["imp_review_index"] = 0

                current_idx = st.session_state["imp_review_index"]
                current_img = unreviewed_now[current_idx]
                current_fid = current_img["id"]
                current_meta = metadata[current_fid]

                nav_col1, nav_col2, nav_col3 = st.columns([1, 2, 1])
                with nav_col1:
                    if st.button("⬅️ 前へ", disabled=(current_idx == 0), key="imp_rev_prev"):
                        st.session_state["imp_review_index"] = current_idx - 1
                        st.session_state.pop("editing_file_id", None)
                        st.rerun()
                with nav_col2:
                    st.write(f"**{current_idx + 1} / {len(unreviewed_now)}** 件目")
                with nav_col3:
                    if st.button("次へ ➡️", disabled=(current_idx >= len(unreviewed_now) - 1), key="imp_rev_next"):
                        st.session_state["imp_review_index"] = current_idx + 1
                        st.session_state.pop("editing_file_id", None)
                        st.rerun()

                st.markdown("---")
                try:
                    image_bytes = download_image(service, current_fid)
                except Exception as e:
                    st.error(f"画像の読み込みに失敗: {e}")
                    return

                rev_col_img, rev_col_info = st.columns([1, 1])
                with rev_col_img:
                    st.image(image_bytes, width="stretch")
                with rev_col_info:
                    title = current_meta.get("title", current_img.get("name", "不明"))
                    st.subheader(title)
                    render_summary(current_meta.get("summary", ""))
                    keywords = current_meta.get("keywords", [])
                    if keywords:
                        render_keyword_tags(keywords)

                display_edit_form(current_fid, current_meta, metadata)

                st.markdown("---")
                if st.button("⏭️ スキップして次へ", key="imp_rev_skip"):
                    if current_idx < len(unreviewed_now) - 1:
                        st.session_state["imp_review_index"] = current_idx + 1
                    else:
                        st.session_state["imp_review_index"] = 0
                    st.session_state.pop("editing_file_id", None)
                    st.rerun()

        # --- 一括レビュー済みに変更 ---
        elif adv_mode == "一括レビュー済みに変更":
            st.caption("未確認の画像をまとめて確認済みに変更、または確認済みを未確認に戻せます。")
            metadata = load_metadata()
            review_filter = st.radio(
                "対象",
                ["未確認→確認済み（📝→✅）", "確認済み→未確認に戻す（✅→📝）"],
                horizontal=True, key="imp_bulk_review_filter",
            )
            if review_filter == "未確認→確認済み（📝→✅）":
                target_list = [
                    img for img in images
                    if img["id"] in metadata and get_status(metadata[img["id"]]) == STATUS_AUTO
                ]
                action_label = "確認済みにする"
                action_key_prefix = "imp_bulkrev"
            else:
                target_list = [
                    img for img in images
                    if img["id"] in metadata and get_status(metadata[img["id"]]) == STATUS_REVIEWED
                ]
                action_label = "未確認に戻す"
                action_key_prefix = "imp_bulkunrev"

            if not target_list:
                st.success("該当する画像がありません。")
            else:
                st.info(f"**{len(target_list)} 件**が対象です。")
                bc1, bc2, bc3 = st.columns([1, 1, 3])
                with bc1:
                    if st.button("☑️ 全選択", key=f"{action_key_prefix}_sel_all"):
                        for img in target_list:
                            st.session_state[f"{action_key_prefix}_{img['id']}"] = True
                        st.rerun()
                with bc2:
                    if st.button("☐ 全解除", key=f"{action_key_prefix}_sel_none"):
                        for img in target_list:
                            st.session_state[f"{action_key_prefix}_{img['id']}"] = False
                        st.rerun()

                br_page_items, br_cur, br_total_pages = _paginate(target_list, "imp_bulkreview_page")
                _render_pagination_controls("imp_bulkreview_page", br_cur, br_total_pages, len(target_list))

                action_ids = []
                cols_per_row = 4
                for row_start in range(0, len(br_page_items), cols_per_row):
                    cols = st.columns(cols_per_row)
                    for col_idx in range(cols_per_row):
                        img_idx = row_start + col_idx
                        if img_idx >= len(br_page_items):
                            break
                        img = br_page_items[img_idx]
                        fid = img["id"]
                        meta = metadata[fid]
                        title = meta.get("title", img["name"])
                        status_icon = get_status_icon(meta)
                        with cols[col_idx]:
                            try:
                                thumb_bytes = download_image(service, fid)
                                st.image(thumb_bytes, width="stretch")
                            except Exception:
                                st.markdown(
                                    '<div style="background:#333;border-radius:8px;'
                                    'height:80px;display:flex;align-items:center;'
                                    'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                                    unsafe_allow_html=True,
                                )
                            st.caption(f"{status_icon} {title}")
                            kw = meta.get("keywords", [])
                            if kw:
                                st.caption(" ".join(f"`{k}`" for k in kw[:3]))
                            if st.checkbox(action_label, value=st.session_state.get(f"{action_key_prefix}_{fid}", False), key=f"{action_key_prefix}_{fid}"):
                                action_ids.append(fid)

                st.markdown("---")
                action_count = len(action_ids)
                if review_filter == "未確認→確認済み（📝→✅）":
                    if st.button(
                        f"✅ 選択した {action_count} 件を確認済みにする",
                        type="primary", key="imp_bulk_review_run",
                        disabled=(action_count == 0),
                    ):
                        for fid in action_ids:
                            if fid in metadata:
                                metadata[fid]["status"] = STATUS_REVIEWED
                        save_metadata(metadata)
                        for fid in action_ids:
                            st.session_state.pop(f"{action_key_prefix}_{fid}", None)
                        st.success(f"✅ {action_count} 件を確認済みにしました。")
                        st.rerun()
                else:
                    if st.button(
                        f"🆕 選択した {action_count} 件を未確認に戻す",
                        type="primary", key="imp_bulk_unreview_run",
                        disabled=(action_count == 0),
                    ):
                        for fid in action_ids:
                            if fid in metadata:
                                metadata[fid]["status"] = STATUS_AUTO
                        save_metadata(metadata)
                        for fid in action_ids:
                            st.session_state.pop(f"{action_key_prefix}_{fid}", None)
                        st.success(f"🆕 {action_count} 件を未確認に戻しました。")
                        st.rerun()


# ===========================================================================
# 統合ページ: ⚙️ 設定（フォルダ管理 + ゴミ箱 + システム 統合）
# ===========================================================================
def page_settings_all():
    """設定ページ — フォルダ管理・ゴミ箱・システム設定を3つのサブタブに統合。"""
    sub_tab1, sub_tab2, sub_tab3 = st.tabs([
        "📂 フォルダ管理", "🗑️ ゴミ箱", "🔧 システム"
    ])

    # =======================================================================
    # サブタブ1: フォルダ管理
    # =======================================================================
    with sub_tab1:
        page_folder_settings()

    # =======================================================================
    # サブタブ2: ゴミ箱
    # =======================================================================
    with sub_tab2:
        page_trash()

    # =======================================================================
    # サブタブ3: システム
    # =======================================================================
    with sub_tab3:
        st.subheader("🔧 システム")

        # --- 解析データの一括削除 ---
        st.markdown("#### 🗑️ 解析データの一括削除")
        metadata = load_metadata()
        service = get_drive_service()
        folder_id = get_folder_id()
        images = list_all_images(service, folder_id, metadata, get_patient_folder_id())
        analyzed_images = [img for img in images if img["id"] in metadata]

        if not analyzed_images:
            st.info("解析済みの画像データはありません。")
        else:
            st.warning(
                f"**{len(analyzed_images)} 件**の解析済みデータがあります。"
            )
            sys_del_method = st.radio(
                "削除方法",
                ["🗑️ ゴミ箱に移動（再取り込み不可）", "🔄 メタデータのみ削除（再取り込み可能）"],
                key="sys_del_method", horizontal=True,
            )
            if sys_del_method == "🔄 メタデータのみ削除（再取り込み可能）":
                st.info("💡 画像ファイルはDriveに残ります。メタデータのみ削除します。")

            sdel_c1, sdel_c2, sdel_c3 = st.columns([1, 1, 3])
            with sdel_c1:
                if st.button("☑️ 全選択", key="sys_del_sel_all"):
                    for img in analyzed_images:
                        st.session_state[f"sys_del_{img['id']}"] = True
                    st.rerun()
            with sdel_c2:
                if st.button("☐ 全解除", key="sys_del_sel_none"):
                    for img in analyzed_images:
                        st.session_state[f"sys_del_{img['id']}"] = False
                    st.rerun()

            del_page_items, del_cur, del_total_pages = _paginate(analyzed_images, "sys_delete_page")
            _render_pagination_controls("sys_delete_page", del_cur, del_total_pages, len(analyzed_images))

            delete_ids = []
            cols_per_row = 4
            for row_start in range(0, len(del_page_items), cols_per_row):
                cols = st.columns(cols_per_row)
                for col_idx in range(cols_per_row):
                    img_idx = row_start + col_idx
                    if img_idx >= len(del_page_items):
                        break
                    img = del_page_items[img_idx]
                    fid = img["id"]
                    meta = metadata[fid]
                    title = meta.get("title", img["name"])
                    status_icon = get_status_icon(meta)
                    with cols[col_idx]:
                        try:
                            thumb_bytes = download_image(service, fid)
                            st.image(thumb_bytes, width="stretch")
                        except Exception:
                            st.markdown(
                                '<div style="background:#333;border-radius:8px;'
                                'height:80px;display:flex;align-items:center;'
                                'justify-content:center;color:#888;font-size:24px;">🖼️</div>',
                                unsafe_allow_html=True,
                            )
                        st.caption(f"{status_icon} {title}")
                        if st.checkbox("削除する", value=st.session_state.get(f"sys_del_{fid}", False), key=f"sys_del_{fid}"):
                            delete_ids.append(fid)

            st.markdown("---")
            delete_count = len(delete_ids)
            if sys_del_method == "🗑️ ゴミ箱に移動（再取り込み不可）":
                if delete_count > 0:
                    st.warning(f"🗑️ **{delete_count} 件**をゴミ箱に移動します。")
                if st.button(
                    f"🗑️ 選択した {delete_count} 件をゴミ箱へ",
                    type="primary", key="sys_del_trash_run",
                    disabled=(delete_count == 0),
                ):
                    moved = move_to_trash(delete_ids, metadata)
                    for fid in delete_ids:
                        st.session_state.pop(f"sys_del_{fid}", None)
                    st.success(f"✅ {moved} 件をゴミ箱に移動しました。")
                    st.rerun()
            else:
                if delete_count > 0:
                    st.info(f"🔄 **{delete_count} 件**のメタデータを削除します。")
                if st.button(
                    f"🔄 選択した {delete_count} 件のメタデータを削除",
                    type="primary", key="sys_del_meta_run",
                    disabled=(delete_count == 0),
                ):
                    removed = 0
                    for fid in delete_ids:
                        if fid in metadata:
                            del metadata[fid]
                            removed += 1
                        st.session_state.pop(f"sys_del_{fid}", None)
                    remove_from_ignore_list(delete_ids)
                    save_metadata(metadata)
                    _invalidate_all_caches()
                    st.success(f"✅ {removed} 件のメタデータを削除しました。")
                    st.rerun()

        st.markdown("---")

        # --- Sheets接続状態 + 移行ツール ---
        st.markdown("#### ☁️ データ管理")
        sh_status = get_sheets_client()
        if sh_status is not None:
            st.success("☁️ Google Sheets: 接続済み")
            # 体重データの同期ステータス
            try:
                wd = _read_json_from_sheet(sh_status, "weight_data")
                if wd and "records" in wd:
                    rec_count = len(wd["records"])
                    item_count = sum(len(_get_day_items(wd["records"][d])) for d in wd["records"])
                    st.caption(f"📡 体重データ: {rec_count}日分 / {item_count}品目 (Sheets上)")
                else:
                    st.caption("📡 体重データ: Sheets上にデータなし")
            except Exception:
                st.caption("📡 体重データ: 読み取り確認スキップ")
        else:
            st.warning("☁️ Google Sheets: 未接続（ローカルJSONにフォールバック中）")

        col_sys1, col_sys2 = st.columns(2)
        with col_sys1:
            if st.button("📤 ローカル → Sheets 移行", key="sys_migrate", width="stretch"):
                _migrate_local_to_sheets()
        with col_sys2:
            if st.button("🔄 データ再読み込み", key="sys_reload", width="stretch"):
                _invalidate_all_caches()
                st.toast("☁️ Google Sheets から最新データを再読み込みしました")
                st.rerun()

        # --- ログイン情報 & ログアウト ---
        st.markdown("---")
        st.markdown("#### 👤 ログイン情報")
        auth_user = st.session_state.get("auth_user")
        if auth_user:
            st.write(f"ログイン中: **{auth_user}**")
            if st.button("🚪 ログアウト", key="sys_logout", use_container_width=True):
                # localStorage のトークンをクリア
                _clear_auth_storage()
                st.session_state["authenticated"] = False
                st.session_state.pop("auth_user", None)
                # URLからトークンも削除
                if "token" in st.query_params:
                    del st.query_params["token"]
                st.rerun()
        else:
            st.caption("認証が設定されていないか、フリーアクセスモードです。")


# ===========================================================================
# 体重管理ページ
# ===========================================================================
def _inject_wm_css():
    """MoneyForward風CSSスタイル注入。"""
    st.markdown("""
    <style>
    .mf-weight-card {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        border-radius: 16px; padding: 20px; color: white; text-align: center;
        margin-bottom: 8px;
    }
    .mf-weight-card .mf-label { font-size: 13px; opacity: 0.8; }
    .mf-weight-card .mf-value { font-size: 32px; font-weight: bold; margin: 4px 0; }
    .mf-weight-card .mf-sub { font-size: 12px; opacity: 0.7; }
    .mf-cal-card {
        background: white; border: 1px solid #e0e0e0; border-radius: 16px;
        padding: 20px; text-align: center; margin-bottom: 8px;
    }
    .mf-cal-card .mf-label { font-size: 13px; color: #666; }
    .mf-cal-card .mf-value { font-size: 36px; font-weight: bold; margin: 4px 0; }
    .mf-cal-card .mf-target { font-size: 14px; color: #999; }
    .mf-cal-card .mf-remaining { font-size: 13px; color: #666; margin-top: 8px; }
    .mf-progress-bg {
        background: #e0e0e0; border-radius: 10px; height: 12px; margin: 10px 0;
        overflow: hidden;
    }
    .mf-progress-bar {
        height: 12px; border-radius: 10px; transition: width 0.3s;
    }
    .mf-meal-header {
        display: flex; justify-content: space-between; align-items: center;
        padding: 10px 14px; background: #f8f9fa; border-radius: 8px;
        margin: 12px 0 4px 0; font-weight: bold; font-size: 15px;
    }
    .mf-item-row {
        display: flex; justify-content: space-between; align-items: center;
        padding: 6px 14px 6px 24px; border-bottom: 1px solid #f5f5f5;
        font-size: 14px;
    }
    .mf-item-row:last-child { border-bottom: none; }
    .mf-date-display {
        text-align: center; font-size: 18px; font-weight: bold;
        padding: 8px 0; line-height: 2.2;
    }
    .mf-grand-total {
        text-align: right; font-size: 16px; font-weight: bold;
        padding: 12px 14px; border-top: 2px solid #333; margin-top: 8px;
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
    """MoneyForward風の日付ナビゲーション。◀ 前日 | 日付 | 翌日 ▶ | 今日"""
    if "wm_selected_date" not in st.session_state:
        st.session_state["wm_selected_date"] = date.today()

    sel = st.session_state["wm_selected_date"]
    weekday_ja = ["月", "火", "水", "木", "金", "土", "日"][sel.weekday()]

    col_prev, col_date, col_next, col_today = st.columns([1, 4, 1, 1.5])
    with col_prev:
        if st.button("◀", key="wm_prev_day", use_container_width=True):
            st.session_state["wm_selected_date"] = sel - timedelta(days=1)
            st.rerun()
    with col_date:
        st.markdown(
            f"<div class='mf-date-display'>{sel.month}月{sel.day}日（{weekday_ja}）</div>",
            unsafe_allow_html=True,
        )
    with col_next:
        if st.button("▶", key="wm_next_day", use_container_width=True):
            st.session_state["wm_selected_date"] = sel + timedelta(days=1)
            st.rerun()
    with col_today:
        if sel != date.today():
            if st.button("今日", key="wm_today_btn", use_container_width=True):
                st.session_state["wm_selected_date"] = date.today()
                st.rerun()


def _render_dashboard_card(day_data: dict, goals: dict, records: dict):
    """MoneyForward風のダッシュボードカード: 体重 + カロリー。"""
    total_cal = day_data.get("total_calories", 0)
    weight = day_data.get("weight")
    target_cal = goals.get("daily_calorie_target", 0)
    target_wt = goals.get("target_weight_kg")
    remaining = max(0, target_cal - total_cal) if target_cal else 0

    # カロリー色分け
    if target_cal > 0:
        ratio = total_cal / target_cal
        if ratio <= 0.8:
            cal_color = "#4CAF50"
        elif ratio <= 1.0:
            cal_color = "#FF9800"
        else:
            cal_color = "#F44336"
        progress_pct = min(100, int(ratio * 100))
    else:
        cal_color = "#888"
        progress_pct = 0

    # 体重トレンド
    trend = _get_weight_trend(records)
    trend_arrow = {"down": "↓", "up": "↑", "flat": "→"}.get(trend, "")

    col_wt, col_cal = st.columns([1, 1.5])

    with col_wt:
        w_display = f"{weight}" if weight else "--"
        wt_sub = ""
        if weight and target_wt:
            diff = round(weight - target_wt, 1)
            wt_sub = f"目標まで {abs(diff)} kg" if diff > 0 else "目標達成!"
        elif target_wt:
            wt_sub = f"目標: {target_wt} kg"

        st.markdown(f"""
        <div class="mf-weight-card">
            <div class="mf-label">⚖️ 体重</div>
            <div class="mf-value">{w_display} <span style="font-size:16px;">kg</span> {trend_arrow}</div>
            <div class="mf-sub">{wt_sub}</div>
        </div>
        """, unsafe_allow_html=True)

    with col_cal:
        target_str = f"/ {target_cal:,}" if target_cal else ""
        remaining_str = f"残り <b>{remaining:,}</b> kcal" if target_cal else "目標未設定"
        pct_str = f"{progress_pct}%" if target_cal else ""

        st.markdown(f"""
        <div class="mf-cal-card">
            <div class="mf-label">🔥 カロリー</div>
            <div class="mf-value" style="color: {cal_color};">{total_cal:,}</div>
            <div class="mf-target">{target_str} kcal {pct_str}</div>
            <div class="mf-progress-bg">
                <div class="mf-progress-bar" style="background: {cal_color}; width: {progress_pct}%;"></div>
            </div>
            <div class="mf-remaining">{remaining_str}</div>
        </div>
        """, unsafe_allow_html=True)


# ---------------------------------------------------------------------------
# 栄養バランス ダッシュボード
# ---------------------------------------------------------------------------

def _nutrient_bar_color(ratio: float) -> str:
    """達成率に応じた色を返す。"""
    if ratio <= 0:
        return "#BDBDBD"
    elif ratio < 0.6:
        return "#F44336"   # 赤（大幅不足）
    elif ratio < 0.8:
        return "#FF9800"   # 黄（やや不足）
    elif ratio <= 1.2:
        return "#4CAF50"   # 緑（適正）
    else:
        return "#F44336"   # 赤（過剰）


def _render_nutrient_dashboard(day_data: dict, goals: dict):
    """栄養素の摂取状況をプログレスバーで表示する。"""
    totals = _aggregate_day_nutrients(day_data)
    if not totals:
        return  # 栄養素データなし → 何も表示しない

    targets = _get_nutrient_targets(goals)

    with st.expander("🥗 栄養バランス", expanded=True):
        # --- PFC（三大栄養素）プログレスバー ---
        st.markdown("#### 三大栄養素 (PFC)")
        pfc_html_parts = []
        for key in _PFC_KEYS:
            info = targets[key]
            actual = round(totals.get(key, 0), 1)
            target_val = info["target"] or 0
            if target_val > 0:
                ratio = actual / target_val
                pct = min(100, int(ratio * 100))
            else:
                ratio = 0
                pct = 0
            color = _nutrient_bar_color(ratio)
            label = info["label"]
            unit = info["unit"]
            target_str = f"/ {target_val}{unit}" if target_val else ""
            warn = " ⚠️" if ratio > 1.2 or (target_val > 0 and ratio < 0.6) else ""
            pfc_html_parts.append(f"""
            <div style="margin-bottom:8px;">
                <div style="display:flex;justify-content:space-between;font-size:13px;margin-bottom:2px;">
                    <span><b>{label}</b></span>
                    <span>{actual}{unit} {target_str} ({pct}%){warn}</span>
                </div>
                <div style="background:#E0E0E0;border-radius:4px;height:12px;overflow:hidden;">
                    <div style="background:{color};width:{pct}%;height:100%;border-radius:4px;transition:width 0.3s;"></div>
                </div>
            </div>""")
        st.markdown("".join(pfc_html_parts), unsafe_allow_html=True)

        # --- PFCカロリー比率 ---
        p_cal = totals.get("protein", 0) * 4
        f_cal = totals.get("fat", 0) * 9
        c_cal = totals.get("carbs", 0) * 4
        total_pfc_cal = p_cal + f_cal + c_cal
        if total_pfc_cal > 0:
            p_pct = int(p_cal / total_pfc_cal * 100)
            f_pct = int(f_cal / total_pfc_cal * 100)
            c_pct = 100 - p_pct - f_pct
            st.markdown(f"""
            <div style="display:flex;height:20px;border-radius:4px;overflow:hidden;margin:4px 0 12px;">
                <div style="background:#42A5F5;width:{p_pct}%;display:flex;align-items:center;justify-content:center;font-size:10px;color:#fff;">{p_pct}%P</div>
                <div style="background:#FFA726;width:{f_pct}%;display:flex;align-items:center;justify-content:center;font-size:10px;color:#fff;">{f_pct}%F</div>
                <div style="background:#66BB6A;width:{c_pct}%;display:flex;align-items:center;justify-content:center;font-size:10px;color:#fff;">{c_pct}%C</div>
            </div>
            <div style="font-size:11px;color:#888;text-align:center;margin-bottom:8px;">
                理想: P 13-20% / F 20-30% / C 50-65%
            </div>
            """, unsafe_allow_html=True)

        # --- 食塩摂取量（上限のみ） ---
        salt_actual = round(totals.get("salt", 0), 1)
        salt_upper = targets["salt"]["upper"] or 7.5
        salt_ok = salt_actual <= salt_upper
        salt_icon = "✅" if salt_ok else "⚠️"
        salt_color = "#4CAF50" if salt_ok else "#F44336"
        st.markdown(f"""
        <div style="padding:6px 12px;background:#F5F5F5;border-radius:6px;margin:8px 0;font-size:13px;">
            🧂 <b>食塩</b>: <span style="color:{salt_color};">{salt_actual}g</span> / {salt_upper}g以下 {salt_icon}
        </div>
        """, unsafe_allow_html=True)

        # --- 微量栄養素（達成率バー） ---
        has_micro = any(totals.get(k, 0) > 0 for k in _MICRO_KEYS)
        if has_micro:
            st.markdown("#### ビタミン・ミネラル")
            micro_html_parts = []
            for key in _MICRO_KEYS:
                info = targets[key]
                actual = round(totals.get(key, 0), 1)
                target_val = info["target"]
                if target_val and target_val > 0:
                    ratio = actual / target_val
                    pct = min(150, int(ratio * 100))
                    display_pct = min(100, pct)
                else:
                    ratio = 0
                    pct = 0
                    display_pct = 0
                color = _nutrient_bar_color(ratio)
                label = info["label"]
                unit = info["unit"]
                target_str = f"/ {target_val}{unit}" if target_val else ""
                micro_html_parts.append(f"""
                <div style="margin-bottom:6px;">
                    <div style="display:flex;justify-content:space-between;font-size:12px;margin-bottom:1px;">
                        <span>{label}</span>
                        <span>{actual}{unit} {target_str} ({pct}%)</span>
                    </div>
                    <div style="background:#E0E0E0;border-radius:3px;height:8px;overflow:hidden;">
                        <div style="background:{color};width:{display_pct}%;height:100%;border-radius:3px;"></div>
                    </div>
                </div>""")
            st.markdown("".join(micro_html_parts), unsafe_allow_html=True)


def _render_meal_groups(day_data: dict, weight_data: dict):
    """食事タイプ別にグループ化して表示（MoneyForwardカテゴリ風）。"""
    current_items = _get_day_items(day_data)

    if not current_items:
        st.caption("📋 この日の食事記録はまだありません。")
        return

    groups = _group_items_by_meal(current_items)

    for meal_key, meal_items in groups.items():
        label = MEAL_TYPE_LABELS.get(meal_key, "📋 未分類")
        color = MEAL_TYPE_COLORS.get(meal_key, "#757575")
        subtotal = sum(it.get("calories", 0) for it in meal_items)

        # カテゴリヘッダー
        st.markdown(
            f'<div class="mf-meal-header" style="border-left: 4px solid {color};">'
            f'<span>{label}</span><span>{subtotal:,} kcal</span></div>',
            unsafe_allow_html=True,
        )

        if not meal_items:
            st.caption("　（記録なし）")
        else:
            for it in meal_items:
                _render_food_item_row(it, day_data, weight_data)

    # 合計
    total = sum(it.get("calories", 0) for it in current_items)
    st.markdown(
        f'<div class="mf-grand-total">合計: {total:,} kcal</div>',
        unsafe_allow_html=True,
    )


def _render_food_item_row(item: dict, day_data: dict, weight_data: dict):
    """MoneyForward風の1品目行（タップで編集展開）。"""
    item_id = item.get("id", "")
    name = item.get("name", "")
    qty = item.get("quantity", "ふつう")
    cal = item.get("calories", 0)
    meal_type = item.get("meal_type", "")

    edit_key = f"wm_edit_{item_id}"
    is_editing = st.session_state.get(edit_key, False)

    c1, c2, c3, c4 = st.columns([4.5, 1.8, 0.5, 0.5])

    with c1:
        st.markdown(
            f'**{name}** <span style="color:#999; font-size:13px;">({qty})</span>',
            unsafe_allow_html=True,
        )
    with c2:
        st.markdown(f"**{cal:,} kcal**")
    with c3:
        if item_id and st.button("✏️", key=f"wm_edt_{item_id}", help="編集"):
            st.session_state[edit_key] = not is_editing
            st.rerun()
    with c4:
        if item_id and st.button("🗑️", key=f"wm_del_{item_id}", help="削除"):
            if "items" in day_data:
                day_data["items"] = [x for x in day_data["items"] if x.get("id") != item_id]
                day_data["total_calories"] = sum(x.get("calories", 0) for x in day_data["items"])
            save_weight_data(weight_data)
            st.rerun()

    # --- インライン編集フォーム ---
    if is_editing and item_id:
        with st.form(key=f"wm_edit_form_{item_id}"):
            ec1, ec2 = st.columns(2)
            with ec1:
                new_name = st.text_input("品目名", value=name)
            with ec2:
                new_qty = st.text_input("量", value=qty)
            ec3, ec4 = st.columns(2)
            with ec3:
                meal_options = list(MEAL_TYPE_LABELS.keys())
                meal_labels = [MEAL_TYPE_LABELS[k] for k in meal_options]
                current_idx = meal_options.index(meal_type) if meal_type in meal_options else 0
                new_meal_label = st.selectbox("食事タイプ", meal_labels, index=current_idx)
                new_meal_type = meal_options[meal_labels.index(new_meal_label)]
            with ec4:
                st.markdown(f"現在: **{cal} kcal**")
                st.caption("💡 品目名・量を変更すると保存時にAIが自動再計算します")
            edit_submitted = st.form_submit_button("💾 保存", use_container_width=True)
        if edit_submitted:
            final_name = new_name.strip() or name
            final_qty = new_qty.strip() or qty
            # 品目名 or 量が変わったら AI でカロリー再計算
            name_changed = final_name != name
            qty_changed = final_qty != qty
            final_cal = cal
            if name_changed or qty_changed:
                api_key = get_gemini_api_key()
                if api_key:
                    with st.spinner("🤖 カロリーを再計算中..."):
                        recalc = _recalc_calories(
                            [{"name": final_name, "quantity": final_qty}],
                            api_key,
                        )
                    if recalc and len(recalc) > 0 and recalc[0].get("calories", 0) > 0:
                        final_cal = recalc[0]["calories"]
                        _recalc_nuts = recalc[0].get("nutrients", {})
                    else:
                        _recalc_nuts = {}
                else:
                    _recalc_nuts = {}
            else:
                _recalc_nuts = {}
            for x in day_data.get("items", []):
                if x.get("id") == item_id:
                    x["name"] = final_name
                    x["quantity"] = final_qty
                    x["calories"] = final_cal
                    x["meal_type"] = new_meal_type
                    if _recalc_nuts:
                        x["nutrients"] = _recalc_nuts
                    break
            day_data["total_calories"] = sum(
                x.get("calories", 0) for x in _get_day_items(day_data)
            )
            save_weight_data(weight_data)
            st.session_state[edit_key] = False
            st.rerun()

        # --- 栄養素リトロフィットボタン ---
        has_nutrients = bool(item.get("nutrients"))
        if not has_nutrients:
            if st.button("🔄 栄養素を推定", key=f"wm_retro_{item_id}", help="AIで栄養素を推定します"):
                _ak = get_gemini_api_key()
                if _ak:
                    with st.spinner("栄養素を推定中..."):
                        _retro = _recalc_calories(
                            [{"name": name, "quantity": qty}], _ak
                        )
                    if _retro and len(_retro) > 0:
                        _retro_nuts = _retro[0].get("nutrients", {})
                        _retro_cal = _retro[0].get("calories", 0)
                        for x in day_data.get("items", []):
                            if x.get("id") == item_id:
                                x["nutrients"] = _retro_nuts
                                if _retro_cal > 0:
                                    x["calories"] = _retro_cal
                                break
                        day_data["total_calories"] = sum(
                            x.get("calories", 0) for x in _get_day_items(day_data)
                        )
                        save_weight_data(weight_data)
                        st.toast(f"✅ {name} の栄養素を推定しました")
                        st.rerun()
                    else:
                        st.error("推定失敗")
                else:
                    st.warning("APIキー未設定")
        else:
            # 栄養素サマリーを小さく表示
            nuts = item.get("nutrients", {})
            p = round(nuts.get("protein", 0), 1)
            f = round(nuts.get("fat", 0), 1)
            c = round(nuts.get("carbs", 0), 1)
            if p or f or c:
                st.caption(f"P:{p}g  F:{f}g  C:{c}g")


def _render_weight_history(records: dict, goals: dict):
    """体重管理の履歴一覧（MoneyForward風）。"""

    if not records:
        st.info("まだ記録がありません。「📝 記録」タブからデータを入力してください。")
        return

    # --- 期間フィルター ---
    period = st.selectbox("表示期間", ["直近7日", "直近30日", "全期間"], key="wm_hist_period")
    today = date.today()
    if period == "直近7日":
        cutoff = today - timedelta(days=7)
    elif period == "直近30日":
        cutoff = today - timedelta(days=30)
    else:
        cutoff = None

    # 日付降順でフィルタ
    sorted_dates = sorted(records.keys(), reverse=True)
    if cutoff:
        sorted_dates = [d for d in sorted_dates if d >= cutoff.strftime("%Y-%m-%d")]

    if not sorted_dates:
        st.caption("この期間のデータはありません。")
        return

    # --- 体重推移チャート ---
    weight_dates = []
    weight_vals = []
    for dk in sorted(sorted_dates):  # チャートは昇順
        w = records[dk].get("weight")
        if w:
            weight_dates.append(dk)
            weight_vals.append(w)

    if weight_vals:
        st.markdown("### 📈 体重推移")
        import pandas as pd
        chart_df = pd.DataFrame({"日付": weight_dates, "体重(kg)": weight_vals})
        chart_df["日付"] = pd.to_datetime(chart_df["日付"])
        chart_df = chart_df.set_index("日付")
        st.line_chart(chart_df)

        target_wt = goals.get("target_weight_kg")
        if target_wt:
            st.caption(f"🎯 目標体重: {target_wt} kg")

    # --- 期間サマリー ---
    total_days = len(sorted_dates)
    total_cal_all = sum(records[dk].get("total_calories", 0) for dk in sorted_dates)
    days_with_items = sum(1 for dk in sorted_dates if _get_day_items(records[dk]))
    avg_cal = int(total_cal_all / days_with_items) if days_with_items else 0

    sc1, sc2, sc3 = st.columns(3)
    with sc1:
        st.metric("記録日数", f"{total_days} 日")
    with sc2:
        st.metric("平均カロリー", f"{avg_cal} kcal")
    with sc3:
        if len(weight_vals) >= 2:
            wt_change = round(weight_vals[-1] - weight_vals[0], 1)
            sign = "+" if wt_change > 0 else ""
            st.metric("体重変化", f"{sign}{wt_change} kg")
        else:
            st.metric("体重変化", "---")

    # --- カテゴリ別カロリー内訳 ---
    meal_cal_totals = {mt: 0 for mt in MEAL_TYPE_ORDER}
    for dk in sorted_dates:
        day_items = _get_day_items(records[dk])
        for it in day_items:
            mt = it.get("meal_type")
            if mt in meal_cal_totals:
                meal_cal_totals[mt] += it.get("calories", 0)

    if any(v > 0 for v in meal_cal_totals.values()):
        st.markdown("### 🥧 食事カテゴリ別カロリー")
        import pandas as pd
        labels = [MEAL_TYPE_LABELS.get(mt, mt) for mt in MEAL_TYPE_ORDER]
        vals = [meal_cal_totals[mt] for mt in MEAL_TYPE_ORDER]
        pie_df = pd.DataFrame({"カテゴリ": labels, "カロリー(kcal)": vals})
        pie_df = pie_df.set_index("カテゴリ")
        st.bar_chart(pie_df)

    # --- 栄養素トレンド ---
    # 各日の栄養素を集計
    _nut_dates = []
    _nut_p = []
    _nut_f = []
    _nut_c = []
    for dk in sorted(sorted_dates):  # チャートは昇順
        day_nuts = _aggregate_day_nutrients(records[dk])
        if day_nuts:
            _nut_dates.append(dk)
            _nut_p.append(round(day_nuts.get("protein", 0), 1))
            _nut_f.append(round(day_nuts.get("fat", 0), 1))
            _nut_c.append(round(day_nuts.get("carbs", 0), 1))

    if _nut_dates:
        st.markdown("### 🥗 栄養素推移 (PFC)")
        import pandas as pd
        _nut_df = pd.DataFrame({
            "日付": _nut_dates,
            "たんぱく質(g)": _nut_p,
            "脂質(g)": _nut_f,
            "炭水化物(g)": _nut_c,
        })
        _nut_df["日付"] = pd.to_datetime(_nut_df["日付"])
        _nut_df = _nut_df.set_index("日付")
        st.line_chart(_nut_df)

        # 期間平均
        _avg_p = round(sum(_nut_p) / len(_nut_p), 1) if _nut_p else 0
        _avg_f = round(sum(_nut_f) / len(_nut_f), 1) if _nut_f else 0
        _avg_c = round(sum(_nut_c) / len(_nut_c), 1) if _nut_c else 0
        _avg_salt_vals = [
            round(_aggregate_day_nutrients(records[dk]).get("salt", 0), 1)
            for dk in sorted_dates
            if _aggregate_day_nutrients(records[dk])
        ]
        _avg_salt = round(sum(_avg_salt_vals) / len(_avg_salt_vals), 1) if _avg_salt_vals else 0

        nc1, nc2, nc3, nc4 = st.columns(4)
        with nc1:
            st.metric("平均P", f"{_avg_p}g")
        with nc2:
            st.metric("平均F", f"{_avg_f}g")
        with nc3:
            st.metric("平均C", f"{_avg_c}g")
        with nc4:
            st.metric("平均食塩", f"{_avg_salt}g")

    # --- 日別サマリー（MoneyForward風） ---
    st.markdown("### 📋 日別記録")

    for dk in sorted_dates:
        day = records[dk]
        w = day.get("weight")
        cal = day.get("total_calories", 0)
        day_items = _get_day_items(day)
        item_count = len(day_items)

        dt = datetime.strptime(dk, "%Y-%m-%d")
        weekday = ["月", "火", "水", "木", "金", "土", "日"][dt.weekday()]

        w_str = f"⚖️ {w} kg" if w else "⚖️ --"
        header = f"📅 {dt.month}/{dt.day}（{weekday}）　{w_str}　🔥 {cal} kcal　🍽️ {item_count}品"

        with st.expander(header, expanded=False):
            if not day_items:
                st.caption("食事記録なし")
            else:
                groups = _group_items_by_meal(day_items)
                for meal_key, items in groups.items():
                    if not items:
                        continue
                    label = MEAL_TYPE_LABELS.get(meal_key, "📋 未分類")
                    sub = sum(it.get("calories", 0) for it in items)
                    st.markdown(f"**{label}** — {sub} kcal")
                    for it in items:
                        st.markdown(
                            f"　{it.get('name', '')}（{it.get('quantity', 'ふつう')}）"
                            f"　**{it.get('calories', 0)} kcal**"
                        )


def page_weight_management():
    """体重管理ページ — MoneyForward風UI。"""
    _inject_wm_css()
    st.markdown("## ⚖️ 体重管理")

    weight_data = load_weight_data()
    api_key = get_gemini_api_key()
    records = weight_data.setdefault("records", {})
    goals = weight_data.get("goals", {})

    tab_record, tab_history = st.tabs(["📝 記録", "📊 履歴"])

    with tab_history:
        _render_weight_history(records, goals)

    with tab_record:

        # ====== 日付ナビゲーション ======
        _render_date_navigation()
        selected_date = st.session_state.get("wm_selected_date", date.today())
        date_key = selected_date.strftime("%Y-%m-%d")
        day_data = records.setdefault(date_key, {"items": [], "total_calories": 0})
        weight = day_data.get("weight")

        # ====== ダッシュボードカード ======
        _render_dashboard_card(day_data, goals, records)

        # ====== 体重入力（折りたたみ） ======
        with st.expander("⚖️ 体重を入力"):
            wt_uploaded = st.file_uploader(
                "体重計の写真（任意）",
                type=["png", "jpg", "jpeg"],
                key=f"wm_weight_upload_{date_key}",
            )
            if wt_uploaded is not None:
                wt_bytes = wt_uploaded.getvalue()
                st.image(wt_bytes, width=250, caption="体重計の写真")
                if st.button("🤖 AIで読み取る", key="wm_weight_ai"):
                    if api_key:
                        with st.spinner("体重を読み取り中..."):
                            result = analyze_weight_scale_image(wt_bytes, api_key)
                        if result and result.get("weight_kg") is not None:
                            st.session_state["wm_ai_weight"] = result["weight_kg"]
                            conf = result.get("confidence", "")
                            if conf == "high":
                                st.success(f"✅ 読み取り: **{result['weight_kg']} kg**（高精度）")
                            elif conf == "low":
                                st.warning(f"⚠️ 読み取り: **{result['weight_kg']} kg**（低精度）")
                            else:
                                st.error("読み取れませんでした。")
                        else:
                            st.error("読み取り失敗。手動入力してください。")
                    else:
                        st.warning("APIキー未設定")

            default_wt = st.session_state.get("wm_ai_weight", day_data.get("weight") or 0.0)
            with st.form(key=f"wm_weight_form_{date_key}"):
                input_weight = st.number_input(
                    "体重 (kg)", min_value=0.0, max_value=300.0,
                    value=float(default_wt), step=0.1, format="%.1f",
                )
                weight_submitted = st.form_submit_button("💾 体重を記録", type="primary")
            if weight_submitted:
                if input_weight > 0:
                    day_data["weight"] = round(input_weight, 1)
                    day_data["weight_recorded_at"] = datetime.now().isoformat()
                    if wt_uploaded is not None:
                        WEIGHT_UPLOADS_DIR.mkdir(exist_ok=True)
                        wt_id = f"wm_{uuid.uuid4().hex[:12]}"
                        ext = wt_uploaded.name.rsplit(".", 1)[-1].lower() if "." in wt_uploaded.name else "png"
                        (WEIGHT_UPLOADS_DIR / f"{wt_id}.{ext}").write_bytes(wt_uploaded.getvalue())
                        day_data["weight_image_id"] = wt_id
                        day_data["weight_image_ext"] = ext
                    save_weight_data(weight_data)
                    st.session_state.pop("wm_ai_weight", None)
                    st.toast(f"✅ 体重 {input_weight} kg を記録しました")
                    st.rerun()
                else:
                    st.warning("0 より大きい値を入力してください。")

        # ====== AIコメント ======
        comment = _generate_weight_comment(day_data, goals)
        st.info(comment)

        # ====== 栄養バランス ======
        _render_nutrient_dashboard(day_data, goals)

        # ====== カテゴリ別食事リスト ======
        _render_meal_groups(day_data, weight_data)

        # ====== 食事を追加 ======
        with st.expander("➕ 食事を追加", expanded=bool(st.session_state.get("wm_uploaded_foods"))):
            # 食事タイプ選択（MoneyForward風）
            meal_type = st.radio(
                "食事タイプ",
                options=MEAL_TYPE_ORDER,
                format_func=lambda x: MEAL_TYPE_LABELS[x],
                index=MEAL_TYPE_ORDER.index(_guess_meal_type()),
                key="wm_meal_type_select",
                horizontal=True,
            )

            # Google Drive取り込み
            food_fid = get_food_folder_id()
            if food_fid:
                gd_col1, gd_col2 = st.columns([3, 1])
                with gd_col1:
                    st.caption("📂 Google Driveから自動取り込み")
                with gd_col2:
                    if st.button("🔄 取り込み", key="wm_food_drive_scan"):
                        try:
                            service = get_drive_service()
                            _ak = get_gemini_api_key()
                            if _ak:
                                with st.spinner("取り込み中..."):
                                    n = scan_food_images(service, food_fid, _ak, manual=True)
                                if n > 0:
                                    st.toast(f"🔔 {n} 枚取り込みました", icon="📷")
                                    st.rerun()
                                else:
                                    st.toast("新しい画像なし", icon="ℹ️")
                            else:
                                st.warning("APIキー未設定")
                        except Exception as e:
                            st.error(f"エラー: {e}")

            # 画像アップロード
            with st.form("wm_food_form", clear_on_submit=True):
                food_files = st.file_uploader(
                    "食事画像（複数選択可）",
                    type=["png", "jpg", "jpeg"],
                    accept_multiple_files=True,
                    key="wm_food_upload",
                )
                submitted = st.form_submit_button("📤 アップロード", type="primary")

            if submitted and food_files:
                uploaded_foods = []
                for f in food_files:
                    uploaded_foods.append({"bytes": f.getvalue(), "name": f.name})
                st.session_state["wm_uploaded_foods"] = uploaded_foods
                st.rerun()
            elif submitted and not food_files:
                st.warning("画像を選択してください。")

            # アップロード済み画像の処理
            all_food_bytes = st.session_state.get("wm_uploaded_foods", [])

            if all_food_bytes:
                st.success(f"📷 {len(all_food_bytes)} 枚アップロード済み")
                thumb_cols = st.columns(min(len(all_food_bytes), 4))
                for i, fb_info in enumerate(all_food_bytes):
                    with thumb_cols[i % len(thumb_cols)]:
                        st.image(fb_info["bytes"], width=150, caption=fb_info["name"])

                if st.button("🤖 AIでカロリー解析", key="wm_food_ai"):
                    if api_key:
                        with st.spinner(f"解析中...（{len(all_food_bytes)}枚）"):
                            images_list = [fb["bytes"] for fb in all_food_bytes]
                            result = analyze_food_images(images_list, api_key)
                        if result and "items" in result:
                            st.session_state["wm_food_items"] = result["items"]
                            st.session_state["wm_food_total"] = result.get("total_calories", 0)
                            st.session_state.pop("wm_recalced_items", None)
                            st.rerun()
                        else:
                            st.error("解析失敗")
                    else:
                        st.warning("APIキー未設定")

                # AI解析結果の編集
                items = st.session_state.get("wm_food_items", [])
                if items:
                    st.markdown("**🤖 AI解析結果（編集可）:**")
                    edited_items = []
                    for i, item in enumerate(items):
                        c1, c2, c3, c4 = st.columns([3, 1.5, 1.5, 1])
                        with c1:
                            name = st.text_input("品目", value=item.get("name", ""), key=f"wm_item_name_{date_key}_{i}")
                        with c2:
                            qty_val = item.get("quantity", "ふつう")
                            qty_idx = QUANTITY_OPTIONS.index(qty_val) if qty_val in QUANTITY_OPTIONS else 1
                            qty = st.selectbox("量", QUANTITY_OPTIONS, index=qty_idx, key=f"wm_item_qty_{date_key}_{i}")
                        with c3:
                            cal = st.number_input("kcal", value=int(item.get("calories", 0)), min_value=0, step=10, key=f"wm_item_cal_{date_key}_{i}")
                        with c4:
                            st.markdown("<br>", unsafe_allow_html=True)
                            remove = st.checkbox("削除", key=f"wm_item_del_{date_key}_{i}")
                        if not remove and name.strip():
                            edited_items.append({"name": name.strip(), "quantity": qty, "calories": cal, "nutrients": item.get("nutrients", {})})

                    st.markdown("---")
                    ac1, ac2, ac3 = st.columns([3, 1.5, 1.5])
                    with ac1:
                        add_name = st.text_input("品目を追加", key=f"wm_add_name_{date_key}", placeholder="品目名")
                    with ac2:
                        add_qty = st.selectbox("量", QUANTITY_OPTIONS, index=1, key=f"wm_add_qty_{date_key}")
                    with ac3:
                        add_cal = st.number_input("kcal", value=0, min_value=0, step=10, key=f"wm_add_cal_{date_key}")
                    if add_name.strip():
                        edited_items.append({"name": add_name.strip(), "quantity": add_qty, "calories": add_cal})

                    new_total = sum(it["calories"] for it in edited_items)
                    st.markdown(f"**合計: {new_total} kcal**")

                    # カロリー再計算
                    if st.button("🔄 カロリー再計算", key="wm_recalc_cal"):
                        if api_key:
                            items_for_recalc = [{"name": it["name"], "quantity": it["quantity"]} for it in edited_items]
                            if items_for_recalc:
                                with st.spinner("再計算中..."):
                                    new_cals = _recalc_calories(items_for_recalc, api_key)
                                if new_cals and len(new_cals) == len(edited_items):
                                    recalced = [
                                        {
                                            "name": it["name"],
                                            "quantity": it["quantity"],
                                            "calories": nc["calories"],
                                            "nutrients": nc.get("nutrients", {}),
                                        }
                                        for it, nc in zip(edited_items, new_cals)
                                    ]
                                    st.session_state["wm_food_items"] = recalced
                                    st.session_state["wm_food_total"] = sum(rc["calories"] for rc in recalced)
                                    st.session_state["wm_recalced_items"] = list(recalced)
                                    for idx in range(len(recalced)):
                                        st.session_state.pop(f"wm_item_name_{date_key}_{idx}", None)
                                        st.session_state.pop(f"wm_item_qty_{date_key}_{idx}", None)
                                        st.session_state.pop(f"wm_item_cal_{date_key}_{idx}", None)
                                        st.session_state.pop(f"wm_item_del_{date_key}_{idx}", None)
                                    st.rerun()
                                else:
                                    st.error("再計算失敗")
                else:
                    edited_items = []
                    st.caption("「🤖 AIでカロリー解析」を押すか、手動入力してください。")
                    mc1, mc2, mc3 = st.columns([3, 1.5, 1.5])
                    with mc1:
                        add_name = st.text_input("品目名", key=f"wm_manual_name_{date_key}", placeholder="例: カレーライス")
                    with mc2:
                        add_qty = st.selectbox("量", QUANTITY_OPTIONS, index=1, key=f"wm_manual_qty_{date_key}")
                    with mc3:
                        add_cal = st.number_input("kcal", value=0, min_value=0, step=10, key=f"wm_manual_cal_{date_key}")
                    if add_name.strip():
                        edited_items.append({"name": add_name.strip(), "quantity": add_qty, "calories": add_cal})

                # 追加・取消ボタン
                btn_col1, btn_col2 = st.columns([3, 1])
                with btn_col1:
                    if st.button("➕ 追加する", key="wm_meal_save", type="primary", disabled=(len(edited_items) == 0)):
                        recalced_data = st.session_state.get("wm_recalced_items")
                        if recalced_data:
                            final_items = []
                            for i, rc_item in enumerate(recalced_data):
                                w_name = st.session_state.get(f"wm_item_name_{date_key}_{i}", rc_item.get("name", ""))
                                w_qty = st.session_state.get(f"wm_item_qty_{date_key}_{i}", rc_item.get("quantity", "ふつう"))
                                w_cal = st.session_state.get(f"wm_item_cal_{date_key}_{i}", rc_item.get("calories", 0))
                                w_del = st.session_state.get(f"wm_item_del_{date_key}_{i}", False)
                                if not w_del and str(w_name).strip():
                                    final_items.append({"name": str(w_name).strip(), "quantity": w_qty, "calories": int(w_cal), "nutrients": rc_item.get("nutrients", {})})
                        else:
                            final_items = list(edited_items)

                        add_n = st.session_state.get(f"wm_add_name_{date_key}", "")
                        if str(add_n).strip():
                            final_items.append({
                                "name": str(add_n).strip(),
                                "quantity": st.session_state.get(f"wm_add_qty_{date_key}", "ふつう"),
                                "calories": int(st.session_state.get(f"wm_add_cal_{date_key}", 0)),
                            })

                        # 画像保存
                        saved_image_ids = []
                        if all_food_bytes:
                            WEIGHT_UPLOADS_DIR.mkdir(exist_ok=True)
                            for fb_info in all_food_bytes:
                                img_id = f"wm_{uuid.uuid4().hex[:12]}"
                                ext = fb_info["name"].rsplit(".", 1)[-1].lower() if "." in fb_info["name"] else "png"
                                (WEIGHT_UPLOADS_DIR / f"{img_id}.{ext}").write_bytes(fb_info["bytes"])
                                saved_image_ids.append({"id": img_id, "ext": ext})

                        # 品目リストに追加（meal_type付き）
                        new_items = []
                        for it in final_items:
                            item_entry = {
                                "id": f"item_{uuid.uuid4().hex[:12]}",
                                "name": it["name"],
                                "quantity": it.get("quantity", "ふつう"),
                                "calories": it["calories"],
                                "nutrients": it.get("nutrients", {}),
                                "meal_type": meal_type,
                            }
                            if saved_image_ids:
                                item_entry["image_id"] = saved_image_ids[0]["id"]
                                item_entry["image_ext"] = saved_image_ids[0]["ext"]
                            new_items.append(item_entry)

                        day_data.setdefault("items", []).extend(new_items)
                        all_items = _get_day_items(day_data)
                        day_data["total_calories"] = sum(it.get("calories", 0) for it in all_items)
                        save_weight_data(weight_data)
                        st.session_state.pop("wm_food_items", None)
                        st.session_state.pop("wm_food_total", None)
                        st.session_state.pop("wm_uploaded_foods", None)
                        st.session_state.pop("wm_recalced_items", None)
                        final_total = sum(it["calories"] for it in final_items)
                        st.toast(f"✅ {len(new_items)} 品目（{final_total} kcal）を追加しました")
                        st.rerun()
                with btn_col2:
                    if st.button("🗑️ 取消", key="wm_meal_cancel"):
                        st.session_state.pop("wm_food_items", None)
                        st.session_state.pop("wm_food_total", None)
                        st.session_state.pop("wm_uploaded_foods", None)
                        st.session_state.pop("wm_recalced_items", None)
                        st.rerun()
            else:
                # 画像未アップロード時の手動入力（formで囲んでスマホ対応）
                with st.form(key=f"wm_manual_form_{date_key}", clear_on_submit=True):
                    mc1, mc2, mc3 = st.columns([3, 1.5, 1.5])
                    with mc1:
                        add_name = st.text_input("品目名", placeholder="例: カレーライス")
                    with mc2:
                        add_qty = st.selectbox("量", QUANTITY_OPTIONS, index=1)
                    with mc3:
                        add_cal = st.number_input("kcal", value=0, min_value=0, step=10)
                    manual_submitted = st.form_submit_button("➕ 追加する", type="primary")
                if manual_submitted and add_name.strip():
                    item_entry = {
                        "id": f"item_{uuid.uuid4().hex[:12]}",
                        "name": add_name.strip(),
                        "quantity": add_qty,
                        "calories": add_cal,
                        "meal_type": meal_type,
                    }
                    # カロリー0の場合はAIで推定
                    if add_cal == 0:
                        _ak = get_gemini_api_key()
                        if _ak:
                            recalc = _recalc_calories(
                                [{"name": add_name.strip(), "quantity": add_qty}], _ak
                            )
                            if recalc and len(recalc) > 0 and recalc[0].get("calories", 0) > 0:
                                item_entry["calories"] = recalc[0]["calories"]
                                item_entry["nutrients"] = recalc[0].get("nutrients", {})
                    day_data.setdefault("items", []).append(item_entry)
                    all_items = _get_day_items(day_data)
                    day_data["total_calories"] = sum(it.get("calories", 0) for it in all_items)
                    save_weight_data(weight_data)
                    st.toast(f"✅ {add_name.strip()}（{item_entry['calories']} kcal）を追加しました")
                    st.rerun()
                elif manual_submitted and not add_name.strip():
                    st.warning("品目名を入力してください。")

        # ====== 目標設定 ======
        with st.expander("🎯 目標設定"):
            cur_target_wt = goals.get("target_weight_kg", 0.0)
            cur_target_date = goals.get("target_date", "")
            cur_target_cal = goals.get("daily_calorie_target", 0)

            # 現在体重を取得（目標計算用）
            current_weight = weight
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
            # session_state に過去日付が残っている場合はクリア
            if "wm_goal_date" in st.session_state:
                try:
                    _cached_gd = st.session_state["wm_goal_date"]
                    if hasattr(_cached_gd, "date"):
                        _cached_gd = _cached_gd.date()
                    if not isinstance(_cached_gd, date) or _cached_gd < date.today():
                        del st.session_state["wm_goal_date"]
                except Exception:
                    st.session_state.pop("wm_goal_date", None)

            cal_default = cur_target_cal if cur_target_cal > 0 else 2000

            with st.form(key="wm_goal_form"):
                new_target_wt = st.number_input(
                    "目標体重 (kg)", min_value=0.0, max_value=300.0,
                    value=float(cur_target_wt), step=0.1, format="%.1f",
                )
                new_target_date = st.date_input(
                    "いつまでに達成？", value=default_target_date,
                )
                new_target_cal = st.number_input(
                    "1日の目標カロリー (kcal)", min_value=0, max_value=10000,
                    value=int(cal_default), step=100,
                )
                goal_submitted = st.form_submit_button("💾 目標を保存", type="primary")

            if goal_submitted:
                if new_target_date < date.today():
                    new_target_date = date.today()
                new_goals = {
                    "target_weight_kg": round(new_target_wt, 1),
                    "target_date": new_target_date.strftime("%Y-%m-%d"),
                    "daily_calorie_target": new_target_cal,
                }
                # 既存の栄養素目標を保持
                if "nutrient_targets" in goals:
                    new_goals["nutrient_targets"] = goals["nutrient_targets"]
                if current_weight:
                    new_goals["current_weight_kg"] = current_weight
                weight_data["goals"] = new_goals
                save_weight_data(weight_data)
                st.toast("✅ 目標を保存しました")
                st.rerun()

            # --- 栄養素目標設定 ---
            with st.expander("🥗 栄養素目標（詳細）"):
                st.caption("日本人の食事摂取基準(2020年版)に基づくデフォルト値を使用しています。変更する場合のみ編集してください。")
                cur_nut_targets = goals.get("nutrient_targets", {})
                with st.form(key="wm_nutrient_goal_form"):
                    st.markdown("**三大栄養素 (PFC)**")
                    _ng_cols = st.columns(3)
                    _nut_inputs = {}
                    for i, key in enumerate(_PFC_KEYS):
                        info = DEFAULT_NUTRIENT_TARGETS[key]
                        cur_val = cur_nut_targets.get(key, {}).get("target", info["target"]) or 0
                        with _ng_cols[i]:
                            _nut_inputs[key] = st.number_input(
                                f"{info['label']} ({info['unit']})",
                                min_value=0.0, max_value=1000.0,
                                value=float(cur_val), step=5.0,
                                key=f"wm_ng_{key}",
                            )
                    st.markdown("**ビタミン・ミネラル**")
                    _mg_cols = st.columns(3)
                    _micro_display = _MICRO_KEYS + ["salt"]
                    for i, key in enumerate(_micro_display):
                        info = DEFAULT_NUTRIENT_TARGETS[key]
                        default_val = info["target"] if info["target"] else info.get("upper", 0)
                        cur_val = cur_nut_targets.get(key, {}).get("target", default_val) or 0
                        with _mg_cols[i % 3]:
                            _nut_inputs[key] = st.number_input(
                                f"{info['label']} ({info['unit']})",
                                min_value=0.0, max_value=10000.0,
                                value=float(cur_val), step=1.0,
                                key=f"wm_ng_{key}",
                            )
                    nut_goal_submitted = st.form_submit_button("💾 栄養素目標を保存")
                if nut_goal_submitted:
                    new_nut_targets = {}
                    for key, val in _nut_inputs.items():
                        if val > 0:
                            new_nut_targets[key] = {"target": round(val, 1)}
                    goals["nutrient_targets"] = new_nut_targets
                    weight_data["goals"] = goals
                    save_weight_data(weight_data)
                    st.toast("✅ 栄養素目標を保存しました")
                    st.rerun()

            # 推奨カロリー表示（form外に配置）
            if current_weight and cur_target_wt > 0 and cur_target_wt < current_weight:
                remaining_days = (default_target_date - date.today()).days
                if remaining_days > 0:
                    need_loss_kg = current_weight - cur_target_wt
                    daily_deficit = (need_loss_kg * 7200) / remaining_days
                    auto_cal = max(1200, int(2000 - daily_deficit))
                    st.info(
                        f"📐 現在 **{current_weight} kg** → 目標 **{cur_target_wt} kg**"
                        f"（**-{round(need_loss_kg, 1)} kg**）\n\n"
                        f"残り **{remaining_days}日** — 推奨: **{auto_cal} kcal/日**"
                    )


# ===========================================================================
# メインエントリポイント
# ===========================================================================
def main():
    st.set_page_config(
        page_title="Clinical Knowledge Base",
        page_icon="🧸",
        layout="wide",
    )

    # ★ 認証チェック（未認証ならログイン画面のみ表示）
    if not _check_auth():
        return

    # Git自動push開始（バックグラウンド、60秒間隔）
    start_auto_push()

    st.markdown(
        "<link href='https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700&display=swap' rel='stylesheet'>",
        unsafe_allow_html=True,
    )

    # アクティブタブの管理（5タブ構成）
    TAB_NAMES = ["💬 チャット", "📸 画像ライブラリ", "⚡ 取り込み・解析", "⚖️ 体重管理", "⚙️ 設定"]
    if "active_tab" not in st.session_state:
        st.session_state["active_tab"] = TAB_NAMES[0]
    # 旧タブ名からのマイグレーション
    old_tab_map = {
        "💬 チャット検索": TAB_NAMES[0],
        "📸 画像管理": TAB_NAMES[1],
        "📂 手動整理": TAB_NAMES[1],
        "🤖 AI整理": TAB_NAMES[1],
        "⚡ 一括解析": TAB_NAMES[2],
        "🗂️ フォルダ設定": TAB_NAMES[4],
        "🗑️ ゴミ箱": TAB_NAMES[4],
        "⚙️ 設定": TAB_NAMES[4],
    }
    if st.session_state["active_tab"] in old_tab_map:
        st.session_state["active_tab"] = old_tab_map[st.session_state["active_tab"]]

    home_clicked = st.button("🧸 Clinical Knowledge Base", key="home_btn")
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
        st.session_state["active_session_id"] = None
        st.session_state["chat_messages"] = []
        st.session_state.pop("lib_selected_id", None)
        st.session_state.pop("last_upload_id", None)
        st.rerun()

    # ─── サイドバー: ページ切り替え（4ボタンのみ）───
    st.sidebar.markdown("### ページ切り替え")
    for tab_name in TAB_NAMES:
        is_active = st.session_state["active_tab"] == tab_name
        if st.sidebar.button(
            tab_name,
            key=f"tab_btn_{tab_name}",
            width="stretch",
            type="primary" if is_active else "secondary",
        ):
            st.session_state["active_tab"] = tab_name
            st.rerun()

    st.sidebar.markdown("---")

    # ─── サイドバー: 統計サマリー（1行表示）───
    metadata_for_sidebar = load_metadata()
    _ensure_patient_data_folder(metadata_for_sidebar)
    total_count = len(metadata_for_sidebar)
    reviewed_sidebar = sum(
        1 for m in metadata_for_sidebar.values()
        if get_status(m) == STATUS_REVIEWED
    )
    st.sidebar.caption(f"📊 確認済み {reviewed_sidebar} / 全 {total_count} 件")

    # ─── 前回失敗した Sheets 書き込みを再試行 ───
    _retry_pending_saves()

    # ─── サイドバー: 自動取り込み ON/OFF ───
    if "auto_scan_enabled" not in st.session_state:
        st.session_state["auto_scan_enabled"] = True

    auto_scan_val = st.sidebar.toggle(
        "🔄 自動取り込み",
        value=st.session_state["auto_scan_enabled"],
        key="auto_scan_toggle_main",
    )
    st.session_state["auto_scan_enabled"] = auto_scan_val

    if st.sidebar.button("🔄 今すぐスキャン", key="manual_scan", width="stretch"):
        st.session_state["manual_scan_running"] = True
        list_images.clear()
        st.rerun()

    # --- 手動スキャン（リアルタイム進捗表示） ---
    if st.session_state.pop("manual_scan_running", False):
        try:
            _scan_service = get_drive_service()
            _scan_folder_id = get_folder_id()
            _scan_api_key = get_gemini_api_key()
            if _scan_api_key:
                _run_manual_scan(_scan_service, _scan_folder_id, _scan_api_key)
                # 食事画像も同時にスキャン
                _food_fid = get_food_folder_id()
                if _food_fid:
                    _fc = scan_food_images(_scan_service, _food_fid, _scan_api_key, manual=True)
                    if _fc > 0:
                        st.sidebar.success(f"🍽️ 食事画像 {_fc} 枚を取り込みました")
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
            if _food_api_key:
                _food_count = scan_food_images(_food_service, _food_fid, _food_api_key)
                if _food_count > 0:
                    st.toast(f"🔔 {_food_count} 枚の食事画像を自動取り込みしました", icon="📷")
                    st.rerun()
    except Exception as e:
        _log.error(f"[食事画像自動取り込み] エラー: {type(e).__name__}: {e}")

    # ─── ページ表示 ───
    active = st.session_state["active_tab"]
    if active == TAB_NAMES[0]:
        page_chat()
    elif active == TAB_NAMES[1]:
        page_image_library()
    elif active == TAB_NAMES[2]:
        page_import_analyze()
    elif active == TAB_NAMES[3]:
        page_weight_management()
    elif active == TAB_NAMES[4]:
        page_settings_all()



if __name__ == "__main__":
    main()

"""
Clinical Knowledge Base - Phase 4: チャット検索(Q&A)付き画像ビューワー

Google Driveの指定フォルダ内にある医療関連スクリーンショットを
ブラウザ上で閲覧し、Gemini 2.0 Flash で内容を自動解析する。
解析結果はユーザー（医師）が手動で修正・追記し、確定情報として保存できる。
蓄積された知識に対して、チャット形式で自然言語による質問・検索が可能。

認証方式: Google サービスアカウント (Drive API)
AI解析/チャット: Gemini 2.0 Flash (REST API)
"""

import base64
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
from datetime import datetime
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
    "https://www.googleapis.com/auth/drive.readonly",
    "https://www.googleapis.com/auth/spreadsheets",
]
METADATA_PATH = Path(__file__).parent / "metadata.json"
CHAT_SESSIONS_PATH = Path(__file__).parent / "chat_sessions.json"
TRASH_PATH = Path(__file__).parent / "trash.json"
IGNORE_LIST_PATH = Path(__file__).parent / "ignore_list.json"
FOLDERS_PATH = Path(__file__).parent / "folders.json"
UPLOADS_DIR = Path(__file__).parent / "uploads"
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
_SHEETS_WORKSHEETS = ["metadata", "folders", "chat_sessions", "trash"]
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
    """JSONデータをチャンク分割してワークシートに書き込む。"""
    try:
        ws = sh.worksheet(worksheet_name)
        json_str = json.dumps(data, ensure_ascii=False)
        chunks = []
        for i in range(0, len(json_str), _SHEETS_CHUNK_SIZE):
            chunks.append(json_str[i:i + _SHEETS_CHUNK_SIZE])
        if not chunks:
            chunks = ["{}"]
        ws.clear()
        cells = [gspread.Cell(row=idx + 1, col=1, value=chunk)
                 for idx, chunk in enumerate(chunks)]
        ws.update_cells(cells)
        _log.info(f"[Sheets] {worksheet_name}: 書き込み成功 ({len(json_str)} chars, {len(chunks)} chunks)")
        return True
    except Exception as e:
        err_msg = f"{type(e).__name__}: {e}"
        _log.error(f"[Sheets] {worksheet_name} 書き込みエラー: {err_msg}")
        st.session_state["_save_error_detail"] = err_msg
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
    for ck in ["_cache_metadata", "_cache_trash", "_cache_ignore_list", "_cache_folders", "_cache_chat_sessions"]:
        st.session_state.pop(ck, None)
        st.session_state.pop(f"{ck}_ts", None)


# ---------------------------------------------------------------------------
# メタデータ管理
# ---------------------------------------------------------------------------
def load_metadata() -> dict:
    """メタデータを読み込む。session_state → Sheets → ローカルの順。"""
    ck = "_cache_metadata"
    if _is_cache_valid(ck):
        pass  # session_state キャッシュ使用
        return st.session_state[ck]
    # Google Sheets（接続できれば常にSheetsを信頼する）
    sh = get_sheets_client()
    _log.info(f"[load_metadata] get_sheets_client() = {sh is not None}")
    if sh is not None:
        data = _read_json_from_sheet(sh, "metadata")
        _log.info(f"[load_metadata] Sheets data = {data is not None}, entries = {len(data) if data else 0}")
        if data is not None:
            _set_cache(ck, data)
            # ローカルファイルも同期更新
            try:
                with open(METADATA_PATH, "w", encoding="utf-8") as f:
                    json.dump(data, f, ensure_ascii=False, indent=2)
            except IOError:
                pass
            _log.info("[load_metadata] ★ Sheets からデータ返却")
            return data
    # Sheets未接続時のみローカルフォールバック
    _log.info("[load_metadata] ローカルフォールバック使用")
    if METADATA_PATH.exists():
        try:
            with open(METADATA_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                _set_cache(ck, data)
                return data
        except (json.JSONDecodeError, IOError):
            pass
    _set_cache(ck, {})
    return {}


def save_metadata(metadata: dict) -> bool:
    """メタデータを保存する。session_state + Sheets + ローカル（バックアップ）。
    Sheetsへの書き込み成否を返す（未接続の場合もFalse）。"""
    _log.info(f"[save_metadata] 保存開始 entries={len(metadata)}")
    _set_cache("_cache_metadata", metadata)
    sheets_ok = False
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
    return sheets_ok


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
    """指定フォルダ内の画像ファイル一覧を取得する（2分キャッシュ、リトライ付）。"""
    mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
    query = f"'{folder_id}' in parents and ({mime_query}) and trashed=false"
    max_retries = 3
    for attempt in range(max_retries):
        try:
            results = (
                _service.files()
                .list(
                    q=query,
                    fields="files(id, name, mimeType, createdTime, modifiedTime, thumbnailLink)",
                    orderBy="modifiedTime desc",
                    pageSize=100,
                )
                .execute()
            )
            return results.get("files", [])
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
            return []
        except Exception:
            if attempt < max_retries - 1:
                time.sleep(2)
                continue
            st.warning("⚠️ Google Driveとの通信に失敗しました。ページを再読み込みしてください。")
            return []


@st.cache_data(ttl=120, show_spinner="患者データを取得中...")
def list_patient_images(_service, patient_folder_id: str) -> list[dict]:
    """患者データフォルダ内の画像ファイル一覧を取得する（2分キャッシュ）。"""
    mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
    query = f"'{patient_folder_id}' in parents and ({mime_query}) and trashed=false"
    max_retries = 3
    for attempt in range(max_retries):
        try:
            results = (
                _service.files()
                .list(
                    q=query,
                    fields="files(id, name, mimeType, createdTime, modifiedTime, thumbnailLink)",
                    orderBy="modifiedTime desc",
                    pageSize=100,
                )
                .execute()
            )
            return results.get("files", [])
        except HttpError as e:
            if e.resp.status == 404:
                return []
            if attempt < max_retries - 1:
                time.sleep(2)
                continue
            return []
        except Exception:
            if attempt < max_retries - 1:
                time.sleep(2)
                continue
            return []


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


@st.cache_data(ttl=300, show_spinner=False)
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
                        save_metadata(metadata)
                        success_count += 1
                except Exception:
                    continue

            if success_count > 0:
                msg = f"✅ 新着 {success_count} 件を自動登録しました！"
                if classified_count > 0:
                    msg += f"\n（{classified_count} 件をフォルダに自動分類）"
                if remaining > 0:
                    msg += f"\n（残り {remaining} 件は次回スキャン時に処理）"
                scan_placeholder.success(msg)
            else:
                scan_placeholder.empty()


def _run_manual_scan(service, folder_id: str, api_key: str) -> None:
    """手動スキャン: メイン画面にリアルタイム進捗を表示しながら新着画像を解析する。"""
    st.markdown("---")
    st.subheader("🔄 新着画像スキャン")

    status_text = st.empty()
    status_text.info("📡 Google Drive を確認中...")

    # Drive APIで最新一覧を取得
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
    new_images = [img for img in drive_images if img["id"] not in metadata and img["id"] not in ignore]

    if not new_images:
        status_text.success("✅ 新着画像はありません。すべて解析済みです。")
        st.caption(f"Google Drive: {len(drive_images)} 件 / 解析済み: {len(metadata)} 件")
    else:
        status_text.info(
            f"🆕 新着 **{len(new_images)}** 件を検出！ AI解析・自動登録を開始します..."
        )

        # フォルダ一覧を取得（自動分類用）
        folders = load_folders()

        # プログレスバー
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
                    # 自動取り込み: 確認済みとして登録 & フォルダ自動分類
                    result["status"] = STATUS_REVIEWED
                    assigned_folder = _auto_classify_folder(result, api_key, folders)
                    result["folder"] = assigned_folder
                    metadata[fid] = result
                    save_metadata(metadata)
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

        progress_bar.progress(1.0, text="完了！")

        # 結果サマリー
        if success_count > 0:
            status_text.success(
                f"🎉 スキャン完了！ **{success_count}** 件を新しく解析しました"
                + (f"（{fail_count} 件失敗）" if fail_count else "")
            )
            st.balloons()
        else:
            status_text.warning("⚠️ 新着画像の解析に失敗しました。再度お試しください。")

    # --- 患者データフォルダの手動スキャン（AI解析なし） ---
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

        metadata = load_metadata()
        ignore_p = load_ignore_list()
        new_patient = [img for img in patient_images if img["id"] not in metadata and img["id"] not in ignore_p]

        if new_patient:
            # 「患者データ」フォルダが存在しなければ作成
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
                st.success(f"🏥 患者データ {p_count} 件を登録しました（AI解析なし・手動入力用）")


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
        st.success("✅ 登録済み")
    else:
        st.warning("🆕 未登録 — AIが自動生成した情報です。内容を確認・修正してください")

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
                st.caption("ステータス: ✅ 登録済み")
            else:
                st.caption("ステータス: 🆕 未登録")

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
        status = "登録済み" if s == STATUS_REVIEWED else "未登録"
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
                    st.session_state["selected_image_id"] = fid
                    st.session_state["active_tab"] = "📸 画像管理"
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
                    st.session_state["selected_image_id"] = fid
                    st.session_state["active_tab"] = "📸 画像管理"
                    st.rerun()

    # 知識件数バッジ
    st.markdown("")
    st.markdown(
        f"<p style='text-align:center;'>"
        f"<span style='background:#1a3a5c; color:#7eb8da; padding:6px 18px;"
        f"border-radius:20px; font-size:14px;'>"
        f"📚 {knowledge_count}件 の知識が登録済み</span></p>",
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
    st.sidebar.write(f"✅ 登録済み: **{reviewed_count}** 件")

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
        f"📊 全 {total} 件 | 解析済 {analyzed} 件 | ✅登録済み {reviewed_count} 件"
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
                    st.success("✅ 登録済み")
                else:
                    st.warning("🆕 未登録")
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
    st.sidebar.write(f"🆕 未登録: **{len(unreviewed)}** 件")
    st.sidebar.write(f"✅ 登録済み: **{len(reviewed)}** 件")
    if patient_data_images:
        st.sidebar.write(f"🏥 患者データ: **{len(patient_data_images)}** 件")
    st.sidebar.write(f"合計: **{len(images)}** 件")

    # プログレスバー
    if images:
        done_count = len(reviewed)
        progress = done_count / len(images)
        st.sidebar.progress(progress, text=f"登録済み: {done_count}/{len(images)}")

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
        with sel_col1:
            if st.button("☑️ 全選択", key="batch_select_all"):
                for img in unanalyzed:
                    st.session_state[f"batch_sel_{img['id']}"] = True
                st.rerun()
        with sel_col2:
            if st.button("☐ 全解除", key="batch_deselect_all"):
                for img in unanalyzed:
                    st.session_state[f"batch_sel_{img['id']}"] = False
                st.rerun()

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
            ["すべて", "未登録のみ（🆕）", "登録済みのみ（✅）"],
            horizontal=True,
            key="reanalyze_filter",
        )
        if filter_choice == "未登録のみ（🆕）":
            target_list = unreviewed
        elif filter_choice == "登録済みのみ（✅）":
            target_list = reviewed
        else:
            target_list = analyzed_all

        if not target_list:
            st.info("該当する画像がありません。")
            return

        st.info(f"**{len(target_list)} 件**の画像が対象です。除外したい画像のチェックを外してください。")

        rc1, rc2, rc3 = st.columns([1, 1, 3])
        with rc1:
            if st.button("☑️ 全選択", key="reanalyze_sel_all"):
                for img in target_list:
                    st.session_state[f"reanalyze_sel_{img['id']}"] = True
                st.rerun()
        with rc2:
            if st.button("☐ 全解除", key="reanalyze_sel_none"):
                for img in target_list:
                    st.session_state[f"reanalyze_sel_{img['id']}"] = False
                st.rerun()

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
            st.warning("⚠️ 再解析すると現在の解析データ（タイトル・要約・キーワード）が上書きされます。ステータスも未登録に戻ります。")
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
            ["すべて", "未登録のみ（🆕）", "登録済みのみ（✅）"],
            horizontal=True,
            key="hint_reanalyze_filter",
        )
        if hint_filter == "未登録のみ（🆕）":
            hint_target_list = unreviewed
        elif hint_filter == "登録済みのみ（✅）":
            hint_target_list = reviewed
        else:
            hint_target_list = analyzed_all

        if not hint_target_list:
            st.info("該当する画像がありません。")
            return

        st.info(f"**{len(hint_target_list)} 件**の画像が対象です。修正したい画像を選択してください。")

        hc1, hc2, hc3 = st.columns([1, 1, 3])
        with hc1:
            if st.button("☑️ 全選択", key="hint_sel_all"):
                for img in hint_target_list:
                    st.session_state[f"hint_sel_{img['id']}"] = True
                st.rerun()
        with hc2:
            if st.button("☐ 全解除", key="hint_sel_none"):
                for img in hint_target_list:
                    st.session_state[f"hint_sel_{img['id']}"] = False
                st.rerun()

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

        st.info(f"**{len(unreviewed_now)} 件**の未登録画像があります。順番に確認してください。")

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
        st.caption("未登録の画像をまとめて登録済みに変更、または登録済みを未登録に戻せます。")

        metadata = load_metadata()

        # 対象選択
        review_filter = st.radio(
            "対象",
            ["未登録→登録済み（🆕→✅）", "登録済み→未登録に戻す（✅→🆕）"],
            horizontal=True,
            key="bulk_review_filter",
        )

        if review_filter == "未登録→登録済み（🆕→✅）":
            target_list = [
                img for img in images
                if img["id"] in metadata
                and get_status(metadata[img["id"]]) == STATUS_AUTO
            ]
            action_label = "登録済みにする"
            action_key_prefix = "bulkrev"
        else:
            target_list = [
                img for img in images
                if img["id"] in metadata
                and get_status(metadata[img["id"]]) == STATUS_REVIEWED
            ]
            action_label = "未登録に戻す"
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

        if review_filter == "未登録→登録済み（🆕→✅）":
            if st.button(
                f"✅ 選択した {action_count} 件を登録済みにする",
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
                st.success(f"✅ {action_count} 件を登録済みにしました。")
                st.rerun()
        else:
            if st.button(
                f"🆕 選択した {action_count} 件を未登録に戻す",
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
                st.success(f"🆕 {action_count} 件を未登録に戻しました。")
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
        with del_col1:
            if st.button("☑️ 全選択", key="del_select_all"):
                for img in analyzed_images:
                    st.session_state[f"del_sel_{img['id']}"] = True
                st.rerun()
        with del_col2:
            if st.button("☐ 全解除", key="del_deselect_all"):
                for img in analyzed_images:
                    st.session_state[f"del_sel_{img['id']}"] = False
                st.rerun()

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
    act_col1, act_col2, act_col3 = st.columns([1, 1, 4])
    with act_col1:
        if st.button("☑️ 全選択", key="trash_sel_all"):
            for i in range(len(trash)):
                st.session_state[f"trash_sel_{i}"] = True
            st.rerun()
    with act_col2:
        if st.button("☐ 全解除", key="trash_sel_none"):
            for i in range(len(trash)):
                st.session_state.pop(f"trash_sel_{i}", None)
            st.rerun()

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
    mc1, mc2, mc3 = st.columns([1, 1, 4])
    with mc1:
        if st.button("☑️ 全選択", key="mf_sel_all"):
            for img in display_images:
                st.session_state[f"mf_sel_{img['id']}"] = True
            st.rerun()
    with mc2:
        if st.button("☐ 全解除", key="mf_sel_none"):
            for img in display_images:
                st.session_state.pop(f"mf_sel_{img['id']}", None)
            st.rerun()

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
                        st.success("✅ 登録済み")
                    else:
                        st.warning("🆕 未登録")
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
        st.subheader(f"📁 {view_folder}")
        if not folder_images:
            st.info("このフォルダには画像がありません。")
            return

        # ページネーション
        fd_page_items, fd_cur, fd_total_pages = _paginate(folder_images, "ai_folder_grid_page")
        _render_pagination_controls("ai_folder_grid_page", fd_cur, fd_total_pages, len(folder_images))

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
                    # 詳細ボタン
                    if st.button("🔍 詳細を見る", key=f"folder_open_{fid}", width="stretch"):
                        st.session_state["folder_detail_id"] = fid
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

    # --- 📷 画像貼り付け → AI解析して取り込み ---
    with st.expander("📷 画像を貼り付けて取り込む", expanded=False):
        # streamlit-paste-button はCloud環境で動かない場合があるため安全にimport
        paste_result = None
        try:
            from streamlit_paste_button import paste_image_button as pib
            st.markdown("**方法①** スクショをコピーして以下のボタンで貼り付け:")
            paste_result = pib(
                label="📋 クリップボードから画像を貼り付け",
                text_color="#5b8def",
                background_color="transparent",
                hover_background_color="rgba(91,139,239,0.1)",
            )
        except Exception:
            st.caption("📋 クリップボード貼り付けはPC版でのみ利用可能です")

        st.markdown("**方法②** ファイルを選択 / ドラッグ＆ドロップ:")
        uploaded_file = st.file_uploader(
            "画像ファイルを選択",
            type=["png", "jpg", "jpeg"],
            key="chat_image_upload",
            label_visibility="collapsed",
        )

        # 画像データの決定（貼り付け or ファイル選択）
        img_bytes = None
        img_name = "clipboard_image.png"
        if paste_result and paste_result.image_data is not None:
            # クリップボードから貼り付けた画像
            buf = io.BytesIO()
            paste_result.image_data.save(buf, format="PNG")
            img_bytes = buf.getvalue()
            img_name = f"paste_{datetime.now().strftime('%H%M%S')}.png"
        elif uploaded_file is not None:
            img_bytes = uploaded_file.getvalue()
            img_name = uploaded_file.name

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
                        st.markdown("✅ **登録済み**")
                    else:
                        st.markdown("🆕 **未登録**")
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
                        st.session_state["active_tab"] = "📸 画像管理"
                        st.session_state["selected_image_id"] = last_upload_id
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
            "上の📷から画像を取り込むか、「📸 画像管理」タブで画像をAI解析して知識を蓄積してください。"
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

    if migrated:
        st.success(f"✅ 移行完了: {', '.join(migrated)}")
        # キャッシュクリア
        for ck in ["_cache_metadata", "_cache_folders", "_cache_chat_sessions", "_cache_trash"]:
            st.session_state.pop(ck, None)
            st.session_state.pop(f"{ck}_ts", None)
    else:
        st.warning("移行するローカルデータがありませんでした。")


# ===========================================================================
# メインエントリポイント
# ===========================================================================
def main():
    st.set_page_config(
        page_title="Clinical Knowledge Base",
        page_icon="🧸",
        layout="wide",
    )

    # Git自動push開始（バックグラウンド、60秒間隔）
    start_auto_push()

    st.markdown(
        "<link href='https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700&display=swap' rel='stylesheet'>",
        unsafe_allow_html=True,
    )
    # アクティブタブの管理
    TAB_NAMES = ["💬 チャット検索", "📸 画像管理", "⚡ 一括解析", "🗂️ フォルダ設定", "📂 手動整理", "🤖 AI整理", "🗑️ ゴミ箱"]
    if "active_tab" not in st.session_state:
        st.session_state["active_tab"] = TAB_NAMES[0]

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
        st.session_state.pop("ai_view_folder", None)
        st.session_state.pop("folder_detail_id", None)
        st.session_state.pop("last_upload_id", None)
        st.rerun()

    # サイドバー上部にタブ切り替えボタン
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
            # AI整理以外に移動するときはフォルダ表示をリセット
            if tab_name != TAB_NAMES[5]:
                st.session_state["ai_view_folder"] = None
            st.rerun()

    # --- フォルダ一覧（常時表示） ---
    if "ai_view_folder" not in st.session_state:
        st.session_state["ai_view_folder"] = None

    metadata_for_folders = load_metadata()
    # 患者データの folder を自動修正（「未分類」→「患者データ」）
    _ensure_patient_data_folder(metadata_for_folders)
    all_sidebar_folders = get_all_folders_from_metadata(metadata_for_folders)
    folder_counts_sidebar = {}
    for fid, meta in metadata_for_folders.items():
        # ローカルアップロード画像はファイルが存在する場合のみカウント
        if meta.get("source") == "upload":
            exists = any(
                (UPLOADS_DIR / f"{fid}.{ext}").exists()
                for ext in ("png", "jpg", "jpeg")
            )
            if not exists:
                continue
        f = get_folder(meta)
        folder_counts_sidebar[f] = folder_counts_sidebar.get(f, 0) + 1

    if all_sidebar_folders:
        st.sidebar.markdown("### 📁 フォルダ")
        for f in all_sidebar_folders:
            cnt = folder_counts_sidebar.get(f, 0)
            if cnt == 0:
                continue
            is_viewing = (
                st.session_state["active_tab"] == TAB_NAMES[5]
                and st.session_state["ai_view_folder"] == f
            )
            icon_active = "🏥" if f == PATIENT_DATA_FOLDER else "📂"
            icon_normal = "🏥" if f == PATIENT_DATA_FOLDER else "📁"
            label = f"{icon_active} {f}（{cnt}）" if is_viewing else f"{icon_normal} {f}（{cnt}）"
            if st.sidebar.button(
                label,
                key=f"global_folder_{f}",
                width="stretch",
                type="primary" if is_viewing else "secondary",
            ):
                st.session_state["active_tab"] = TAB_NAMES[5]
                st.session_state["ai_view_folder"] = f
                st.session_state.pop("folder_detail_id", None)
                st.rerun()

    st.sidebar.markdown("---")

    # --- 新着画像の自動検知 & AI解析 ---
    if "auto_scan_enabled" not in st.session_state:
        st.session_state["auto_scan_enabled"] = True

    with st.sidebar.expander("⚙️ 自動取り込み設定", expanded=False):
        st.session_state["auto_scan_enabled"] = st.checkbox(
            "新着画像を自動でAI解析",
            value=st.session_state["auto_scan_enabled"],
            key="auto_scan_toggle",
        )
        st.caption(f"Google Driveに追加された画像を{AUTO_SCAN_INTERVAL // 60}分ごとに検知して自動解析します。")
        if st.button("🔄 今すぐスキャン", key="manual_scan", width="stretch"):
            st.session_state["manual_scan_running"] = True
            list_images.clear()
            st.rerun()

    # --- データ同期 ---
    if st.sidebar.button("🔄 データ再読み込み", key="reload_from_sheets", use_container_width=True):
        _invalidate_all_caches()
        st.toast("☁️ Google Sheets から最新データを再読み込みしました")
        st.rerun()

    # --- データ移行ツール（ローカル→Sheets 1回きり） ---
    with st.sidebar.expander("🔧 管理者ツール", expanded=False):
        sh_status = get_sheets_client()
        if sh_status is not None:
            st.success("☁️ Google Sheets: 接続済み")
        else:
            st.warning("☁️ Google Sheets: 未接続")
        if st.button("📤 ローカル → Sheets 移行", key="migrate_to_sheets", width="stretch"):
            _migrate_local_to_sheets()

    # --- 手動スキャン（リアルタイム進捗表示） ---
    if st.session_state.pop("manual_scan_running", False):
        try:
            _scan_service = get_drive_service()
            _scan_folder_id = get_folder_id()
            _scan_api_key = get_gemini_api_key()
            if _scan_api_key:
                _run_manual_scan(_scan_service, _scan_folder_id, _scan_api_key)
        except Exception:
            st.warning("⚠️ スキャン中にエラーが発生しました。")
        st.session_state["auto_scan_last"] = time.time()

    # --- 自動スキャン（バックグラウンド） ---
    elif st.session_state["auto_scan_enabled"]:
        try:
            _scan_service = get_drive_service()
            _scan_folder_id = get_folder_id()
            _scan_api_key = get_gemini_api_key()
            auto_scan_new_images(_scan_service, _scan_folder_id, _scan_api_key)
        except Exception:
            pass

    # 選択されたタブに応じてページを表示
    active = st.session_state["active_tab"]
    if active == TAB_NAMES[0]:
        page_chat()
    elif active == TAB_NAMES[1]:
        page_image_manager()
    elif active == TAB_NAMES[2]:
        page_batch_analyze()
    elif active == TAB_NAMES[3]:
        page_folder_settings()
    elif active == TAB_NAMES[4]:
        page_folder_manual()
    elif active == TAB_NAMES[5]:
        page_folder_ai()
    elif active == TAB_NAMES[6]:
        page_trash()


if __name__ == "__main__":
    main()

"""
pomken 食事画像 自動スキャナ（ヘッドレス版）

Streamlit UI を起動せずに Google Drive 上の食事画像をスキャンして
weight_data.json / Google Sheets に取り込む。

Windows タスクスケジューラから定期実行することで、ブラウザを開いて
いなくても自動取り込みが走る。

実行例:
    python scan_food_images.py
    python scan_food_images.py --max 20
    python scan_food_images.py --quiet
"""
from __future__ import annotations

import argparse
import base64
import io
import json
import logging
import os
import sys
import time
import tomllib
import uuid
from datetime import datetime, date
from pathlib import Path

import requests
from PIL import Image
from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload
import gspread

try:
    import food_search as _fs  # 検索索引（説明文 + 埋め込み）。無くてもスキャンは動く
except Exception:  # pragma: no cover
    _fs = None

# ---------------------------------------------------------------------------
# パス・定数（app.py と同じ場所を参照）
# ---------------------------------------------------------------------------
ROOT = Path(__file__).resolve().parent
SECRETS_PATH = ROOT / ".streamlit" / "secrets.toml"
WEIGHT_DATA_PATH = ROOT / "weight_data.json"
WEIGHT_UPLOADS_DIR = ROOT / "weight_uploads"
FOOD_IMAGES_PROCESSED_PATH = ROOT / "food_images_processed.json"
LOG_PATH = ROOT / "scan_food_images.log"
LOCK_PATH = ROOT / ".scan_food_images.lock"

IMAGE_MIME_TYPES = ["image/jpeg", "image/png"]
SCOPES = [
    "https://www.googleapis.com/auth/drive",
    "https://www.googleapis.com/auth/spreadsheets",
]
SHEETS_CHUNK_SIZE = 49000
DEFAULT_MAX_IMAGES = 30
LOCK_STALE_SECONDS = 30 * 60  # 30分以上前のロックは自動解除
GEMINI_INTER_CALL_DELAY = 1  # 画像間スリープ秒（保険）
GEMINI_429_BACKOFF = (5, 10, 20)  # 429時のリトライ待機（秒）

GEMINI_MODEL = "gemini-2.5-flash"
GEMINI_API_URL = (
    "https://generativelanguage.googleapis.com/v1beta/models/"
    "{model}:generateContent?key={key}"
)

FOOD_ANALYSIS_PROMPT = """あなたは管理栄養士です。この食事の画像（1枚または複数枚）を解析してください。

写っている料理の品目名、推定量、それぞれの推定カロリー（kcal）、および主要栄養素を日本語で出力してください。
複数の画像がある場合は、全ての画像に写っている品目をまとめて1つのリストで出力してください。
JSON以外のテキストは一切含めないでください。

出力形式:
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

【ルール】
- 品目名は日本語で記載
- quantityは「少なめ」「ふつう」「多め」のいずれかで推定
- 量が判断できない場合は「ふつう」とする
- caloriesはquantityを考慮した整数値（kcalの数値のみ、単位は不要）
- 「半量」は標準の約0.5倍、「少なめ」は標準の約0.6倍、「多め」は標準の約1.5倍のカロリー
- 見える範囲の全ての品目を列挙
- total_caloriesはitemsのcaloriesの合計と一致させること
- 飲み物が見える場合はそれも含めること
- 同じ料理が複数画像に写っている場合は重複カウントしないこと
- 全ての栄養素は数値（小数可）で出力。単位は付けない
- quantityに応じて栄養素もスケーリングすること（半量=0.5倍、少なめ=0.6倍、多め=1.5倍）
- 推定が困難な場合は0とする
- 日本食品標準成分表の値を参考に推定すること
- nutrientsオブジェクトは必ず全品目に含めること"""


# ---------------------------------------------------------------------------
# ロガー
# ---------------------------------------------------------------------------
def setup_logger(quiet: bool) -> logging.Logger:
    log = logging.getLogger("food_scan")
    log.setLevel(logging.INFO)
    log.handlers.clear()
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")

    fh = logging.FileHandler(LOG_PATH, encoding="utf-8")
    fh.setFormatter(fmt)
    log.addHandler(fh)

    if not quiet:
        sh = logging.StreamHandler(sys.stdout)
        sh.setFormatter(fmt)
        log.addHandler(sh)
    return log


# ---------------------------------------------------------------------------
# プロセスロック（多重起動防止）
# ---------------------------------------------------------------------------
class ProcessLock:
    def __init__(self, path: Path, log: logging.Logger):
        self.path = path
        self.log = log
        self.acquired = False

    def __enter__(self):
        if self.path.exists():
            try:
                age = time.time() - self.path.stat().st_mtime
                if age < LOCK_STALE_SECONDS:
                    self.log.info(
                        f"既に別プロセスがスキャン中です (lock age={age:.0f}s) — スキップ"
                    )
                    sys.exit(0)
                self.log.warning(
                    f"古いロックを検出 (age={age:.0f}s) — 上書き取得"
                )
            except OSError:
                pass
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                f.write(f"{os.getpid()}\n{datetime.now().isoformat()}\n")
            self.acquired = True
        except OSError as e:
            self.log.error(f"ロック取得失敗: {e}")
            sys.exit(1)
        return self

    def __exit__(self, exc_type, exc, tb):
        if self.acquired:
            try:
                self.path.unlink(missing_ok=True)
            except OSError:
                pass


# ---------------------------------------------------------------------------
# secrets 読み込み
# ---------------------------------------------------------------------------
def load_secrets() -> dict:
    if not SECRETS_PATH.exists():
        raise FileNotFoundError(f"secrets.toml が見つかりません: {SECRETS_PATH}")
    with open(SECRETS_PATH, "rb") as f:
        return tomllib.load(f)


# ---------------------------------------------------------------------------
# Google API クライアント
# ---------------------------------------------------------------------------
def build_drive_service(secrets: dict):
    creds = service_account.Credentials.from_service_account_info(
        secrets["gcp_service_account"], scopes=SCOPES,
    )
    return build("drive", "v3", credentials=creds, cache_discovery=False)


def build_sheets_client(secrets: dict):
    spreadsheet_id = secrets.get("spreadsheet_id", "")
    if not spreadsheet_id:
        return None
    creds = service_account.Credentials.from_service_account_info(
        secrets["gcp_service_account"], scopes=SCOPES,
    )
    gc = gspread.authorize(creds)
    return gc.open_by_key(spreadsheet_id)


# ---------------------------------------------------------------------------
# Sheets I/O（app.py と互換のチャンク形式）
# ---------------------------------------------------------------------------
def read_json_from_sheet(sh, worksheet_name: str, log: logging.Logger):
    if sh is None:
        return None
    try:
        ws = sh.worksheet(worksheet_name)
        all_values = ws.col_values(1)
        if not all_values:
            return None
        return json.loads("".join(all_values))
    except Exception as e:
        log.warning(f"[Sheets] {worksheet_name} 読み込み失敗: {e}")
        return None


def write_json_to_sheet(sh, worksheet_name: str, data, log: logging.Logger) -> bool:
    if sh is None:
        return False
    last_err = ""
    for attempt in range(3):
        try:
            try:
                ws = sh.worksheet(worksheet_name)
            except gspread.exceptions.WorksheetNotFound:
                ws = sh.add_worksheet(title=worksheet_name, rows=100, cols=1)
            json_str = json.dumps(data, ensure_ascii=False)
            chunks = [json_str[i:i + SHEETS_CHUNK_SIZE]
                      for i in range(0, len(json_str), SHEETS_CHUNK_SIZE)] or ["{}"]
            needed_rows = len(chunks) + 5
            if ws.row_count < needed_rows:
                ws.resize(rows=needed_rows, cols=max(ws.col_count, 1))
                time.sleep(1)
            ws.clear()
            time.sleep(0.5)
            cells = [gspread.Cell(row=i + 1, col=1, value=c)
                     for i, c in enumerate(chunks)]
            ws.update_cells(cells)
            log.info(f"[Sheets] {worksheet_name} 書込成功 ({len(json_str)} chars)")
            return True
        except gspread.exceptions.APIError as e:
            status_code = getattr(getattr(e, "response", None), "status_code", 0)
            last_err = f"APIError({status_code}): {e}"
            log.warning(f"[Sheets] {worksheet_name} attempt {attempt+1}: {last_err}")
            if attempt < 2:
                wait = 10 * (attempt + 1) if status_code == 429 else 5 * (attempt + 1)
                time.sleep(wait)
        except Exception as e:
            last_err = f"{type(e).__name__}: {e}"
            log.warning(f"[Sheets] {worksheet_name} attempt {attempt+1}: {last_err}")
            if attempt < 2:
                time.sleep(5 * (attempt + 1))
    log.error(f"[Sheets] {worksheet_name} 書込失敗: {last_err}")
    return False


# ---------------------------------------------------------------------------
# JSON ファイル原子的書き込み
# ---------------------------------------------------------------------------
def atomic_json_write(path: Path, data) -> bool:
    tmp = path.with_suffix(path.suffix + ".tmp")
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        tmp.replace(path)
        return True
    except OSError:
        try:
            tmp.unlink(missing_ok=True)
        except OSError:
            pass
        return False


# ---------------------------------------------------------------------------
# データ読み書き（Sheets+ローカル マージ）
# ---------------------------------------------------------------------------
def load_food_processed(sh, log: logging.Logger) -> dict:
    sheets_data = read_json_from_sheet(sh, "food_processed", log)
    local_data = None
    if FOOD_IMAGES_PROCESSED_PATH.exists():
        try:
            with open(FOOD_IMAGES_PROCESSED_PATH, "r", encoding="utf-8") as f:
                local_data = json.load(f)
        except (json.JSONDecodeError, OSError):
            pass
    if sheets_data is not None and local_data is not None:
        merged = dict(sheets_data)
        for fid, meta in local_data.items():
            merged.setdefault(fid, meta)
        return merged
    return sheets_data or local_data or {}


def save_food_processed(sh, data: dict, log: logging.Logger) -> bool:
    atomic_json_write(FOOD_IMAGES_PROCESSED_PATH, data)
    return write_json_to_sheet(sh, "food_processed", data, log)


def load_weight_data(sh, log: logging.Logger) -> dict:
    default = {"goals": {}, "records": {}}
    sheets_data = read_json_from_sheet(sh, "weight_data", log)
    local_data = None
    if WEIGHT_DATA_PATH.exists():
        try:
            with open(WEIGHT_DATA_PATH, "r", encoding="utf-8") as f:
                local_data = json.load(f)
        except (json.JSONDecodeError, OSError):
            pass

    if sheets_data is not None and local_data is not None:
        merged = dict(sheets_data)
        s_records = merged.setdefault("records", {})
        l_records = local_data.get("records", {})
        for dk, day in l_records.items():
            if dk not in s_records:
                s_records[dk] = day
            else:
                s_ids = {it.get("id") for it in s_records[dk].get("items", []) if it.get("id")}
                for it in day.get("items", []):
                    if it.get("id") and it["id"] not in s_ids:
                        s_records[dk].setdefault("items", []).append(it)
                if not s_records[dk].get("weight") and day.get("weight"):
                    s_records[dk]["weight"] = day["weight"]
                    if day.get("weight_recorded_at"):
                        s_records[dk]["weight_recorded_at"] = day["weight_recorded_at"]
                if day.get("total_calories", 0) > s_records[dk].get("total_calories", 0):
                    s_records[dk]["total_calories"] = day["total_calories"]
        if not merged.get("goals") and local_data.get("goals"):
            merged["goals"] = local_data["goals"]
        return merged
    return sheets_data or local_data or default


def save_weight_data(sh, data: dict, log: logging.Logger) -> bool:
    atomic_json_write(WEIGHT_DATA_PATH, data)
    return write_json_to_sheet(sh, "weight_data", data, log)


# ---------------------------------------------------------------------------
# Drive ヘルパー
# ---------------------------------------------------------------------------
def resolve_food_folder_id(secrets: dict, service, log: logging.Logger) -> str | None:
    fid = secrets.get("food_images_folder_id", "")
    if fid:
        return fid
    parent_id = secrets.get("folder_id", "")
    if not parent_id:
        log.error("folder_id も food_images_folder_id も未設定")
        return None
    try:
        query = (f"'{parent_id}' in parents and name='食事画像' "
                 f"and mimeType='application/vnd.google-apps.folder' and trashed=false")
        results = service.files().list(q=query, fields="files(id)", pageSize=5).execute()
        existing = results.get("files", [])
        if existing:
            log.info(f"食事画像フォルダを発見: {existing[0]['id']}")
            return existing[0]["id"]
    except Exception as e:
        log.warning(f"食事画像フォルダ検索失敗: {e}")
    return None


def download_image(service, file_id: str) -> bytes:
    for attempt in range(3):
        try:
            request = service.files().get_media(fileId=file_id)
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


# ---------------------------------------------------------------------------
# 画像解析
# ---------------------------------------------------------------------------
def extract_exif_datetime(image_bytes: bytes) -> datetime | None:
    try:
        img = Image.open(io.BytesIO(image_bytes))
        exif = img._getexif()
        if exif is None:
            return None
        for tag_id in (36867, 36868):
            dt_str = exif.get(tag_id)
            if dt_str:
                return datetime.strptime(dt_str, "%Y:%m:%d %H:%M:%S")
    except Exception:
        pass
    return None


def guess_meal_type_from_dt(dt: datetime) -> str:
    h = dt.hour
    if 4 <= h < 10:
        return "breakfast"
    if 10 <= h < 15:
        return "lunch"
    if 15 <= h < 21:
        return "dinner"
    return "snack"


def get_day_items(day_data: dict) -> list[dict]:
    if "items" in day_data:
        items = day_data["items"]
    else:
        items = []
        for meal in day_data.get("meals", []):
            meal_images = meal.get("images", [])
            if not meal_images and meal.get("image_id"):
                meal_images = [{"id": meal["image_id"], "ext": meal.get("image_ext", "png")}]
            img = meal_images[0] if meal_images else {}
            for it in meal.get("items", []):
                row = {"name": it["name"], "calories": it["calories"]}
                if img:
                    row["image_id"] = img.get("id", "")
                    row["image_ext"] = img.get("ext", "png")
                items.append(row)
    for it in items:
        it.setdefault("quantity", "ふつう")
    return items


def parse_gemini_json(text: str) -> dict | None:
    text = text.strip()
    if text.startswith("```"):
        lines, inside, out = text.split("\n"), False, []
        for line in lines:
            if line.startswith("```") and not inside:
                inside = True
                continue
            if line.startswith("```") and inside:
                break
            if inside:
                out.append(line)
        text = "\n".join(out)
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        return None


def analyze_food_images(images: list[bytes], api_key: str,
                        log: logging.Logger) -> dict | None:
    try:
        parts = [{"text": FOOD_ANALYSIS_PROMPT}]
        for img_bytes in images:
            pil = Image.open(io.BytesIO(img_bytes))
            fmt = pil.format or "PNG"
            mime = f"image/{fmt.lower()}"
            if mime == "image/jpg":
                mime = "image/jpeg"
            parts.append({
                "inline_data": {
                    "mime_type": mime,
                    "data": base64.b64encode(img_bytes).decode("utf-8"),
                }
            })
    except Exception as e:
        log.warning(f"Gemini 画像準備エラー: {e}")
        return None

    url = GEMINI_API_URL.format(model=GEMINI_MODEL, key=api_key)
    payload = {"contents": [{"parts": parts}]}
    for attempt in range(len(GEMINI_429_BACKOFF) + 1):
        try:
            resp = requests.post(url, json=payload, timeout=120)
            if resp.status_code == 429:
                if attempt < len(GEMINI_429_BACKOFF):
                    wait = GEMINI_429_BACKOFF[attempt]
                    log.warning(
                        f"Gemini 429 (attempt {attempt+1}/{len(GEMINI_429_BACKOFF)+1})"
                        f" — {wait}s 待機後リトライ"
                    )
                    time.sleep(wait)
                    continue
                log.warning("Gemini 429 — リトライ上限到達、次回スキャンに持ち越し")
                return None
            resp.raise_for_status()
            text = resp.json()["candidates"][0]["content"]["parts"][0]["text"]
            result = parse_gemini_json(text)
            if not isinstance(result, dict):
                return None
            if "items" not in result:
                return {"items": []}
            return result
        except requests.RequestException as e:
            log.warning(f"Gemini リクエストエラー (attempt {attempt+1}): {e}")
            if attempt < len(GEMINI_429_BACKOFF):
                time.sleep(GEMINI_429_BACKOFF[attempt])
                continue
            return None
        except Exception as e:
            log.warning(f"Gemini 解析エラー: {e}")
            return None
    return None


# ---------------------------------------------------------------------------
# 中核処理: スキャン
# ---------------------------------------------------------------------------
def scan_food_images(service, sh, food_folder_id: str, api_key: str,
                     max_images: int, log: logging.Logger) -> int:
    """新規食事画像を取り込んで weight_data + Sheets に反映する。"""
    processed = load_food_processed(sh, log)
    log.info(f"処理済みエントリ: {len(processed)}")

    # Drive 一覧
    all_files: list[dict] = []
    try:
        mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
        query = f"'{food_folder_id}' in parents and ({mime_query}) and trashed=false"
        page_token = None
        while True:
            params = dict(
                q=query,
                fields="nextPageToken, files(id, name, mimeType, createdTime, modifiedTime)",
                orderBy="modifiedTime desc",
                pageSize=100,
            )
            if page_token:
                params["pageToken"] = page_token
            results = service.files().list(**params).execute()
            all_files.extend(results.get("files", []))
            page_token = results.get("nextPageToken")
            if not page_token:
                break
    except Exception as e:
        log.error(f"Drive 一覧取得失敗: {e}")
        return 0
    log.info(f"Drive 上の食事画像: {len(all_files)}")

    # 未処理判定: 新規 / error は常に / no_items は24h以上経過
    now_dt = datetime.now()

    def should_include(f: dict) -> bool:
        fid = f["id"]
        entry = processed.get(fid)
        if entry is None:
            return True
        status = entry.get("status")
        if status == "error":
            return True
        if status == "no_items":
            try:
                last = datetime.fromisoformat(entry.get("processed_at", ""))
                return (now_dt - last).total_seconds() >= 86400
            except (ValueError, TypeError):
                return True
        return False

    new_files = [f for f in all_files if should_include(f)]
    if not new_files:
        log.info("新規画像なし")
        return 0

    candidates = len(new_files)
    new_files = new_files[:max_images]
    log.info(f"処理対象: {len(new_files)} / {candidates}")

    weight_data = load_weight_data(sh, log)
    records = weight_data.setdefault("records", {})
    WEIGHT_UPLOADS_DIR.mkdir(exist_ok=True)
    count = 0

    for idx, file_info in enumerate(new_files, 1):
        if idx > 1:
            time.sleep(GEMINI_INTER_CALL_DELAY)  # 無料枠15RPM対策
        file_id = file_info["id"]
        file_name = file_info.get("name", file_id)
        log.info(f"[{idx}/{len(new_files)}] {file_name}")
        try:
            img_bytes = download_image(service, file_id)
            if not img_bytes:
                continue

            photo_dt = extract_exif_datetime(img_bytes)
            if photo_dt is None:
                mod_time = file_info.get("modifiedTime", "")
                if mod_time:
                    try:
                        photo_dt = datetime.fromisoformat(mod_time.replace("Z", "+00:00"))
                    except (ValueError, TypeError):
                        pass
            if photo_dt is None:
                photo_dt = datetime.now()
            date_key = photo_dt.strftime("%Y-%m-%d")

            img_id = f"wm_{uuid.uuid4().hex[:12]}"
            ext = file_name.rsplit(".", 1)[-1].lower() if "." in file_name else "png"
            if ext not in ("jpg", "jpeg", "png"):
                ext = "png"
            (WEIGHT_UPLOADS_DIR / f"{img_id}.{ext}").write_bytes(img_bytes)

            result = analyze_food_images([img_bytes], api_key, log)
            if result is None:
                processed[file_id] = {
                    "date": "",
                    "file_name": file_name,
                    "processed_at": datetime.now().isoformat(),
                    "status": "error",
                    "error": "AI解析に失敗（一時エラー）",
                }
                log.warning(f"  → 一時エラー、次回再試行")
                continue

            items_list = result.get("items") or []
            if items_list:
                day_data = records.setdefault(date_key, {"items": [], "total_calories": 0})
                existing_fids = {x.get("drive_file_id") for x in day_data.get("items", [])}
                if file_id in existing_fids:
                    processed[file_id] = {
                        "date": date_key,
                        "file_name": file_name,
                        "processed_at": datetime.now().isoformat(),
                        "status": "ok",
                    }
                    log.info("  → 既に取り込み済みファイル、processed のみ更新")
                    continue

                meal_type = guess_meal_type_from_dt(photo_dt)
                for it in items_list:
                    day_data.setdefault("items", []).append({
                        "id": f"item_{uuid.uuid4().hex[:12]}",
                        "name": it.get("name", "不明"),
                        "quantity": it.get("quantity", "ふつう"),
                        "calories": it.get("calories", 0),
                        "nutrients": it.get("nutrients", {}),
                        "meal_type": meal_type,
                        "image_id": img_id,
                        "image_ext": ext,
                        "drive_file_id": file_id,
                    })

                all_items = get_day_items(day_data)
                day_data["total_calories"] = sum(it.get("calories", 0) for it in all_items)

                processed[file_id] = {
                    "date": date_key,
                    "file_name": file_name,
                    "processed_at": datetime.now().isoformat(),
                    "status": "ok",
                }
                count += 1
                log.info(f"  → 取り込み成功 ({len(items_list)} 品目, {date_key})")
                # 検索索引（説明文 + 埋め込み）も同時に作る。失敗してもスキャンは続行。
                if _fs is not None:
                    try:
                        time.sleep(GEMINI_INTER_CALL_DELAY)
                        _fs.index_image(img_id, img_bytes, api_key,
                                        extra_names=[it.get("name", "") for it in items_list])
                    except Exception as ix_err:
                        log.warning(f"  → 検索索引の作成失敗（後で build_food_search_index.py で補完可）: {ix_err}")
            else:
                processed[file_id] = {
                    "date": date_key,
                    "file_name": file_name,
                    "processed_at": datetime.now().isoformat(),
                    "status": "no_items",
                }
                log.info("  → 食事と判定されず")
        except Exception as e:
            log.warning(f"  → 失敗: {type(e).__name__}: {e}")
            processed[file_id] = {
                "date": "",
                "file_name": file_name,
                "processed_at": datetime.now().isoformat(),
                "status": "error",
                "error": str(e),
            }

    # 保存。UI と並走している場合に備え、保存直前に最新を再取得してマージする。
    if count > 0:
        latest_wd = load_weight_data(sh, log)
        latest_records = latest_wd.setdefault("records", {})
        for dk, day in records.items():
            if dk not in latest_records:
                latest_records[dk] = day
                continue
            existing_ids = {it.get("id") for it in latest_records[dk].get("items", []) if it.get("id")}
            existing_fids = {it.get("drive_file_id") for it in latest_records[dk].get("items", []) if it.get("drive_file_id")}
            for it in day.get("items", []):
                if it.get("id") in existing_ids:
                    continue
                if it.get("drive_file_id") and it["drive_file_id"] in existing_fids:
                    continue
                latest_records[dk].setdefault("items", []).append(it)
            latest_records[dk]["total_calories"] = sum(
                x.get("calories", 0) for x in get_day_items(latest_records[dk])
            )
        save_weight_data(sh, latest_wd, log)

    latest_processed = load_food_processed(sh, log)
    latest_processed.update(processed)
    save_food_processed(sh, latest_processed, log)
    return count


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main() -> int:
    parser = argparse.ArgumentParser(description="pomken 食事画像の自動スキャナ")
    parser.add_argument("--max", type=int, default=DEFAULT_MAX_IMAGES,
                        help=f"1回で処理する最大画像数 (デフォルト {DEFAULT_MAX_IMAGES})")
    parser.add_argument("--quiet", action="store_true",
                        help="標準出力に進捗を出さない（タスクスケジューラ用）")
    args = parser.parse_args()

    log = setup_logger(args.quiet)
    log.info("=" * 60)
    log.info("食事画像スキャン開始")

    with ProcessLock(LOCK_PATH, log):
        try:
            secrets = load_secrets()
        except Exception as e:
            log.error(f"secrets 読み込み失敗: {e}")
            return 1

        api_key = secrets.get("GOOGLE_API_KEY", "")
        if not api_key or api_key == "YOUR_GEMINI_API_KEY":
            log.error("GOOGLE_API_KEY が未設定です")
            return 1

        try:
            service = build_drive_service(secrets)
        except Exception as e:
            log.error(f"Drive 認証失敗: {e}")
            return 1

        try:
            sh = build_sheets_client(secrets)
        except Exception as e:
            log.warning(f"Sheets 接続失敗（ローカルのみで継続）: {e}")
            sh = None

        food_folder_id = resolve_food_folder_id(secrets, service, log)
        if not food_folder_id:
            log.error("食事画像フォルダIDを解決できませんでした")
            return 1

        try:
            count = scan_food_images(service, sh, food_folder_id, api_key,
                                     args.max, log)
            log.info(f"完了: {count} 枚を取り込み")
            return 0
        except Exception as e:
            log.exception(f"スキャン中に予期せぬエラー: {e}")
            return 1


if __name__ == "__main__":
    sys.exit(main())

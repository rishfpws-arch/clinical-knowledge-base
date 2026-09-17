"""
pomken 食事画像 自動取り込み（ヘッドレス版）

Streamlit UI を起動せずに Google Drive の「食事画像」フォルダをスキャンし、
未取り込みの写真を weight_uploads/ に保存 → Gemini で説明文・品目を索引化
（food_search.py）→ weight_data.json に登録する。

Windows タスクスケジューラ（pomken_food_scan）から定期実行される。
app.py の自動取り込みと同じ処理で、データはローカル JSON のみ（Sheets 同期なし）。
スキャン後にデータファイルを GitHub へ push するので、app.py を開いていなくても
スマホ版（Streamlit Cloud）が更新される。
カロリー・栄養素の推定は 2026-09-14 に廃止（旧版は scan_food_images.py.bak-20260914-full）。

実行例:
    python scan_food_images.py
    python scan_food_images.py --max 20
    python scan_food_images.py --quiet
"""
from __future__ import annotations

import argparse
import io
import json
import logging
import os
import shutil
import subprocess
import sys
import time
import tomllib
import uuid
from datetime import datetime, date
from pathlib import Path

from PIL import Image
from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload

import food_search as fs

ROOT = Path(__file__).resolve().parent
SECRETS_PATH = ROOT / ".streamlit" / "secrets.toml"
WEIGHT_DATA_PATH = ROOT / "weight_data.json"
WEIGHT_UPLOADS_DIR = ROOT / "weight_uploads"
THUMB_CACHE_DIR = ROOT / ".thumb_cache"
BACKUP_DIR = ROOT / "backups"
FOOD_IMAGES_PROCESSED_PATH = ROOT / "food_images_processed.json"
LOG_PATH = ROOT / "scan_food_images.log"
LOCK_PATH = ROOT / ".scan_food_images.lock"

IMAGE_MIME_TYPES = ["image/jpeg", "image/png"]
SCOPES = ["https://www.googleapis.com/auth/drive"]
DEFAULT_MAX_IMAGES = 30
LOCK_STALE_SECONDS = 30 * 60
INTER_CALL_DELAY = 1.0
BACKUP_KEEP = 7
GIT_DATA_FILES = ["weight_data.json", "food_images_processed.json",
                  "food_search_index.json", "food_search_embeddings.npz"]


# ---------------------------------------------------------------------------
# ロガー・ロック
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
    fs._log.handlers = log.handlers
    fs._log.setLevel(logging.INFO)
    return log


class ProcessLock:
    def __init__(self, path: Path, log: logging.Logger):
        self.path, self.log, self.acquired = path, log, False

    def __enter__(self):
        if self.path.exists():
            age = time.time() - self.path.stat().st_mtime
            if age < LOCK_STALE_SECONDS:
                self.log.warning("別のスキャンが実行中です（ロック %d 秒前）。終了。", int(age))
                return self
            self.log.warning("古いロック（%d 秒前）を解除します。", int(age))
        self.path.write_text(str(os.getpid()), encoding="utf-8")
        self.acquired = True
        return self

    def __exit__(self, *exc):
        if self.acquired:
            try:
                self.path.unlink()
            except OSError:
                pass


# ---------------------------------------------------------------------------
# 設定・Drive
# ---------------------------------------------------------------------------
def load_secrets() -> dict:
    if not SECRETS_PATH.exists():
        raise FileNotFoundError(f"secrets.toml が見つかりません: {SECRETS_PATH}")
    with open(SECRETS_PATH, "rb") as f:
        return tomllib.load(f)


def build_drive_service(secrets: dict):
    creds = service_account.Credentials.from_service_account_info(
        secrets["gcp_service_account"], scopes=SCOPES)
    return build("drive", "v3", credentials=creds, cache_discovery=False)


def download_image(service, file_id: str) -> bytes:
    for attempt in range(3):
        try:
            req = service.files().get_media(fileId=file_id)
            buf = io.BytesIO()
            dl = MediaIoBaseDownload(buf, req)
            done = False
            while not done:
                _, done = dl.next_chunk()
            return buf.getvalue()
        except Exception:
            if attempt < 2:
                time.sleep(2)
                continue
            raise
    return b""


def resolve_food_folder_id(secrets: dict, service, log: logging.Logger) -> str | None:
    """トップレベル → [gcp_service_account] 内（旧版が末尾に追記）→ Drive 検索の順。"""
    fid = (secrets.get("food_images_folder_id")
           or (secrets.get("gcp_service_account") or {}).get("food_images_folder_id")
           or "")
    if fid:
        return fid
    parent = secrets.get("folder_id", "")
    if not parent:
        return None
    try:
        q = (f"'{parent}' in parents and name='食事画像' "
             f"and mimeType='application/vnd.google-apps.folder' and trashed=false")
        res = service.files().list(q=q, fields="files(id)", pageSize=5).execute()
        files = res.get("files", [])
        if files:
            log.info("食事画像フォルダを発見: %s", files[0]["id"])
            return files[0]["id"]
    except Exception as e:
        log.warning("食事画像フォルダ検索失敗: %s", e)
    return None


def list_food_files(service, folder_id: str) -> list[dict]:
    mime_query = " or ".join(f"mimeType='{mt}'" for mt in IMAGE_MIME_TYPES)
    query = f"'{folder_id}' in parents and ({mime_query}) and trashed=false"
    files: list[dict] = []
    token = None
    while True:
        params = dict(q=query, orderBy="modifiedTime desc", pageSize=100,
                      fields="nextPageToken, files(id, name, mimeType, createdTime, modifiedTime)")
        if token:
            params["pageToken"] = token
        res = service.files().list(**params).execute()
        files.extend(res.get("files", []))
        token = res.get("nextPageToken")
        if not token:
            break
    return files


# ---------------------------------------------------------------------------
# ローカル JSON
# ---------------------------------------------------------------------------
def load_json(path: Path, default):
    if not path.exists():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return default


def atomic_json_write(path: Path, data) -> None:
    tmp = path.with_suffix(".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.flush()
        os.fsync(f.fileno())
    for i in range(6):  # Streamlit が読んでいる瞬間の PermissionError を待って再試行
        try:
            os.replace(tmp, path)
            return
        except PermissionError:
            if i == 5:
                raise
            time.sleep(0.3 * (i + 1))


def daily_backup(path: Path) -> None:
    try:
        if not path.exists():
            return
        BACKUP_DIR.mkdir(exist_ok=True)
        dst = BACKUP_DIR / f"{path.stem}-{date.today().strftime('%Y%m%d')}{path.suffix}"
        if dst.exists():
            return
        shutil.copy2(path, dst)
        for p in sorted(BACKUP_DIR.glob(f"{path.stem}-*{path.suffix}"))[:-BACKUP_KEEP]:
            p.unlink(missing_ok=True)
    except OSError:
        pass


# ---------------------------------------------------------------------------
# 画像
# ---------------------------------------------------------------------------
def extract_exif_datetime(image_bytes: bytes) -> datetime | None:
    try:
        exif = Image.open(io.BytesIO(image_bytes))._getexif()
        if not exif:
            return None
        for tag in (36867, 36868):
            v = exif.get(tag)
            if v:
                return datetime.strptime(v, "%Y:%m:%d %H:%M:%S")
    except (AttributeError, ValueError, OSError):
        pass
    return None


def save_thumb(image_id: str, raw: bytes) -> None:
    try:
        THUMB_CACHE_DIR.mkdir(exist_ok=True)
        p = THUMB_CACHE_DIR / f"food_{image_id}.jpg"
        if p.exists():
            return
        img = Image.open(io.BytesIO(raw))
        img.thumbnail((400, 400))
        buf = io.BytesIO()
        img.convert("RGB").save(buf, format="JPEG", quality=70, optimize=True)
        p.write_bytes(buf.getvalue())
    except Exception:
        pass


# ---------------------------------------------------------------------------
# スキャン本体
# ---------------------------------------------------------------------------
def scan(service, folder_id: str, api_key: str, max_images: int, log: logging.Logger) -> int:
    processed = load_json(FOOD_IMAGES_PROCESSED_PATH, {})
    if not isinstance(processed, dict):
        processed = {}
    files = list_food_files(service, folder_id)
    new_files = [f for f in files if f["id"] not in processed]
    log.info("Drive 画像 %d 件 / 未処理 %d 件", len(files), len(new_files))
    if not new_files:
        return 0
    new_files = new_files[:max_images]

    weight_data = load_json(WEIGHT_DATA_PATH, {"goals": {}, "records": {}})
    if not isinstance(weight_data, dict):
        weight_data = {"goals": {}, "records": {}}
    records = weight_data.setdefault("records", {})
    WEIGHT_UPLOADS_DIR.mkdir(exist_ok=True)

    count = 0
    for idx, info in enumerate(new_files, 1):
        if idx > 1:
            time.sleep(INTER_CALL_DELAY)
        file_id = info["id"]
        name = info.get("name", file_id)
        log.info("[%d/%d] %s", idx, len(new_files), name)
        try:
            raw = download_image(service, file_id)
            if not raw:
                continue
            dt = extract_exif_datetime(raw)
            if dt is None and info.get("modifiedTime"):
                try:
                    dt = datetime.fromisoformat(info["modifiedTime"].replace("Z", "+00:00"))
                except (ValueError, TypeError):
                    dt = None
            if dt is None:
                dt = datetime.now()
            date_key = dt.strftime("%Y-%m-%d")

            img_id = f"wm_{uuid.uuid4().hex[:12]}"
            ext = name.rsplit(".", 1)[-1].lower() if "." in name else "png"
            if ext not in ("jpg", "jpeg", "png"):
                ext = "png"
            (WEIGHT_UPLOADS_DIR / f"{img_id}.{ext}").write_bytes(raw)
            save_thumb(img_id, raw)

            day = records.setdefault(date_key, {"items": []})
            if file_id in {x.get("drive_file_id") for x in day.get("items", [])}:
                processed[file_id] = {"date": date_key, "file_name": name,
                                      "processed_at": datetime.now().isoformat(), "status": "ok"}
                log.info("  → 既に取り込み済み、processed のみ更新")
                continue

            items: list[str] = []
            try:
                entry = fs.index_image(img_id, raw, api_key)
                if entry:
                    items = list(entry.get("items") or [])
            except fs.GeminiRateLimited as e:
                log.error("  → レート制限。次回再試行: %s", e)
                (WEIGHT_UPLOADS_DIR / f"{img_id}.{ext}").unlink(missing_ok=True)
                break
            except Exception as e:
                log.warning("  → 索引作成失敗（写真は登録、後で「🧠 索引」で補完可）: %s", e)

            day.setdefault("items", []).append({
                "id": f"item_{uuid.uuid4().hex[:12]}",
                "name": "・".join(items) if items else name,
                "items_extracted": items,
                "image_id": img_id,
                "image_ext": ext,
                "drive_file_id": file_id,
            })
            processed[file_id] = {"date": date_key, "file_name": name,
                                  "processed_at": datetime.now().isoformat(), "status": "ok"}
            count += 1
            log.info("  → 取り込み成功 (%s) %s", date_key, "、".join(items)[:60] or "(品目なし)")
        except Exception as e:
            log.warning("  → 失敗: %s: %s", type(e).__name__, e)
            processed[file_id] = {"date": "", "file_name": name,
                                  "processed_at": datetime.now().isoformat(),
                                  "status": "error", "error": str(e)}

    if count > 0:
        # UI と並走している場合に備え、保存直前に最新を読み直してマージする
        latest = load_json(WEIGHT_DATA_PATH, {"goals": {}, "records": {}})
        lrec = latest.setdefault("records", {}) if isinstance(latest, dict) else {}
        for dk, day in records.items():
            if dk not in lrec:
                lrec[dk] = day
                continue
            have_ids = {it.get("id") for it in lrec[dk].get("items", [])}
            have_fids = {it.get("drive_file_id") for it in lrec[dk].get("items", [])}
            for it in day.get("items", []):
                if it.get("id") in have_ids or it.get("drive_file_id") in have_fids:
                    continue
                lrec[dk].setdefault("items", []).append(it)
        daily_backup(WEIGHT_DATA_PATH)
        atomic_json_write(WEIGHT_DATA_PATH, latest if isinstance(latest, dict) else weight_data)

    latest_processed = load_json(FOOD_IMAGES_PROCESSED_PATH, {})
    if not isinstance(latest_processed, dict):
        latest_processed = {}
    latest_processed.update(processed)
    atomic_json_write(FOOD_IMAGES_PROCESSED_PATH, latest_processed)
    return count


# ---------------------------------------------------------------------------
# GitHub へ push（スマホ版 = Streamlit Cloud は GitHub main しか見ない）
# ---------------------------------------------------------------------------
def _git(args: list[str], timeout: int = 60) -> subprocess.CompletedProcess:
    return subprocess.run(["git"] + args, cwd=str(ROOT), capture_output=True, text=True,
                          encoding="utf-8", errors="replace", timeout=timeout,
                          creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))


def push_data(log: logging.Logger) -> None:
    """データファイルの変更を commit & push する。app.py を開いていなくてもスマホ版が更新される。
    コードは対象外（app.py 側の自動 push に任せる）。失敗しても次回のスキャンで再試行される。"""
    if not (ROOT / ".git").exists():
        return
    try:
        files = [f for f in GIT_DATA_FILES if (ROOT / f).exists()]
        if _git(["status", "--porcelain", "--"] + files).stdout.strip():
            _git(["add", "--"] + files)
            ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            r = _git(["commit", "-m", f"auto(scan): {ts}", "--"] + files)
            if r.returncode != 0:
                log.warning("git commit 失敗: %s", (r.stderr or r.stdout).strip()[:300])
                return
        # 前回 push に失敗した分も含め、未送信の commit があれば送る
        ahead = _git(["rev-list", "--count", "origin/main..HEAD"]).stdout.strip()
        if ahead in ("", "0"):
            return
        r = _git(["push", "origin", "main"], timeout=120)
        if r.returncode == 0:
            log.info("GitHub へ push 完了（%s commit）", ahead)
        else:
            log.warning("git push 失敗（次回再試行）: %s", (r.stderr or r.stdout).strip()[:300])
    except Exception as e:
        log.warning("git push エラー: %s: %s", type(e).__name__, e)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=DEFAULT_MAX_IMAGES)
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    log = setup_logger(args.quiet)

    with ProcessLock(LOCK_PATH, log) as lock:
        if not lock.acquired:
            return 2
        try:
            secrets = load_secrets()
            api_key = secrets.get("GOOGLE_API_KEY") or ""
            if not api_key or api_key == "YOUR_GEMINI_API_KEY":
                log.error("secrets.toml に GOOGLE_API_KEY がありません")
                return 1
            service = build_drive_service(secrets)
            folder_id = resolve_food_folder_id(secrets, service, log)
            if not folder_id:
                log.error("食事画像フォルダが見つかりません（food_images_folder_id / folder_id）")
                return 1
            started = time.time()
            n = scan(service, folder_id, api_key, args.max, log)
            log.info("完了: %d 枚取り込み (%.0f 秒)", n, time.time() - started)
            push_data(log)
            return 0
        except Exception as e:
            log.exception("スキャン失敗: %s", e)
            return 1


if __name__ == "__main__":
    sys.exit(main())

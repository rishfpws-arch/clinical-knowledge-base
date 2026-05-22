"""Pomken の Google Sheets メタデータと Drive 画像を Book Capture の Cloudflare R2/D1 に同期する。

GitHub Actions から定期実行される。state は D1 の content_hash カラムで管理するので
state ファイル不要。Book Capture リポジトリの src/pomken_sync.py と同等のロジックを
Sheets ソース + 環境変数認証で再構成したもの。

環境変数:
    GSHEETS_SPREADSHEET_ID   - Pomken の metadata が保存された Spreadsheet ID
    GCP_SERVICE_ACCOUNT_JSON - サービスアカウント JSON 全体 (Sheets + Drive 読み取り権限)
    R2_ENDPOINT              - https://<account>.r2.cloudflarestorage.com
    R2_ACCESS_KEY_ID         - R2 access key
    R2_SECRET_ACCESS_KEY     - R2 secret key
    R2_BUCKET                - book-capture-images
    CF_ACCOUNT_ID            - Cloudflare account ID
    CF_D1_DATABASE_ID        - book-capture-fts database ID
    CF_API_TOKEN             - D1:Edit 権限の API token

CLI:
    python scripts/cloud_sync_from_sheets.py
    python scripts/cloud_sync_from_sheets.py --dry-run --verbose
    python scripts/cloud_sync_from_sheets.py --high-res 1600
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import logging
import os
import re
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Any

logger = logging.getLogger(__name__)

DRIVE_SCOPES = [
    "https://www.googleapis.com/auth/spreadsheets.readonly",
    "https://www.googleapis.com/auth/drive.readonly",
]

# D1 REST API は 1 リクエスト当たりのレスポンスサイズに上限がある。
# ページング前提で取得する。
D1_SELECT_PAGE = 1000


# ---------------------------------------------------------------------------
# データクラス
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class PomkenEntry:
    fid: str
    title: str
    keywords: list[str]
    folder: str
    summary: str
    ocr_text: str
    status: str
    content_hash: str

    @property
    def image_key(self) -> str:
        return f"pomken/{self.fid}.jpg"

    @property
    def r2_key(self) -> str:
        return f"images/{self.image_key}"


# ---------------------------------------------------------------------------
# ユーティリティ
# ---------------------------------------------------------------------------
def _normalize_keywords(v: Any) -> list[str]:
    if v is None:
        return []
    if isinstance(v, list):
        return [str(x).strip() for x in v if x is not None and str(x).strip()]
    if isinstance(v, dict):
        return [str(x).strip() for x in v.values() if x is not None and str(x).strip()]
    if isinstance(v, str):
        return [s.strip() for s in v.replace("、", ",").split(",") if s.strip()]
    return [str(v).strip()]


def _content_hash(meta: dict) -> str:
    parts = [
        str(meta.get("title", "")),
        str(meta.get("summary", "")),
        json.dumps(
            _normalize_keywords(meta.get("keywords")),
            sort_keys=True,
            ensure_ascii=False,
        ),
        str(meta.get("ocr_text", "")),
        str(meta.get("folder", "")),
        str(meta.get("status", "")),
    ]
    return hashlib.sha256("\x00".join(parts).encode("utf-8")).hexdigest()


def _is_valid_fid(fid: str) -> bool:
    return bool(fid) and bool(re.match(r"^[A-Za-z0-9_-]+$", fid))


def build_entries(metadata: dict[str, dict]) -> list[PomkenEntry]:
    entries: list[PomkenEntry] = []
    for fid, m in metadata.items():
        if not isinstance(m, dict):
            continue
        if not _is_valid_fid(fid):
            logger.warning("skip invalid fid: %r", fid)
            continue
        entries.append(PomkenEntry(
            fid=fid,
            title=str(m.get("title", "")),
            keywords=_normalize_keywords(m.get("keywords")),
            folder=str(m.get("folder", "")),
            summary=str(m.get("summary", "")),
            ocr_text=str(m.get("ocr_text", "")),
            status=str(m.get("status", "")),
            content_hash=_content_hash(m),
        ))
    return entries


# ---------------------------------------------------------------------------
# Google Sheets / Drive
# ---------------------------------------------------------------------------
def load_metadata_from_sheets(spreadsheet_id: str, creds_info: dict) -> dict[str, dict]:
    """Sheets の "metadata" worksheet の A 列を結合して JSON 復元。app.py:381 と同等。"""
    import gspread
    from google.oauth2 import service_account

    creds = service_account.Credentials.from_service_account_info(creds_info, scopes=DRIVE_SCOPES)
    gc = gspread.authorize(creds)
    sh = gc.open_by_key(spreadsheet_id)
    ws = sh.worksheet("metadata")
    all_values = ws.col_values(1)
    if not all_values:
        raise RuntimeError("Sheets 'metadata' worksheet is empty")
    json_str = "".join(all_values)
    data = json.loads(json_str)
    if not isinstance(data, dict):
        raise RuntimeError("Sheets metadata top-level must be a dict")
    return data


def fetch_drive_image(
    fid: str,
    creds_info: dict,
    max_px: int | None = 1600,
    quality: int = 88,
) -> tuple[bytes, str] | None:
    """Drive から画像を取得。max_px 指定時は Pillow でリサイズ。
    Pomken の app.py:1443 download_image と同等 + リサイズ。"""
    from googleapiclient.discovery import build
    from googleapiclient.http import MediaIoBaseDownload
    from google.oauth2 import service_account

    try:
        creds = service_account.Credentials.from_service_account_info(creds_info, scopes=DRIVE_SCOPES)
        service = build("drive", "v3", credentials=creds, cache_discovery=False)
        request = service.files().get_media(fileId=fid)
        buf = io.BytesIO()
        downloader = MediaIoBaseDownload(buf, request)
        done = False
        while not done:
            _, done = downloader.next_chunk()
        raw = buf.getvalue()
    except Exception as e:
        logger.warning("Drive fetch failed for fid=%s: %s", fid, e)
        return None

    if max_px is None:
        return raw, "image/jpeg"

    try:
        from PIL import Image
        img = Image.open(io.BytesIO(raw))
        img.thumbnail((max_px, max_px))
        out = io.BytesIO()
        img.convert("RGB").save(out, format="JPEG", quality=quality, optimize=True)
        return out.getvalue(), "image/jpeg"
    except Exception as e:
        logger.warning("resize failed for fid=%s: %s (returning raw)", fid, e)
        return raw, "image/jpeg"


# ---------------------------------------------------------------------------
# Cloudflare R2 / D1
# ---------------------------------------------------------------------------
def make_s3_client(endpoint: str, access_key: str, secret_key: str):
    import boto3
    return boto3.client(
        "s3",
        endpoint_url=endpoint,
        aws_access_key_id=access_key,
        aws_secret_access_key=secret_key,
        region_name="auto",
    )


def _d1_query(cf_account_id: str, db_id: str, api_token: str, sql: str, params: list | None = None) -> dict:
    url = f"https://api.cloudflare.com/client/v4/accounts/{cf_account_id}/d1/database/{db_id}/query"
    body = json.dumps({"sql": sql, "params": params or []}).encode("utf-8")
    req = urllib.request.Request(
        url, data=body, method="POST",
        headers={
            "Authorization": f"Bearer {api_token}",
            "Content-Type": "application/json",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"D1 HTTP {e.code}: {err_body[:500]}") from e
    if not payload.get("success"):
        raise RuntimeError(f"D1 error: {payload.get('errors')}")
    return payload


def fetch_d1_state(cf_account_id: str, db_id: str, api_token: str) -> dict[str, str]:
    """D1 から (fid, content_hash) を全件取得。ページング対応。"""
    state: dict[str, str] = {}
    offset = 0
    while True:
        sql = f"SELECT fid, content_hash FROM pomken_pages LIMIT {D1_SELECT_PAGE} OFFSET {offset}"
        payload = _d1_query(cf_account_id, db_id, api_token, sql)
        rows = payload.get("result", [{}])[0].get("results", [])
        if not rows:
            break
        for r in rows:
            state[r["fid"]] = r.get("content_hash", "")
        if len(rows) < D1_SELECT_PAGE:
            break
        offset += D1_SELECT_PAGE
    return state


def upload_image_to_r2(s3, bucket: str, entry: PomkenEntry, image_bytes: bytes, content_type: str) -> bool:
    try:
        s3.put_object(Bucket=bucket, Key=entry.r2_key, Body=image_bytes, ContentType=content_type)
        return True
    except Exception as e:
        logger.error("R2 upload failed for %s: %s", entry.r2_key, e)
        return False


def upsert_d1(cf_account_id: str, db_id: str, api_token: str, entry: PomkenEntry) -> bool:
    sql = (
        "INSERT INTO pomken_pages "
        "(fid, image_key, title, keywords, folder, summary, ocr_text, status, content_hash, synced_at) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, datetime('now')) "
        "ON CONFLICT(fid) DO UPDATE SET "
        "  image_key=excluded.image_key, "
        "  title=excluded.title, "
        "  keywords=excluded.keywords, "
        "  folder=excluded.folder, "
        "  summary=excluded.summary, "
        "  ocr_text=excluded.ocr_text, "
        "  status=excluded.status, "
        "  content_hash=excluded.content_hash, "
        "  synced_at=datetime('now')"
    )
    params = [
        entry.fid,
        entry.image_key,
        entry.title,
        json.dumps(entry.keywords, ensure_ascii=False),
        entry.folder,
        entry.summary,
        entry.ocr_text,
        entry.status,
        entry.content_hash,
    ]
    try:
        _d1_query(cf_account_id, db_id, api_token, sql, params)
        return True
    except Exception as e:
        logger.error("D1 upsert failed for fid=%s: %s", entry.fid, e)
        return False


def delete_from_d1(cf_account_id: str, db_id: str, api_token: str, fid: str) -> bool:
    try:
        _d1_query(cf_account_id, db_id, api_token, "DELETE FROM pomken_pages WHERE fid = ?", [fid])
        return True
    except Exception as e:
        logger.warning("D1 delete failed for fid=%s: %s", fid, e)
        return False


def delete_from_r2(s3, bucket: str, fid: str) -> bool:
    try:
        s3.delete_object(Bucket=bucket, Key=f"images/pomken/{fid}.jpg")
        return True
    except Exception as e:
        logger.warning("R2 delete failed for fid=%s: %s", fid, e)
        return False


# ---------------------------------------------------------------------------
# 環境変数
# ---------------------------------------------------------------------------
def _require_env(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise RuntimeError(f"missing required env var: {name}")
    return v


def _load_env() -> dict:
    creds_json = _require_env("GCP_SERVICE_ACCOUNT_JSON")
    try:
        creds_info = json.loads(creds_json)
    except json.JSONDecodeError as e:
        raise RuntimeError(f"GCP_SERVICE_ACCOUNT_JSON is not valid JSON: {e}") from e
    return {
        "spreadsheet_id": _require_env("GSHEETS_SPREADSHEET_ID"),
        "creds_info": creds_info,
        "r2_endpoint": _require_env("R2_ENDPOINT"),
        "r2_access_key_id": _require_env("R2_ACCESS_KEY_ID"),
        "r2_secret_access_key": _require_env("R2_SECRET_ACCESS_KEY"),
        "r2_bucket": _require_env("R2_BUCKET"),
        "cf_account_id": _require_env("CF_ACCOUNT_ID"),
        "cf_d1_database_id": _require_env("CF_D1_DATABASE_ID"),
        "cf_api_token": _require_env("CF_API_TOKEN"),
    }


# ---------------------------------------------------------------------------
# メイン同期処理
# ---------------------------------------------------------------------------
def sync(env: dict, *, dry_run: bool = False, high_res_max_px: int = 1600, high_res_quality: int = 88) -> tuple[int, int, int]:
    started = time.time()
    logger.info("loading metadata from Sheets (spreadsheet_id=%s)...", env["spreadsheet_id"][:8] + "...")
    metadata = load_metadata_from_sheets(env["spreadsheet_id"], env["creds_info"])
    entries = build_entries(metadata)
    logger.info("loaded %d entries from Sheets (%.1fs)", len(entries), time.time() - started)

    logger.info("fetching D1 state...")
    d1_state = fetch_d1_state(env["cf_account_id"], env["cf_d1_database_id"], env["cf_api_token"])
    logger.info("D1 has %d existing rows", len(d1_state))

    s3 = None if dry_run else make_s3_client(
        env["r2_endpoint"], env["r2_access_key_id"], env["r2_secret_access_key"]
    )
    bucket = env["r2_bucket"]

    uploaded = 0
    indexed = 0
    skipped = 0
    failed_images: list[str] = []

    for entry in entries:
        prev_hash = d1_state.get(entry.fid)
        if prev_hash == entry.content_hash:
            skipped += 1
            continue

        is_new = prev_hash is None
        action = "new" if is_new else "updated"
        logger.info("[%s] fid=%s title=%s", action, entry.fid, entry.title[:50])

        img = fetch_drive_image(entry.fid, env["creds_info"], max_px=high_res_max_px, quality=high_res_quality)
        if img is None:
            failed_images.append(entry.fid)
            continue

        if dry_run:
            logger.info("  [dry-run] would upload R2 %s (%d bytes) + upsert D1", entry.r2_key, len(img[0]))
            uploaded += 1
            indexed += 1
            continue

        if upload_image_to_r2(s3, bucket, entry, img[0], img[1]):
            uploaded += 1
        if upsert_d1(env["cf_account_id"], env["cf_d1_database_id"], env["cf_api_token"], entry):
            indexed += 1

        if uploaded > 0 and uploaded % 20 == 0:
            logger.info("progress: R2 +%d / D1 +%d / skipped %d", uploaded, indexed, skipped)

    # 削除検知: D1 にあるが Sheets にない fid
    current_fids = {e.fid for e in entries}
    deleted_fids = set(d1_state.keys()) - current_fids
    deleted = 0
    for fid in deleted_fids:
        logger.info("[delete] fid=%s", fid)
        if dry_run:
            deleted += 1
            continue
        delete_from_d1(env["cf_account_id"], env["cf_d1_database_id"], env["cf_api_token"], fid)
        delete_from_r2(s3, bucket, fid)
        deleted += 1

    if failed_images:
        logger.warning(
            "%d image(s) failed Drive fetch: %s%s",
            len(failed_images),
            ", ".join(failed_images[:5]),
            "..." if len(failed_images) > 5 else "",
        )

    elapsed = time.time() - started
    logger.info(
        "sync done in %.1fs: R2 +%d / D1 +%d / skipped %d / deleted %d / failed %d",
        elapsed, uploaded, indexed, skipped, deleted, len(failed_images),
    )
    return uploaded, indexed, deleted


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--dry-run", action="store_true", help="実際の書き込みを行わずログのみ")
    p.add_argument("--high-res", type=int, default=1600, metavar="MAX_PX",
                   help="Drive から取得後のリサイズ上限 (既定 1600)")
    p.add_argument("--high-res-quality", type=int, default=88,
                   help="JPEG quality (1-100, 既定 88)")
    p.add_argument("-v", "--verbose", action="store_true")
    args = p.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )
    for noisy in ("boto3", "botocore", "urllib3", "s3transfer", "googleapiclient"):
        logging.getLogger(noisy).setLevel(logging.WARNING)

    try:
        env = _load_env()
    except RuntimeError as e:
        logger.error(str(e))
        return 2

    try:
        sync(env, dry_run=args.dry_run, high_res_max_px=args.high_res, high_res_quality=args.high_res_quality)
    except Exception as e:
        logger.exception("sync failed: %s", e)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

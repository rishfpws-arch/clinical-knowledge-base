"""
pomken 食事画像 検索インデックス バックフィル（ヘッドレス）

weight_data.json に登録済みの食事画像のうち、まだ食事検索インデックス
（food_search_index.json / food_search_embeddings.npz）に無いものを
Gemini で説明文化 → 埋め込みして登録する。何度実行しても未処理分だけ進む。

実行例:
    python build_food_search_index.py            # 未処理をすべて
    python build_food_search_index.py --max 10   # お試し 10 枚
    python build_food_search_index.py --embed-only   # 説明済み・未埋め込み分のみ
    python build_food_search_index.py --force --max 5  # 既存も作り直す
"""
from __future__ import annotations

import argparse
import io
import json
import logging
import sys
import time
import tomllib
from pathlib import Path

from PIL import Image

import food_search as fs

ROOT = Path(__file__).resolve().parent
SECRETS_PATH = ROOT / ".streamlit" / "secrets.toml"
WEIGHT_DATA_PATH = ROOT / "weight_data.json"
WEIGHT_UPLOADS_DIR = ROOT / "weight_uploads"
THUMB_CACHE_DIR = ROOT / ".thumb_cache"
LOG_PATH = ROOT / "build_food_search_index.log"
LOCK_PATH = ROOT / ".build_food_search_index.lock"
INTER_CALL_DELAY = 1.0


def setup_logger(quiet: bool) -> logging.Logger:
    log = logging.getLogger("food_index")
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


def load_api_key() -> str:
    with open(SECRETS_PATH, "rb") as f:
        secrets = tomllib.load(f)
    key = secrets.get("GOOGLE_API_KEY") or ""
    if not key or key == "YOUR_GEMINI_API_KEY":
        raise RuntimeError("secrets.toml に GOOGLE_API_KEY がありません")
    return key


def collect_images(weight_data: dict) -> list[dict]:
    """image_id ごとに {id, ext, drive_file_id, names, date} を日付降順で返す。"""
    out: dict[str, dict] = {}
    records = weight_data.get("records", {}) or {}
    for date_key in sorted(records.keys(), reverse=True):
        for it in (records[date_key] or {}).get("items", []) or []:
            iid = it.get("image_id")
            if not iid:
                continue
            e = out.setdefault(iid, {
                "id": iid, "ext": it.get("image_ext", "jpg"),
                "drive_file_id": it.get("drive_file_id", ""),
                "names": [], "date": date_key,
            })
            name = it.get("name")
            if isinstance(name, str) and name and name not in e["names"]:
                e["names"].append(name)
            for x in it.get("items_extracted") or []:
                sx = str(x)
                if sx and sx not in e["names"]:
                    e["names"].append(sx)
    return list(out.values())


def load_image_bytes(img: dict, drive_service=None) -> bytes | None:
    p = WEIGHT_UPLOADS_DIR / f"{img['id']}.{img['ext']}"
    if p.exists():
        return p.read_bytes()
    t = THUMB_CACHE_DIR / f"food_{img['id']}.jpg"
    if t.exists():
        return t.read_bytes()
    if drive_service is not None and img.get("drive_file_id"):
        try:
            from googleapiclient.http import MediaIoBaseDownload
            req = drive_service.files().get_media(fileId=img["drive_file_id"])
            buf = io.BytesIO()
            dl = MediaIoBaseDownload(buf, req)
            done = False
            while not done:
                _, done = dl.next_chunk()
            return buf.getvalue()
        except Exception:
            return None
    return None


def build_drive_service():
    try:
        from google.oauth2 import service_account
        from googleapiclient.discovery import build
        with open(SECRETS_PATH, "rb") as f:
            secrets = tomllib.load(f)
        creds = service_account.Credentials.from_service_account_info(
            secrets["gcp_service_account"],
            scopes=["https://www.googleapis.com/auth/drive"],
        )
        return build("drive", "v3", credentials=creds, cache_discovery=False)
    except Exception:
        return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=0, help="処理する最大枚数（0=無制限）")
    ap.add_argument("--force", action="store_true", help="索引済みも作り直す")
    ap.add_argument("--embed-only", action="store_true", help="説明済み・未埋め込み分だけ埋め込む")
    ap.add_argument("--dry-run", action="store_true", help="対象を数えるだけ")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--sleep", type=float, default=INTER_CALL_DELAY)
    args = ap.parse_args()
    log = setup_logger(args.quiet)

    if LOCK_PATH.exists() and time.time() - LOCK_PATH.stat().st_mtime < 3 * 3600:
        log.warning("別のインデックス処理が実行中です（%s）。終了。", LOCK_PATH.name)
        return 2
    LOCK_PATH.write_text(str(time.time()))
    try:
        return _run(args, log)
    finally:
        try:
            LOCK_PATH.unlink()
        except OSError:
            pass


def _run(args, log: logging.Logger) -> int:
    api_key = load_api_key()
    index = fs.load_index()

    if args.embed_only:
        n = fs.embed_pending(index, api_key)
        log.info("埋め込み完了: %d 件", n)
        return 0

    weight_data = json.loads(WEIGHT_DATA_PATH.read_text(encoding="utf-8"))
    images = collect_images(weight_data)
    targets = [im for im in images
               if args.force or im["id"] not in index
               or not (index.get(im["id"]) or {}).get("search_text")]
    log.info("画像 %d 枚 / 索引済み %d / 対象 %d", len(images), len(index), len(targets))
    if args.max > 0:
        targets = targets[: args.max]
    if args.dry_run:
        log.info("dry-run: %d 枚を処理予定", len(targets))
        return 0

    drive = None
    ok = fail = skipped = 0
    pending: dict = {}  # この実行で新しく作った索引エントリ（マージ保存用）
    started = time.time()
    for i, im in enumerate(targets, 1):
        if i > 1 and args.sleep > 0:
            time.sleep(args.sleep)
        raw = load_image_bytes(im, drive)
        if raw is None and drive is None:
            drive = build_drive_service()
            raw = load_image_bytes(im, drive)
        if raw is None:
            skipped += 1
            log.warning("[%d/%d] %s 画像なし（スキップ）", i, len(targets), im["id"])
            continue
        try:
            entry = fs.index_image(im["id"], raw, api_key, extra_names=im["names"],
                                   index=index, embed=False)
        except fs.GeminiRateLimited as e:
            log.error("[%d/%d] レート制限で中断: %s", i, len(targets), e)
            break
        except Exception as e:
            fail += 1
            log.warning("[%d/%d] %s 失敗: %s: %s", i, len(targets), im["id"], type(e).__name__, e)
            continue
        if entry is None:
            fail += 1
            log.warning("[%d/%d] %s 説明生成失敗", i, len(targets), im["id"])
            continue
        ok += 1
        pending[im["id"]] = entry
        log.info("[%d/%d] %s (%s) → %s", i, len(targets), im["id"], im["date"],
                 "、".join(entry.get("items") or [])[:60])
        if ok % 10 == 0:
            index = fs.merge_save_index(pending)
            pending = {}
            try:
                fs.embed_pending(index, api_key)
            except Exception as e:
                log.warning("埋め込み一時失敗（後で --embed-only で再試行可）: %s", e)

    index = fs.merge_save_index(pending)
    try:
        n_emb = fs.embed_pending(index, api_key)
    except Exception as e:
        n_emb = -1
        log.warning("埋め込み失敗（--embed-only で再試行可）: %s", e)
    log.info("完了: 説明 %d 成功 / %d 失敗 / %d スキップ, 埋め込み %s 件, %.0f 秒",
             ok, fail, skipped, n_emb, time.time() - started)
    remaining = sum(1 for im in images if im["id"] not in index)
    if remaining:
        log.info("未索引 残り %d 枚（再実行で続きから処理）", remaining)
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

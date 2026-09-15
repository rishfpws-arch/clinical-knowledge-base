"""
pomken 食事画像 検索インデックス（説明文 + 埋め込み）

app.py（Streamlit UI）と build_food_search_index.py（バックフィル用 CLI）の両方から
使う共通モジュール。Streamlit には依存しない。

データファイル（すべてローカル、Sheets には同期しない）:
    food_search_index.json      image_id → 説明文・カテゴリ等のテキスト索引
    food_search_embeddings.npz  image_id 配列 + 埋め込み行列（L2 正規化済み）
    food_synonyms_cache.json    検索語の類義語展開キャッシュ
    food_query_cache.json       検索クエリの埋め込みキャッシュ
"""
from __future__ import annotations

import base64
import io
import json
import logging
import os
import re
import time
import unicodedata
from datetime import datetime
from pathlib import Path

import numpy as np
import requests
from PIL import Image

ROOT = Path(__file__).resolve().parent
INDEX_PATH = ROOT / "food_search_index.json"
EMB_PATH = ROOT / "food_search_embeddings.npz"
SYN_CACHE_PATH = ROOT / "food_synonyms_cache.json"
QUERY_CACHE_PATH = ROOT / "food_query_cache.json"

GEMINI_MODEL = "gemini-2.5-flash"
EMBED_MODEL = "gemini-embedding-001"
EMBED_DIM = 768
GEMINI_API_BASE = "https://generativelanguage.googleapis.com/v1beta/models/"
GEMINI_429_BACKOFF = (5, 10, 20)
DESCRIBE_MAX_PX = 800  # 解析に送る画像の長辺（トークン節約）
INDEX_VERSION = 1
MODULE_VERSION = 4  # app.py が要求する版。上げると古いモジュールを掴んだ Streamlit が再読込する

# 意味検索のデフォルト（gemini-embedding-001 / 768 次元での経験値）
# 無関係な語でも全件 0.55〜0.59 程度になるため、絶対値の下限に加えて
# 「その検索での分布からどれだけ突出しているか」(z スコア) でも絞る。
SEMANTIC_FLOOR = 0.60        # これ未満は候補にしない
SEMANTIC_Z = 1.0             # median + Z*std 以上を候補にする
SEMANTIC_TOP_K = 30          # 候補の上限（再ランクに渡す件数）
QUERY_CACHE_MAX = 500

_log = logging.getLogger("food_search")


# ---------------------------------------------------------------------------
# プロンプト
# ---------------------------------------------------------------------------
FOOD_DESCRIBE_PROMPT = """この食事の画像を、後から日本語で検索しやすいように整理してください。
JSON 以外のテキストは一切含めないでください。

出力形式:
{
  "items": ["写っている料理・食品・飲み物の名前（日本語、具体的に）"],
  "categories": ["和食/洋食/中華/エスニック などの系統、主食/主菜/副菜/汁物/デザート/おやつ/飲料 などの区分"],
  "cooking": ["揚げ物/焼き物/煮物/炒め物/蒸し物/生/汁物/麺類/丼/パン/弁当 などの調理法・形態"],
  "ingredients": ["鶏肉/豚肉/牛肉/魚/卵/大豆/豆腐/乳製品/米/小麦/野菜/きのこ/海藻/果物 などの主材料"],
  "context": ["自炊/弁当/コンビニ/外食/テイクアウト/宅配/居酒屋/カフェ/ファストフード など、分かる範囲の状況"],
  "aliases": ["items の別名・言い換え・読み（例: 鶏肉→とり肉, チキン / ご飯→ごはん, ライス, 白米 / 鮭→サーモン）"],
  "description": "1〜2文の自然な日本語の説明。何がどのくらい、どんな盛り付けか。色や器、量の印象（少なめ/多め/野菜が多い/揚げ物中心 など）も含める。"
}

ルール:
- 見えるものだけを書き、推測で増やさない（ただし aliases は積極的に）
- items は 1〜10 個、それ以外の配列は 0〜8 個
- 食事でない画像の場合は items を空配列にし、description にその旨を書く
- 単語はすべて日本語。説明や前置きは不要"""

SYNONYM_PROMPT = (
    "「{token}」の関連する日本語の料理名・食べ物名を5〜20個、カンマ区切りで挙げてください。"
    "・上位カテゴリ(例: 「パスタ」→ パスタ全般), 下位の具体名(例: ナポリタン, カルボナーラ), "
    "同義語・別表記(例: スパゲッティ) を含む。"
    "・料理・食材と無関係な単語の場合は何も返さない。"
    "・説明や前置きは一切不要、純粋にカンマ区切りの単語のみ。\n"
    "入力例「パスタ」→ 出力例: スパゲッティ,ナポリタン,カルボナーラ,ペペロンチーノ,ボロネーゼ,ラザニア,マカロニ\n"
    "入力例「肉」→ 出力例: ステーキ,焼肉,ハンバーグ,鶏肉,豚肉,牛肉,唐揚げ,生姜焼き"
)


# ---------------------------------------------------------------------------
# テキスト正規化
# ---------------------------------------------------------------------------
_KATA_TO_HIRA = {c: c - 0x60 for c in range(0x30A1, 0x30F7)}  # ァ..ヶ → ぁ..ゖ


def normalize_text(s: str) -> str:
    """検索比較用の正規化: NFKC → 小文字 → カタカナをひらがなへ → 空白圧縮。"""
    if not s:
        return ""
    t = unicodedata.normalize("NFKC", str(s)).lower()
    t = t.translate(_KATA_TO_HIRA)
    t = re.sub(r"\s+", " ", t).strip()
    return t


_HIRAGANA_ONLY = re.compile(r"^[ぁ-ゖ゛-ゞー\s]+$")


def build_search_text(desc: dict, extra_names: list[str] | None = None) -> str:
    """索引エントリ（describe 結果）から正規化済みの検索対象文字列を作る。

    aliases のうち「ひらがなだけの読み」（例: 牛丼→ぎゅうどん）は含めない。
    部分一致で「うどん」が「ぎゅうどん」に当たるような誤ヒットの元になるため。
    カタカナの言い換え（鮭→サーモン）や漢字の別名（牛めし）は残す。
    """
    parts: list[str] = []
    for key in ("items", "categories", "cooking", "ingredients", "context", "aliases"):
        v = desc.get(key)
        if isinstance(v, str) and v:
            v = [v]
        if not isinstance(v, list):
            continue
        for x in v:
            sx = str(x).strip()
            if not sx:
                continue
            if key == "aliases" and _HIRAGANA_ONLY.match(unicodedata.normalize("NFKC", sx)):
                continue
            parts.append(sx)
    d = desc.get("description")
    if isinstance(d, str) and d:
        parts.append(d)
    for n in extra_names or []:
        if n:
            parts.append(str(n))
    return normalize_text(" ".join(parts))


def embedding_text(desc: dict, extra_names: list[str] | None = None) -> str:
    """埋め込みに渡す（正規化前の）自然文。"""
    names = [str(x) for x in (desc.get("items") or []) if x]
    for n in extra_names or []:
        if n and str(n) not in names:
            names.append(str(n))
    lines = []
    if names:
        lines.append("品目: " + "、".join(names))
    for key, label in (("categories", "分類"), ("cooking", "調理"),
                       ("ingredients", "材料"), ("context", "状況")):
        v = desc.get(key) or []
        if v:
            lines.append(f"{label}: " + "、".join(str(x) for x in v if x))
    d = desc.get("description")
    if d:
        lines.append(str(d))
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Gemini REST
# ---------------------------------------------------------------------------
class GeminiRateLimited(RuntimeError):
    pass


def _post_gemini(url: str, payload: dict, timeout: int = 120) -> dict:
    """429 は段階的に待って再試行。失敗時は例外。"""
    last_err: Exception | None = None
    for attempt in range(len(GEMINI_429_BACKOFF) + 1):
        resp = requests.post(url, json=payload, timeout=timeout)
        try:
            data = resp.json()
        except ValueError:
            raise RuntimeError(
                f"Gemini API: 非JSONレスポンス (status={resp.status_code}, body={resp.text[:200]})"
            )
        if resp.status_code == 429 or (isinstance(data, dict) and
                                       (data.get("error") or {}).get("code") == 429):
            msg = ((data.get("error") or {}).get("message") if isinstance(data, dict) else "") or ""
            last_err = GeminiRateLimited(f"Gemini API 429: {msg[:200]}")
            if attempt < len(GEMINI_429_BACKOFF):
                time.sleep(GEMINI_429_BACKOFF[attempt])
                continue
            raise last_err
        if isinstance(data, dict) and "error" in data:
            err = data["error"] or {}
            raise RuntimeError(
                f"Gemini API エラー [{resp.status_code} {err.get('status', '')}]: "
                f"{err.get('message', '不明なエラー')}"
            )
        return data
    raise last_err or RuntimeError("Gemini API: 不明な失敗")


def gemini_generate(api_key: str, parts: list, model: str | None = None,
                    json_mode: bool = False) -> str:
    url = f"{GEMINI_API_BASE}{model or GEMINI_MODEL}:generateContent?key={api_key}"
    payload = {
        "contents": [{"parts": parts}],
        "safetySettings": [
            {"category": "HARM_CATEGORY_HARASSMENT", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_HATE_SPEECH", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_SEXUALLY_EXPLICIT", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_DANGEROUS_CONTENT", "threshold": "BLOCK_NONE"},
        ],
    }
    if json_mode:
        # gemini-2.5-flash は思考トークンも maxOutputTokens に含まれるため、
        # 思考を切って出力枠を JSON 本文に全部使う（途中で切れて解析失敗するのを防ぐ）
        payload["generationConfig"] = {
            "responseMimeType": "application/json",
            "temperature": 0.2,
            "maxOutputTokens": 4096,
            "thinkingConfig": {"thinkingBudget": 0},
        }
    data = _post_gemini(url, payload)
    candidates = data.get("candidates") or []
    if not candidates:
        raise RuntimeError(f"Gemini API: candidates が空 ({str(data)[:200]})")
    cparts = ((candidates[0] or {}).get("content") or {}).get("parts") or []
    if not cparts:
        raise RuntimeError(
            f"Gemini API: 応答テキストが空 (finishReason={candidates[0].get('finishReason', '')})"
        )
    return cparts[0].get("text", "")


def parse_gemini_json(text: str) -> dict | None:
    t = (text or "").strip()
    if t.startswith("```"):
        t = re.sub(r"^```[a-zA-Z]*\s*", "", t)
        t = re.sub(r"\s*```$", "", t)
    try:
        v = json.loads(t)
        return v if isinstance(v, dict) else None
    except json.JSONDecodeError:
        m = re.search(r"\{.*\}", t, re.DOTALL)
        if m:
            try:
                v = json.loads(m.group(0))
                return v if isinstance(v, dict) else None
            except json.JSONDecodeError:
                return None
    return None


def _image_part(image_bytes: bytes, max_px: int = DESCRIBE_MAX_PX) -> dict:
    """長辺 max_px に縮小した JPEG を inline_data として返す。"""
    try:
        img = Image.open(io.BytesIO(image_bytes))
        img.thumbnail((max_px, max_px))
        buf = io.BytesIO()
        img.convert("RGB").save(buf, format="JPEG", quality=85)
        data, mime = buf.getvalue(), "image/jpeg"
    except Exception:
        data, mime = image_bytes, "image/jpeg"
    return {"inline_data": {"mime_type": mime,
                            "data": base64.b64encode(data).decode("utf-8")}}


def describe_food_image(image_bytes: bytes, api_key: str, hint: str = "") -> dict | None:
    """画像 1 枚から検索用の構造化説明を得る。失敗時は None（呼び出し側で判断）。

    hint には撮影者からの補足（例: 「ビニール袋に入った食べ物です」）を渡せる。
    品目が読み取れなかった写真の再解析に使う。
    """
    prompt = FOOD_DESCRIBE_PROMPT
    hint = (hint or "").strip()
    if hint:
        prompt += chr(10)*2 + f"補足（撮影者からの情報。これを前提に判断すること）: {hint[:300]}"
    parts = [{"text": prompt}, _image_part(image_bytes)]
    parsed = None
    for attempt in range(2):  # 出力が崩れた場合に 1 回だけ再試行
        text = gemini_generate(api_key, parts, json_mode=True)
        parsed = parse_gemini_json(text)
        if parsed and isinstance(parsed.get("items"), list):
            break
        _log.warning("[describe] JSON 解析失敗 (try %d): %s", attempt + 1, (text or "")[:200])
        parsed = None
    if not parsed:
        return None
    out: dict = {}
    for key in ("items", "categories", "cooking", "ingredients", "context", "aliases"):
        v = parsed.get(key) or []
        if isinstance(v, str):
            v = [x for x in re.split(r"[,、/]", v)]
        cleaned: list[str] = []
        for x in v if isinstance(v, list) else []:
            s = str(x).strip()
            if s and s not in cleaned:
                cleaned.append(s)
        out[key] = cleaned
    d = parsed.get("description")
    out["description"] = str(d).strip() if d else ""
    return out


def embed_texts(texts: list[str], api_key: str,
                task_type: str = "RETRIEVAL_DOCUMENT",
                batch_size: int = 50) -> np.ndarray:
    """テキスト群を埋め込み、L2 正規化した (n, EMBED_DIM) 行列を返す。"""
    if not texts:
        return np.zeros((0, EMBED_DIM), dtype=np.float32)
    url = f"{GEMINI_API_BASE}{EMBED_MODEL}:batchEmbedContents?key={api_key}"
    rows: list[list[float]] = []
    for i in range(0, len(texts), batch_size):
        chunk = texts[i:i + batch_size]
        payload = {"requests": [
            {
                "model": f"models/{EMBED_MODEL}",
                "content": {"parts": [{"text": t or " "}]},
                "taskType": task_type,
                "outputDimensionality": EMBED_DIM,
            }
            for t in chunk
        ]}
        data = _post_gemini(url, payload, timeout=120)
        embs = data.get("embeddings") or []
        if len(embs) != len(chunk):
            raise RuntimeError(f"embedding 件数不一致: {len(embs)} != {len(chunk)}")
        rows.extend(e.get("values") or [] for e in embs)
    mat = np.asarray(rows, dtype=np.float32)
    if mat.ndim != 2 or mat.shape[1] != EMBED_DIM:
        raise RuntimeError(f"embedding 形状不正: {mat.shape}")
    norms = np.linalg.norm(mat, axis=1, keepdims=True)
    norms[norms == 0] = 1.0
    return mat / norms


def embed_query(query: str, api_key: str) -> np.ndarray:
    return embed_texts([query], api_key, task_type="RETRIEVAL_QUERY")[0]


# ---------------------------------------------------------------------------
# 永続化
# ---------------------------------------------------------------------------
def _replace_with_retry(tmp: Path, path: Path, tries: int = 6) -> None:
    """Windows では別プロセス（Streamlit）が読んでいる瞬間に os.replace が
    PermissionError になるので、少し待って再試行する。"""
    for i in range(tries):
        try:
            os.replace(tmp, path)
            return
        except PermissionError:
            if i == tries - 1:
                raise
            time.sleep(0.3 * (i + 1))


def _atomic_write_json(path: Path, data) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
    _replace_with_retry(tmp, path)


def _load_json(path: Path, default):
    if not path.exists():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        _log.warning("[load] %s 読み込み失敗: %s", path.name, e)
        return default


def load_index() -> dict:
    """image_id → {items, categories, ..., description, search_text, embedded, updated}"""
    d = _load_json(INDEX_PATH, {})
    return d if isinstance(d, dict) else {}


def save_index(index: dict) -> None:
    _atomic_write_json(INDEX_PATH, index)


def merge_save_index(new_entries: dict) -> dict:
    """ディスク上の最新索引を読み直して new_entries を上書きマージし保存する。

    UI の索引ボタンと build_food_search_index.py が同時に走っても
    互いの追加分を消さないための保存方法。戻り値はマージ後の索引。
    """
    latest = load_index()
    latest.update(new_entries)
    save_index(latest)
    return latest


def load_embeddings() -> tuple[list[str], np.ndarray]:
    if not EMB_PATH.exists():
        return [], np.zeros((0, EMBED_DIM), dtype=np.float32)
    try:
        with np.load(EMB_PATH, allow_pickle=False) as z:
            ids = [str(x) for x in z["ids"].tolist()]
            mat = np.asarray(z["vectors"], dtype=np.float32)
        if mat.shape[0] != len(ids):
            raise ValueError("ids と vectors の件数不一致")
        return ids, mat
    except Exception as e:
        _log.warning("[load] embeddings 読み込み失敗: %s", e)
        return [], np.zeros((0, EMBED_DIM), dtype=np.float32)


def save_embeddings(ids: list[str], mat: np.ndarray) -> None:
    tmp = EMB_PATH.with_suffix(".npz.tmp")
    with open(tmp, "wb") as f:
        np.savez(f, ids=np.asarray(ids, dtype=str), vectors=mat.astype(np.float32))
    _replace_with_retry(tmp, EMB_PATH)


def upsert_embeddings(new: dict[str, np.ndarray]) -> None:
    """既存 npz に new（image_id → ベクトル）をマージして保存。"""
    if not new:
        return
    ids, mat = load_embeddings()
    pos = {iid: i for i, iid in enumerate(ids)}
    add_ids: list[str] = []
    add_rows: list[np.ndarray] = []
    for iid, vec in new.items():
        if iid in pos:
            mat[pos[iid]] = vec
        else:
            add_ids.append(iid)
            add_rows.append(vec)
    if add_rows:
        mat = np.vstack([mat, np.asarray(add_rows, dtype=np.float32)]) if len(ids) else \
            np.asarray(add_rows, dtype=np.float32)
        ids = ids + add_ids
    save_embeddings(ids, mat)


def file_mtimes() -> tuple[float, float]:
    """キャッシュ無効化用: (index.json mtime, npz mtime)。"""
    def _m(p: Path) -> float:
        try:
            return p.stat().st_mtime
        except OSError:
            return 0.0
    return _m(INDEX_PATH), _m(EMB_PATH)


# ---------------------------------------------------------------------------
# 索引作成（1 枚）
# ---------------------------------------------------------------------------
def index_image(image_id: str, image_bytes: bytes, api_key: str,
                extra_names: list[str] | None = None,
                index: dict | None = None, embed: bool = True,
                hint: str = "") -> dict | None:
    """画像 1 枚を説明 → 索引に登録（→ 埋め込み）。

    index を渡した場合はそこに書き込むだけで保存しない（バッチ用）。
    渡さない場合は読み込み → 更新 → 保存まで行う。
    戻り値は索引エントリ（失敗時 None）。
    """
    desc = describe_food_image(image_bytes, api_key, hint=hint)
    if desc is None:
        return None
    entry = dict(desc)
    if hint:
        entry["hint"] = hint.strip()[:300]
    entry["search_text"] = build_search_text(desc, extra_names)
    entry["embed_text"] = embedding_text(desc, extra_names)
    entry["embedded"] = False
    entry["version"] = INDEX_VERSION
    entry["updated"] = datetime.now().isoformat(timespec="seconds")

    own = index is None
    if own:
        index = load_index()
    index[image_id] = entry

    if embed:
        try:
            vec = embed_texts([entry["embed_text"]], api_key)[0]
            upsert_embeddings({image_id: vec})
            entry["embedded"] = True
        except Exception as e:
            _log.warning("[index] 埋め込み失敗 %s: %s", image_id, e)
    if own:
        save_index(index)
    return entry


def embed_pending(index: dict, api_key: str, batch_size: int = 50) -> int:
    """index 内で未埋め込み（embedded=False、または npz に無い）のエントリをまとめて埋め込む。

    npz を消してしまった場合も、これで全件作り直せる。戻り値は処理件数。
    """
    have = set(load_embeddings()[0])
    pending = [(iid, e) for iid, e in index.items()
               if isinstance(e, dict) and e.get("embed_text")
               and (not e.get("embedded") or iid not in have)]
    done = 0
    for i in range(0, len(pending), batch_size):
        chunk = pending[i:i + batch_size]
        mat = embed_texts([e["embed_text"] for _, e in chunk], api_key, batch_size=batch_size)
        upsert_embeddings({iid: mat[j] for j, (iid, _) in enumerate(chunk)})
        for iid, e in chunk:
            e["embedded"] = True
        done += len(chunk)
        save_index(index)
    return done


# ---------------------------------------------------------------------------
# 検索
# ---------------------------------------------------------------------------
def load_synonym_cache() -> dict:
    d = _load_json(SYN_CACHE_PATH, {})
    return d if isinstance(d, dict) else {}


def get_synonyms(token: str, api_key: str | None, cache: dict | None = None) -> set[str]:
    """類義語をディスクキャッシュ付きで取得（正規化済み小文字）。失敗は空集合。"""
    key = normalize_text(token)
    if not key:
        return set()
    if cache is None:
        cache = load_synonym_cache()
    if key in cache and isinstance(cache[key], list):
        return {normalize_text(x) for x in cache[key] if x}
    if not api_key:
        return set()
    syns: set[str] = set()
    try:
        text = gemini_generate(api_key, [{"text": SYNONYM_PROMPT.format(token=token)}])
        for raw in (text or "").replace("\n", ",").split(","):
            s = normalize_text(raw.strip().lstrip("・- 　").rstrip("。 　"))
            if s and 1 <= len(s) <= 30 and s != key:
                syns.add(s)
    except Exception as e:
        _log.warning("[synonyms] 失敗 token=%s: %s", token, e)
        return set()
    cache[key] = sorted(syns)
    try:
        _atomic_write_json(SYN_CACHE_PATH, cache)
    except Exception as e:
        _log.warning("[synonyms] キャッシュ保存失敗: %s", e)
    return syns


def keyword_groups(query: str, api_key: str | None,
                   expand: bool = True) -> list[set[str]]:
    """クエリを空白で分割し、各トークンを {トークン} ∪ 類義語 の集合にする。"""
    tokens = [t for t in normalize_text(query).split(" ") if t]
    cache = load_synonym_cache() if expand else {}
    groups: list[set[str]] = []
    for t in tokens:
        g = {t}
        if expand:
            g |= get_synonyms(t, api_key, cache)
        groups.append(g)
    return groups


# 検索語の「飾り」: 末尾から繰り返し剥がして核になる語を取り出す
# 例: バランスのいい食事 → バランス / ガッツリ系 → ガッツリ / あっさりしたもの → あっさり
_QUERY_SUFFIXES = ("系", "っぽい", "っぽいもの", "的", "的な", "の", "食事", "ご飯", "ごはん", "料理",
                   "もの", "やつ", "めにゅー", "メニュー", "いい", "よい", "良い", "した", "する")
_QUERY_SUFFIX_RE = re.compile("(" + "|".join(sorted(map(re.escape, _QUERY_SUFFIXES), key=len, reverse=True)) + ")$")


def relax_token(token: str) -> str:
    """検索トークンから飾り語を剥がす（2 文字未満になるなら剥がさない）。正規化済み前提。"""
    t = token
    for _ in range(4):
        m = _QUERY_SUFFIX_RE.search(t)
        if not m:
            break
        core = t[: m.start()]
        if len(core) < 2:
            break
        t = core
    return t or token


def relax_query(query: str) -> str:
    """空白区切りの各トークンに relax_token を適用した文字列を返す（正規化済み）。"""
    return " ".join(relax_token(t) for t in normalize_text(query).split(" ") if t)


# 雰囲気を表す語の簡易辞書（意味検索が使えないときの保険。正規化前の表記で書く）
MOOD_SYNONYMS: dict[str, list[str]] = {
    # 具体的な料理名だけにする。「たっぷり」「多め」「野菜」のような広い語は朝食やサラダまで拾ってしまう
    "がっつり": ["とんかつ", "カツ丼", "カツカレー", "唐揚げ", "焼肉", "ステーキ", "ハンバーグ", "ラーメン", "つけ麺", "牛丼", "豚丼", "天丼", "チャーシュー", "フライドチキン", "ピザ", "大盛り"],
    "こってり": ["ラーメン", "つけ麺", "カツカレー", "カルボナーラ", "チーズハンバーグ", "ドリア", "グラタン", "焼肉", "豚骨", "背脂", "濃厚"],
    "あっさり": ["そば", "ざるそば", "素麺", "冷奴", "おひたし", "お茶漬け", "梅", "酢の物", "湯豆腐", "雑炊", "うどん"],
    "さっぱり": ["そば", "ざるそば", "素麺", "冷奴", "酢の物", "梅", "レモン", "サラダ", "サラダチキン", "刺身"],
    "ヘルシー": ["サラダ", "サラダチキン", "蒸し鶏", "豆腐", "納豆", "玄米", "雑穀米", "焼き魚", "きのこ", "海藻", "ヨーグルト"],
    "バランス": ["定食", "副菜", "小鉢", "汁物", "焼き魚", "煮物"],
    "軽め": ["おにぎり", "サンドイッチ", "スープ", "ヨーグルト", "バナナ", "プロテイン", "軽食"],
    "重め": ["とんかつ", "カツ丼", "ラーメン", "焼肉", "ステーキ", "ピザ", "大盛り"],
    "甘いもの": ["ケーキ", "チョコ", "アイス", "プリン", "ドーナツ", "パンケーキ", "クレープ", "大福", "団子", "シュークリーム", "デザート"],
    "甘い": ["ケーキ", "チョコ", "アイス", "プリン", "ドーナツ", "パンケーキ", "クレープ", "大福", "団子", "シュークリーム", "デザート"],
    "辛い": ["麻婆", "キムチ", "担々", "カレー", "唐辛子", "辛味", "激辛", "麻辣"],
    "夜食": ["カップ麺", "夜食", "お茶漬け", "おにぎり", "ラーメン"],
    "朝食": ["グラノーラ", "トースト", "食パン", "ヨーグルト", "納豆", "目玉焼き", "朝食", "モーニング"],
}


def mood_terms(token: str) -> list[str]:
    """正規化済みトークンに対応する雰囲気辞書の語（正規化済み）を返す。無ければ空。"""
    key = normalize_text(token)
    for k, v in MOOD_SYNONYMS.items():
        if normalize_text(k) == key:
            return [normalize_text(x) for x in v]
    return []


def keyword_match(search_text: str, groups: list[set[str]]) -> bool:
    """グループ間 AND・グループ内 OR の部分一致。search_text は正規化済み前提。"""
    return all(any(s in search_text for s in g) for g in groups)


def _load_query_cache() -> dict:
    d = _load_json(QUERY_CACHE_PATH, {})
    return d if isinstance(d, dict) else {}


def cached_query_embedding(query: str, api_key: str) -> np.ndarray | None:
    key = normalize_text(query)
    if not key:
        return None
    cache = _load_query_cache()
    v = cache.get(key)
    if isinstance(v, list) and len(v) == EMBED_DIM:
        return np.asarray(v, dtype=np.float32)
    vec = None
    for attempt in range(2):  # 一時的な失敗（レート制限・タイムアウト）は 1 回だけ再試行
        try:
            vec = embed_query(query, api_key)
            break
        except Exception as e:
            _log.warning("[query] 埋め込み失敗 (try %d) '%s': %s", attempt + 1, query, e)
            time.sleep(2)
    if vec is None:
        return None
    cache[key] = [round(float(x), 6) for x in vec.tolist()]
    if len(cache) > QUERY_CACHE_MAX:
        for k in list(cache.keys())[: len(cache) - QUERY_CACHE_MAX]:
            cache.pop(k, None)
    try:
        _atomic_write_json(QUERY_CACHE_PATH, cache)
    except Exception as e:
        _log.warning("[query] キャッシュ保存失敗: %s", e)
    return vec


def semantic_scores(query_vec: np.ndarray, ids: list[str],
                    mat: np.ndarray) -> dict[str, float]:
    if mat.shape[0] == 0:
        return {}
    sims = mat @ query_vec
    return {iid: float(s) for iid, s in zip(ids, sims)}


def select_candidates(scores: dict[str, float], exclude: set[str] | None = None,
                      floor: float = SEMANTIC_FLOOR, z: float = SEMANTIC_Z,
                      top_k: int = SEMANTIC_TOP_K) -> list[tuple[str, float]]:
    """類似度の分布から突出している候補を類似度降順で返す。"""
    if not scores:
        return []
    vals = np.fromiter(scores.values(), dtype=np.float32)
    gate = max(floor, float(np.median(vals) + z * vals.std()))
    exclude = exclude or set()
    ranked = sorted(scores.items(), key=lambda kv: kv[1], reverse=True)
    out = [(iid, sc) for iid, sc in ranked if sc >= gate and iid not in exclude]
    return out[:top_k]


RERANK_PROMPT = """あなたは食事写真アルバムの検索アシスタントです。
ユーザーの検索語に「本当に該当する」写真だけを選んでください。

検索語: 「{query}」

候補（番号: 説明）:
{candidates}

ルール:
- 検索語の意図（料理名・食材・調理法・食事の状況・雰囲気・量の印象など）に「明らかに」合う候補の番号だけを選ぶ
- 雰囲気語（がっつり／あっさり／ヘルシー 等）は料理の内容と量から厳しめに判断する。例:「がっつり」なら揚げ物・肉・丼・こってり麺が主役で量が多いもののみ。サンドイッチやシリアル、普通の定食は含めない
- 迷う程度に弱い関連は含めない。該当なしなら空配列
- JSON のみを出力: {{"match": [番号, ...]}}"""


def _rerank_cache_key(query: str, cand_ids: list[str]) -> str:
    import hashlib
    h = hashlib.sha1(",".join(cand_ids).encode("utf-8")).hexdigest()[:12]
    return f"rerank:{normalize_text(query)}:{h}"


def rerank_with_llm(query: str, candidates: list[tuple[str, str]],
                    api_key: str) -> list[str] | None:
    """候補 (image_id, 説明テキスト) を Gemini に見せ、該当する image_id を返す。

    失敗時は None（呼び出し側で候補をそのまま使う）。結果はディスクにキャッシュ。
    """
    if not candidates:
        return []
    cache = _load_query_cache()
    ckey = _rerank_cache_key(query, [c[0] for c in candidates])
    cached = cache.get(ckey)
    if isinstance(cached, list):
        return [str(x) for x in cached]

    lines = []
    for i, (_, text) in enumerate(candidates, 1):
        t = re.sub(r"\s+", " ", text or "").strip()[:220]
        lines.append(f"{i}: {t}")
    prompt = RERANK_PROMPT.format(query=query, candidates=chr(10).join(lines))
    try:
        raw = gemini_generate(api_key, [{"text": prompt}], json_mode=True)
        parsed = parse_gemini_json(raw)
        if not isinstance(parsed, dict) or "match" not in parsed:
            # 応答が壊れている: 「該当なし」として保存せず、呼び出し側で候補をそのまま使う
            _log.warning("[rerank] 応答を解析できず '%s': %s", query, (raw or "")[:120])
            return None
        nums = parsed.get("match") or []
        picked: list[str] = []
        for n in nums:
            try:
                k = int(n)
            except (TypeError, ValueError):
                continue
            if 1 <= k <= len(candidates):
                iid = candidates[k - 1][0]
                if iid not in picked:
                    picked.append(iid)
    except Exception as e:
        _log.warning("[rerank] 失敗 '%s': %s", query, e)
        return None
    cache[ckey] = picked
    if len(cache) > QUERY_CACHE_MAX:
        for k in list(cache.keys())[: len(cache) - QUERY_CACHE_MAX]:
            cache.pop(k, None)
    try:
        _atomic_write_json(QUERY_CACHE_PATH, cache)
    except Exception as e:
        _log.warning("[rerank] キャッシュ保存失敗: %s", e)
    return picked

# Clinical Knowledge Base — Phase 1

Google Drive に保存した医療関連スクリーンショットをブラウザで閲覧するための Streamlit アプリです。

## 前提条件

- Python 3.10 以上
- Google アカウント（Google Cloud プロジェクトを作成できること）

---

## 1. Google Cloud の設定

### 1-1. プロジェクトの作成

1. [Google Cloud Console](https://console.cloud.google.com/) にアクセス
2. 画面上部のプロジェクト選択 → **「新しいプロジェクト」** をクリック
3. プロジェクト名（例: `clinical-kb`）を入力して **「作成」**

### 1-2. Google Drive API の有効化

1. 左メニュー → **「APIとサービス」** → **「ライブラリ」**
2. 検索バーで **「Google Drive API」** を検索
3. **「Google Drive API」** をクリック → **「有効にする」**

### 1-3. サービスアカウントの作成

1. 左メニュー → **「APIとサービス」** → **「認証情報」**
2. **「＋認証情報を作成」** → **「サービスアカウント」**
3. サービスアカウント名（例: `clinical-kb-reader`）を入力 → **「作成して続行」**
4. ロールの付与はスキップ可（**「続行」** → **「完了」**）

### 1-4. JSON キーのダウンロード

1. 作成したサービスアカウントをクリック
2. **「鍵」** タブ → **「鍵を追加」** → **「新しい鍵を作成」**
3. **JSON** を選択 → **「作成」**
4. JSON ファイルが自動ダウンロードされる（安全な場所に保管してください）

### 1-5. Google Drive フォルダの共有

1. Google Drive で対象フォルダを開く
2. フォルダを右クリック → **「共有」**
3. サービスアカウントのメールアドレス（`xxx@xxx.iam.gserviceaccount.com`）を追加
4. 権限は **「閲覧者」** で OK
5. フォルダの URL から **フォルダ ID** を控える
   - URL: `https://drive.google.com/drive/folders/XXXXX` → `XXXXX` がフォルダ ID

---

## 2. アプリのセットアップ

### 2-1. 依存ライブラリのインストール

```bash
pip install -r requirements.txt
```

### 2-2. 認証情報の設定

```bash
mkdir .streamlit
cp secrets_template.toml .streamlit/secrets.toml
```

`.streamlit/secrets.toml` を開き、以下を設定してください:

- `folder_id`: Google Drive のフォルダ ID
- `[gcp_service_account]`: ダウンロードした JSON キーの内容を転記

### 2-3. .gitignore の設定（Git 管理する場合）

`.streamlit/secrets.toml` を `.gitignore` に追加してください:

```
.streamlit/secrets.toml
```

---

## 3. アプリの起動

```bash
streamlit run app.py
```

ブラウザが自動で開き、`http://localhost:8501` でアプリにアクセスできます。

---

## 使い方

1. サイドバーに Google Drive フォルダ内の画像一覧が表示されます
2. 画像名をクリックすると、メイン画面に大きくプレビューされます
3. **「一覧を更新」** ボタンで最新のファイルリストを再取得できます

---

## ファイル構成

```
.
├── app.py                  # メインアプリケーション
├── requirements.txt        # 依存ライブラリ
├── secrets_template.toml   # secrets.toml のテンプレート
├── README.md               # このファイル
└── .streamlit/
    └── secrets.toml        # 認証情報（Git管理しない）
```

---

## トラブルシューティング

| 症状 | 対処法 |
|------|--------|
| 「認証情報が見つかりません」 | `.streamlit/secrets.toml` が正しく配置されているか確認 |
| 「フォルダが見つかりません」 | `folder_id` が正しいか、サービスアカウントにフォルダが共有されているか確認 |
| 画像が表示されない | 画像が JPG/PNG 形式であることを確認 |
| 403 エラー | Google Drive API が有効になっているか、サービスアカウントに閲覧権限があるか確認 |

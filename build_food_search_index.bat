@echo off
rem pomken 食事検索インデックスの未処理分を作成（何度実行しても続きから進む）
rem 例: build_food_search_index.bat --max 50
cd /d "%~dp0"
"C:\Users\rishf\AppData\Local\Python\bin\python.exe" build_food_search_index.py %*
pause

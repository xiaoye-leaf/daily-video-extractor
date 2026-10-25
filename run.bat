@echo off
setlocal
chcp 65001 >nul
cd /d "%~dp0"
set "PY="
if exist ".venv\Scripts\python.exe" set "PY=.venv\Scripts\python.exe"
if not defined PY (
    where py >nul 2>nul
    if not errorlevel 1 set "PY=py -3"
)
if not defined PY (
    where python >nul 2>nul
    if not errorlevel 1 set "PY=python"
)
if defined PY (
    %PY% douyin_daily.py %*
    if errorlevel 1 (
        echo.
        echo Failed. Check the error above.
        pause
    )
    exit /b 0
)
if exist "dist\DouyinDailyExtractor\DouyinDailyExtractor.exe" (
    start "" "dist\DouyinDailyExtractor\DouyinDailyExtractor.exe"
    exit /b 0
)
echo [ERROR] Python 3.10+ not found.
pause
exit /b 1

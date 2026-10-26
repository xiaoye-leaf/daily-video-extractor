@echo off
setlocal
chcp 65001 >nul
cd /d "%~dp0"
set "PY="
if exist ".venv\Scripts\python.exe" set "PY=.venv\Scripts\python.exe"
if not defined PY (
    where python >nul 2>nul
    if not errorlevel 1 set "PY=python"
)
if not defined PY (
    echo [ERROR] Python not found.
    pause
    exit /b 1
)
%PY% -m pip install --disable-pip-version-check pyinstaller imageio-ffmpeg
if errorlevel 1 (
    echo [ERROR] Failed to install build dependencies.
    pause
    exit /b 1
)
%PY% -m PyInstaller --noconfirm --clean --onedir --windowed ^
  --name DouyinDailyExtractor ^
  --icon "assets\douyin_daily_icon.ico" ^
  --hidden-import tkinter --hidden-import tkinter.ttk ^
  --hidden-import tkinter.filedialog --hidden-import tkinter.messagebox ^
  --collect-all imageio_ffmpeg ^
  douyin_daily.py
if errorlevel 1 (
    echo [ERROR] Build failed.
    pause
    exit /b 1
)
echo Build complete: dist\DouyinDailyExtractor\DouyinDailyExtractor.exe
pause
endlocal

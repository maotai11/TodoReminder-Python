@echo off
setlocal enabledelayedexpansion
title TodoReminder - Build Tool

echo ==========================================
echo   TodoReminder  ^|  Python to EXE Build
echo ==========================================
echo.

:: -- Find Python --------------------------------------------------
set PYTHON_CMD=

python --version >nul 2>&1
if not errorlevel 1 (
    set PYTHON_CMD=python
    goto :found_python
)

py --version >nul 2>&1
if not errorlevel 1 (
    set PYTHON_CMD=py
    goto :found_python
)

echo [ERROR] Python not found in PATH.
echo.
echo Please install Python 3.10+ from:
echo   https://www.python.org/downloads/
echo.
echo During install, CHECK this option:
echo   [x] Add Python to PATH
echo.
pause
exit /b 1

:found_python
echo [1/3] Python found:
%PYTHON_CMD% --version
echo.

:: -- Install dependencies (skip if already installed) -------------
echo [2/3] Checking dependencies...
%PYTHON_CMD% -m pip install pystray Pillow pyinstaller --quiet
if errorlevel 1 (
    echo [ERROR] pip install failed. Check internet connection.
    pause
    exit /b 1
)
echo       Dependencies OK
echo.

:: -- Clean old build artifacts ------------------------------------
if exist "dist"           rmdir /s /q "dist"
if exist "build"          rmdir /s /q "build"
if exist "TodoReminder.spec" del /q "TodoReminder.spec"

:: -- PyInstaller --------------------------------------------------
echo [3/3] Packaging with PyInstaller (1-3 min)...
echo.

%PYTHON_CMD% -m PyInstaller ^
    --onefile ^
    --windowed ^
    --name "TodoReminder" ^
    --hidden-import pystray ^
    --hidden-import pystray._win32 ^
    --hidden-import PIL ^
    --hidden-import PIL.Image ^
    --hidden-import PIL.ImageDraw ^
    --hidden-import PIL._imaging ^
    --collect-all pystray ^
    --collect-all PIL ^
    --noconfirm ^
    main.py

if errorlevel 1 (
    echo.
    echo [ERROR] Build failed. See error above.
    pause
    exit /b 1
)

:: -- Copy EXE to root folder --------------------------------------
copy /y "dist\TodoReminder.exe" "TodoReminder.exe" >nul

:: -- Print file size ----------------------------------------------
for %%A in (TodoReminder.exe) do set EXE_SIZE=%%~zA
set /a EXE_MB=!EXE_SIZE! / 1048576

echo.
echo ==========================================
echo   BUILD SUCCESSFUL
echo ==========================================
echo   Output : TodoReminder.exe
echo   Size   : ~!EXE_MB! MB
echo.
echo   Usage:
echo   - Double-click TodoReminder.exe
echo   - A 'data' folder is auto-created next to EXE
echo   - Copy EXE to any offline Windows machine
echo ==========================================
echo.
pause

@echo off
set "RUNTIME=%~dp0runtime\pythonw.exe"
if not exist "%RUNTIME%" set "RUNTIME=%LOCALAPPDATA%\AmzFlow\runtime\pythonw.exe"
if not exist "%RUNTIME%" (
  echo AmzFlow runtime is not installed on this computer.
  echo Run the initial AmzFlow setup once, then open this file again.
  pause
  exit /b 1
)
start "AmzFlow Admin" /wait "%RUNTIME%" "%~dp0amzflow_admin.py"

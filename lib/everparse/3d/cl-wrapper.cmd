@echo off
setlocal
where cl.exe >nul 2>nul
if not errorlevel 1 goto compile

set "vswhere=%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe"
if exist "%vswhere%" (
  for /f "usebackq delims=" %%V in (`"%vswhere%" -latest -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath`) do call "%%V\VC\Auxiliary\Build\vcvars64.bat"
) else if defined VS150COMNTOOLS (
  call "%VS150COMNTOOLS%\..\..\VC\vcvarsall.bat" amd64
) else if defined VS140COMNTOOLS (
  call "%VS140COMNTOOLS%\..\..\VC\vcvarsall.bat" amd64
) else if defined VS120COMNTOOLS (
  call "%VS120COMNTOOLS%\..\..\VC\vcvarsall.bat" amd64
) else if defined VS110COMNTOOLS (
  call "%VS110COMNTOOLS%\..\..\VC\vcvarsall.bat" amd64
)
where cl.exe >nul 2>nul
if errorlevel 1 (
  echo Cannot locate MSVC. Install Visual C++ tools or run from a Developer Command Prompt. >&2
  exit /b 1
)

:compile
cl.exe %*
exit /b %errorlevel%

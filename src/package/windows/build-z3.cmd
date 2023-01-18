setlocal
set mypath0=%~dp0
set mypath=%mypath0:~0,-1%
cd %mypath%\z3-sources
python scripts/mk_make.py -x
if %ERRORLEVEL% neq 0 exit /b %ERRORLEVEL%
cd build
for /f "usebackq delims=" %%i in (`"%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe" -prerelease -latest -property installationPath`) do (
  if exist "%%i\Common7\Tools\vsdevcmd.bat" (
    call "%%i\Common7\Tools\vsdevcmd.bat" -arch=amd64 %* && nmake
    exit /b %ERRORLEVEL%
  )
)
echo vswhere not found
exit /b 2

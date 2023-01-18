setlocal
set mypath0=%~dp0
set mypath=%mypath0:~0,-1%
cd %mypath%\z3-sources
python scripts/mk_make.py -x
if %ERRORLEVEL% neq 0 exit /b %ERRORLEVEL%
cd build
for /f "usebackq delims=" %%i in (`"%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe" -prerelease -latest -property installationPath`) do (
  if exist "%%i\Common7\Tools\vsdevcmd.bat" (
    set vsdevcmd_bat="%%i\Common7\Tools\vsdevcmd.bat"
    goto continue
  )
)
echo vswhere not found
exit /b 2

:continue
call %vsdevcmd_bat% -arch=amd64 %* && nmake
if %ERRORLEVEL% neq 0 exit /b %ERRORLEVEL%
if not exist %mypath%\z3 mkdir %mypath%\z3
if %ERRORLEVEL% neq 0 exit /b %ERRORLEVEL%
if not exist %mypath%\z3\bin mkdir %mypath%\z3\bin
if %ERRORLEVEL% neq 0 exit /b %ERRORLEVEL%
copy %mypath%\z3-sources\build\*.exe %mypath%\z3\bin\
if %ERRORLEVEL% neq 0 exit /b %ERRORLEVEL%
copy %mypath%\z3-sources\build\*.dll %mypath%\z3\bin\

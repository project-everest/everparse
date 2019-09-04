setlocal

if not "%1" == "" goto paths
echo Missing argument
endlocal
set errorlevel=1
goto exit

:paths

set mypath0=%~dp0
set mypath=%mypath0:~0,-1%
if "%FSTAR_HOME%" == "" set FSTAR_HOME=%mypath%
if "%KREMLIN_HOME%" == "" set KREMLIN_HOME=%mypath%
set krml=%KREMLIN_HOME%\bin\krml.exe
if not exist "%krml%" set krml=%KREMLIN_HOME%\krml
if "%LOWPARSE_HOME%" == "" set LOWPARSE_HOME=%mypath%\src\lowparse
if "%NINJA_BIN%" == "" set NINJA_BIN=%mypath%\bin\ninja.exe

copy %mypath%\src\package\build.ninja .

echo FSTAR_HOME = %FSTAR_HOME%> vars.ninja
echo KREMLIN_HOME = %KREMLIN_HOME%>> vars.ninja
echo LOWPARSE_HOME = %LOWPARSE_HOME%>> vars.ninja
echo NINJA_BIN = %NINJA_BIN%>> vars.ninja

%mypath%\bin\qd.exe %1
%FSTAR_HOME%\bin\fstar.exe --dep ninja --dep_ninja krml --cache_checked_modules --already_cached FStar,LowStar,C,Spec.Loops,LowParse --include %LOWPARSE_HOME% --include %KREMLIN_HOME%\kremlib *.fst *.fsti > deps.ninja
%NINJA_BIN% build.bat
call build.bat
%krml% -skip-compilation -warn-error -9 -bundle LowParse.\* -I %LOWPARSE_HOME% *.krml

:exit

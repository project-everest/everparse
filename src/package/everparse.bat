setlocal

:arg1

if not "%1" == "" goto arg2
echo Missing argument: input file
goto argerror

:arg2

if not "%2" == "" goto main
echo Missing argument: module name
goto argerror

:argerror

endlocal
set errorlevel=1
goto exit

:runerror
echo Error while running EverParse
endlocal
goto exit

:main

set mypath0=%~dp0
set mypath=%mypath0:~0,-1%
if "%FSTAR_HOME%" == "" set FSTAR_HOME=%mypath%
if "%KREMLIN_HOME%" == "" set KREMLIN_HOME=%mypath%
set krml=%KREMLIN_HOME%\bin\krml.exe
if not exist "%krml%" set krml=%KREMLIN_HOME%\krml
if "%LOWPARSE_HOME%" == "" set LOWPARSE_HOME=%mypath%\src\lowparse
if "%NINJA_BIN%" == "" set NINJA_BIN=%mypath%\bin\ninja.exe
if "%DDD_HOME%" == "" set DDD_HOME=%mypath%\src\3d

copy %mypath%\src\package\build.ninja .

echo FSTAR_HOME = %FSTAR_HOME%> vars.ninja
echo KREMLIN_HOME = %KREMLIN_HOME%>> vars.ninja
echo LOWPARSE_HOME = %LOWPARSE_HOME%>> vars.ninja
echo NINJA_BIN = %NINJA_BIN%>> vars.ninja

%mypath%\bin\3d.exe %1 --module_name %2 --odir .
copy %DDD_HOME%\Prelude.fst .
if errorlevel 1 goto runerror
%FSTAR_HOME%\bin\fstar.exe --dep ninja --dep_ninja krml --cache_checked_modules --already_cached FStar,LowStar,C,Spec.Loops,LowParse --include %LOWPARSE_HOME% --include %KREMLIN_HOME%\kremlib *.fst > deps.ninja
if errorlevel 1 goto runerror
%NINJA_BIN% build.bat
if errorlevel 1 goto runerror
call build.bat
if errorlevel 1 goto runerror
%krml% -skip-compilation -warn-error -9 -bundle LowParse.\* -I %LOWPARSE_HOME% *.krml
if errorlevel 1 goto runerror

:exit

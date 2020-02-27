@echo off
setlocal
set mypath0=%~dp0
set mypath=%mypath0:~0,-1%
set everparseerror=0

:mode

if "%1" == "/?"  goto help
if "%1" == "/3D" goto 3d-file
if "%1" == "/3d" goto 3d-file
echo Missing argument: EverParse running mode
goto argerror

:argerror

set everparseerror=1
goto help

:help
echo.
echo EverParse: verified parsing for binary data formats
echo.
echo Usage: everparse.bat /3D modulename
echo.
echo Arguments:
echo.
echo /3D modulename    Run EverParse in 3D (Dependent Data Description) mode
echo                   reading the format description from modulename.3d
echo.
goto exit

:3d-file

shift
if not "%1" == "" goto 3d
echo Missing argument: module name (without 3d extension)
goto argerror

:runerror

@echo off
echo Error while running EverParse
set everparseerror=1
goto exit

:3d

echo on
set mymodule=%1
set FSTAR_HOME=%mypath%
set KREMLIN_HOME=%mypath%
set krml=%KREMLIN_HOME%\bin\krml.exe
set LOWPARSE_HOME=%mypath%\src\lowparse
set DDD_HOME=%mypath%\src\3d

%mypath%\bin\3d.exe %mymodule%.3d --module_name %mymodule% --odir .
@if errorlevel 1 goto runerror
%FSTAR_HOME%\bin\fstar.exe --cache_checked_modules --already_cached FStar,LowStar,C,Spec.Loops,LowParse --include %LOWPARSE_HOME% --include %KREMLIN_HOME%\kremlib --include %DDD_HOME% --cmi %mymodule%.fsti
@if errorlevel 1 goto runerror
%FSTAR_HOME%\bin\fstar.exe --cache_checked_modules --already_cached FStar,LowStar,C,Spec.Loops,LowParse --include %LOWPARSE_HOME% --include %KREMLIN_HOME%\kremlib --include %DDD_HOME% --cmi %mymodule%.fst
@if errorlevel 1 goto runerror
%FSTAR_HOME%\bin\fstar.exe --cache_checked_modules --already_cached FStar,LowStar,C,Spec.Loops,LowParse --include %LOWPARSE_HOME% --include %KREMLIN_HOME%\kremlib --include %DDD_HOME% --cmi --extract_module %mymodule% %mymodule%.fst --codegen Kremlin
@if errorlevel 1 goto runerror
copy %mypath%\src\3d\.clang-format .
@if errorlevel 1 goto runerror
copy %mypath%\include\EverParseEndianness.h .
%krml% -skip-compilation -bundle ResultOps=Prims,C.\*,FStar.\*,LowStar.\*,LowParse.\*,Prelude,Prelude.\*,Actions[rename=EverParse,rename-prefix] -warn-error -9 -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft -header %DDD_HOME%\noheader.txt -minimal -add-include EverParse:"EverParseEndianness.h" -static-header Prelude.StaticHeader,LowParse.Low.Base,Prelude,Actions,ResultOps -no-prefix LowParse.Slice -no-prefix LowParse.Low.BoundedInt %DDD_HOME%\*.krml *.krml
@if errorlevel 1 goto runerror
@echo EverParse successfully completed verification and code generation!
@goto exit

:exit

@if %everparseerror% == 0 goto trueexit
@endlocal
@exit /b 1

:trueexit

@endlocal

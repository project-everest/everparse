@echo off
setlocal
set mypath0=%~dp0
set EVERPARSE_HOME=%mypath0:~0,-1%
set KRML_HOME=%EVERPARSE_HOME%
%EVERPARSE_HOME%\bin\3d.exe --__arg0 everparse.cmd --fstar %EVERPARSE_HOME%\bin\fstar.exe --z3_executable %EVERPARSE_HOME%\lib\fstar\z3-4.13.3\bin\z3 --clang_format_executable %EVERPARSE_HOME%\bin\clang-format.exe %*
exit /b %ERRORLEVEL%

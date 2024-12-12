@echo off
setlocal
set mypath0=%~dp0
set EVERPARSE_HOME=%mypath0:~0,-1%
set FSTAR_EXE=%EVERPARSE_HOME%\bin\fstar.exe
set KRML_HOME=%EVERPARSE_HOME%
%EVERPARSE_HOME%\bin\3d.exe --__arg0 everparse.cmd --clang_format_executable %EVERPARSE_HOME%\bin\clang-format.exe %*
exit /b %ERRORLEVEL%

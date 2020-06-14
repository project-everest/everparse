@echo off
setlocal
set mypath0=%~dp0
set QD_HOME=%mypath0:~0,-1%
set FSTAR_HOME=%QD_HOME%
set KREMLIN_HOME=%QD_HOME%
%QD_HOME%\bin\3d.exe --__arg0 everparse.bat --clang_format_executable %QD_HOME%\bin\clang-format.exe %*

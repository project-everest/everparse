@echo off
setlocal
set "mypath0=%~dp0"
"%mypath0%bin\everparse-3d.exe" --__arg0 everparse.cmd --clang_format_executable "%mypath0%bin\clang-format.exe" %*
exit /b %ERRORLEVEL%

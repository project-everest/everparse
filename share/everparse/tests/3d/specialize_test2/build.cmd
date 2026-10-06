@echo off
if "%1" == "" goto error
if not exist obj mkdir obj
call %1\everparse.cmd --odir obj --makefile nmake src\SpecializeABC.3d
call nmake /f helper.NMakefile EVERPARSE_INPUT_DIR=src EVERPARSE_OUTPUT_DIR=obj EVERPARSE_HOME=%1 EVERPARSE_CMD=%1\everparse.cmd
goto end

:error
echo Please provide the path to the EverParse binary package directory
set errorlevel=1

:end

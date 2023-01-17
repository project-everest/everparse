setlocal
set mypath0=%~dp0
set mypath=%mypath0:~0,-1%
cd %mypath%\z3-sources
python scripts/mk_make.py -x
cd build
nmake

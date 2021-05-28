#!/usr/bin/env bash
set -e
unset CDPATH
export QD_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export FSTAR_HOME="$QD_HOME"
export KREMLIN_HOME="$QD_HOME"
export PATH="$QD_HOME/bin:$PATH" # because of z3
export LD_LIBRARY_PATH="$QD_HOME/bin:$LD_LIBRARY_PATH"
if which clang-format >/dev/null ; then
    clang_format=--clang_format
else
    clang_format=
fi
exec "$QD_HOME/bin/3d.exe" --__arg0 everparse.sh --batch $clang_format "$@"

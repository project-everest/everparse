#!/usr/bin/env bash
set -e
unset CDPATH
export EVERPARSE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export FSTAR_HOME="$EVERPARSE_HOME"
export KRML_HOME="$EVERPARSE_HOME"
export PATH="$EVERPARSE_HOME/bin:$PATH" # because of z3
export LD_LIBRARY_PATH="$EVERPARSE_HOME/bin:$LD_LIBRARY_PATH"
if which clang-format >/dev/null ; then
    clang_format=--clang_format
else
    clang_format=
fi
exec "$EVERPARSE_HOME/bin/3d.exe" --__arg0 everparse.sh --batch $clang_format "$@"

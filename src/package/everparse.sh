#!/usr/bin/env bash
set -e
unset CDPATH
export EVERPARSE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
(cd "$EVERPARSE_HOME/bin" ; chmod +x * ) || true
(cd "$EVERPARSE_HOME/z3-latest/bin" ; chmod +x * ) || true
FSTAR_EXE="$EVERPARSE_HOME/bin/fstar.exe"
export KRML_HOME="$EVERPARSE_HOME"
export PATH="$EVERPARSE_HOME/bin:$PATH" # because of z3
export LD_LIBRARY_PATH="$EVERPARSE_HOME/bin:$LD_LIBRARY_PATH"
if which clang-format >/dev/null ; then
    clang_format=--clang_format
else
    clang_format=
fi
exec "$EVERPARSE_HOME/bin/3d.exe" --__arg0 everparse.sh --fstar "$FSTAR_EXE" --batch --z3_executable "$EVERPARSE_HOME/z3-latest/bin/z3" $clang_format "$@"

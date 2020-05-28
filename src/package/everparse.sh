#!/usr/bin/env bash
set -e
unset CDPATH
export QD_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export FSTAR_HOME="$QD_HOME"
export KREMLIN_HOME="$QD_HOME"
export PATH="$QD_HOME/bin:$PATH" # because of z3
if which clang-format >/dev/null ; then
    clang_format=--clang_format
else
    clang_format=
fi
exec "$QD_HOME/bin/3d" --batch $clang_format "$@"

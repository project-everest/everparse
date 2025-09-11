#!/usr/bin/env bash
set -e
unset CDPATH
EVERPARSE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
if [[ "$OS" = "Windows_NT" ]] ; then
   MAKE=make
else
   MAKE="$(which gmake >/dev/null 2>&1 && echo gmake || echo make)"
fi
$MAKE -C "$EVERPARSE_HOME" -s deps
eval "$($MAKE -C "$EVERPARSE_HOME" -s env)"
exec bash "$@"

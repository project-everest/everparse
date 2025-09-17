#!/usr/bin/env bash
set -e
unset CDPATH
EVERPARSE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$EVERPARSE_HOME"/env.sh
exec "$FSTAR_EXE" --include "$KRML_HOME/krmllib" --include "$KRML_HOME/krmllib/obj" --include "$PULSE_HOME/lib/pulse" "$@"

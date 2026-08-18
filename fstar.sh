#!/usr/bin/env bash
set -e
unset CDPATH
EVERPARSE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$EVERPARSE_HOME"/env.sh
if [[ -z "$KRML_LIB" ]] ; then
    KRML_LIB="$("$KRML_EXE" -locate-krmllib)"
fi
if [[ "$OS" = Windows_NT ]] ; then
    KRML_LIB="$(cygpath -m "$(echo "$KRML_LIB" | sed 's!\r!!g')")"
fi
exec "$FSTAR_EXE" --z3version $EVERPARSE_Z3_VERSION --include "$KRML_LIB" --include "$KRML_LIB"/obj --include "$PULSE_HOME/lib/pulse" "$@"

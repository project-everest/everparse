#!/usr/bin/env bash
set -e
unset CDPATH
EVERPARSE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"/../../../..
source "$EVERPARSE_HOME"/env.sh
exec "$EVERPARSE_HOME/fstar.sh" --include "$PULSE_HOME/share/pulse/examples/dice/_cache" --include "$PULSE_HOME/share/pulse/examples/dice" "$@"

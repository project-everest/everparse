#!/usr/bin/env bash
set -e
unset CDPATH
EVERPARSE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
exec "$EVERPARSE_HOME/fstar.sh" --include "$EVERPARSE_HOME/src/cbor/spec" --include "$EVERPARSE_HOME/src/cbor/pulse"  --include "$EVERPARSE_HOME/src/cddl/spec" --include "$EVERPARSE_HOME/src/cddl/pulse" --include "$EVERPARSE_HOME/src/cddl/tool" "$@"

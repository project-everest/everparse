#!/usr/bin/env bash
set -e
unset CDPATH
EVERPARSE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$EVERPARSE_HOME"/env.sh
exec bash "$@"

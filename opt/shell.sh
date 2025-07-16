#!/bin/bash
set -e
unset CDPATH
OPT="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
eval $(make -s -C "$OPT" env)
exec bash "$@"

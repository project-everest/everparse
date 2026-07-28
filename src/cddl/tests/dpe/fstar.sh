#!/usr/bin/env bash
set -e
unset CDPATH
DPE_HOME="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
EVERPARSE_HOME="$DPE_HOME"/../../../..
source "$EVERPARSE_HOME"/env.sh
DICE_HOME="$(make -C "$DPE_HOME" -f dice_home.Makefile -s echo_DICE_HOME)"
exec "$EVERPARSE_HOME/fstar.sh" --include "$DICE_HOME/_cache" --include "$DICE_HOME/." "$@"

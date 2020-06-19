#!/bin/bash

FSTAR_EXE="$FSTAR_HOME/bin/fstar.exe"

if args=$(make -s --no-print-directory "$1-in") ; then
   echo Found arguments: $args
   exec "$FSTAR_EXE" $args "$@"
fi

"$FSTAR_EXE" "$@"

#!/bin/bash
if [[ -z "$FSTAR_EXE" ]] ; then
    FSTAR_EXE=fstar.exe
fi
if args=$(make -s --no-print-directory "$1-in") ; then
    exec "$FSTAR_EXE" $args "$@"
else
    exec "$FSTAR_EXE" "$@"
fi

#!/bin/bash
set -e
set -x
unset CDPATH
MAKE=$(which gmake >/dev/null 2>&1 && echo gmake || echo make)
cd "$( dirname "${BASH_SOURCE[0]}" )"
"$MAKE" _opam
opam exec -- "$MAKE" -j -C opt
opam exec -- "$MAKE" -j 8 -k cddl

#!/usr/bin/env bash
set -e
set -x
unset CDPATH
MAKE=$(which gmake >/dev/null 2>&1 && echo gmake || echo make)
cd "$( dirname "${BASH_SOURCE[0]}" )"
"$MAKE" _opam
nproc=$(nproc) || nproc=$(sysctl -n hw.logicalcpu) || nproc=1
if [[ $nproc -gt 8 ]] ; then nproc=8 ; fi # to prevent OOM during extraction
opam exec -- "$MAKE" -j$nproc -C opt
OTHERFLAGS='--admit_smt_queries true' opam exec -- "$MAKE" -j$nproc -k cddl

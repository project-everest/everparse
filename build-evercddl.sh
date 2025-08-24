#!/usr/bin/env bash
set -e
set -x
unset CDPATH
MAKE=$(which gmake >/dev/null 2>&1 && echo gmake || echo make)
cd "$( dirname "${BASH_SOURCE[0]}" )"
nproc=$(nproc) || nproc=$(sysctl -n hw.logicalcpu) || nproc=1
if [[ $nproc -gt 8 ]] ; then nproc=8 ; fi # to prevent OOM during extraction
"$MAKE" -j$nproc -C opt
OTHERFLAGS='--admit_smt_queries true' "$MAKE" -j$nproc -k cddl

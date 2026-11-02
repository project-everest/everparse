#!/usr/bin/env bash
set -e
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
fstar_hash=$(git -C FStar rev-parse HEAD)
printf 'FStar_hash := %s\n' "$fstar_hash" > hashes.Makefile.tmp
mv hashes.Makefile.tmp hashes.Makefile
touch hashes.Makefile

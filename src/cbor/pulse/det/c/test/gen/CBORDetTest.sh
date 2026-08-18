#!/usr/bin/env bash
set -e
set -x

# Switch to the directory of this script
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

dune build
if ! [[ -e appendix_a.json ]] ; then
    curl https://raw.githubusercontent.com/cbor/test-vectors/master/appendix_a.json -o appendix_a.json
fi
if ! [[ -e utf8tests.txt ]] ; then
    curl https://raw.githubusercontent.com/flenniken/utf8tests/refs/heads/main/utf8tests.txt -o utf8tests.txt
fi
_build/default/GenCBORDetTest.exe > ../CBORDetTest.c

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
_build/default/GenCBORDetTest.exe appendix_a.json > ../tests/unit.rs

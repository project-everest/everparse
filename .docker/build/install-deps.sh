#!/usr/bin/env bash

set -e
set -x

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
opam depext conf-gmp z3.4.8.5-1 conf-m4

# Identify the F* branch
FSTAR_BRANCH=$(jq -c -r '.BranchName' "$build_home"/config.json)

# Install F*
[[ -n "$FSTAR_DIR" ]]
git clone --branch $FSTAR_BRANCH https://github.com/FStarLang/FStar "$FSTAR_DIR"
opam install --deps-only "$FSTAR_DIR/fstar.opam"
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$FSTAR_DIR"

# Only to build karamel below. NB the dockerfile also set this to the same value.
export FSTAR_EXE=$FSTAR_DIR/bin/fstar.exe

# Install other EverParse deps
"$build_home"/install-other-deps.sh

#!/usr/bin/env bash

set -e
set -x

args=( "$@" )
skip_build=false
skip_z3=false
while [[ -n "$1" ]]
do
    if [[ "$1" = "--skip-build" ]] ; then
	skip_build=true
    elif [[ "$1" = "--no-skip-build" ]] ; then
	skip_build=false
    elif [[ "$1" = "--skip-z3" ]] ; then
	skip_z3=true
    elif [[ "$1" = "--no-skip-z3" ]] ; then
	skip_z3=false
    fi
    shift
done

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
opam depext conf-gmp z3.4.8.5-1 conf-m4

# Identify the F* branch
FSTAR_BRANCH=$(jq -c -r '.BranchName' "$build_home"/config.json)

# Install F*
[[ -n "$FSTAR_DIR" ]]
git clone --branch $FSTAR_BRANCH https://github.com/FStarLang/FStar "$FSTAR_DIR"
opam install --deps-only "$FSTAR_DIR/fstar.opam"
if ! $skip_z3 ; then
    "$FSTAR_DIR/bin/get_fstar_z3.sh" "$FSTAR_DIR/z3-versions"
    export PATH="$FSTAR_DIR/z3-versions:$PATH"
fi
$skip_build || make -j 24 -C "$FSTAR_DIR" ADMIT=1
export FSTAR_EXE="$FSTAR_DIR/bin/fstar.exe"

# Install other EverParse deps
"$build_home"/install-other-deps.sh "${args[@]}"

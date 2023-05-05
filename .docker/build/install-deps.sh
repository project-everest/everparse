#!/usr/bin/env bash

set -e
set -x

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
opam depext conf-gmp z3.4.8.5 conf-m4

# Identify the F* branch
if [[ -z "$FSTAR_BRANCH" ]] ; then
FSTAR_BRANCH=$(jq -c -r '.BranchName' "$build_home"/config.json)
fi

# Install F*
[[ -n "$FSTAR_HOME" ]]
git clone --branch $FSTAR_BRANCH https://github.com/FStarLang/FStar "$FSTAR_HOME"
opam install --deps-only "$FSTAR_HOME/fstar.opam"
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$FSTAR_HOME"

# Identify the Karamel branch
if [[ -z "$KRML_BRANCH" ]] ; then
KRML_BRANCH=$(jq -c -r '.RepoVersions.karamel_version' "$build_home"/config.json | sed 's!^origin/!!')
fi

# Install Karamel and its dependencies
[[ -n "$KRML_HOME" ]]
git clone --branch $KRML_BRANCH https://github.com/FStarLang/karamel "$KRML_HOME"
pushd $KRML_HOME
.docker/build/install-other-deps.sh
popd
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$KRML_HOME"

# Identify the Steel branch
if [[ -z "$STEEL_BRANCH" ]] ; then
STEEL_BRANCH=$(jq -c -r '.RepoVersions.steel_version' "$build_home"/config.json | sed 's!^origin/!!')
fi

# Install Steel and its dependencies
[[ -n "$STEEL_HOME" ]]
git clone --branch $STEEL_BRANCH https://github.com/FStarLang/steel "$STEEL_HOME"
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$STEEL_HOME"

# Install other EverParse deps
"$build_home"/install-other-deps.sh

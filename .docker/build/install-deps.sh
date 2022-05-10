#!/usr/bin/env bash

set -e
set -x

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
opam depext conf-gmp z3.4.8.5 conf-m4

# Identify the F* branch
FSTAR_BRANCH=$(jq -c -r '.BranchName' "$build_home"/config.json)

# Install F*
[[ -n "$FSTAR_HOME" ]]
git clone --branch $FSTAR_BRANCH https://github.com/FStarLang/FStar "$FSTAR_HOME"
opam install --deps-only "$FSTAR_HOME/fstar.opam"
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$FSTAR_HOME"

# Identify the Karamel branch
KRML_BRANCH=$(jq -c -r '.RepoVersions.karamel_version' "$build_home"/config.json | sed 's!^origin/!!')

# Install Karamel and its dependencies
[[ -n "$KRML_HOME" ]]
git clone --branch $KRML_BRANCH https://github.com/FStarLang/karamel "$KRML_HOME"
pushd $KRML_HOME
.docker/build/install-other-deps.sh
popd
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$KRML_HOME"

# Install other EverParse deps
"$build_home"/install-other-deps.sh

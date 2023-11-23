#!/usr/bin/env bash

set -e
set -x

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

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
if [[ -n "$STEEL_HOME" ]] ; then
    git clone --branch $STEEL_BRANCH https://github.com/FStarLang/steel "$STEEL_HOME"
    OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$STEEL_HOME"
fi

opam install hex re ctypes sha sexplib

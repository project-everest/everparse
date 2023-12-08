#!/usr/bin/env bash

set -e
set -x

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Identify the Karamel branch
KRML_BRANCH=$(jq -c -r '.RepoVersions.karamel_version' "$build_home"/config.json | sed 's!^origin/!!')

# Install Karamel and its dependencies
[[ -n "$KRML_HOME" ]]
git clone --branch $KRML_BRANCH https://github.com/FStarLang/karamel "$KRML_HOME"
pushd $KRML_HOME
.docker/build/install-other-deps.sh
popd
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$KRML_HOME"

opam install hex re ctypes sha sexplib

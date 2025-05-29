#!/usr/bin/env bash

set -e
set -x

skip_build=false
while [[ -n "$1" ]] ;
do
    if [[ "$1" = "--skip-build" ]] ; then
	skip_build=true
    elif [[ "$1" = "--no-skip-build" ]] ; then
	skip_build=false
    fi
    shift
done

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Identify the Karamel branch
KRML_BRANCH=$(jq -c -r '.RepoVersions.karamel_version' "$build_home"/config.json | sed 's!^origin/!!')

# Install Karamel and its dependencies
[[ -n "$KRML_HOME" ]]
git clone --branch $KRML_BRANCH https://github.com/FStarLang/karamel "$KRML_HOME"
pushd $KRML_HOME
.docker/build/install-other-deps.sh
popd
$skip_build || OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$KRML_HOME"

# Identify the Pulse branch
PULSE_BRANCH=$(jq -c -r '.RepoVersions.pulse_version' "$build_home"/config.json | sed 's!^origin/!!')

# Install Pulse and its dependencies
# NOTE: $PULSE_HOME should now be $PULSE_REPO/out, cf. FStarLang/pulse#246
[[ -n "$PULSE_REPO" ]]
git clone --branch $PULSE_BRANCH https://github.com/FStarLang/pulse "$PULSE_REPO"
$skip_build || OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$PULSE_REPO"

opam install hex re ctypes sha sexplib

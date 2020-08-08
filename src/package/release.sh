#!/bin/bash

set -e

if [[ -z "$QD_HOME" ]] ; then
    if ! [[ -f src/rfc_fstar_compiler.ml ]] ; then
        echo QuackyDucky not found
        exit 1
    fi
    # This file MUST be run from the EverParse root directory
    export QD_HOME=$PWD
fi

if [[ -z "$SATS_TOKEN" ]] ; then
    echo Missing environment variable: SATS_TOKEN
    exit 1
fi

if [[ -z "$OS" ]] ; then
    OS=$(uname)
fi

is_windows=false
if [[ "$OS" = "Windows_NT" ]] ; then
   is_windows=true
fi

git fetch
git pull --ff-only

everparse_version=$(cat $QD_HOME/version.txt)
everparse_last_version=$(git show --no-patch --format=%h $everparse_version || true)
everparse_commit=$(git show --no-patch --format=%h)
push_new_tag=false
if [[ $everparse_commit != $everparse_last_version ]] ; then
    everparse_version=$(date '+test-v%Y.%m.%d')
    echo $everparse_version > $QD_HOME/version.txt
    git add $QD_HOME/version.txt
    git commit -m "Release $everparse_version"
    push_new_tag=true
fi

everparse_version=$everparse_version src/package/package.sh -zip

# push my commit and the tag
if $push_new_tag ; then
    branchname=$(git rev-parse --abbrev-ref HEAD)
    git tag $everparse_version
    git push origin $branchname $everparse_version
fi

platform=$(uname --machine)

if $is_windows ; then
    ext=.zip
else
    ext=.tar.gz
fi

docker build \
       -t everparse-release:$everparse_version \
       -f src/package/Dockerfile.release.$OS \
       --build-arg OS=$OS \
       --build-arg platform=$platform \
       --build-arg everparse_version=$everparse_version \
       --build-arg ext=$ext \
       .

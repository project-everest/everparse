#!/usr/bin/env bash

set -x

set -e # abort on errors

threads=$1
branchname=$2

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh

function fetch_and_make_karamel() {
    # Karamel is already supposed to have been built and fetched before
    # (e.g. by install-deps.sh)
    true
}

rootPath=$(pwd)
result_file="result.txt"
status_file="status.txt"
exec_build $target

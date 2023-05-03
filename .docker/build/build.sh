#!/usr/bin/env bash

#set -x
set -e

target=$1
out_file=$2
threads=$3
branchname=$4

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh
. "$build_home"/install-krml-funs.sh
. "$build_home"/install-steel-funs.sh
export_home FSTAR "$(pwd)/FStar"

cd quackyducky
result_file="../result.txt"
status_file="../status.txt"
rootPath=$(pwd)
exec_build
cd ..

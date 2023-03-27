#!/usr/bin/env bash

set -x

set -e # abort on errors

threads=$1
branchname=$2

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh
. "$build_home"/install-krml-funs.sh

# Clear EVERPARSE_HOME, which was set by F*'s build
unset EVERPARSE_HOME
sed -i -E "s|^EVERPARSE_HOME=.*||" ~/.bashrc

rootPath=$(pwd)
result_file="result.txt"
status_file="status.txt"

out_file="log.txt"
{ { { { { { exec_build ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDERR]!' ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDOUT]!' ; } 2>&1 ; } | awk '{ print strftime("[%Y-%m-%d %H:%M:%S]"), $0 }' | tee $out_file

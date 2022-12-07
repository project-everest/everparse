#!/usr/bin/env bash
# This script builds F* and EverParse, assuming that their build
# dependencies are all installed.
set -e
set -x
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
pwd | grep '/src/package/windows$' > /dev/null
cd ../../..
# This config is necessary if everparse was cloned with non-Cygwin git
git config --global --add safe.directory $(pwd)
# Revert the submodules back to a clean working copy
submodules="FStar karamel hacl-star"
rm -rf $submodules
git checkout $submodules
git submodule update --init
rm -rf everparse* EverParse* nuget_package
export EVERPARSE_MAKE_OPTS='-j 12'
if [[ "$1" = "--release" ]] ; then
    make release
else
    make everparse
fi

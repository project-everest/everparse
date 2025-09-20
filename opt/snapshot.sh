#!/usr/bin/env bash
set -e
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
projects="FStar karamel pulse"
for f in $projects
do
    pushd $f
    g=$f"_hash"
    declare $g=$(git rev-parse HEAD)
    popd
done
rm -f hashes.Makefile hashes.Makefile.tmp
touch hashes.Makefile.tmp
for f in $projects
do
    g=$f"_hash"
    echo $f"_hash := "${!g} >> hashes.Makefile.tmp
done
mv hashes.Makefile.tmp hashes.Makefile
touch hashes.Makefile

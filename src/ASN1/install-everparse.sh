#!/bin/bash

set -e

if [[ -z "$CI_THREADS" ]] ; then
    CI_THREADS=1
fi

if [[ -n "$NO_INTERACTIVE" ]] ; then
    NO_INTERACTIVE=--yes
fi

git clone https://github.com/project-everest/everest.git everest
pushd everest
if ! ./everest $NO_INTERACTIVE opam z3 ; then
    echo "Please follow the instructions above and re-run this script"
    exit 1
fi
export PATH=$PWD/z3/bin:$PATH
./everest $NO_INTERACTIVE reset
./everest $NO_INTERACTIVE -j "$CI_THREADS" FStar make karamel make
make -C everparse -j "$CI_THREADS" lowparse

echo "Please set the following environment variables:"
echo "FSTAR_EXE=$(pwd)/FStar/bin/fstar.exe"
echo "KRML_HOME=$(pwd)/karamel"
echo "EVERPARSE_HOME=$(pwd)/everparse"
popd

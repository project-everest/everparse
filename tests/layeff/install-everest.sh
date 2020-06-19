#!/bin/bash
set -e
set -x
git clone https://github.com/project-everest/everest.git
old_pwd="$PWD"
everest_home="$old_pwd/everest"
cd "$everest_home"
./everest --yes opam
if ! z3=$(which z3) ; then
    ./everest --yes z3
    export z3path="$everest_home/z3/bin"
else
    z3path=$(dirname "$z3")
fi
export PATH="$z3path":"$PATH"
if [[ -z "$EVEREST_THREADS" ]]
then
    EVEREST_THREADS=1
fi
if [[ -n "$FSTAR_HOME" ]] ; then
    cd "$FSTAR_HOME"
    git fetch
    git checkout _c_layeff
else
    git clone --branch _c_layeff https://github.com/FStarLang/FStar.git FStar
    export FSTAR_HOME=$everest_home/FStar
fi
cd "$FSTAR_HOME"
make -j $EVEREST_THREADS -k
cd "$everest_home"
if [[ -z "$KREMLIN_HOME" ]] ; then
    git clone https://github.com/FStarLang/kremlin.git kremlin
    export KREMLIN_HOME=$everest_home/kremlin
fi
cd "$KREMLIN_HOME"
make -j $EVEREST_THREADS -k
cd "$old_pwd"
cat >everest-env.sh <<EOF
export PATH=$z3path:\$PATH
export FSTAR_HOME=$FSTAR_HOME
export KREMLIN_HOME=$KREMLIN_HOME
EOF
echo Please set up your environment by running:
echo source everest-env.sh

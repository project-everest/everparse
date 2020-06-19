#!/bin/bash
set -e
set -x
git clone https://github.com/project-everest/everest.git
old_pwd="$PWD"
everest_home="$old_pwd/everest"
export FSTAR_HOME=$everest_home/FStar
export KREMLIN_HOME=$everest_home/kremlin
cd "$FSTAR_HOME"
git checkout _c_layeff
cd "$everest_home"
./everest --yes opam
./everest --yes reset
./everest --yes z3
export PATH=$everest_home/z3/bin:$PATH
if [[ -z "$EVEREST_THREADS" ]]
then
    EVEREST_THREADS=1
fi
OTHERFLAGS='--admit_smt_queries true' ./everest -j $EVEREST_THREADS FStar make kremlin make
cd "$old_pwd"
cat >everest-env.sh <<EOF
export PATH=$everest_home/z3/bin:\$PATH
export FSTAR_HOME=$FSTAR_HOME
export KREMLIN_HOME=$KREMLIN_HOME
EOF
echo Please set up your environment by running:
echo source everest-env.sh

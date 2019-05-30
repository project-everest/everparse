#!/bin/bash

KREMLIN_HOME=/home/jonathan/Code/kremlin
PATH=/home/jonathan/opt/compcert/bin:$PATH

for c in "ccomp -fstruct-passing" gcc-7 "gcc-7 -O2" "gcc-7 -O3" gcc-8 "gcc-8 -O2" "gcc-8 -O3" clang-7 "clang-7 -O2" "clang-7 -O3" clang-8 "clang-8 -O2" "clang-8 -O3"; do
  rm -rf a.out *.o
  $c -I $KREMLIN_HOME/include -I . -DKRML_VERIFIED_UINT128 -D_DEFAULT_SOURCE $(ls *.c | grep -v Test) $KREMLIN_HOME/kremlib/dist/generic/libkremlib.a &> log
  echo $c && ./a.out
done

chmod a+rw log
rm -rf a.out

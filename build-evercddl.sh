#!/bin/bash
set -e
set -x
make _opam
opam exec -- make -j -C opt
OTHERFLAGS='--admit_smt_queries true' opam exec -- make -j 8 cddl

#!/bin/bash
set -e
set -x
make _opam
opam exec -- make -j -C opt
opam exec -- make -j 8 -k cddl

#!/usr/bin/env bash
unset CDPATH
SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
# Print OPAM environment in GNU Makefile format
opam env --root=opam --set-root --shell=sh | $SED 's!^\([^=]*\)='"'"'\(.*\)'"'"'; export [^;]*;$!export \1 := \2!'

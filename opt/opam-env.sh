#!/usr/bin/env bash
unset CDPATH
SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
# Print OPAM environment in GNU Makefile format
opam env --root=opam --set-root --shell=sh | grep -v '^PATH=' | $SED 's!^\([^=]*\)='"'"'\(.*\)'"'"'; export [^;]*;$!export \1 := \2!'
echo 'export PATH := '"$(pwd)/opam/$(opam switch --root=opam show)/bin"':$(PATH)'

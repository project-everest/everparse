#!/usr/bin/env bash
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
if ! [[ "$EVERPARSE_USE_OPAMROOT" = 1 ]] ; then
        OPAMROOT="$(pwd)/opam"
elif [[ -z "$OPAMROOT" ]] ; then
	OPAMROOT="$(opam var root | $SED 's!\r!!g')"
fi
if [[ "$OS" = Windows_NT ]] ; then
    OPAMROOT="$(cygpath -m "$OPAMROOT")"
fi
root_opam="--root=$OPAMROOT"
opam env "$root_opam" --set-root --shell=sh | grep -v '^PATH=' |
    if [[ "$1" = --shell ]] ; then
	cat
    else
	$SED 's!^\([^=]*\)='"'"'\(.*\)'"'"'; export [^;]*;$!export \1 := \2!'
    fi
if [[ "$1" = --shell ]] ; then
    equal="='"
    epath="'"':"$PATH"'
    eocamlpath=";'"'"$OCAMLPATH"'
else
    equal=':='
    epath=':$(PATH)'
    eocamlpath=';$(OCAMLPATH)'
fi
if [[ "$OS" = Windows_NT ]] ; then
    # Work around an opam bug about `opam var lib`
    echo 'export OCAMLPATH'$equal"$(cygpath -m "$OPAMROOT")/$(opam switch "$root_opam" show | $SED 's!\r!!g')/lib$eocamlpath"
    # convert back because I need Unix-style PATH
    OPAMROOT="$(cygpath -u "$OPAMROOT")"
fi
echo 'export PATH'$equal"$OPAMROOT/$(opam switch "$root_opam" show | $SED 's!\r!!g')/bin$epath"

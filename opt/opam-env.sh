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
opam env "$root_opam" --set-root --shell=sh |
    if [[ "$1" = --shell ]] ; then
        $SED 's!^PATH=\(.*\); export PATH;$!PATH=\1:"$PATH"; export PATH;!'
    else
	$SED 's!^\([^=]*\)='"'"'\(.*\)'"'"'; export [^;]*;$!export \1 := \2!' |
	$SED 's!^export PATH := \(.*\)$!export PATH := \1:$(PATH)!'
    fi
if [[ "$1" = --shell ]] ; then
    equal="="
    if [[ "$OS" = Windows_NT ]] ; then
	eocamlpath="';'"'"$OCAMLPATH"'
	eopamswitchprefixunix='"$(cygpath -u "$OPAM_SWITCH_PREFIX")"'
	eopamswitchprefixwindows='"$(cygpath -m "$OPAM_SWITCH_PREFIX")"'
    else
	eocamlpath=':"$OCAMLPATH"'
	eopamswitchprefixunix='$OPAM_SWITCH_PREFIX'
    fi
else
    equal=':='
    if [[ "$OS" = Windows_NT ]] ; then
	eopamswitchprefixunix='$(shell cygpath -u "$(OPAM_SWITCH_PREFIX)")'
	eopamswitchprefixwindows='$(shell cygpath -m "$(OPAM_SWITCH_PREFIX)")'
	eocamlpath=';$(OCAMLPATH)'
    else
	eopamswitchprefixunix='$(OPAM_SWITCH_PREFIX)'
	eocamlpath=':$(OCAMLPATH)'
    fi
fi
if [[ "$OS" = Windows_NT ]] ; then
    # Work around an opam bug about `opam var lib`
    echo 'export OCAMLPATH'"$equal$eopamswitchprefixwindows/lib$eocamlpath"
fi

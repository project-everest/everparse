# This file is meant to be sourced rather than run
if [[ -z "$OS" ]] ; then
  OS=$(uname)
fi
if [[ "$OS" != "Darwin" ]] ; then
   MAKE=make
else
   MAKE=gmake
fi
$MAKE -C "$EVERPARSE_HOME" -f deps.Makefile -s
eval "$($MAKE -C "$EVERPARSE_HOME" -f deps.Makefile -s env)"

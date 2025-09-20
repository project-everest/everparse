# This file is meant to be sourced rather than run
if [[ "$OS" = "Windows_NT" ]] ; then
   MAKE=make
else
   MAKE="$(which gmake >/dev/null 2>&1 && echo gmake || echo make)"
fi
$MAKE -C "$EVERPARSE_HOME" -f deps.Makefile -s
eval "$($MAKE -C "$EVERPARSE_HOME" -f deps.Makefile -s env)"

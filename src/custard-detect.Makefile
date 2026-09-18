# Is the F* we are about to run a Custard-capable one?
#
# Custard lives on F*'s `gebner_custard` branch (FStarLang/FStar#4395) and is
# not in any released F*.  The committed CBOR and COSE snapshots are Custard's
# output, but the .fst sources must keep building with a released F*, so the
# extraction backend is chosen from the compiler at hand rather than
# hardcoded.  Set CUSTARD explicitly to override.
#
# This is a separate fragment from custard.Makefile because the decision has
# to be available at parse time, before the Makefiles that need it have set up
# the variables custard.Makefile depends on.

FSTAR_EXE ?= fstar.exe

CUSTARD_AVAILABLE := $(shell $(FSTAR_EXE) --help 2>/dev/null | grep -q -- --custard_backend && echo 1 || echo 0)

CUSTARD ?= $(CUSTARD_AVAILABLE)

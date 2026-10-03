# Run from a built source tree:
#   make -C src/3d/tests/pulse-lowstar-diff-tests/adapter-tests check
#   make -C src/3d/tests/pulse-lowstar-diff-tests/adapter-tests check32
# Add SANITIZE=1 for ASan/UBSan on the host-width C tests.
#
# check verifies/extracts the O(1) >2^32 counter fixture, reuses the original
# extern/static clients for Read/Peep assertions, and exercises scoped probe
# views through extern, native Pulse buffer, and Low* ABI buffer instances.
# The native specialization batch also rejects new shared callback headers.
# check32 requires real -m32 support; it never silently substitutes a size model.
# native-probe runs the existing native Z3-generated probe harness in both modes.
# Standalone artifacts/logs stay in _build/; native-probe uses upstream outputs.
PYTHON ?= python3
JOBS ?= 16
ROOT := $(realpath ../../../../..)

.PHONY: all check check32 runtime large large32 extern static probes native-probe
all: check

runtime:
	+$(MAKE) -C $(ROOT) -j$(JOBS) 3d-pulse-krml

check: runtime
	$(PYTHON) run.py all

# Unlike check, this requires a working 32-bit compiler and runtime.
check32: runtime
	$(PYTHON) run.py large32

native-probe: runtime
	+$(MAKE) -C $(ROOT)/share/everparse/tests/3d pulse-z3-testgen-probe-test

large large32 extern static probes:
	$(PYTHON) run.py $@

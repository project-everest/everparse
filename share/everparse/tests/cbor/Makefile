# EverCBOR benchmark/conformance tests.
#
# Compiles share/everparse/tests/cbor/cbor_tests.c twice — once against the
# non-deterministic snapshot, once against the deterministic snapshot —
# and runs each of the two resulting binaries.
#
# A Python harness (cbor_tests.py) then re-validates the artefacts written
# by the C binaries against the cbor2 library, exercising cross-language
# conformance.
#
# Override the snapshot locations on the command line if needed:
#
#   make EVERCBOR_NONDET_PATH=/path/to/nondet/c \
#        EVERCBOR_DET_PATH=/path/to/det/c
#
# The snapshot directory must contain the corresponding header(s) and
# pre-built object file (CBORNondet.o or CBORDet.o, plus its dependencies).

# Default snapshot locations: the in-tree C extractions.
EVERCBOR_NONDET_PATH ?= $(realpath $(CURDIR)/../../../../src/cbor/pulse/nondet/c)
EVERCBOR_DET_PATH    ?= $(realpath $(CURDIR)/../../../../src/cbor/pulse/det/c)

# Number of iterations for benchmarking. Override on the command line to make
# timing measurements more reliable, e.g. BENCH_ITERATIONS=1000.
# A value of 10000 keeps total runtime under ~10s for both binaries.
BENCH_ITERATIONS ?= 10000

# Python iteration count (the Python tests are slower per iteration so a
# smaller default keeps total runtime in the same ballpark).
PYTHON_ITERATIONS ?= 1000

CC      ?= cc
CFLAGS  ?= -O2 -Wall

# The non-deterministic snapshot ships only CBORNondet.o.
NONDET_OBJS = $(EVERCBOR_NONDET_PATH)/CBORNondet.o

# The deterministic snapshot ships CBORDet.o plus auxiliary object files.
DET_OBJS    = $(EVERCBOR_DET_PATH)/CBORDet.o \
              $(EVERCBOR_DET_PATH)/CBORDetAbstract.o \
              $(EVERCBOR_DET_PATH)/CBORDetSizeCheck.o

SRC = $(CURDIR)/cbor_tests.c

NONDET_BIN = cbor_tests_nondet.exe
DET_BIN    = cbor_tests_det.exe

# Directory into which the C binaries write artefact files for the
# Python harness to consume.
OUT_DIR = $(CURDIR)/out

# Python virtual environment used to run the cross-language tests.
PYTHON       ?= python3
VENV_DIR      = $(CURDIR)/.venv
VENV_PYTHON   = $(VENV_DIR)/bin/python
PY_SRC        = $(CURDIR)/cbor_tests.py
# Pin a cbor2 floor that includes the Rust rewrite (immutable / allow_indefinite
# decoder flags). 6.0.x is the first family with that codebase.
CBOR2_REQ    ?= cbor2>=6.0,<7

.PHONY: all build run run-nondet run-det run-python clean
.PHONY: build-nondet build-det venv

all: run

build: build-nondet build-det

build-nondet: $(NONDET_BIN)
build-det:    $(DET_BIN)

$(NONDET_BIN): $(SRC) $(NONDET_OBJS)
	$(CC) $(CFLAGS) -DEVERCBOR_NONDET -DBENCH_ITERATIONS=$(BENCH_ITERATIONS) \
	    -I $(EVERCBOR_NONDET_PATH) \
	    -o $@ $(SRC) $(NONDET_OBJS)

$(DET_BIN): $(SRC) $(DET_OBJS)
	$(CC) $(CFLAGS) -DEVERCBOR_DET -DBENCH_ITERATIONS=$(BENCH_ITERATIONS) \
	    -I $(EVERCBOR_DET_PATH) \
	    -o $@ $(SRC) $(DET_OBJS)

run: run-c run-python

# C-only run target. Used by nofstar.Makefile's cbor-shared-c-test so that
# the unverified-test pipeline doesn't gain a Python/network dependency.
run-c: run-nondet run-det
.PHONY: run-c

run-nondet: $(NONDET_BIN)
	CBOR_TEST_OUT_DIR=$(OUT_DIR) ./$(NONDET_BIN)

run-det: $(DET_BIN)
	CBOR_TEST_OUT_DIR=$(OUT_DIR) ./$(DET_BIN)

# Build (or refresh) the virtual environment containing the Python cbor2
# library used by the cross-language harness. The sentinel is the venv's
# python interpreter; the install step is a separate target so that the
# pip install runs once per fresh venv rather than on every make run.
$(VENV_PYTHON):
	$(PYTHON) -m venv $(VENV_DIR)
	$(VENV_PYTHON) -m pip install --upgrade pip
	$(VENV_PYTHON) -m pip install '$(CBOR2_REQ)'

venv: $(VENV_PYTHON)

# Run the Python harness against the artefacts emitted by the C binaries.
# Depends on the C runs so that the artefacts exist on disk first.
run-python: run-nondet run-det $(VENV_PYTHON) $(PY_SRC)
	$(VENV_PYTHON) $(PY_SRC) --out-dir $(OUT_DIR) --iterations $(PYTHON_ITERATIONS)

clean:
	rm -f $(NONDET_BIN) $(DET_BIN)
	rm -rf $(OUT_DIR) $(VENV_DIR)

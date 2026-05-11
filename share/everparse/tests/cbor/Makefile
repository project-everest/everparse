# EverCBOR benchmark/conformance tests.
#
# Compiles share/everparse/tests/cbor/cbor_tests.c twice — once against the
# non-deterministic snapshot, once against the deterministic snapshot —
# and runs each of the two resulting binaries.
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

.PHONY: all build run run-nondet run-det clean
.PHONY: build-nondet build-det

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

run: run-nondet run-det

run-nondet: $(NONDET_BIN)
	./$(NONDET_BIN)

run-det: $(DET_BIN)
	./$(DET_BIN)

clean:
	rm -f $(NONDET_BIN) $(DET_BIN)

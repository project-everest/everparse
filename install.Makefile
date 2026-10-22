PREFIX ?= /usr/local

LOWPARSE_SRC_DIR := lib/everparse/lowparse
LOWPARSE_FILES := $(wildcard $(addprefix $(LOWPARSE_SRC_DIR)/*.,fst fsti checked))

all: install-makefiles install-lowparse install-quackyducky

all: install-3d

# EverCBOR and EverCDDL are not built at all when only 3d is requested, so
# there is nothing to install then. Mirrors the EVERPARSE_ONLY_3D guard on
# `package-subset` in the top-level Makefile.
ifneq (1,$(EVERPARSE_ONLY_3D))

all: install-cbor

all: install-cddl

endif

install-makefiles:
	install -d $(PREFIX)/lib/everparse
	install -m 644 $(filter-out %-exe.Makefile,$(wildcard lib/everparse/*.Makefile)) $(PREFIX)/lib/everparse

install-lowparse:
	install -d $(PREFIX)/lib/everparse/lowparse
	install -m 644 $(LOWPARSE_FILES) $(PREFIX)/lib/everparse/lowparse

install-quackyducky:
	install -d $(PREFIX)/bin
	install -m 755 bin/everparse-qd.exe $(PREFIX)/bin

# EverParseEndianness.h, EverParsePulse{,Endianness}.h, noheader.txt,
# copyright.txt, .clang-format and Makefile.basic are the 3d runtime support
# proper: they are checked-in sources needed by every API and backend. The rest
# of lib/everparse/3d is the Pulse combinator library, which only exists when
# Pulse is enabled, hence install-3d-pulse below.
install-3d:
	install -d $(PREFIX)/lib/everparse/3d
	install -m 644 $(wildcard $(addprefix lib/everparse/3d/*.,txt h)) $(PREFIX)/lib/everparse/3d
	install -m 644 $(addprefix lib/everparse/3d/,Makefile.basic .clang-format cl-wrapper.cmd) $(PREFIX)/lib/everparse/3d
	install -d $(PREFIX)/bin
	install -m 755 bin/everparse-3d.exe $(PREFIX)/bin

ifeq (,$(NO_PULSE))
install-3d: install-3d-pulse
endif

# The Pulse 3d combinator library: sources and .checked files for the F*
# --include path and the pre-generated per-backend runtime headers and units.
install-3d-pulse:
	install -d $(PREFIX)/lib/everparse/3d
	install -m 644 $(wildcard $(addprefix lib/everparse/3d/*.,fst fsti checked)) $(PREFIX)/lib/everparse/3d
	for parent in "" lowstar/ ; do for backend in buffer extern static ; do \
	  source=lib/everparse/3d/krml/$$parent$$backend ; \
	  destination=$(PREFIX)/$$source ; \
	  install -d $$destination/src $$destination/checked && \
	  install -m 644 $$source/EverParse.h $$source/EverParse.cui $$destination && \
	  install -m 644 $$source/src/*.fst $$source/src/*.fsti $$destination/src && \
	  install -m 644 $$source/checked/*.checked $$destination/checked || exit 1 ; \
	done ; done
	for parent in "" lowstar/ ; do install -m 644 lib/everparse/3d/krml/$${parent}static/EverParseStreamPrimitives.h $(PREFIX)/lib/everparse/3d/krml/$${parent}static ; done

.PHONY: install-3d install-3d-pulse

install-cbor:
	install -d $(PREFIX)/include/everparse
	install -m 644 $(wildcard include/everparse/CBOR*.h) $(PREFIX)/include/everparse
	install -m 644 include/everparse/krmllib.h $(PREFIX)/include/everparse
	install -d $(PREFIX)/lib/everparse
	install -m 644 $(addprefix lib/everparse/,CBORDet.o CBORNondet.o) $(PREFIX)/lib/everparse
	install -d $(PREFIX)/lib/everparse/cbor/spec/raw/everparse
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/spec/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/spec
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/spec/raw/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/spec/raw
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/spec/raw/everparse/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/spec/raw/everparse

ifeq (,$(NO_PULSE))
install-cbor: install-cbor-pulse
endif

install-cbor-pulse:
	install -d $(PREFIX)/lib/everparse/cbor/pulse/raw/everparse
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/raw/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse/raw
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/raw/everparse/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse/raw/everparse
	install -d $(PREFIX)/lib/everparse/cbor/pulse/raw/slice-rust
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/raw/slice-rust/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse/raw/slice-rust
	install -d $(PREFIX)/lib/everparse/cbor/pulse/raw/slice-c
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/raw/slice-c/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse/raw/slice-c

.PHONY: install-cbor install-cbor-pulse

install-cddl:
	install -d $(PREFIX)/lib/everparse/cddl
	install -m 644 lib/everparse/cddl/noheader.txt $(PREFIX)/lib/everparse/cddl
	install -d $(PREFIX)/lib/everparse/cddl/spec
	install -m 644 $(wildcard $(addprefix lib/everparse/cddl/spec/*.,fst fsti checked cddl)) $(PREFIX)/lib/everparse/cddl/spec

# The CDDL tool and the Pulse part of the CDDL library are only built when
# Pulse is enabled (`cddl-tool` is empty under NO_PULSE.)
ifeq (,$(NO_PULSE))
install-cddl: install-cddl-pulse
endif

install-cddl-pulse:
	install -d $(PREFIX)/bin
	install -m 755 bin/everparse-cddl.exe $(PREFIX)/bin
	install -d $(PREFIX)/lib/everparse/cddl/pulse
	install -m 644 $(wildcard $(addprefix lib/everparse/cddl/pulse/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cddl/pulse

.PHONY: install-cddl install-cddl-pulse

.PHONY: all install-makefiles install-lowparse install-quackyducky

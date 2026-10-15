PREFIX ?= /usr/local

LOWPARSE_SRC_DIR := lib/everparse/lowparse
LOWPARSE_FILES := $(wildcard $(addprefix $(LOWPARSE_SRC_DIR)/*.,fst fsti checked))

all: install-makefiles install-lowparse install-quackyducky

all: install-3d

all: install-cbor

install-makefiles:
	install -d $(PREFIX)/lib/everparse
	install -m 644 $(wildcard lib/everparse/*.Makefile) $(PREFIX)/lib/everparse

install-lowparse:
	install -d $(PREFIX)/lib/everparse/lowparse
	install -m 644 $(LOWPARSE_FILES) $(PREFIX)/lib/everparse/lowparse

install-quackyducky:
	install -d $(PREFIX)/bin
	install -m 755 bin/everparse-qd.exe $(PREFIX)/bin

install-3d:
	install -d $(PREFIX)/lib/everparse/3d
	install -m 644 $(wildcard $(addprefix lib/everparse/3d/*.,txt fst fsti checked h)) $(PREFIX)/lib/everparse/3d
	install -m 644 $(addprefix lib/everparse/3d/,Makefile.basic .clang-format) $(PREFIX)/lib/everparse/3d
	install -d $(PREFIX)/lib/everparse/3d/krml/extracted
	install -m 644 lib/everparse/3d/krml/extracted/Custard.krml $(PREFIX)/lib/everparse/3d/krml/extracted
	for parent in "" lowstar/ ; do for backend in buffer extern static ; do install -d $(PREFIX)/lib/everparse/3d/krml/$$parent$$backend && install -m 644 lib/everparse/3d/krml/$$parent$$backend/EverParse.h $(PREFIX)/lib/everparse/3d/krml/$$parent$$backend ; done ; done
	install -d $(PREFIX)/bin
	install -m 755 bin/everparse-3d.exe $(PREFIX)/bin

.PHONY: install-3d

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
	install -d $(PREFIX)/lib/everparse/cbor/pulse/raw/everparse
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/raw/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse/raw
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/raw/everparse/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse/raw/everparse
	install -d $(PREFIX)/lib/everparse/cbor/pulse/raw/slice-rust
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/raw/slice-rust/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse/raw/slice-rust
	install -d $(PREFIX)/lib/everparse/cbor/pulse/raw/slice-c
	install -m 644 $(wildcard $(addprefix lib/everparse/cbor/pulse/raw/slice-c/*.,fst fsti checked)) $(PREFIX)/lib/everparse/cbor/pulse/raw/slice-c

.PHONY: install-cbor

.PHONY: all install-makefiles install-lowparse install-quackyducky

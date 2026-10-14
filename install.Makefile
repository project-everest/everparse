PREFIX ?= /usr/local

LOWPARSE_SRC_DIR := lib/everparse/lowparse
LOWPARSE_FILES := $(wildcard $(addprefix $(LOWPARSE_SRC_DIR)/*.,fst fsti checked))

all: install-makefiles install-lowparse install-quackyducky

install-makefiles:
	install -d $(PREFIX)/lib/everparse
	install -m 644 $(wildcard lib/everparse/*.Makefile) $(PREFIX)/lib/everparse

install-lowparse:
	install -d $(PREFIX)/lib/everparse/lowparse
	install -m 644 $(LOWPARSE_FILES) $(PREFIX)/lib/everparse/lowparse

install-quackyducky:
	install -d $(PREFIX)/bin
	install -m 755 bin/everparse-qd.exe $(PREFIX)/bin

.PHONY: all install-makefiles install-lowparse install-quackyducky

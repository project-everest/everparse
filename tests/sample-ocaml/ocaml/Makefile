FSTAR_HOME ?= $(realpath ../../../../FStar)

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/bin);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif
export OCAMLPATH

TEST_EXE=$(realpath .)/_build/default/Test.exe

all: build

build:
	dune build
	chmod +x $(TEST_EXE)
	touch -c $(TEST_EXE)

test: build
	$(TEST_EXE) < sample_input

clean:
	rm -rf _build generated

.PHONY: all clean build test

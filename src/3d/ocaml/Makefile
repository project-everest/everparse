FSTAR_EXE ?= fstar.exe

all: $(filter-out %~,$(wildcard *.ml*))
	$(FSTAR_EXE) --ocamlenv dune build

clean-local:
	rm -rf _build *~

clean: clean-local
	rm -rf generated

.PHONY: all clean clean-local

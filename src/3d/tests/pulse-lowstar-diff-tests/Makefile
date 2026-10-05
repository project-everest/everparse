PYTHON ?= python3
EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME
export FSTAR_EXE 3D_Z3_EXECUTABLE KRML_HOME CC CXX CFLAGS CXXFLAGS LDFLAGS

.PHONY: all test runtime adapters selftest inventory clean
all: test
test: runtime adapters
	+$(PYTHON) run.py --home "$(EVERPARSE_HOME)" $(ARGS)
runtime:
	$(PYTHON) -m unittest test_runtime -v
adapters:
	$(PYTHON) adapter-tests/run.py all
	$(PYTHON) adapter-tests/run.py large32
selftest:
	$(PYTHON) -m unittest discover -s . -p 'test_*.py' -v
inventory:
	$(PYTHON) run.py --home "$(EVERPARSE_HOME)" --inventory-only $(ARGS)
clean:
	$(PYTHON) run.py --clean

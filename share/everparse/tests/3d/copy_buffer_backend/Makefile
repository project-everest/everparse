# Regression test for `EVERPARSE_COPY_BUFFER_T` across the three input-stream
# backends under `--pulse`.
#
# Two halves:
#   - Test.3d mentions EVERPARSE_COPY_BUFFER_T without probing. It must be
#     ACCEPTED on buffer, extern and static. This half is `--batch`, not
#     `--no_batch`: the regression it guards against (the type being printed
#     as `B.copy_buffer_t`, which only the buffer backend's `B` defines) was
#     invisible to the frontend and surfaced as `Error 72` from F* on the
#     generated code.
#   - Probe.3d must be REJECTED on extern and static and ACCEPTED on buffer,
#     pinning the probe restriction. That half is generation-only, since the
#     frontend decides it.
#
# Nothing is run: there is no client stream implementation, only the two type
# names in EverParseStream.h. The extern and static tests cover the runtime.

EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE) --pulse \
  --input_stream_include EverParseStream.h

EVERPARSE_OUTPUT_DIR=obj

all: world

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

world: Test.3d Probe.3d | $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --batch --input_stream buffer --odir $(EVERPARSE_OUTPUT_DIR)/buffer.cb Test.3d
	$(EVERPARSE_CMD) --batch --input_stream extern --odir $(EVERPARSE_OUTPUT_DIR)/extern.cb Test.3d
	$(EVERPARSE_CMD) --batch --input_stream static --odir $(EVERPARSE_OUTPUT_DIR)/static.cb Test.3d
	$(EVERPARSE_CMD) --no_batch --input_stream buffer --odir $(EVERPARSE_OUTPUT_DIR)/buffer.probe Probe.3d
	! $(EVERPARSE_CMD) --no_batch --input_stream extern --odir $(EVERPARSE_OUTPUT_DIR)/extern.probe Probe.3d >$(EVERPARSE_OUTPUT_DIR)/extern.probe.out 2>&1
	grep -q 'only supported by the buffer backend' $(EVERPARSE_OUTPUT_DIR)/extern.probe.out
	! $(EVERPARSE_CMD) --no_batch --input_stream static --odir $(EVERPARSE_OUTPUT_DIR)/static.probe Probe.3d >$(EVERPARSE_OUTPUT_DIR)/static.probe.out 2>&1
	grep -q 'only supported by the buffer backend' $(EVERPARSE_OUTPUT_DIR)/static.probe.out
	@echo "PASS: EVERPARSE_COPY_BUFFER_T works on every input stream; probes are buffer-only"

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

.PHONY: all world clean

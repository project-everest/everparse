# Regression test for the backend restriction on the `field_pos_32` action
# (also spelled `field_pos`).
#
# `field_pos_32` narrows the validator position to 32 bits, which is only
# lossless when the whole input is addressed by a 32-bit length. Low* enforces
# that by giving `action_field_pos_32` a
# `squash (backend_flag == BackendFlagBuffer)` argument; the Pulse backend has
# no such witness, so the frontend rejects it instead.
#
# Two halves:
#   - Test.3d must be REJECTED on `extern` and `static`, ACCEPTED on `buffer`.
#   - Ok.3d (field_pos_64) must be ACCEPTED on all three, guarding against
#     over-restricting.
#
# Generation-only (`--no_batch`): what is under test is the frontend's
# accept/reject decision, so there is no need to pay for F* verification and
# KaRaMeL extraction. Nothing is run.

EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE) --pulse

EVERPARSE_OUTPUT_DIR=obj

all: world

$(EVERPARSE_OUTPUT_DIR):
	mkdir -p $@

world: Test.3d Ok.3d | $(EVERPARSE_OUTPUT_DIR)
	$(EVERPARSE_CMD) --no_batch --input_stream buffer --odir $(EVERPARSE_OUTPUT_DIR)/buffer.pos32 Test.3d
	! $(EVERPARSE_CMD) --no_batch --input_stream extern --odir $(EVERPARSE_OUTPUT_DIR)/extern.pos32 Test.3d >$(EVERPARSE_OUTPUT_DIR)/extern.pos32.out 2>&1
	grep -q 'field_pos_32 action' $(EVERPARSE_OUTPUT_DIR)/extern.pos32.out
	! $(EVERPARSE_CMD) --no_batch --input_stream static --odir $(EVERPARSE_OUTPUT_DIR)/static.pos32 Test.3d >$(EVERPARSE_OUTPUT_DIR)/static.pos32.out 2>&1
	grep -q 'field_pos_32 action' $(EVERPARSE_OUTPUT_DIR)/static.pos32.out
	$(EVERPARSE_CMD) --no_batch --input_stream buffer --odir $(EVERPARSE_OUTPUT_DIR)/buffer.pos64 Ok.3d
	$(EVERPARSE_CMD) --no_batch --input_stream extern --odir $(EVERPARSE_OUTPUT_DIR)/extern.pos64 Ok.3d
	$(EVERPARSE_CMD) --no_batch --input_stream static --odir $(EVERPARSE_OUTPUT_DIR)/static.pos64 Ok.3d
	@echo "PASS: field_pos_32 is buffer-only, field_pos_64 is unrestricted"

clean:
	rm -rf $(EVERPARSE_OUTPUT_DIR)

.PHONY: all world clean

# Tests for the C output style options of 3D: --hoist_locals,
# --init_locals c23|c99|c89, --line_comments and --goto_for_early_return.
#
# Locals.3d is extracted with --batch once per option set (a "variant"), each
# into its own output directory. Every variant is compiled with
# -Wall -Wextra -Werror and linked against the same driver, main.c, which must
# pass on all of them: these options change the shape of the generated C
# code, not its behavior. Then each option is checked to have the expected
# effect on the generated C code, against the default variant.
#
# share/everparse/tests/3d/lowstar/c_style_options runs this Makefile with
# EVERPARSE_API=lowstar.

SRC_DIR := $(patsubst %/,%,$(dir $(lastword $(MAKEFILE_LIST))))
EVERPARSE_HOME ?= $(realpath $(SRC_DIR)/../../../../..)
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile
EVERPARSE_API ?= pulse
EVERPARSE_EXE = $(EVERPARSE_HOME)/bin/everparse-3d.exe --api $(EVERPARSE_API) $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)")
OUTPUT_DIR = output

CC ?= cc

variants := default hoist_locals init_locals_c23 init_locals_c99 \
  init_locals_c89 line_comments goto_for_early_return all

options_default :=
options_hoist_locals := --hoist_locals
options_init_locals_c23 := --init_locals c23
options_init_locals_c99 := --init_locals c99
options_init_locals_c89 := --init_locals c89
options_line_comments := --line_comments
options_goto_for_early_return := --goto_for_early_return
options_all := --hoist_locals --init_locals c89 --line_comments \
  --goto_for_early_return

# The C standard each variant is compiled with. `--init_locals c23' emits
# empty initializers `= { }', which are C23-only.
std_default := c11
std_hoist_locals := c11
std_init_locals_c23 := c2x
std_init_locals_c99 := c11
std_init_locals_c89 := c11
std_line_comments := c11
std_goto_for_early_return := c11
std_all := c11

TEST_CFLAGS = -Wall -Wextra -Werror -pedantic

all: test

.PHONY: all test clean

# Generation, F* verification and C extraction
.PRECIOUS: $(OUTPUT_DIR)/%/.extracted
$(OUTPUT_DIR)/%/.extracted: $(SRC_DIR)/Locals.3d
	rm -rf $(OUTPUT_DIR)/$*
	mkdir -p $(OUTPUT_DIR)/$*
	$(EVERPARSE_EXE) --batch --odir $(OUTPUT_DIR)/$* $(options_$*) $<
	touch $@

# Compile the generated code with the driver, and run it
.PRECIOUS: $(OUTPUT_DIR)/%/test.exe
$(OUTPUT_DIR)/%/test.exe: $(OUTPUT_DIR)/%/.extracted $(SRC_DIR)/main.c
	$(CC) $(TEST_CFLAGS) -std=$(std_$*) -I $(OUTPUT_DIR)/$* -o $@ \
	  $(SRC_DIR)/main.c $(OUTPUT_DIR)/$*/Locals.c $(OUTPUT_DIR)/$*/LocalsWrapper.c

run_targets := $(addprefix run-,$(variants))
.PHONY: $(run_targets)
$(run_targets): run-%: $(OUTPUT_DIR)/%/test.exe
	$<

test: $(run_targets)

# --hoist_locals: no declaration after a statement in the generated
# validators. The generated .c file is compiled from a copy outside of its
# output directory, so that the EverParse headers, found with -isystem, are not
# subject to the warning.
hoisted_variants := hoist_locals all
decl_after_stmt = ( mkdir -p $(OUTPUT_DIR)/$1.copy && \
  cp $(OUTPUT_DIR)/$1/Locals.c $(OUTPUT_DIR)/$1.copy/ && \
  $(CC) -std=c11 -Werror=declaration-after-statement -isystem $(OUTPUT_DIR)/$1 \
    -c -o $(OUTPUT_DIR)/$1.copy/Locals.o $(OUTPUT_DIR)/$1.copy/Locals.c )

.PHONY: check-hoist_locals
check-hoist_locals: $(addprefix $(OUTPUT_DIR)/,$(addsuffix /.extracted,default $(hoisted_variants)))
	! $(call decl_after_stmt,default) 2>/dev/null
	$(foreach v,$(hoisted_variants),$(call decl_after_stmt,$v) &&) true

# --init_locals: no local variable declared without an initializer, in the
# generated validators and wrappers. `return x;' and `goto exit;' have the
# same shape as a declaration, so they are excluded.
initialized_variants := init_locals_c23 init_locals_c99 init_locals_c89 all
uninitialized_locals = grep -E '^[[:space:]]+[A-Za-z_][A-Za-z0-9_]*[[:space:]*]+[A-Za-z_][A-Za-z0-9_]*;$$' \
  $(OUTPUT_DIR)/$1/Locals.c $(OUTPUT_DIR)/$1/LocalsWrapper.c | grep -v -E ':[[:space:]]*(return|goto) '

.PHONY: check-init_locals
check-init_locals: $(addprefix $(OUTPUT_DIR)/,$(addsuffix /.extracted,default $(initialized_variants)))
	$(call uninitialized_locals,default) > /dev/null
	$(foreach v,$(initialized_variants),! $(call uninitialized_locals,$v) &&) true
	grep -q -E '= *\{ *\}' $(OUTPUT_DIR)/init_locals_c23/Locals.c
	! $(CC) -std=c11 -pedantic-errors -I $(OUTPUT_DIR)/init_locals_c23 -c -o $(OUTPUT_DIR)/init_locals_c23/Locals.c11.o $(OUTPUT_DIR)/init_locals_c23/Locals.c 2>/dev/null
	$(foreach v,init_locals_c99 init_locals_c89,! grep -q -E '= *\{ *\}' $(OUTPUT_DIR)/$v/Locals.c $(OUTPUT_DIR)/$v/LocalsWrapper.c &&) true

# --line_comments: no block comments in the generated validators.
line_comments_variants := line_comments all
block_comments = grep -q -F '/*' $(OUTPUT_DIR)/$1/Locals.c

.PHONY: check-line_comments
check-line_comments: $(addprefix $(OUTPUT_DIR)/,$(addsuffix /.extracted,default $(line_comments_variants)))
	$(call block_comments,default)
	$(foreach v,$(line_comments_variants),! $(call block_comments,$v) && grep -q -F '//' $(OUTPUT_DIR)/$v/Locals.c &&) true

# --goto_for_early_return: every early return of the generated validators and
# wrappers becomes a jump to the single exit label of its function, so that no
# function has more than one return statement. A function starts at a line
# that begins with an identifier character and ends with `{', or at a line
# that is just `{', and ends at a line that begins with `}'. (No `/' in a
# bracket expression: BSD awk ends the regex there.)
goto_variants := goto_for_early_return all
multi_return_functions = awk '/^[A-Za-z_].*\{$$/ || /^\{$$/ { n = 0 } \
    /(^|[^A-Za-z0-9_])return([^A-Za-z0-9_]|$$)/ { n++ } \
    /^\}/ { if (n > 1) m++ } END { print m + 0 }' $(OUTPUT_DIR)/$1/$2

.PHONY: check-goto_for_early_return
check-goto_for_early_return: $(addprefix $(OUTPUT_DIR)/,$(addsuffix /.extracted,default $(goto_variants)))
	test $$($(call multi_return_functions,default,Locals.c)) -gt 0
	! grep -q -F 'goto exit;' $(OUTPUT_DIR)/default/Locals.c $(OUTPUT_DIR)/default/LocalsWrapper.c
	$(foreach v,$(goto_variants),$(foreach f,Locals.c LocalsWrapper.c,test $$($(call multi_return_functions,$v,$f)) -eq 0 && grep -q -F 'goto exit;' $(OUTPUT_DIR)/$v/$f &&)) true

test: check-hoist_locals check-init_locals check-line_comments \
  check-goto_for_early_return

clean:
	rm -rf $(OUTPUT_DIR)

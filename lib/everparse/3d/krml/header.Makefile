# Pre-generation of the Pulse runtime header, EverParse.h, one per input stream
# backend.
#
# `3d.exe --pulse` used to rebuild this header on every invocation, bundling the
# whole runtime into the client's output directory with -static-header. That is
# wasteful, because the result does not depend on the .3d input at all: it is
# the fixed prelude (error codes, EverParseIsRangeOkay, the bitfield accessors)
# plus the backend's assumed stream primitives. So we generate it once here and
# ship it, exactly as the Low* backend does in src/3d/prelude/<backend>.
#
# 3d.exe then passes KaRaMeL -library instead of -static-header, which turns the
# runtime into plain `extern` declarations and drops them from the output, and
# copies the header generated here into the output directory. The generated
# validators are byte-identical either way.
#
# The flags below must stay in sync with krml_args/call_krml in
# src/3d/ocaml/Batch.ml; see the comments there for why each is needed.

all: headers

EVERPARSE_SRC_PATH := $(realpath ../../../../src)
# On Windows, $(realpath) yields a Cygwin path (/cygdrive/d/...) that the
# native krml.exe cannot open. windows.Makefile rewrites EVERPARSE_SRC_PATH
# with `cygpath -m`, so DDD_HOME must be derived *after* this include.
# The sibling extract.Makefile does the same.
include $(EVERPARSE_SRC_PATH)/windows.Makefile
DDD_HOME := $(EVERPARSE_SRC_PATH)/3d

BACKENDS := buffer extern static

KRML_FILES := $(wildcard extracted/*.krml)

# The bundle's API modules: those whose declarations stay public and so land in
# EverParse.h. Only the selected backend's module is listed, because each of
# Buffer/Extern/Static owns a [@@CMacro] error_handler_macro and making two
# public at once collides on EVERPARSE_ERROR_HANDLER_MACRO (KaRaMeL warning 23).
API_COMMON := EverParse3d.Actions.Common+EverParse3d.ErrorCode+EverParse3d.Prelude.StaticHeader
API_buffer := $(API_COMMON)+EverParse3d.CopyBuffer.Buffer
API_extern := $(API_COMMON)+EverParse3d.InputStream.Extern
# static re-exports extern's instance and has no extracted declarations of its own
API_static := $(API_extern)

# With `extern` (and `static`) the stream primitives are assumed vals that the
# client implements in C, so KaRaMeL's "no corresponding implementation"
# warning (2) is expected.
WARN_buffer := -9@4-20-26
WARN_extern := -9@4-20-26-2
WARN_static := $(WARN_extern)

define header_rule
$(1)/EverParse.h: $$(KRML_FILES)
	mkdir -p $(1)
	$$(KRML_EXE) \
	  -skip-compilation \
	  -skip-makefiles \
	  -tmpdir $(1) \
	  -minimal \
	  -header $$(DDD_HOME)/noheader.txt \
	  -add-include 'EverParse:"EverParsePulseEndianness.h"' \
	  -static-header 'Pulse.\*,EverParse3d.Prelude.StaticHeader,EverParse3d.ErrorCode' \
	  -warn-error '$$(WARN_$(1))' \
	  -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft -fno-shadow \
	  -fextern-c \
	  -finitialize-locals no \
	  -bundle 'Prims,FStar.\*,LowStar.\*[rename=SHOULDNOTBETHERE]' \
	  -bundle '$$(API_$(1))=Prims,LowParse.\*,EverParse3d.\*,Pulse.\*[rename=EverParse,rename-prefix]' \
	  $$(KRML_FILES)
	test '!' -e $(1)/EverParse.c
	test '!' -e $(1)/SHOULDNOTBETHERE.h
	test '!' -d $(1)/internal
endef

$(foreach b,$(BACKENDS),$(eval $(call header_rule,$(b))))

headers: $(foreach b,$(BACKENDS),$(b)/EverParse.h)

.PHONY: all headers clean-headers

clean-headers:
	rm -rf $(BACKENDS)

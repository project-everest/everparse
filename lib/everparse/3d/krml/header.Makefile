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
API_buffer := $(API_COMMON)+EverParse3d.CopyBuffer.Buffer+EverParse3d.Actions.ErrorHandler.Buffer
API_extern := $(API_COMMON)+EverParse3d.InputStream.Extern+EverParse3d.Actions.ErrorHandler.Extern
# static re-exports extern's instance and has no extracted declarations of its own
API_static := $(API_extern)

# With `extern` (and `static`) the stream primitives are assumed vals that the
# client implements in C, so KaRaMeL's "no corresponding implementation"
# warning (2) is expected.
WARN_buffer := -9@4-20-26
WARN_extern := -9@4-20-26-2
WARN_static := $(WARN_extern)

# The public EVERPARSE_ERROR_HANDLER typedef.
#
# The Low* backend gets this typedef from KaRaMeL for free: there,
# EverParse3d.Actions.Common.error_handler is a *monomorphic* F* type
# abbreviation, because the Low* prelude is built once per input stream
# backend with the stream type already fixed. 3d.exe passes
# `-no-inline-type-abbrev EverParse3d.Actions.Common.error_handler`, KaRaMeL
# keeps the abbreviation as a C typedef, and -fmicrosoft uppercases it.
#
# The Pulse prelude is built *once* and instantiated through a typeclass, so
# its error_handler is parameterized by the stream types. KaRaMeL has no
# parameterized typedefs: it can only inline such an abbreviation at each use
# site, which is why the generated prototypes spell the function-pointer type
# out in full, and why -no-inline-type-abbrev cannot be applied to
# EverParse3d.Actions.Common.error_handler itself -- it would leave an
# un-inlined TApp that the KaRaMeL checker rejects as "not a function type".
#
# So we recover a monomorphic abbreviation the same way the Low* backend has
# one, by instantiating it at the backend's stream types in a leaf module:
# EverParse3d.Actions.ErrorHandler.<Backend>.error_handler. That module is an
# API module of the bundle below, so `[rename=EverParse,rename-prefix]` names
# it EverParse_error_handler and -fmicrosoft uppercases it to
# EVERPARSE_ERROR_HANDLER, matching the Low* backend exactly.
#
# The typedef is therefore derived from the Pulse definition, not snapshotted:
# if the error_handler binder in EverParse3d.Actions.Common changes, this
# typedef changes with it.
HANDLER_buffer := EverParse3d.Actions.ErrorHandler.Buffer.error_handler
HANDLER_extern := EverParse3d.Actions.ErrorHandler.Extern.error_handler
HANDLER_static := $(HANDLER_extern)

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
	  -no-inline-type-abbrev '$$(HANDLER_$(1))' \
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
	grep -q 'EVERPARSE_ERROR_HANDLER)' $(1)/EverParse.h
endef

$(foreach b,$(BACKENDS),$(eval $(call header_rule,$(b))))

headers: $(foreach b,$(BACKENDS),$(b)/EverParse.h)

.PHONY: all headers clean-headers

clean-headers:
	rm -rf $(BACKENDS)

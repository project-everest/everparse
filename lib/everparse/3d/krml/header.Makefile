# Pre-generation of the Pulse runtime header, EverParse.h, one per input stream
# backend.
#
# `3d.exe --api pulse` used to rebuild this header on every invocation, bundling the
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
API_EXTERN := EverParse3d.InputStream.Extern+EverParse3d.InputStream.Extern.NullPtr+EverParse3d.Actions.ErrorHandler.Extern
API_buffer := $(API_COMMON)+EverParse3d.CopyBuffer.Buffer+EverParse3d.Actions.ErrorHandler.Buffer
API_extern := $(API_COMMON)+$(API_EXTERN)
# static re-exports extern's instance and has no extracted declarations of its own
API_static := $(API_extern)

# `--input_stream static` asks for the stream primitives to be declared
# `static inline` rather than `extern`, so that the compiler sees each stream
# operation at every validator call site instead of linking against it. That is
# the whole of the static/extern distinction at the C level, and KaRaMeL
# produces it from -static-header applied to the module holding the assumed
# primitives -- exactly as the Low* prelude does in
# src/3d/prelude/extern/Makefile (KRML_STATIC).
#
# The pattern names EverParse3d.InputStream.Extern *exactly*, with no trailing
# `\*`: EverParse3d.InputStream.Extern.NullPtr must stay out of it. -static-header
# applied to an assumed *value* rather than an assumed function emits a
# per-translation-unit tentative definition instead of a declaration. See that
# module.
STATIC_HEADER_COMMON := Pulse.\*,EverParse3d.Prelude.StaticHeader,EverParse3d.ErrorCode
STATIC_HEADER_buffer := $(STATIC_HEADER_COMMON)
STATIC_HEADER_extern := $(STATIC_HEADER_COMMON)
STATIC_HEADER_static := $(STATIC_HEADER_COMMON),EverParse3d.InputStream.Extern

# Warning 2 (no corresponding implementation) stays fatal for every backend.
# With `extern` (and `static`) the stream primitives are assumed vals that the
# client implements in C, but they are all reached through the -bundle below
# and KaRaMeL emits them as plain extern declarations, so none of them is
# reported as unbound.
WARN_buffer := -9@4-20-26
WARN_extern := $(WARN_buffer)
WARN_static := $(WARN_buffer)

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
# site, so -no-inline-type-abbrev cannot be applied to
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
# The same alias is what 3d.exe preserves in the client's own KaRaMeL run (see
# src/3d/ocaml/Batch.ml), so generated validator prototypes name the typedef
# too, exactly as under Low*.
#
# The typedef is therefore derived from the Pulse definition, not snapshotted:
# if EverParse3d.InputStream.Base.error_handler_arrow changes, this typedef
# changes with it.
HANDLER_buffer := EverParse3d.Actions.ErrorHandler.Buffer.error_handler
HANDLER_extern := EverParse3d.Actions.ErrorHandler.Extern.error_handler
HANDLER_static := $(HANDLER_extern)

# `Custard.\*` is Custard's bucket for monomorphized instances of polymorphic
# definitions. It is named on the right of the `=` only, so those instances are
# private to the bundle: the reachable ones are inlined into EverParse.h, the
# rest are dropped. It is deliberately absent from pulse_everparse_only_bundle
# in src/3d/ocaml/Batch.ml, because that pattern list is also the client's
# `-library` and the client's own Custard run produces its own `Custard.\*`
# modules, which must be emitted rather than assumed. The two still agree in
# the sense that matters: no Custard.\* declaration survives into EverParse.h.
define header_rule
$(1)/EverParse.h: $$(KRML_FILES) header.Makefile
	mkdir -p $(1)
	$$(KRML_EXE) \
	  -skip-compilation \
	  -skip-makefiles \
	  -tmpdir $(1) \
	  -minimal \
	  -header $$(DDD_HOME)/noheader.txt \
	  -add-include 'EverParse:"EverParsePulseEndianness.h"' \
	  -static-header '$$(STATIC_HEADER_$(1))' \
	  -no-inline-type-abbrev '$$(HANDLER_$(1))' \
	  -warn-error '$$(WARN_$(1))' \
	  -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft -fno-shadow \
	  -fextern-c \
	  -finitialize-locals no \
	  -bundle 'Prims,FStar.\*,LowStar.\*[rename=SHOULDNOTBETHERE]' \
	  -bundle '$$(API_$(1))=Prims,LowParse.\*,EverParse3d.\*,Pulse.\*,Custard.\*[rename=EverParse,rename-prefix]' \
	  $$(KRML_FILES)
	test '!' -e $(1)/EverParse.c
	test '!' -e $(1)/SHOULDNOTBETHERE.h
	test '!' -d $(1)/internal
	grep -q 'EVERPARSE_ERROR_HANDLER)' $(1)/EverParse.h
endef

$(foreach b,$(BACKENDS),$(eval $(call header_rule,$(b))))

LOWSTAR_COMMON := EverParse3d.Actions.Common+EverParse3d.Prelude.StaticHeader+EverParse3d.ErrorCode+EverParse3d.Lowstar.Public
LOWSTAR_buffer := $(LOWSTAR_COMMON)+EverParse3d.Lowstar.SupportBuffer+EverParse3d.InputStream.LowstarBuffer+EverParse3d.CopyBuffer.LowstarBuffer+EverParse3d.Actions.ErrorHandler.LowstarBuffer
LOWSTAR_extern := $(LOWSTAR_COMMON)+EverParse3d.Lowstar.SupportExtern+EverParse3d.InputStream.LowstarExtern+EverParse3d.InputStream.LowstarExtern.Types+EverParse3d.InputStream.LowstarExtern.Raw+EverParse3d.CopyBuffer.LowstarExtern+EverParse3d.Actions.ErrorHandler.LowstarExtern
LOWSTAR_static := $(LOWSTAR_extern)
LOWSTAR_HANDLER_buffer := EverParse3d.Actions.ErrorHandler.LowstarBuffer.error_handler
LOWSTAR_HANDLER_extern := EverParse3d.Actions.ErrorHandler.LowstarExtern.error_handler
LOWSTAR_HANDLER_static := $(LOWSTAR_HANDLER_extern)
LOWSTAR_STATIC := EverParse3d.Prelude.StaticHeader,EverParse3d.ErrorCode,EverParse3d.Lowstar.Public,EverParse3d.Lowstar.SupportBuffer,EverParse3d.Lowstar.SupportExtern,EverParse3d.InputStream.LowstarExtern.Types
LOWSTAR_STATIC_static := ,EverParse3d.InputStream.LowstarExtern.Raw

# The final, already-consumed bundle only overrides ErrorCode's C prefix.
# Its declarations live in EverParse.h, not in a second support header.
define lowstar_header_rule
lowstar/$(1)/EverParse.h: $$(KRML_FILES) header.Makefile
	mkdir -p lowstar/$(1)
	$$(KRML_EXE) -skip-compilation -skip-makefiles -tmpdir lowstar/$(1) \
	  -minimal -header $$(DDD_HOME)/noheader.txt \
	  -add-include 'EverParse:"EverParseEndianness.h"' \
	  -static-header '$$(LOWSTAR_STATIC)$$(LOWSTAR_STATIC_$(1))' \
	  -no-inline-type-abbrev '$$(LOWSTAR_HANDLER_$(1)),EverParse3d.Lowstar.SupportBuffer.input_buffer' \
	  -warn-error '$$(WARN_$(1))' \
	  -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft -fno-shadow -fextern-c \
	  -finitialize-locals no \
	  -bundle 'Prims,FStar.\*,LowStar.\*[rename=SHOULDNOTBETHERE]' \
	  -bundle '$$(LOWSTAR_$(1))=Prims,LowParse.\*,EverParse3d.\*,Pulse.\*,Custard.\*[rename=EverParse,rename-prefix]' \
	  -bundle 'EverParse3d.ErrorCode[rename=EverParsePulseInternal,rename-prefix]' \
	  $$(KRML_FILES)
	test '!' -e lowstar/$(1)/EverParse.c
	test '!' -e lowstar/$(1)/EverParsePulseInternal.h
	test '!' -e lowstar/$(1)/SHOULDNOTBETHERE.h
	test '!' -d lowstar/$(1)/internal
	test "$$$$(ls lowstar/$(1))" = EverParse.h
endef

$(foreach b,$(BACKENDS),$(eval $(call lowstar_header_rule,$(b))))

headers: $(foreach b,$(BACKENDS),$(b)/EverParse.h lowstar/$(b)/EverParse.h)
	rm -f lowstar/EverParsePulseInternal.h

.PHONY: all headers clean-headers

clean-headers:
	rm -rf $(BACKENDS) lowstar

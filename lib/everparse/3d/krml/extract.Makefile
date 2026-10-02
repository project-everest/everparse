all: extract

EVERPARSE_SRC_PATH := $(realpath ../../../../src)
include $(EVERPARSE_SRC_PATH)/windows.Makefile

SRC_DIRS += $(realpath ..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

FSTAR_OPTIONS += --warn_error -342

# Whole-program extraction of the Pulse 3d runtime, to the .krml that
# header.Makefile turns into EverParse.h and that `3d.exe --pulse` passes to
# KaRaMeL alongside the generated modules (see all_everparse_krmls in
# src/3d/ocaml/Batch.ml, which simply globs this directory).
#
# Custard eliminates dead code by reachability from the roots, and a karamel
# -bundle or -library clause is packaging rather than reachability: Custard has
# no notion of either. The client's own KaRaMeL run passes
# `-library Prims,LowParse.\*,EverParse3d.\*,Pulse.\*`, which turns this runtime
# into `extern` declarations that KaRaMeL still has to have *seen* in order to
# type the generated validators' calls into it. So the whole runtime is rooted,
# not just the API modules that land in EverParse.h.
CUSTARD_BACKEND := KrmlC

# EverParse3d.Interpreter is specialized away in generated code (the `specialize`
# tactic), exactly as in the Low* prelude, so it is never extracted itself, and
# EverParse3d.Smoke is a verification-only smoke test. Neither is rooted; nothing
# else reaches them, so neither is emitted.
#
# The four Pulse.* modules were named explicitly in the old --extract list and
# must stay rooted: header.Makefile applies -static-header to Pulse.\*, so their
# definitions become `static inline` in EverParse.h, and 3d.exe then passes
# -library Pulse.\* for the client's own KaRaMeL run, which assumes the header
# supplies them. Dropping one as unreachable here (Pulse.Lib.Pervasives's
# _zero_for_deref, say, which no runtime definition mentions but generated
# validators do) leaves the client with an undefined reference.
CUSTARD_ENTRY_MODULES := \
  EverParse3d.Actions.Base \
  EverParse3d.Actions.Common \
  EverParse3d.Actions.ErrorHandler.Buffer \
  EverParse3d.Actions.ErrorHandler.Extern \
  EverParse3d.AppCtxt \
  EverParse3d.CopyBuffer \
  EverParse3d.CopyBuffer.Buffer \
  EverParse3d.ErrorCode \
  EverParse3d.InputStream.Base \
  EverParse3d.InputStream.Buffer \
  EverParse3d.InputStream.Buffer.Types \
  EverParse3d.InputStream.Extern \
  EverParse3d.InputStream.Extern.NullPtr \
  EverParse3d.InputStream.Extern.Types \
  EverParse3d.InputStream.Static \
  EverParse3d.Kinds \
  EverParse3d.Prelude \
  EverParse3d.Prelude.StaticHeader \
  EverParse3d.ProbeActions \
  EverParse3d.State

# header.Makefile applies -static-header to Pulse.\*, so what the Pulse runtime
# contributes to EverParse.h is emitted there as `static inline`, and 3d.exe
# then passes -library Pulse.\* for the client's own KaRaMeL run, which assumes
# the header supplies it. Everything the generated validators use from Pulse is
# inline_for_extraction and so already inlined by F* -- except _zero_for_deref,
# the constant behind Pulse's `b[_zero_for_deref]` dereference idiom, which no
# runtime definition mentions and which reachability would therefore drop,
# leaving the client with an undefined reference. Root it by name rather than
# rooting its module: Pulse.Lib.Pervasives re-exports the tactic builtins, and
# rooting those drags FStarC.Tactics.\* into the output.
CUSTARD_ENTRIES := Pulse.Lib.Pervasives._zero_for_deref

# The `--use_error_handler_macro` hook: one [@@CMacro] assume val per backend,
# named by the 3D frontend and by nothing in the runtime, so reachability drops
# it. KaRaMeL needs the declaration in order to know it is a macro; without it
# the client's run invents an ordinary extern and warning 2 is fatal.
CUSTARD_ENTRIES += EverParse3d.InputStream.Buffer.error_handler_macro
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.error_handler_macro
CUSTARD_ENTRIES += EverParse3d.InputStream.Static.error_handler_macro

# The C primitives the client implements by hand (EverParseStreamOf,
# EverParseStreamHasAt, ...). Every one of them is an `assume val`, and
# Custard roots only the *definitions* of an entry module, so none of them is
# reachable: the runtime reaches them exclusively through
# inline_for_extraction wrappers, which F* has already inlined into the
# generated validators by the time this extraction runs.
#
# Dropping them is not a link error but something subtler. KaRaMeL needs the
# declaration to know the function's extracted arity, which is shorter than
# its F* arity because the Ghost.erased position/contents/permission
# arguments are erased. Without it, the client's call sites keep those
# arguments, and the generated code passes six arguments to the client's
# four-argument prototype (plus an "implicit declaration" warning).
#
# Ghost `assume val`s are deliberately absent: stream_pts_to_raw and friends,
# the two assumed lemmas, and stream_split/stream_join, which only rearrange
# the ghost view of the stream. They have no C counterpart, and naming one
# here is an error (Custard error 385).
CUSTARD_ENTRIES += EverParse3d.CopyBuffer.Buffer.stream_of
CUSTARD_ENTRIES += EverParse3d.CopyBuffer.Buffer.stream_len
CUSTARD_ENTRIES += EverParse3d.CopyBuffer.Buffer.stream_pos
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.NullPtr.null_ptr
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.stream_get_position
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.stream_has
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.stream_has_at
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.stream_read_bytes
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.stream_skip
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.stream_empty
CUSTARD_ENTRIES += EverParse3d.InputStream.Extern.field_ptr_after_impl

# Abstract types the client realizes in C, so Custard must declare rather than
# define them: EVERPARSE_COPY_BUFFER_T is `void*` from EverParseEndianness.h
# (reached through the EverParse bundle's -add-include of
# EverParsePulseEndianness.h), and EVERPARSE_INPUT_STREAM_BASE and
# EVERPARSE_EXTRA_T come from the client's own EverParseStream.h. Letting
# Custard emit `typedef struct EVERPARSE_INPUT_STREAM_BASE_s ...` instead
# conflicts with the client's pointer typedef.
CUSTARD_EXTERN_TYPES := EverParse3d.CopyBuffer.Buffer.copy_buffer_t
CUSTARD_EXTERN_TYPES += EverParse3d.InputStream.Extern.Types.input_stream_base
CUSTARD_EXTERN_TYPES += EverParse3d.InputStream.Extern.Types.extra_t

CUSTARD_ROOTS := EverParse3d.Krml.Roots.fst

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY := extracted
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

clean_rules += clean-extracted

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

extract-krml: $(CUSTARD_KRML)

.PHONY: extract-krml

# common.Makefile's clean-krml only removes $(OUTPUT_DIRECTORY)/*.krml, which
# leaves the directory and the .depend it holds behind. Drop the lot.
clean-extracted:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-extracted

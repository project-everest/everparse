# Extracting COSE with Custard

[Custard](https://github.com/FStarLang/FStar/pull/4395) is F\*'s work-in-progress
replacement for the `--codegen krml` extraction pipeline.  This directory wires
it up for the COSE formatter, on both targets:

| leg | pipeline |
| --- | --- |
| Rust | Custard `--custard_backend KrmlRust` → karamel `-backend rust` |
| C    | Custard `--custard_backend C` (direct-to-C; karamel is not used) |

Both legs consume the **same** `.checked` files as the karamel-native build, so
`make verify` is shared and nothing is verified twice.

## Requirements

An F\* built from the `gebner_custard` branch, at **`4904bf105f`** or later.
Earlier revisions hit blockers that are fixed there; in particular anything
before `4af84d2f86` extracts COSE roughly **50× slower** (C: 1994 s → 37 s).
Point `FSTAR_EXE` at that build as usual.

## Building

```sh
# Rust (produces src/cose/rust/src/*.rs)
make -C src/cose/generate-rust snapshot          # ~27 s

# C (produces src/cose/c/COSE_Format.{c,h})
make -C src/cose/verifiedinterop snapshot        # ~37 s

# karamel-native instead, on either leg
make -C src/cose/generate-rust   snapshot CUSTARD=0
make -C src/cose/verifiedinterop snapshot CUSTARD=0
```

`CUSTARD=0` regenerates the *generated* files only.  The hand-written consumers
(`c/COSE_OpenSSL.c`, `interop/*.c`, `verifiedinterop/test/*.c`) are written
against Custard's output and would have to be reverted alongside it.

The shared settings live in [`custard.Makefile`](custard.Makefile); the targets
themselves are in `generate-rust/extract.Makefile` and
`verifiedinterop/Makefile`.

## Status

**Rust: switched over.**  `src/cose/rust/src/*.rs` is Custard output.  The
crate, its binary and `cargo test --release` (2 passed, 1 ignored) all behave
exactly as on the karamel-native snapshot, and the public API matches it
function-for-function (99/99, 35/35, 9/9 `pub fn` per module).

**C: available, not switched over.**  `extract-custard` produces C at full API
parity with `../c` (82/82, 41/41, 41/41, 9/9 declarations, each measured by
function prefix and checked with a deletion control).  It is *not* the default,
because it is not a drop-in replacement for the snapshot in `../c` — see below.

## Why the C leg is not the default

Custard's C output is correct and complete, but its *shape* differs from
karamel's in two ways that the hand-written consumers in `../c` and `../interop`
depend on:

1. **One translation unit.**  karamel splits the program over
   `COSE_Format.{c,h}`, `COSE_EverCrypt.{c,h}`, `CBORDetAPI.h` and
   `internal/COSE_Format.h`; Custard emits a single `.c`/`.h` pair.  That pair
   also *defines* the 40 `cbor_det_*` functions that the karamel-native build
   links in separately from `cbor/pulse/det/c/CBORDet.c`, so `CBOR_Det.o` has to
   be dropped from `interop/Makefile` to avoid duplicate symbols.

2. **Generated type names.**  `../c/COSE_OpenSSL.h` and `../interop/common.c`
   spell out generated names — `Pulse_Lib_Slice_slice__uint8_t`,
   `COSE_Format_Inl`, `COSE_Format_Mkevercddl_int0`, and option
   monomorphizations — which Custard names differently (see "Naming" below).

(1) and the first name are mechanical.  (2) is not: `common.c` pattern-matches
several layers deep into generated structs, so switching the C snapshot means
rewriting hand-written interop C, which is out of scope here.  Both are naming,
not semantics.

## Naming divergences

Three differences from karamel-native output are **working as designed**, per
the Custard author:

* Option/either monomorphizations can land in a different bundle than they do
  under karamel.  Custard places an instance where it first demands it, which is
  a whole-program property and not something to pin.  In Rust this moved
  `option__Pulse_Lib_Slice_slice·uint8_t` from `commonpulse` to `coseformat`.
* CDDL abbreviations are unfolded in generated type names, so
  `option__COSE_Format_bstr` becomes `option__Pulse_Lib_Slice_slice·uint8_t`.
  Monomorphization runs on unfolded types.
* The 69 `uu___is_*` discriminators that karamel emits and Custard does not are
  dead code: Custard extracts a whole program from its entry points and nothing
  calls them.

Together these cost 4 lines in the Rust consumers (3 in `rust/src/main.rs`,
1 import plus 2 paths in `rust/tests/interop.rs`), all already applied.  The C
consumers absorb the same difference in the naming changes described above.

## Entry modules

Custard extracts a whole program starting from entry modules, so **every module
named in a karamel `-bundle` `+` list must be its own `--custard_entry_module`** —
otherwise it is simply not extracted.  This is easy to get wrong quietly: a
`-bundle 'M=[...]'` naming an absent module is fatal to karamel, so an omission
shows up as a bundle error rather than as missing code.  The two lists are
`CUSTARD_C_ENTRY_MODULES` (6) and `CUSTARD_RUST_ENTRY_MODULES` (8) in
`custard.Makefile`.

## Gotcha: karamel exits 0 on printing failures

On the Rust leg karamel can fail to print a function and still exit 0, leaving a
`.rs` that is missing definitions.  `extract-custard` therefore greps its log for
`ERROR printing` and fails explicitly.  Do not remove that check.

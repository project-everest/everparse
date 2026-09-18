# Extracting EverParse with Custard

[Custard](https://github.com/FStarLang/FStar/pull/4395) is F\*'s work-in-progress
replacement for the `--codegen krml` extraction pipeline.  `src/cose` and
`src/cbor` are both extracted with it, on both targets:

| leg | pipeline |
| --- | --- |
| Rust | Custard `--custard_backend KrmlRust` → karamel `-backend rust` |
| C    | Custard `--custard_backend C` (direct-to-C; karamel is not used) |

Both legs consume the **same** `.checked` files as the karamel-native build, so
`make verify` is shared and nothing is verified twice.

## What is and is not migrated

`src/cose`, `src/cbor` (all four legs: det and nondet, C and Rust) and
`src/cddl/tests` use Custard.  That is every Pulse-based part of EverParse.

`src/3d`, `src/ASN1` and `LowParse.Low.*` **cannot** be migrated: they are
written against Low\*/`HyperStack`, which Custard does not support at all, and
so they stay on `--codegen krml` + karamel indefinitely.  Only the Pulse-based
parts of EverParse are candidates.

## Shape of the C output

Custard emits **one translation unit** per leg, where karamel split its output
across a public header, a type header and an `internal/` header.  So
`src/cbor/pulse/det/c` no longer has a real `CBORDetType.h` or
`internal/CBORDet.h`; `CBORDetType.h` is a one-line shim that includes
`CBORDet.h`, kept so the karamel-driven `cddl` tests and `cbor` vertests, which
pass `-add-include '"CBORDetType.h"'`, keep building until `cddl` migrates.
`krmllib.h` is kept for the same reason.  The public function names are
unchanged, which is why every C consumer builds without modification.

## Requirements

An F\* master at **`d57a6d9ae3`** or later -- the merge of
FStarLang/FStar#4395, which brought Custard into `master`.  (Before that merge
this needed the `gebner_custard` branch at `09acba059a` or later; earlier
revisions hit blockers, and anything before `4af84d2f86` extracts COSE roughly
**50× slower** -- C: 1994 s → 37 s.)  Point `FSTAR_EXE` at that build as usual.

`opt/hashes.Makefile` pins `FStar_hash` to that merge, so CI builds and tests
with a Custard-enabled compiler.  Custard is still not in any *released* F\*,
though, so the choice of backend remains made from the compiler at hand rather
than hardcoded: `custard-detect.Makefile` asks
`$(FSTAR_EXE) --help` whether it knows `--custard_backend` and sets `CUSTARD`
to 1 or 0 accordingly.  With a released F\* the COSE `.fst` sources still
verify and still extract through `--codegen krml` + karamel; what a released
F\* cannot do is *refresh the snapshots*, and `snapshot` refuses rather than
overwriting Custard output with karamel's.  Nothing in `src/cose` depends on a
Custard-only F\* attribute or option at typechecking time.

## Building

```sh
# Rust (produces src/cose/rust/src/*.rs)
make -C src/cose/generate-rust snapshot          # ~27 s

# C (produces src/cose/c/COSE_Format.{c,h})
make -C src/cose/verifiedinterop snapshot        # ~37 s

# karamel-native extraction instead, on either leg
make -C src/cose/generate-rust   extract-all CUSTARD=0
make -C src/cose/verifiedinterop extract     CUSTARD=0
```

`CUSTARD=0` runs the karamel-native extraction but does not update the
snapshots: `snapshot` under `CUSTARD=0` fails on purpose.  The snapshots and
the hand-written consumers (`c/COSE_OpenSSL.c`, `interop/*.c`,
`verifiedinterop/test/*.c`) are written against Custard's output, and a
karamel snapshot dropped on top of them would leave the tree inconsistent.
Reverting the leg means reverting all of it together.

The shared settings live in [`custard.Makefile`](custard.Makefile); the targets
themselves are in `generate-rust/extract.Makefile` and
`verifiedinterop/Makefile`.

## Status

Both legs are switched over; Custard output is what is committed.

**Rust.**  `rust/src/*.rs` is Custard output.  The crate, its binary and
`cargo test --release` (2 passed, 1 ignored) behave exactly as on the
karamel-native snapshot, and the public API matches it function-for-function
(99/99, 35/35, 9/9 `pub fn` per module).

**C.**  `c/COSE_Format.{c,h}` is Custard output, at full declaration parity with
the karamel-native snapshot it replaced (82/82, 41/41, 41/41, 9/9, each measured
by function prefix and checked with a deletion control).  Both C consumer suites
round-trip against pycose: `interop`, which is OpenSSL-backed, and
`verifiedinterop/test`, which links HACL*'s `libevercrypt.a`.  `interop`'s
benchmark is unchanged or slightly better than the karamel-native build --
notably `parse` 2.96 vs 4.02 us/iter.

## What switching the C leg required

Custard's C output is correct and complete, but its *shape* differs from
karamel's, and the hand-written consumers had to follow.

1. **One translation unit.**  karamel splits the program over
   `COSE_Format.{c,h}`, `COSE_EverCrypt.{c,h}`, `CBORDetAPI.h` and
   `internal/COSE_Format.h`; Custard emits a single `.c`/`.h` pair.
   `--custard_split` does *not* apply to the C backend -- it still writes one
   unit -- so this is inherent.  Consequences:

   * That unit also *defines* the 40 `cbor_det_*` functions the karamel build
     links separately from `cbor/pulse/det/c/CBORDet.c`, so `CBOR_Det.o` is no
     longer linked; it would be a duplicate definition.
   * It also contains the EverCrypt-backed entry points, so `COSE_Format.o`
     references `EverCrypt_Ed25519_{sign,verify}` even in `interop`, which does
     not use them.  `interop` compiles with `-ffunction-sections
     -fdata-sections` and links with `-Wl,--gc-sections`, which drops that code
     rather than take on a HACL* dependency.  `verifiedinterop/test`, which does
     use EverCrypt, links `libevercrypt.a` as before.
   * `COSE_EverCrypt.h` no longer exists; its nine declarations are in
     `COSE_Format.h`.

2. **Generated names and tagged-union layout.**  karamel emits
   `typedef enum { COSE_Format_Mkevercddl_int0, ... }` with payloads in
   `.case_Mkevercddl_int0`; Custard emits `COSE_FORMAT_MKEVERCDDL_INT0` with
   payloads in `.val.Mkevercddl_int0`.  Tuple fields are `._1`
   and `._2` rather than `.fst` and `.snd`; monomorphized names are abbreviated
   (`option___COSE_Format_cose_key_okp___Pulse_Lib_Slice_slice__uint8_t_` becomes
   `option__tuple2_cose_key_okp_slice_uint8`); and a constructor whose payloads
   are all unit collapses to a bare enum rather than a tagged struct.

3. **`Abort.abort` is emitted unprefixed.**  It is an `assume val` realized by
   libc's `abort`, and the karamel-native build gave it that unqualified name
   via `-no-prefix Abort`.  Custard does the same, via `Abort` in
   `CUSTARD_C_NO_PREFIX`, so `COSE_Format.c` declares `extern void abort(void);`
   and calls it, and consumers need to do nothing.

   This needed a fix on the Custard side: `--custard_c_no_prefix` originally
   covered definitions but not `assume val`s, so listing `Abort` did nothing
   and Custard emitted `Abort_abort`, which each consumer had to define itself.
   The only other mechanism, `[@@custard_extern "abort"]` on the declaration,
   does not exist in a released F\*, so using it stops `Abort.fst`
   typechecking there -- which broke EverParse's CI until it was
   backed out.  FStarLang/FStar#4395 section 102 extended the option to
   `assume val`s, which is why the shim is gone; this is the one item that
   requires `a1d6ba3f5a` rather than merely `12104fcba4`.

4. **Two modellings changed.**  `sig_structure.context` is
   `FStar_Pervasives_either__unit_unit` where karamel had a plain enum tag, and
   `cose_sign1.protected` is no longer renamed to `protected0`.

None of this is a semantic difference; the round-trip tests against pycose are
what establish that.

## Naming divergences

Three differences from karamel-native output are working as designed, per the
Custard author:

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

Together these cost 4 lines in the Rust consumers (3 in `rust/src/main.rs`, 1
import plus 2 paths in `rust/tests/interop.rs`).  The C consumers absorb the
same difference in the naming changes described above.

### Caveat: generated specialization names are not stable

Custard warns, during extraction, that the name of a monomorphized
specialization carries "a hint built from the monomorphizer's input and may
change when that input does", and advises that a consumer needing to spell one
should typedef it once in its own header rather than depend on the name
throughout.  The consumers here do spell them, so expect churn there when the
specification changes.

### Two option types for what looks like one type

The C output has both `FStar_Pervasives_Native_option__bstr` and
`FStar_Pervasives_Native_option__slice_uint8`.  They are structurally identical
-- each wraps a `Pulse_Lib_Slice_slice__uint8` -- but are distinct C types, so a
consumer must spell whichever one appears in the signature it is calling.

This is faithful rather than a defect: `COSE.Format.bstr` and
`Pulse.Lib.Slice.slice UInt8.t` really are different F* types.  `bstr` is a
nominal type spliced by `FStar.Tactics.PrettifyType`; it does not unfold under
`delta`, or even under `delta_only` naming it, and a `slice UInt8.t` is rejected
where a `bstr` is expected.  What makes the two indistinguishable in C is that
Custard then collapses each single-field wrapper to its payload, so the
*identity* of the monomorphization is fixed before the collapse and its
*representation* after it.

The two backends differ here.  The Rust leg has a single
`option__Pulse_Lib_Slice_slice·uint8_t`, used both for `cose_key_okp.intkeyneg2`
(an `option bstr`) and as `verify1_simple`'s return type (an
`option (slice uint8)`).  That is because the C leg monomorphizes inside Custard
(`--custard_monomorphize_types true`) over F* types, whereas the Rust leg leaves
monomorphization to karamel, by which point Custard has already collapsed `bstr`
away.

## `src/cddl/tests`

The five test corpora are wired the same way, through the shared fragment
[`cddl/tests/custard.Makefile`](cddl/tests/custard.Makefile).  Unlike `cose`
and `cbor`, **nothing here is snapshotted**: these are tests, and the C or Rust
is regenerated from the `.cddl` sources on every run, so the only job is to
produce a translation unit the existing consumers can be built against.

| corpus | leg | how |
| --- | --- | --- |
| `demo` | C | one unit, `client.c` links against it |
| `unit` | C | one unit per `.cddl`, nine hand-written C/C++ drivers |
| `rust` | Rust | `--custard_backend KrmlRust`, then karamel unchanged |
| `dpe` | C | one unit, compile-only (never linked or run) |
| `roundtrip` | — | **not a Custard target**: it extracts to OCaml through F\*'s own backend.  It includes `karamel.Makefile` only for krmllib include paths, and runs no karamel extraction. |

Each corpus builds either way: `make` picks the backend through
`custard-detect.Makefile`, and `CUSTARD=0` forces the karamel-native path.
Both are checked in CI.

### The CBOR det API has to be published by the unit itself

The karamel-native build gets `cbor_det_t` and `cbor_raw` from the `cbor`
snapshot's `CBORDetType.h`, which is on its include path, and emits neither
itself.  Custard folds the det API into the single unit it emits, so that unit
has to publish those names -- and publishes them *unprefixed* only if the
declaring module is named in `--custard_c_no_prefix`.  Hence
`CBOR.Pulse.Raw.Type` in `CUSTARD_C_NO_PREFIX`, which karamel did not need.

`CBORDetAPI.h` and `CBORDetType.h` are then generated shims so that consumers
that spell them keep building.  There are two variants, and the choice matters:

* `custard-cbor-shim` writes a one-line `#include` of the unit's header.  Use
  it where the directory holds a *single* unit (`demo`, `dpe`).
* `custard-cbor-shim-empty` writes a comment and nothing else.  Use it where a
  directory holds *several* units side by side (`unit`).  Redirecting to any
  one of them would drag a second copy of the det API into every other unit's
  consumer, because each unit publishes the whole API.  It is safe for the
  shim to be empty there because every consumer in that directory includes its
  own unit's header, which already carries the API, before it includes
  `CBORDetAPI.h`.

### Consumers need `#ifdef EVERPARSE_CUSTARD`

The C drivers are shared between the two backends, so the places where the two
C surfaces differ are collected into a macro block at the top of each file and
the body is left identical.  The Custard rules pass `-DEVERPARSE_CUSTARD`.
The differences are the naming ones described under *Naming divergences*
below, plus the shape of a tagged union:

```c
/* karamel: a one-payload-constructor union is flattened, and a multi-arm
   union is anonymous with short `case_<Ctor>' members. */
o.v                 e.case_Inl
/* Custard: every arm nests under `val', named after the bare constructor.
   A constructor with exactly one field *is* the member; two or more fields
   keep a wrapper struct (`t.val.A.x'). */
o.val.Some          e.val.Inl
```

Neither is wrong, and only the enclosing union member remains to be
`#ifdef`-ed.  Custard originally spelled the member with the full, explicitly
unstable specialization suffix and wrapped every payload in a struct; that was
reported upstream as
[§113](https://github.com/FStarLang/FStar/pull/4395#issuecomment-5667930537)
and
[§114](https://github.com/FStarLang/FStar/pull/4395#issuecomment-5667985942)
-- the argument being that a member name, unlike a type name, cannot be
abstracted behind a `typedef`, so an unstable member name is load-bearing for
consumers.  Both were fixed in `09acba059a`.

### Gotcha: expansion order

`CUSTARD_C_ENTRY_MODULES` must be assigned with deferred `=`, not `:=`, when
it names `$(CUSTARD_CBOR_DET_ENTRY_MODULES)` before the shared fragment is
included -- and a rule whose prerequisites test `$(CUSTARD)` must be written
*after* `custard-detect.Makefile` is included, because prerequisites are
expanded where the rule is written.  Both mistakes fail quietly, producing a
karamel build when a Custard one was asked for, or a unit with no CBOR API at
all.  The tell for the second is `Warning 375: --custard_c_no_prefix X renamed
nothing`, which means the entry module never took effect.

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

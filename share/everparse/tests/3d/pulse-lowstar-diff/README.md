# Low\*-compatible vs. native Pulse API differential test

This suite compares `3d --api lowstar` with `3d --api pulse`: the
Low\*-compatible and native Pulse public APIs of `lib/everparse/3d/`.
The original Low\* implementation is compared separately in
`src/3d/tests/pulse-lowstar-diff-tests`, using the same shared Low\*-API corpus.

This directory asserts that, empirically, on the 3D test grammars.

## What is compared

One driver is generated from the emitted `*Wrapper.h` files and compiled twice,
once against each backend's C output. For every test case both executables must
agree on:

- the accept/reject verdict returned by `<Mod>Check<T>`,
- every value written to an out-parameter,
- the full contents of every copy buffer left by probe actions, and
- every error delivered to the client's `<Mod>EverParseError` callback --
  count, field name and reason.

The check is made in two stages so that a regression in error *attribution*
alone is not misreported as a parser-semantics regression.

## Where the inputs come from

`harness.c` runs a feedback-guided fuzzer whose progress signal is the outcome
signature itself: when a mutation drives the parser one field deeper, the
reported field name changes, so the input is retained in the corpus. Each
backend is fuzzed separately -- they explore slightly differently -- and the
union of the two corpora is then replayed through *both*.

The RNG is a fixed-seed xorshift, so a given `ITERS` always yields the same
corpus. The test is fully reproducible and has no golden files.

## Running it

    make -j16 -C share/everparse/tests/3d/pulse-lowstar-diff

That runs two things: the top-level batch comparison, and the sub-directory
tests (`make -C share/everparse/tests/3d/pulse-lowstar-diff pulse-diff-subdirs`
on its own), plus the compile-only callback ABI check.

Knobs:

| Variable | Default | Meaning |
| --- | --- | --- |
| `ITERS` | `20000` | fuzzer iterations per entrypoint, per backend |
| `LO_DIR` | `share/everparse/tests/3d/lowstar/out.batch-interpret` | `--api lowstar` generated C |
| `PU_DIR` | `share/everparse/tests/3d/out.batch-interpret.pulse` | `--api pulse` generated C |
| `SUBDIR_TESTS` | see Makefile | which sub-directory tests to compare |
| `DIFF_PREBUILT` | `0` | set to `1` only when both ordinary corpora have already been built |

The two input directories are produced by the ordinary `batch-interpret-test`
and `pulse-batch-interpret-test` targets. By default, this Makefile invokes
the root `3d-unit-test` and `3d-pulse-test` targets first, building both complete
corpora, including subdirectory outputs. The first target explicitly selects
`--api lowstar`; the second explicitly selects `--api pulse`.
No generated test code from `legacy_lowstar` is required.

The enclosing `make 3d-test` already builds both corpora and passes
`DIFF_PREBUILT=1` to avoid duplicate builds. Even in prebuilt mode, every compared
directory is checked for the expected validator result type and Low\*-adapter
worker references. Missing, mixed, or original-Low\* outputs fail rather
than silently comparing the wrong implementations. Clean and rebuild a corpus
if it contains stale output from another API.

The top-level driver, binaries, and fuzz corpora are regenerated on each run
so changed input directories or `ITERS` cannot reuse an old passing trace.
`make selftest` exercises the build wiring and wrong/missing-API rejection
without running the verifier.

We read those rather than the `batch-test`/`pulse-batch` outputs because the
latter are built from `positive_tests`, which excludes `ActAndCheck.3d` and
`FieldDependence0.3d`. Both targets drive an identical pipeline today and
differ only in their file list, so taking the wider one costs nothing and buys
coverage of the only test that exercises `:act`/`:check`.

`pulse-diff` is **not** part of the shared Low\*-API corpus's `all` target:
it also needs the native Pulse outputs. The root `make 3d-test` builds both
trees before running this suite on Pulse-enabled Linux builds.

## When there is no Low\* backend

On the `fstar2` branch there is only one backend left. F\*'s ulib no longer
ships `FStar.HyperStack`, so neither `LowParse.Low.*` nor `src/3d/prelude`
can be verified; the top-level Makefile has dropped its `3d-prelude` target;
and `Options.get_pulse` is hardwired to `true`, so `3d.exe` emits Pulse
whether or not `--pulse` is passed. A "differential" run would compare the
Pulse backend against itself, and would not even get that far: the generated
C includes `EverParse.h`, and the Low\* one is precisely what
`src/3d/prelude/buffer` no longer produces.

The Makefile therefore keys off `src/3d/prelude/buffer/EverParse.h`. When that
header is missing the whole test skips itself with a message -- the same way
`run_subdir.sh` skips a sub-directory that only one of the two trees has --
instead of regenerating `out.batch` for twenty minutes and then failing to
compile it. Restoring the Low\* prelude build restores the test.

## The sub-directory tests

The top-level batch covers the 25 `.3d` files in `share/everparse/tests/3d/lowstar` itself. The
sub-directories exercise things it does not: multi-module compilation, output
types, external typedefs and iterators, conditional compilation,
specialization, probes, and the error-handler macro. `share/everparse/tests/3d`
mirrors the whole tree, so each has a Pulse counterpart built from the same
grammar, and `run_subdir.sh` compares one such pair.

It works out which sources to link rather than being told: everything the
backend generated, minus any file carrying its own `main` (Z3TestGen's
`testcases.c`) plus whatever the test supplies by hand (external-typedef
implementations, for instance) minus its own `main` and error callbacks, which
the generated driver provides instead.

    ./run_subdir.sh ifdefs/obj 20000

One relative path normally names the directory in both trees. The `=` form
handles the single layout that differs -- the Low\* side emits every
`output_types` test into one `interpret.out` while the Pulse side gives each
its own directory:

    ./run_subdir.sh output_types/interpret.out=output_types/TPoint.out

Entrypoints are read from the Pulse side, so pairing a narrow Pulse directory
against a wider Low\* one compares exactly that subset. A missing directory
is a failure, not a skip. For a deliberate subset, set `SUBDIR_TESTS`;
the default retains all 21 output-directory pairs.

### What is left out, and why

| Test | Reason |
| --- | --- |
| `extern`, `static`, `funptr` | the wrapper takes an opaque `EVERPARSE_INPUT_STREAM_BASE` rather than a byte array, so only the client can construct an input. `gen_diff.py` recognises and skips such signatures. |
| `exttype`, `goto_return` | generation-only tests: they compare emitted sources against a snapshot and never build a validator. |
| `output_types/ExternVector.out` | needs `Push()`, which the test supplies from a file that also carries its own `main` and error callback, so it cannot be linked against the generated driver. |

Out-parameters whose type the test defines itself (an output type, or `iter`'s
`OUT_T`) are handed over zeroed -- as a well-behaved client would -- and
compared byte for byte afterwards. They are *not* poisoned with a fill
pattern: some of them hold pointers that the test's own external API
dereferences.

## Requirements and portability

POSIX only. `harness.c` maps its probe source region at a *fixed* address with
`mmap(MAP_FIXED)`: the two executables must observe byte-identical pointer
values, otherwise probe actions that copy pointers would legitimately differ.
There is precedent for the restriction -- `probe_error_handler_macro` is
likewise disabled on Windows for want of `sys/mman.h`.

`python3` is required to generate the driver.

## Reaching the accepting path

Comparing two backends on inputs they both reject is worth much less than
comparing them on inputs they accept: a rejection exercises one refinement and
stops, while an accepted parse runs the whole validator. An entrypoint that is
never once satisfied therefore contributes almost no evidence, and a blind
mutator satisfies very few grammars. Four things get the corpus past that:

- **A constant dictionary.** `gen_diff.py` collects every integer literal in
  the entrypoint's `.3d` and hands it to the mutator, which plants them at
  random offsets in each width and byte order. Literals are read from the
  `.3d` rather than from generated code because the interpreter backend
  compiles them away into a grammar data structure -- neither `ELF.c` nor
  `ELF.fst` retains the ELF magic. They are kept in order of first appearance,
  so laying a run of the dictionary down end to end reproduces a multi-byte
  magic number verbatim; the corpus is seeded with several such runs.
- **A solver-derived seed corpus.** Some grammars cannot be hit by search at
  all: `Arithmetic`'s `_Check` is thirteen consecutive `UINT32`s each pinned
  to an exact value computed from earlier fields. `gen_seeds.py` runs
  EverParse's own `3d --api lowstar --z3_test` over those and checks the accepted witnesses
  in as `seeds.inc`, so neither Z3 nor the generator is needed to build or run
  this test. See `gen_seeds.py` for how to regenerate it.
- **Seeds in several content families.** All zeroes above all: an empty
  `[:zeroterm]` array is two zero bytes and a zero tag selects a union's
  smallest case, so the all-zero input is the shortest accepted input of many
  grammars.
- **Budget where it is needed.** An entrypoint that has not yet accepted
  anything keeps fuzzing for `STARVED` times the normal budget, and a slice of
  the corpus is reserved so that a rare accepted case is not evicted by the
  thousands of distinct ways to fail.

The fuzz log names any entrypoint that never accepted an input, so this stays
visible rather than having to be rediscovered.

## Known coverage gaps

- Three entrypoints are still never satisfied. `ElfCheckElf` and
  `TatMostCheckT` need a combination of magic values, lengths and terminators
  that neither the dictionary nor the solver reaches in reasonable time --
  `3d --z3_test` does not finish on either grammar. `Specialize6CheckSri` is
  out of the witness generator's reach for a different reason: it rejects
  probe arguments outright ("unsupported argument type"). All three are still
  compared on thousands of rejecting inputs.
- Only the `buffer` input-stream backend is exercised; `extern` and `static`
  are covered by the fixed-input tests elsewhere.
- Error *position* is not observable through the `<Mod>Check<T>` ABI, so it is
  not compared here.

## History

This harness found the one real difference between the backends: Pulse's
`validate_pair` ignored its `k1_const`/`k2_const` flags and so lacked Low\*'s
length-only fast path. It showed up as a different reported field name on
"not enough data". After the fix, the traces are identical.

## Files

| File | Role |
| --- | --- |
| `gen_diff.py` | parses `*Wrapper.h`, emits `driver.c` (thunk + dispatch table per entrypoint, plus the per-module constant dictionary) |
| `gen_seeds.py` | regenerates `seeds.inc` from `3d --z3_test`; run by hand, not by the build |
| `check_api.py` | rejects absent, mixed, or wrong-API generated validator headers |
| `test_harness.py` | regression tests for API checks and on-demand build wiring |
| `seeds.inc` | checked-in inputs a solver proved are accepted, for entrypoints fuzzing cannot reach |
| `run_subdir.sh` | compares one sub-directory test: works out the sources, builds both, fuzzes, replays, diffs |
| `harness.h` | shared case/entry/callback types |
| `harness.c` | probe & copy-buffer model, mmap'd source region, mutation engine, `fuzz`/`replay` `main` |

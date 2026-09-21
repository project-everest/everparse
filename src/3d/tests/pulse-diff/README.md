# Low\* vs. Pulse differential test

3D has two code-generation backends: the original Low\* one (`src/3d/prelude/`)
and the Pulse one (`lib/everparse/3d/`, selected with `3d --pulse`). They share
only the frontend; the validators they emit are produced by entirely separate
verified preludes. They are nevertheless supposed to be *behaviourally
identical*.

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

    make -C src/3d/tests pulse-diff

Knobs:

| Variable | Default | Meaning |
| --- | --- | --- |
| `ITERS` | `20000` | fuzzer iterations per entrypoint, per backend |
| `LO_DIR` | `src/3d/tests/out.batch` | Low\* generated C |
| `PU_DIR` | `share/everparse/tests/3d/out.pulse` | Pulse generated C |

The two input directories are produced by the ordinary `batch-test` and
`pulse-batch` targets, so a normal build already has them; the Makefile builds
them on demand otherwise. Regenerating them is slow (several minutes per
backend), which is why they are reused rather than rebuilt here.

`pulse-diff` is **not** part of `src/3d/tests`' `all` target, because it needs
both backends and the Pulse one is absent from `NO_PULSE` builds.

## Requirements and portability

POSIX only. `harness.c` maps its probe source region at a *fixed* address with
`mmap(MAP_FIXED)`: the two executables must observe byte-identical pointer
values, otherwise probe actions that copy pointers would legitimately differ.
There is precedent for the restriction -- `probe_error_handler_macro` is
likewise disabled on Windows for want of `sys/mman.h`.

`python3` is required to generate the driver.

## Known coverage gaps

- Seven of the 41 entrypoints are never satisfied even after fuzzing, because
  they need structured magic values the mutator will not stumble upon:
  `ArithmeticCheckCheck`, `ElfCheckElf`, `ElftestGenCheckElftestGen`,
  `FineGrainedProbeSpecializeCheckD`, `Specialize6CheckSri`, `TatMostCheckT`,
  `TestActions1CheckC`. Seeding the corpus from Z3TestGen would close these.
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
| `gen_diff.py` | parses `*Wrapper.h`, emits `driver.c` (thunk + dispatch table per entrypoint) |
| `harness.h` | shared case/entry/callback types |
| `harness.c` | probe & copy-buffer model, mmap'd source region, mutation engine, `fuzz`/`replay` `main` |

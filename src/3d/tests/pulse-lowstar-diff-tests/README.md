# Pulse legacy-ABI differential gate

Run `make -C src/3d/tests/pulse-lowstar-diff-tests`. The corpus comparison selects
**only** `--api legacy_lowstar` and `--api lowstar`, never native Pulse and never a
reference-versus-reference fallback. It needs the existing EverParse toolchain,
Python 3, a C compiler with GNU-compatible `--wrap` linker support, and clang
for inspecting structured output declarations. No Python packages are needed.

The default gate runs `adapter-tests/run.py all`, including native Pulse
regression clients. Set `EVERPARSE_TEST_32BIT=1` to additionally run `large32`
(for example, `EVERPARSE_TEST_32BIT=1 make -j16 3d-test`). The 32-bit tests are
disabled by default; enabling them requires real `-m32` support, provided on
Ubuntu by `gcc-multilib`. The GitHub Actions `ci.yml` workflow installs that
package in the test container and enables the tests.
Host and enabled 32-bit tests run sequentially because they share generated fixtures.
They do not rebuild the runtime: the root target's `3d-pulse-krml` prerequisite
provides it without racing concurrent native tests. `SANITIZE=1` enables the
adapter host-width ASan/UBSan checks. Missing 32-bit support is a hard failure
when the tests are enabled or `adapter-tests/run.py large32` is invoked directly.
Adapter fixtures are separate regressions, not part of the old-corpus inventory.

`make runtime` compares the legacy and Pulse-generated runtime headers for
all three stream backends in C and C++: packed helpers, error reasons, range
checks, bitfields, first-error recording, callback signatures, and record
layouts. It also checks the internal byte-status helpers independently.
This runs as part of the differential gate.

`make selftest` runs independent Python and compiled C fixtures. Fixture success
is **not** backend compatibility evidence. `ARGS='--suite check_complete'`
restricts an integration investigation; a restricted run always reports
`incomplete` and exits nonzero, even when its selected comparisons pass.
`--timeout` bounds each command and each individual Make target, not the sum of
all root build targets. Timeouts terminate the command's process group, including
generator/compiler descendants. `--iterations` controls additional deterministic
random inputs, not the boundary cases or existing solver seeds.

## Parallel execution

`make -j16 3d-lowstar-diff-test` (or the enclosing `make -j16 3d-test`)
shares GNU Make's jobserver budget with the rest of the build. The runner
holds one implicit slot and borrows a token for each additional active job,
returning tokens even after failures. Linux pipe jobservers and GNU Make FIFO
jobservers are supported; inaccessible or unsupported jobservers fail explicitly.

For a standalone invocation, use `python3 run.py --jobs 8`. Without a jobserver,
the default remains one job. `--jobs N` also caps concurrency under Make without
overriding its token budget; the default cap there is the CPU count.

Both API builds, independent suites, the six root build targets, and individual
negative cases run concurrently. After the build phase, module comparisons and
direct ABI regressions share that same budget. Each Make invocation stays at
`-j1`, and each module's two compilations/runs remain sequential, avoiding nested
worker pools. Jobs only read shared source/toolchain files: build targets write
separate output directories, and comparisons have per-module package directories.
Host and enabled 32-bit adapter checks still run sequentially before the corpus phase
because they reuse fixture outputs.

Build logs are named `<api>.<target>.build.log` in each suite's results directory.
A single coordinator writes the report, including individual `build_jobs`
outcomes; comparison entries are sorted independently of completion order.
All runnable jobs finish even when another fails. Failed builds block their
suite's comparisons, never turn into skips or reduce required corpus coverage.

## Corpus and isolation

`git ls-files share/everparse/tests/3d/lowstar` is the source of truth, excluding generated output
directories and differential-harness sources. Every remaining file has a
category, SHA-256 digest, and owning build recipe in `inventory.json`. Unknown
directories and new negative cases fail closed. Sources are copied byte-for-byte
into two fresh staging trees; no original Makefile, grammar, client, callback,
stream, or copy-buffer implementation is edited.

Ordinary builds of that shared corpus default to `--api lowstar`. This harness
stays in `src/3d/tests` and sets `EVERPARSE_API` separately in each isolated
staging tree; no second source corpus is maintained for `legacy_lowstar`.

Each staging tree has a proxy `EVERPARSE_HOME/bin/3d.exe`. It preserves all
arguments, appends the selected API, rejects attempts to select another API,
and records invocations. In particular, it does **not** replace `EVERPARSE_CMD`:
extern/static options, includes, macro handlers, configuration, Z3 test
generation, and complete wrappers remain selected by the original recipes.
The real toolchain and library installation are shared read-only dependencies.
Generated C and headers, including `internal/`, are copied to separate
compilation packages; differential compilation does not include the original
generation directories. Every run gets a new `_build/run-*` directory.

For source tarballs, run `make inventory` in a Git checkout and package its
reported `inventory.json`. Pass `--manifest /path/to/inventory.json` in the
tarball. Checksums and the absence of unlisted source grammars are checked.
Package `share/everparse/tests/3d/pulse-lowstar-diff/seeds.inc` too: the deterministic witness bytes are reused
unchanged, though the old harness is not part of this suite's corpus inventory.

`goto_return` is explicitly **snapshot-only**: its original wrapper snapshot
checks must pass for each API. `exttype` is **generation-only**, not a runtime
test. Probe witness/differential/checker targets retain their original
generation/compilation expectations. All ten negative grammars have explicit
frontend or verification failure expectations; an option error, missing tool,
crash, or unrelated verification failure cannot satisfy a negative case.
The separate hash-checker implementation/rebuild is outside the shared corpus;
the corpus's generation and hash checks remain included.

Only lowstar's root `batch-cleanup-test` receives
`EXTRA_CLEAN_OUT_FILES=internal`. The original Make
recipe still checks the exact top-level file set; the runner additionally
requires the recursive internal inventory to be exactly the regular file
`internal/ELF.h`. Missing files, extra/nested entries, and symlinks fail.
The obsolete separate `EverParsePulseInternal.h` is rejected. Each API uses
its matching prebuilt `EverParse.h` for no-copy builds: `legacy_lowstar` uses
`src/3d/prelude/<backend>`, and `lowstar` uses
`lib/everparse/3d/krml/lowstar/<backend>`. Legacy receives no extras, and
inherited cleanup overrides are removed.

## Observations

Public wrappers and exported validators are discovered from actual generated
headers, not a hand-picked function list. Their names, return types, and argument
types must agree. One driver source is compiled against both variants, with
exact function-pointer assignments and incompatible-pointer diagnostics promoted
to errors.

The driver records returns, scalar and structured outputs, partial updates,
preservation of initialized outputs, normalized pointer offsets, stream suffix
length, and callback events. Linker interception of public validator calls exposes
packed kind/position and forwards the original callback unchanged after recording
type, field, reason, code, context identity, input view, and position. Original
macro diagnostics are associated with the current input and compared as well.
No callback event is truncated. Original clients run separately through their
unchanged recipes; supplemental drivers include their implementations with only
the `main`/error-hook symbol names isolated by the preprocessor.

Output structs use their actual header field declarations, including nested
records, arrays, and bitfields. Iterator and vector referents have explicit
initialized backing arrays. Union observers select the active member. C struct
padding is never serialized. Pointer identity is an offset in a registered
input/output region, or a specified referent; an unregistered pointer is an
error, never an `"other"` equivalence class.

The root probe grammars have no original standalone C client. Their supplemental
bounded symbolic-source model is in `root_probes.py`; its serialized field
observers describe the `.3d` wire layouts, omit alignment padding, and normalize
wire pointers to symbolic source offsets. This model is **not** substituted for
the original probe/specialization clients in subdirectories. Those retain their
actual pointer-returning, repointing, copying, and initialization callbacks.

`abi_regression.c` additionally asserts specific contract results against the
real `TestActions1` and exported `Point` headers: nonzero starts, no-read failure,
failure before/after consumption, action failure kind 5, constraint failure
kind 6, packed positions, and partial output preservation.

## Coverage and failures

Every function has a `required.json` field contract. `inputs.txt` identifies
every deterministic case, initial scalar state, start position, capacity, and
stream chunk size. `comparison.json` reports exact mismatches by case, function,
field, and both values, plus per-function success/failure and missing-field
counts. The final `report.json` accounts for every tracked corpus source,
original build outcome, generation invocation, and differential result.

A missing output directory/header, ABI mismatch, unsupported output shape,
unobserved required field/input case, or missing success/failure outcome blocks
the gate. Five top-level `ProbeInPlace` wrappers are explicitly negative-only:
their fixed requests are 28, 42, or 3338 bytes, whereas the unchanged original
callback accepts exactly four bytes. Their returns and outputs remain fully
compared, and an unexpected success fails the gate.
Failures are not converted to skips. Inspect the report's missing-coverage
entries when adding witnesses; do not weaken them to acceptance-only comparisons.
The input capacity is 4096 bytes: in particular, `TAtMost`'s 1729-byte bounded
field cannot be covered by the old harness's 256-byte limit. Focused witnesses
also cover ELF, enumerations, dependent lengths, TCP/IP, mutable outputs, and
both 32-bit and 64-bit specialization-array sources. Focused witnesses
receive nonzero destination capacity so success does not depend on their index
in the random corpus. Specialization-array arguments encode the source-width selector
in bit zero and the element count in the remaining bits.
Generation-only and snapshot-only categories provide no runtime coverage claim.
Passing this suite is an empirical corpus gate, not a proof of every valid
input or of the separate 32-bit large-stream portability milestone.

## Parent wiring

The root `3d-lowstar-diff-test` target runs this suite after generator and
runtime generation. It is included in `make 3d-test` on Pulse-enabled Linux
builds, alongside the existing native Pulse differential suite. The full
default run, without `--suite`, is the acceptance gate. `NO_PULSE` builds do
not run it. The existing test cleanup delegates to this directory's `clean`
target; it removes the owned
`_build` and `adapter-tests/_build` directories, preserving sources.

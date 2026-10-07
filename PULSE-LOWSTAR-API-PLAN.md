# Recovering the Low* C API with the 3D-Pulse backend

> **Historical design record — superseded by the implementation.**
>
> This document was written as a forward-looking proposal, and its text is
> left in the future tense as originally drafted. The migration it describes
> has since been carried out: `--api pulse` and `--api lowstar` both ship,
> the adapters of step 3 are implemented and verified, and the test moves of
> steps 4 and 5 are done.
>
> Two things to keep in mind when reading it:
>
> * **`--api legacy_lowstar` no longer exists.** Step 2 proposed retaining the
>   original Low\* implementation under that name as the default. It was
>   retained for a time, then disabled, and the Low\* backend and its prelude
>   have since been deleted outright. Every mention of `legacy_lowstar` below
>   therefore describes a transitional state, not a current option. The two
>   surviving APIs are `pulse` (the default) and `lowstar`, the latter being a
>   Pulse implementation behind a Low\*-compatible C ABI.
> * **The disclaimer below is out of date.** Where the introduction says no
>   implementation or proof has been performed, that was true at drafting time
>   only.
>
> For the behaviour EverParse actually has today, see `doc/3d.rst` and
> `doc/3d-lang.rst`, which are maintained; this file is not.

The Low* C API can be recovered while sharing most of the Pulse
implementation, but not merely by adding instances of the current typeclasses.
The plan is organized in execution order:

1. Align existing Pulse error values with Low* error kinds.
2. Replace `--pulse` with `--api pulse`, retaining the existing Low*
   implementation as the default `--api legacy_lowstar`.
3. Add `--api lowstar` using verified public ABI adapters around byte-status
   Pulse workers, and establish compatibility with a full Low* differential
   test suite.
4. Move the converted Low*-API tests to `share/everparse/tests/3d/lowstar`,
   defaulting their builds to `--api lowstar`; leave Low*-only tests in
   `src/3d/tests`.
5. Move the existing Low*-Pulse differential tests into the shared test tree
   and compare `--api lowstar` with `--api pulse`.
6. Retain the prior deeper validator/action refactor as an alternative or
   subsequent development, not a prerequisite for step 3.

This document records an investigation and proposed design. No implementation
or proof of the proposed interfaces has been performed. Extraction of the
proposed representation boundary is an explicit early milestone.

## 1. Renumber existing Pulse error values

Redefine the existing constants in
[`EverParse3d.ErrorCode`](lib/everparse/3d/EverParse3d.ErrorCode.fst)
to the following values. These remain `U8.t` **kind numbers**, not the
already-shifted `U64` error constants used by Low*:

| Current Pulse status | Meaning | Planned Pulse status / Low* kind |
|---|---|---|
| 0 | Success | 0 |
| 1 | Action failed | 5 |
| 2 | Not enough data | 2 |
| 3 | Impossible | 3 |
| 4 | List size not multiple | 4 |
| 5 | Constraint failed | 6 |
| 6 | Unexpected padding | 7 |
| 7 | Probe failed diagnostic | 8 |

Reserve kind 1 for Low*'s generic error rather than action failure; no new
generic-error production path is required. Update `error_reason_of_result`
with the renumbering so existing named errors retain their reason strings.
For defined statuses, later callback conversion becomes widening to `U64`,
with no permutation of error kinds.

The core can retain its current `res == 0` tests, but must replace
`res > validator_error_action_failed` and equivalent hard-coded numeric
tests with semantic predicates. For validator results, the parser-rejection
case is `res != validator_success && res != validator_error_action_failed`.
Apply this consistently to consuming/non-consuming contracts, loop
invariants, supporting lemmas, and callers; otherwise moving action failure
to 5 would lose the rejection guarantee for errors 2-4. Keep the separate
action-failure-implies-`has_action` property. Diagnostic codes passed to a
callback do not themselves establish parser rejection.

This intentionally changes the numeric statuses observable through the
existing native Pulse API, while preserving its byte return type and calling
conventions. Update native documentation, generated headers, reason tables,
test expectations, and any literal-code consumers together. Record the
numeric compatibility change explicitly; do not describe native behavior as
completely unchanged.

**Completion gate:** verify every named value and its reason string,
especially action failure 5 versus parser failures 2-4, retain success 0,
and re-establish the rejection/action guarantees throughout the shared
development. This step does not depend on public ABI adapters or the CLI
migration.

## 2. Replace `--pulse` with `--api pulse`

Introduce a single `--api` selector, orthogonal to stream transport, with
these two implemented choices at this stage:

| Option | Implementation | Public C API |
|---|---|---|
| `--api legacy_lowstar` (default when omitted) | Existing Low* implementation | Existing Low* API |
| `--api pulse` | Existing Pulse implementation, after step 1 | Native Pulse API |

Remove `--pulse` from the supported options and migrate its uses to
`--api pulse`. Omitting `--api` must preserve today's default Low*
implementation. Do not introduce a separate `--pulse_api` option.
`--api lowstar` is added in step 3; until it is implemented, it must not
silently fall back to either existing backend.

Represent the selection as an explicit API-mode value, extensible with the
third case in step 3, rather than independent booleans. Audit every
`Options.get_pulse` branch and distinguish implementation selection from
public calling-convention selection. At this stage, `pulse` uses the Pulse
generator/toolchain and native ABI, while `legacy_lowstar` uses the original
Low* generator, prelude, toolchain, and ABI.

Carry the selection through configuration, dependency generation,
extraction/header directories, generated command lines, and any
option-sensitive cache or hash handling so incompatible artifacts cannot be
reused. Update CLI help, documentation, examples, build scripts, and test
invocations to use the new names.

**Completion gate:** omitted `--api` and explicit `--api legacy_lowstar`
select the same existing implementation; `--api pulse` replaces the former
switch without changing its behavior beyond step 1's error renumbering.
Reject unknown values and the removed `--pulse` switch using the standard
option-error mechanism. Generated build commands must preserve the selected
mode.

## 3. Add `--api lowstar` with verified public ABI adapters

This is the lower-churn design formerly presented as Section 7. It follows
steps 1 and 2, retains byte-status workers internally, and adds the third API
mode rather than replacing either existing implementation. The deeper
refactor in Section 6 is not a prerequisite.

### 3.1. Compatibility target

Target the checked-in Low* headers and implementation, rather than every
detail of the prose documentation. In particular, the actual Low* error
callback has seven arguments, not the older nine-argument example in
`doc/3d-lang.rst`.

| Surface | Current Pulse | Low*-compatible target |
|---|---|---|
| Consuming validator result | `uint8_t` status | `uint64_t`: position on success; error kind in the high four bits and position in the low 60 bits on failure |
| Buffer validator input | Pointer, `size_t` length, `size_t *` position | Pointer, `uint64_t` length, `uint64_t` position passed by value |
| Extern validator input | Stream base, encoded bound, origin | `EVERPARSE_INPUT_BUFFER { base, has_length, length }`, plus position passed by value; separate length argument erases |
| Error callback | Byte error code and separate stream components | `uint64_t` error kind, `EVERPARSE_INPUT_BUFFER`, field-start position |
| Extern primitives | `EverParseStream*`, including position lookup and copying reads | `EverParseHas/Read/Skip/Empty/Peep`; no position-lookup requirement; reads may return a pointer other than the scratch buffer |
| Buffer copy-buffer projections | `StreamOf`, `size_t StreamLen`, `StreamPos` | `StreamOf`, `uint64_t StreamLen`; no client-owned position cell |

Sources:

- [Low* error encoding](src/3d/prelude/EverParse3d.ErrorCode.fst#L9-L163)
- [Low* buffer header](src/3d/prelude/buffer/EverParse.h#L177-L224)
- [Low* extern header](src/3d/prelude/extern/EverParse.h#L172-L257)
- [Pulse validator types](lib/everparse/3d/EverParse3d.Actions.Base.fst#L65-L145)

Compatibility includes direct calls to generated validators, callbacks,
macros, copy buffers, and existing stream implementations, not merely the
already-compatible `Check...` entrypoint signatures.

### 3.2. Why new instances alone are insufficient

Three assumptions are embedded in the shared implementation:

- **Results are fixed to `U8.t`.** Both validator types return it. Step 1
  aligns error kinds and removes ordering-based failure classification, but
  changing an input-stream instance still cannot change the result type to
  Low*'s packed position/error representation.
- **Consumption changes state behind the same stream arguments.** The
  consuming validator's postcondition uses the same `sl_pos` as its
  precondition. This works for a mutable buffer-position reference or a
  self-positioning extern stream. Setting `pos_t = U64.t` does not make a
  scalar position advance. Non-consuming validators additionally hard-code
  a `ref SZ.t` lookahead cursor.
- **Copy-buffer ownership includes a persistent position projection.**
  `copy_buffer.pos_of` and `reset` assume the copy buffer supplies its
  validation cursor. Low* buffer clients supply no such cell. See
  [CopyBuffer](lib/everparse/3d/EverParse3d.CopyBuffer.fsti#L39-L65).

Some existing abstractions are already useful. The class's high-level `read`
returns a parsed value, so it does not inherently require copying. Also,
`error_handler_t` already permits a distinct callback type: an inlined
`error_handler_arrow_of_t` adapter can discard arguments and translate codes.
Retain these foundations rather than duplicating the backend.

### 3.3. Lower-churn approach

Keep the existing `U8.t` validator answers, mutable-cursor consuming protocol,
and most combinator implementations, using the aligned error kinds and
semantic classifications established in step 1. Pack results only when
leaving a public validator, and widen diagnostic codes only when invoking a
legacy callback.

This is more than a hand-written C wrapper around today's Pulse output:

- The public adapter must be verified in Pulse, before C extraction.
- Its worker must use a legacy-compatible callback type and stream instance.
- The extern instance must count consumption locally, without requiring
  `EverParseStreamGetPosition`.
- Copy-buffer ownership must no longer require a client-provided position
  cell.
- Full 32-bit stream compatibility still requires a small change to the
  stream/lookahead interface. Widening a final C cast is insufficient.

The important distinction from Section 6 is that progress remains in mutable
state throughout the core. Therefore, list loops can continue retaining only
failure statuses, `t_at_most` can continue returning byte success after
draining, and actions can continue returning their existing value types.
The adapter reads the final cursor and constructs the packed result.

This is a source-grounded design, not yet a typechecked or extracted
prototype. The proof and extraction gates below must be completed before
claiming feasibility of every proposed interface detail.

### 3.4. Two validator views, not two parser implementations

For each generated validator that has a public C definition, generate:

| Definition | Role |
|---|---|
| `validate_X_core` | Current Pulse validator denotation, specialized to the selected instance; returns `U8.t` and uses an internal cursor |
| `validate_X` | Public Low*-compatible Pulse adapter; keeps the existing C validator name, accepts scalar start position, and returns packed `U64.t` |
| `dtyp_X` | Interpreter metadata whose validator component refers to `validate_X_core`, not to the public adapter |

The names above are illustrative. Keep the current normalization,
`allow_reading` metadata, state-dictionary parameters, and erasure discipline.
Only emit a public adapter where the current backend emits a public
validator. Internal grammar helpers need not acquire redundant public
wrappers.

This split is necessary because the frontend currently uses `validate_X`
twice: as the extracted C function and as the validator stored in `dtyp_X`.
Simply changing its return type would break `mk_dtyp_app` and imported
`global_binding.p_v`, which require the Pulse validator type. Relevant sites:

- [Validator and dtyp generation](src/3d/InterpreterTarget.fst#L1602-L1688)
- [Generated interfaces and export decisions](src/3d/InterpreterTarget.fst#L1396-L1444)
- [Global binding's validator type](lib/everparse/3d/EverParse3d.Interpreter.fst#L242-L266)
- [mk_dtyp_app](lib/everparse/3d/EverParse3d.Interpreter.fst#L1676-L1700)

Within a generated module, and across imported grammar modules, workers call
workers. The mutable cursor is passed through unchanged as a reference, and
there is no pack/unpack round trip at each field or module call.

Do not recover this internal view by calling the public adapter in reverse.
Such a bridge would need to decode results, update the caller's cursor, and
handle nonzero speculative offsets. In particular, an extern no-read
validator cannot be invoked at a fictitious advanced physical position
without consuming the stream. Retaining the actual worker interface avoids
this problem.

All modules in one generated dependency graph must use the same API policy.
Supporting arbitrary calls between precompiled native-Pulse and
legacy-Pulse workers is outside this plan. Public Low* C compatibility is
not F* source-interface compatibility.

### 3.5. Public adapters and their proof obligations

Write reusable, backend-specific adapter combinators in the Pulse library.
The frontend instantiates them with the generated worker; it should not
generate ad hoc packing arithmetic in every validator body.

The following is pseudocode, not proposed compilable F*:

```text
consuming_adapter(input, length, start):
    allocate local actual_cursor initialized from start
    establish the worker stream predicate using that cursor
    status = consuming_worker(input, length, actual_cursor)
    end = read actual_cursor
    restore public stream ownership and retire local cursor
    return pack(status, end)

non_consuming_adapter(input, length, start):
    allocate local actual_cursor initialized from start
    allocate local lookahead_offset initialized to zero
    establish the worker stream predicate
    status = no_read_worker(input, length, actual_cursor, lookahead_offset)
    if status is success:
        answer = start + lookahead_offset
    else:
        answer = pack(status, start)
    restore public stream ownership and retire both local cursors
    return answer
```

The public adapter passes the original base and coordinate system to the
worker. It must not rebase the buffer to `base + start` and then report
field positions relative to that new base. Likewise, nested workers must not
reset an extern cursor to zero.

Use separate verified adapter types for consuming and non-consuming
validators, or an erased `allow_reading` index selecting between them:

| Case | Public result position | Physical stream effect |
|---|---|---|
| Consuming success | Final actual cursor | Parser's consumed prefix removed |
| Consuming failure | Final actual cursor, with translated error kind | Any consumed prefix remains consumed |
| Non-consuming success | Start plus validated lookahead | Input stream unchanged |
| Non-consuming failure | Start, with translated error kind | Input stream unchanged |

The failure case must ignore any final lookahead-reference value: the
current no-read postcondition does not constrain that value on failure.
The original input stream is preserved on both no-read outcomes. These
facts are visible in
[the Pulse contracts](lib/everparse/3d/EverParse3d.Actions.Base.fst#L65-L145);
the Low* contract also distinguishes prospective success positions from
actual consumed positions on failure:
[Low* validator postcondition](src/3d/prelude/EverParse3d.Actions.Base.fst#L231-L254).

The exported Pulse specification must establish:

- Correct correspondence to the same pure parser.
- Exact consumption on success and suffix preservation on failure.
- The Low* error-position rule for the selected `allow_reading` mode.
- Parser rejection for non-action validation failures.
- Preservation of application-context ownership and the state dictionary,
  including the existing no-action state-preservation guarantee.
- Every encoded position is at most `2^60 - 1`.
- Local cursor references do not escape, including through copy-buffer
  state or callbacks.

For a consuming worker, its suffix postcondition plus the instance's cursor
invariant already supplies the position needed for packing. There is no need
to strengthen every consuming combinator with a new runtime result field.
For non-consuming success, the parser-length theorem supplies the bound for
the addition. Do not use masking or modular addition to hide an unproved
position bound.

The adapter must select the same reading mode as the existing generator.
Entrypoints are consuming; exported non-entrypoint validators may be
non-consuming. Do not force every exported validator through `validate_drop`.

### 3.6. Pack aligned statuses and adapt callbacks

Use the aligned byte kinds from Section 1. Result packing and callback
invocation share a verified `legacy_kind` conversion; named kinds only need
widening, not renumbering.

For a bounded position `p`, packing is conceptually
`(legacy_kind(status) << 60) | p`; success consequently returns `p`.
Reuse the pure bitfield reasoning underlying the Low* implementation, in a
distinct Pulse compatibility namespace. Do not import the effectful Low*
prelude or put two different modules named `EverParse3d.ErrorCode` on the
Pulse include path.

The current validator contracts admit arbitrary byte statuses, even though
the constructors in the current implementation use the listed constants.
Make the conversion total without assuming an unstated range: map other
nonzero byte statuses to a reserved unspecified Low* kind, for example 15.
This preserves failure and the existing "unspecified" reason, and avoids
truncating an arbitrary byte into four bits. The values from Section 1 remain
mandatory: `legacy_kind` widens those new values, rather than applying the
old-to-new renumbering a second time. Any future named status must use its
corresponding Low* kind. An alternative is to strengthen the worker contracts
with a finite-status invariant, but that is additional churn and is not
required by this design.

Error reporting has a separate boundary from validator return. Use the
existing `error_handler_t` member for the actual seven-argument callback,
and implement `error_handler_arrow_of_t` as an inlined adapter that:

1. Widens the aligned byte kind, applying the unspecified-code policy above.
2. Preserves type name, field name, reason, context, and saved field start.
3. Passes the legacy input pointer or input-buffer record.
4. Discards the internal length/cursor arguments that the legacy callback
   does not accept.

The worker itself receives the legacy callback value, not a newly allocated
closure. Only its application is adapted. The current canonical arrow
provides enough information for this, and all callback applications go
through the conversion hook:
[InputStream.Base](lib/everparse/3d/EverParse3d.InputStream.Base.fst#L40-L137)
and
[Actions.Common](lib/everparse/3d/EverParse3d.Actions.Common.fst#L38-L52).
Thus the general callback-dispatch redesign in Section 6.1.D is not necessary
for this alternative.

Check extraction explicitly: the conversion must beta-reduce to a direct
call of the supplied handler. Do not cast incompatible function pointers,
use a global trampoline, or replace the caller's application context with
adapter bookkeeping.

Macro mode uses a separately typed legacy
`EVERPARSE_ERROR_HANDLER_MACRO`, still with seven arguments. Specialization
must remove the dynamic handler parameter, just as it does today.

Preserve the distinction between diagnostics and validator outcomes. For
example, a failed probe can report diagnostic kind 8 and then cause an
enclosing action to return failure kind 5. Also preserve probe diagnostics
that deliberately pass code zero and a contextual reason. Recomputing every
reason from a packed return value would lose that information.

### 3.7. Buffer: reuse the current stream machinery

The lower-churn buffer worker does not need a scalar cursor or `U64` length
internally. Reuse the current:

```text
base_t = ArrayPtr.ptr U8.t
len_t  = SizeT.t
pos_t  = ref SizeT.t
```

Create a legacy buffer instance using the same points-to predicate and
stream operations, but selecting the legacy handler type and conversion.
Retain the existing `field_ptr` implementation, with any necessary
instance-specialization adjustment rather than a second pointer algorithm.

The public adapter still has `uint64_t length, uint64_t start`. It proves
their conversion to `SizeT` from the Low* buffer-domain bound and
`start <= length`. The Low* public length type is `U64`, but its underlying
buffer model is bounded by `U32`:
[Low* buffer length](src/3d/prelude/buffer/EverParse3d.InputStream.Buffer.fst#L8-L16).
The existing platform assumption that `size_t` can represent `U32` is
therefore sufficient.

This avoids modifying the native buffer implementation merely to change a
public argument width. The final native-sized cursor is widened for result
packing. Copy buffers need the separate lifetime treatment in Section 3.10.

### 3.8. Extern/static: a counted internal stream instance

Unlike buffer, the legacy extern worker needs a new implementation. Use:

```text
base_t  = named legacy input_buffer record { base; has_length; length }
len_t   = unit
pos_t   = ref U64.t
extra_t = abstract legacy EVERPARSE_EXTRA_T
trunc_t = base_t
```

The reference is allocated by the public adapter and initialized to its
scalar start argument. It is not stored in the client object and does not
appear in the public C signature.

The stream predicate owns the raw client-stream resource and that local
reference, tying the reference's value to
`length(contents) - length(remaining)`. A bounded view additionally ties its
length to the input-buffer record. Prove the packed-position bound from the
legacy stream model, matching the existing Low* obligation rather than
imposing a new client position-query function.

Implement the methods as follows:

| Method | Legacy implementation |
|---|---|
| `get_position` | Read the local `U64` reference |
| `has` | For a bounded view, compare against `length - current`; otherwise call `EverParseHas` with a widened count |
| `has_at` | Check the relative offset/count against the bound, or call `EverParseHas(extra, base, off + n)` using checked arithmetic |
| `read` | Call pointer-returning `EverParseRead`, read the returned bytes with the existing leaf reader, and increment the local counter once |
| `skip` | Call `EverParseSkip` and increment the local counter once |
| `empty` | Unbounded: call `EverParseEmpty` and add its returned count; bounded: skip exactly `length - current` |
| `truncate` | Return a record with `has_length = true`, `length = current + n`, and the same raw base |
| `untruncate` | Rejoin the ghost view resources; keep the same updated cursor reference |

Set `trunc_base` to the returned record, `trunc_len` to unit, and `trunc_pos`
to the existing reference. The current `trunc_t`/projection mechanism already
supports this: it does not require the native instances' choice
`trunc_t = len_t`. A named public legacy record is intentional here, unlike
an anonymous tuple whose C placement is determined by first use.

Nested calls share the reference, including on failure. A fresh public
validation starts from the caller's scalar argument, so repeated wrapper
calls do not require a cumulative client counter. `EverParseRetreat` retains
the Low* wrapper protocol; there is no native origin subtraction or
`EverParseStreamGetPosition` dependency.

For pointer-returning reads, give the raw primitive an assumed Pulse contract
that lends a readable view of the result and a ghost restoration obligation
for the stream and scratch-buffer resources. Apply the existing fractional
leaf reader, discharge the restoration, and only then leave the scratch
buffer's scope. The result may equal `dst` or point into client storage.
Never require these alternatives to be disjoint full-ownership resources
simultaneously. No new C release primitive is needed: restoration is ghost.

This is a new formulation of the existing trusted client obligation, not a
proof of arbitrary client C implementations. Keep the trust boundary
explicit and do not add assumptions that exclude Low*'s permitted aliasing.

For `field_ptr_after`, call `EverParsePeep` after a bounds check, test the
nullable pointer, and update the destination or invoke the setter only on
success. Do not advance the local counter for `Peep`: the Low* specification
is non-consuming despite the documentation discrepancy noted in Section 6.2.
Use a nullable-pointer FFI representation and a checked conversion to the
non-null action pointer type, not an assumed non-null result.

Static mode reuses this instance and changes only the linkage of the old
client primitives.

### 3.9. The limited count-interface changes still needed

An unchanged `SizeT` interface is not sufficient for full legacy extern
semantics on 32-bit targets. There are two independent problems:

**The `empty` return type.** It currently returns `SZ.t` equal to the entire
remaining length, although both generic callers discard the value:
[`validate_t_at_most`](lib/everparse/3d/EverParse3d.Actions.Base.fst#L1176-L1183)
and
[`validate_all_bytes`](lib/everparse/3d/EverParse3d.Actions.Base.fst#L2316-L2336).
An opaque legacy stream can have more remaining bytes than `SIZE_MAX`.

The smallest useful change is to make the high-level class method return
unit with the same "remaining stream is empty" postcondition. Native
instances discard their existing helper's count; the legacy instance uses
its raw `U64` count internally to update the cursor. This does not change
either native or legacy client primitive signatures. It also avoids
introducing a general numeric dictionary just for draining.

**The `has_at` contract.** It requires both mathematical availability and
`SZ.fits(off + n)` on success:
[current contract](lib/everparse/3d/EverParse3d.InputStream.Base.fst#L219-L239).
On a 32-bit machine, take `off = SIZE_MAX`, `n = 1`, and a stream with at
least `2^32` remaining bytes. Availability requires true, while the fit
condition is false. An unbounded legacy instance cannot satisfy this
contract, even if today's generated calls commonly start lookahead at zero.

Do not implement overflow by returning "not enough data" when the legacy
stream actually has those bytes; that would change parser semantics.

For full portability, add a narrow lookahead/count policy to the stream
dictionary:

- Associated `scan_t`, its ghost natural-number value, zero, conversion to
  `U64`, and checked addition of a `SizeT` field size.
- `has_at` takes `scan_t` offsets and proves the sum fits `scan_t` on success.
- No-read validators keep `ref scan_t`, rather than hard-coded `ref SZ.t`.
- The committing `skip` accepts `scan_t`, since `validate_drop` obtains its
  count from that reference.
- Native instances and legacy buffer choose `scan_t = SizeT`; legacy extern
  chooses `scan_t = U64`.

Keep leaf read sizes, `has`'s small requested counts, and size-bounded
truncation arguments as `SizeT` where they already arise from leaf widths
or `U32` grammar lengths. The existing fused-size fast path explicitly
requires a size below `2^32`. This is smaller than parameterizing all
arithmetic or the consuming cursor protocol.

The affected shared code is concentrated: the no-read type and wrappers,
the zero-initialized lookahead locals, the size-check addition,
`validate_drop`, the list-up-to reset, and the no-read error-handler offset
conversion. This count-interface change does not alter the consuming
validator result or loop-status invariants beyond the separate error
classification migration in Section 1. Native specialization must retain
its existing C types.

A 64-bit-only initial spike can keep `scan_t = SizeT`, but it is not the
completion criterion for full compatibility. Do not silently declare
32-bit clients unsupported.

### 3.10. Copy-buffer cursor lifetime and probe diagnostics

Do not implement a fake `EverParseStreamPos`, a global handle-to-position
table, a heap allocation per copy buffer, or a hidden extra field in the
client's opaque object. These would change the client contract and create
reentrancy or lifetime problems.

Instead, change the copy-buffer dictionary in three focused ways:

| Component | Purpose |
|---|---|
| Instance-provided storage predicate | Describe persistent copy-buffer ownership without requiring a live validation cursor |
| Scoped validation-view operation | Supply base/length/cursor to an inlined continuation, then restore storage ownership |
| Probe-diagnostic operation | Report against a copy buffer without requiring a generic runtime position projection |

Keep `CB.pts_to` as the common name used by probe contracts and state
dictionaries, but make it delegate to the instance's storage predicate.
This avoids rewriting the probe monad's state plumbing just to remove
`pos_of`.

The scoped validation operation has a higher-order, compile-time-only shape:
the continuation runs with the normal stream predicate and returns it with
an updated suffix. It must be inlined/specialized, not emitted as a C closure.
This is preferable to returning a reference to a stack-allocated cursor.

For native buffers, storage is the existing predicate; the operation uses
the existing projected position cell and reset. For legacy buffers, storage
owns the byte-array view independently of any position reference; allocate
a local `SizeT` cursor at zero for the continuation. For legacy extern,
storage owns the raw input-buffer view; allocate a local `U64` cursor at
zero.

Require an unread destination when acquiring this zero-based validation
view. `probe_then_validate` calls it only after a successful `run_probe_m`,
whose postcondition already gives `contents_dest == v_dest`. Do not invent
a general rewind operation for a consumed legacy extern stream. The probe
initialization/copy callbacks are responsible for establishing a fresh unread
view, as in their existing contracts.

At the end, restore storage ownership on success and failure, dispose of
the local cursor, and retain the updated logical contents/suffix in the
existing state-dictionary entry. A buffer need not store that logical cursor
in client memory. Fetch the destination projections after probe callbacks:
those callbacks are allowed to repoint the handle.

Only a few places depend on the concrete projections:
[`probe_then_validate`](lib/everparse/3d/EverParse3d.Actions.Base.fst#L3151-L3267)
and
[`handle_probe_error`](lib/everparse/3d/EverParse3d.ProbeActions.fst#L200-L234).
Most probe combinators already use the abstract `CB.pts_to`.

For probe diagnostics, delegate to the copy-buffer instance. The native
instance retains today's reporting behavior. The legacy instance reports the
destination with code zero and start zero, matching
[the Low* helper](src/3d/prelude/EverParse3d.ProbeActions.fst#L212-L234).
It does not need to reconstruct a discarded cursor from ghost sequence
lengths. Ordinary validation errors inside that destination still use the
worker's live local cursor and saved field starts.

Update the frontend's copy-buffer/probe selection as well. It currently
hard-codes `B.input_stream_buffer` in copy-buffer arguments and standalone
probe generation, in addition to rejecting extern probes. Replace those
assumptions with the selected instance/capability. Preserve restrictions that
also exist in Low*, such as top-level probe wrappers being buffer-only.

### 3.11. Keep workers available to F* but out of the public C ABI

An imported `dtyp_X` needs a visible F* declaration for `validate_X_core`.
Therefore, ordinary F* `private` is not the right way to hide all workers.
Likewise, `noextract` on a worker that remains a runtime callee would remove
its implementation rather than solve visibility.

The repository already has a more suitable mechanism:
`[@@ "KrmlPrivate"]` extraction metadata. It is emitted by
[the CDDL generator](src/cddl/tool/CDDL.Tool.Gen.fst#L166-L172), recognized
by [F* extraction](opt/FStar/src/extraction/FStarC.Extraction.ML.Modul.fst#L129-L158),
and translated into KaRaMeL's private flag. Investigate emitting that
metadata consistently on worker declarations/definitions while retaining
their F* interface visibility.

KaRaMeL can retain a same-translation-unit worker as static, or promote a
cross-translation-unit private reference to its `Internal` visibility class
and emit an `internal/<Module>.h` declaration. The latter can still have
external C linkage; it is not a public-header API. This is supported by
[its visibility analysis](opt/karamel/lib/Inlining.ml#L240-L266).
It is not a promise that every worker will disappear through inlining.

Accept generated internal headers as implementation artifacts, while
requiring the public `<Module>.h` to expose the old validator types. Update
artifact collection, generated build dependencies, copying, cleanup, and
packaging accordingly. Current runtime-header generation explicitly rejects
an `internal/` directory, and
[Batch's file collection](src/3d/ocaml/Batch.ml#L723-L794)
enumerates a fixed set of public files; those assumptions need deliberate
treatment rather than relying on incidental build-directory contents.

First test metadata propagation through a generated `.fsti` and a two-module
call. If it cannot be made reliable, use an auxiliary implementation module
and bundle it as non-API, accounting for specification/type dependencies.
Do not postprocess generated C declarations to force the desired ABI.

### 3.12. Runtime names and addition of `--api lowstar`

Keeping byte statuses internally introduces a naming hazard even after
aligning the kinds: native status macros and legacy packed macros use names
such as `EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED`, but represent 5 and
`5 << 60`, respectively.
It is not safe to compile unchanged native worker references against the
old `EverParse.h`.

For legacy mode, give internal Pulse statuses and their reason helper a
distinct extracted prefix, for example `EverParsePulseInternal`, while
exposing the Low* names and packed meanings in the public header. Use
backend-specific bundle/name configuration or another extraction-supported
mechanism. Keep native-mode names unchanged. Generate the internal support
header if references survive inlining; do not rely on constant folding to
eliminate every collision.

The public legacy header must preserve the input-buffer record,
`EVERPARSE_ERROR_HANDLER`, `EVERPARSE_ERROR_FRAME`, packed error helpers,
copy-buffer projections, and stream primitive declarations. Keep
monomorphic callback aliases in small API modules, following the current
header-generation pattern. The C-visible struct and typedef names are part
of compatibility, not just their field representations.

Select wrapper behavior by C API policy, not solely by `Options.get_pulse`:

- Public compatibility validators use the existing Low*-style wrapper calls,
  `EverParseIsError`, and `EverParseGetValidatorErrorPos`.
- Wrapper constants use the Low* numbering.
- Default error handlers use the seven-argument signature and the correct
  input-buffer type.
- Complete-buffer wrappers compare the packed result position against the
  supplied length.
- Extern wrappers use the old `EverParseHandleError`/`EverParseRetreat`
  protocol and never emit a position-lookup declaration.
- Direct-validator calls and handlers emitted by `Z3TestGen` use the same
  policy.

Do not blindly include today's `EverParsePulse.h` alongside a complete
legacy runtime header: it defines the error frame and a buffer-pointer
default handler, which would duplicate or conflict with legacy definitions,
especially for extern. Select the appropriate runtime header set.

Extend the `--api` selector introduced in step 2 with `lowstar`. The completed
selection is:

| Option | Implementation | Public C API |
|---|---|---|
| `--api legacy_lowstar` (default when omitted) | Existing Low* implementation | Existing Low* API |
| `--api pulse` | Existing Pulse implementation, with the planned error-kind alignment | Native Pulse API |
| `--api lowstar` | Proposed Pulse implementation with verified adapters and compatible instances | Low*-compatible API |

Keep `legacy_lowstar` as the default; adding an API-compatible implementation
must not silently change the implementation selected when the option is
omitted. Extend the mode dispatch established in step 2: implementation
selection uses Pulse for both `pulse` and `lowstar`, whereas native calling
conventions apply only to `pulse`. Legacy calling conventions apply to both
`lowstar` and `legacy_lowstar`; the latter still selects the original Low*
generator, prelude, and toolchain path.

Extend configuration, dependency generation, extraction/header directories,
generated commands, cache/hash handling, CLI help, documentation, and tests
to account for the new mode. Keep all three modes' artifacts distinct.

Primary frontend/build surfaces:

| Surface | Change |
|---|---|
| `Options.Base`, `Options`, related interfaces | Extend the selector with `lowstar`; dispatch to Pulse with the Low*-compatible ABI |
| `InterpreterTarget` | Emit worker/public-adapter pairs, keep dtyp references on workers, select copy-buffer capabilities |
| `Target` | Select legacy wrapper calls, callbacks, constants, and runtime includes |
| `Z3TestGen` | Select matching direct-validator ABI and diagnostics |
| `Batch.ml` | Select runtime API modules, internal status prefix, typedef preservation, headers, and artifact handling |
| `krml/header.Makefile`, extraction/build rules | Generate native and legacy runtime variants without symbol collisions |
| `GenMakefile`, packaging/tests | Track any internal headers and the selected runtime variant |

### 3.13. Expected change budget

| Area | Expected impact under this alternative |
|---|---|
| Pure parsers, kinds, integer readers | No conceptual change |
| Consuming validator result type and classification | Retain `U8.t` and step 1's aligned kinds/semantic classification |
| Pair/filter/list/bounded-validator algorithms | Preserve control flow and step 1's migrated status invariants |
| Action return types and state dictionaries | Preserve; adjust copy-buffer predicate implementation |
| Buffer stream implementation | Reuse; add legacy handler instance and public adapters |
| Extern stream implementation | New counted instance using old primitives |
| Shared stream class | Unit-returning drain and narrow scan-type policy for full portability |
| Non-consuming combinators | Replace hard-coded scan type/operations; do not change their protocol |
| Error-handler class hook | Reuse existing conversion field rather than redesign dispatch |
| Copy-buffer class and two projection-dependent consumers | Focused ownership/lifetime redesign |
| Frontend and C runtime packaging | Necessary ABI-policy and worker-visibility changes |

This is not a zero-change-core solution, but it avoids migrating the entire
validator development to packed results and scalar cursor threading.

### 3.14. Implementation milestones and acceptance criteria

After completing steps 1 and 2:

1. **Adapter and callback extraction spike.** Use an ordinary leaf, an
   action/constraint failure after a read, and an exported no-read validator.
   Verify public scalar-start/packed-result specifications. Extract dynamic
   and macro callbacks. Confirm that the adapter leaves no incompatible
   callback casts, closure objects, or escaping stack references.
2. **Two-module visibility spike.** Generate an exported type in one module
   and a use in another. Confirm that dtyp metadata retains the worker,
   public prototypes retain the Low* ABI, and an internal worker declaration
   is generated and packaged when needed. Cover both reading modes.
3. **Legacy buffer, without probes.** Reuse native stream operations and
   add callback/result conversion. Compare unchanged Low* clients against
   the new public functions, including nonzero starts, nested error traces,
   output actions, and complete wrappers.
4. **Count-interface portability.** Change high-level draining to unit and
   add the scan policy. Re-specialize native instances to confirm unchanged
   native C signatures. Exercise the `has_at` overflow counterexample with a
   modeled large stream rather than allocating a giant byte array.
5. **Legacy extern/static.** Verify counting, bounds, truncation, drain, and
   pointer-returning read contracts. Exercise returned pointers equal to
   scratch and different from scratch; verify no extra count updates.
6. **Copy buffers and probes.** Introduce the storage/scoped-view interface
   and diagnostic hook. Cover reused and nested destinations, callback
   repointing, initialization failures, reader failures, destination-validator
   failures, and the old extern copy-buffer projection API.
7. **Add `--api lowstar` and complete frontend/runtime integration.**
   Extend the existing selector as specified in Section 3.12, retaining
   `legacy_lowstar` as the default. Update all API-policy branches,
   headers, macros, generated build rules, and packaging. Build standalone
   and batch-generated modules from clean output directories, including
   static primitives and handler-macro mode.
8. **Implement the full Low* differential suite.** Add
    `src/3d/tests/pulse-lowstar-diff-tests` to compare all existing Low* tests
    between `--api lowstar` and `--api legacy_lowstar`. Inventory the complete
    existing corpus and reuse its test inputs, C tests, callbacks, and client
    stream/copy-buffer implementations without backend-specific changes.
    Generate and compile each variant in an isolated output directory, then
    run it with equivalent initial state. Reuse existing differential-test
    infrastructure where appropriate, but do not limit coverage to its
    currently supported subset.

    Compare every exercised wrapper's return value and all specified
    outparameter values, including parsed size, action-populated output
    fields, and error information. Cover success and failure, including
    partial updates and preservation of initialized outputs on failure.
    Compare structured outputs field by field, not padding bytes; compare
    pointer outputs by their referent/offset within corresponding buffers,
    not process-specific addresses. Exclude only values genuinely
    unspecified by the legacy contract, with explicit justification.
    Matching process exit codes or acceptance/rejection alone is insufficient.

    Report mismatches with the test/input, wrapper, return value or
    outparameter field, and both observed values. Account explicitly for
    negative tests and their expected failure stage. Missing coverage,
    unexpected generation/compilation failures, and unsupported existing
    tests must not silently count as passes. Wire the suite into the
    repository's test targets and CI; completing all existing Low* tests is
    an acceptance gate for the new implementation.

The paths above describe this implementation stage. Section 4 subsequently
moves the converted corpus and this differential harness into the shared
test tree without changing their coverage or comparison requirements.

Acceptance criteria:

- Omitting `--api` selects the same implementation as
  `--api legacy_lowstar`; `--api pulse` selects native Pulse and
  `--api lowstar` selects the Low*-compatible Pulse implementation. Unknown
  values and the removed `--pulse` switch are rejected, and generated build
  commands preserve the selected mode.
- Existing Low* C client sources compile without Pulse-specific conditionals,
  extra stream primitives, or copy-buffer position fields.
- The suite in `src/3d/tests/pulse-lowstar-diff-tests` covers all existing
  Low* tests and establishes matching wrapper return values and specified
  outparameters between `--api lowstar` and `--api legacy_lowstar`, on both
  success and failure. Existing C tests and client implementations compile,
  link, and pass with the replacement generated output.
- Exact function-pointer assignments check public signatures; passing
  literal zero arguments is not a sufficient ABI check.
- Results agree on both packed kind and position, not merely success/failure.
- Native Pulse returns the aligned byte kinds with unchanged reason strings
  for existing named errors; semantic rejection/action guarantees still hold.
- Callback traces agree on order, code, reason, input view, and field start;
  probe diagnostics and enclosing action failures remain distinct.
- Large opaque streams work on 32-bit targets within the legacy 60-bit model;
  native Pulse retains its prior calling conventions and domain, with the
  explicitly documented error-number alignment.
- Separate invocations, nested validators, and distinct copy buffers cannot
  interfere through hidden cursor storage.
- The legacy public header contains no native status-name collisions or new
  `EverParseStreamGetPosition`, `EverParseStreamPos`,
  `EverParseStreamReadBytes`, or `EverParseFieldPtrAfterImpl` requirements.
- All generated internal dependencies are present in copied/packaged output;
  no test succeeds only because it sees the original generation directory.

The existing differential suite is reusable infrastructure, not proof of
these properties: its current wrapper-level comparisons do not observe the
packed positions, all callback details, or the extern/static ABI. The new
suite must provide the complete Low* corpus and return/outparameter
comparisons above, alongside the additional ABI and diagnostic checks in
this plan.

The largest uncertainties are the alias-aware raw-read specification,
scoped copy-buffer view extraction, and generated worker visibility. Resolve
those gates before broad migration. Failure of a visibility optimization is
not a reason to weaken the public contract; failure of a proof obligation is
not a reason to add an unchecked count conversion or an assumed position
accessor to the client API.

## 4. Move converted Low*-API tests to the shared test tree

After establishing `--api lowstar` compatibility in Section 3, move the
existing tests from `src/3d/tests` that exercise the supported Low* C API to
`share/everparse/tests/3d/lowstar`. Preserve their grammars, C tests,
callbacks, and client implementations; move the tests rather than maintain
a second source copy.

**Placement rule:** new or converted 3D tests belong under
`share/everparse/tests/3d`. Move the entire ordinary Low*-API corpus: no
Low*-only exception remains after Section 3's compatibility gate.
Only the legacy/lowstar differential harness stays in `src/3d/tests`, plus
the native-Pulse differential harness temporarily until Section 5.

Implementation items:

1. Inventory and move the converted top-level and subdirectory tests, their
   fixtures, client sources, and build rules to
   `share/everparse/tests/3d/lowstar`. Leave the existing
   `src/3d/tests/pulse-diff` harness for its separate migration in Section 5.
2. Make all ordinary targets in the migrated tree explicitly generate with
   `--api lowstar` by default, including batch, subdirectory, negative,
   wrapper, and generated-test targets. This is a test-build default, not a
   change to the CLI's global default of `--api legacy_lowstar`.
3. Retain an explicit `--api legacy_lowstar` build variant of the migrated
   corpus only for differential comparison with `--api lowstar`. Both
   variants must reuse the same source tests and client code, with isolated
   generated files and executables. Ordinary migrated test targets and CI
   must not silently build or fall back to the original Low* implementation.
4. Keep Section 3's `src/3d/tests/pulse-lowstar-diff-tests` harness in place.
   Update it to
   build both API variants from the new shared source location. Preserve
   its full return/outparameter comparisons and explicit coverage accounting.
5. Update parent Makefiles, subdirectory runners, relative includes, fixture
   paths, CI, packaging, cleanup, and documentation. Route ordinary Low*-API
   testing to the new tree, retain the differential harnesses
   in `src/3d/tests`, and make the new `lowstar` outputs available to
   the Pulse API comparison suite in Section 5.

**Completion gate:** the migrated corpus builds and runs by default with
`--api lowstar` from its new location, without depending on a stale source
copy or generated outputs under `src/3d/tests`. Its `legacy_lowstar` variant
is exercised through the differential suite only, and the return/outparameter
compatibility gate still passes. No ordinary tests remain in `src/3d/tests`;
new or converted tests are placed in the shared tree.

## 5. Move and adapt the existing Low*-Pulse differential tests

After the test-tree migration in Section 4, move the existing suite from
`src/3d/tests/pulse-diff` to
`share/everparse/tests/3d/pulse-lowstar-diff`. Replace its original Low*
implementation side (`--api legacy_lowstar` after step 2) with
`--api lowstar`; retain `--api pulse` on its native-Pulse side.

The migrated suite compares two public APIs of the Pulse implementation,
not the old Low* implementation against Pulse. It complements, rather than
replaces, the full legacy-implementation compatibility suite from Section 3:

| Suite | Compared modes | Purpose |
|---|---|---|
| `src/3d/tests/pulse-lowstar-diff-tests` | `lowstar` versus `legacy_lowstar` | Establish drop-in compatibility with all existing Low* tests, including wrapper returns and outparameters |
| `share/everparse/tests/3d/pulse-lowstar-diff` | `lowstar` versus `pulse` | Preserve the existing differential coverage across Low*-compatible and native Pulse APIs |

Implementation items:

1. Move the suite's Makefile, harness, driver generation, subdirectory runner,
   ABI checks, and documentation together. Update parent test targets,
   scripts, CI references, and relative paths to the new location; do not
   leave a second diverging copy in the old directory.
2. Generate the Low*-API side explicitly with `--api lowstar` and the native
   side with `--api pulse`. Update batch/subdirectory build dependencies,
   output-directory pairing, and defaults such as `LO_DIR` and `PU_DIR`.
   Obtain the Low*-API outputs from the migrated
   `share/everparse/tests/3d/lowstar` build targets.
   Keep the outputs isolated and ensure neither a missing option nor reused
   artifacts silently selects `legacy_lowstar`.
3. Retain the existing deterministic fuzzing, union-corpus replay, wrapper
   return/outparameter comparisons, copy-buffer-content comparisons, and
   callback diagnostics. Adapt backend-specific harness and ABI assumptions
   to the two selected APIs without weakening the comparisons or reducing
   the existing grammar/subdirectory coverage.
4. Update the README and documented invocation to the shared test tree.
   Make the migrated suite build its selected outputs on demand without
   requiring generated C from the legacy Low* implementation.

**Completion gate:** the suite runs from its new location against fresh
`--api lowstar` and `--api pulse` output, preserves its existing behavioral
coverage, and has no stale build references to `src/3d/tests/pulse-diff`.
Section 3's separate `lowstar`-versus-`legacy_lowstar` suite remains required
and unchanged in purpose.

## 6. Deeper alternative: refactor validators and actions

This preserves the prior direct-specialization proposal. Unlike Section 3,
it generalizes the shared result-and-position protocol itself, so typeclass
specialization can produce the Low* calling convention directly. It is an
alternative or possible subsequent refactor, not required to complete
`--api lowstar`. The error-kind alignment and CLI selection from Sections 1
and 2 apply to either design.

### 6.1. Shared-interface changes for direct specialization

#### A. Separate semantic outcomes from their representation

Introduce a small result-policy component, carried by `input_stream_inst` or
a companion dictionary.

| Operation or associated type | Purpose |
|---|---|
| `result_t`, `error_code_t` | Separate the validator answer from the code delivered to callbacks |
| Success/error constructors | Construct an answer at a particular cursor, rather than return a global success/error constant |
| `is_success`, `is_action_failure` | Classify outcomes without depending on numeric ordering |
| Error-code extraction and reason lookup | Decode a packed answer or a byte status appropriately |
| Cursor recovery from an answer and its input cursor | Support scalar-position results and stateful native cursors |
| Representation laws | Connect constructors, classifiers, and cursor recovery to the validator specification |

The native policy specializes to the byte codes aligned in Section 1. The
compatibility policy specializes to Low*'s packed `U64.t`, including action
failure = 5, constraint failure = 6, padding failure = 7, and internal probe
failure = 8.

Do not require a universal pure `get_position(result)` operation: a native
byte result contains no position. A suitable operation is conceptually
`cursor_after(input_cursor, result)`. It retains the native mutable
handle/origin, but extracts the low 60 bits for the legacy scalar cursor.
The stream's existing position-observation operation can then interpret that
cursor.

The validator contracts must retain their functional meaning:

- Success establishes the parser result and exact consumed suffix.
- A non-action validation failure establishes parser rejection.
- Action failure need not establish parser rejection.

Generalize the semantic classifications introduced in Section 1 to this
result policy. The original numeric inequality appears in
[the current contracts](lib/everparse/3d/EverParse3d.Actions.Base.fst#L85-L145).
Do not apply the rejection theorem indiscriminately to probe-diagnostic
codes.

#### B. Make cursor advancement explicit in the specifications

For direct specialization to the old ABI, consuming postconditions must
describe ownership at the resulting cursor, rather than invariably at the
incoming `sl_pos`.

The same applies to `read`, `skip`, `empty`, and truncation restoration.
Known-size operations can use an instance-specific `advance(cursor, count)`
in their postconditions: it leaves the native handle unchanged and advances
a legacy scalar. Readers can use the end established by prior validation as
a proof witness. If an implementation genuinely needs to return additional
runtime progress, prefer an inlined out-parameter over introducing a public
tuple-return ABI.

Truncation needs particular care: on return from a bounded child, restore
the parent view using the child's final cursor, while retaining the parent's
coordinate system. Reusing the original scalar cursor would lose all child
progress. The present
[truncate/untruncate interface](lib/everparse/3d/EverParse3d.InputStream.Base.fst#L302-L365)
works because both native instances keep the relevant cursor identity
unchanged.

Non-consuming validators need separate treatment. Their successful result
describes a prospective end, not actual stream consumption. A consuming
conversion commits that progress only on success. The current
[non-consuming type](lib/everparse/3d/EverParse3d.Actions.Base.fst#L104-L145)
and
[`validate_drop`](lib/everparse/3d/EverParse3d.Actions.Base.fst#L2353-L2389)
cannot be generalized by blindly threading `cursor_after` everywhere.

Preserve the native lookahead-reference implementation. For compatibility,
either specialize a small lookahead calling-convention abstraction to the
scalar-start/packed-result protocol, or put a verified adapter around the
shared internal lookahead implementation. Its exported signature must not
retain the extra reference. Failure positions must describe the actual
consumed position required by the Low* contract, not an uncommitted lookahead
offset.

#### C. Separate stream counts from host pointer sizes

Changing only the result type leaves `SZ.t` embedded in `has`, `has_at`,
`skip`, `empty`, and non-consuming offsets.

For full compatibility, use an associated count/offset type with the small
arithmetic interface these combinators need: native instances use `SizeT`,
legacy instances use `U64`. Conversion to `SizeT` belongs at actual array
accesses and scratch-buffer allocation, with bounds proofs. Leaf reads are
small, but an extern stream's total skipped or remaining length need not fit
a 32-bit `size_t`.

Enforce the 60-bit packed-position bound in legacy instances without imposing
it on native Pulse instances. Preserve the existing Low* buffer-domain bounds
too: a public `uint64_t` length parameter does not imply that its verified
buffer model supports arbitrary 64-bit arrays.

#### D. Abstract callback invocation, not just its typedef

Retain the monomorphic per-backend `error_handler_t` aliases. Replace or
generalize the fixed byte-code `error_handler_arrow_of_t` interface with an
invoke-handler operation that accepts the abstract error code and semantic
diagnostic information.

Native invocation emits today's argument list. Legacy invocation emits the
seven-argument Low* call, passing the decoded kind rather than the packed
result, and the saved field-start position rather than the failure/end
position.

Use this operation in both validator error wrappers and probe reporting.
The latter currently contains a literal `0uy`, independent of ordinary
validator-result handling:
[handle_probe_error](lib/everparse/3d/EverParse3d.ProbeActions.fst#L201-L234).
Preserve macro-handler mode as well as function-pointer mode. No runtime
closure or callback trampoline should be needed if dispatch specializes and
inlines as intended.

### 6.2. New instances

#### Legacy buffer

Use a byte-pointer base, `U64` length, scalar position, and packed results.
Most array-reading and splitting/joining proofs can be adapted from the
current buffer instance; cursor ownership and integer conversions change.
The public handler and copy-buffer projections match Low*.

#### Legacy extern

Use the actual named `EVERPARSE_INPUT_BUFFER` layout, with `len_t = unit` and
a scalar position. Maintain progress through the validator protocol rather
than asking the client for it. Bound checks and truncation operate on
`has_length/length` and the explicit position.

The old primitives are sufficient:

- `has_at(off, n)` can be implemented with a checked `off + n` and
  `EverParseHas`, or directly from a bounded view. It does not require a new
  client primitive.
- `empty` calls `EverParseEmpty` only for an unbounded view. A bounded view
  drains only its remaining bytes through `EverParseSkip`.
- `read` calls pointer-returning `EverParseRead` and applies the existing leaf
  reader to the returned pointer, not necessarily to `dst`.
- `field_ptr_after` and its setter variant use nullable `EverParsePeep`,
  updating the destination only on success. No `EverParseFieldPtrAfterImpl`
  or `EverParseNullPtr` dependency should leak into this API.

The hardest new stream proof is pointer-returning reads. The result can alias
the scratch buffer or storage owned by the stream. Its Pulse specification
must provide a temporary readable view and a way to restore ownership
afterwards; it must not assert disjoint full ownership of the result, scratch
buffer, and stream unconditionally. Existing
[ArrayPtr leaf readers](src/lowparse/pulse/LowParse.Pulse.ArrayPtr.Int.fst#L35-L60)
already accept fractional permissions, which helps. The current always-copy
implementation remains appropriate for native instances.

There is a documentation discrepancy to resolve in the compatibility
contract: the prose says `Peep` advances, but
[the Low* specification](src/3d/prelude/extern/EverParse3d.InputStream.Extern.Base.fsti#L98-L139)
requires no memory modification, and its action combinator does not advance
the cursor. Follow the actual Low* behavior, rather than silently introducing
consumption based on that prose.

#### Legacy static

Reuse legacy extern's proof development and differ in emitted linkage, as
today's header-generation machinery already supports.

#### Copy buffers

Decouple the persistent copy-buffer invariant from the cursor used for one
validation. Give the class operations to acquire a validation view/cursor and
restore its ownership afterwards, instead of requiring every implementation
to supply `pos_of`.

The native instance can implement those operations with the existing position
projection and reset. The legacy buffer instance starts a scalar cursor at
zero and uses only `EverParseStreamOf/Len`. The legacy extern instance uses
the old `EverParseStreamOf` returning an `EVERPARSE_INPUT_BUFFER`; its length
component erases.

Update `copy_buffer_state`, `probe_then_validate`, and probe diagnostics
together. Keep the current state-dictionary disjointness mechanism and probe
callback signatures. The frontend's buffer-only probe restriction must become
capability-based if full Low* extern/probe compatibility is included; it is
currently hard-coded in
[InterpreterTarget](src/3d/InterpreterTarget.fst#L1247-L1283).

### 6.3. Combinator changes and preserved code

Most parsing algorithms and pure sequence lemmas can remain shared. The
necessary edits are systematic, but more substantial than replacing equality
tests.

| Combinator family | Required change |
|---|---|
| `ret`, unit, impossible, leaf checks | Construct results at the appropriate position; success is not always zero |
| Pair/dependent pair/filter | Thread resulting cursors; preserve child failures; distinguish validated lookahead from consumed input |
| Success/dependent actions | Keep actions returning `bool` or their existing value type; convert action failure into a validator result at the post-validation position |
| Lists, strings, list-up-to | Track final cursor and semantic result classification in loop invariants |
| `t_at_most`, `all_bytes` | Account for the bytes drained by `empty`; do not discard its count |
| `t_exact`, bounded lists | Preserve child error positions and construct padding/length errors at the correct cursor |
| Error/probe wrappers | Invoke the instance's diagnostic operation and interpret results through the policy |

For example, current list loops initialize `res` to success and update it
only on failure. With packed results, leaving that structure unchanged would
return the initial position after a successful list. They must track progress
or construct success from the final cursor. Likewise,
[`validate_t_at_most`](lib/everparse/3d/EverParse3d.Actions.Base.fst#L1126-L1190)
must return the position after draining the remainder, not the child's
successful end.

The pure parsers, kinds, most interpreter structure, state dictionaries,
external-action interfaces, and leaf integer readers need no conceptual
redesign.

### 6.4. Implementation sequence and acceptance criteria

1. **Reuse the compatibility target.** Retain the actual Low* prototypes,
   typedef layouts, constants, and callback behavior from Section 3,
   including non-entrypoint/non-consuming validators. Keep native Pulse as a
   separate API policy with the aligned error kinds from Section 1.
2. **Prototype the representation boundary first.** Extract a leaf validator,
   a two-field validator, a non-consuming validator, and a callback invocation
   with native and legacy policies. Establish scalar results, unit-argument
   erasure, named stream structs, and handler typedefs before migrating the
   large combinator file.
3. **Generalize shared contracts and combinators under native instances
   first.** Then add legacy buffer, followed by legacy extern/static and their
   pointer-read proof. This separates regressions in the shared implementation
   from new-instance problems.
4. **Wire every generated surface.** Update instance selection in
   `Options`/`InterpreterTarget`; wrapper calls, parsed-size recovery, and
   constants in `Target`; direct-validator calls in `Z3TestGen`; and typedef
   preservation, bundles, and shipped headers in `Batch.ml` and
   `lib/everparse/3d/krml/header.Makefile`. Preserve the implementation/ABI
   distinction established by the `--api` selector.
5. **Establish both compatibility and non-regression.** Compile unchanged
   Low* clients against legacy Pulse with exact function-pointer types and
   struct-layout checks. Compare packed results, callback kinds/start
   positions, consumed lengths, output actions, and probes, not just
   accept/reject. Exercise nonzero starts, partial failures, bounded draining,
   repeated stream validations, both `Read` return-pointer cases, failed
   `Peep`, nested/reused copy buffers, and macro handlers. Include 32-bit count
   boundaries. Reuse Section 3's full Low* differential suite and require the
   same wrapper return/outparameter compatibility.

The original `pulse-diff` suite, migrated in Section 5, alone is insufficient
to establish legacy-implementation compatibility. In its current form it excludes
extern/static streams and does not compare error positions, while its ABI
check intentionally tolerates the current signature differences.
See [its coverage notes](src/3d/tests/pulse-diff/README.md#L89-L153) and
[abi_check.c](src/3d/tests/pulse-diff/abi_check.c).

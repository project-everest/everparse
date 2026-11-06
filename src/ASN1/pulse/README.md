# Verified C validators for ASN.1 DER (Pulse + Custard)

This directory implements, in Pulse, validators for the pure F\* ASN.1 DER
specification of `..` (`ASN1.Spec.Interpreter`), and extracts them to C
with Custard (F\*'s direct-to-C backend; no KaRaMeL).

A validator for a schema `k` checks that a byte buffer starts with a value
of `asn1_as_parser k` and returns the number of bytes consumed; it is
proven to succeed exactly when the spec parser succeeds, with the same
consumed length (`LowParse.Pulse.Base.validator`).

## Coverage

Every schema construct of the specification: all universal terminal types,
restricted terminals (`asn1_restriction`), PREFIXED (EXPLICIT tags),
SEQUENCE (OPTIONAL, DEFAULT: default values are `asn1_key_lit` literals,
so a present component encoding its default is rejected by the same
comparison as ANY DEFINED BY keys, for every terminal kind supported as a
key, restricted or not; `ASN1.Pulse.DefaultLit`), SEQUENCE OF, SET OF
(DER ordering), SET (at most 64 components), CHOICE, ANY, ANY DEFINED BY
(with or without a prefix, with or without a fallback; keys of any terminal
type except RELATIVE-OID: OBJECT IDENTIFIER keys are
compared subidentifier by subidentifier, tagged (EXPLICIT) keys structurally
by checking the inner identifier and DER length and recursing on the
inner key (`ASN1.Pulse.AdbPrefixed`), other keys byte-for-byte against
their DER content encoding, computed at extraction from the list-based key
literals `asn1_key_lit` of `ASN1.Base`; INTEGER key literals are the
minimal two's complement content bytes themselves, `asn1_int_lit`, so
keys of any size are supported, built with `ASN1.Syntax.mk_int_lit` when
the refinement is not proved automatically), and the
presentation types (EXTERNAL, EMBEDDED PDV, CHARACTER
STRING). The interpreter rejects unsupported schemas statically
(`supported_k`), which the extraction roots discharge by normalization.

## Zero-copy parsers and right-to-left writers

Beyond validators, the directory has parsers and serializers over a
low-level representation `asn1_impl_t k` of the values of a schema `k`
(`ASN1.Pulse.Rel`): machine integers, booleans, slices pointing into the
input for strings and big integers, tuples/`option`/`either` for
SEQUENCE, SET and CHOICE, and LowParse mixed lists
(`LowParse.PulseParse.Iterator.*`) for SEQUENCE OF and SET OF. The relation
`asn1_rel k pm x' x` ties a low-level value `x'` to a spec value `x`,
holding fractional permission `pm` on the input bytes it borrows.

* **Parsers** (`ASN1.Pulse.Parser`, `parse_k`): from a validated input
  (`pts_to_parsed`), return `x'` with `asn1_rel k pm x' x`, where `x` is
  the value parsed by `asn1_as_parser k`; no copy, no allocation (SEQUENCE
  OF and SET OF are returned lazily, as a count and the payload). Supported
  schemas: `psupported_k`. SET components may be declared in any order
  (`ASN1.Pulse.ParseSetAny`): each element, read in encoding order, is
  dispatched by its tag to the slot of its component in a tuple of
  `option`s, and the empty slots are then filled with absent/default
  values; the result follows the declaration order.
* **Raw writers** (`ASN1.Pulse.RawWriter`, `raw_write_k`): right-to-left.
  The raw relation `raw_rel k pm x' y` (`ASN1.Pulse.RawRel`) relates a
  low-level value `x': asn1_impl_t k` to the bytes `y` that its fields
  spell out, with no semantic constraint: any slice is accepted as string,
  time, OID, ANY or big INTEGER contents, any `unused` byte and slice as a
  BIT STRING, any `int64` as an INTEGER. Given an output slice and a
  position `pos`, the raw writer writes those bytes just left of `pos` and
  moves `pos` to their start, or returns `false` (output too small)
  leaving the bytes right of `pos` untouched
  (`LowParse.Pulse.R2L.r2l_writer_f`). Writing from the right lets every
  TLV length be written after its contents, so no size is computed ahead.
  Schemas must satisfy `raw_ok k` (`supported_k` and `Conformance.wf`).
  The raw writer sorts while writing, in the style of the CDDL "table"
  map groups (`ASN1.Pulse.SortedInsert`): right after writing a SET
  component or a SET OF element, it inserts it in place, by rotation, into
  the already written and sorted ones, by tag (X.690 10.3) or by encoding
  (X.690 11.6). So neither the order of the SET components in the schema
  nor the order of the SET OF elements in the input matter (duplicate SET
  OF elements are kept). The insertion is total (a malformed frame just
  stops the scan). What remains a precondition: `Serialized` chunks of
  SEQUENCE OF / SET OF must be a sequence of TLVs (`p_raw`). For ANY
  DEFINED BY, the raw relation is the choice, in order, of each key
  literal (written as a constant TLV, `WriteAdb.raw_key_enc`, unrolled at
  extraction time from the literal, with no scratch buffer) followed by
  its payload, then of the fallback.

* **Just-in-time writers** (`ASN1.Pulse.JitWriter`, `jit_writer`): same
  input as the raw writers, but they also check, while writing, that the
  written bytes are the DER encoding of a value of `k`, and return
  `JIT_OK`, `JIT_NO_SPACE` (the encoding does not fit) or `JIT_INVALID`
  (it is not the DER encoding of a value of `k`), so all constraints of
  `k` become runtime checks. Where validity is not compositional (because
  of ANY), the check is made over the smallest enclosing content, which is
  then written again by the raw writer and validated within its own bounds
  (`jit_fix`, `jit_local`), so the top-level JIT writer never returns
  `JIT_RETRY`. Proofs: `ASN1.Pulse.JitWriter.Lemmas`.

* **JIT writers of raw values** (`ASN1.Pulse.RawJitWriter`,
  `jit_write_raw`): the same JIT writer, seen as a writer of raw values
  `y: ASN1.Spec.Raw.asn1_raw_t k` (`asn1_raw_rel k pm x' y`,
  `ASN1.Pulse.RawValueRel`): `JIT_OK` iff `check_ser k () y == Some x` and
  `Ser.asn1_enc k x` fits, which is then written; `JIT_INVALID` implies
  `check_ser k () y == None`. It runs `jit_writer` on the raw bytes
  `rb k y` of `y` (`ASN1.Pulse.RawBytes`), through a ghost bridge between
  the two relations (`ASN1.Pulse.RawBridge`).
  On impl descriptors (`d: adesc k t`, `ASN1.Pulse.Rel`),
  `jit_write_raw_d` takes the value-level relation
  `ASN1.Pulse.RawVRel.raw_varel d pm x' y`, which relates the C value `x'`
  to the raw value `y` leaf by leaf and never mentions bytes: the caller
  does not reason about encodings. A ghost bridge
  (`ASN1.Pulse.RawVBridge`) splits it into the byte-level relation that
  `jit_writer_d` needs (`jit_write_raw_bytes_d` keeps the byte-level
  interface).

* **Typed writers** (`ASN1.Pulse.TypedWriter`, `write_typed_d`): take the
  typed relation `arel false d pm x' v` with `v: asn1_t k`, and
  `encodable k v`, and never return `JIT_INVALID`: `JIT_OK` writes
  `Ser.asn1_enc k v`. They convert `arel false` to `raw_varel` and back
  with a ghost conversion (`ASN1.Pulse.RawVConv.arel_to_raw`, with
  `forget k v` as the raw value). Every parsed value is encodable, and its
  encoding is the parsed input (`parsed_encodable_d`), so parsing then
  writing back round-trips (`ASN1.Pulse.NamedTest.roundtrip_rec`).

* **KEEP-BYTES** (`D_KEEP d wf : adesc k (kept t)`, `ASN1.Pulse.Rel`): a
  value `{ kval; kraw }` where `kraw` is optionally the bytes of the DER
  encoding of `kval` (e.g. to check a signature over a `tbsCertificate`).
  The relation `arel kb d pm x' v` takes a Boolean `kb`: with `true`, the
  `kraw` of every KEEP-BYTES node is `Some` of a slice holding exactly
  `Ser.asn1_enc k v` (with permission); with `false`, `kraw` is ignored.
  Parsers ensure `arel true` (`parse_d`), writers require `arel false`
  (raw writers ignore `kraw` too), so callers of writers never reason
  about bytes, and stale bytes are never written. The ghost
  `ASN1.Pulse.RelKeep.to_writer d pm x' v` turns `arel true` into
  `arel false` together with a trade back to `arel true`. Its frame is
  the pure fact `kept_a d x'` (every `kraw` is `Some`), so it releases no
  permission (`weaken` / `restore`). Tests: `ASN1.Pulse.NamedTest`
  (`Outer`, `roundtrip_outer`) and `test/named_test.c`.

`make test-parse` runs the parsers extracted from `ASN1.Pulse.ParseTest`
on hand-written encodings (`test/parse_test.c`). `make test-raw-write`
runs the JIT writers extracted from `ASN1.Pulse.RawWriteTest`
(`jit_<name>` and `jit_raw_<name>`) on values built in C, including
invalid strings, BIT STRING padding, non-minimal INTEGERs, bad ANY
slices, unsorted SET OF elements, a SET declared in non-canonical order,
and ANY DEFINED BY values (known keys in the fallback, bad payloads)
(`test/raw_write_test.c`), checking that they succeed exactly on valid
values, with the DER bytes, and return `JIT_NO_SPACE` when the buffer is
one byte short.

## Layout

| Module | Contents |
| --- | --- |
| `ASN1.Pulse.Identifier`, `ASN1.Pulse.ILC` | identifier and length readers, TLV framing |
| `ASN1.Pulse.Terminal`, `ASN1.Pulse.Checkers`, `ASN1.Pulse.OID` | terminal contents |
| `ASN1.Pulse.Restrict` | restricted terminals |
| `ASN1.Pulse.Sequence`, `ASN1.Pulse.SeqAny` | SEQUENCE items, and the prefix of ANY DEFINED BY |
| `ASN1.Pulse.Constructed`, `ASN1.Pulse.SetOf`, `ASN1.Pulse.SetComp` | SEQUENCE OF, CHOICE, SET OF, SET |
| `ASN1.Pulse.Any`, `ASN1.Pulse.AnyDefinedBy` | ANY, ANY DEFINED BY |
| `ASN1.Pulse.Interpreter` | the interpreter `validate_k` over schemas |
| `ASN1.Pulse.Rel`, `ASN1.Pulse.RelShare` | low-level value types and relations; generic share/gather combinators |
| `ASN1.Pulse.Parse*`, `ASN1.Pulse.Parser` | zero-copy parser combinators and the interpreter `parse_k` |
| `ASN1.Pulse.WriteLeaf`, `ASN1.Pulse.WriteComb`, `ASN1.Pulse.WriteAdb` | right-to-left writer building blocks (ANY DEFINED BY keys: `WriteAdb`) |
| `ASN1.Pulse.RawRel`, `ASN1.Pulse.RawWriter` | raw relations, and raw writers `raw_write_k` |
| `ASN1.Pulse.JitWriter.*`, `ASN1.Pulse.JitTerminal`, `ASN1.Pulse.JitFrame`, `ASN1.Pulse.JitAdb*` | just-in-time writers `jit_writer` (check while writing) |
| `ASN1.Pulse.RawValueRel`, `ASN1.Pulse.RawBytes`, `ASN1.Pulse.RawBridge`, `ASN1.Pulse.RawJitWriter` | raw value relation `asn1_raw_rel`, and the JIT writer of raw values `jit_write_raw` |
| `ASN1.Pulse.RawVRel`, `ASN1.Pulse.RawVBridge` | value-level relation of writers on descriptors `raw_varel`, and its bridge to bytes |
| `ASN1.Pulse.RawVConv`, `ASN1.Pulse.TypedWriter` | from the typed relation `arel false` to `raw_varel` (`arel_to_raw`), and typed writers `write_typed_d` |
| `ASN1.Pulse.RelKeep` | KEEP-BYTES: from the parser relation `arel true` to the writer relation `arel false` and back (`weaken`, `restore`, `to_writer`) |
| `ASN1.Pulse.SortedInsert` | on-the-fly insertion sort of SET components and SET OF elements for the raw writers |
| `ASN1.Pulse.ParseTest`, `ASN1.Pulse.RawWriteTest` | extraction roots for parser and writer tests |
| `ASN1.Pulse.DiffTest.*` | extraction roots for the difftest schemas (`../difftest`) |
| `ASN1.Pulse.X509` | extraction roots for X.509 certificates and CRLs |

Generic parts live in LowParse (`lib/everparse/lowparse`), e.g.
`LowParse.PulseParse.VReader` (validate-and-read combinators) and
`LowParse.Pulse.Lex` (lexicographic comparison, for SET OF).

## Code shape

* **One C function per schema node.** The interpreter is not inlined:
  its schema arguments carry `[@@@FStar.Attributes.monomorphize]`, so
  Custard emits one specialization of each interpreter function per
  distinct schema value it is applied to (identical sub-schemas share one
  C function).
* **Bounded stack.** No C function is recursive; the call depth is bounded
  by the depth of the schema. ANY values, whose nesting depth is
  controlled by the input, are validated by a loop with constant stack
  (`ASN1.Pulse.Any`, `validate_rec_vlgen`). No heap allocation.
* Extraction roots are plain F\* `let`s with `normalize_for_extraction`
  (see `ASN1.Pulse.X509`), unfolding the schema definitions.

Custard pitfalls met in this code (comments in `ASN1.Pulse.Interpreter`):

* Custard F\* 4cb038ec6f misclassifies the binders that a specialized
  function gets from the lambdas of its body (wrong parameters are
  dropped), so every monomorphized validator takes the validator arguments
  explicitly and returns `vres ...`.
* In a specialization, `let C x = v` and `match v with C x -> ...` on a
  monomorphized value do not reduce: use projectors (`C?.x v`).
* A monomorphized argument must not be a closure whose type mentions the
  schema (Error 368): rebuild the closure in the callee instead.
* A top-level record of functions (such as `ASN1.Pulse.Rel.ml_ops`) is
  extracted as a zero-initialized static, without its initializer: mark it
  `inline_for_extraction`.

## Build and test

```
make            # verify
make test       # difftest vectors (committed verdicts)
make test-oracle  # difftest vectors and mutations, against the F* spec runner
make test-corpus  # X.509 and CRL corpora (../evaluation/data), against the spec runner
make test-deep-any  # ANY nested 4000 deep, under a 64 KiB stack limit
make stack-check    # no recursion, and worst-case stack of the X.509/CRL validators
make test-parse     # zero-copy parsers on hand-written encodings
make test-raw-write  # JIT writers: OK, INVALID and NO_SPACE cases
```

`make -C .. test` runs all of these but `test-raw-write`, unless
`NO_PULSE` is set. C files
go to `_output/`.

Reference numbers (one core, x86-64): extracting `ASN1.Pulse.X509`
(certificates and CRLs) takes about 5 minutes and yields 959 KB of C
(62 KB of code at -O1); the X.509 corpus (14620 files) and the CRL
corpus (6154 files) agree with the spec runner on every file; the
worst-case stack is 16 KB at -O0 (4 KB at -O1) for a certificate;
validating the whole X.509 corpus (14.6 MB) takes about 0.1 s, file I/O
included.

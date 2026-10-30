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
* **Writers** (`ASN1.Pulse.Writer`, `write_k`): right-to-left. Given
  `asn1_rel k pm x' x`, an output slice and a position `pos`, write the
  encoding just left of `pos` and move `pos` to its start, or return
  `false` (output too small) leaving the bytes right of `pos` untouched
  (`LowParse.Pulse.R2L.r2l_writer_f`). Writing from the right lets every
  TLV length be written after its contents, so no size is computed ahead.
  The bytes written are `asn1_value_enc (to_value k x)`, which is the DER
  encoding `serialize (asn1_serializer k) x` of `ASN1.Spec.Serializer`.
  Supported schemas: `RS.wsupported_k` (all but ANY DEFINED BY; SET
  components in canonical order) and well-formed (`Conformance.wf`).

* **Checked writers** (`ASN1.Pulse.CheckedWriter`, `check_write_k`): the
  writers above require `asn1_rel k pm x' x`, i.e. that the value already
  satisfies all the constraints of `k`. A checked writer instead takes a
  value of the *relaxed* schema `relax k` (`ASN1.Spec.Relax`), which has
  the same low-level type `asn1_impl_t k` but drops the constraints that
  can be checked on the encoding: value restrictions, DEFAULT (becomes
  OPTIONAL: a present value equal to the default is rejected), SIZE
  (1..MAX), SET OF order, small INTEGER bounds (relaxed to 8 bytes), and
  the contents of non-universally tagged strings, times and OIDs (relaxed
  to OCTET STRING). It writes with `write_k (relax k)`, validates the
  written bytes with `validate_k k`, and returns `CW_OK` (the bytes are
  the DER encoding of a value of `k`, and they are exactly the relaxed
  encoding of the input), `CW_NO_SPACE` (the relaxed encoding does not fit)
  or `CW_INVALID` (it fits, but no value of `k` encodes to it). The
  specification `cw_post` is complete: `CW_OK` iff the encoding fits and
  conforms (relying on the injectivity of `to_value`,
  `ASN1.Spec.ToValue.Inj`). Schemas must satisfy `checked_ok k`, proved
  per schema by normalization. What remains a precondition (part of
  `asn1_rel (relax k)`) is what the relaxed schema still enforces: the
  contents of universally tagged strings, times and OIDs, BIT STRING
  padding, minimal and out-of-`int64` big INTEGER slices, ANY slices
  holding one TLV, and `Serialized` chunks of SEQUENCE OF / SET OF valid
  under the relaxed element schema. Writing and validating are two passes
  over the output.

* **Checked raw writers** (`ASN1.Pulse.RawWriter`, `check_write_raw_k`):
  they remove those remaining preconditions, using the same
  `asn1_impl_t k` input type. The raw relation `raw_rel k pm x' y`
  (`ASN1.Pulse.RawRel`) relates a low-level value to the bytes `y` that
  its fields spell out, with no semantic constraint: any slice is accepted
  as string, time, OID, ANY or big INTEGER contents, any `unused` byte and
  slice as a BIT STRING, any `int64` as an INTEGER. The raw writer
  `raw_write_k` writes those bytes right to left, then `validate_k k`
  checks them, with the same `cw_post` as the checked writers, so all
  constraints of `k` become runtime checks (`CW_INVALID`). Schemas must
  satisfy `raw_ok k` (`supported_k` and `Conformance.wf`). The raw
  writer sorts while writing, in the style of the CDDL "table" map
  groups (`ASN1.Pulse.SortedInsert`): right after writing a SET component
  or a SET OF element, it inserts it in place, by rotation, into the
  already written and sorted ones, by tag (X.690 10.3) or by encoding
  (X.690 11.6). So neither the order of the SET components in the schema
  nor the order of the SET OF elements in the input matter (duplicate SET
  OF elements are kept). The insertion is total (a malformed frame just
  stops the scan) and sortedness is never proven: the final validation
  checks it. What remains a precondition: `Serialized` chunks of
  SEQUENCE OF / SET OF must be a sequence of TLVs (`p_raw`). ANY DEFINED
  BY has no raw representation.

* **Just-in-time checked raw writers** (`ASN1.Pulse.JitWriter`,
  `check_write_jit_k`): same input, same `cw_post`, but the checks are
  made while writing, instead of in a final validation pass over the
  whole output. The JIT writer `jit_write_k` writes right to left like
  `raw_write_k` and either succeeds, having proven that the chunk it wrote
  is accepted by the parser of its schema (it parses and consumes it all),
  or gives up. The TLV framing of SEQUENCEs and PREFIXED types and the
  alternatives of CHOICEs are correct by construction; SEQUENCE
  components only need a runtime check of the identifier of the first
  written component (it must belong to the component just written if
  present, and must not if absent, which rules out DEFAULT values
  written out). All other chunks (terminals, SET, SEQUENCE OF, SET OF,
  ANY, DEFAULT components) are validated locally, right after being
  written, within their own bounds (so, still in the cache). Each byte is
  validated at most once. If the JIT writer gives up (invalid value, or
  not enough space), `check_write_jit_k` falls back to `check_write_raw_k`
  to tell `CW_INVALID` from `CW_NO_SPACE`, so the fallback only costs on
  failure paths. Proofs: `ASN1.Pulse.JitWriter.Lemmas`.

`make test-parse` and `make test-write` run the parsers and writers
extracted from `ASN1.Pulse.ParseTest` on hand-written encodings
(`test/parse_test.c`, `test/write_test.c`: parse/write round trips).
`make test-checked-write` runs the checked writers extracted from
`ASN1.Pulse.CheckedWriteTest` on values built in C
(`test/checked_write_test.c`). `make test-raw-write` runs the checked
raw writers extracted from `ASN1.Pulse.RawWriteTest` on values built in C,
including invalid strings, BIT STRING padding, non-minimal INTEGERs, bad
ANY slices, unsorted SET OF elements and a SET declared in non-canonical
order (`test/raw_write_test.c`); each case is also run on the JIT
variants, checking that the JIT writer alone succeeds exactly on valid
values.

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
| `ASN1.Pulse.Rel`, `ASN1.Pulse.RelShare` | low-level value types and relations; share/gather; writer-supported schemas |
| `ASN1.Pulse.Parse*`, `ASN1.Pulse.Parser` | zero-copy parser combinators and the interpreter `parse_k` |
| `ASN1.Pulse.WriteLeaf`, `ASN1.Pulse.WriteComb`, `ASN1.Pulse.Writer.Lemmas`, `ASN1.Pulse.Writer` | right-to-left writers, and the interpreter `write_k` |
| `ASN1.Pulse.CheckedWriter` | checked writers `check_write_k` (relaxed write, then validate) |
| `ASN1.Pulse.RawRel`, `ASN1.Pulse.RawWriter` | raw relations, and checked raw writers `check_write_raw_k` (raw write, then validate) |
| `ASN1.Pulse.JitWriter.Lemmas`, `ASN1.Pulse.JitWriter` | just-in-time checked raw writers `check_write_jit_k` (check while writing) |
| `ASN1.Pulse.SortedInsert` | on-the-fly insertion sort of SET components and SET OF elements for the raw writers |
| `ASN1.Pulse.ParseTest`, `ASN1.Pulse.CheckedWriteTest`, `ASN1.Pulse.RawWriteTest` | extraction roots for parser and writer tests |
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
make test-write     # right-to-left writers: parse/write round trips
make test-checked-write  # checked writers: OK, INVALID and NO_SPACE cases
make test-raw-write      # checked raw writers: OK, INVALID and NO_SPACE cases
```

`make -C .. test` runs all of these, unless `NO_PULSE` is set. C files
go to `_output/`.

Reference numbers (one core, x86-64): extracting `ASN1.Pulse.X509`
(certificates and CRLs) takes about 5 minutes and yields 959 KB of C
(62 KB of code at -O1); the X.509 corpus (14620 files) and the CRL
corpus (6154 files) agree with the spec runner on every file; the
worst-case stack is 16 KB at -O0 (4 KB at -O1) for a certificate;
validating the whole X.509 corpus (14.6 MB) takes about 0.1 s, file I/O
included.

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
SEQUENCE (OPTIONAL, DEFAULT for BOOLEAN and NULL), SEQUENCE OF, SET OF
(DER ordering), SET (at most 64 components), CHOICE, ANY, ANY DEFINED BY
(with or without a prefix, with or without a fallback; keys of any terminal
type except INTEGER, RELATIVE-OID and tagged terminals: OBJECT
IDENTIFIER keys are compared subidentifier by subidentifier, other keys
byte-for-byte against their DER content encoding, computed at extraction
from the list-based key literals `asn1_key_lit` of `ASN1.Base`), and the
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
  schemas: `psupported_k`.
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

`make test-parse` and `make test-write` run the parsers and writers
extracted from `ASN1.Pulse.ParseTest` on hand-written encodings
(`test/parse_test.c`, `test/write_test.c`: parse/write round trips).

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
| `ASN1.Pulse.ParseTest` | extraction roots for parser and writer tests |
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

# everparse-asn1: from an ASN.1 module to verified C

`everparse-asn1` takes an ASN.1 module and generates, for each root type, a C
struct/union type with a validator, a zero-copy parser, and a right-to-left
DER writer. The parser and writer are verified against the pure F\* ASN.1 DER
specification (`..`). It works like the CDDL front end of EverParse:

1. Parse the `.asn` files, resolve type and value references (across
   IMPORTS), and elaborate tags.
2. Generate two F\* modules:
   * `M.fst`: the schemas (`k_T : asn1_k`) as `ASN1.Syntax` terms. Their
     well-formedness, including the absence of tag ambiguity in SEQUENCE,
     SET and CHOICE, is proved by the tactics of `ASN1.Syntax`
     (`seq_tac`, `set_tac`, `wf_tac`).
   * `M.Impl.fst`: one C type per named SEQUENCE, SET, CHOICE and OPTIONAL
     component, and an impl descriptor `d_T : adesc k_T t_T` that ties each
     C type to its schema (`ASN1.Pulse.Rel`). The roots `validate_T`,
     `parse_T`, `write_T` and `write_T_typed` instantiate the generic Pulse interpreters
     of `../pulse` with these descriptors.
3. Verify both modules with F\*, then extract `M.Impl` to `M.c`/`M.h` with
   Custard, F\*'s direct-to-C backend (no KaRaMeL).
4. Compile `M.c` (`cc -c`) as a sanity check.

## Building and running

Prerequisites: OCaml with `dune` (e.g. the opam switch of EverParse), F\*
built in `opt/FStar`, and the verified ASN.1 Pulse library
(`make -C ../pulse verify`).

```
make build      # ocaml/_build/default/everparse-asn1/Main.exe
make test       # test-small and test-x509lite (C tests), and test-golden
```

```
Main.exe [--odir DIR] [--mname NAME] [--root A,B,...] [--keep_bytes A,B,...] [--lax_size_of] [--fstar_only] [--skip_compilation] main.asn [imported.asn ...]
```

The first file is the main module: its types are generated, with those of
the other files that it uses (directly or not) through IMPORTS. Every
imported module must be given on the command line.

* `--odir`: the output directory (default `.`; created if missing).
* `--mname`: the F\* module name (default: the ASN.1 module name).
* `--root`: the types to generate C functions for (default: the types
  that no other type uses).
* `--keep_bytes`: the types whose parsed values keep their bytes (see
  KEEP-BYTES below). A line `--#KEEP-BYTES A B ...` in the `.asn` file has
  the same effect.
* `--lax_size_of`: accept `SIZE (lo..hi)` and `SIZE (n)` on SEQUENCE OF /
  SET OF, but only check that the list is nonempty when `lo >= 1` (the
  library only supports `SIZE (1..MAX)`). The validators then accept more
  values than the schema. RFC 5280 uses such bounds in its ORAddress types,
  e.g. `SIZE (1..ub-domain-defined-attributes)`.
* `--fstar_only`: generate the F\* modules only.
* `--skip_compilation`: do not run `cc` on the generated C.

`EVERPARSE_HOME` is the EverParse root; by default it is found by
searching upward from the executable. `FSTAR_EXE` defaults to
`$EVERPARSE_HOME/opt/FStar/out/bin/fstar.exe`, and `CC` to `cc`.
Extraction can take several minutes per schema.

## Generated C API

For each root type `T` of a module `M`:

```c
void custard_init_globals(void);  /* call once before anything else */
bool validate_T(Pulse_Lib_Slice_slice__uint8 input, size_t *offset);
T    parse_T(Pulse_Lib_Slice_slice__uint8 validated_input);
ASN1_Pulse_JitWriter_jit_result
     write_T(T x, Pulse_Lib_Slice_slice__uint8 out, size_t *pos);
ASN1_Pulse_JitWriter_jit_result
     write_T_typed(T x, Pulse_Lib_Slice_slice__uint8 out, size_t *pos);
```

* `validate_T` succeeds exactly when the spec parser succeeds. It then
  advances `*offset` by the number of bytes consumed.
* `parse_T` runs on validated input only and copies nothing. Strings, big
  INTEGERs, OIDs and similar values are slices into the input.
* `write_T` writes right to left, ending at `*pos`, and moves `*pos`
  back to the start of the encoding. It returns:
  * `JIT_OK` when `x` is encodable;
  * `JIT_INVALID` when `x` breaks a constraint of the schema (a value
    outside a range or SIZE, an undeclared ENUMERATED value, and so on);
  * `JIT_NO_SPACE` when `x` is encodable but the buffer is too small.

  A DEFAULT component that is present with its default value is omitted
  from the output, as DER requires.

  In F\*, the precondition of `write_T` is the value-level relation
  `ASN1.Pulse.RawVRel.raw_varel d_T pm x y` between `x` and a ghost raw
  value `y: asn1_raw_t k_T`. It never mentions bytes, so a verified
  caller relates its C values to raw values without reasoning about
  encodings. (Per-type introduction lemmas for this relation are not
  generated yet: a caller unfolds `raw_varel d_T` itself.)
* `write_T_typed` is the same writer, with the typed relation
  `arel false d_T pm x v` (with `v: asn1_t k_T`) and `encodable k_T v` as
  its F\* precondition. It never returns `JIT_INVALID`, and `JIT_OK`
  writes the encoding of `v`. Its C code is that of `write_T`.
* `parse_T` ensures `arel true d_T pm x v`. The Boolean says whether the
  values of KEEP-BYTES types carry their bytes: `true` for parsers, `false`
  for writers, which never need bytes. The ghost
  `ASN1.Pulse.RelKeep.to_writer d_T pm x v` turns `arel true` into
  `arel false`, with a trade back to `arel true`. So a parsed value can
  be written back: every value returned by `parse_T` is encodable
  (`ASN1.Pulse.TypedWriter.parsed_encodable_d`), and writing it yields
  the parsed bytes. Without KEEP-BYTES types, `arel true` and `arel false`
  coincide.

### KEEP-BYTES

`--#KEEP-BYTES T` (or `--keep_bytes T`) makes every use of `T`, as well as
`parse_T`, `write_T` and `write_T_typed` if `T` is a root, use the C type

```c
typedef struct { T value; T_raw raw; } T_kept;
```

where `raw` is tagged `M_IMPL_T_RAW_ABSENT` / `M_IMPL_T_RAW_PRESENT`
(member `T_raw_present`, a slice). Parsers always set `raw` to the bytes
of the DER encoding of `value` in the input (zero-copy). This is useful to
check a signature over a sub-structure, such as the `tbsCertificate` of an
X.509 certificate. Writers ignore `raw`: a caller can set it ABSENT, and
stale bytes are never written. In F\*, `d_T` is
`D_VIEW (D_KEEP dbase_T wf_T) ...`. The generated `to_writer_T` is
`to_writer d_T`, specialized. Limitations: KEEP-BYTES applies to whole
types, not to single components. It is lost at IMPLICIT tags on `T` (they
reuse the content of `T`, not its descriptor). It is rejected on a CHOICE
used untagged as an alternative of another CHOICE.

Type naming:

* SEQUENCE and SET map to a struct `T` with one field per component.
  Anonymous nested types are named after their path, e.g. `Msg_extra`.
* CHOICE maps to a tagged union `T`. Its tags are `M_IMPL_T_ALT`, its
  union members `T_alt`, and nested CHOICEs are not flattened.
* An OPTIONAL or DEFAULT component `f` of `T` gets a tagged type with
  tags `M_IMPL_T_F_ABSENT` / `M_IMPL_T_F_PRESENT` and member `T_f_present`.
* An INTEGER maps to `int64_t` if its constraint fits in 64 bits.
  Otherwise it maps to `ASN1_Pulse_Rel_asn1_int_impl`: either an
  `int64_t` (`Small`) or the slice of its minimal content bytes. The same
  applies to ENUMERATED.
* BOOLEAN maps to `bool`, NULL to `unit`, and OCTET STRING and the
  character string types to `Pulse_Lib_Slice_slice__uint8`.
* SEQUENCE OF / SET OF map to a LowParse mixed list,
  `LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_<elt>`. Parsers
  return it lazily (count and payload). To write one, build its `Base` /
  `Slice` case over a C array (see `tests/small_test.c`).

* A SEQUENCE with an ANY DEFINED BY table (see below) maps to a struct `T`
  with the components before the key, and a tagged union `T_key` for the
  key and the components after it: one alternative `T_key_case` per
  table entry (the key is implicit; the payload is a struct `T_case` of
  the remaining components, if more than one), and `T_key_other` with the
  key and the payload of the fallback.
* An `OCTET STRING (CONTAINING U)` maps to the C type of `U`: the parser decodes the contents, and the writer
  encodes them.

See `tests/Small.asn` and `tests/small_test.c` for a complete example,
including KEEP-BYTES on `Names`, and `tests/X509Lite.asn` (with
`tests/X509LiteBase.asn`) and `tests/x509lite_test.c` for IMPORTS, OID
values, ANY DEFINED BY tables and extension values.

### ANY DEFINED BY tables: `--#DEFINED-BY`

ASN.1 (X.208) `ANY DEFINED BY key` does not say which type corresponds to
which key; X.680 uses information object classes instead, which are not
supported. A `--#DEFINED-BY` directive (an ASN.1 comment, ignored by other
tools) gives the table:

```
--#DEFINED-BY AlgorithmIdentifier.parameters {
--#  sha256WithRSAEncryption : NULL,
--#  ecdsa-with-SHA256 : ABSENT
--#}

--#DEFINED-BY Extension.extnValue BY extnID {
--#  id-ce-basicConstraints : CONTAINING BasicConstraints,
--#  id-ce-keyUsage : CONTAINING KeyUsage
--#} FALLBACK NONE
```

* `T.f` is the dependent component of the SEQUENCE `T`. Its key is the
  component named by `ANY DEFINED BY`, or by `BY key` (needed when `f` is
  not an ANY, e.g. the OCTET STRING `extnValue`).
* The key must be a mandatory BOOLEAN, INTEGER or OBJECT IDENTIFIER
  component without constraints (EXPLICIT tags allowed). The keys are value
  references, `TRUE`/`FALSE`, numbers or `{ ... }` OID values.
* For each key, `f` becomes, under its declared tags:
  * `ABSENT`: nothing (the component is removed);
  * `U` or `U OPTIONAL`: type `U` (`f` is OPTIONAL only if so marked);
  * `CONTAINING U`: the declared type of `f` (an OCTET STRING), whose
    contents are the DER encoding of a `U`.
  The components between the key and `f` (e.g. `critical`) are kept as is
  in every case.
* Unknown keys use the declared component (the default), the given
  `FALLBACK` entry, or are rejected (`FALLBACK NONE`).

A directive may span several `--#` lines. The generated schema is the
`ASN1_ANY_DEFINED_BY` of `ASN1.Base` (as in `asn1_any_oid_with_fallback`).
Without a table, `ANY DEFINED BY x` is parsed as ANY.

The other directives are `--#KEEP-BYTES T1, T2 ...` (see above).

### IMPORTS and values

`IMPORTS a, B FROM M;` (optionally followed by an OID or a value
reference naming the module) imports type and value assignments of the
module `M`, which must be given on the command line. Value assignments of
INTEGER (and of a type with named numbers) and OBJECT IDENTIFIER types can
be used in DEFAULT values, constraint bounds (`SIZE (1..ub-name)`) and
DEFINED-BY keys. OID values use the X.680 syntax
(`{ id-ce 19 }`, `{ iso(1) member-body(2) 840 }`, with the names `iso`,
`itu-t` and `joint-iso-itu-t` predefined). Each OBJECT IDENTIFIER value
`v` is generated as `oid_v` in `M.fst`.

## Supported ASN.1

Supported:

* Modules with `IMPLICIT TAGS`, `EXPLICIT TAGS` or `AUTOMATIC TAGS`.
* Type assignments and references.
* All universal terminal types; INTEGER and ENUMERATED with named numbers.
* Value range and single value constraints on INTEGER; SIZE constraints
  on OCTET STRING and character strings. SIZE counts characters:
  octets for OCTET STRING and the ISO 2022 based strings (TeletexString,
  VideotexString, GraphicString, GeneralString, ObjectDescriptor), code
  points for UTF8String, BMPString and UniversalString. SIZE bounds must
  be below 65536.
* `[n]` / `[APPLICATION n]` / ... tags, IMPLICIT and EXPLICIT.
* SEQUENCE and SET (at most 64 components) with OPTIONAL and DEFAULT
  components. DEFAULT applies to BOOLEAN, INTEGER, ENUMERATED and
  (unconstrained) OBJECT IDENTIFIER components, also under one EXPLICIT
  tag if unconstrained (such as `[0] EXPLICIT Version DEFAULT v1`).
* CHOICE, SEQUENCE OF and SET OF (with SIZE), and ANY.
* IMPORTS, INTEGER and OBJECT IDENTIFIER value assignments.
* ANY DEFINED BY, with a `--#DEFINED-BY` table or as ANY.
* `OCTET STRING (CONTAINING T)`.

Not supported (rejected with an error message):

* Parameterized types, information object classes, and `ENCODED BY`.
* Extension markers (`...`) and `EXTENSIBILITY IMPLIED`.
* Open ranges (`<`) and unions of ranges in constraints (single values
  `(v1 | v2)` are supported).
* ANY as a CHOICE alternative.
* Recursive types.
* Value assignments of other types.
* EXTERNAL, EMBEDDED PDV and CHARACTER STRING. The Pulse library
  supports these, but the front end does not yet.
* DEFAULT on a constructed type, or on an EXPLICIT-tagged restricted
  INTEGER or ENUMERATED. The specification allows DEFAULT only on
  terminals, possibly under one EXPLICIT tag.
* `SIZE` on SEQUENCE OF / SET OF other than `SIZE (1..MAX)` (but see
  `--lax_size_of`).

Ambiguous schemas are reported by F\*, not by the front end: verifying
`M.fst` fails in `seq_tac`/`set_tac`. A typical case is an OPTIONAL
component followed by a component that can start with the same tag.

`make test-golden` checks that the schemas generated from
`../difftest/schemas/{DiffConstructed,DiffSet,DiffConstraints,DiffAny}.asn` are
equal, by normalization, to the hand-written translations in
`../difftest`.

Custard emits Warning 377 for `Pulse_Lib_Slice_slice__uint8`. This warning
is expected.

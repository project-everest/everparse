# everparse-asn1: from an ASN.1 module to verified C

`everparse-asn1` takes an ASN.1 module and generates, for each root type, a C
struct/union type with a validator, a zero-copy parser, and a right-to-left
DER writer. The parser and writer are verified against the pure F\* ASN.1 DER
specification (`..`). It works like the CDDL front end of EverParse:

1. Parse the `.asn` file, resolve type references, and elaborate tags.
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
make test       # test-small (C round trip) and test-golden
```

```
Main.exe [--odir DIR] [--mname NAME] [--root A,B,...] [--fstar_only] [--skip_compilation] file.asn
```

* `--odir`: the output directory (default `.`; created if missing).
* `--mname`: the F\* module name (default: the ASN.1 module name).
* `--root`: the types to generate C functions for (default: the types
  that no other type uses).
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
* `write_T_typed` is the same writer, with the relation returned by
  `parse_T` (`arel d_T pm x v`, with `v: asn1_t k_T`) and `encodable k_T v`
  as its F\* precondition. It never returns `JIT_INVALID`, and `JIT_OK`
  writes the encoding of `v`. Every value returned by `parse_T` qualifies
  (`ASN1.Pulse.TypedWriter.parsed_encodable_d`), and writing it back
  yields the parsed bytes. Its C code is that of `write_T`.

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

See `tests/Small.asn` and `tests/small_test.c` for a complete example.

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
  components.
* CHOICE, SEQUENCE OF and SET OF (with SIZE), and ANY.

Not supported (rejected with an error message):

* IMPORTS and parameterized types.
* Extension markers (`...`) and `EXTENSIBILITY IMPLIED`.
* Open ranges (`<`) and unions of ranges in constraints (single values
  `(v1 | v2)` are supported).
* ANY as a CHOICE alternative.
* Recursive types.
* Value assignments other than DEFAULT literals; OID values.
* ANY DEFINED BY.
* EXTERNAL, EMBEDDED PDV and CHARACTER STRING. The Pulse library
  supports these and ANY DEFINED BY, but the front end does not yet.
* DEFAULT on anything other than an implicitly tagged BOOLEAN or INTEGER
  (including restricted INTEGER and ENUMERATED). The specification allows
  DEFAULT only on terminals.

Ambiguous schemas are reported by F\*, not by the front end: verifying
`M.fst` fails in `seq_tac`/`set_tac`. A typical case is an OPTIONAL
component followed by a component that can start with the same tag.

`make test-golden` checks that the schemas generated from
`../difftest/schemas/{DiffConstructed,DiffSet,DiffConstraints}.asn` are
equal, by normalization, to the hand-written translations in
`../difftest`.

Custard emits Warning 377 for `Pulse_Lib_Slice_slice__uint8`. This warning
is expected.

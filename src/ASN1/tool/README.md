# everparse-asn1: from an ASN.1 module to verified C

`everparse-asn1` takes an ASN.1 module and generates, for each root type, a C
struct/union type with a validator, a zero-copy parser, and a right-to-left
DER writer. The parser and writer are verified against the pure F\* ASN.1 DER
specification (`lib/everparse/asn1/spec`). It works like the CDDL front end of EverParse:

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
     of the ASN.1 Pulse library (`lib/everparse/asn1/pulse`) with these
     descriptors, the `L_iter_*` roots iterate over parsed SEQUENCE OF
     and SET OF values, and the `L_witer_*` roots over any such list in
     writer form (built with `L_empty`, `L_of_slice` and `L_append`).
     The `T_seq_*` and `T_c_get` roots iterate lazily over the components
     of a SEQUENCE `T`.
3. Verify both modules with F\*, then extract `M.Impl` to `M.c`/`M.h` with
   Custard, F\*'s direct-to-C backend (no KaRaMeL).
4. Compile `M.c` (`cc -c`) as a sanity check.

## Building and running

From the EverParse root, `make asn1` verifies the ASN.1 library
(`lib/everparse/asn1/{spec,pulse}`) and builds `bin/everparse-asn1.exe`
(`make asn1-tool` only builds the executable). Both are part of the
binary package, and installed by `make install`.

The tests are in `share/everparse/tests/asn1/tool` (`make asn1-test` at the
toplevel), and run against `$EVERPARSE_HOME` (by default, the EverParse
repository):

```
make test       # C tests (test-small, test-x509lite, test-features, test-features2) and test-golden
```

```
everparse-asn1.exe [--odir DIR] [--mname NAME] [--root A,B,...] [--keep_bytes A,B,...] [--lax_size_of] [--max_int_union N] [--fstar_only] [--skip_compilation] [--fstar PATH] [--z3 PATH] main.asn [imported.asn ...]
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
* `--max_int_union N`: the maximal number of values of an INTEGER
  constraint that is not a single range (default 256), expanded into a
  list of values compared in turn by the validators.
* `--fstar_only`: generate the F\* modules only.
* `--skip_compilation`: do not run `cc` on the generated C.
* `--fstar PATH`: the F\* executable (default: `$FSTAR_EXE`, then
  `opt/FStar/bin/fstar.exe` or `bin/fstar.exe` of the EverParse home, then
  `fstar.exe` in the `PATH`).
* `--z3 PATH`: the Z3 executable (default: the one that F\* finds for the
  Z3 version of EverParse, then `opt/z3/z3-<version>` of the EverParse
  home).

The EverParse home is `$EVERPARSE_HOME` if set, else the parent of the
directory of the executable (`bin/`); the ASN.1 and LowParse libraries are
taken from its `lib/everparse`. `CC` defaults to `cc`.
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

### Iterators over SEQUENCE OF / SET OF

Parsed SEQUENCE OF and SET OF values are lazy: a count and the DER payload.
For each such list `L` reachable from the roots, the tool generates

```c
ASN1_Pulse_ListIter_iter L_iter_start(<list C type> x);
bool   L_iter_is_empty(ASN1_Pulse_ListIter_iter it);
size_t L_iter_length(ASN1_Pulse_ListIter_iter it);
E      L_iter_next(ASN1_Pulse_ListIter_iter *it);  /* requires !L_iter_is_empty(*it) */
```

where `L` is `T` for a named list type `T ::= SEQUENCE OF E`, `T_c` for a
list component (or CHOICE alternative) `c` of `T`, `T_k_c` for a component
`c` of the case `k` of an ANY DEFINED BY `T` (`T_other_c` for the other
keys), and `L_elt` for the elements of a list `L` that are themselves
lists. `L_iter_next` parses the next element, zero-copy, and advances the
cursor. These functions apply to parsed values only (in F\*, `start`
requires `arel true`), not to lists built by a caller.

To build a list, or to iterate over any list the writers accept (parsed,
built, or a mix: `arel false`), the tool also generates

```c
<list C type> L_empty(void);
<list C type> L_of_slice(<slice of E> a);           /* the elements of an array */
<list C type> L_append(<list C type> *b, <list C type> *a);  /* b, then a */
LowParse_PulseParse_Iterator_Type_iterator__uintsize_E L_witer_start(<list C type> x);
bool L_witer_is_empty(LowParse_PulseParse_Iterator_Type_iterator__uintsize_E it);
E    L_witer_next(LowParse_PulseParse_Iterator_Type_iterator__uintsize_E *it);  /* requires !L_witer_is_empty(*it) */
```

`L_append` points to `b` and `a`, which must outlive the result, and
`L_of_slice` points to the array; neither copies the elements.
`L_witer_next` returns array elements as they are, and parses serialized
ones zero-copy. The C iterator and list types are generic instances
(Custard warning 377): typedef them once if needed. A SET OF is iterated
in list order; the writers sort it.

### Iterators over the components of a SEQUENCE or SET

Instead of parsing a whole SEQUENCE `T` with `parse_T`, its components can
be visited one at a time, each parsed only on demand. For each non-empty
SEQUENCE `T` reachable from the roots (named, or anonymous `T_c`), the tool
generates

```c
ASN1_Pulse_SeqIter_seq_iter T_seq_start(Pulse_Lib_Slice_slice__uint8 input);
bool T_seq_is_empty(ASN1_Pulse_SeqIter_seq_iter it);
ASN1_Pulse_SeqIter_seq_item T_seq_next(ASN1_Pulse_SeqIter_seq_iter *it);  /* requires !T_seq_is_empty(*it) */
#define T_c_index (<i>U)                       /* for each component c, the i-th */
<C type of c> T_c_get(ASN1_Pulse_SeqIter_seq_item x);  /* requires x.comp == T_c_index */
```

`T_seq_start` takes the bytes of a validated `T` (`validate_T`). Each item
returned by `T_seq_next` is a *present* component: `x.comp` is its index
(absent OPTIONAL and DEFAULT components are skipped) and `x.bytes` its
encoding (a slice of the input), so a caller dispatches with
`switch (x.comp) { case T_c_index: ... T_c_get(x) ... }`. `T_c_get` returns
the same value as the `c` field of `parse_T` (an OPTIONAL or DEFAULT
component is `T_c_present`). A component whose type is itself a named
SEQUENCE `U` can be iterated in turn with `U_seq_start(x.bytes)`.

For each non-empty SET `T`, the tool generates the same functions, named
`T_set_start`, `T_set_is_empty` and `T_set_next` (with the same item type,
`T_c_index` and `T_c_get`). The components then come in encoding order,
i.e. in the canonical (DER) order of their tags, which may differ from
their declaration order; `x.comp` is still the index of the component in
the declaration. `T_set_start` needs the bytes of a SET with its universal
tag (`0x31`): for an IMPLICITly tagged SET, use `parse_T` instead.

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
`to_writer d_T`, specialized.

An IMPLICIT tag on `T` (`[1] T` in an IMPLICIT TAGS module, or
`[1] IMPLICIT T`) keeps the bytes too: the tagged type gets its own
KEEP-BYTES descriptor, with the same C type `T_kept`, and `raw` covers the
encoding with the new tag.

`--#KEEP-BYTES T.c` (or `--keep_bytes T.c`) keeps the bytes of the
component `c` of the SEQUENCE or SET `T` only, including its tags. If the
type of `c` is anonymous, e.g. `c SEQUENCE { ... }`, its C type `T_c` gets
the kept version `T_c_kept`; otherwise, the component gets a new type
`T_c` (an alias of the type of `c`, kept). KEEP-BYTES is rejected on DEFAULT
components and on the key and dependent components of a DEFINED-BY table.

Limitations: KEEP-BYTES is rejected on a CHOICE used untagged as an
alternative of another CHOICE. A CHOICE alternative of a KEEP-BYTES type
does not keep its bytes (everparse-asn1 prints a warning): CHOICE
alternatives are content descriptors.

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
values, ANY DEFINED BY tables and extension values. `tests/Features.asn`
and `tests/features_test.c` cover open ranges and unions, DEFAULT strings
and BIT STRINGs, DEFINED-BY keys of other types, EXTERNAL, EMBEDDED PDV,
and KEEP-BYTES under IMPLICIT tags and on components. `tests/Features2.asn`
(with `tests/Features2Base.asn`) and `tests/features2_test.c` cover value
notations, BOOLEAN constraints, WITH COMPONENTS, parameterized types,
information object classes (also in nested SEQUENCE types), constraint set
operations, value sets, contained subtypes and extensible constraints.

### ANY DEFINED BY tables: `--#DEFINED-BY`

ASN.1 (X.208) `ANY DEFINED BY key` does not say which type corresponds to
which key; X.680 uses information object classes instead (see below). A
`--#DEFINED-BY` directive (an ASN.1 comment, ignored by other tools) gives
the table:

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
* The key must be a mandatory component of a terminal type other than
  RELATIVE-OID, without constraints (EXPLICIT tags allowed). The keys are
  values (see Values below): value references, `TRUE`/`FALSE`, numbers,
  `{ ... }` OID values, strings, times, etc.
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

The other directives are `--#KEEP-BYTES T1, T2.c ...` (see above).

### Information object classes and table constraints

The common use of information object classes (X.681) and table
constraints (X.682), an open type selected by an OID, generates a
DEFINED-BY table:

```
EXTENSION ::= CLASS {
  &id OBJECT IDENTIFIER UNIQUE, &ExtnType, &Critical BOOLEAN DEFAULT FALSE
} WITH SYNTAX { SYNTAX &ExtnType IDENTIFIED BY &id [CRITICALITY &Critical] }

ext-bc EXTENSION ::= { SYNTAX BasicConstraints IDENTIFIED BY id-ce-basicConstraints }
Exts EXTENSION ::= { ext-bc | ext-ku, ... }

Extension { EXTENSION : ExtSet } ::= SEQUENCE {
  extnId EXTENSION.&id ({ExtSet}),
  critical BOOLEAN DEFAULT FALSE,
  extnValue OCTET STRING (CONTAINING EXTENSION.&ExtnType ({ExtSet}{@extnId}))
}
Extensions ::= SEQUENCE SIZE (1..MAX) OF Extension {{Exts}}
```

* Classes: `CLASS { ... }` with type fields (`&T`, possibly OPTIONAL or
  DEFAULT) and fixed-type value fields (`&id T [UNIQUE] [OPTIONAL | DEFAULT
  v]`), with or without `WITH SYNTAX` (with optional groups `[...]`);
  `TYPE-IDENTIFIER` and `ABSTRACT-SYNTAX`; class aliases (`ALG ::=
  TYPE-IDENTIFIER`). Other kinds of fields (value sets, objects,
  variable-type values) are skipped, and cannot be referenced.
* Objects (`obj CLASS ::= { ... }`, in the default syntax `&f setting, ...`
  or the class's syntax) and object sets (`Set CLASS ::= { o1 | o2 | { inline
  object } | OtherSet, ... }`, with `|` or `UNION`, and an optional
  extension marker). Object set parameters (`{ EXTENSION : ExtSet }`) and
  class parameters (`{ ALG-TYPE, ALG-TYPE : AlgSet }`) of parameterized
  types are supported.
* In a SEQUENCE type (a type assignment, an instance of a parameterized
  SEQUENCE, or a nested SEQUENCE type, which is then generated as a new
  type), a component `C.&T ({Set}{@key})`, possibly under tags, `SET
  OF` / `SEQUENCE OF` or `OCTET STRING (CONTAINING ...)`, whose key
  component is `C.&id ({Set})`, generates a DEFINED-BY table: each object
  of `Set` gives a case (its `&id` value), where the component has the
  object's `&T` (or is absent, if the object has no `&T` and the
  component is OPTIONAL). If `Set` is extensible, unknown keys use the
  declared component (`C.&T` is ANY); otherwise, they are rejected. A
  `--#DEFINED-BY` directive on the same type takes precedence (with a
  warning).
* The key `@key` may be written as an absolute (`@a.b.key`, from the type
  assignment) or relative (`@.key`, from the innermost SEQUENCE, SET or
  CHOICE; `@..key` from the one enclosing it, ...) component reference,
  but must designate a component of the same SEQUENCE as the dependent
  component.
* Everywhere else, `C.&T` is ANY, `C.&id` has the type of the field, and
  the simple table constraints `({Set})` are ignored: in particular, a key
  component is not checked against the set by itself (only through its
  dependent component, if the set is not extensible).
* Not supported: several `{@key}` constraints in a SEQUENCE, `{@key}` in
  SET or CHOICE types, keys in another SEQUENCE than the dependent
  component (e.g. in an enclosing one), and keys of several components.
  The settings of value fields other than the key (e.g. `&Critical`) are
  not checked.

### Parameterized types

Parameterized types (X.683) with type parameters, value parameters
(`{ INTEGER : ub }`), object set parameters and class parameters, also
imported (`IMPORTS Name{} FROM M`), are expanded at their use sites: each
instance `Name { args }` becomes a type `Name_args` of the module of the
template, with its own C type. Parameterized values, value sets, objects
and object sets are not supported, nor are recursive instances.

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

Value assignments of all the types with supported values may be used in
DEFAULT values and DEFINED-BY keys; values of other types (SEQUENCE,
CHOICE, `SEQUENCE OF`, ...) are parsed and ignored. Values of other types:

* NULL: `NULL`. BOOLEAN: `TRUE`, `FALSE`.
* OCTET STRING: `'0A1B'H` or `'00001010'B` (padded with zeros to whole
  octets).
* BIT STRING: `'1010'B`, `'A0'H`, or named bits `{ a, b }` (with `{}`
  for no bits). With named bits, trailing zero bits are removed, as DER
  requires (X.690 11.2.2). Note that the parser compares the encoded
  bytes: a value with trailing zero bits is not equal to its normalized
  DEFAULT value. Validators and writers do not check that a BIT STRING
  with named bits has no trailing zero bits (X.690 11.2.2) either.
* Character strings: `"..."` (with `""` for a quote). UTF8String
  values are the UTF-8 bytes of the source file, BMPString and
  UniversalString values are re-encoded as UTF-16BE and UTF-32BE.
  PrintableString, NumericString, VisibleString and IA5String values are
  checked against their character sets. The other string types accept
  printable ASCII only. Character string lists (`{ "ab", {0, 0, 3, 177},
  ref }`) with Quadruples and Tuples are supported. String values of
  SIZE-constrained types are checked against the constraint by F\*
  (`ASN1.Lit`).
* Time types: `"YYMMDDhhmmssZ"` (UTCTime), `"YYYYMMDDhhmmss[.f]Z"`
  (GeneralizedTime), `"YYYY-MM-DD"` (DATE), `"hh:mm:ss"` (TIME-OF-DAY),
  `"YYYY-MM-DDThh:mm:ss"` (DATE-TIME). OID-IRI and RELATIVE-OID-IRI:
  `"/ISO/a"`, `"a/1"`. Their DER validity is checked by F\* (`ASN1.Lit`).
* Not supported: RELATIVE-OID values.

## Supported ASN.1

Supported:

* Modules with `IMPLICIT TAGS`, `EXPLICIT TAGS` or `AUTOMATIC TAGS`.
* Type assignments and references.
* All universal terminal types; INTEGER and ENUMERATED with named numbers.
* Value range and single value constraints on INTEGER, with open bounds
  (`0<..<10`, `MIN<..0`); single value constraints on BOOLEAN. Set
  operations (`|` / `UNION`, `^` / `INTERSECTION`, `EXCEPT`, `ALL EXCEPT`,
  parentheses) and serial constraints (`T (C1) (C2)`, also on a reference
  to a constrained type) are evaluated by the front end; a result that is
  not a single range is expanded into its values (at most 256, see
  `--max_int_union`). Contained subtypes (`INCLUDES T`, or `T`) are
  replaced with the (value or SIZE) constraints of `T`. Value sets
  (`Name INTEGER ::= { 1 | 3..5 }`) are constrained types, and may be
  used as such or as contained subtypes. Extensible constraints (`(C,
  ...)`, `(C, ..., D)`, also within SIZE) do not restrict the values that
  a DER decoder accepts (X.680 49.4), so they are ignored. SIZE
  constraints on OCTET STRING and character strings, with open bounds and
  set operations whose result is a single range. SIZE counts characters:
  octets for OCTET STRING and the ISO 2022 based strings (TeletexString,
  VideotexString, GraphicString, GeneralString, ObjectDescriptor), code
  points for UTF8String, BMPString and UniversalString. SIZE bounds must
  be below 65536.
* `[n]` / `[APPLICATION n]` / ... tags, IMPLICIT and EXPLICIT.
* SEQUENCE and SET (at most 64 components) with OPTIONAL and DEFAULT
  components. DEFAULT applies to components of terminal types other than
  RELATIVE-OID, also under one EXPLICIT tag if unconstrained (such as
  `[0] EXPLICIT Version DEFAULT v1`), and to constrained INTEGER,
  ENUMERATED, BOOLEAN, OCTET STRING and character strings.
* CHOICE, SEQUENCE OF and SET OF (with SIZE), and ANY.
* Inner type constraints: `WITH COMPONENTS { [...,] c (C) PRESENT | ABSENT
  | OPTIONAL, ... }` on SEQUENCE, SET, CHOICE, and the SEQUENCE types of
  EXTERNAL, EMBEDDED PDV and CHARACTER STRING; `WITH COMPONENT (C)` on
  SEQUENCE OF and SET OF. A constrained type is generated as a new type.
* Parameterized types, information object classes and table constraints
  (see above).
* IMPORTS and value assignments.
* EXTERNAL, EMBEDDED PDV and CHARACTER STRING, with their X.680 associated
  types (as in `ASN1.UniversalTypes`). They are defined in a prelude ASN.1
  module (`Prelude.ml`), named `EXTERNAL`, `EMBEDDED-PDV` and
  `CHARACTER-STRING`, generated only if used.
* ANY DEFINED BY, with a `--#DEFINED-BY` table or as ANY.
* `OCTET STRING (CONTAINING T)`.

Not supported (rejected with an error message):

* `ENCODED BY`.
* Extension markers (`...`) in types, and `EXTENSIBILITY IMPLIED`.
* SIZE constraints that are not a single range, combinations of SIZE and
  value constraints, and permitted alphabet (`FROM`) and `PATTERN`
  constraints. Contained subtypes of tagged types, constrained `SEQUENCE
  OF` / `SET OF` types, or types with constraints other than value and
  SIZE constraints. Value sets of types other than INTEGER and BOOLEAN
  (their values are parsed as constraint bounds).
* ANY as a CHOICE alternative.
* Recursive types.
* RELATIVE-OID values.
* DEFAULT on a constructed type, or on an EXPLICIT-tagged restricted
  INTEGER or ENUMERATED. The specification allows DEFAULT only on
  terminals, possibly under one EXPLICIT tag.
* `SIZE` on SEQUENCE OF / SET OF other than `SIZE (1..MAX)` (but see
  `--lax_size_of`).

Ambiguous schemas are reported by F\*, not by the front end: verifying
`M.fst` fails in `seq_tac`/`set_tac`. A typical case is an OPTIONAL
component followed by a component that can start with the same tag.

`make test-golden` checks that the schemas generated from
`share/everparse/tests/asn1/difftest/schemas/{DiffConstructed,DiffSet,DiffConstraints,DiffAny,DiffExternal,DiffPdv,DiffCharStr}.asn`
are equal, by normalization, to the hand-written translations
`ASN1.DiffTest.*` of that directory.

Custard emits Warning 377 for `Pulse_Lib_Slice_slice__uint8`. This warning
is expected.

.. _asn1:

everparse-asn1: Verified ASN.1 DER Parsers and Serializers
==========================================================

.. note::

   This page documents the current source tree and package layout.
   ASN.1 support is experimental.

EverParse/ASN.1 turns an ASN.1 module into C data types together with
validators, zero-copy parsers and DER writers, all formally verified
against a pure F\* specification of ASN.1 DER (X.680, X.690). It has
three layers:

* **The specification** (``lib/everparse/asn1/spec``): a schema language
  for ASN.1 types (``ASN1.Syntax``, ``asn1_k``), and its interpretation as
  LowParse parsers and serializers of DER encodings. It builds on the
  ASN1\* work (`CPP 2022
  <https://www.microsoft.com/en-us/research/publication/asn1-provably-correct-non-malleable-parsing-for-asn-1-der/>`_).

* **The verified library** (``lib/everparse/asn1/pulse``): validators,
  zero-copy parsers and right-to-left DER writers, generic in the schema,
  written and verified in Pulse, and extracted to C with Custard
  (F\*'s direct-to-C backend).

* **The front end** ``everparse-asn1``: from ``.asn`` files, it generates
  the F\* schemas, C types tied to them, and the C code of the validators,
  parsers and writers, by instantiating the library.

Verified guarantees
-------------------

For each generated type ``T`` with schema ``k_T``:

* **Memory safety:** no buffer overrun, and no heap allocation.

* **Validators are correct and complete:** ``validate_T`` succeeds
  exactly when the specification parser succeeds, and consumes the same
  number of bytes. Since the specification only accepts DER, validators
  reject BER and every non-canonical encoding.

* **Non-malleability:** like all LowParse parsers, the specification
  parsers are injective: a value has at most one accepted encoding. The
  specification also gives each schema a serializer, proven to be the
  inverse of its parser.

* **Parsers are correct:** ``parse_T`` returns a C value that represents
  the value parsed by the specification.

* **Writers are correct:** ``write_T`` writes exactly the DER encoding of
  the value it is given, and fails if there is none.

* **Constant stack, no recursion:** the extracted C code has one function
  per schema node and no recursive call. Even ANY, whose nesting is
  unbounded, is validated in a loop.

Getting started
---------------

``everparse-asn1.exe`` is in the ``bin/`` directory of the EverParse
binary package. To build it from the EverParse source tree, run ``make
asn1``, which also verifies the ASN.1 library and copies the executable to
``bin/``. ``make install`` installs both.

Consider ``Small.asn``:

.. code-block:: text

   Small DEFINITIONS IMPLICIT TAGS ::= BEGIN

   --#KEEP-BYTES Names

   Version ::= INTEGER { v1(0), v2(1), v3(2) } (0..2)

   Color ::= ENUMERATED { red, green(5), blue }

   Inner ::= CHOICE {
     num  INTEGER,
     flag BOOLEAN
   }

   Alt ::= CHOICE {
     name  [0] OCTET STRING,
     inner Inner,
     nul   NULL
   }

   Pair ::= SET {
     left  [0] INTEGER (0..255),
     right [1] OCTET STRING (SIZE (1..4)),
     note  [2] BOOLEAN OPTIONAL
   }

   Names ::= SEQUENCE {
     short PrintableString (SIZE (1..4)),
     wide  UTF8String (SIZE (1..2)),
     bmp   BMPString (SIZE (2)) OPTIONAL
   }

   Msg ::= SEQUENCE {
     version  [0] Version DEFAULT v1,
     id       INTEGER,
     critical BOOLEAN DEFAULT FALSE,
     color    Color OPTIONAL,
     body     [3] Alt,
     pair     [1] Pair OPTIONAL,
     items    SEQUENCE SIZE (1..MAX) OF OCTET STRING,
     extra    [2] SEQUENCE { a INTEGER, b UTF8String } OPTIONAL
   }

   Wrapper ::= SEQUENCE {
     n     INTEGER (0..255),
     names Names,
     alt   [0] EXPLICIT Names OPTIONAL
   }

   END

Then run::

  everparse-asn1.exe --odir out --root Msg,Names,Wrapper Small.asn

This produces, in ``out/``:

* ``Small.fst``: the F\* schemas ``k_T``. F\* tactics prove that they are
  well-formed, and in particular that no SEQUENCE, SET or CHOICE is
  ambiguous (for instance, an OPTIONAL component followed by a component
  with the same tag).
* ``Small.Impl.fst``: the C types, the descriptors ``d_T`` that tie them
  to the schemas, and the extraction roots.
* ``Small.c`` and ``Small.h``: the C code, extracted from
  ``Small.Impl.fst`` after both modules are verified.

``Small.c`` is self-contained: it only needs ``Small.h`` and the C
standard library. The tool compiles it with ``cc -c`` as a sanity check.

Command-line options
^^^^^^^^^^^^^^^^^^^^

::

  everparse-asn1.exe [options] main.asn [imported.asn ...]

The first file is the main module. Every module that it imports, directly
or not, must also be given on the command line.

``--odir DIR``
  The output directory (default ``.``, created if missing).

``--mname NAME``
  The F\* module name (default: the ASN.1 module name).

``--root A,B,...``
  The types for which to generate C functions (default: the types that no
  other type uses).

``--keep_bytes A,B.c,...``
  The types (or components ``c`` of a SEQUENCE or SET ``B``) whose parsed
  values keep their bytes. See :ref:`asn1-keep-bytes`.

``--lax_size_of``
  Accept ``SIZE (lo..hi)`` and ``SIZE (n)`` on SEQUENCE OF / SET OF, but
  only check that the list is non-empty when ``lo >= 1``. **The validators
  then accept more values than the schema allows.** RFC 5280 uses such
  bounds, e.g. ``SIZE (1..ub-domain-defined-attributes)``.

``--max_int_union N``
  The maximal number of values of an INTEGER constraint that is not a
  single range (default 256). Such a constraint is expanded into a list
  of values, which the validators compare in turn.

``--fstar_only``
  Only generate the F\* modules.

``--skip_compilation``
  Do not compile the generated C code.

``--fstar PATH``
  The F\* executable. By default: ``$FSTAR_EXE``, then the F\* of the
  EverParse home (``opt/FStar`` in a source tree, ``bin/fstar.exe`` in a
  binary package), then ``fstar.exe`` in the ``PATH``.

``--z3 PATH``
  The Z3 executable. By default: the one F\* finds for the Z3 version of
  EverParse, then the one shipped with EverParse.

The EverParse home is ``$EVERPARSE_HOME`` if set, otherwise the parent
of the directory of ``everparse-asn1.exe``. The ASN.1 and LowParse
libraries are taken from its ``lib/everparse``. ``$CC`` defaults to
``cc``.

.. warning::

   Extraction is slow and memory-hungry: it can take tens of minutes and
   more than 10 GB of memory per schema. F\* verification and C
   compilation take seconds; Custard extraction takes the rest.

The C API
---------

Functions
^^^^^^^^^

For each root type ``T``:

.. code-block:: c

   void custard_init_globals(void);  /* call once, before anything else */

   bool validate_T(Pulse_Lib_Slice_slice__uint8 input, size_t *offset);

   T parse_T(Pulse_Lib_Slice_slice__uint8 validated_input);

   ASN1_Pulse_JitWriter_jit_result
   write_T(T x, Pulse_Lib_Slice_slice__uint8 out, size_t *pos);

   ASN1_Pulse_JitWriter_jit_result
   write_T_typed(T x, Pulse_Lib_Slice_slice__uint8 out, size_t *pos);

A byte buffer is a slice:

.. code-block:: c

   typedef struct { uint8_t *elt; size_t len; } Pulse_Lib_Slice_slice__uint8;

``validate_T``
  Checks that the bytes of ``input`` from ``*offset`` start with the DER
  encoding of a value of ``T``. On success, it returns ``true`` and
  advances ``*offset`` past that encoding. To check that a buffer is
  *exactly* one encoding, start with ``*offset == 0`` and check
  ``*offset == input.len`` afterwards.

``parse_T``
  Must be called on validated input only: a slice of exactly the bytes
  accepted by ``validate_T``. It copies nothing and allocates nothing:
  strings, OIDs, big INTEGERs, times and ANY values in the result are
  slices of the input. The result is valid as long as the input buffer
  is.

``write_T``
  Writes the DER encoding of ``x`` *right to left*: the encoding ends at
  ``*pos``, and on success ``*pos`` is moved back to its start, so the
  encoding is ``out.elt[*pos .. old *pos)``. Each length is written after
  its contents, so no size is computed beforehand. ``write_T`` returns:

  * ``ASN1_PULSE_JITWRITER_JIT_OK``: the encoding was written;
  * ``ASN1_PULSE_JITWRITER_JIT_INVALID``: ``x`` is not a valid value of
    ``T``, for instance an INTEGER out of range, a string that is too
    long or has a forbidden character, an undeclared ENUMERATED value, or
    a non-minimal big INTEGER;
  * ``ASN1_PULSE_JITWRITER_JIT_NO_SPACE``: ``x`` is valid, but the
    encoding does not fit before ``*pos``.

  On failure, the bytes of ``out`` after ``*pos`` are unchanged. The
  writer also does what DER requires of the encoder: it omits a DEFAULT
  component equal to its default value, and sorts SET components and SET
  OF elements. ``JIT_RETRY`` is internal and never returned.

``write_T_typed``
  The same C code as ``write_T``, with a stronger F\* precondition (see
  :ref:`asn1-pulse-api`), under which it never returns ``JIT_INVALID``.

Here is a round trip with ``Msg``:

.. code-block:: c

   #include "Small.h"

   int roundtrip(uint8_t *in, size_t len, uint8_t *buf, size_t buf_len) {
     custard_init_globals();
     Pulse_Lib_Slice_slice__uint8 s = { .elt = in, .len = len };
     size_t off = 0;
     if (!validate_Msg(s, &off) || off != len)
       return 1;                       /* not exactly one DER Msg */
     Msg m = parse_Msg(s);             /* zero-copy */
     Pulse_Lib_Slice_slice__uint8 o = { .elt = buf, .len = buf_len };
     size_t pos = buf_len;
     if (write_Msg(m, o, &pos) != ASN1_PULSE_JITWRITER_JIT_OK)
       return 2;
     /* buf[pos .. buf_len) == in[0 .. len) */
     return 0;
   }

The complete tests are in ``share/everparse/tests/asn1/tool``
(``small_test.c``, ``x509lite_test.c``, ``features_test.c``,
``features2_test.c``).

C types
^^^^^^^

.. list-table::
   :header-rows: 1
   :widths: 35 65

   * - ASN.1
     - C
   * - SEQUENCE, SET
     - ``struct T``, one field per component. Anonymous nested types are
       named after their path, e.g. ``Msg_extra``.
   * - CHOICE
     - tagged union ``T``: tags ``M_IMPL_T_ALT``, union members
       ``T_alt``. Nested CHOICEs are not flattened.
   * - OPTIONAL or DEFAULT component ``f`` of ``T``
     - tagged type ``T_f_opt``: tags ``M_IMPL_T_F_ABSENT`` /
       ``M_IMPL_T_F_PRESENT``, member ``T_f_present``. A parsed DEFAULT
       component equal to its default is ``ABSENT``.
   * - INTEGER, ENUMERATED
     - ``int64_t`` if the constraint fits in 64 bits. Otherwise
       ``ASN1_Pulse_Rel_asn1_int_impl``: either ``Small`` (``int64_t``)
       or ``Big`` (the slice of the minimal two's-complement content
       bytes).
   * - BOOLEAN, NULL
     - ``bool``, ``unit``
   * - OCTET STRING, character strings, OBJECT IDENTIFIER, RELATIVE-OID,
       time types, OID-IRI types
     - ``Pulse_Lib_Slice_slice__uint8``: the content bytes
   * - ANY
     - ``Pulse_Lib_Slice_slice__uint8``: the whole TLV
   * - BIT STRING
     - ``asn1_bitstring_impl { uint8_t unused; slice bytes; }``
   * - SEQUENCE OF, SET OF
     - LowParse mixed list
       ``LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_<elt>``.
       To write one, use its ``Base`` / ``Slice`` case over a C array of
       elements. A parsed list is in its ``Base`` / ``Serialized`` case:
       the element count, and the payload (the concatenated, validated
       DER encodings of the elements).
   * - ``OCTET STRING (CONTAINING U)``
     - the C type of ``U``: parsers decode the contents, writers encode
       them.
   * - SEQUENCE with an ANY DEFINED BY table
     - ``struct T`` with the components before the key, and a tagged
       union ``T_key``: one case per table entry (the key is implicit),
       and ``T_key_other { key; other }`` for the fallback.
   * - KEEP-BYTES type ``T``
     - ``T_kept { T value; T_raw raw; }``: see :ref:`asn1-keep-bytes`.
   * - Value assignments of INTEGER and OBJECT IDENTIFIER
     - constants, e.g. ``oid_<name>`` (the content bytes)

For instance, ``Small.h`` contains:

.. code-block:: c

   struct Pair_s {
     int64_t left;
     Pulse_Lib_Slice_slice__uint8 right;
     Pair_note_opt note;
   };

   struct Msg_s {
     Msg_version_opt version;
     ASN1_Pulse_Rel_asn1_int_impl id;
     Msg_critical_opt critical;
     Msg_color_opt color;
     Alt body;
     Msg_pair_opt pair;
     LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 items;
     Msg_extra_opt extra;
   };

.. _asn1-keep-bytes:

KEEP-BYTES
^^^^^^^^^^

A line ``--#KEEP-BYTES T`` in the ``.asn`` file (an ASN.1 comment, which
other tools ignore), or ``--keep_bytes T``, makes every use of ``T`` use
the C type

.. code-block:: c

   typedef struct { T value; T_raw raw; } T_kept;

Parsers set ``raw`` (tag ``M_IMPL_T_RAW_PRESENT``, member
``T_raw_present``) to the slice of the input holding the DER encoding of
``value``. This is useful to check a signature over a sub-structure, such
as the ``tbsCertificate`` of an X.509 certificate. Writers ignore ``raw``,
so stale bytes are never written.

An IMPLICIT tag on ``T`` keeps the bytes too, including the new tag.
``--#KEEP-BYTES T.c`` keeps the bytes of the component ``c`` of the
SEQUENCE or SET ``T`` only, including its tags.

ANY DEFINED BY tables
^^^^^^^^^^^^^^^^^^^^^

An ``ANY DEFINED BY`` component, or an ``ANY`` component, can be given a
dispatch table in a ``--#DEFINED-BY`` comment:

.. code-block:: text

   --#DEFINED-BY AlgorithmIdentifier.parameters { sha256WithRSAEncryption : NULL, ecdsa-with-SHA256 : ABSENT }
   --#DEFINED-BY Extension.extnValue BY extnID { id-ce-basicConstraints : CONTAINING BasicConstraints } FALLBACK NONE

Each case is ``ABSENT``, ``U [OPTIONAL]`` or ``CONTAINING U``. Unknown
keys use the declared type of the component, the given ``FALLBACK U``, or
are rejected (``FALLBACK NONE``). Table constraints of information object
classes (``C.&Type ({Set}{@key})``) are compiled to the same verified
dispatch. Without a table, ANY DEFINED BY is treated as ANY.

Supported ASN.1
---------------

DER encoding
^^^^^^^^^^^^

The specification follows X.690 DER:

* identifiers of any class and number, in their shortest form, with a
  constructed bit that must match the type; definite lengths only, in
  their shortest form (up to :math:`2^{32}-1` bytes);
* minimal INTEGER encodings; BOOLEAN ``TRUE`` encoded as ``0xFF``;
* OBJECT IDENTIFIER and RELATIVE-OID with minimal subidentifiers; the
  first OID subidentifier (40X+Y) can take several bytes;
* BIT STRING with zero padding bits;
* primitive encodings of strings (no constructed strings);
* UTCTime as ``YYMMDDhhmmssZ``, GeneralizedTime as
  ``YYYYMMDDhhmmss[.f]Z`` with no trailing zero in the fraction;
* SET components sorted by tag (X.690 10.3), SET OF elements sorted by
  encoding (X.690 11.6);
* DEFAULT components equal to their default value are absent (X.690
  11.5).

Types
^^^^^

* BOOLEAN, NULL, INTEGER (of any size), ENUMERATED, BIT STRING,
  OCTET STRING, OBJECT IDENTIFIER, RELATIVE-OID, OID-IRI,
  RELATIVE-OID-IRI.
* UTCTime, GeneralizedTime, DATE, TIME-OF-DAY, DATE-TIME.
* Character strings: UTF8String, PrintableString, IA5String,
  NumericString, VisibleString, BMPString and UniversalString, whose
  contents are checked; TeletexString, VideotexString, GraphicString,
  GeneralString and ObjectDescriptor, whose contents are not checked
  (see `Limitations`_).
* SEQUENCE and SET (up to 64 components), with OPTIONAL and DEFAULT
  components; CHOICE; SEQUENCE OF and SET OF.
* ANY, validated as any DER value; ANY DEFINED BY.
* EXTERNAL, EMBEDDED PDV and CHARACTER STRING, through their X.680
  associated types.
* ``OCTET STRING (CONTAINING U)``.
* Tags: ``[n]``, ``[APPLICATION n]``, ``[PRIVATE n]``, ``[UNIVERSAL n]``,
  IMPLICIT and EXPLICIT; modules with ``IMPLICIT``, ``EXPLICIT`` or
  ``AUTOMATIC TAGS``.

Constraints
^^^^^^^^^^^

* Value ranges and single values on INTEGER, with open bounds
  (``0<..<10``, ``MIN<..0``); single values on BOOLEAN. INTEGER and
  ENUMERATED can have named numbers; ENUMERATED values are restricted to
  the declared ones.
* SIZE on OCTET STRING and character strings. SIZE counts characters:
  bytes, or code points for UTF8String, BMPString and UniversalString.
* ``SIZE (1..MAX)`` on SEQUENCE OF and SET OF.
* Set operations (``|``, ``UNION``, ``^``, ``INTERSECTION``, ``EXCEPT``,
  ``ALL EXCEPT``) and serial constraints (``T (C1) (C2)``), evaluated by
  the front end. An INTEGER constraint that is not a single range is
  expanded into a list of values (see ``--max_int_union``).
* Contained subtypes (``INCLUDES T``) and value sets
  (``Small INTEGER ::= { 1 | 3..5 }``), which become constrained types.
* Inner type constraints: ``WITH COMPONENTS { ... }`` on SEQUENCE, SET
  and CHOICE, ``WITH COMPONENT (C)`` on SEQUENCE OF and SET OF.
* Extensible constraints (``(0..10, ...)``) are accepted and their
  extension is ignored, since it does not change which DER encodings are
  valid (X.680 49.4).

Modules, values, parameters and classes
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

* Type assignments and references; IMPORTS across several files.
* Value assignments of all terminal types except RELATIVE-OID (INTEGER,
  OBJECT IDENTIFIER such as ``{ id-ce 19 }``, BOOLEAN, strings including
  Quadruple and Tuple notations, ``'..'H`` / ``'..'B``, named bits,
  times, IRIs), used in DEFAULT values, constraint bounds and table keys.
  Values of constructed types are parsed and ignored.
* DEFAULT on terminal types other than RELATIVE-OID, also under one
  EXPLICIT tag (``[0] EXPLICIT Version DEFAULT v1``) when unconstrained.
  F\* proves by normalization that each default value is valid.
* Parameterized types (X.683) with type, value, object set and class
  parameters: each instance is expanded into a new type.
* Information object classes (X.681) and table constraints (X.682):
  ``CLASS`` with ``WITH SYNTAX``, ``TYPE-IDENTIFIER``,
  ``ABSTRACT-SYNTAX``, objects and object sets, and components
  ``C.&Type ({Set}{@key})`` with absolute or relative keys in the same
  SEQUENCE. An extensible object set uses the declared type for
  unknown keys; a non-extensible one rejects them.

.. _asn1-pulse-api:

The Pulse API
-------------

The library can also be used directly from F\* and Pulse, to write
verified code that calls the generated functions or builds new ones. A
*descriptor* ``d: adesc k t`` (``ASN1.Pulse.Rel``) ties a schema ``k``
to a C type ``t``. ``everparse-asn1`` generates one per type,
``d_T`` in ``M.Impl.fst``, and the generic functions below are
instantiated with it.

.. list-table::
   :header-rows: 1
   :widths: 25 35 40

   * - Function
     - Precondition
     - Postcondition
   * - ``validate_k`` (``validate_T``)
     - input bytes
     - ``true`` iff the specification parser ``asn1_as_parser k``
       succeeds; the offset is advanced by the number of bytes it
       consumes
   * - ``parse_d`` (``parse_T``)
     - validated input (``pts_to_parsed``)
     - a value ``x: t`` with ``arel true d pm x v``, where ``v`` is the
       value parsed by the specification
   * - ``jit_write_raw_d`` (``write_T``)
     - ``raw_varel d pm x y``, relating ``x`` to a ghost *raw* value
       ``y: asn1_raw_t k`` that need not satisfy the constraints of
       ``k``; no bytes involved
     - ``JIT_OK`` iff ``check_ser k () y == Some v`` and
       ``asn1_enc k v`` fits, and then ``asn1_enc k v`` is written;
       ``JIT_INVALID`` implies ``check_ser k () y == None``
   * - ``write_typed_d`` (``write_T_typed``)
     - ``arel false d pm x v`` and ``encodable k v``
     - ``JIT_OK``, having written ``asn1_enc k v``, or ``JIT_NO_SPACE``
   * - ``RelKeep.to_writer d pm x v`` (ghost)
     - ``arel true d pm x v``
     - ``arel false d pm x v``, and a trade back to ``arel true``

The Boolean in ``arel`` says whether the values of KEEP-BYTES types carry
their bytes: ``true`` for parsers, ``false`` for writers, which therefore
never require callers to reason about encodings. Without KEEP-BYTES,
the two relations coincide. ``parsed_encodable_d`` states that every
parsed value is encodable and that its encoding is the parsed input, so
parsing and then writing back round-trips.

Specification theorems
^^^^^^^^^^^^^^^^^^^^^^

The specification (``lib/everparse/asn1/spec``) also proves:

* **Conformance** (``ASN1.Spec.Conformance``): for every well-formed
  schema ``k``, the typed parser accepts an input iff the generic ANY
  parser accepts it with a value that conforms to ``k``.
* **Serialization** (``ASN1.Spec.Serializer``): ``asn1_enc k`` is a total
  encoder, ``serialize_asn1 k`` is a LowParse serializer, and every parsed
  value is encodable.
* **Raw values** (``ASN1.Spec.Raw*``): constraint-free values, with
  ``check`` and ``forget`` between them and typed values.

Limitations
-----------

Specification and library
^^^^^^^^^^^^^^^^^^^^^^^^^

* **Not supported:** REAL, extensible types (``...`` in SEQUENCE, SET,
  CHOICE or ENUMERATED), recursive types, and encodings other than DER
  (BER, CER, PER, XER...).
* **Not checked:**

  * the DER rule on trailing zero bits of BIT STRINGs with named bits
    (X.690 11.2.2);
  * the contents of TeletexString, VideotexString, GraphicString,
    GeneralString and ObjectDescriptor (ISO 2022);
  * OID-IRI labels, beyond UTF-8 validity.

* **Bounds:** lengths are below :math:`2^{32}`; SIZE bounds are below
  65536; SET has at most 64 components.
* SEQUENCE OF / SET OF support no SIZE constraint other than
  ``SIZE (1..MAX)`` (see ``--lax_size_of``).
* SIZE constraints must be a single range; permitted alphabet (``FROM``)
  and ``PATTERN`` constraints are not supported; value sets and single
  values are only supported on INTEGER, ENUMERATED and BOOLEAN.
* DEFAULT is only supported on terminal types (not on SEQUENCE, SET,
  CHOICE, SEQUENCE OF or SET OF), and not on EXPLICIT-tagged constrained
  INTEGER or ENUMERATED.
* ANY cannot be a CHOICE alternative.

The ``everparse-asn1`` front end
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The front end rejects with an error the constructs listed above, and
also:

* ``--#DEFINED-BY`` tables and table constraints on SET or CHOICE; with
  a key that is OPTIONAL, constrained or RELATIVE-OID; with a dependent
  component before the key; with several keys or several tables in one
  SEQUENCE; or with a key in another SEQUENCE than the dependent
  component.
* KEEP-BYTES on a CHOICE alternative, on a DEFAULT component, or on the
  key and dependent components of a DEFINED-BY table. A CHOICE
  alternative of a KEEP-BYTES type does not keep its bytes (with a
  warning).
* Information object classes beyond type fields selected by a key:
  value fields selected by a key, value set, object and object set
  fields, variable-type value fields, parameterized object sets, and
  DEFAULT on a dependent component. Two objects with the same ``UNIQUE``
  key are not reported (the first one wins).
* Parameterized values, value sets, objects and object sets; recursive
  parameterized instances.
* ``ENCODED BY`` with an encoding other than DER.
* Ambiguous schemas are reported by F\* (``seq_tac`` / ``set_tac``), not
  by the front end.

C API
^^^^^

* No C iterator is generated for parsed SEQUENCE OF / SET OF lists: the
  caller walks the payload, which is a sequence of validated TLVs.
* ``validate_T``, ``parse_T`` and the writers are only generated for root
  types (``--root``).
* The names of the generic C types, such as
  ``Pulse_Lib_Slice_slice__uint8``, are generated by Custard and may
  change across versions.
* No per-type introduction lemmas are generated for the writer relation
  ``raw_varel``: a verified Pulse caller of ``write_T`` has to unfold it.

Testing
-------

Besides proofs, the ASN.1 support is tested (``make asn1-test`` in the
EverParse source tree):

* on 14620 X.509 certificates and 6154 CRLs, with no mismatch between the
  specification and the C validators and parsers, and with encoder round
  trips;
* against three third-party ASN.1 libraries (asn1tools, rasn, asn1-rs),
  on hand-written vectors and generated DER mutations;
* on nested ANY values 4000 deep, under a 64 KiB stack;
* with the C tests of ``share/everparse/tests/asn1``, which can also run
  against an installed EverParse.

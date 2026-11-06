# Triage of the differential test discrepancies

`known.json` records every discrepancy between an implementation and the
X.690 verdict, with its evidence. This file groups them by root cause and
drafts upstream bug reports. We have filed none of them; `upstream` is
`null` in every entry. Some are already known upstream: see "Prior reports"
below.

Versions: asn1tools 0.169.0 (`der` codec), rasn 0.29.0 with rasn-compiler
0.16, asn1-rs 0.7.2. The counts include the generated `mut/...` vectors.
Our parser agrees with every expected verdict.

## Root causes

| Implementation | Root cause | Vectors | Example |
|---|---|---|---|
| asn1tools | **DoS**: the SEQUENCE OF / SET OF decoder loops forever, with unbounded memory, on an element with the wrong tag | 10 | `intseq/reject/wrong-element` |
| asn1tools | non-minimal lengths accepted | 138 | `smoke/reject/length-long-form` |
| asn1tools | BER SEQUENCE/SET decoding: components in any order, unknown and trailing components, inner overrun | 31 | `seq/reject/out-of-order` |
| asn1tools | invalid contents escape as uncaught Python exceptions (`UnicodeDecodeError`, `ValueError`, `IndexError`) | 27 | `utf8/reject/0` |
| asn1tools | indefinite length accepted | 23 | `seq/reject/indefinite` |
| asn1tools | non-minimal or empty INTEGER / ENUMERATED | 6 | `int/reject/leading-00` |
| asn1tools | BOOLEAN other than 00/FF | 5 | `bool/reject/true-01` |
| asn1tools | BIT STRING unused bits not checked | 4 | `bits/reject/unused-8` |
| asn1tools | DATE / TIME-OF-DAY: year < 1582, missing seconds | 3 | `date/reject/15811231` |
| asn1tools | primitive/constructed bit not checked (tagged members, ObjectDescriptor) | 2 | `seq/reject/c-constructed` |
| asn1tools | DEFAULT value encoded explicitly | 2 | `seq/reject/default-encoded` |
| asn1tools | non-minimal OID subidentifiers | 2 | `oid/reject/leading-80` |
| asn1tools | non-minimal tag numbers in ANY | 2 | `any/reject/tag-nonminimal` |
| asn1tools | SET OF order not checked | 1 | `nonemptysetof/reject/unsorted` |
| asn1tools | EXTERNAL `single-ASN1-type` expected with an IMPLICIT tag (valid EXPLICIT encoding rejected) | 1 | `external/accept/single-asn1-type` |
| rasn | non-minimal lengths accepted | 127 | `smoke/reject/length-long-form` |
| rasn | non-minimal tag numbers accepted | 100 | `highctx/reject/tag-nonminimal` |
| rasn | primitive/constructed bit not checked | 28 | `int/reject/constructed` |
| rasn | non-minimal INTEGER / ENUMERATED | 5 | `int/reject/leading-00` |
| rasn | SET OF order not checked | 4 | `octetsset/reject/unsorted` |
| rasn | SET component order not checked | 3 | `set/reject/a-b-c` |
| rasn | UniversalString decoded as UTF-8 | 3 | `universal/accept/2` |
| rasn | rasn-compiler generates RELATIVE-OID with the OID tag | 3 | `reloid/accept/1.2.3` |
| rasn | GeneralizedTime fraction with a trailing 0 | 2 | `gen/reject/20250101120000.50Z` |
| rasn | DEFAULT value encoded explicitly | 2 | `seq/reject/default-encoded` |
| rasn | non-minimal OID subidentifiers | 2 | `oid/reject/leading-80` |
| rasn | BIT STRING unused bits not zero | 1 | `bits/reject/unused-bits-nonzero` |
| asn1-rs | **panic** on an empty BOOLEAN | 1 | `bool/reject/empty` |
| asn1-rs | non-minimal lengths accepted | 124 | `smoke/reject/length-long-form` |
| asn1-rs | non-minimal tag numbers accepted | 101 | `highctx/reject/tag-nonminimal` |
| asn1-rs | primitive/constructed bit not checked | 40 | `seq/reject/primitive` |
| asn1-rs | trailing components accepted (derive, TaggedExplicit) | 16 | `seq/reject/extra-component` |
| asn1-rs | UTCTime / GeneralizedTime: missing seconds, offsets, fractions, invalid dates | 11 | `utc/reject/250230120000Z` |
| asn1-rs | `Oid` checks neither its tag nor its contents | 7 | `algid/reject/no-oid` |
| asn1-rs | SET OF order not checked | 3 | `octetsset/reject/unsorted` |
| asn1-rs | DEFAULT value encoded explicitly | 2 | `seq/reject/default-encoded` |
| asn1-rs | BMPString odd length, VisibleString DEL | 2 | `bmp/reject/0` |
| asn1-rs | the DER check runs before the tag check, rejecting a valid SEQUENCE with an absent OPTIONAL | 1 | `seq/accept/a-d` |
| asn1-rs | BIT STRING unused-bits octet > 7 | 1 | `bits/reject/unused-8` |
| asn1-rs | non-minimal ENUMERATED | 1 | `enum/reject/leading-00` |
| asn1-rs | BOOLEAN other than 00/FF under an IMPLICIT tag | 1 | `set/reject/b-not-ff` |

The remaining entries are not bugs:

* `policy` (2): our parser bounds OID arcs to 32 bits.
* `ambiguity` (13):
  * leap seconds (`utc/accept/161231235960Z`, `tod/accept/235960`,
    `utc/reject/250101120060Z`);
  * a lone surrogate in a BMPString (`bmp/reject/1`);
  * the AlgId table constraint (`algid/reject/123-*`), which the plain
    `ANY DEFINED BY` schema given to the other tools cannot express.

## Prior reports

We checked every issue (open and closed) in eerimoq/asn1tools,
librasn/rasn, librasn/compiler and rusticata/asn1-rs on 2026-10-27, as well
as the source comments and user documentation of the tested versions. No
project's user documentation mentions any of these gaps.

| Draft | GitHub issue | Source comment |
|---|---|---|
| asn1tools: SEQUENCE OF infinite loop | eerimoq/asn1tools#180 (open): the same root cause (`der.py:92`, `TAG_MISMATCH` without advancing), triggered there by valid CHOICE data | — |
| asn1tools: `der` codec does not enforce DER | Partly: eerimoq/asn1tools#186 (open) covers only the uncaught `UnicodeDecodeError`. Related but different: eerimoq/asn1tools#162 (top-level trailing bytes; closed, use `decode_with_length`) and eerimoq/asn1tools#195 (SET OF *encoding* order) | `ber.py:769`: "Extra data is allowed in cases of versioned additions" |
| rasn: UniversalString as UTF-8 | none | — |
| rasn-compiler: RELATIVE-OID as OID | none | The type lexer maps both keywords to `ASN1Type::ObjectIdentifier` (`lexer/object_identifier.rs:47-55`). The only TODO is for OID *values*: "store info whether the object id is relative" (`:40`) |
| rasn: `der()` does not enforce DER | none. Related but different: librasn/rasn#552 (top-level trailing bytes; fixed by librasn/rasn#562, after 0.29.0) | `src/ber/de.rs:347-349`: redundant INTEGER sign octets are accepted on purpose ("BER data in the wild carries them"), also in DER |
| asn1-rs: empty BOOLEAN panic | rusticata/asn1-rs#142 (open): exact match, including the constraint-before-tag ordering; fix in rusticata/asn1-rs#145 (open) | — |
| asn1-rs: `Oid` unchecked | Partly: rusticata/asn1-rs#150 (open) covers the subidentifiers (leading 0x80, truncated), not the missing tag check | `oid.rs:57`: "check that any.data.last().unwrap() >> 7 == 0u8" |
| asn1-rs: header and derive | Partly: rusticata/asn1-rs#149 (open) covers non-minimal tags and lengths | `XXX` on length minimality (`header.rs:306`), derive trailing contents (asn1-rs-derive 0.6.0 `container.rs:171`, "XXX check if empty?"), IMPLICIT constructed bit (`tagged/implicit.rs:111-126`), UTCTime seconds (`utctime.rs:27`) |

Not documented anywhere, and so the first to file:

* rasn: UniversalString; RELATIVE-OID (rasn-compiler); length and tag
  minimality; the constructed bit; unused bits; DEFAULT; SET and SET OF
  order; GeneralizedTime fractions.
* asn1tools: indefinite and non-minimal lengths; BOOLEAN; INTEGER; unused
  bits; out-of-order and unknown components; DEFAULT; SET OF order.
* asn1-rs: the `Oid` tag check; DEFAULT; `SetOf` order; the constructed bit
  of SEQUENCE and NULL; BMPString odd length; VisibleString DEL;
  ENUMERATED minimality; BIT STRING unused-bits octet > 7.

## Upstream report drafts

Each draft is minimal, and its reproducer is a vector id. Drafts already
fully reported upstream are omitted: the asn1tools SEQUENCE OF infinite
loop (eerimoq/asn1tools#180) and the asn1-rs empty-BOOLEAN panic
(rusticata/asn1-rs#142). The others are trimmed to what prior reports do
not cover.

### asn1tools: the `der` codec does not enforce DER

The `der` codec reuses the BER decoders for BOOLEAN, ENUMERATED, OBJECT
IDENTIFIER, SEQUENCE, SET, SET OF and ANY (`codecs/der.py:17-31`). It
accepts:

* non-minimal lengths and the indefinite length (X.690 10.1);
* BOOLEAN contents other than 00/FF (11.1);
* non-minimal INTEGER (8.3.2);
* nonzero unused bits (11.2.1);
* out-of-order and unknown SEQUENCE/SET components (X.680 25, 27; X.690
  10.3);
* explicitly encoded DEFAULTs (11.5);
* unsorted SET OF (11.6).

Invalid time contents raise `ValueError`, and invalid BIT STRING and OID
contents `IndexError`, instead of `asn1tools.DecodeError`. (The
`UnicodeDecodeError` case is eerimoq/asn1tools#186.)

### rasn: UniversalString decoded as UTF-8

`src/types.rs:55` defines `UniversalString = Implicit<UNIVERSAL_STRING,
Utf8String>`. X.690 8.23.7 encodes UniversalString as UCS-4 (4 octets per
character), so valid values such as `1c040001f600` (U+1F600) are rejected,
and invalid ones such as `1c03000041` are accepted.

### rasn-compiler: RELATIVE-OID generated as OBJECT IDENTIFIER

For `T ::= RELATIVE-OID`, rasn-compiler 0.16 generates a delegate of
`ObjectIdentifier`, with universal tag 6. rasn then rejects `0d03010203`
and accepts `0603010203`. The generated type should use rasn's
`RelativeOid` (tag 13).

### rasn: `DecoderOptions::der()` does not enforce DER

With `DecoderOptions::der()`, rasn accepts:

* non-minimal lengths (`src/ber/de/parser.rs:206-213`, X.690 10.1);
* tag numbers below 31 in the high form, and high tag numbers with leading
  0x80 octets (`parser.rs:145-146,176`, X.690 8.1.2.2, 8.1.2.4.2);
* constructed INTEGER/NULL/OID and constructed IMPLICIT-tagged primitives
  (8.1.2.5);
* non-minimal INTEGER, whose redundant octets are dropped
  (`src/ber/de.rs:347-351`, 8.3.2);
* nonzero unused bits (11.2.1);
* GeneralizedTime fractions with a trailing 0 (11.7.3);
* explicitly encoded DEFAULTs (11.5);
* unsorted SET OF (11.6);
* SET components out of canonical order (10.3).

### asn1-rs: valid SEQUENCE rejected after an absent OPTIONAL BOOLEAN

The blanket `FromDer` runs `CheckDerConstraints::check_constraints`
before the tag check in `try_from` (`src/traits.rs:192`). In a
`DerSequence` with an absent OPTIONAL or DEFAULT BOOLEAN, the BOOLEAN's DER
check therefore runs on the *next* component, which then fails when its
tag number is 1 in another class (`seq/accept/a-d`). rusticata/asn1-rs#142
reports the resulting panic on an empty BOOLEAN and mentions the ordering,
but not this rejection of valid input.

### asn1-rs: `Oid` does not check its tag

`Oid::try_from(&Any)` (`src/asn1_types/oid.rs:56-60`) does not check the
tag, so `Oid::from_der(&[0x05, 0x00])` (a NULL) succeeds (`algid/reject/no-oid`).
The empty OID is also accepted. rusticata/asn1-rs#150 covers the other
content checks (leading 0x80, truncated subidentifier).

### asn1-rs: DER checks missing in the derive and types

Non-minimal lengths and tags are rusticata/asn1-rs#149. Not covered there:

* The primitive/constructed bit is not checked for most types.
* The `DerSequence`/`DerSet` derive and `TaggedExplicit` ignore trailing
  contents.
* `#[default]` accepts an explicitly encoded DEFAULT.
* `SetOf` does not check the order.
* UTCTime/GeneralizedTime accept missing seconds, offsets and invalid dates
  in DER.

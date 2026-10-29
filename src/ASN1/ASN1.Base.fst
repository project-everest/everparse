module ASN1.Base
open LowParse.Tot.Base
open LowParse.Tot.Combinators

open ASN1.Bytes
open ASN1.Spec.Time
open ASN1.Spec.IRI
open ASN1.Spec.Content.INTEGER

// ASN.1 Kinds

module U32 = FStar.UInt32
module I32 = FStar.Int32
module U8 = FStar.UInt8
module Seq = FStar.Seq
module List = FStar.List.Tot

// ASN.1 Identifier

type asn1_id_class_t =
| UNIVERSAL
| APPLICATION
| CONTEXT_SPECIFIC
| PRIVATE

type asn1_id_flag_t = 
| PRIMITIVE
| CONSTRUCTED

type asn1_id_value_t = U32.t

type asn1_id_t =
| MK_ASN1_ID : c : asn1_id_class_t -> f : asn1_id_flag_t -> v : asn1_id_value_t -> asn1_id_t

// The canonical order of tags (X.690 10.3, 8.6): by class (UNIVERSAL,
// APPLICATION, CONTEXT-SPECIFIC, PRIVATE), then by tag number. The
// primitive/constructed flag is not part of the tag.
let asn1_id_class_rank (c : asn1_id_class_t) : nat =
  match c with
  | UNIVERSAL -> 0
  | APPLICATION -> 1
  | CONTEXT_SPECIFIC -> 2
  | PRIVATE -> 3

let asn1_tag_lt (a b : asn1_id_t) : bool =
  let ra = asn1_id_class_rank a.c in
  let rb = asn1_id_class_rank b.c in
  ra < rb || (ra = rb && U32.lt a.v b.v)

let asn1_same_tag (a b : asn1_id_t) : bool =
  a.c = b.c && a.v = b.v

//TODO: constant tables (Currently in X.509)

//ASN.1 kinds and High-level types

//Can we describe the correspondence between the kind and the type by defining a function that maps a kind to its type. In that way, we can get the parsers from the partial computation of the function on a template which is slick.

//A hack for dependency on default

type asn1_terminal_k : Type =
| ASN1_BOOLEAN
| ASN1_INTEGER : (bound : pos) -> asn1_terminal_k
// ENUMERATED has the contents encoding of INTEGER (X.690 8.4); see
// ASN1.Syntax.asn1_enumerated
| ASN1_BITSTRING
| ASN1_OCTETSTRING
| ASN1_PRINTABLESTRING
| ASN1_UTF8STRING
| ASN1_IA5STRING
| ASN1_VISIBLESTRING
| ASN1_BMPSTRING
| ASN1_UNIVERSALSTRING
| ASN1_TELETEXSTRING
| ASN1_NUMERICSTRING
| ASN1_VIDEOTEXSTRING
| ASN1_GRAPHICSTRING
| ASN1_GENERALSTRING
| ASN1_OBJECTDESCRIPTOR
| ASN1_NULL
| ASN1_OID
| ASN1_RELATIVE_OID
| ASN1_OID_IRI
| ASN1_RELATIVE_OID_IRI
| ASN1_UTCTIME
| ASN1_GENERALIZEDTIME
| ASN1_DATE
| ASN1_TIME_OF_DAY
| ASN1_DATE_TIME
| ASN1_PREFIXED_TERMINAL : asn1_id_t -> asn1_terminal_k -> asn1_terminal_k

type asn1_boolean_t = bool

type asn1_integer_t (bound : pos) = integer_in_interval bound

let rec pow2_mono (n m:nat)
: Lemma
  (requires n < m)
  (ensures pow2 n < pow2 m)
= if n + 1 = m then () else pow2_mono n (m - 1)
let pow2_le (n:nat {n < 8}) : Lemma (pow2 n < 256) = pow2_mono n 8

//Bitstring is represented as an array of bytes and 0~7 unused bits
type asn1_bitstring_t = 
| BYTES_WITH_UNUSEDBITS :
  unused : U8.t {0 <= (U8.v unused) /\ (U8.v unused) <= 7} ->
  b : asn1_bytes {let _ = pow2_le (U8.v unused) in
               (U8.v unused = 0) \/ 
               ((U8.v unused > 0) /\ Seq.length b > 0 /\ 
                FStar.UInt.mod (U8.v (Seq.index b ((Seq.length b) - 1))) (pow2 (U8.v unused)) = 0)} -> asn1_bitstring_t
//TODO: use bit op

type asn1_octetstring_t = asn1_bytes

(* Well-formed UTF-8 (RFC 3629): no overlong forms, surrogates, or code
   points above U+10FFFF. *)
type asn1_utf8string_t = (b : asn1_bytes {LowParse.Spec.UTF8.correct b})

let is_printable_char (ch : U8.t) : bool =
  let v = U8.v ch in
  (65 <= v && v <= 90) ||  // A - Z
  (97 <= v && v <= 122) || // a - z
  (48 <= v && v <= 57) ||  // 0 - 9
  v = 32 ||              // (space)
  (39 <= v && v <= 41) ||  // '()
  (43 <= v && v <= 47) ||  // +,-./
  v = 58 || v = 61 || v = 63 // :=?

type asn1_printablestring_t = list (b : byte {is_printable_char b})

let is_ia5_char (ch : U8.t) : bool = U8.v ch < 128

type asn1_ia5string_t = list (b : byte {is_ia5_char b})

(* X.680 §41.4: VisibleString is ISO 646 graphic characters plus space. *)
let is_visible_char (ch : U8.t) : bool = 32 <= U8.v ch && U8.v ch <= 126

type asn1_visiblestring_t = list (b : byte {is_visible_char b})

(* BMPString (X.690 §8.23.8): big-endian UCS-2 code units. Surrogate code
   points (U+D800..U+DFFF) are not characters, so they are rejected. *)
let rec is_valid_bmp_from (b : asn1_bytes) (i : nat {i <= Seq.length b})
: Tot bool (decreases (Seq.length b - i))
= if i = Seq.length b then true
  else if i + 2 > Seq.length b then false
  else
    let hi = U8.v (Seq.index b i) in
    not (0xD8 <= hi && hi <= 0xDF) && is_valid_bmp_from b (i + 2)

let is_valid_bmp (b : asn1_bytes) : bool = is_valid_bmp_from b 0

type asn1_bmpstring_t = (b : asn1_bytes {is_valid_bmp b})

(* UniversalString (X.690 §8.23.7): big-endian UCS-4 code units, each a
   Unicode scalar value (at most U+10FFFF, not a surrogate). *)
let rec is_valid_universal_from (b : asn1_bytes) (i : nat {i <= Seq.length b})
: Tot bool (decreases (Seq.length b - i))
= if i = Seq.length b then true
  else if i + 4 > Seq.length b then false
  else
    let b0 = U8.v (Seq.index b i) in
    let b1 = U8.v (Seq.index b (i + 1)) in
    let b2 = U8.v (Seq.index b (i + 2)) in
    b0 = 0 && b1 <= 0x10 && not (b1 = 0 && 0xD8 <= b2 && b2 <= 0xDF) &&
    is_valid_universal_from b (i + 4)

let is_valid_universal (b : asn1_bytes) : bool = is_valid_universal_from b 0

type asn1_universalstring_t = (b : asn1_bytes {is_valid_universal b})

(* TeletexString (T.61) has no practical validity rule; its content is kept
   as raw bytes. *)
type asn1_teletexstring_t = asn1_bytes

(* NumericString (X.680 41.2): digits and space. *)
let is_numeric_char (ch : U8.t) : bool =
  let v = U8.v ch in
  (48 <= v && v <= 57) || v = 32

type asn1_numericstring_t = list (b : byte {is_numeric_char b})

(* VideotexString, GraphicString, GeneralString (ISO 2022 based, X.680 41)
   and ObjectDescriptor ([UNIVERSAL 7] IMPLICIT GraphicString, X.680 48)
   have no practical validity rule either; their contents are kept as raw
   bytes. *)
type asn1_videotexstring_t = asn1_bytes
type asn1_graphicstring_t = asn1_bytes
type asn1_generalstring_t = asn1_bytes
type asn1_objectdescriptor_t = asn1_bytes

type asn1_null_t = unit

let asn1_OID_wf' (value1 value2 : U32.t) =
  (U32.v value1 < 2 && U32.v value2 < 40) || (U32.v value1 = 2 && U32.v value2 < pow2 32 - 80)

let asn1_OID_wf (l : list U32.t) =
  List.length l >= 2 &&
  (match l with
  | value1 :: value2 :: tl -> asn1_OID_wf' value1 value2)

type asn1_oid_t = 
  (l : list U32.t {asn1_OID_wf l})

(* RELATIVE-OID (X.690 8.20): a non-empty list of subidentifiers. *)
let asn1_relative_oid_wf (l : list U32.t) : bool = Cons? l

type asn1_relative_oid_t = (l : list U32.t {asn1_relative_oid_wf l})

type asn1_oid_iri_t = (b : asn1_bytes {is_valid_oid_iri b})

type asn1_relative_oid_iri_t = (b : asn1_bytes {is_valid_relative_oid_iri b})

type asn1_utctime_t = (b : asn1_bytes {is_valid_ASN1UTCTIME b})

type asn1_generalizedtime_t = (b : asn1_bytes {is_valid_ASN1GENERALIZEDTIME b})

type asn1_date_t = (b : asn1_bytes {is_valid_ASN1DATE b})

type asn1_time_of_day_t = (b : asn1_bytes {is_valid_ASN1TIMEOFDAY b})

type asn1_date_time_t = (b : asn1_bytes {is_valid_ASN1DATETIME b})

let rec asn1_terminal_t (k : asn1_terminal_k) : eqtype =
  match k with
  | ASN1_BOOLEAN -> asn1_boolean_t
  | ASN1_INTEGER bound -> asn1_integer_t bound
  | ASN1_BITSTRING -> asn1_bitstring_t
  | ASN1_OCTETSTRING -> asn1_octetstring_t
  | ASN1_UTF8STRING -> asn1_utf8string_t
  | ASN1_PRINTABLESTRING -> asn1_printablestring_t
  | ASN1_IA5STRING -> asn1_ia5string_t
  | ASN1_VISIBLESTRING -> asn1_visiblestring_t
  | ASN1_BMPSTRING -> asn1_bmpstring_t
  | ASN1_UNIVERSALSTRING -> asn1_universalstring_t
  | ASN1_TELETEXSTRING -> asn1_teletexstring_t
  | ASN1_NUMERICSTRING -> asn1_numericstring_t
  | ASN1_VIDEOTEXSTRING -> asn1_videotexstring_t
  | ASN1_GRAPHICSTRING -> asn1_graphicstring_t
  | ASN1_GENERALSTRING -> asn1_generalstring_t
  | ASN1_OBJECTDESCRIPTOR -> asn1_objectdescriptor_t
  | ASN1_NULL -> asn1_null_t
  | ASN1_OID -> asn1_oid_t
  | ASN1_RELATIVE_OID -> asn1_relative_oid_t
  | ASN1_OID_IRI -> asn1_oid_iri_t
  | ASN1_RELATIVE_OID_IRI -> asn1_relative_oid_iri_t
  | ASN1_UTCTIME -> asn1_utctime_t
  | ASN1_GENERALIZEDTIME -> asn1_generalizedtime_t
  | ASN1_DATE -> asn1_date_t
  | ASN1_TIME_OF_DAY -> asn1_time_of_day_t
  | ASN1_DATE_TIME -> asn1_date_time_t
  | ASN1_PREFIXED_TERMINAL _ k -> asn1_terminal_t k

(* Literals for the keys of ANY DEFINED BY. `asn1_bytes` is abstract, so a
   constant of a type based on it does not reduce to a literal that the
   Pulse validators could compare with the input. So, the keys of the
   supported cases of ANY DEFINED BY are given as lists of bytes instead,
   and mapped to their values by `key_of_lit`. Kinds not based on
   `asn1_bytes` use their own values. *)

let asn1_bitstring_lit_wf (unused : U8.t) (b : asn1_bytes) : prop =
  0 <= U8.v unused /\ U8.v unused <= 7 /\
  (let _ = pow2_le (U8.v unused) in
   (U8.v unused = 0) \/
   ((U8.v unused > 0) /\ Seq.length b > 0 /\
    FStar.UInt.mod (U8.v (Seq.index b ((Seq.length b) - 1))) (pow2 (U8.v unused)) = 0))

type asn1_bitstring_lit = (x : (U8.t & list U8.t) { asn1_bitstring_lit_wf (fst x) (Seq.seq_of_list (snd x)) })

type asn1_bytes_lit (p : asn1_bytes -> Tot bool) = (l : list U8.t { p (Seq.seq_of_list l) })

let asn1_bytes_any (b : asn1_bytes) : Tot bool = true

(* INTEGER literals: the DER content bytes (minimal two's complement,
   big-endian), so that arbitrarily large keys are supported. *)

let int_lit_ok (bound : pos) (l : list U8.t) : Tot bool =
  let n = List.length l in
  n > 0 && n <= bound &&
  (match l with
   | c0 :: c1 :: _ -> not ((c0 = 0uy && c1 `U8.lt` 128uy) || (c0 = 255uy && 127uy `U8.lt` c1))
   | _ -> true)

type asn1_int_lit (bound : pos) = (l : list U8.t { int_lit_ok bound l })

let int_lit_valid (bound : pos) (l : asn1_int_lit bound)
: Lemma (valid_unsigned_repr (Seq.seq_of_list l) /\ Seq.length (Seq.seq_of_list l) <= bound)
= match l with
  | c0 :: tl ->
    Seq.lemma_seq_of_list_induction l;
    begin match tl with
    | c1 :: _ -> Seq.lemma_seq_of_list_induction tl
    | _ -> ()
    end

let int_of_lit (bound : pos) (l : asn1_int_lit bound) : Tot (integer_in_interval bound) =
  int_lit_valid bound l;
  let b = Seq.seq_of_list l in
  mk_integer'_eq' b;
  let r = mk_integer' b in
  interval_intro (Seq.length b) r;
  interval_weaken (Seq.length b) bound r;
  r

let int_of_lit_inj (bound : pos) (l1 l2 : asn1_int_lit bound)
: Lemma (requires (int_of_lit bound l1 == int_of_lit bound l2)) (ensures (l1 == l2))
= int_lit_valid bound l1;
  int_lit_valid bound l2;
  mk_integer'_inj (Seq.seq_of_list l1) (Seq.seq_of_list l2);
  Seq.lemma_list_seq_bij l1;
  Seq.lemma_list_seq_bij l2

let rec asn1_key_lit (k : asn1_terminal_k) : eqtype =
  match k with
  | ASN1_INTEGER bound -> asn1_int_lit bound
  | ASN1_BITSTRING -> asn1_bitstring_lit
  | ASN1_OCTETSTRING
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR -> asn1_bytes_lit asn1_bytes_any
  | ASN1_UTF8STRING -> asn1_bytes_lit LowParse.Spec.UTF8.correct
  | ASN1_BMPSTRING -> asn1_bytes_lit is_valid_bmp
  | ASN1_UNIVERSALSTRING -> asn1_bytes_lit is_valid_universal
  | ASN1_OID_IRI -> asn1_bytes_lit is_valid_oid_iri
  | ASN1_RELATIVE_OID_IRI -> asn1_bytes_lit is_valid_relative_oid_iri
  | ASN1_UTCTIME -> asn1_bytes_lit is_valid_ASN1UTCTIME
  | ASN1_GENERALIZEDTIME -> asn1_bytes_lit is_valid_ASN1GENERALIZEDTIME
  | ASN1_DATE -> asn1_bytes_lit is_valid_ASN1DATE
  | ASN1_TIME_OF_DAY -> asn1_bytes_lit is_valid_ASN1TIMEOFDAY
  | ASN1_DATE_TIME -> asn1_bytes_lit is_valid_ASN1DATETIME
  | ASN1_PREFIXED_TERMINAL _ k -> asn1_key_lit k
  | _ -> asn1_terminal_t k

#push-options "--fuel 2 --ifuel 2"
let rec key_of_lit (k : asn1_terminal_k) (x : asn1_key_lit k) : Tot (asn1_terminal_t k) (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id' k' ->
    assert_norm (asn1_key_lit (ASN1_PREFIXED_TERMINAL id' k') == asn1_key_lit k');
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id' k') == asn1_terminal_t k');
    let x' : asn1_key_lit k' = coerce_eq #(asn1_key_lit k) #(asn1_key_lit k') () x in
    coerce_eq #(asn1_terminal_t k') #(asn1_terminal_t k) () (key_of_lit k' x')
  | ASN1_INTEGER bound -> int_of_lit bound x
  | ASN1_BITSTRING ->
    let x : asn1_bitstring_lit = x in
    BYTES_WITH_UNUSEDBITS (fst x) (Seq.seq_of_list (snd x))
  | ASN1_OCTETSTRING
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR
  | ASN1_UTF8STRING
  | ASN1_BMPSTRING
  | ASN1_UNIVERSALSTRING
  | ASN1_OID_IRI
  | ASN1_RELATIVE_OID_IRI
  | ASN1_UTCTIME
  | ASN1_GENERALIZEDTIME
  | ASN1_DATE
  | ASN1_TIME_OF_DAY
  | ASN1_DATE_TIME -> Seq.seq_of_list #U8.t x
  | _ -> x

let rec key_of_lit_inj (k : asn1_terminal_k) (x1 x2 : asn1_key_lit k)
: Lemma (requires (key_of_lit k x1 == key_of_lit k x2)) (ensures (x1 == x2)) (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id' k' ->
    assert_norm (asn1_key_lit (ASN1_PREFIXED_TERMINAL id' k') == asn1_key_lit k');
    key_of_lit_inj k' (coerce_eq #(asn1_key_lit k) #(asn1_key_lit k') () x1) (coerce_eq #(asn1_key_lit k) #(asn1_key_lit k') () x2)
  | ASN1_INTEGER bound -> int_of_lit_inj bound x1 x2
  | ASN1_BITSTRING ->
    let x1 : asn1_bitstring_lit = x1 in
    let x2 : asn1_bitstring_lit = x2 in
    Seq.lemma_list_seq_bij (snd x1);
    Seq.lemma_list_seq_bij (snd x2)
  | ASN1_OCTETSTRING
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR
  | ASN1_UTF8STRING
  | ASN1_BMPSTRING
  | ASN1_UNIVERSALSTRING
  | ASN1_OID_IRI
  | ASN1_RELATIVE_OID_IRI
  | ASN1_UTCTIME
  | ASN1_GENERALIZEDTIME
  | ASN1_DATE
  | ASN1_TIME_OF_DAY
  | ASN1_DATE_TIME ->
    Seq.lemma_list_seq_bij #U8.t x1;
    Seq.lemma_list_seq_bij #U8.t x2
  | _ -> ()

#pop-options

// Generic ASN.1 values (for ANY)

// Ref: X.680 8.4 Table 1
// Universal types with a DER content parser. ENUMERATED (10) has the
// same content encoding as INTEGER (X.690 8.4)
inline_for_extraction
let asn1_any_integer_bound : pos = 4294967295

let asn1_universal_terminal (v : asn1_id_value_t) : option asn1_terminal_k =
  match U32.v v with
  | 1 -> Some ASN1_BOOLEAN
  | 2 -> Some (ASN1_INTEGER asn1_any_integer_bound)
  | 3 -> Some ASN1_BITSTRING
  | 4 -> Some ASN1_OCTETSTRING
  | 5 -> Some ASN1_NULL
  | 6 -> Some ASN1_OID
  | 7 -> Some ASN1_OBJECTDESCRIPTOR
  | 10 -> Some (ASN1_INTEGER asn1_any_integer_bound)
  | 12 -> Some ASN1_UTF8STRING
  | 13 -> Some ASN1_RELATIVE_OID
  | 18 -> Some ASN1_NUMERICSTRING
  | 19 -> Some ASN1_PRINTABLESTRING
  | 20 -> Some ASN1_TELETEXSTRING
  | 21 -> Some ASN1_VIDEOTEXSTRING
  | 22 -> Some ASN1_IA5STRING
  | 23 -> Some ASN1_UTCTIME
  | 24 -> Some ASN1_GENERALIZEDTIME
  | 25 -> Some ASN1_GRAPHICSTRING
  | 26 -> Some ASN1_VISIBLESTRING
  | 27 -> Some ASN1_GENERALSTRING
  | 28 -> Some ASN1_UNIVERSALSTRING
  | 30 -> Some ASN1_BMPSTRING
  | 31 -> Some ASN1_DATE
  | 32 -> Some ASN1_TIME_OF_DAY
  | 33 -> Some ASN1_DATE_TIME
  | 35 -> Some ASN1_OID_IRI
  | 36 -> Some ASN1_RELATIVE_OID_IRI
  | _ -> None

// Universal types whose encoding is always constructed: EXTERNAL (8),
// EMBEDDED PDV (11), SEQUENCE (16), SET (17), CHARACTER STRING (29)
let asn1_universal_always_constructed (v : asn1_id_value_t) : bool =
  let v = U32.v v in
  v = 8 || v = 11 || v = 16 || v = 17 || v = 29

// Ref: X.690 8.1.2, 10.2. Tag 0 is reserved for end-of-contents and tag
// 15 is reserved. In DER, all universal types other than the above
// always-constructed ones are primitive (in particular, no constructed
// strings.) Unassigned universal tags (> 36) are accepted in either form.
let asn1_any_id_valid (id : asn1_id_t) : bool =
  match id with
  | MK_ASN1_ID UNIVERSAL f v ->
    let n = U32.v v in
    n <> 0 && n <> 15 &&
    begin match f with
    | CONSTRUCTED -> asn1_universal_always_constructed v || n > 36
    | PRIMITIVE -> not (asn1_universal_always_constructed v)
    end
  | _ -> true

let asn1_any_id_t = (id : asn1_id_t { asn1_any_id_valid id == true })

// A generic ASN.1 DER value: the identifier, and either the raw primitive
// contents (which the ANY parser checks against the corresponding universal
// type, if known), or the list of the values in the constructed contents.
// Keeping the raw contents makes the value determine its DER encoding, so
// that conformance to a schema is a Boolean predicate on values (see
// ASN1.Spec.Conformance.)
type asn1_value =
| ASN1_VALUE_PRIMITIVE : (id : asn1_any_id_t) -> (v : asn1_octetstring_t) -> asn1_value
| ASN1_VALUE_CONSTRUCTED : (id : asn1_any_id_t) -> (l : list asn1_value) -> asn1_value

type asn1_decorator : Type =
| PLAIN
| OPTION
| DEFAULT

let id_dec = Set.set asn1_id_t & asn1_decorator
let id_decs = list id_dec

let rec asn1_sequence_k_wf' (li : id_decs) (s : Set.set asn1_id_t) : prop =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s', d) = hd in
    Set.disjoint s s' /\
    (match d with
    | PLAIN -> asn1_sequence_k_wf tl
    | _ -> asn1_sequence_k_wf' tl (Set.union s s'))

and asn1_sequence_k_wf (li : id_decs) : prop =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s', d) = hd in 
    match d with
    | PLAIN -> asn1_sequence_k_wf tl
    | OPTION | DEFAULT -> asn1_sequence_k_wf' tl s'

let my_as_set l = Set.as_set l

let proj2_of_3 (#a #b : Type) (#c : a -> b -> Type) (x : dtuple3 a (fun _ -> b) c) : a & b = 
  let (| xa, xb, _ |) = x in (xa, xb)

let rec asn1_any_prefix_k_wf' (ks : Set.set asn1_id_t) (li : id_decs) (s : Set.set asn1_id_t) : prop =
  match li with
  | [] -> Set.disjoint s ks
  | hd :: tl ->
    let (s', d) = hd in
    Set.disjoint s s' /\
    (match d with
    | PLAIN -> asn1_any_prefix_k_wf ks tl
    | OPTION | DEFAULT -> asn1_any_prefix_k_wf' ks tl (Set.union s s'))

and asn1_any_prefix_k_wf (ks : Set.set asn1_id_t) (li : id_decs) : prop =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s', d) = hd in 
    match d with
    | PLAIN -> asn1_any_prefix_k_wf ks tl
    | OPTION | DEFAULT -> asn1_any_prefix_k_wf' ks tl s'

// The components of a SET have distinct tags (X.680 27.3), regardless of the
// primitive/constructed flag.
let asn1_set_disjoint (s1 s2 : Set.set asn1_id_t) : prop =
  forall (i1 i2 : asn1_id_t) . (Set.mem i1 s1 /\ Set.mem i2 s2) ==> ~ (asn1_same_tag i1 i2)

let rec asn1_set_k_wf' (s : Set.set asn1_id_t) (li : id_decs) : prop =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s', _) = hd in
    asn1_set_disjoint s s' /\ asn1_set_k_wf' s tl

let rec asn1_set_k_wf (li : id_decs) : prop =
  match li with
  | [] -> True
  | hd :: tl ->
    let (s, _) = hd in
    asn1_set_k_wf' s tl /\ asn1_set_k_wf tl

// Value restrictions on terminals (X.680 49-51). Besides arbitrary
// predicates (RESTRICT_CUSTOM), the common restrictions are first-class,
// so that validator generators can implement them without inspecting
// F* functions.
noeq
type asn1_restriction (k : asn1_terminal_k) : Type =
// SingleValue / union of SingleValues, e.g. ENUMERATED, `version`
| RESTRICT_IN : values : list (asn1_terminal_t k) -> asn1_restriction k
// union of SingleValues on INTEGER (e.g. ENUMERATED)
| RESTRICT_INT_IN : values : list int -> asn1_restriction k
// ValueRange on INTEGER, with optional bounds (MIN, MAX)
| RESTRICT_INT_RANGE : lo : option int -> hi : option int -> asn1_restriction k
// SizeConstraint on OCTET STRING, with an optional upper bound (MAX)
| RESTRICT_SIZE : lo : nat -> hi : option nat -> asn1_restriction k
| RESTRICT_CUSTOM : is_valid : (asn1_terminal_t k -> bool) -> asn1_restriction k

let int_in_range (lo hi : option int) (x : int) : Tot bool =
  (match lo with None -> true | Some l -> l <= x) &&
  (match hi with None -> true | Some h -> x <= h)

let restriction_pred (#k : asn1_terminal_k) (r : asn1_restriction k) (x : asn1_terminal_t k) : Tot bool =
  match r with
  | RESTRICT_IN l -> List.mem x l
  | RESTRICT_INT_IN l ->
    (match k with
     | ASN1_INTEGER _ -> List.mem #int x l
     | _ -> false)
  | RESTRICT_INT_RANGE lo hi ->
    (match k with
     | ASN1_INTEGER _ -> int_in_range lo hi x
     | _ -> false)
  | RESTRICT_SIZE lo hi ->
    (match k with
     | ASN1_OCTETSTRING ->
       lo <= Seq.length #byte x &&
       (match hi with None -> true | Some h -> Seq.length #byte x <= h)
     | _ -> false)
  | RESTRICT_CUSTOM f -> f x

noeq //noextract
type asn1_content_k : Type =
| ASN1_RESTRICTED_TERMINAL : (k : asn1_terminal_k) -> (r : asn1_restriction k) -> asn1_content_k
| ASN1_TERMINAL : asn1_terminal_k -> asn1_content_k
| ASN1_SEQUENCE : asn1_gen_items_lk -> asn1_content_k
// `nonempty = true` encodes the `SIZE (1..MAX)` constraint
| ASN1_SEQUENCE_OF : nonempty : bool -> #s : _ -> asn1_k s -> asn1_content_k
// SET: the components are encoded in the canonical order of their tags
// (X.690 10.3), so the order of the components in the value (the same as
// for SEQUENCE) is the order of the declaration, not of the encoding.
| ASN1_SET : id_decs : id_decs -> items : asn1_gen_items_l id_decs -> pf : squash (asn1_set_k_wf id_decs) -> asn1_content_k
| ASN1_SET_OF : nonempty : bool -> #s : _ -> asn1_k s -> asn1_content_k
| ASN1_PREFIXED : #s : _ -> asn1_k s -> asn1_content_k
| ASN1_ANY_DEFINED_BY :
             id_decs_prefix : id_decs ->
             prefix:asn1_gen_items_l id_decs_prefix ->
             id : asn1_id_t ->
             key_k : asn1_terminal_k ->
             supported : list (asn1_key_lit key_k & asn1_gen_items_lk) -> 
             fallback : option asn1_gen_items_lk ->
             pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton id) id_decs_prefix) ->
             pf_sup : squash (List.noRepeats (List.map fst supported)) -> 
             asn1_content_k

// The complete ASN.1 kind is indexed by the set of valid first identifiers
// Note that length does not matter here
and asn1_k : Set.set asn1_id_t -> Type =
| ASN1_ILC : id : asn1_id_t -> asn1_content_k -> asn1_k (Set.singleton id)
| ASN1_CHOICE_ILC : choices : list (asn1_id_t & asn1_content_k) -> 
                    pf : squash (List.noRepeats (List.map fst choices)) -> 
                    asn1_k (my_as_set (List.map fst choices))
| ASN1_ANY_ILC : asn1_k (Set.complement (Set.empty))                   
                    
and asn1_decorated_k : Set.set asn1_id_t -> asn1_decorator -> Type =
| ASN1_PLAIN_ILC : #s : _ -> k : asn1_k s -> asn1_decorated_k s PLAIN
| ASN1_OPTION_ILC : #s : _ -> k : asn1_k s -> asn1_decorated_k s OPTION
| ASN1_DEFAULT_TERMINAL : id : asn1_id_t -> #k : asn1_terminal_k -> defaultv : asn1_terminal_t k -> asn1_decorated_k (Set.singleton id) DEFAULT
| ASN1_DEFAULT_RESTRICTED_TERMINAL : id : asn1_id_t -> #k : asn1_terminal_k -> r : asn1_restriction k -> 
                                     defaultv : asn1_terminal_t k {restriction_pred r defaultv = true} -> asn1_decorated_k (Set.singleton id) DEFAULT


and asn1_gen_items_l : id_decs -> Type0 = 
  | ASN1_GEN_ITEMS_NIL : asn1_gen_items_l []
  | ASN1_GEN_ITEMS_CONS : s:Set.set asn1_id_t -> d:asn1_decorator -> asn1_decorated_k s d -> 
                          tl:id_decs -> asn1_gen_items_l tl -> asn1_gen_items_l ((s, d)::tl)

and asn1_gen_items_lk : Type = (id_decs:id_decs { asn1_sequence_k_wf id_decs } & asn1_gen_items_l id_decs)


let asn1_gen_item_k : Type = s : Set.set asn1_id_t & d : asn1_decorator & asn1_decorated_k s d

let asn1_gen_items_k : Type = items : list (asn1_gen_item_k) & squash (asn1_sequence_k_wf (List.map proj2_of_3 items))


let mk_ASN1_GEN_ITEM (#s) (#d) (k : asn1_decorated_k s d) : asn1_gen_item_k =
  (| s, d, k |)

(* Conversions to go between asn1_gen_items_lk and asn1_get_items_k *)
let rec l_as_list (#i:id_decs) (l:asn1_gen_items_l i)
  : r:list asn1_gen_item_k { List.map proj2_of_3 r == i }
  = match l with
    | ASN1_GEN_ITEMS_NIL -> []
    | ASN1_GEN_ITEMS_CONS s d dd _ tl ->
      (| s, d, dd |) :: l_as_list tl

let lk_as_k (lk:asn1_gen_items_lk)
  : asn1_gen_items_k
  = let (| ids, l |) = lk in
    (| l_as_list l, () |)

let rec list_as_l (l:list asn1_gen_item_k)
  : asn1_gen_items_l (List.map proj2_of_3 l)
  = match l with
    | [] -> ASN1_GEN_ITEMS_NIL
    | hd::tl ->
      let (| i, d, dd |) = hd in
      ASN1_GEN_ITEMS_CONS i d dd _ (list_as_l tl)

let k_as_lk (k:asn1_gen_items_k)
  : asn1_gen_items_lk
  = let (| l, _ |) = k in
    (| _, list_as_l l |)

type default_tv (#a : eqtype) (v : a) =
| Default : default_tv v
| Nondefault  : v' : a{~(v' = v)} -> default_tv v

let v_of_default (#a : eqtype) (#v : a) (v' : default_tv v) : a =
  match v' with
  | Default -> v
  | Nondefault v'' -> v''

let rec assoc_slt (#xT: eqtype) (#yT : Type) (l : list (xT & yT)) (x : xT) :
  Lemma (requires Some? (List.assoc x l))
        (ensures (let Some y = (List.assoc x l) in y << l))
        (decreases l)
= match l with
  | (a, b) :: t -> if x = a then () else (assoc_slt t x)

let idlookup_t_postcond (#key : eqtype) (id : key) (lc : list (key & Type)) (t : Type) : GTot prop
= (t << lc \/ t == False)

let idlookup_t (#key : eqtype) (id : key) (lc : list (key & Type)) :
  Pure Type
  (requires True)
  (ensures fun t -> idlookup_t_postcond id lc t)
= let _ = List.assoc_mem id lc in
  let res = List.assoc id lc in
  match res with
  | Some t -> 
    let _ = List.assoc_memP_some id t lc in
    let _ = assoc_slt lc id in
    t  
  | None -> 
    let _ = List.assoc_memP_none id lc in
    False 

let idlookup_with_fallback_t_postcond (#key : eqtype) (id : key) (lc : list (key & Type)) (fb : Type) (t : Type) : GTot prop
= (t << lc \/ t == fb)

let idlookup_with_fallback_t (#key : eqtype) (id : key) (lc : list (key & Type)) (fb : Type) :
  Pure Type
  (requires True)
  (ensures fun t -> idlookup_with_fallback_t_postcond id lc fb t)
= let _ = List.assoc_mem id lc in
  let res = List.assoc id lc in
  match res with
  | Some t -> 
    let _ = List.assoc_memP_some id t lc in
    let _ = assoc_slt lc id in
    t  
  | None -> 
    let _ = List.assoc_memP_none id lc in
    fb

let make_gen_choice_type (#key : eqtype) (lc : list (key & Type)) = id : key & idlookup_t id lc

let make_gen_choice_type_with_fallback (#key : eqtype) (lc : list (key & Type)) (fb : Type) = id : key & idlookup_with_fallback_t id lc fb

let isNonEmpty (#t : Type) (l : list t)
= match l with
  | [] -> false
  | _ -> true

let list_size_ok (#t : Type) (nonempty : bool) (l : list t) : bool
= not nonempty || isNonEmpty l

let sized_list (nonempty : bool) (t : Type) = l : (list t) {list_size_ok nonempty l}

let rec asn1_content_t (k : asn1_content_k) : Tot Type (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' r -> parse_filter_refine (restriction_pred r)
  | ASN1_TERMINAL k' -> asn1_terminal_t k'
  | ASN1_SEQUENCE gitems -> asn1_sequence_t_core (dsnd gitems)
  | ASN1_SET _ items _ -> asn1_sequence_t_core items
  | ASN1_SEQUENCE_OF ne k' -> sized_list ne (asn1_t k')
  | ASN1_SET_OF ne k' -> sized_list ne (asn1_t k')
  | ASN1_PREFIXED k' -> asn1_t k'
  | ASN1_ANY_DEFINED_BY id_decs_prefix prefix id key_k ls ofb pf_wf pf_sup -> 
    let suffix_t =
      (match ofb with
      | None -> make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls)
      | Some fb -> make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls) (asn1_sequence_t_core (dsnd fb))) in
    asn1_sequence_any_t_core prefix suffix_t

and asn1_any_t_core (#lt : eqtype) (t : eqtype) (f : lt -> Tot t) (ls : list (lt & asn1_gen_items_lk)) : Tot (list (t & Type)) (decreases ls) =
  match ls with
  | [] -> [] 
  | h :: tl -> 
    let (x, y) = h in
    (f x, asn1_sequence_t_core (dsnd y)) :: asn1_any_t_core t f tl

and asn1_lc_t (lc : list (asn1_id_t & asn1_content_k)) : Tot (list (asn1_id_t & Type)) (decreases lc) =
  match lc with
  | [] -> [] 
  | h :: t -> 
    let (x, y) = h in
    (x, asn1_content_t y) :: (asn1_lc_t t)

and asn1_t (#s : _) (k : asn1_k s) : Tot Type (decreases k) =
  match k with
  | ASN1_ILC id k' -> asn1_content_t k'
  | ASN1_CHOICE_ILC lc pf -> make_gen_choice_type (asn1_lc_t lc)
  | ASN1_ANY_ILC -> asn1_value

and asn1_decorated_t_core #s #d (dk:asn1_decorated_k s d) : Tot Type  (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> asn1_t k
  | ASN1_OPTION_ILC k -> option (asn1_t k)
  | ASN1_DEFAULT_TERMINAL id defv -> default_tv defv
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv -> default_tv #(parse_filter_refine (restriction_pred r)) defv

and asn1_sequence_t_core #id_decs (items:asn1_gen_items_l id_decs) : Tot Type (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> unit
  | ASN1_GEN_ITEMS_CONS s d dd _ ASN1_GEN_ITEMS_NIL ->
    asn1_decorated_t_core dd
  | ASN1_GEN_ITEMS_CONS s d dd _ tl ->
    asn1_decorated_t_core dd & asn1_sequence_t_core tl

and asn1_sequence_any_t_core #id_decs (items : asn1_gen_items_l id_decs) (suffix_t : Type) : Tot Type (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> suffix_t
  | ASN1_GEN_ITEMS_CONS s d dd _ ASN1_GEN_ITEMS_NIL ->
    asn1_decorated_t_core dd & suffix_t
  | ASN1_GEN_ITEMS_CONS s d dd _ tl ->
    asn1_decorated_t_core dd & asn1_sequence_any_t_core tl suffix_t

(* It may be convenient to use these alternative but equivalent formulations in the rest of the development *)
let asn1_decorated_t (i:asn1_gen_item_k) : Type =
  let (| _, _, dk |) = i in
  asn1_decorated_t_core dk

let rec asn1_sequence_t (items:list asn1_gen_item_k) =
  match items with
  | [] -> unit
  | [hd] ->
    asn1_decorated_t hd
  | hd::tl -> 
    asn1_decorated_t hd & asn1_sequence_t tl

let rec asn1_sequence_t_core_equiv #id_decs (items:asn1_gen_items_l id_decs)
  : Lemma (ensures asn1_sequence_t_core items == asn1_sequence_t (l_as_list items))
          (decreases items)
  = match items with
    | ASN1_GEN_ITEMS_NIL -> ()
    | ASN1_GEN_ITEMS_CONS _ _ _ _ tl ->
      asn1_sequence_t_core_equiv tl

let rec asn1_sequence_t_core_equiv' (items:list asn1_gen_item_k)
  : Lemma (ensures asn1_sequence_t_core (list_as_l items) == asn1_sequence_t items)
          (decreases items)
  = match items with
    | [] -> ()
    | hd::tl -> asn1_sequence_t_core_equiv' tl


let rec asn1_any_t (#lt : eqtype) (t : eqtype) (f : lt -> Tot t) (ls : list (lt & asn1_gen_items_k)) : Tot (list (t & Type)) (decreases ls) =
  match ls with
  | [] -> [] 
  | h :: tl -> 
    let (x, y) = h in
    (f x, asn1_sequence_t (dfst y)) :: asn1_any_t _ f tl

let t_lk_as_t_k #t (ls:list (t & asn1_gen_items_lk))
  : list (t & asn1_gen_items_k)
  = List.map (fun (t, lk) -> t, lk_as_k lk) ls

let t_k_as_t_lk #t (ls:list (t & asn1_gen_items_k))
  : list (t & asn1_gen_items_lk)
  = List.map (fun (t, k) -> t, k_as_lk k) ls

let rec asn1_any_t_equiv (#lt #t:eqtype) (f : lt -> Tot t) (ls:list (lt & asn1_gen_items_lk))
  : Lemma (ensures asn1_any_t_core t f ls == asn1_any_t t f (t_lk_as_t_k ls))
   = match ls with
     | [] -> ()
     | hd::tl ->
       let x,y = hd in
       asn1_any_t_equiv f tl; asn1_sequence_t_core_equiv (dsnd y)

let rec asn1_any_t_equiv' (#lt #t:eqtype) (f : lt -> Tot t) (ls:list (lt & asn1_gen_items_k))
  : Lemma (ensures asn1_any_t_core t f (t_k_as_t_lk ls) == asn1_any_t t f ls)
   = match ls with
     | [] -> ()
     | hd::tl ->
       let x,y = hd in
       asn1_any_t_equiv' f tl; asn1_sequence_t_core_equiv' (dfst y)


let rec asn1_sequence_any_t (items : list asn1_gen_item_k) (suffix_t : Type) : Tot Type (decreases items) =
  match items with
  | [] -> suffix_t
  | [hd] -> asn1_decorated_t hd & suffix_t
  | hd :: tl ->
    asn1_decorated_t hd & asn1_sequence_any_t tl suffix_t

let rec asn1_sequence_any_t_equiv #id_decs (items : asn1_gen_items_l id_decs) (suffix_t : Type)
  : Lemma (ensures asn1_sequence_any_t_core items suffix_t ==
                   asn1_sequence_any_t (l_as_list items) suffix_t)
          (decreases items)
  = match items with
    | ASN1_GEN_ITEMS_NIL -> ()
    | ASN1_GEN_ITEMS_CONS s d dd _ tl ->
      asn1_sequence_any_t_equiv tl suffix_t


let rec asn1_sequence_any_t_equiv' (items : list asn1_gen_item_k) (suffix_t : Type)
  : Lemma (ensures asn1_sequence_any_t_core (list_as_l items) suffix_t ==
                   asn1_sequence_any_t items suffix_t)
          (decreases items)
  = match items with
    | [] -> ()
    | hd::tl -> asn1_sequence_any_t_equiv' tl suffix_t

type asn1_length_u32_t = U32.t

let asn1_decorated_pure_t (item : asn1_gen_item_k) : Type =
  match item with
  | (| _, _, dk |) -> match dk with
                     | ASN1_PLAIN_ILC k -> asn1_t k
                     | ASN1_OPTION_ILC k -> asn1_t k
                     | ASN1_DEFAULT_TERMINAL _ #k _ -> asn1_terminal_t k 
                     | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k r _ -> parse_filter_refine (restriction_pred r)

type asn1_strong_parser_kind : parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_injective = true;
}

type asn1_weak_parser_kind : parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = None;
  parser_kind_injective = true;
}

type asn1_strong_parser (t : Type) = parser asn1_strong_parser_kind t 

type asn1_weak_parser (t : Type) = parser asn1_weak_parser_kind t

noeq
type gen_parser (k : parser_kind) = 
| Mkgenparser : (t : Type) -> (p : parser k t) -> gen_parser k

noeq
type parser_twin (k : parser_kind) (t : Type) =
| Mkparsertwin : (p : parser k t) -> (fp : (asn1_id_t -> parser k t) {and_then_cases_injective fp} ) -> parser_twin k t

noeq
type gen_decorated_parser_twin =
| Mkgendcparser : (d : asn1_gen_item_k) -> (p : asn1_strong_parser (asn1_decorated_pure_t d)) 
-> fp : (asn1_id_t -> asn1_strong_parser (asn1_decorated_pure_t d)) {and_then_cases_injective fp} ->
gen_decorated_parser_twin

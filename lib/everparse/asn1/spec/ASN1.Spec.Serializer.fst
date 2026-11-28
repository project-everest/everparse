module ASN1.Spec.Serializer

(* Spec serializers for ASN.1 DER schemas.

   A typed value `x : asn1_t k` is serialized as the DER encoding of its
   generic value: `asn1_enc k x = asn1_value_enc (to_value k x)`.

   Not every typed value can be serialized: e.g. a DEFAULT component
   explicitly set to its default value, a SET OF whose elements are not
   sorted, or contents too long for a 32-bit length. The values that can
   are those that round-trip through the typed parser (`encodable`).
   Every value returned by the typed parser of a well-formed schema is
   encodable, and the bytes it consumes are exactly its encoding
   (`asn1_as_parser_consumed`, `parsed_encodable`), so restricting the
   typed parser to encodable values does not change it
   (`parse_asn1_ser_eq`). *)

open LowParse.Spec.Base

open ASN1.Base
open ASN1.Spec.Value.Enc
open ASN1.Spec.Interpreter
open ASN1.Spec.ToValue

module Seq = FStar.Seq
module LPC = LowParse.Spec.Combinators
module Conf = ASN1.Spec.Conformance
module TVM = ASN1.Spec.ToValue.Main
module SEM = FStar.IndefiniteDescription

let asn1_enc (#s: _) (k: asn1_k s) (x: asn1_t k) : Tot bytes =
  asn1_value_enc (to_value k x)

let encodable (#s: _) (k: asn1_k s) (x: asn1_t k) : prop =
  parse (asn1_as_parser k) (asn1_enc k x) == Some (x, Seq.length (asn1_enc k x))

let encodable_b (#s: _) (k: asn1_k s) (x: asn1_t k) : GTot bool =
  SEM.strong_excluded_middle (encodable k x)

let asn1_ser_t (#s: _) (k: asn1_k s) : Type =
  LPC.parse_filter_refine (encodable_b k)

let parse_asn1_ser (#s: _) (k: asn1_k s) : Tot (LowParse.Spec.Base.parser (LPC.parse_filter_kind asn1_strong_parser_kind) (asn1_ser_t k)) =
  LPC.parse_filter #asn1_strong_parser_kind (asn1_as_parser k) (encodable_b k)

let serialize_asn1' (#s: _) (k: asn1_k s) : Tot (LowParse.Spec.Base.bare_serializer (asn1_ser_t k)) =
  fun x -> asn1_enc k x

let serialize_asn1_correct (#s: _) (k: asn1_k s)
: Lemma (serializer_correct (parse_asn1_ser k) (serialize_asn1' k))
= let prf (x: asn1_ser_t k) : Lemma (parse (parse_asn1_ser k) (serialize_asn1' k x) == Some (x, Seq.length (serialize_asn1' k x))) =
    LPC.parse_filter_eq #asn1_strong_parser_kind (asn1_as_parser k) (encodable_b k) (asn1_enc k x)
  in
  Classical.forall_intro prf

let serialize_asn1 (#s: _) (k: asn1_k s) : Tot (LowParse.Spec.Base.serializer (parse_asn1_ser k)) =
  serialize_asn1_correct k;
  serialize_asn1' k

(* The bytes consumed by the typed parser are the encoding of its result *)

let asn1_as_parser_consumed (#s: _) (k: asn1_k s) (b: bytes)
: Lemma
  (requires (Conf.wf k))
  (ensures (match parse (asn1_as_parser k) b with
    | Some (x, n) -> Seq.slice b 0 n == asn1_enc k x
    | None -> True))
= TVM.top_lemma k

(* Every parsed value is encodable *)

let parsed_encodable (#s: _) (k: asn1_k s) (b: bytes)
: Lemma
  (requires (Conf.wf k))
  (ensures (match parse (asn1_as_parser k) b with
    | Some (x, _) -> encodable k x
    | None -> True))
= asn1_as_parser_consumed k b;
  match parse (asn1_as_parser k) b with
  | Some (x, n) ->
    let e = Seq.slice b 0 n in
    parse_strong_prefix #asn1_strong_parser_kind (asn1_as_parser k) b e
  | None -> ()

(* Both facts together *)

let parsed_spec (#s: _) (k: asn1_k s) (b: bytes) : GTot prop =
  match parse (asn1_as_parser k) b with
  | Some (x, n) -> Seq.slice b 0 n == asn1_enc k x /\ encodable k x
  | None -> True

let parsed_spec_correct (#s: _) (k: asn1_k s) (b: bytes)
: Lemma
  (requires (Conf.wf k))
  (ensures (parsed_spec k b))
= asn1_as_parser_consumed k b;
  parsed_encodable k b

(* Hence restricting the parser to encodable values does not change it *)

let parse_asn1_ser_eq (#s: _) (k: asn1_k s) (b: bytes)
: Lemma
  (requires (Conf.wf k))
  (ensures (match parse (parse_asn1_ser k) b, parse (asn1_as_parser k) b with
    | Some (x1, n1), Some (x2, n2) -> (x1 <: asn1_t k) == x2 /\ n1 == n2
    | None, None -> True
    | _ -> False))
= parsed_encodable k b;
  LPC.parse_filter_eq #asn1_strong_parser_kind (asn1_as_parser k) (encodable_b k) b

(* Encodable values conform to the schema (`ASN1.Spec.Conformance`) *)

let encodable_conforms (#s: _) (k: asn1_k s) (x: asn1_t k)
: Lemma
  (requires (encodable k x))
  (ensures (Conf.conforms k (to_value k x) == true))
= ()

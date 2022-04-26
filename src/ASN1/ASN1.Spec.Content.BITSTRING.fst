module ASN1.Spec.Content.BITSTRING

open ASN1.Base

open LowParse.Spec.Combinators
open LowParse.Spec.Bytes

module U8 = FStar.UInt8
module B = FStar.Bytes

let filter_asn1_bitstring_unused (u : U8.t)
= 0 <= U8.v u && U8.v u <= 7

let filter_asn1_bitstring_payload (u : U8.t {0 <= U8.v u /\ U8.v u <= 7}) (b : B.bytes)
= if (U8.v u = 0) then
    if (B.length b = 0) then
      true
    else
      false
  else if (B.length b > 0) then
        let lastb = B.index b (B.length b - 1) in
        let mask = pow2 (U8.v u) in
        (FStar.UInt.mod (U8.v lastb) mask = 0)
      else
        false

(* TODO: use the a named thing *)

let synth_asn1_bitstring (u : U8.t {0 <= U8.v u /\ U8.v u <= 7}) 
  (b : B.bytes {(U8.v u = 0) \/ 
                ((U8.v u > 0) /\ B.length b > 0 /\ 
                FStar.UInt.mod (U8.v (B.index b ((B.length b) - 1))) (pow2 (U8.v u)) = 0)})
= BYTES_WITH_UNUSEDBITS u b

let parse_asn1_bitstring_payload (u : U8.t {0 <= U8.v u /\ U8.v u <= 7}) : asn1_weak_parser asn1_bitstring_t
= weaken _
  (parse_all_bytes
  `parse_filter`
  (filter_asn1_bitstring_payload u)
  `parse_synth`
  (synth_asn1_bitstring u))

let parse_asn1_bitstring_payload_cases_injective () : 
  Lemma (ensures and_then_cases_injective parse_asn1_bitstring_payload)
= let p = parse_asn1_bitstring_payload in
  and_then_cases_injective_intro p (
    fun u1 u2 b1 b2 -> 
      parse_all_bytes_injective ();
      parse_synth_eq (parse_all_bytes `parse_filter` (filter_asn1_bitstring_payload u1)) (synth_asn1_bitstring u1) b1;
      parse_synth_eq (parse_all_bytes `parse_filter` (filter_asn1_bitstring_payload u2)) (synth_asn1_bitstring u2) b2
  )
  
let parse_asn1_bitstring : asn1_weak_parser asn1_bitstring_t
= let _ = parse_asn1_bitstring_payload_cases_injective () in
  weaken _
  (parse_u8
  `parse_filter`
  filter_asn1_bitstring_unused
  `and_then`
  parse_asn1_bitstring_payload)

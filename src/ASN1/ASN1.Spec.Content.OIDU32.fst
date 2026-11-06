module ASN1.Spec.Content.OIDU32

open ASN1.Base
open ASN1.Spec.IdentifierU32

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.Int
open LowParse.Tot.List


module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

let byte = U8.t

let parse_asn1_OIDU32_tail = parse_list parse_asn1_identifier_U32_alt

(* X.690 8.19.4: the first subidentifier, (X*40)+Y, is itself a
   base-128 subidentifier, possibly spanning several octets. *)
let decode_OIDU32_head (v : U32.t)
: (p : (U32.t & U32.t) {asn1_OID_wf' (fst p) (snd p)})
= if (U32.v v < 40) then
    (0ul, v)
  else 
    if (U32.v v < 80) then
      (1ul, U32.sub v 40ul)
    else
      (2ul, U32.sub v 80ul)

let decode_OIDU32_head_inj (v1 v2 : U32.t) :
Lemma (requires (decode_OIDU32_head v1 = decode_OIDU32_head v2))
      (ensures (v1 = v2))
= ()
        
let synth_OIDU32 (btl : U32.t & list U32.t)
: asn1_oid_t
= let (buf, tl) = btl in
  let p = decode_OIDU32_head buf in
  (fst p) :: (snd p) :: tl

let lemma_synth_OIDU32_inj () :
  Lemma (ensures (synth_injective synth_OIDU32))
= synth_injective_intro' (synth_OIDU32) (fun x1 x2 ->
    let (b1, tl1) = x1 in
    let (b2, tl2) = x2 in
    assert (tl1 = tl2);
    let p1 = decode_OIDU32_head b1 in
    let p2 = decode_OIDU32_head b2 in
    assert (p1 = p2);
    let _ = decode_OIDU32_head_inj b1 b2 in
    _)    

let parse_asn1_OIDU32 : asn1_weak_parser asn1_oid_t =
  let _ = lemma_synth_OIDU32_inj () in
  weaken asn1_weak_parser_kind ((parse_asn1_identifier_U32_alt `nondep_then` parse_asn1_OIDU32_tail) `parse_synth` synth_OIDU32)

(* X.690 8.20: RELATIVE-OID, a non-empty list of subidentifiers *)
let parse_asn1_RELATIVE_OIDU32 : asn1_weak_parser asn1_relative_oid_t =
  weaken asn1_weak_parser_kind (parse_asn1_OIDU32_tail `parse_filter` asn1_relative_oid_wf)

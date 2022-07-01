module ASN1.Spec.Content.OIDU32

open ASN1.Base
open ASN1.Spec.IdentifierU32

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Int
open LowParse.Spec.List

open FStar.Mul

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

let byte = U8.t

let parse_asn1_OIDU32_tail = parse_list parse_asn1_identifier_U32_alt

let decode_OIDU32_head (buf : byte)
: (p : (U32.t & U32.t) {asn1_OID_wf' (fst p) (snd p)})
= if (U8.v buf < 40) then
    (0ul, Cast.uint8_to_uint32 buf)
  else 
    if (U8.v buf < 80) then
      (1ul, Cast.uint8_to_uint32 (U8.sub buf 40uy))
    else
      (2ul, Cast.uint8_to_uint32 (U8.sub buf 80uy))

let decode_OIDU32_head_inj (buf1 buf2 : byte) :
Lemma (requires (decode_OIDU32_head buf1 = decode_OIDU32_head buf2))
      (ensures (buf1 = buf2))
= if (U8.v buf1 < 40) then
    if (U8.v buf2 < 40) then
      _
    else if (U8.v buf2 < 80) then
      _
    else 
      _
  else if (U8.v buf1 < 80) then
    if (U8.v buf2 < 40) then
      _
    else if (U8.v buf2 < 80) then
      _
    else 
      _
  else
    if (U8.v buf2 < 40) then
      _
    else if (U8.v buf2 < 80) then
      _
    else 
      _
        
let synth_OIDU32 (btl : byte & list U32.t)
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
  weaken asn1_weak_parser_kind ((parse_u8 `nondep_then` parse_asn1_OIDU32_tail) `parse_synth` synth_OIDU32)

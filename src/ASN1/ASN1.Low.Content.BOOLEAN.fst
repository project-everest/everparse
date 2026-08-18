module ASN1.Low.Content.BOOLEAN

open ASN1.Base

open ASN1.Spec.Content.BOOLEAN

open LowParse.Low.Base
open LowParse.Low.Combinators
open LowParse.Low.Int

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

let valid_asn1_boolean
  (h : HS.mem)
  (#rrel #rel: _)
  (input : slice rrel rel)
  (pos : U32.t)
: Lemma ((valid parse_asn1_boolean h input pos)
  <==>
  (valid parse_u8 h input pos /\
  (let v = contents parse_u8 h input pos in 
   v == asn1_boolean_TRUE_DER \/ v == asn1_boolean_FALSE_DER)))
= valid_facts parse_asn1_boolean h input pos;
  valid_facts parse_u8 h input pos;
  lemma_parse_asn1_boolean_unfold (bytes_of_slice_from h input pos)

inline_for_extraction 
let validate_asn1_boolean () : Tot (validator parse_asn1_boolean)
= fun #rrel #rel (input : slice rrel rel) pos ->
  let h = HST.get() in
    let _ =
      valid_asn1_boolean h input (uint64_to_uint32 pos);
      valid_equiv parse_u8 h input (uint64_to_uint32 pos)
    in
  if U32.lt (input.len `U32.sub` (uint64_to_uint32) pos) 1ul
  then
    validator_error_not_enough_data
  else
    let _ = 
      valid_total_constant_size h parse_u8 1 input (uint64_to_uint32 pos);
      assert (valid parse_u8 h input (uint64_to_uint32 pos))
    in
    let v' = read_u8 input (uint64_to_uint32 pos) in
    if (U8.eq v' asn1_boolean_TRUE_DER) || (U8.eq v' asn1_boolean_FALSE_DER) then
      pos `U64.add` 1uL
    else
      validator_error_generic

//TODO: Use validator combinators

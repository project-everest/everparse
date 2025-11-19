module CBOR.Pulse.Raw.Compare
#lang-pulse
include CBOR.Pulse.Raw.Read
include CBOR.Spec.Raw.Format
include CBOR.Pulse.Raw.Compare.Bytes
include CBOR.Pulse.Raw.Compare.Iterator
open CBOR.Pulse.Raw.Format.Serialized
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Sort.Base
module SM = Pulse.Lib.SeqMatch.Util
module SZ = FStar.SizeT
module I16 = FStar.Int16
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Ser = CBOR.Pulse.Raw.Format.Compare

let rec cbor_compare_array_eq
  (x1 x2: list raw_data_item)
: Lemma
  (requires (List.Tot.length x1 == List.Tot.length x2))
  (ensures (cbor_compare_array x1 x2 == lex_compare cbor_compare x1 x2))
  (decreases x1)
= match x1, x2 with
  | [], [] -> ()
  | a1 :: q1, a2 :: q2 ->
    let c = cbor_compare a1 a2 in
    if c = 0
    then cbor_compare_array_eq q1 q2
    else ()

let cbor_compare_key_value
  (x1 x2: (raw_data_item & raw_data_item))
: Tot int
= let c = cbor_compare (fst x1) (fst x2) in
  if c = 0
  then cbor_compare (snd x1) (snd x2)
  else c

let rec cbor_compare_map_eq
  (x1 x2: list (raw_data_item & raw_data_item))
: Lemma
  (requires (List.Tot.length x1 == List.Tot.length x2))
  (ensures (cbor_compare_map x1 x2 == lex_compare cbor_compare_key_value x1 x2))
  (decreases x1)
= match x1, x2 with
  | [], [] -> ()
  | a1 :: q1, a2 :: q2 ->
    let c = cbor_compare_key_value a1 a2 in
    if c = 0
    then cbor_compare_map_eq q1 q2
    else ()

inline_for_extraction
let cbor_compare_t =
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#p1: perm) ->
  (#p2: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
      (cbor_match p1 x1 v1 ** cbor_match p2 x2 v2)
      (fun res -> cbor_match p1 x1 v1 ** cbor_match p2 x2 v2 **
        pure (
          same_sign (I16.v res) (cbor_compare v1 v2)
        )
      )

inline_for_extraction
fn cbor_compare_of_impl_compare
  (ih: A.impl_compare_t (vmatch_with_perm cbor_match) cbor_compare)
: cbor_compare_t
=
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
{
  let px1 = Mkwith_perm x1 p1;
  Trade.rewrite_with_trade
    (cbor_match p1 x1 v1)
    (vmatch_with_perm cbor_match px1 v1);
  let px2 = Mkwith_perm x2 p2;
  Trade.rewrite_with_trade
    (cbor_match p2 x2 v2)
    (vmatch_with_perm cbor_match px2 v2);
  let res = ih px1 px2;
  Trade.elim _ (cbor_match p1 x1 v1);
  Trade.elim _ (cbor_match p2 x2 v2);
  res
}

inline_for_extraction
fn impl_compare_of_cbor_compare
  (ih: cbor_compare_t)
: A.impl_compare_t u#0 u#0 #_ #_ (vmatch_with_perm cbor_match) cbor_compare
=
  (x1: with_perm cbor_raw)
  (x2: with_perm cbor_raw)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
{
  unfold (vmatch_with_perm cbor_match x1 v1);
  unfold (vmatch_with_perm cbor_match x2 v2);
  let res = ih x1.v x2.v;
  fold (vmatch_with_perm cbor_match x1 v1);
  fold (vmatch_with_perm cbor_match x2 v2);
  res
}

inline_for_extraction
fn impl_cbor_compare_key_value
  (ih: cbor_compare_t)
: A.impl_compare_t u#0 u#0 #_ #_
    (vmatch_with_perm cbor_match_map_entry)
    cbor_compare_key_value
= (x1: _)
  (x2: _)
  (#v1: _)
  (#v2: _)
{
  unfold (vmatch_with_perm cbor_match_map_entry x1 v1);
  unfold (vmatch_with_perm cbor_match_map_entry x2 v2);
  unfold (cbor_match_map_entry x1.p x1.v v1);
  unfold (cbor_match_map_entry x2.p x2.v v2);
  let c = ih x1.v.cbor_map_entry_key x2.v.cbor_map_entry_key;
  if (c = 0s) {
    let c = ih x1.v.cbor_map_entry_value x2.v.cbor_map_entry_value;
    fold (cbor_match_map_entry x1.p x1.v v1);
    fold (cbor_match_map_entry x2.p x2.v v2);
    fold (vmatch_with_perm cbor_match_map_entry x1 v1);
    fold (vmatch_with_perm cbor_match_map_entry x2 v2);
    c
  } else {
    fold (cbor_match_map_entry x1.p x1.v v1);
    fold (cbor_match_map_entry x2.p x2.v v2);
    fold (vmatch_with_perm cbor_match_map_entry x1 v1);
    fold (vmatch_with_perm cbor_match_map_entry x2 v2);
    c
  }
}

fn impl_major_type
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match p x v
returns t: major_type_t
ensures
  cbor_match p x v ** pure (t == get_major_type v)
{
  cbor_match_cases x;
  match x {
    norewrite
    CBOR_Case_Simple _ -> {
      cbor_major_type_simple_value
    }
    norewrite
    CBOR_Case_Int _ -> {
      let res = cbor_match_int_elim_type x;
      res
    }
    norewrite
    CBOR_Case_String _ -> {
      let res = cbor_match_string_elim_type x;
      res
    }
    norewrite
    CBOR_Case_Tagged _ -> {
      cbor_major_type_tagged
    }
    norewrite
    CBOR_Case_Serialized_Tagged _ -> {
      cbor_major_type_tagged
    }
    norewrite
    CBOR_Case_Array _ -> {
      cbor_major_type_array
    }
    norewrite
    CBOR_Case_Serialized_Array _ -> {
      cbor_major_type_array
    }
    norewrite
    CBOR_Case_Map _ -> {
      cbor_major_type_map
    }
    norewrite
    CBOR_Case_Serialized_Map _ -> {
      cbor_major_type_map
    }
  }
}

let uint64_compare (x1 x2: U64.t) : Tot I16.t =
  if U64.lt x1 x2
  then (-1s)
  else if U64.gt x1 x2
  then 1s
  else 0s

fn impl_raw_uint64_compare (_: unit) : impl_compare_scalar_t u#0 #_ raw_uint64_compare
= (x1: _)
  (x2: _)
{
  let c = impl_uint8_compare () x1.size x2.size;
  if (c = 0s) {
    uint64_compare x1.value x2.value
  } else {
    c
  }
}

let cbor_pair_is_serialized
  (c1 c2: cbor_raw)
: Tot (option (cbor_serialized & cbor_serialized))
= match c1 with
  | CBOR_Case_Serialized_Tagged s1 ->
    begin match c2 with
    | CBOR_Case_Serialized_Tagged s2 -> Some (s1, s2)
    | _ -> None
    end
  | _ -> None

#push-options "--z3rlimit 32"

#restart-solver
inline_for_extraction
fn cbor_compare_body
  (ih: cbor_compare_t)
: cbor_compare_t
=  
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
{
  cbor_match_cases x1;
  cbor_match_cases x2;
  let ty1 = impl_major_type x1;
  let ty2 = impl_major_type x2;
  let c = impl_uint8_compare () ty1 ty2;
  if (c = 0s) {
    if (ty1 = cbor_major_type_uint64 || ty1 = cbor_major_type_neg_int64) {
      let i1 = cbor_match_int_elim_value x1;
      let i2 = cbor_match_int_elim_value x2;
      impl_raw_uint64_compare () i1 i2
    } else if (ty1 = cbor_major_type_byte_string || ty1 = cbor_major_type_text_string) {
      let i1 = cbor_match_string_elim_length x1;
      let i2 = cbor_match_string_elim_length x2;
      let c : I16.t = impl_raw_uint64_compare () i1 i2;
      if (c = 0s) {
        let pl1 = cbor_match_string_elim_payload x1;
        let pl2 = cbor_match_string_elim_payload x2;
        let res = lex_compare_bytes pl1 pl2;
        Trade.elim _ (cbor_match p1 x1 v1);
        Trade.elim _ (cbor_match p2 x2 v2);
        res
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_tagged) {
      let tag1 = cbor_match_tagged_get_tag x1;
      let tag2 = cbor_match_tagged_get_tag x2;
      let c = impl_raw_uint64_compare () tag1 tag2;
      if (c = 0s) {
        match cbor_pair_is_serialized x1 x2 {
          Some pair -> {
            Trade.rewrite_with_trade
              (cbor_match p1 x1 v1)
              (cbor_match_serialized_tagged (fst pair) p1 v1);
            Trade.rewrite_with_trade
              (cbor_match p2 x2 v2)
              (cbor_match_serialized_tagged (snd pair) p2 v2);
            let res = Ser.cbor_match_compare_serialized_tagged (fst pair) (snd pair);
            Trade.elim _ (cbor_match p2 x2 v2);
            Trade.elim _ (cbor_match p1 x1 v1);
            res
          }
          _ -> {
            let pl1 = cbor_match_tagged_get_payload x1;
            let pl2 = cbor_match_tagged_get_payload x2;
            let res = ih pl1 pl2;
            Trade.elim _ (cbor_match p1 x1 v1);
            Trade.elim _ (cbor_match p2 x2 v2);
            res
          }
        }
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_array) {
      let len1 = cbor_match_array_get_length x1;
      let len2 = cbor_match_array_get_length x2;
      let c = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        match cbor_pair_is_serialized x1 x2 {
          Some pair -> {
            Trade.rewrite_with_trade
              (cbor_match p1 x1 v1)
              (cbor_match_serialized_array (fst pair) p1 v1);
            Trade.rewrite_with_trade
              (cbor_match p2 x2 v2)
              (cbor_match_serialized_array (snd pair) p2 v2);
            let res = Ser.cbor_match_compare_serialized_array (fst pair) (snd pair);
            Trade.elim _ (cbor_match p2 x2 v2);
            Trade.elim _ (cbor_match p1 x1 v1);
            res
          }
          _ -> {
            cbor_compare_array_eq (Array?.v v1) (Array?.v v2);
            let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
            let i1 = cbor_array_iterator_init f64 x1;
            with p1' . assert (cbor_array_iterator_match p1' i1 (Array?.v v1));
            unfold (cbor_array_iterator_match p1' i1 (Array?.v v1));
            let i2 = cbor_array_iterator_init f64 x2;
            with p2' . assert (cbor_array_iterator_match p2' i2 (Array?.v v2));
            unfold (cbor_array_iterator_match p2' i2 (Array?.v v2));
            let res = lex_compare_iterator_peel_perm cbor_match cbor_serialized_array_iterator_match cbor_serialized_array_iterator_is_empty (cbor_serialized_array_iterator_next f64) cbor_compare (impl_compare_of_cbor_compare ih) i1 i2;
            fold (cbor_array_iterator_match p1' i1 (Array?.v v1));
            fold (cbor_array_iterator_match p2' i2 (Array?.v v2));
            Trade.elim _ (cbor_match p1 x1 v1);
            Trade.elim _ (cbor_match p2 x2 v2);
            res
          }
        }
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_map) {
      let len1 = cbor_match_map_get_length x1;
      let len2 = cbor_match_map_get_length x2;
      let c = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        match cbor_pair_is_serialized x1 x2 {
          Some pair -> {
            Trade.rewrite_with_trade
              (cbor_match p1 x1 v1)
              (cbor_match_serialized_map (fst pair) p1 v1);
            Trade.rewrite_with_trade
              (cbor_match p2 x2 v2)
              (cbor_match_serialized_map (snd pair) p2 v2);
            let res = Ser.cbor_match_compare_serialized_map (fst pair) (snd pair);
            Trade.elim _ (cbor_match p2 x2 v2);
            Trade.elim _ (cbor_match p1 x1 v1);
            res
          }
          _ -> {
            cbor_compare_map_eq (Map?.v v1) (Map?.v v2);
            let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
            let i1 = cbor_map_iterator_init f64 x1;
            with p1' . assert (cbor_map_iterator_match p1' i1 (Map?.v v1));
            unfold (cbor_map_iterator_match p1' i1 (Map?.v v1));
            let i2 = cbor_map_iterator_init f64 x2;
            with p2' . assert (cbor_map_iterator_match p2' i2 (Map?.v v2));
            unfold (cbor_map_iterator_match p2' i2 (Map?.v v2));
            let res = lex_compare_iterator_peel_perm cbor_match_map_entry cbor_serialized_map_iterator_match cbor_serialized_map_iterator_is_empty (cbor_serialized_map_iterator_next f64) cbor_compare_key_value (impl_cbor_compare_key_value ih) i1 i2;
            fold (cbor_map_iterator_match p1' i1 (Map?.v v1));
            fold (cbor_map_iterator_match p2' i2 (Map?.v v2));
            Trade.elim _ (cbor_match p1 x1 v1);
            Trade.elim _ (cbor_match p2 x2 v2);
            res
          }
        }
      } else {
        c
      }
    } else {
      assert (pure (ty1 == cbor_major_type_simple_value));
      let val1 = cbor_match_simple_elim x1;
      let val2 = cbor_match_simple_elim x2;
      impl_uint8_compare () val1 val2
    }
  } else {
    c
  }
}

#pop-options

fn rec impl_cbor_compare
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
requires
  (cbor_match p1 x1 v1 ** cbor_match p2 x2 v2)
returns res: I16.t
ensures
      (cbor_match p1 x1 v1 ** cbor_match p2 x2 v2 **
        pure (
          same_sign (I16.v res) (cbor_compare v1 v2)
        )
      )
{
  cbor_compare_body impl_cbor_compare x1 x2
}

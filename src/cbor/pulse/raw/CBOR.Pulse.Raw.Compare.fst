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
module Sl = Pulse.Lib.Slice

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

#push-options "--z3rlimit 32"

// ===================================================================
// Depth-indexed lexicographic comparison (proves termination).
// Thin public wrapper [impl_cbor_compare] over a depth-indexed driver
// [cbor_compare_with_depth]; mirrors CBOR.Pulse.Raw.Nondet.Compare.
// ===================================================================

// Convert a non-inline-composite (leaf or serialized) [cbor_match_with_depth]
// to a plain [cbor_match], with a trade to restore the depth predicate.
ghost
fn cbor_match_with_depth_to_match
  (depth: Ghost.erased nat)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p x v **
  pure (~ (CBOR_Case_Array? x \/ CBOR_Case_Map? x \/ CBOR_Case_Tagged? x))
ensures
  cbor_match p x v **
  Trade.trade (cbor_match p x v) (cbor_match_with_depth depth p x v)
{
  cbor_match_with_depth_cases depth p x v;
  match x {
    norewrite
    CBOR_Case_Int ct -> {
      cbor_match_with_depth_eq_match_int depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Simple ct -> {
      cbor_match_with_depth_eq_match_simple depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_String ct -> {
      cbor_match_with_depth_eq_match_string depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Array ct -> {
      cbor_match_with_depth_eq_match_ser_array depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Map ct -> {
      cbor_match_with_depth_eq_match_ser_map depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Serialized_Tagged ct -> {
      cbor_match_with_depth_eq_match_ser_tagged depth p ct v;
      Trade.rewrite_with_trade (cbor_match_with_depth depth p x v) (cbor_match p x v);
    }
    norewrite
    CBOR_Case_Array ct -> {
      unreachable ()
    }
    norewrite
    CBOR_Case_Map ct -> {
      unreachable ()
    }
    norewrite
    CBOR_Case_Tagged ct -> {
      unreachable ()
    }
  }
}

// A tagged at [cbor_match_with_depth depth] forces depth >= 1.
ghost
fn cbor_match_with_depth_tagged_pos
  (depth: Ghost.erased nat) (p: perm) (a: cbor_tagged) (v: raw_data_item { Tagged? v })
  requires cbor_match_with_depth depth p (CBOR_Case_Tagged a) v
  ensures cbor_match_with_depth depth p (CBOR_Case_Tagged a) v ** pure (Ghost.reveal depth >= 1)
{
  cbor_match_with_depth_tagged_elim depth p a v;
  Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
}

ghost
fn cbor_match_with_depth_tagged_pos_raw
  (depth: Ghost.erased nat) (p: perm) (x: cbor_raw) (v: raw_data_item { Tagged? v })
  requires cbor_match_with_depth depth p x v ** pure (CBOR_Case_Tagged? x)
  ensures cbor_match_with_depth depth p x v ** pure (Ghost.reveal depth >= 1)
{
  let a = CBOR_Case_Tagged?.v x;
  rewrite (cbor_match_with_depth depth p x v) as (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
  cbor_match_with_depth_tagged_pos depth p a v;
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v) as (cbor_match_with_depth depth p x v);
}

ghost
fn cbor_match_with_depth_array_pos_raw
  (depth: Ghost.erased nat) (p: perm) (x: cbor_raw) (v: raw_data_item { Array? v })
  requires cbor_match_with_depth depth p x v ** pure (CBOR_Case_Array? x)
  ensures cbor_match_with_depth depth p x v ** pure (Cons? (Array?.v v) ==> Ghost.reveal depth >= 1)
{
  let a = CBOR_Case_Array?.v x;
  rewrite (cbor_match_with_depth depth p x v) as (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
  cbor_match_with_depth_array_pos depth p a v;
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Array a) v) as (cbor_match_with_depth depth p x v);
}

ghost
fn cbor_match_with_depth_map_pos_raw
  (depth: Ghost.erased nat) (p: perm) (x: cbor_raw) (v: raw_data_item { Map? v })
  requires cbor_match_with_depth depth p x v ** pure (CBOR_Case_Map? x)
  ensures cbor_match_with_depth depth p x v ** pure (Cons? (Map?.v v) ==> Ghost.reveal depth >= 1)
{
  let a = CBOR_Case_Map?.v x;
  rewrite (cbor_match_with_depth depth p x v) as (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
  cbor_match_with_depth_map_pos depth p a v;
  rewrite (cbor_match_with_depth depth p (CBOR_Case_Map a) v) as (cbor_match_with_depth depth p x v);
}

ghost
fn array_pos2
  (depth: Ghost.erased nat)
  (p1: perm) (x1: cbor_raw) (v1: raw_data_item { Array? v1 })
  (p2: perm) (x2: cbor_raw) (v2: raw_data_item { Array? v2 })
requires
  cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
  pure ((CBOR_Case_Array? x1 \/ CBOR_Case_Array? x2) /\
        List.Tot.length (Array?.v v1) == List.Tot.length (Array?.v v2))
ensures
  cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
  pure (Cons? (Array?.v v1) ==> Ghost.reveal depth >= 1)
{
  if (CBOR_Case_Array? x1) {
    cbor_match_with_depth_array_pos_raw depth p1 x1 v1;
  } else {
    cbor_match_with_depth_array_pos_raw depth p2 x2 v2;
  }
}

ghost
fn map_pos2
  (depth: Ghost.erased nat)
  (p1: perm) (x1: cbor_raw) (v1: raw_data_item { Map? v1 })
  (p2: perm) (x2: cbor_raw) (v2: raw_data_item { Map? v2 })
requires
  cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
  pure ((CBOR_Case_Map? x1 \/ CBOR_Case_Map? x2) /\
        List.Tot.length (Map?.v v1) == List.Tot.length (Map?.v v2))
ensures
  cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
  pure (Cons? (Map?.v v1) ==> Ghost.reveal depth >= 1)
{
  if (CBOR_Case_Map? x1) {
    cbor_match_with_depth_map_pos_raw depth p1 x1 v1;
  } else {
    cbor_match_with_depth_map_pos_raw depth p2 x2 v2;
  }
}

ghost
fn tagged_pos2
  (depth: Ghost.erased nat)
  (p1: perm) (x1: cbor_raw) (v1: raw_data_item { Tagged? v1 })
  (p2: perm) (x2: cbor_raw) (v2: raw_data_item { Tagged? v2 })
requires
  cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
  pure (CBOR_Case_Tagged? x1 \/ CBOR_Case_Tagged? x2)
ensures
  cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
  pure (Ghost.reveal depth >= 1)
{
  if (CBOR_Case_Tagged? x1) {
    cbor_match_with_depth_tagged_pos_raw depth p1 x1 v1;
  } else {
    cbor_match_with_depth_tagged_pos_raw depth p2 x2 v2;
  }
}

// Depth-preserving major-type reader.
fn impl_major_type_with_depth
  (depth: Ghost.erased nat)
  (x: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p x v
returns t: major_type_t
ensures
  cbor_match_with_depth depth p x v ** pure (t == get_major_type v)
{
  cbor_match_with_depth_cases depth p x v;
  match x {
    norewrite
    CBOR_Case_Simple _ -> { cbor_major_type_simple_value }
    norewrite
    CBOR_Case_Int ct -> {
      cbor_match_with_depth_to_match depth x;
      let res = cbor_match_int_elim_type x;
      Trade.elim (cbor_match p x v) (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_String ct -> {
      cbor_match_with_depth_to_match depth x;
      let res = cbor_match_string_elim_type x;
      Trade.elim (cbor_match p x v) (cbor_match_with_depth depth p x v);
      res
    }
    norewrite
    CBOR_Case_Tagged _ -> { cbor_major_type_tagged }
    norewrite
    CBOR_Case_Serialized_Tagged _ -> { cbor_major_type_tagged }
    norewrite
    CBOR_Case_Array _ -> { cbor_major_type_array }
    norewrite
    CBOR_Case_Serialized_Array _ -> { cbor_major_type_array }
    norewrite
    CBOR_Case_Map _ -> { cbor_major_type_map }
    norewrite
    CBOR_Case_Serialized_Map _ -> { cbor_major_type_map }
  }
}

// Depth-preserving array length reader (inline and serialized).
fn cbor_match_array_get_length_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p c v ** pure (Array? v)
returns res: raw_uint64
ensures
  cbor_match_with_depth depth p c v ** pure (Array? v /\ res == Array?.len v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Array a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
      cbor_match_with_depth_array_elim depth p a v;
      let res : raw_uint64 = { size = a.cbor_array_length_size; value = SZ.sizet_to_uint64 (Sl.len a.cbor_array_ptr) };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Array a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Array a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Array a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_array_get_length c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
  }
}

// Depth-preserving map length reader (inline and serialized).
fn cbor_match_map_get_length_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p c v ** pure (Map? v)
returns res: raw_uint64
ensures
  cbor_match_with_depth depth p c v ** pure (Map? v /\ res == Map?.len v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Map a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
      cbor_match_with_depth_map_elim depth p a v;
      let res : raw_uint64 = { size = a.cbor_map_length_size; value = SZ.sizet_to_uint64 (Sl.len a.cbor_map_ptr) };
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Map a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Map a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Map a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_map_get_length c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
  }
}

// Depth-preserving tag reader (inline and serialized).
fn cbor_match_tagged_get_tag_with_depth
  (depth: Ghost.erased nat)
  (c: cbor_raw)
  (#p: perm)
  (#v: Ghost.erased raw_data_item)
requires
  cbor_match_with_depth depth p c v ** pure (Tagged? v)
returns res: raw_uint64
ensures
  cbor_match_with_depth depth p c v ** pure (Tagged? v /\ res == Tagged?.tag v)
{
  cbor_match_with_depth_cases depth p c v;
  match c {
    norewrite
    CBOR_Case_Tagged a -> {
      rewrite (cbor_match_with_depth depth p c v) as (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
      cbor_match_with_depth_tagged_elim depth p a v;
      let res = a.cbor_tagged_tag;
      Trade.elim _ (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v);
      rewrite (cbor_match_with_depth depth p (CBOR_Case_Tagged a) v) as (cbor_match_with_depth depth p c v);
      res
    }
    norewrite
    CBOR_Case_Serialized_Tagged a -> {
      cbor_match_with_depth_to_match depth c;
      let res = cbor_match_tagged_get_tag c;
      Trade.elim (cbor_match p c v) (cbor_match_with_depth depth p c v);
      res
    }
  }
}

// Two serialized arrays / maps (the only shapes that are depth-agnostic and so
// may occur at depth 0): dedicated serialized comparison, no recursion needed.
inline_for_extraction
let cbor_compare_with_depth_t (depth: Ghost.erased nat) =
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#p1: perm) ->
  (#p2: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
    (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2)
    (fun res -> cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
      pure (
        same_sign (I16.v res) (cbor_compare v1 v2)
      )
    )

inline_for_extraction
fn impl_compare_of_cbor_compare_with_depth
  (d: Ghost.erased nat)
  (ih_d: cbor_compare_with_depth_t d)
: A.impl_compare_t u#0 u#0 #_ #_ (vmatch_with_perm (cbor_match_with_depth d)) cbor_compare
=
  (x1: with_perm cbor_raw)
  (x2: with_perm cbor_raw)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
{
  unfold (vmatch_with_perm (cbor_match_with_depth d) x1 v1);
  unfold (vmatch_with_perm (cbor_match_with_depth d) x2 v2);
  let res = ih_d x1.v x2.v;
  fold (vmatch_with_perm (cbor_match_with_depth d) x1 v1);
  fold (vmatch_with_perm (cbor_match_with_depth d) x2 v2);
  res
}

inline_for_extraction
fn impl_cbor_compare_key_value_with_depth
  (d: Ghost.erased nat)
  (ih_d: cbor_compare_with_depth_t d)
: A.impl_compare_t u#0 u#0 #_ #_ (vmatch_with_perm (cbor_match_map_entry_with_depth d)) cbor_compare_key_value
= (x1: _)
  (x2: _)
  (#v1: _)
  (#v2: _)
{
  unfold (vmatch_with_perm (cbor_match_map_entry_with_depth d) x1 v1);
  unfold (vmatch_with_perm (cbor_match_map_entry_with_depth d) x2 v2);
  unfold (cbor_match_map_entry_with_depth d x1.p x1.v v1);
  unfold (cbor_match_map_entry_with_depth d x2.p x2.v v2);
  let c = ih_d x1.v.cbor_map_entry_key x2.v.cbor_map_entry_key;
  if (c = 0s) {
    let c = ih_d x1.v.cbor_map_entry_value x2.v.cbor_map_entry_value;
    fold (cbor_match_map_entry_with_depth d x1.p x1.v v1);
    fold (cbor_match_map_entry_with_depth d x2.p x2.v v2);
    fold (vmatch_with_perm (cbor_match_map_entry_with_depth d) x1 v1);
    fold (vmatch_with_perm (cbor_match_map_entry_with_depth d) x2 v2);
    c
  } else {
    fold (cbor_match_map_entry_with_depth d x1.p x1.v v1);
    fold (cbor_match_map_entry_with_depth d x2.p x2.v v2);
    fold (vmatch_with_perm (cbor_match_map_entry_with_depth d) x1 v1);
    fold (vmatch_with_perm (cbor_match_map_entry_with_depth d) x2 v2);
    c
  }
}

#restart-solver
inline_for_extraction
fn cbor_compare_body_d
  (depth: Ghost.erased nat)
  (ih: (depth': Ghost.erased nat { depth' < depth }) -> cbor_compare_with_depth_t depth')
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
requires
  (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2)
returns res: I16.t
ensures
  (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
    pure (
      same_sign (I16.v res) (cbor_compare v1 v2)
    )
  )
{
  cbor_match_with_depth_cases depth p1 x1 v1;
  cbor_match_with_depth_cases depth p2 x2 v2;
  let ty1 = impl_major_type_with_depth depth x1;
  let ty2 = impl_major_type_with_depth depth x2;
  let c = impl_uint8_compare () ty1 ty2;
  if (c = 0s) {
    if (ty1 = cbor_major_type_uint64 || ty1 = cbor_major_type_neg_int64) {
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      let i1 = cbor_match_int_elim_value x1;
      let i2 = cbor_match_int_elim_value x2;
      let res = impl_raw_uint64_compare () i1 i2;
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      res
    } else if (ty1 = cbor_major_type_byte_string || ty1 = cbor_major_type_text_string) {
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      let i1 = cbor_match_string_elim_length x1;
      let i2 = cbor_match_string_elim_length x2;
      let c : I16.t = impl_raw_uint64_compare () i1 i2;
      if (c = 0s) {
        let pl1 = cbor_match_string_elim_payload x1;
        let pl2 = cbor_match_string_elim_payload x2;
        let res = lex_compare_bytes pl1 pl2;
        Trade.elim _ (cbor_match p1 x1 v1);
        Trade.elim _ (cbor_match p2 x2 v2);
        Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
        Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
        res
      } else {
        Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
        Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
        c
      }
    } else if (ty1 = cbor_major_type_tagged) {
      let tag1 = cbor_match_tagged_get_tag_with_depth depth x1;
      let tag2 = cbor_match_tagged_get_tag_with_depth depth x2;
      let c = impl_raw_uint64_compare () tag1 tag2;
      if (c = 0s) {
        if (match x1, x2 with CBOR_Case_Serialized_Tagged _, CBOR_Case_Serialized_Tagged _ -> true | _ -> false) {
          cbor_match_with_depth_to_match depth x1;
          cbor_match_with_depth_to_match depth x2;
          norewrite let CBOR_Case_Serialized_Tagged cs1 = x1;
          norewrite let CBOR_Case_Serialized_Tagged cs2 = x2;
          Trade.rewrite_with_trade
            (cbor_match p1 x1 v1)
            (cbor_match_serialized_tagged cs1 p1 v1);
          Trade.rewrite_with_trade
            (cbor_match p2 x2 v2)
            (cbor_match_serialized_tagged cs2 p2 v2);
          let res = Ser.cbor_match_compare_serialized_tagged cs1 cs2;
          Trade.elim _ (cbor_match p2 x2 v2);
          Trade.elim _ (cbor_match p1 x1 v1);
          Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
          res
        } else {
          tagged_pos2 depth p1 x1 v1 p2 x2 v2;
          let pl1 = cbor_match_tagged_get_payload_with_depth depth x1;
          let pl2 = cbor_match_tagged_get_payload_with_depth depth x2;
          let res = ih (nat_pred depth) pl1 pl2;
          Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
          res
        }
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_array) {
      let len1 = cbor_match_array_get_length_with_depth depth x1;
      let len2 = cbor_match_array_get_length_with_depth depth x2;
      let c = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        if (match x1, x2 with CBOR_Case_Serialized_Array _, CBOR_Case_Serialized_Array _ -> true | _ -> false) {
          cbor_match_with_depth_to_match depth x1;
          cbor_match_with_depth_to_match depth x2;
          norewrite let CBOR_Case_Serialized_Array cs1 = x1;
          norewrite let CBOR_Case_Serialized_Array cs2 = x2;
          Trade.rewrite_with_trade
            (cbor_match p1 x1 v1)
            (cbor_match_serialized_array cs1 p1 v1);
          Trade.rewrite_with_trade
            (cbor_match p2 x2 v2)
            (cbor_match_serialized_array cs2 p2 v2);
          let res = Ser.cbor_match_compare_serialized_array cs1 cs2;
          Trade.elim _ (cbor_match p2 x2 v2);
          Trade.elim _ (cbor_match p1 x1 v1);
          Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
          res
        } else {
          cbor_compare_array_eq (Array?.v v1) (Array?.v v2);
          if (len1.value = 0uL) {
            0s
          } else {
            array_pos2 depth p1 x1 v1 p2 x2 v2;
            let i1 = cbor_array_iterator_init_with_depth depth x1;
            with p1' . assert (cbor_array_iterator_match_with_depth (nat_pred depth) p1' i1 (Array?.v v1));
            unfold (cbor_array_iterator_match_with_depth (nat_pred depth) p1' i1 (Array?.v v1));
            let i2 = cbor_array_iterator_init_with_depth depth x2;
            with p2' . assert (cbor_array_iterator_match_with_depth (nat_pred depth) p2' i2 (Array?.v v2));
            unfold (cbor_array_iterator_match_with_depth (nat_pred depth) p2' i2 (Array?.v v2));
            let res = lex_compare_iterator_peel_perm (cbor_match_with_depth (nat_pred depth)) cbor_serialized_array_iterator_match cbor_serialized_array_iterator_is_empty (cbor_serialized_array_iterator_next_with_depth (nat_pred depth)) cbor_compare (impl_compare_of_cbor_compare_with_depth (nat_pred depth) (ih (nat_pred depth))) i1 i2;
            fold (cbor_array_iterator_match_with_depth (nat_pred depth) p1' i1 (Array?.v v1));
            fold (cbor_array_iterator_match_with_depth (nat_pred depth) p2' i2 (Array?.v v2));
            Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
            Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
            res
          }
        }
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_map) {
      let len1 = cbor_match_map_get_length_with_depth depth x1;
      let len2 = cbor_match_map_get_length_with_depth depth x2;
      let c = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        if (match x1, x2 with CBOR_Case_Serialized_Map _, CBOR_Case_Serialized_Map _ -> true | _ -> false) {
          cbor_match_with_depth_to_match depth x1;
          cbor_match_with_depth_to_match depth x2;
          norewrite let CBOR_Case_Serialized_Map cs1 = x1;
          norewrite let CBOR_Case_Serialized_Map cs2 = x2;
          Trade.rewrite_with_trade
            (cbor_match p1 x1 v1)
            (cbor_match_serialized_map cs1 p1 v1);
          Trade.rewrite_with_trade
            (cbor_match p2 x2 v2)
            (cbor_match_serialized_map cs2 p2 v2);
          let res = Ser.cbor_match_compare_serialized_map cs1 cs2;
          Trade.elim _ (cbor_match p2 x2 v2);
          Trade.elim _ (cbor_match p1 x1 v1);
          Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
          Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
          res
        } else {
          cbor_compare_map_eq (Map?.v v1) (Map?.v v2);
          if (len1.value = 0uL) {
            0s
          } else {
            map_pos2 depth p1 x1 v1 p2 x2 v2;
            let i1 = cbor_map_iterator_init_with_depth depth x1;
            with p1' . assert (cbor_map_iterator_match_with_depth (nat_pred depth) p1' i1 (Map?.v v1));
            unfold (cbor_map_iterator_match_with_depth (nat_pred depth) p1' i1 (Map?.v v1));
            let i2 = cbor_map_iterator_init_with_depth depth x2;
            with p2' . assert (cbor_map_iterator_match_with_depth (nat_pred depth) p2' i2 (Map?.v v2));
            unfold (cbor_map_iterator_match_with_depth (nat_pred depth) p2' i2 (Map?.v v2));
            let res = lex_compare_iterator_peel_perm (cbor_match_map_entry_with_depth (nat_pred depth)) cbor_serialized_map_iterator_match cbor_serialized_map_iterator_is_empty (cbor_serialized_map_iterator_next_with_depth (nat_pred depth)) cbor_compare_key_value (impl_cbor_compare_key_value_with_depth (nat_pred depth) (ih (nat_pred depth))) i1 i2;
            fold (cbor_map_iterator_match_with_depth (nat_pred depth) p1' i1 (Map?.v v1));
            fold (cbor_map_iterator_match_with_depth (nat_pred depth) p2' i2 (Map?.v v2));
            Trade.elim _ (cbor_match_with_depth depth p1 x1 v1);
            Trade.elim _ (cbor_match_with_depth depth p2 x2 v2);
            res
          }
        }
      } else {
        c
      }
    } else {
      assert (pure (ty1 == cbor_major_type_simple_value));
      cbor_match_with_depth_to_match depth x1;
      cbor_match_with_depth_to_match depth x2;
      let val1 = cbor_match_simple_elim x1;
      let val2 = cbor_match_simple_elim x2;
      let res = impl_uint8_compare () val1 val2;
      Trade.elim (cbor_match p1 x1 v1) (cbor_match_with_depth depth p1 x1 v1);
      Trade.elim (cbor_match p2 x2 v2) (cbor_match_with_depth depth p2 x2 v2);
      res
    }
  } else {
    c
  }
}

#pop-options

let common_depth (n1 n2: Ghost.erased nat) : Ghost.erased nat =
  Ghost.hide (if Ghost.reveal n1 >= Ghost.reveal n2 then Ghost.reveal n1 else Ghost.reveal n2)

#push-options "--z3rlimit 32"

fn rec cbor_compare_with_depth
  (depth: Ghost.erased nat)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased raw_data_item)
  (#v2: Ghost.erased raw_data_item)
requires
  (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2)
returns res: I16.t
ensures
  (cbor_match_with_depth depth p1 x1 v1 ** cbor_match_with_depth depth p2 x2 v2 **
    pure (
      same_sign (I16.v res) (cbor_compare v1 v2)
    )
  )
decreases (Ghost.reveal depth)
{
  cbor_compare_body_d depth (fun (depth': Ghost.erased nat { depth' < depth }) -> cbor_compare_with_depth depth') x1 x2
}

fn impl_cbor_compare
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
  cbor_match_match_with_depth p1 x1 v1;
  with n1. assert (cbor_match_with_depth n1 p1 x1 v1);
  cbor_match_match_with_depth p2 x2 v2;
  with n2. assert (cbor_match_with_depth n2 p2 x2 v2);
  let m = common_depth n1 n2;
  cbor_match_with_depth_weaken n1 m p1 x1 v1;
  cbor_match_with_depth_weaken n2 m p2 x2 v2;
  let res = cbor_compare_with_depth m x1 x2;
  cbor_match_with_depth_forget m p1 x1 v1;
  cbor_match_with_depth_forget m p2 x2 v2;
  res
}

#pop-options

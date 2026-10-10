module CBOR.Pulse.Raw.Format.Compare
friend CBOR.Pulse.Raw.Format.Match
friend CBOR.Spec.Raw.Format
include CBOR.Spec.Raw.Format
include CBOR.Pulse.Raw.Compare.Base
include CBOR.Pulse.Raw.Match
open Pulse.Lib.Pervasives
module I16 = FStar.Int16
#lang-pulse
module Bytes = CBOR.Pulse.Raw.Compare.Bytes
module F = CBOR.Spec.Raw.EverParse
module VCList = LowParse.Spec.VCList

#set-options "--print_implicits"

(* Discharged inside the Pulse function below, this one step of [cbor_compare]
   only fits in the rlimit by a hair (17.2 of 20), and it went over in CI.
   Prove it once here instead, in a small context where it is cheap. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"

let cbor_compare_tagged'
  (tag: raw_uint64)
  (v1 v2: raw_data_item)
: Lemma
  (ensures (cbor_compare (Tagged tag v1) (Tagged tag v2) == cbor_compare v1 v2))
= assert_norm (get_major_type (Tagged tag v1) == cbor_major_type_tagged);
  assert_norm (raw_uint64_compare tag tag == 0)

let cbor_compare_tagged
  (x1 x2: raw_data_item)
: Lemma
  (requires (Tagged? x1 /\ Tagged? x2 /\ Tagged?.tag x1 == Tagged?.tag x2))
  (ensures (cbor_compare x1 x2 == cbor_compare (Tagged?.v x1) (Tagged?.v x2)))
= let Tagged tag v1 = x1 in
  let Tagged _ v2 = x2 in
  cbor_compare_tagged' tag v1 v2

#pop-options

#push-options "--z3rlimit_factor 4"

fn cbor_match_compare_serialized_tagged
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Tagged? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Tagged? r2 })
requires
  (cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (Tagged?.tag r1 == Tagged?.tag r2)
  )
returns res: I16.t
ensures
  (
    cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )
{
  unfold (cbor_match_serialized_tagged c1 pm1 r1);
  unfold (cbor_match_serialized_tagged c2 pm2 r2);
  unfold (cbor_match_serialized_payload_tagged (to_slice c1.cbor_serialized_payload) (pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1));
  unfold (cbor_match_serialized_payload_tagged (to_slice c2.cbor_serialized_payload) (pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2));
  cbor_compare_tagged r1 r2;
  assert (pure (cbor_compare r1 r2 == cbor_compare (Tagged?.v r1) (Tagged?.v r2)));
  cbor_compare_correct (Tagged?.v r1) (Tagged?.v r2);
  (* tedious folding/unfolding, desperately need an "unfold all" that's universe polymorphic *)
  unfold
    LowParse.Pulse.Base.pts_to_serialized
      CBOR.Spec.Raw.EverParse.serialize_raw_data_item (to_slice c1.cbor_serialized_payload) #(pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1);
  unfold
    LowParse.Pulse.Base.pts_to_serialized
      CBOR.Spec.Raw.EverParse.serialize_raw_data_item (to_slice c2.cbor_serialized_payload) #(pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2);
  let res = Bytes.lex_compare_bytes (to_slice c1.cbor_serialized_payload) (to_slice c2.cbor_serialized_payload);
  fold
    LowParse.Pulse.Base.pts_to_serialized
      CBOR.Spec.Raw.EverParse.serialize_raw_data_item (to_slice c1.cbor_serialized_payload) #(pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1);
  fold
    LowParse.Pulse.Base.pts_to_serialized
      CBOR.Spec.Raw.EverParse.serialize_raw_data_item (to_slice c2.cbor_serialized_payload) #(pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2);
  fold (cbor_match_serialized_payload_tagged (to_slice c2.cbor_serialized_payload) (pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2));
  fold (cbor_match_serialized_payload_tagged (to_slice c1.cbor_serialized_payload) (pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1));
  fold (cbor_match_serialized_tagged c1 pm1 r1);
  fold (cbor_match_serialized_tagged c2 pm2 r2);
  res
}
#pop-options


fn cbor_match_compare_serialized_array
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Array? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Array? r2 })
requires
  (cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (Array?.len r1 == Array?.len r2)
  )
returns res: I16.t
ensures
  (
    cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )
{
  unfold (cbor_match_serialized_array c1 pm1 r1);
  unfold (cbor_match_serialized_array c2 pm2 r2);
  unfold (cbor_match_serialized_payload_array (to_slice c1.cbor_serialized_payload) (pm1 `perm_mul` c1.cbor_serialized_perm) (Array?.v r1));
  unfold (cbor_match_serialized_payload_array (to_slice c2.cbor_serialized_payload) (pm2 `perm_mul` c2.cbor_serialized_perm) (Array?.v r2));
  cbor_compare_correct r1 r2;
  F.serialized_lex_compare_array_aux (Array?.len r1) (Array?.v r1) (Array?.len r2) (Array?.v r2);
  unfold (LowParse.Pulse.Base.pts_to_serialized
           (VCList.serialize_nlist (UInt64.v (Array?.len r1).value) CBOR.Spec.Raw.EverParse.serialize_raw_data_item)
           (to_slice c1.cbor_serialized_payload)
           #(pm1 `perm_mul` c1.cbor_serialized_perm)
           (Array?.v r1));
  unfold (LowParse.Pulse.Base.pts_to_serialized
           (VCList.serialize_nlist (UInt64.v (Array?.len r2).value) CBOR.Spec.Raw.EverParse.serialize_raw_data_item)
           (to_slice c2.cbor_serialized_payload)
           #(pm2 `perm_mul` c2.cbor_serialized_perm)
           (Array?.v r2));
  let res = Bytes.lex_compare_bytes (to_slice c1.cbor_serialized_payload) (to_slice c2.cbor_serialized_payload);
  fold (LowParse.Pulse.Base.pts_to_serialized
           (VCList.serialize_nlist (UInt64.v (Array?.len r2).value) CBOR.Spec.Raw.EverParse.serialize_raw_data_item)
           (to_slice c2.cbor_serialized_payload)
           #(pm2 `perm_mul` c2.cbor_serialized_perm)
           (Array?.v r2));
  fold (LowParse.Pulse.Base.pts_to_serialized
           (VCList.serialize_nlist (UInt64.v (Array?.len r1).value) CBOR.Spec.Raw.EverParse.serialize_raw_data_item)
           (to_slice c1.cbor_serialized_payload)
           #(pm1 `perm_mul` c1.cbor_serialized_perm)
           (Array?.v r1));
  fold (cbor_match_serialized_payload_array (to_slice c2.cbor_serialized_payload) (pm2 `perm_mul` c2.cbor_serialized_perm) (Array?.v r2));
  fold (cbor_match_serialized_payload_array (to_slice c1.cbor_serialized_payload) (pm1 `perm_mul` c1.cbor_serialized_perm) (Array?.v r1));
  fold (cbor_match_serialized_array c1 pm1 r1);
  fold (cbor_match_serialized_array c2 pm2 r2);
  res
}

fn cbor_match_compare_serialized_map
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Map? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Map? r2 })
requires
  (cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (Map?.len r1 == Map?.len r2)
  )
returns res: I16.t
ensures
  (
    cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (
      same_sign (I16.v res) (cbor_compare r1 r2)
    )
  )
{
  unfold (cbor_match_serialized_map c1 pm1 r1);
  unfold (cbor_match_serialized_map c2 pm2 r2);
  unfold (cbor_match_serialized_payload_map (to_slice c1.cbor_serialized_payload) (pm1 `perm_mul` c1.cbor_serialized_perm) (Map?.v r1));
  unfold (cbor_match_serialized_payload_map (to_slice c2.cbor_serialized_payload) (pm2 `perm_mul` c2.cbor_serialized_perm) (Map?.v r2));
  cbor_compare_correct r1 r2;
  F.serialized_lex_compare_map_aux (Map?.len r1) (Map?.v r1) (Map?.len r2) (Map?.v r2);
  (* yikes *)
  unfold (LowParse.Pulse.Base.pts_to_serialized
           (VCList.serialize_nlist (UInt64.v (Map?.len r1).value)
             (CBOR.Spec.Raw.EverParse.serialize_raw_data_item
              `LowParse.Spec.Combinators.serialize_nondep_then`
              CBOR.Spec.Raw.EverParse.serialize_raw_data_item)
           )
           (to_slice c1.cbor_serialized_payload)
           #(pm1 `perm_mul` c1.cbor_serialized_perm)
           (Map?.v r1));
  unfold (LowParse.Pulse.Base.pts_to_serialized
           (VCList.serialize_nlist (UInt64.v (Map?.len r2).value)
             (CBOR.Spec.Raw.EverParse.serialize_raw_data_item
              `LowParse.Spec.Combinators.serialize_nondep_then`
              CBOR.Spec.Raw.EverParse.serialize_raw_data_item)
           )
           (to_slice c2.cbor_serialized_payload)
           #(pm2 `perm_mul` c2.cbor_serialized_perm)
           (Map?.v r2));
  let res = Bytes.lex_compare_bytes (to_slice c1.cbor_serialized_payload) (to_slice c2.cbor_serialized_payload);
  fold (LowParse.Pulse.Base.pts_to_serialized
           (VCList.serialize_nlist (UInt64.v (Map?.len r2).value)
             (CBOR.Spec.Raw.EverParse.serialize_raw_data_item
              `LowParse.Spec.Combinators.serialize_nondep_then`
              CBOR.Spec.Raw.EverParse.serialize_raw_data_item)
           )
           (to_slice c2.cbor_serialized_payload)
           #(pm2 `perm_mul` c2.cbor_serialized_perm)
           (Map?.v r2));
  fold (LowParse.Pulse.Base.pts_to_serialized
           (VCList.serialize_nlist (UInt64.v (Map?.len r1).value)
             (CBOR.Spec.Raw.EverParse.serialize_raw_data_item
              `LowParse.Spec.Combinators.serialize_nondep_then`
              CBOR.Spec.Raw.EverParse.serialize_raw_data_item)
           )
           (to_slice c1.cbor_serialized_payload)
           #(pm1 `perm_mul` c1.cbor_serialized_perm)
           (Map?.v r1));
  fold (cbor_match_serialized_payload_map (to_slice c2.cbor_serialized_payload) (pm2 `perm_mul` c2.cbor_serialized_perm) (Map?.v r2));
  fold (cbor_match_serialized_payload_map (to_slice c1.cbor_serialized_payload) (pm1 `perm_mul` c1.cbor_serialized_perm) (Map?.v r1));
  fold (cbor_match_serialized_map c1 pm1 r1);
  fold (cbor_match_serialized_map c2 pm2 r2);
  res
}

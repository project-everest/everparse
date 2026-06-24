module CBOR.Pulse.Raw.EverParse.Det.MapInsert
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.Compare.Base        // same_sign
open CBOR.Spec.Raw.Format               // cbor_compare, lemma_compare_prop
open CBOR.Spec.Raw.MapLexInsert         // entry_lex_compare, entry_lex_order, entry_lex_compare_prop
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Iterator.Sorted // cmp_t
open LowParse.Spec.Combinators            // nondep_then
open Pulse.Lib.Trade                      // trade
open LowParse.PulseParse.Iterator.Type
open LowParse.PulseParse.Iterator
open FStar.Real

module SZ = FStar.SizeT
module I16 = FStar.Int16
module Cmp = CBOR.Pulse.Raw.EverParse.Det.Compare
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module RME = CBOR.Pulse.Raw.EverParse.ReadMapEntry
module Validate = CBOR.Pulse.Raw.EverParse.Validate
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module MB = CBOR.Pulse.Raw.EverParse.MapBuilder
module Make = CBOR.Pulse.Raw.EverParse.Make
module ArrayBuilder = CBOR.Pulse.Raw.EverParse.ArrayBuilder
module Valid = CBOR.Spec.Raw.Valid
module L = FStar.List.Tot
module U64 = FStar.UInt64
module MapLexInsert = CBOR.Spec.Raw.MapLexInsert
module SpecMap = CBOR.Spec.Raw.Map
module Optimal = CBOR.Spec.Raw.Optimal
module LPS = LowParse.Pulse.Base
module PB = LowParse.PulseParse.Base

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"

(* The runtime comparator for CBOR map entries.  Fully applied,
   [impl_map_entry_lex_compare f64] is exactly the [cmp_t] unfolding for the
   lexicographic (key-then-value) total order [entry_lex_order], i.e. it has type:

     LowParse.PulseParse.Iterator.Sorted.cmp_t
       (cbor_map_entry_match cbor_raw_match) entry_lex_order

   (We give the [stt]-unfolded form rather than the literal [cmp_t] annotation,
   since ascribing the named alias trips an F* subtyping limitation on [stt]
   post-conditions that are [pure] function literals.) *)
inline_for_extraction
fn impl_map_entry_lex_compare (f64: squash FStar.SizeT.fits_u64)
  (x1: cbor_map_entry cbor_raw)
  (x2: cbor_map_entry cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased (raw_data_item & raw_data_item))
  (#pm2: perm)
  (#v2: Ghost.erased (raw_data_item & raw_data_item))
requires
  cbor_map_entry_match cbor_raw_match pm1 x1 (Ghost.reveal v1) **
  cbor_map_entry_match cbor_raw_match pm2 x2 (Ghost.reveal v2)
returns r: SZ.t
ensures
  cbor_map_entry_match cbor_raw_match pm1 x1 (Ghost.reveal v1) **
  cbor_map_entry_match cbor_raw_match pm2 x2 (Ghost.reveal v2) **
  pure (
    (SZ.v r == 0 <==> entry_lex_order (Ghost.reveal v1) (Ghost.reveal v2) == true) /\
    (SZ.v r == 1 <==> (Ghost.reveal v1 == Ghost.reveal v2)) /\
    (SZ.v r == 2 <==> entry_lex_order (Ghost.reveal v2) (Ghost.reveal v1) == true) /\
    SZ.v r <= 2
  )
{
  let _ = lemma_compare_prop;
  let _ = entry_lex_compare_prop;
  // Expose the key- and value- sub-matches of both entries.
  unfold (cbor_map_entry_match cbor_raw_match pm1 x1 (Ghost.reveal v1));
  unfold (vmatch_pair_with_proj (cbor_raw_match pm1) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm1) cbor_map_entry_value_proj) x1 (Ghost.reveal v1));
  unfold (vmatch_with_pair_proj (cbor_raw_match pm1) cbor_map_entry_value_proj x1 (snd (Ghost.reveal v1)));
  unfold (cbor_map_entry_match cbor_raw_match pm2 x2 (Ghost.reveal v2));
  unfold (vmatch_pair_with_proj (cbor_raw_match pm2) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm2) cbor_map_entry_value_proj) x2 (Ghost.reveal v2));
  unfold (vmatch_with_pair_proj (cbor_raw_match pm2) cbor_map_entry_value_proj x2 (snd (Ghost.reveal v2)));
  // Compare keys.
  let ck = Cmp.impl_cbor_compare f64 x1.cbor_map_entry_key x2.cbor_map_entry_key;
  if (I16.lt ck 0s) {
    // key1 < key2
    fold (vmatch_with_pair_proj (cbor_raw_match pm1) cbor_map_entry_value_proj x1 (snd (Ghost.reveal v1)));
    fold (vmatch_pair_with_proj (cbor_raw_match pm1) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm1) cbor_map_entry_value_proj) x1 (Ghost.reveal v1));
    fold (cbor_map_entry_match cbor_raw_match pm1 x1 (Ghost.reveal v1));
    fold (vmatch_with_pair_proj (cbor_raw_match pm2) cbor_map_entry_value_proj x2 (snd (Ghost.reveal v2)));
    fold (vmatch_pair_with_proj (cbor_raw_match pm2) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm2) cbor_map_entry_value_proj) x2 (Ghost.reveal v2));
    fold (cbor_map_entry_match cbor_raw_match pm2 x2 (Ghost.reveal v2));
    0sz
  } else if (I16.gt ck 0s) {
    // key1 > key2
    fold (vmatch_with_pair_proj (cbor_raw_match pm1) cbor_map_entry_value_proj x1 (snd (Ghost.reveal v1)));
    fold (vmatch_pair_with_proj (cbor_raw_match pm1) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm1) cbor_map_entry_value_proj) x1 (Ghost.reveal v1));
    fold (cbor_map_entry_match cbor_raw_match pm1 x1 (Ghost.reveal v1));
    fold (vmatch_with_pair_proj (cbor_raw_match pm2) cbor_map_entry_value_proj x2 (snd (Ghost.reveal v2)));
    fold (vmatch_pair_with_proj (cbor_raw_match pm2) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm2) cbor_map_entry_value_proj) x2 (Ghost.reveal v2));
    fold (cbor_map_entry_match cbor_raw_match pm2 x2 (Ghost.reveal v2));
    2sz
  } else {
    // keys equal: compare values
    let cv = Cmp.impl_cbor_compare f64 x1.cbor_map_entry_value x2.cbor_map_entry_value;
    fold (vmatch_with_pair_proj (cbor_raw_match pm1) cbor_map_entry_value_proj x1 (snd (Ghost.reveal v1)));
    fold (vmatch_pair_with_proj (cbor_raw_match pm1) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm1) cbor_map_entry_value_proj) x1 (Ghost.reveal v1));
    fold (cbor_map_entry_match cbor_raw_match pm1 x1 (Ghost.reveal v1));
    fold (vmatch_with_pair_proj (cbor_raw_match pm2) cbor_map_entry_value_proj x2 (snd (Ghost.reveal v2)));
    fold (vmatch_pair_with_proj (cbor_raw_match pm2) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm2) cbor_map_entry_value_proj) x2 (Ghost.reveal v2));
    fold (cbor_map_entry_match cbor_raw_match pm2 x2 (Ghost.reveal v2));
    if (I16.lt cv 0s) {
      0sz
    } else if (I16.gt cv 0s) {
      2sz
    } else {
      1sz
    }
  }
}

#pop-options

(* ============================================================
   Raw-level key-presence scan over a CBOR map's entries.
   ============================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

(* Runtime emptiness test for a map-entry iterator: returns [Nil? l]. *)
inline_for_extraction
fn cbor_raw_map_iter_is_empty
  (it: IT.iterator (cbor_map_entry cbor_raw))
  (#p: perm)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.iterator_match (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item) p it l
returns res: bool
ensures
  I.iterator_match (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item) p it l **
  pure (res == Nil? (Ghost.reveal l))
{
  match it {
    IT.IBase bi -> {
      rewrite each it as (IT.IBase #(cbor_map_entry cbor_raw) bi);
      unfold (I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        p (IT.IBase #(cbor_map_entry cbor_raw) bi) l);
      I.base_mixed_list_match_length (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) p bi l;
      let len = IT.base_mixed_list_length bi;
      let res = (len = 0sz);
      assert (pure (res == Nil? (Ghost.reveal l)));
      fold (I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        p (IT.IBase #(cbor_map_entry cbor_raw) bi) l);
      rewrite each (IT.IBase #(cbor_map_entry cbor_raw) bi) as it;
      res
    }
    IT.IPair bi ml -> {
      rewrite each it as (IT.IPair #(cbor_map_entry cbor_raw) bi ml);
      unfold (I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        p (IT.IPair #(cbor_map_entry cbor_raw) bi ml) l);
      with l1 l2. assert (
        I.base_mixed_list_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) p bi l1 **
        I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) p ml l2
      );
      I.base_mixed_list_match_length (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) p bi l1;
      I.mixed_list_match_length (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) p ml l2;
      let len = IT.base_mixed_list_length bi;
      let res = (len = 0sz);
      assert (pure (res == Nil? (Ghost.reveal l)));
      fold (I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        p (IT.IPair #(cbor_map_entry cbor_raw) bi ml) l);
      rewrite each (IT.IPair #(cbor_map_entry cbor_raw) bi ml) as it;
      res
    }
  }
}

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

fn cbor_raw_map_key_present
  (f64: squash FStar.SizeT.fits_u64)
  (key: cbor_raw)
  (ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (#pm: perm)
  (#l: Ghost.erased (list (raw_data_item & raw_data_item)))
  (#pk: perm)
  (#vk: Ghost.erased raw_data_item)
requires
  I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_raw_match pk key vk
returns res: bool
ensures
  I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_raw_match pk key vk **
  pure (res == true <==> List.Tot.memP (Ghost.reveal vk) (List.Tot.map fst (Ghost.reveal l)))
{
  let it0 = I.iterator_start
    (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item)
    Validate.jump_nondep_then_raw_data_item_eta
    pm ml l
    RME.cbor_map_entry_match_share_aux
    RME.cbor_map_entry_match_gather_aux;
  with pm0. assert (
    I.iterator_match (cbor_map_entry_match cbor_raw_match)
      (nondep_then parse_raw_data_item parse_raw_data_item) pm0 it0 l **
    Trade.trade
      (I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) pm0 it0 l)
      (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
  );
  let empt0 = cbor_raw_map_iter_is_empty it0;
  let mut r_it = it0;
  let mut r_found = false;
  let mut r_cont = (not empt0);
  while (
    !r_cont
  )
  invariant exists* p_cur cur_it remaining found cont.
    R.pts_to r_it cur_it **
    R.pts_to r_found found **
    R.pts_to r_cont cont **
    cbor_raw_match pk key vk **
    I.iterator_match (cbor_map_entry_match cbor_raw_match)
      (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
    Trade.trade
      (I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l) **
    pure (
      (found == true ==> List.Tot.memP (Ghost.reveal vk) (List.Tot.map fst (Ghost.reveal l))) /\
      (found == false ==> (List.Tot.memP (Ghost.reveal vk) (List.Tot.map fst (Ghost.reveal l)) <==>
                           List.Tot.memP (Ghost.reveal vk) (List.Tot.map fst remaining))) /\
      (cont == true ==> (found == false /\ Cons? remaining)) /\
      (cont == false ==> (found == true \/ Nil? remaining))
    )
  {
    with p_cur cur_it remaining found cont. assert (
      R.pts_to r_it cur_it **
      R.pts_to r_found found **
      R.pts_to r_cont cont **
      cbor_raw_match pk key vk **
      I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
      Trade.trade
        (I.iterator_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
        (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
    );
    let cur = !r_it;
    let entry, tail_it = RME.iterator_next_map_entry_raw_data_item f64 _ cur remaining;
    with pm_v hd_val tl_l pm'. assert (
      cbor_map_entry_match cbor_raw_match pm_v entry hd_val **
      I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) pm' tail_it tl_l **
      Trade.trade
        (cbor_map_entry_match cbor_raw_match pm_v entry hd_val **
         I.iterator_match (cbor_map_entry_match cbor_raw_match)
           (nondep_then parse_raw_data_item parse_raw_data_item) pm' tail_it tl_l)
        (I.iterator_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur remaining)
    );
    // Expose the key sub-match of the head entry.
    unfold (cbor_map_entry_match cbor_raw_match pm_v entry hd_val);
    unfold (vmatch_pair_with_proj (cbor_raw_match pm_v) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm_v) cbor_map_entry_value_proj) entry hd_val);
    let ck = Cmp.impl_cbor_compare f64 key entry.cbor_map_entry_key;
    fold (vmatch_pair_with_proj (cbor_raw_match pm_v) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm_v) cbor_map_entry_value_proj) entry hd_val);
    fold (cbor_map_entry_match cbor_raw_match pm_v entry hd_val);
    cbor_compare_equal (Ghost.reveal vk) (fst (Ghost.reveal hd_val));
    // map fst (hd :: tl) = fst hd :: map fst tl ; memP cons unfolding.
    assert (pure (List.Tot.map fst remaining == fst (Ghost.reveal hd_val) :: List.Tot.map fst tl_l));
    assert (pure (
      List.Tot.memP (Ghost.reveal vk) (List.Tot.map fst remaining) <==>
      (Ghost.reveal vk == fst (Ghost.reveal hd_val) \/
       List.Tot.memP (Ghost.reveal vk) (List.Tot.map fst tl_l))
    ));
    if (I16.eq ck 0s) {
      // Key found: vk == fst hd_val.
      Trade.elim
        (cbor_map_entry_match cbor_raw_match pm_v entry hd_val **
         I.iterator_match (cbor_map_entry_match cbor_raw_match)
           (nondep_then parse_raw_data_item parse_raw_data_item) pm' tail_it tl_l)
        (I.iterator_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur remaining);
      r_found := true;
      r_cont := false;
    } else {
      // Key not equal to this entry's key: advance.
      Trade.elim_hyp_l
        (cbor_map_entry_match cbor_raw_match pm_v entry hd_val)
        (I.iterator_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' tail_it tl_l)
        (I.iterator_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur remaining);
      Trade.trans
        (I.iterator_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm' tail_it tl_l)
        (I.iterator_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur remaining)
        (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
      r_it := tail_it;
      let empt = cbor_raw_map_iter_is_empty tail_it;
      r_cont := (not empt);
    }
  };
  with p_cur cur_it remaining found cont. assert (
    R.pts_to r_it cur_it **
    R.pts_to r_found found **
    R.pts_to r_cont cont **
    cbor_raw_match pk key vk **
    I.iterator_match (cbor_map_entry_match cbor_raw_match)
      (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining **
    Trade.trade
      (I.iterator_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
      (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l)
  );
  assert (pure (Nil? remaining ==>
    ~(List.Tot.memP (Ghost.reveal vk) (List.Tot.map fst remaining))));
  Trade.elim
    (I.iterator_match (cbor_map_entry_match cbor_raw_match)
      (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur_it remaining)
    (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
      (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l);
  let res = !r_found;
  res
}

#pop-options

(* ============================================================
   Raw-level CBOR map-entry insertion pipeline.
   ============================================================ *)

(* Bridge: the engine produces an existentially-quantified split position
   [kpos]; combine it with [map_insert_lex_correct] to recover the key-sorted
   [map_insert] semantics. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

let map_insert_lex_correct_ex
  (l: list (raw_data_item & raw_data_item))
  (y: (raw_data_item & raw_data_item))
  (l_result: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    L.sorted (Valid.map_entry_order order0 _) l == true /\
    ~ (L.memP (fst y) (L.map fst l)) /\
    L.sorted entry_lex_order l_result == true /\
    (exists (kpos: nat).
       kpos <= L.length l /\
       l_result == L.append (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos)))
  ))
  (ensures (
    SpecMap.map_insert cbor_compare l y == Some l_result /\
    L.sorted (Valid.map_entry_order order0 _) l_result == true
  ))
= eliminate exists (kpos: nat).
    (kpos <= L.length l /\
     l_result == L.append (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos)))
  returns (SpecMap.map_insert cbor_compare l y == Some l_result /\
           L.sorted (Valid.map_entry_order order0 _) l_result == true)
  with _pf. MapLexInsert.map_insert_lex_correct l y kpos l_result

let map_insert_result_length
  (l: list (raw_data_item & raw_data_item))
  (y: (raw_data_item & raw_data_item))
  (l_result: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    (exists (kpos: nat).
       kpos <= L.length l /\
       l_result == L.append (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos)))
  ))
  (ensures (L.length l_result == L.length l + 1))
= eliminate exists (kpos: nat).
    (kpos <= L.length l /\
     l_result == L.append (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos)))
  returns (L.length l_result == L.length l + 1)
  with _pf. begin
    I.list_narrow_length l 0 kpos;
    I.list_narrow_length l kpos (L.length l - kpos);
    L.append_length (I.list_narrow l 0 kpos) (y :: I.list_narrow l kpos (L.length l - kpos))
  end

#pop-options

let map_payload (x: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match x with
  | Map _ v -> v
  | _ -> []

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"

inline_for_extraction
```pulse
fn impl_cmp_for_engine (f64: squash FStar.SizeT.fits_u64)
: cmp_t (cbor_map_entry_match cbor_raw_match) entry_lex_order
= (x1: cbor_map_entry cbor_raw)
  (x2: cbor_map_entry cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased (raw_data_item & raw_data_item))
  (#pm2: perm)
  (#v2: Ghost.erased (raw_data_item & raw_data_item))
{
  let r = impl_map_entry_lex_compare f64 x1 x2;
  r
}
```

#pop-options

#push-options "--z3rlimit 16000 --fuel 2 --ifuel 1 --ext no:context_pruning --z3refresh --split_queries always"

inline_for_extraction
```pulse
fn mixed_list_insert_sorted_concrete
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: LowParse.Spec.Base.parser_kind) (p: LowParse.Spec.Base.parser k u)
  (j: LPS.jumper p)
  (lt_spec: Ghost.erased (u -> u -> bool))
  (cmp: cmp_t vmatch (Ghost.reveal lt_spec))
  (pm: perm) (pm_y: perm)
  (ml: mixed_list t) (l: Ghost.erased (list u))
  (y_elem: t) (y: Ghost.erased u)
  (r1: R.ref (mixed_list t)) (r2: R.ref (mixed_list t))
  (r3: R.ref (mixed_list t)) (r4: R.ref (mixed_list t))
  (ry: R.ref t)
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (zcp: PB.zero_copy_parse_strong_prefix (vmatch 1.0R) p)
requires
  mixed_list_match vmatch p pm ml (Ghost.reveal l) **
  vmatch pm_y y_elem (Ghost.reveal y) **
  (exists* v1 v2 v3 v4 vy.
    R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy) **
  pure (
    List.Tot.Properties.sorted (Ghost.reveal lt_spec) (Ghost.reveal l) == true /\
    SZ.fits (List.Tot.length (Ghost.reveal l) + 1) /\
    (forall (a b c: u). Ghost.reveal lt_spec a b == true /\ Ghost.reveal lt_spec b c == true ==> Ghost.reveal lt_spec a c == true) /\
    (forall (a: u). Ghost.reveal lt_spec a a == false)
  )
returns res: option (mixed_list t)
ensures (match res with
  | None ->
    mixed_list_match vmatch p pm ml (Ghost.reveal l) **
    vmatch pm_y y_elem (Ghost.reveal y) **
    (exists* v1 v2 v3 v4 vy.
      R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy) **
    pure (List.Tot.memP (Ghost.reveal y) (Ghost.reveal l))
  | Some result_ml ->
    exists* (pm_result: perm) (l_result: list u).
      mixed_list_match vmatch p pm_result result_ml l_result **
      trade (mixed_list_match vmatch p pm_result result_ml l_result)
            (mixed_list_match vmatch p pm ml (Ghost.reveal l) **
             vmatch pm_y y_elem (Ghost.reveal y) **
             (exists* v1 v2 v3 v4 vy.
               R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy)) **
      pure (
        (exists (k_pos: nat).
          k_pos <= List.Tot.length (Ghost.reveal l) /\
          l_result == List.Tot.append (list_narrow (Ghost.reveal l) 0 k_pos) (Ghost.reveal y :: list_narrow (Ghost.reveal l) k_pos (List.Tot.length (Ghost.reveal l) - k_pos))) /\
        List.Tot.Properties.sorted (Ghost.reveal lt_spec) l_result == true
      ))
{
  // Get total length
  let total_sz = mixed_list_length ml;
  // Share the mixed_list → two copies at pm/2
  unfold (mixed_list_match vmatch p pm ml (Ghost.reveal l));
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) pm ml (Ghost.reveal l))
    as (mixed_list_match_n vmatch p 0 (SZ.v total_sz) pm ml (Ghost.reveal l));
  mixed_list_match_n_share vmatch p 0 (SZ.v total_sz) pm ml (Ghost.reveal l) vmatch_share;
  // copy1 and copy2 both at pm/2
  // Search loop: find insertion position k (delegated to helper)
  let mut r_k = 0sz;
  let mut r_continue = true;
  let mut r_found = 0sz; // 0 = found (insert before k), 1 = duplicate at k, 2 = insert at end
  mixed_list_match_n_length vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l);
  mixed_list_insert_sorted_find vmatch p j lt_spec cmp pm pm_y ml l y_elem y vmatch_share vmatch_gather zcp r_k r_continue r_found total_sz;
  // After loop: check result
  let k_val = !r_k;
  let found_val = !r_found;
  if (SZ.eq found_val 1sz) {
    // Duplicate: gather copies back and return false
    mixed_list_match_n_gather vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) (pm /. 2.0R) ml (Ghost.reveal l) (Ghost.reveal l) vmatch_gather;
    drop_ (pure (Ghost.reveal l == Ghost.reveal l));
    rewrite (mixed_list_match_n vmatch p 0 (SZ.v total_sz) ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l))
      as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l));
    fold (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l));
    rewrite (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l))
      as (mixed_list_match vmatch p pm ml (Ghost.reveal l));
    // Pack refs back
    List.Tot.Properties.lemma_index_memP (Ghost.reveal l) (SZ.v k_val);
    fold (exists* v1 v2 v3 v4 vy.
      R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy);
    None #(mixed_list t)
  } else {
    // Success: build result
    // Narrow copy1 to [0, k): before part
    let k_nat : Ghost.erased nat = SZ.v k_val;
    let rest_sz = SZ.sub total_sz k_val;
    let ml_before = mixed_list_narrow_n vmatch p j 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)
      0sz k_val vmatch_share vmatch_gather;
    // ml_before matches l[0..k) at pm/4
    // Narrow copy2 to [k, total-k): after part
    let ml_after = mixed_list_narrow_n vmatch p j 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)
      k_val rest_sz vmatch_share vmatch_gather;
    // ml_after matches l[k..total) at pm/4
    // Write refs and share for half-perm pattern
    R.write ry y_elem;
    R.share ry;
    // Share vmatch to get two halves at pm_y/2
    vmatch_share y_elem;
    // Build Singleton: Base (Singleton sp sv ry) matching [y]
    let sp_val : Ghost.erased perm = 0.5R /. (pm /. 4.0R);
    let sv_val : Ghost.erased perm = (pm_y /. 2.0R) /. (pm /. 4.0R);
    let singleton_ml : mixed_list t = Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry);
    // Write inner append refs and share
    R.write r3 singleton_ml;
    R.share r3;
    R.write r4 ml_after;
    R.share r4;
    // Build inner Append
    let bp_val : Ghost.erased perm = 0.5R /. (pm /. 4.0R);
    let inner_depth : Ghost.erased nat = mixed_list_depth ml_after + 1;
    let inner_ml : mixed_list t = Append (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4;
    // Write outer append refs and share
    R.write r1 ml_before;
    R.share r1;
    R.write r2 inner_ml;
    R.share r2;
    // Build outer Append
    let outer_depth : Ghost.erased nat = (if mixed_list_depth ml_before > Ghost.reveal inner_depth then mixed_list_depth ml_before else Ghost.reveal inner_depth) + 1;
    let result_ml : mixed_list t = Append (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2;
    // The result matches l[0..k) @ [y] @ l[k..total)
    let l_before : Ghost.erased (list u) = list_narrow (Ghost.reveal l) 0 (SZ.v k_val);
    let l_after : Ghost.erased (list u) = list_narrow (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz);
    let l_result : Ghost.erased (list u) = List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after);
    // Establish List.Tot.Properties.sorted on result
    assert (pure (
      SZ.v k_val <= List.Tot.length (Ghost.reveal l) /\
      (SZ.v k_val == List.Tot.length (Ghost.reveal l) \/
       (SZ.v k_val < List.Tot.length (Ghost.reveal l) /\
        Ghost.reveal lt_spec (Ghost.reveal y) (List.Tot.index (Ghost.reveal l) (SZ.v k_val)) == true))
    ));
    sorted_insert_lemma (Ghost.reveal lt_spec) (Ghost.reveal l) (Ghost.reveal y) (SZ.v k_val);
    list_narrow_splitAt (Ghost.reveal l) (SZ.v k_val);
    // Fold Singleton match using half-perm refs and vmatch
    perm_mul_div_cancel' (pm /. 4.0R) 0.5R;
    perm_mul_div_cancel' (pm /. 4.0R) (pm_y /. 2.0R);
    rewrite (R.pts_to ry #(1.0R /. 2.0R) y_elem)
      as (pts_to ry #((pm /. 4.0R) *. Ghost.reveal sp_val) y_elem);
    rewrite (vmatch (pm_y /. 2.0R) y_elem (Ghost.reveal y))
      as (vmatch ((pm /. 4.0R) *. Ghost.reveal sv_val) y_elem (Ghost.reveal y));
    fold (base_mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Singleton #t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal y]);
    fold (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
    rewrite (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y])
      as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length singleton_ml)) (pm /. 4.0R) singleton_ml [Ghost.reveal y]);
    fold (mixed_list_match vmatch p (pm /. 4.0R) singleton_ml [Ghost.reveal y]);
    // Fold inner Append match
    rewrite (R.pts_to r3 #(1.0R /. 2.0R) singleton_ml)
      as (pts_to r3 #((pm /. 4.0R) *. Ghost.reveal bp_val) singleton_ml);
    rewrite (R.pts_to r4 #(1.0R /. 2.0R) ml_after)
      as (pts_to r4 #((pm /. 4.0R) *. Ghost.reveal bp_val) ml_after);
    rewrite (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_after (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v rest_sz)))
      as (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v 1sz)) (append_n_after 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) ml_after (Ghost.reveal l_after));
    rewrite (mixed_list_match vmatch p (pm /. 4.0R) singleton_ml [Ghost.reveal y])
      as (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v 1sz)) (append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) singleton_ml [Ghost.reveal y]);
    list_narrow_length (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz);
    intro_pure (
      0 + SZ.v (mixed_list_length inner_ml) <= SZ.v 1sz + SZ.v rest_sz /\
      SZ.v 0sz + SZ.v 1sz <= SZ.v (mixed_list_length singleton_ml) /\
      SZ.v 0sz + SZ.v rest_sz <= SZ.v (mixed_list_length ml_after) /\
      List.Tot.length [Ghost.reveal y] == append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz) /\
      List.Tot.length (Ghost.reveal l_after) == append_n_after 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz) /\
      (Ghost.reveal y :: Ghost.reveal l_after) == List.Tot.append [Ghost.reveal y] (Ghost.reveal l_after) /\
      mixed_list_depth singleton_ml < Ghost.reveal inner_depth /\
      mixed_list_depth ml_after < Ghost.reveal inner_depth
    ) ();
    fold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length inner_ml)) (pm /. 4.0R) (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4) (Ghost.reveal y :: Ghost.reveal l_after));
    rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length inner_ml)) (pm /. 4.0R) (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4) (Ghost.reveal y :: Ghost.reveal l_after))
      as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length inner_ml)) (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after));
    fold (mixed_list_match vmatch p (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after));
    // Fold outer Append match
    rewrite (R.pts_to r1 #(1.0R /. 2.0R) ml_before)
      as (pts_to r1 #((pm /. 4.0R) *. Ghost.reveal bp_val) ml_before);
    rewrite (R.pts_to r2 #(1.0R /. 2.0R) inner_ml)
      as (pts_to r2 #((pm /. 4.0R) *. Ghost.reveal bp_val) inner_ml);
    rewrite (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_before (list_narrow (Ghost.reveal l) (0 - 0) (SZ.v k_val)))
      as (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v k_val)) (append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ml_before (Ghost.reveal l_before));
    rewrite (mixed_list_match vmatch p (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after))
      as (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v k_val)) (append_n_after 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after));
    list_narrow_length (Ghost.reveal l) 0 (SZ.v k_val);
    intro_pure (
      0 + SZ.v (mixed_list_length result_ml) <= SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
      SZ.v 0sz + SZ.v k_val <= SZ.v (mixed_list_length ml_before) /\
      SZ.v 0sz + SZ.v (SZ.add 1sz rest_sz) <= SZ.v (mixed_list_length inner_ml) /\
      List.Tot.length (Ghost.reveal l_before) == append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val) /\
      List.Tot.length (Ghost.reveal y :: Ghost.reveal l_after) == append_n_after 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val) /\
      Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
      mixed_list_depth ml_before < Ghost.reveal outer_depth /\
      mixed_list_depth inner_ml < Ghost.reveal outer_depth
    ) ();
    fold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2) (Ghost.reveal l_result));
    rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2) (Ghost.reveal l_result))
      as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) result_ml (Ghost.reveal l_result));
    fold (mixed_list_match vmatch p (pm /. 4.0R) result_ml (Ghost.reveal l_result));
    // Establish pure facts for trade frame (must be before trade intro)
    list_narrow_length (Ghost.reveal l) 0 (SZ.v k_val);
    list_narrow_length (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz);
    perm_mul_div_cancel' (pm /. 4.0R) 0.5R;
    perm_mul_div_cancel' (pm /. 4.0R) (pm_y /. 2.0R);
    intro_pure (
      (pm /. 4.0R) *. Ghost.reveal bp_val == 1.0R /. 2.0R /\
      (pm /. 4.0R) *. Ghost.reveal sp_val == 1.0R /. 2.0R /\
      (pm /. 4.0R) *. Ghost.reveal sv_val == pm_y /. 2.0R /\
      (pm /. 2.0R) /. 2.0R == pm /. 4.0R /\
      Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
      Ghost.reveal l_before == list_narrow (Ghost.reveal l) 0 (SZ.v k_val) /\
      Ghost.reveal l_after == list_narrow (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz) /\
      List.Tot.length (Ghost.reveal l_before) == SZ.v k_val /\
      List.Tot.length (Ghost.reveal l_after) == SZ.v rest_sz /\
      SZ.v (mixed_list_length result_ml) == SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
      SZ.v (mixed_list_length inner_ml) == 1 + SZ.v rest_sz /\
      SZ.v (mixed_list_length ml_before) == SZ.v k_val /\
      SZ.v (mixed_list_length ml_after) == SZ.v rest_sz /\
      SZ.v (mixed_list_length ml) == SZ.v total_sz
    ) ();
    // Build the trade: result_match → original + vmatch + refs
    // Frame: halves of all refs + vmatch half + narrow trades + pure facts
    intro (mixed_list_match vmatch p (pm /. 4.0R) result_ml (Ghost.reveal l_result) @==>
           (mixed_list_match vmatch p pm ml (Ghost.reveal l) **
            vmatch pm_y y_elem (Ghost.reveal y) **
            (exists* v1 v2 v3 v4 vy.
              R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy)))
      #(trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_before (list_narrow (Ghost.reveal l) (0 - 0) (SZ.v k_val)))
              (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)) **
        trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_after (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v rest_sz)))
              (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)) **
        R.pts_to r1 #(1.0R /. 2.0R) ml_before **
        R.pts_to r2 #(1.0R /. 2.0R) inner_ml **
        R.pts_to r3 #(1.0R /. 2.0R) singleton_ml **
        R.pts_to r4 #(1.0R /. 2.0R) ml_after **
        R.pts_to ry #(1.0R /. 2.0R) y_elem **
        vmatch (pm_y /. 2.0R) y_elem (Ghost.reveal y) **
        pure (
          (pm /. 4.0R) *. Ghost.reveal bp_val == 1.0R /. 2.0R /\
          (pm /. 4.0R) *. Ghost.reveal sp_val == 1.0R /. 2.0R /\
          (pm /. 4.0R) *. Ghost.reveal sv_val == pm_y /. 2.0R /\
          (pm /. 2.0R) /. 2.0R == pm /. 4.0R /\
          Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
          Ghost.reveal l_before == list_narrow (Ghost.reveal l) 0 (SZ.v k_val) /\
          Ghost.reveal l_after == list_narrow (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz) /\
          List.Tot.length (Ghost.reveal l_before) == SZ.v k_val /\
          List.Tot.length (Ghost.reveal l_after) == SZ.v rest_sz /\
          SZ.v (mixed_list_length result_ml) == SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
          SZ.v (mixed_list_length inner_ml) == 1 + SZ.v rest_sz /\
          SZ.v (mixed_list_length ml_before) == SZ.v k_val /\
          SZ.v (mixed_list_length ml_after) == SZ.v rest_sz /\
          SZ.v (mixed_list_length ml) == SZ.v total_sz
        ))
      fn _ {
        // Trade body extracted to mixed_list_insert_sorted_trade_body
        rewrite (mixed_list_match vmatch p (pm /. 4.0R) result_ml (Ghost.reveal l_result))
          as (mixed_list_match vmatch p (pm /. 4.0R)
                (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2)
                (Ghost.reveal l_result));
        rewrite (R.pts_to r2 #(1.0R /. 2.0R) inner_ml)
          as (R.pts_to r2 #(1.0R /. 2.0R) (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4));
        rewrite (R.pts_to r3 #(1.0R /. 2.0R) singleton_ml)
          as (R.pts_to r3 #(1.0R /. 2.0R) (Base #t (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)));
        mixed_list_insert_sorted_trade_body vmatch p pm pm_y ml l y_elem y r1 r2 r3 r4 ry vmatch_gather
          k_val rest_sz total_sz ml_before ml_after l_before l_after l_result sp_val sv_val bp_val outer_depth inner_depth () () ();
      };
    // Establish postcondition pure
    intro_pure (
      (exists (k_pos: nat).
        k_pos <= List.Tot.length (Ghost.reveal l) /\
        Ghost.reveal l_result == List.Tot.append (list_narrow (Ghost.reveal l) 0 k_pos) (Ghost.reveal y :: list_narrow (Ghost.reveal l) k_pos (List.Tot.length (Ghost.reveal l) - k_pos))) /\
      List.Tot.Properties.sorted (Ghost.reveal lt_spec) (Ghost.reveal l_result) == true
    ) ();
    Some result_ml
  }
}
```

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 256 --ext no:context_pruning"

inline_for_extraction
fn cbor_raw_det_map_entry_insert
  (f64: squash FStar.SizeT.fits_u64)
  (x: cbor_raw)
  (key value: cbor_raw)
  (r1 r2 r3 r4: R.ref (IT.mixed_list (cbor_map_entry cbor_raw)))
  (ry: R.ref (cbor_map_entry cbor_raw))
  (#pm: perm) (#xh: Ghost.erased raw_data_item)
  (#pkv: perm) (#vk: Ghost.erased raw_data_item) (#vv: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm x xh **
  cbor_raw_match pkv key vk ** cbor_raw_match pkv value vv **
  (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy) **
  pure (Map? (Ghost.reveal xh) /\
        L.sorted (Valid.map_entry_order order0 _) (Map?.v (Ghost.reveal xh)) == true)
returns res: option cbor_raw
ensures (match res with
  | None ->
    cbor_raw_match pm x xh **
    cbor_raw_match pkv key vk ** cbor_raw_match pkv value vv **
    (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy) **
    pure (L.memP (Ghost.reveal vk) (L.map fst (map_payload (Ghost.reveal xh))) \/
          ~ (FStar.UInt.fits (L.length (map_payload (Ghost.reveal xh)) + 1) 64))
  | Some m ->
    exists* (pm_result: perm) (xh_result: raw_data_item).
      cbor_raw_match pm_result m xh_result **
      Trade.trade
        (cbor_raw_match pm_result m xh_result)
        (cbor_raw_match pm x xh **
         cbor_raw_match pkv key vk ** cbor_raw_match pkv value vv **
         (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy)) **
      pure (Map? xh_result /\
            SpecMap.map_insert cbor_compare (map_payload (Ghost.reveal xh)) (Ghost.reveal vk, Ghost.reveal vv) == Some (map_payload xh_result) /\
            (Map?.len xh_result <: raw_uint64) == Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (map_payload xh_result))) /\
            FStar.UInt.fits (L.length (map_payload xh_result)) U64.n /\
            L.sorted (Valid.map_entry_order order0 _) (map_payload xh_result) == true))
{
  let l_raw : Ghost.erased (list (raw_data_item & raw_data_item)) = Ghost.hide (Map?.v (Ghost.reveal xh));
  MB.cbor_map_borrow_entries pm x xh l_raw;
  with pm0 ml0. assert (
    I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
      (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw) **
    Trade.trade
      (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
      (cbor_raw_match pm x (Ghost.reveal xh))
  );
  let ml0c = ((CBOR_Case_Map?.v x).cbor_map_ptr <: IT.mixed_list (cbor_map_entry cbor_raw));
  rewrite (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
    as (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw));
  rewrite (Trade.trade
             (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
               (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0 (Ghost.reveal l_raw))
             (cbor_raw_match pm x (Ghost.reveal xh)))
    as (Trade.trade
          (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw))
          (cbor_raw_match pm x (Ghost.reveal xh)));
  I.mixed_list_match_length (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw);
  let total_len = IT.mixed_list_length ml0c;
  let la64 = SZ.sizet_to_uint64 total_len;
  let limit = U64.sub 0xffffffffffffffffuL 1uL;
  if (U64.lte la64 limit) {
    let present = cbor_raw_map_key_present f64 key ml0c #pm0 #l_raw #pkv #vk;
    if present {
      Trade.elim
        (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw))
        (cbor_raw_match pm x (Ghost.reveal xh));
      None #cbor_raw
    } else {
      // Key absent: build the new entry and run the sorted-insert engine.
      SZ.fits_u64_implies_fits (SZ.v total_len + 1);
      let y_elem = Make.cbor_mk_map_entry key value #pkv #vk #vv;
      let y_pair : Ghost.erased (raw_data_item & raw_data_item) =
        Ghost.hide (Ghost.reveal vk, Ghost.reveal vv);
      rewrite (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal vk, Ghost.reveal vv))
        as (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair));
      rewrite (Trade.trade
                 (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal vk, Ghost.reveal vv))
                 (cbor_raw_match pkv key (Ghost.reveal vk) ** cbor_raw_match pkv value (Ghost.reveal vv)))
        as (Trade.trade
              (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair))
              (cbor_raw_match pkv key (Ghost.reveal vk) ** cbor_raw_match pkv value (Ghost.reveal vv)));
      // Engine preconditions.
      MapLexInsert.sorted_key_implies_lex (Ghost.reveal l_raw);
      let _ = MapLexInsert.entry_lex_compare_prop;
      FStar.Ghost.reveal_hide entry_lex_order;
      assert (pure (Ghost.reveal (Ghost.hide entry_lex_order) == entry_lex_order));
      assert (pure (L.sorted entry_lex_order (Ghost.reveal l_raw) == true));
      assert (pure (SZ.fits (L.length (Ghost.reveal l_raw) + 1)));
      assert (pure ((forall (a b c: (raw_data_item & raw_data_item)). entry_lex_order a b == true /\ entry_lex_order b c == true ==> entry_lex_order a c == true) /\
                    (forall (a: (raw_data_item & raw_data_item)). entry_lex_order a a == false)));
      let res_ml = mixed_list_insert_sorted_concrete
        (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        Validate.jump_nondep_then_raw_data_item_eta
        (Ghost.hide entry_lex_order)
        (impl_cmp_for_engine f64)
        pm0 pkv ml0c l_raw y_elem y_pair
        r1 r2 r3 r4 ry
        RME.cbor_map_entry_match_share_aux RME.cbor_map_entry_match_gather_aux
        (RME.cbor_raw_read_map_entry 1.0R f64);
      match res_ml {
        Some ml_result -> {
          with pm_result l_result. assert (
            I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result **
            Trade.trade
              (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result)
              (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw) **
               cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair) **
               (exists* v1 v2 v3 v4 vy. R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy))
          );
        // Correctness bridge: recover key-sorted map_insert semantics.
        map_insert_lex_correct_ex (Ghost.reveal l_raw) (Ghost.reveal y_pair) l_result;
        map_insert_result_length (Ghost.reveal l_raw) (Ghost.reveal y_pair) l_result;
        I.mixed_list_match_length (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result;
        // Rebuild a CBOR map value.
        let len_sz_rt = IT.mixed_list_length ml_result;
        let len64_rt = SZ.sizet_to_uint64 len_sz_rt;
        let len_size = ArrayBuilder.minimal_len_size len64_rt;
        ArrayBuilder.minimal_len_size_prop len64_rt;
        let m = MB.cbor_mk_map_full f64 pm_result len_size ml_result #l_result;
        with xh2. assert (
          cbor_raw_match pm_result m (Ghost.reveal xh2) **
          Trade.trade
            (cbor_raw_match pm_result m (Ghost.reveal xh2))
            (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result) **
          pure (Map? (Ghost.reveal xh2) /\
                (Map?.v (Ghost.reveal xh2) <: list (raw_data_item & raw_data_item)) == l_result /\
                (Map?.len (Ghost.reveal xh2)).size == len_size /\
                (Map?.len (Ghost.reveal xh2)).value == U64.uint_to_t (L.length l_result))
        );
        // The rebuilt length field is the minimal (canonical) encoding.
        // NOTE: typing the byte-slice fields as `byte_slice` (the C naming hint)
        // perturbs the SMT context here, so derive the length equalities through
        // explicit value-level steps rather than relying on the solver to chain
        // `len64_rt = sizet_to_uint64 (mixed_list_length ml_result)` to the list
        // length in one shot.
        assert (pure (SZ.v len_sz_rt == L.length l_result));
        assert (pure (FStar.UInt.fits (L.length l_result) U64.n));
        assert (pure (U64.v len64_rt == L.length l_result));
        assert (pure (len64_rt == U64.uint_to_t (L.length l_result)));
        assert (pure (len_size == (Optimal.mk_raw_uint64 (U64.uint_to_t (L.length l_result))).size));
        assert (pure ((Map?.len (Ghost.reveal xh2) <: raw_uint64) == Optimal.mk_raw_uint64 (U64.uint_to_t (L.length l_result))));
        // Compose all trades back to the original resources.
        Trade.intro_trade
          (cbor_raw_match pm_result m (Ghost.reveal xh2))
          (cbor_raw_match pm x (Ghost.reveal xh) **
           cbor_raw_match pkv key (Ghost.reveal vk) **
           cbor_raw_match pkv value (Ghost.reveal vv) **
           (exists* w1 w2 w3 w4 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to r3 w3 ** R.pts_to r4 w4 ** R.pts_to ry wy))
          (Trade.trade
             (cbor_raw_match pm_result m (Ghost.reveal xh2))
             (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
               (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result) **
           Trade.trade
             (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
               (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result)
             (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
               (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw) **
              cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair) **
              (exists* v1 v2 v3 v4 vy. R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy)) **
           Trade.trade
             (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair))
             (cbor_raw_match pkv key (Ghost.reveal vk) ** cbor_raw_match pkv value (Ghost.reveal vv)) **
           Trade.trade
             (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
               (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw))
             (cbor_raw_match pm x (Ghost.reveal xh)))
          fn _ {
            Trade.elim
              (cbor_raw_match pm_result m (Ghost.reveal xh2))
              (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result);
            Trade.elim
              (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm_result ml_result l_result)
              (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw) **
               cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair) **
               (exists* v1 v2 v3 v4 vy. R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy));
            Trade.elim
              (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair))
              (cbor_raw_match pkv key (Ghost.reveal vk) ** cbor_raw_match pkv value (Ghost.reveal vv));
            Trade.elim
              (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw))
              (cbor_raw_match pm x (Ghost.reveal xh));
          };
        Some #cbor_raw m
        }
        None -> {
          FStar.List.Tot.Properties.memP_map_intro fst (Ghost.reveal y_pair) (Ghost.reveal l_raw);
          unreachable ()
        }
      }
    }
  } else {
    // total_len == 2^64 - 1: total_len + 1 does not fit in u64.
    ArrayBuilder.array_append_overflow la64 1uL (SZ.v total_len) 1;
    Trade.elim
      (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw))
      (cbor_raw_match pm x (Ghost.reveal xh));
    None #cbor_raw
  }
}

#pop-options

module CBOR.Pulse.Raw.EverParse.Nondet.MapInsert
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open LowParse.PulseParse.Projectors
open LowParse.Spec.Combinators
open Pulse.Lib.Trade
open LowParse.PulseParse.Iterator.Type
open LowParse.PulseParse.Iterator

module SZ = FStar.SizeT
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module RME = CBOR.Pulse.Raw.EverParse.ReadMapEntry
module Validate = CBOR.Pulse.Raw.EverParse.Validate
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module Valid = CBOR.Spec.Raw.Valid
module L = FStar.List.Tot
module NondetCompare = CBOR.Pulse.Raw.EverParse.Nondet.Compare
module SpecRaw = CBOR.Spec.Raw
module NondetSpec = CBOR.Spec.Raw.Nondet
module MB = CBOR.Pulse.Raw.EverParse.MapBuilder
module Make = CBOR.Pulse.Raw.EverParse.Make
module ArrayBuilder = CBOR.Pulse.Raw.EverParse.ArrayBuilder
module Optimal = CBOR.Spec.Raw.Optimal
module Append = LowParse.PulseParse.Iterator.Append
module MapPrepend = CBOR.Spec.Raw.MapPrepend
module U64 = FStar.UInt64

(* ============================================================
   Raw-level key-presence scan over a NONDETERMINISTIC CBOR map's
   entries, based on structural equivalence ([raw_equiv]) rather
   than syntactic equality ([==]).

   This is the nondet analog of
   [CBOR.Pulse.Raw.EverParse.Det.MapInsert.cbor_raw_map_key_present].
   The deterministic scan compares keys with [impl_cbor_compare] and
   concludes syntactic equality ([==]).  For nondeterministic maps the
   relevant key-presence predicate is the *coarser* structural
   equivalence [raw_equiv = equiv basic_data_model]:

     existsb (raw_equiv vk) (map fst l)

   We obtain it from [NondetCompare.compare_cbor_raw_basic f64 None],
   whose result equals [check_equiv basic_data_model None v1 v2].  By
   [NondetSpec.check_equiv_correct], *provided* both items are valid
   ([check_equiv_precond]), that result is [Some (raw_equiv v1 v2)]
   (it is never [None] when [map_bound = None]).

   Hence we MUST require validity of the searched key [vk] and of all
   the map keys [map fst l].  These hypotheses are exactly what the
   caller (a nondet map insert) has on hand, since they come from
   [cbor_nondet_match], which guarantees structural validity.
   ============================================================ *)

inline_for_extraction
let opt_bool_def (o: option bool) : bool =
  match o with
  | Some b -> b
  | None -> false

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

(* Runtime emptiness test for a map-entry iterator: returns [Nil? l]. *)
inline_for_extraction
fn cbor_raw_nondet_map_iter_is_empty
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

inline_for_extraction
fn cbor_raw_nondet_map_key_present
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
  cbor_raw_match pk key vk **
  pure (
    Valid.valid_raw_data_item (Ghost.reveal vk) == true /\
    L.for_all Valid.valid_raw_data_item (L.map fst (Ghost.reveal l)) == true
  )
returns res: bool
ensures
  I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
    (nondep_then parse_raw_data_item parse_raw_data_item) pm ml l **
  cbor_raw_match pk key vk **
  pure (res == true <==> L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l)))
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
  let empt0 = cbor_raw_nondet_map_iter_is_empty it0;
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
      L.for_all Valid.valid_raw_data_item (L.map fst remaining) == true /\
      (found == true ==> L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l))) /\
      (found == false ==> (L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst (Ghost.reveal l)) <==>
                           L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst remaining))) /\
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
    // Structural-equivalence comparison of the searched key against the entry key.
    let cmp = NondetCompare.compare_cbor_raw_basic f64 None key entry.cbor_map_entry_key;
    fold (vmatch_pair_with_proj (cbor_raw_match pm_v) cbor_map_entry_key_proj
      (vmatch_with_pair_proj (cbor_raw_match pm_v) cbor_map_entry_value_proj) entry hd_val);
    fold (cbor_map_entry_match cbor_raw_match pm_v entry hd_val);
    // remaining = hd_val :: tl_l, so map fst remaining = fst hd_val :: map fst tl_l,
    // and the head key (fst hd_val) is valid (it is in map fst remaining).
    assert (pure (L.map fst remaining == fst (Ghost.reveal hd_val) :: L.map fst tl_l));
    assert (pure (Valid.valid_raw_data_item (fst (Ghost.reveal hd_val)) == true));
    assert (pure (L.for_all Valid.valid_raw_data_item (L.map fst tl_l) == true));
    // cmp == check_equiv basic_data_model None vk (fst hd_val); with both valid and
    // map_bound = None, this is Some (raw_equiv vk (fst hd_val)).
    NondetSpec.check_equiv_correct SpecRaw.basic_data_model None (Ghost.reveal vk) (fst (Ghost.reveal hd_val));
    let found_here = opt_bool_def cmp;
    assert (pure (found_here == true <==> Valid.raw_equiv (Ghost.reveal vk) (fst (Ghost.reveal hd_val))));
    // existsb (raw_equiv vk) (fst hd :: map fst tl) = raw_equiv vk (fst hd) || existsb ...
    assert (pure (
      L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst remaining) ==
      (Valid.raw_equiv (Ghost.reveal vk) (fst (Ghost.reveal hd_val)) ||
       L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst tl_l))
    ));
    if found_here {
      // Key found.
      Trade.elim
        (cbor_map_entry_match cbor_raw_match pm_v entry hd_val **
         I.iterator_match (cbor_map_entry_match cbor_raw_match)
           (nondep_then parse_raw_data_item parse_raw_data_item) pm' tail_it tl_l)
        (I.iterator_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) p_cur cur remaining);
      r_found := true;
      r_cont := false;
    } else {
      // Not equivalent to this entry's key: advance.
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
      let empt = cbor_raw_nondet_map_iter_is_empty tail_it;
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
    ~(L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst remaining))));
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
   Raw-level NONDETERMINISTIC map-entry "prepend" core.

   Inserts a fresh (key, value) entry by PREPENDING it to the
   entry list of a nondeterministic CBOR map [x], provided the
   key is absent (up to structural equivalence [raw_equiv]) and
   the resulting length still fits in a u64.

   This is the nondet analog of
   [CBOR.Pulse.Raw.EverParse.Det.MapInsert.cbor_raw_det_map_entry_insert],
   but (1) the duplicate check uses [cbor_raw_nondet_map_key_present]
   (a [raw_equiv]-based scan) instead of the [==]-based deterministic
   scan, and (2) rather than running the sorted-insert engine we simply
   PREPEND the new entry: the result entry list is [new_entry :: existing].
   ============================================================ *)

(* Total accessor for a map's entry list (returns [] on non-maps), used in the
   postcondition where [xh] is not guarded by a [Map?] conjunct. *)
let map_payload (x: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match x with
  | Map _ v -> v
  | _ -> []

#push-options "--fuel 2 --ifuel 2 --z3rlimit 256 --ext no:context_pruning"

inline_for_extraction
fn cbor_raw_nondet_map_entry_insert
  (f64: squash FStar.SizeT.fits_u64)
  (x: cbor_raw)
  (key value: cbor_raw)
  (r1 r2: R.ref (IT.mixed_list (cbor_map_entry cbor_raw)))
  (ry: R.ref (cbor_map_entry cbor_raw))
  (#pm: perm) (#xh: Ghost.erased raw_data_item)
  (#pkv: perm) (#vk: Ghost.erased raw_data_item) (#vv: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm x xh **
  cbor_raw_match pkv key vk ** cbor_raw_match pkv value vv **
  (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy) **
  pure (Map? (Ghost.reveal xh) /\
        Valid.valid_raw_data_item (Ghost.reveal xh) == true /\
        Valid.valid_raw_data_item (Ghost.reveal vk) == true /\
        Valid.valid_raw_data_item (Ghost.reveal vv) == true)
returns res: option cbor_raw
ensures (match res with
  | None ->
    cbor_raw_match pm x xh **
    cbor_raw_match pkv key vk ** cbor_raw_match pkv value vv **
    (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy) **
    pure (L.existsb (Valid.raw_equiv (Ghost.reveal vk)) (L.map fst (map_payload (Ghost.reveal xh))) \/
          ~ (FStar.UInt.fits (L.length (map_payload (Ghost.reveal xh)) + 1) 64))
  | Some m ->
    exists* (pm_result: perm) (xh_result: raw_data_item).
      cbor_raw_match pm_result m xh_result **
      Trade.trade
        (cbor_raw_match pm_result m xh_result)
        (cbor_raw_match pm x xh **
         cbor_raw_match pkv key vk ** cbor_raw_match pkv value vv **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy)) **
      pure (Map? xh_result /\
            (Map?.v xh_result <: list (raw_data_item & raw_data_item)) ==
              (Ghost.reveal vk, Ghost.reveal vv) :: map_payload (Ghost.reveal xh) /\
            Valid.valid_raw_data_item xh_result == true /\
            (Map?.len xh_result <: raw_uint64) == Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (Map?.v xh_result))) /\
            FStar.UInt.fits (L.length (Map?.v xh_result)) U64.n))
{
  let l_raw : Ghost.erased (list (raw_data_item & raw_data_item)) =
    Ghost.hide (Map?.v (Ghost.reveal xh));
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
    // Surface validity of all map keys, needed by the dup-check.
    Valid.valid_eq SpecRaw.basic_data_model (Ghost.reveal xh);
    assert (pure (L.for_all Valid.valid_raw_data_item (L.map fst (Ghost.reveal l_raw)) == true));
    let present = cbor_raw_nondet_map_key_present f64 key ml0c #pm0 #l_raw #pkv #vk;
    if present {
      Trade.elim
        (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
          (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw))
        (cbor_raw_match pm x (Ghost.reveal xh));
      None #cbor_raw
    } else {
      // Key absent: build the new entry and PREPEND it.
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
      // Build a singleton mixed_list at ambient permission pm0.
      let sing_ml = Append.mixed_list_singleton_gen
        (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm0 pkv y_elem y_pair ry
        RME.cbor_map_entry_match_gather_aux;
      // Prepend: singleton BEFORE the borrowed entries.
      let res_ml = Append.mixed_list_append
        (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm0 sing_ml (Ghost.hide [Ghost.reveal y_pair]) ml0c l_raw r1 r2;
      let l_result : Ghost.erased (list (raw_data_item & raw_data_item)) =
        Ghost.hide (Ghost.reveal y_pair :: Ghost.reveal l_raw);
      rewrite (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml
                (List.Tot.append [Ghost.reveal y_pair] (Ghost.reveal l_raw)))
        as (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result));
      rewrite (Trade.trade
                 (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                   (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml
                   (List.Tot.append [Ghost.reveal y_pair] (Ghost.reveal l_raw)))
                 (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                    (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair] **
                  I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                    (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw) **
                  (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va)))
        as (Trade.trade
              (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result))
              (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair] **
               I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
                (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw) **
               (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va)));
      // Rebuild a CBOR map value.
      I.mixed_list_match_length (cbor_map_entry_match cbor_raw_match)
        (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result);
      let len_sz_rt = IT.mixed_list_length res_ml;
      let len64_rt = SZ.sizet_to_uint64 len_sz_rt;
      let len_size = ArrayBuilder.minimal_len_size len64_rt;
      ArrayBuilder.minimal_len_size_prop len64_rt;
      assert (pure (FStar.UInt.fits (SZ.v len_sz_rt) 64));
      let m = MB.cbor_mk_map_full f64 pm0 len_size res_ml #l_result;
      with xh2. assert (
        cbor_raw_match pm0 m (Ghost.reveal xh2) **
        Trade.trade
          (cbor_raw_match pm0 m (Ghost.reveal xh2))
          (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
            (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result)) **
        pure (Map? (Ghost.reveal xh2) /\
              (Map?.v (Ghost.reveal xh2) <: list (raw_data_item & raw_data_item)) == Ghost.reveal l_result /\
              (Map?.len (Ghost.reveal xh2)).size == len_size /\
              (Map?.len (Ghost.reveal xh2)).value == U64.uint_to_t (L.length (Ghost.reveal l_result)))
      );
      // The rebuilt length field is the minimal (canonical) encoding.
      assert (pure (len64_rt == U64.uint_to_t (L.length (Ghost.reveal l_result))));
      assert (pure (len_size == (Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (Ghost.reveal l_result)))).size));
      assert (pure ((Map?.len (Ghost.reveal xh2) <: raw_uint64) ==
                    Optimal.mk_raw_uint64 (U64.uint_to_t (L.length (Ghost.reveal l_result)))));
      assert (pure (FStar.UInt.fits (L.length (Ghost.reveal l_result)) U64.n));
      // Validity of the prepended map.
      assert (pure (Ghost.reveal xh == Map (Map?.len (Ghost.reveal xh)) (Map?.v (Ghost.reveal xh))));
      assert (pure (U64.v (Map?.len (Ghost.reveal xh2)).value == 1 + U64.v (Map?.len (Ghost.reveal xh)).value));
      MapPrepend.mk_cbor_map_prepend_valid
        (Map?.len (Ghost.reveal xh))
        (Map?.v (Ghost.reveal xh))
        (Ghost.reveal vk)
        (Ghost.reveal vv)
        (Map?.len (Ghost.reveal xh2));
      assert (pure (Valid.valid_raw_data_item (Ghost.reveal xh2) == true));
      // Compose all trades back to the original resources.
      Trade.intro_trade
        (cbor_raw_match pm0 m (Ghost.reveal xh2))
        (cbor_raw_match pm x (Ghost.reveal xh) **
         cbor_raw_match pkv key (Ghost.reveal vk) **
         cbor_raw_match pkv value (Ghost.reveal vv) **
         (exists* w1 w2 wy. R.pts_to r1 w1 ** R.pts_to r2 w2 ** R.pts_to ry wy))
        (Trade.trade
           (cbor_raw_match pm0 m (Ghost.reveal xh2))
           (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
             (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result)) **
         Trade.trade
           (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
             (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result))
           (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
             (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair] **
            I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
             (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw) **
            (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va)) **
         Trade.trade
           (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
             (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair])
           (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair) **
            (exists* vy. R.pts_to ry vy)) **
         Trade.trade
           (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair))
           (cbor_raw_match pkv key (Ghost.reveal vk) ** cbor_raw_match pkv value (Ghost.reveal vv)) **
         Trade.trade
           (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
             (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw))
           (cbor_raw_match pm x (Ghost.reveal xh)))
        fn _ {
          Trade.elim
            (cbor_raw_match pm0 m (Ghost.reveal xh2))
            (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result));
          Trade.elim
            (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm0 res_ml (Ghost.reveal l_result))
            (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair] **
             I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm0 ml0c (Ghost.reveal l_raw) **
             (exists* vb va. R.pts_to r1 vb ** R.pts_to r2 va));
          Trade.elim
            (I.mixed_list_match (cbor_map_entry_match cbor_raw_match)
              (nondep_then parse_raw_data_item parse_raw_data_item) pm0 sing_ml [Ghost.reveal y_pair])
            (cbor_map_entry_match cbor_raw_match pkv y_elem (Ghost.reveal y_pair) **
             (exists* vy. R.pts_to ry vy));
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

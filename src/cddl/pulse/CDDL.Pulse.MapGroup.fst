module CDDL.Pulse.MapGroup
#lang-pulse
include CDDL.Spec.MapGroup
include CDDL.Pulse.Base
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Util = CBOR.Spec.Util

module R = Pulse.Lib.Reference
module U64 = FStar.UInt64

type impl_map_group_result =
  | MGOK
  | MGFail
  | MGCutFail

unfold
let impl_map_group_pre
  (g: map_group)
  (f: map_constraint)
  (v: cbor)
  (m1 m2: cbor_map)
  (count: bool)
  (i: U64.t)
: Tot prop
= map_group_footprint g f /\
  cbor_map_disjoint m1 m2 /\
  cbor_map_disjoint_from_footprint m2 f /\
  (count ==> cbor_map_length m1 == U64.v i) /\
  begin match unpack v with
  | CMap m ->
    cbor_map_equal m (cbor_map_union m1 m2)
  | _ -> False
  end

let impl_map_group_post
  (g: map_group)
  (f: map_constraint)
  (v: cbor)
  (m1 m2: cbor_map)
  (count: bool)
  (i: U64.t)
  (i': U64.t)
  (res: impl_map_group_result)
: Tot prop
= impl_map_group_pre g f v m1 m2 count i /\
  begin match apply_map_group_det g m1, res with
  | MapGroupDet consumed remaining, MGOK ->
    (count ==> cbor_map_length remaining == U64.v i')
  | MapGroupFail, MGFail -> True
  | MapGroupCutFail, MGCutFail -> True
  | _ -> False
  end

inline_for_extraction
let impl_map_group_t
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (g: map_group)
  (f: map_constraint)
=
  (c: t) ->
  (#p: perm) ->
  (#v: Ghost.erased cbor) ->
  (v1: Ghost.erased cbor_map) ->
  (v2: Ghost.erased cbor_map) ->
  (count: bool) ->
  (pi: R.ref U64.t) ->
  (#i: Ghost.erased U64.t) ->
  stt impl_map_group_result
        (
          vmatch p c v **
          pts_to pi i **
          pure (impl_map_group_pre g f v v1 v2 count i)
        )
        (fun res -> exists* i' .
          vmatch p c v **
          pts_to pi i' **
          pure (impl_map_group_post g f v v1 v2 count i i' res)
        )

inline_for_extraction
fn apply_impl_map_group
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#g: Ghost.erased map_group)
  (#f: Ghost.erased map_constraint)
  (w: impl_map_group_t vmatch g f)
  (c: t)
  (#p: perm)
  (#v: Ghost.erased cbor)
  (v1: Ghost.erased cbor_map)
  (v2: Ghost.erased cbor_map)
  (count: bool)
  (pi: R.ref U64.t)
  (#i: Ghost.erased U64.t)
  (sq: squash (
    impl_map_group_pre g f v v1 v2 count i
  ))
requires
        (
          vmatch p c v **
          pts_to pi i
        )
returns res: impl_map_group_result
ensures
        (exists* i' .
          vmatch p c v **
          pts_to pi i' **
          pure (impl_map_group_post g f v v1 v2 count i i' res)
        )
{
  w c v1 v2 count pi
}

inline_for_extraction
fn impl_t_map_group
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (cbor_get_major_type: get_major_type_t vmatch)
  (get_map_length: get_map_length_t vmatch)
  (#g1: Ghost.erased map_group)
  (#f1: Ghost.erased map_constraint)
  (w1: impl_map_group_t vmatch g1 f1)
  (sq: squash (map_group_footprint g1 f1))
: impl_typ u#0 #_ vmatch #None (t_map g1)
= (c: _)
  (#p: _)
  (#v: _)
{
  let ty = cbor_get_major_type c;
  if (ty = cbor_major_type_map) {
    let m = Ghost.hide (CMap?.c (unpack v) <: cbor_map); // coercion needed because of the refinement on CMap?.c
    let rem0 : U64.t = get_map_length c;
    let mut remaining = rem0;
    let res : impl_map_group_result = w1 c m cbor_map_empty true remaining;
    match res {
      MGOK -> {
        let rem = !remaining;
        Classical.forall_intro cbor_map_length_empty_equiv;
        (rem = 0uL)
      }
      MGFail -> {
        false
      }
      MGCutFail -> {
        false
      }
    }
  } else {
    false
  }
}

inline_for_extraction
fn impl_map_group_nop
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (_: unit)
: impl_map_group_t #_ vmatch (map_group_nop) (map_constraint_empty)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (count: _)
  (pi: _)
  (#i: _)
{
  MGOK
}

inline_for_extraction
fn impl_map_group_always_false
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (_: unit)
: impl_map_group_t #_ vmatch (map_group_always_false) (map_constraint_empty)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (count: _)
  (pi: _)
  (#i: _)
{
  MGFail
}

inline_for_extraction
fn impl_map_group_concat
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#g1: Ghost.erased map_group)
  (#f1: Ghost.erased map_constraint)
  (w1: impl_map_group_t vmatch g1 f1)
  (#g2: Ghost.erased map_group)
  (#f2: Ghost.erased map_constraint)
  (w2: impl_map_group_t vmatch g2 f2)
  (prf: squash (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    map_constraint_disjoint f1 f2
  ))
: impl_map_group_t #_ vmatch (map_group_concat g1 g2) (map_constraint_choice f1 f2)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (count: _)
  (pi: _)
  (#i: _)
{
  let res1 = w1 c v1 v2 count pi;
  match res1 {
    MGOK -> {
      let m = Ghost.hide (CMap?.c (unpack v));
      let vres = Ghost.hide (apply_map_group_det g1 v1);
      let vconsumed = Ghost.hide (MapGroupDet?.consumed vres);
      let vremaining = Ghost.hide (MapGroupDet?.remaining vres);
      let v2' = Ghost.hide (cbor_map_union vconsumed v2);
      map_group_footprint_consumed_disjoint g1 f1 f2 v1;
      let res = w2 c vremaining v2' count pi;
      res
    }
    MGFail -> {
      MGFail
    }
    MGCutFail -> {
      MGCutFail
    }
  }
}

inline_for_extraction
fn impl_map_group_choice
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#g1: Ghost.erased map_group)
  (#f1: Ghost.erased map_constraint)
  (w1: impl_map_group_t vmatch g1 f1)
  (#g2: Ghost.erased map_group)
  (#f2: Ghost.erased map_constraint)
  (w2: impl_map_group_t vmatch g2 f2)
  (prf: squash (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2
  ))
: impl_map_group_t #_ vmatch (map_group_choice g1 g2) (map_constraint_choice f1 f2)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (count: _)
  (pi: _)
  (#i: _)
{
  let i0 = !pi;
  let res1 = w1 c v1 v2 count pi;
  match res1 {
    MGOK -> {
      MGOK
    }
    MGFail -> {
      pi := i0;
      let res = w2 c v1 v2 count pi;
      res
    }
    MGCutFail -> {
      MGCutFail
    }
  }
}

inline_for_extraction
fn impl_map_group_ext
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#g1: Ghost.erased map_group)
  (#f1: Ghost.erased map_constraint)
  (impl1: impl_map_group_t vmatch g1 f1)
  (g2: Ghost.erased map_group)
  (f2: Ghost.erased map_constraint)
  (sq: squash (
    map_group_footprint g1 f1 /\
    g2 == g1 /\
    map_constraint_included f1 f2
  ))
: impl_map_group_t #_ vmatch g2 f2
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (count: _)
  (pi: _)
  (#i: _)
{
  impl1 c v1 v2 count pi
}

inline_for_extraction
let impl_map_group_zero_or_one
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#g1: Ghost.erased map_group)
  (#f1: Ghost.erased map_constraint)
  (w1: impl_map_group_t vmatch g1 f1)
  (prf: squash (
    map_group_footprint g1 f1
  ))
: impl_map_group_t #_ vmatch (map_group_zero_or_one g1) f1
=
    (impl_map_group_choice
      w1
      (impl_map_group_nop ())
      ()
    )

let impl_map_group_match_item_for_body_post
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (cut: bool)
  (k: Ghost.erased cbor)
  (dest: Ghost.erased typ)
  (c: t)
  (p: perm)
  (v: Ghost.erased cbor)
  (v1: Ghost.erased cbor_map)
  (v2: Ghost.erased cbor_map)
  (count: bool)
  (pi: R.ref U64.t)
  (i: Ghost.erased U64.t)
  (res: impl_map_group_result)
= exists* i' .
          vmatch p c v **
          pts_to pi i' **
          pure (impl_map_group_post (map_group_match_item_for cut k dest) (map_group_match_item_for_footprint cut k dest) v v1 v2 count i i' res)

#push-options "--z3rlimit 32"

inline_for_extraction
fn impl_map_group_match_item_for_body
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (map_get: map_get_t vmatch)
  (cut: bool)
  (k: Ghost.erased cbor)
  (dest: Ghost.erased typ)
  (vdest: impl_typ vmatch dest)
  (c: t)
  (p: perm)
  (v: Ghost.erased cbor)
  (v1: Ghost.erased cbor_map)
  (v2: Ghost.erased cbor_map)
  (count: bool)
  (pi: R.ref U64.t)
  (i: Ghost.erased U64.t)
: with_cbor_literal_cont_t #_ vmatch k
          (vmatch p c v ** pts_to pi i **
            pure (impl_map_group_pre (map_group_match_item_for cut k dest) (map_group_match_item_for_footprint cut k dest) v v1 v2 count i)
          )
  impl_map_group_result
  (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 count pi i)
= (pk: _)
  (ck: _)
{
  let mg = map_get c ck;
  match mg {
    None -> {
      unfold (map_get_post vmatch c p v k None);
      unfold (map_get_post_none vmatch c p v k);
      fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 count pi i MGFail);
      MGFail
    }
    Some cv -> {
      unfold (map_get_post vmatch c p v k (Some cv));
      unfold (map_get_post_some vmatch c p v k cv);
      with pv vv . assert (vmatch pv cv vv);
      let check_value = vdest cv;
      Trade.elim _ _;
      if (check_value) {
        let rm' = Ghost.hide (MapGroupDet?.remaining (apply_map_group_det (map_group_match_item_for cut k dest) v1));
        if (count) {
          let i1 = !pi;
          cbor_map_length_empty_equiv v1;
          let i2 = U64.sub i1 1uL;
          pi := i2;
          cbor_map_length_disjoint_union (cbor_map_singleton k vv) rm';
          fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 count pi i MGOK);
          MGOK
        } else {
          fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 count pi i MGOK);
          MGOK
        }
      } else if cut {
        fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 count pi i MGCutFail);
        MGCutFail
      } else {
        fold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 count pi i MGFail);
        MGFail
      }
    }
  }
}

#pop-options

inline_for_extraction
fn impl_map_group_match_item_for
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (map_get: map_get_t vmatch)
  (cut: bool)
  (#k: Ghost.erased cbor)
  (wk: with_cbor_literal_t vmatch k)
  (#dest: Ghost.erased typ)
  (vdest: impl_typ vmatch dest)
: impl_map_group_t #_ vmatch (map_group_match_item_for cut k dest) (map_group_match_item_for_footprint cut k dest)
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (count: _)
  (pi: _)
  (#i: _)
{
  let res = wk _ _ _ (impl_map_group_match_item_for_body map_get cut k dest vdest c p v v1 v2 count pi i);
  unfold (impl_map_group_match_item_for_body_post vmatch cut k dest c p v v1 v2 count pi i);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_map_entry_cond
  (#t: Type)
  (vmatch2: perm -> t -> cbor & cbor -> slprop)
  (f: ((cbor & cbor) -> bool))
=
  (x: t) ->
  (#p: perm) ->
  (#v: Ghost.erased (cbor & cbor)) ->
  stt bool
    (vmatch2 p x v)
    (fun res -> vmatch2 p x v ** pure (res == f v))

let impl_map_group_filter_invariant_prop
  (f: ((cbor & cbor) -> bool))
  (v1 v2: cbor_map)
  (l: list (cbor & cbor))
  (vconsumed_past vremaining_past v1_future v2_past v2_future: cbor_map)
  (rem: U64.t)
  (b: bool)
: Tot prop
= b == Cons? l /\
  List.Tot.no_repeats_p (List.Tot.map fst l) /\
  (forall k . cbor_map_get (cbor_map_union v1_future v2_future) k == List.Tot.assoc k l) /\
  cbor_map_disjoint vconsumed_past vremaining_past /\
  cbor_map_disjoint (cbor_map_union vconsumed_past vremaining_past) v1_future /\
  v1 `cbor_map_equal` cbor_map_union (cbor_map_union vconsumed_past vremaining_past) v1_future /\
  cbor_map_disjoint v2_past v2_future /\
  v2 `cbor_map_equal` cbor_map_union v2_past v2_future /\
  begin
    let MapGroupDet vconsumed vremaining = apply_map_group_det (map_group_filter f) v1 in
    let MapGroupDet vconsumed_future vremaining_future = apply_map_group_det (map_group_filter f) v1_future in
    cbor_map_equal vconsumed (cbor_map_union vconsumed_past vconsumed_future) /\
    cbor_map_equal vremaining (cbor_map_union vremaining_past vremaining_future) /\
    U64.v rem == cbor_map_length vremaining_past + cbor_map_length v1_future
  end

let impl_map_group_filter_invariant_prop_intro
  (f: ((cbor & cbor) -> bool))
  (v1 v2: cbor_map)
  (l: list (cbor & cbor))
  (vconsumed_past vremaining_past v1_future v2_past v2_future: cbor_map)
  (rem: U64.t)
  (b: bool)
  (sq1: option (squash (b == Cons? l)))
  (sq2: option (squash (List.Tot.no_repeats_p (List.Tot.map fst l) /\
    (forall k . cbor_map_get (cbor_map_union v1_future v2_future) k == List.Tot.assoc k l)
  )))
  (sq3: option (squash (cbor_map_disjoint vconsumed_past vremaining_past)))
  (sq4: option (squash (cbor_map_disjoint (cbor_map_union vconsumed_past vremaining_past) v1_future)))
  (sq5: option (squash (v1 `cbor_map_equal` cbor_map_union (cbor_map_union vconsumed_past vremaining_past) v1_future)))
  (sq6: option (squash (cbor_map_disjoint v2_past v2_future)))
  (sq7: option (squash (v2 `cbor_map_equal` cbor_map_union v2_past v2_future)))
  (sq8: option (squash (
    let MapGroupDet vconsumed vremaining = apply_map_group_det (map_group_filter f) v1 in
    let MapGroupDet vconsumed_future vremaining_future = apply_map_group_det (map_group_filter f) v1_future in
    cbor_map_equal vconsumed (cbor_map_union vconsumed_past vconsumed_future) /\
    cbor_map_equal vremaining (cbor_map_union vremaining_past vremaining_future)
  )))
  (sq9: option (squash (
    U64.v rem == cbor_map_length vremaining_past + cbor_map_length v1_future
  )))
: Lemma
  ((Some? sq1 /\ Some? sq2 /\ Some? sq3 /\ Some? sq4 /\ Some? sq5 /\ Some? sq6 /\ Some? sq7 /\ Some? sq8 /\ Some? sq9) ==> impl_map_group_filter_invariant_prop f v1 v2 l vconsumed_past vremaining_past v1_future v2_past v2_future rem b)
= ()

module GR = Pulse.Lib.GhostReference
  
// [@@pulse_unfold]
let impl_map_group_filter_invariant
  (#t: Type0)
  (#cbor_map_iterator_t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (f: ((cbor & cbor) -> bool))
  (c: t)
  (p: perm)
  (v: cbor)
  (prem: R.ref U64.t)
  (v1 v2: cbor_map)
  (pj: R.ref cbor_map_iterator_t)
  (pconsumed_past premaining_past p1_future p2_past p2_future: GR.ref cbor_map)
  (b: bool)
: slprop
=
  exists* pl l j vconsumed_past vremaining_past v1_future v2_past v2_future rem . (
    pts_to pj j **
    cbor_map_iterator_match pl j l **
    Trade.trade
      (cbor_map_iterator_match pl j l)
      (vmatch p c v) **
    GR.pts_to pconsumed_past vconsumed_past **
    GR.pts_to premaining_past vremaining_past **
    GR.pts_to p1_future v1_future **
    GR.pts_to p2_past v2_past **
    GR.pts_to p2_future v2_future **
    R.pts_to prem rem **
    pure (impl_map_group_filter_invariant_prop f v1 v2 l vconsumed_past vremaining_past v1_future v2_past v2_future rem b)
  )

let abc_c'ba
  (a b c c': nat)
: Lemma
  (requires (
    a == b + c /\
    c' + b == a
  ))
  (ensures (
    c == c'
  ))
= ()

let cbor_map_of_list_uncons
  (k0 v0: cbor)
  (q: list (cbor & cbor))
  (m: cbor_map)
: Lemma
  (requires (
    let l = (k0, v0) :: q in
    List.Tot.no_repeats_p (List.Tot.map fst l) /\
    (forall k . cbor_map_get m k == List.Tot.assoc k l)
  ))
  (ensures (
    let s = cbor_map_singleton k0 v0 in
    cbor_map_included s m /\
    begin let m' = cbor_map_sub m s in
      cbor_map_disjoint s m' /\
      cbor_map_union s m' == m /\
      List.Tot.no_repeats_p (List.Tot.map fst q) /\
      (forall k . cbor_map_get m' k == List.Tot.assoc k q)
    end
  ))
= Classical.forall_intro (Util.list_assoc_no_repeats_mem q k0);
  Util.list_memP_map_forall fst q;
  ()

inline_for_extraction
let u64_sub
  (a b: U64.t)
: Pure U64.t
  (requires U64.v a >= U64.v b)
  (ensures fun res -> U64.v res == U64.v a - U64.v b)
= U64.sub a b

let cbor_map_sub_union_l
  (a b s: cbor_map)
: Lemma
  (requires (cbor_map_included s a /\
    cbor_map_disjoint a b
  ))
  (ensures (
    cbor_map_included s (cbor_map_union a b) /\
    cbor_map_sub (cbor_map_union a b) s `cbor_map_equal` cbor_map_union (cbor_map_sub a s) b
  ))
= ()

let add_sub_r
  (a b c: int)
: Lemma
  (a + (b - c) == (a + b) - c)
= ()

let add_sub_cancel
  (a b c: int)
: Lemma
  ((a + c) + (b - c) == a + b)
= ()

#push-options "--z3rlimit 32 --split_queries always --fuel 8 --ifuel 6"

#restart-solver
ghost
fn impl_map_group_filter_aux_skip
  (f: ((cbor & cbor) -> bool))
  (phi: map_constraint)
  (v1 v2: cbor_map)
  (hd_k hd_v: cbor)
  (tl: list (cbor & cbor))
  (pconsumed_past premaining_past p1_future p2_past p2_future: GR.ref cbor_map)
  (#vconsumed_past #vremaining_past #v1_future #v2_past #v2_future: cbor_map)
  (prem: R.ref U64.t)
  (#rem: U64.t)
requires
    (
      GR.pts_to pconsumed_past vconsumed_past **
      GR.pts_to premaining_past vremaining_past **
      GR.pts_to p1_future v1_future **
      GR.pts_to p2_past v2_past **
      GR.pts_to p2_future v2_future **
      R.pts_to prem rem **
      pure (
        map_group_footprint (map_group_filter f) phi /\
        cbor_map_disjoint v1 v2 /\
        cbor_map_disjoint_from_footprint v2 phi /\
        impl_map_group_filter_invariant_prop f v1 v2 ((hd_k, hd_v) :: tl) vconsumed_past vremaining_past v1_future v2_past v2_future rem true /\
        f (hd_k, hd_v) == true
      )
    )
ensures
    (exists* vconsumed_past' vremaining_past' v1_future' v2_past' v2_future' .
      GR.pts_to pconsumed_past vconsumed_past' **
      GR.pts_to premaining_past vremaining_past' **
      GR.pts_to p1_future v1_future' **
      GR.pts_to p2_past v2_past' **
      GR.pts_to p2_future v2_future' **
      R.pts_to prem rem **
      pure (
        impl_map_group_filter_invariant_prop f v1 v2 tl vconsumed_past' vremaining_past' v1_future' v2_past' v2_future' rem (Cons? tl)
      )
    )
{
  cbor_map_of_list_uncons hd_k hd_v tl (cbor_map_union v1_future v2_future);
  map_group_footprint_elim (map_group_filter f) phi v1_future v2_future;
  let s = (cbor_map_singleton hd_k hd_v);
  cbor_map_length_singleton hd_k hd_v;
  let chk = cbor_map_get v1_future hd_k;
  match chk {
    Some hd_v' -> {
      assert (pure (hd_v' == hd_v));
      let v1_future' = cbor_map_sub v1_future s;
      map_group_footprint_elim (map_group_filter f) phi v1_future' v2_future;
      cbor_map_length_disjoint_union s v1_future';
      cbor_map_length_disjoint_union vremaining_past s;
      let vremaining_past' = cbor_map_union vremaining_past s;
      GR.op_Colon_Equals p1_future v1_future';
      GR.op_Colon_Equals premaining_past vremaining_past';
      add_sub_cancel (cbor_map_length vremaining_past) (cbor_map_length v1_future) 1;
      impl_map_group_filter_invariant_prop_intro f v1 v2 tl vconsumed_past vremaining_past' v1_future' v2_past v2_future rem (Cons? tl) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ());
      ()
    }
    None -> {
      assert (pure (cbor_map_get v2_future hd_k == Some hd_v));
      let v2_future' = cbor_map_sub v2_future s;
      map_group_footprint_elim (map_group_filter f) phi v1_future v2_future';
      let v2_past' = cbor_map_union v2_past s;
      GR.op_Colon_Equals p2_future v2_future';
      GR.op_Colon_Equals p2_past v2_past';
      impl_map_group_filter_invariant_prop_intro f v1 v2 tl vconsumed_past vremaining_past v1_future v2_past' v2_future' rem (Cons? tl) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ());
      ()
    }
  }
}

#pop-options

#push-options "--z3rlimit 1024 --split_queries always --fuel 8 --ifuel 6"

#restart-solver
inline_for_extraction
fn impl_map_group_filter
  (#t #t2: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#vmatch2: perm -> t2 -> cbor & cbor -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (cbor_map_iterator_init: map_iterator_start_t vmatch cbor_map_iterator_match)
  (cbor_map_iterator_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (cbor_map_iterator_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (#f: Ghost.erased ((cbor & cbor) -> bool))
  (implf: impl_map_entry_cond vmatch2 f)
  (phi: Ghost.erased map_constraint)
  (sq: squash (map_group_footprint (map_group_filter f) phi))
: impl_map_group_t #_ vmatch (map_group_filter f) phi
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
  (count: bool)
  (pi: _)
  (#i: _)
{
if (not count) {
    MGOK
} else {
  let j0 = cbor_map_iterator_init c;
  with pl0 l0 . assert (cbor_map_iterator_match pl0 j0 l0);
  let mut pj = j0;
  let pconsumed_past : GR.ref cbor_map = GR.alloc cbor_map_empty;
  let premaining_past : GR.ref cbor_map = GR.alloc cbor_map_empty;
  let p1_future : GR.ref cbor_map = GR.alloc (Ghost.reveal v1);
  let p2_past : GR.ref cbor_map = GR.alloc cbor_map_empty;
  let p2_future : GR.ref cbor_map = GR.alloc (Ghost.reveal v2);
  fold (impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future (Cons? l0));
  let gres = Ghost.hide (apply_map_group_det (map_group_filter f) v1);
  let gconsumed = Ghost.hide (MapGroupDet?.consumed gres);
  let gremaining = Ghost.hide (MapGroupDet?.remaining gres);
  while (
    with b . assert (impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future b);
    unfold (impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future b);
    with pl j_ l . assert (pts_to pj j_ ** cbor_map_iterator_match pl j_ l ** Trade.trade (cbor_map_iterator_match pl j_ l) (vmatch p c v));
    let j = !pj;
    // FIXME: WHY WHY WHY those 2 rewrites?
    rewrite (cbor_map_iterator_match pl j_ l) as (cbor_map_iterator_match pl j l);
    rewrite (Trade.trade (cbor_map_iterator_match pl j_ l) (vmatch p c v)) as (Trade.trade (cbor_map_iterator_match pl j l) (vmatch p c v));
    let is_empty = cbor_map_iterator_is_empty j;
    let res = not is_empty;
    fold (impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future res);
    res
  ) invariant b . impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future b
  {
    unfold (impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future true);
    let chd = cbor_map_iterator_next pj;
    Trade.trans _ _ (vmatch p c v);
    with phd hd . assert (vmatch2 phd chd hd);
    let hd_k = Ghost.hide (fst hd);
    let hd_v = Ghost.hide (snd hd);
    with ptl itl tl . assert (cbor_map_iterator_match ptl itl tl);
    with v1_future . assert (GR.pts_to p1_future v1_future);
    with v2_future . assert (GR.pts_to p2_future v2_future);
    cbor_map_of_list_uncons hd_k hd_v tl (cbor_map_union v1_future v2_future);
    let test = implf chd;
    Trade.elim_hyp_l _ _ _;
    let s = Ghost.hide (cbor_map_singleton hd_k hd_v);
    with vconsumed_past . assert (GR.pts_to pconsumed_past vconsumed_past);
    with vremaining_past . assert (GR.pts_to premaining_past vremaining_past);
    map_group_footprint_elim (map_group_filter f) phi v1_future v2_future;
    with v2_past . assert (GR.pts_to p2_past v2_past);
    if (test) {
      impl_map_group_filter_aux_skip f phi v1 v2 hd_k hd_v tl pconsumed_past premaining_past p1_future p2_past p2_future pi;
      fold (impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future (Cons? tl))
    } else {
      assert (pure (cbor_map_included s (cbor_map_filter (Util.notp f) v1_future)));
      assert (pure (cbor_map_included s v1_future));
      let v1_future' = Ghost.hide (cbor_map_sub v1_future s);
      cbor_map_length_disjoint_union s v1_future';
      cbor_map_length_singleton hd_k hd_v;
      assert (pure (cbor_map_length v1_future' == cbor_map_length v1_future - 1));
      add_sub_r (cbor_map_length vremaining_past) (cbor_map_length v1_future) 1;
      GR.op_Colon_Equals p1_future v1_future';
      let vconsumed_past' = Ghost.hide (cbor_map_union s vconsumed_past);
      GR.op_Colon_Equals pconsumed_past vconsumed_past' ;
      let i = !pi;
      let i' = u64_sub i 1uL;
      pi := i' ;
      cbor_map_sub_union_l v1_future v2_future s;
      map_group_footprint_elim (map_group_filter f) phi v1_future' v2_future;
      impl_map_group_filter_invariant_prop_intro f v1 v2 tl vconsumed_past' vremaining_past v1_future' v2_past v2_future i' (Cons? tl) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ()) (Some ());
      fold (impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future (Cons? tl));
    }
  };
  unfold (impl_map_group_filter_invariant vmatch cbor_map_iterator_match f c p v pi v1 v2 pj pconsumed_past premaining_past p1_future p2_past p2_future false);
  Trade.elim _ _;
  with vconsumed_past . assert (GR.pts_to pconsumed_past vconsumed_past);
  GR.free pconsumed_past;
  with vremaining_past . assert (GR.pts_to premaining_past vremaining_past);
  GR.free premaining_past;
  with v1_future . assert (GR.pts_to p1_future v1_future);
  GR.free p1_future;
  with v2_past . assert (GR.pts_to p2_past v2_past);
  GR.free p2_past;
  with v2_future . assert (GR.pts_to p2_future v2_future);
  GR.free p2_future;
  assert (pure (cbor_map_equal v1_future cbor_map_empty));
  assert (pure (cbor_map_equal v2_future cbor_map_empty));
  assert (pure (cbor_map_equal vconsumed_past gconsumed));
  assert (pure (cbor_map_equal vremaining_past gremaining));
  MGOK
}}

#pop-options

inline_for_extraction
fn impl_map_entry_cond_matches_map_group_entry
  (#t #t2: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#vmatch2: perm -> t2 -> cbor & cbor -> slprop)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (#tkey: Ghost.erased typ)
  (fkey: impl_typ vmatch tkey)
  (#tvalue: Ghost.erased typ)
  (fvalue: impl_typ vmatch tvalue)
: impl_map_entry_cond u#0 #_ vmatch2 (matches_map_group_entry tkey tvalue)
= (x: _)
  (#p: _)
  (#v: _)
{
  let k = map_entry_key x;
  let testk = fkey k;
  Trade.elim _ _;
  if (testk) {
    let v = map_entry_value x;
    let testv = fvalue v;
    Trade.elim _ _;
    testv
  } else {
    false
  }
}

inline_for_extraction
fn impl_map_entry_cond_notp
  (#t: Type0)
  (#vmatch2: perm -> t -> (cbor & cbor) -> slprop)
  (#f: Ghost.erased ((cbor & cbor) -> bool))
  (implf: impl_map_entry_cond vmatch2 f)
: impl_map_entry_cond u#0 #_ vmatch2 (Util.notp f)
= (x: _)
  (#p: _)
  (#v: _)
{
  let test = implf x;
  not test
}

inline_for_extraction
fn impl_map_entry_cond_andp
  (#t: Type0)
  (#vmatch2: perm -> t -> (cbor & cbor) -> slprop)
  (#f: Ghost.erased ((cbor & cbor) -> bool))
  (implf: impl_map_entry_cond vmatch2 f)
  (#g: Ghost.erased ((cbor & cbor) -> bool))
  (implg: impl_map_entry_cond vmatch2 g)
: impl_map_entry_cond u#0 #_ vmatch2 (Util.andp f g)
= (x: _)
  (#p: _)
  (#v: _)
{
  let test = implf x;
  if (test) {
    implg x
  } else {
    false
  }
}

inline_for_extraction
fn impl_map_entry_cond_orp
  (#t: Type0)
  (#vmatch2: perm -> t -> (cbor & cbor) -> slprop)
  (#f: Ghost.erased ((cbor & cbor) -> bool))
  (implf: impl_map_entry_cond vmatch2 f)
  (#g: Ghost.erased ((cbor & cbor) -> bool))
  (implg: impl_map_entry_cond vmatch2 g)
: impl_map_entry_cond u#0 #_ vmatch2 (map_constraint_choice f g)
= (x: _)
  (#p: _)
  (#v: _)
{
  let test = implf x;
  if (test) {
    true
  } else {
    implg x
  }
}

inline_for_extraction
fn impl_map_entry_cond_empty
  (#t: Type0)
  (vmatch2: perm -> t -> (cbor & cbor) -> slprop)
: impl_map_entry_cond u#0 #_ vmatch2 map_constraint_empty
= (x: _)
  (#p: _)
  (#v: _)
{
  false
}

inline_for_extraction
let impl_zero_or_more_map_group_match_item_except
  (#t #t2: Type0)
  (#cbor_map_iterator_t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (cbor_map_iterator_init: map_iterator_start_t vmatch cbor_map_iterator_match)
  (cbor_map_iterator_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (cbor_map_iterator_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (#tkey #tvalue: Ghost.erased typ)
  (#texcept: Ghost.erased map_constraint)
  (fkey: impl_typ vmatch tkey)
  (fvalue: impl_typ vmatch tvalue)
  (fexcept: impl_map_entry_cond vmatch2 texcept)
: Tot (impl_map_group_t vmatch (map_group_filtered_table tkey tvalue texcept) (Util.andp (matches_map_group_entry tkey tvalue) (Util.notp texcept)))
= impl_map_group_ext
    (impl_map_group_filter
      cbor_map_iterator_init
      cbor_map_iterator_is_empty
      cbor_map_iterator_next
      #(Util.notp (Util.andp (matches_map_group_entry tkey tvalue) (Util.notp texcept)))
      (impl_map_entry_cond_notp
        (impl_map_entry_cond_andp
          (impl_map_entry_cond_matches_map_group_entry
            map_entry_key
            map_entry_value
            fkey
            fvalue
          )
          (impl_map_entry_cond_notp fexcept)
        )
      )
      (Util.andp (matches_map_group_entry tkey tvalue) (Util.notp texcept))
      ()
    )
    _ _
    ()

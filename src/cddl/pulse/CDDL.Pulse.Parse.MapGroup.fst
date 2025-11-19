module CDDL.Pulse.Parse.MapGroup
#lang-pulse
include CDDL.Pulse.MapGroup
include CDDL.Pulse.Parse.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64

let impl_zero_copy_map_group_pre
  (g: det_map_group)
  (f: map_constraint)
  (v: cbor)
  (m1 m2: cbor_map)
: Tot prop
=
  map_group_parser_spec_arg_prop g f m1 /\
  cbor_map_disjoint m1 m2 /\
  cbor_map_disjoint_from_footprint m2 f /\
  begin match unpack v with
  | CMap m ->
    cbor_map_equal m (cbor_map_union m1 m2)
  | _ -> False
  end

let impl_zero_copy_map_group_post
  (#tgt: Type0)
  (#tgt_size: tgt -> nat)
  (#tgt_prop: tgt -> bool)
  (#g: det_map_group)
  (#f: map_constraint)
  (ps: map_group_parser_spec g f tgt_size tgt_prop)
  (v: cbor)
  (m1 m2: cbor_map)
  (v': tgt)
: Tot prop
=
  impl_zero_copy_map_group_pre g f v m1 m2 /\
  (ps m1 <: tgt) == v'

inline_for_extraction
let impl_zero_copy_map_group
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (#g: det_map_group)
  (#f: map_constraint)
  (#tgt: Type0)
  (#tgt_size: tgt -> nat)
  (#tgt_prop: tgt -> bool)
  (ps: map_group_parser_spec g f tgt_size tgt_prop)
  (#impl_tgt: Type0)
  (r: rel impl_tgt tgt)
=
  (c: t) ->
  (#p: perm) ->
  (#v: Ghost.erased cbor) ->
  (v1: Ghost.erased cbor_map) ->
  (v2: Ghost.erased cbor_map) ->
  stt impl_tgt
        (
          vmatch p c v **
          pure (impl_zero_copy_map_group_pre g f v v1 v2)
        )
        (fun res -> exists* v' .
          r res v' **
          Trade.trade (r res v') (vmatch p c v) **
          pure (impl_zero_copy_map_group_post ps v v1 v2 v')
        )

module Util = CBOR.Spec.Util
#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 8 --query_stats --split_queries always"
#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_map
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t: Ghost.erased (det_map_group))
    (#[@@@erasable]fp: Ghost.erased map_constraint)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]tgt_size: Ghost.erased (tgt -> nat))
    (#[@@@erasable]tgt_serializable: Ghost.erased (tgt -> bool))
    (#[@@@erasable]ps: Ghost.erased (map_group_parser_spec t fp tgt_size tgt_serializable))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (pa: impl_zero_copy_map_group vmatch ps r)
    ([@@@erasable]sq: squash (
      map_group_footprint t fp
    ))
: impl_zero_copy_parse #ty vmatch #(t_map (Ghost.reveal t)) #tgt #(spec_map_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable)) (parser_spec_map_group (Ghost.reveal t) (Ghost.reveal ps) (spec_map_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable))) #impl_tgt r
=
  (c: _)
  (#p: _)
  (#v: _)
{
  let m : Ghost.erased cbor_map = Ghost.hide (CMap?.c (unpack v));
  let m1 : Ghost.erased cbor_map = Ghost.hide (cbor_map_filter (fp) m);
  let m2 : Ghost.erased cbor_map = Ghost.hide (cbor_map_filter (Util.notp (fp)) m);
  parser_spec_map_group_eq t ps (spec_map_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable)) v; // FIXME: WHY WHY WHY does the pattern not trigger?
  pa c m1 m2
}

unfold
let impl_zero_copy_map_ext_precond
    (t1: (det_map_group))
    (#fp1: map_constraint)
    (#tgt1: Type0)
    (#tgt_size1: (tgt1 -> nat))
    (#tgt_serializable1: (tgt1 -> bool))
    (ps1: (map_group_parser_spec t1 fp1 tgt_size1 tgt_serializable1))
    (t2: det_map_group)
    (#fp2: map_constraint)
    (#tgt_size2: (tgt1 -> nat))
    (#tgt_serializable2: (tgt1 -> bool))
    (ps2: (map_group_parser_spec t2 fp2 tgt_size2 tgt_serializable2))
: Tot prop
=
      map_group_footprint t1 fp1 /\
      t2 == t1 /\
      map_constraint_equiv fp1 fp2 /\
      (forall (x: cbor_map) .
        (map_group_parser_spec_arg_prop t1 fp1 x /\ map_group_parser_spec_arg_prop t2 fp2 x) ==>
        (ps1 x <: tgt1) == (ps2 (x <: map_group_parser_spec_arg t2 fp2) <: tgt1)
      )

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_map_ext
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (det_map_group))
    (#[@@@erasable]fp1: Ghost.erased map_constraint)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (map_group_parser_spec t1 fp1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_map_group vmatch ps1 r1)
    (#[@@@erasable]t2: Ghost.erased det_map_group)
    (#[@@@erasable]fp2: Ghost.erased map_constraint)
    (#[@@@erasable]tgt_size2: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable2: Ghost.erased (tgt1 -> bool))
    ([@@@erasable]ps2: Ghost.erased (map_group_parser_spec t2 fp2 tgt_size2 tgt_serializable2))
    ([@@@erasable]sq: squash (
      impl_zero_copy_map_ext_precond (Ghost.reveal t1) (Ghost.reveal ps1) (Ghost.reveal t2) (Ghost.reveal ps2)
    ))
: impl_zero_copy_map_group #ty vmatch #(Ghost.reveal t2) #(Ghost.reveal fp2)
#(tgt1) #(Ghost.reveal tgt_size2) #(Ghost.reveal tgt_serializable2) (Ghost.reveal ps2) #(impl_tgt1) (r1)
=
  (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  pa1 c v1 v2
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_map_nop_t
  (#ty: Type0)
  (vmatch: perm -> ty -> cbor -> slprop)
= impl_zero_copy_map_group #ty vmatch #_ #_
#unit #_ #_ mg_spec_nop.mg_parser  #(unit) (rel_unit)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_map_nop
  (#ty: Type0)
  (vmatch: perm -> ty -> cbor -> slprop)
: impl_zero_copy_map_nop_t #_ vmatch
=
  (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  rewrite emp as (rel_unit () ());
  intro
    (Trade.trade
      (rel_unit () ())
      (vmatch p c v)
    )
    #(vmatch p c v)
    fn _
  {
    rewrite (rel_unit () ()) as emp
  };
  ()
}

#set-options "--print_implicits"

#push-options "--ifuel 8"

#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_map_choice
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (det_map_group))
    (#[@@@erasable]fp1: Ghost.erased map_constraint)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (map_group_parser_spec t1 fp1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (va1: impl_map_group_t vmatch t1 fp1)
    (pa1: impl_zero_copy_map_group vmatch ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (det_map_group))
    (#[@@@erasable]fp2: Ghost.erased map_constraint)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable]tgt_size2: Ghost.erased (tgt2 -> nat))
    (#[@@@erasable]tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#[@@@erasable]ps2: Ghost.erased (map_group_parser_spec t2 fp2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_map_group vmatch ps2 r2)
    ([@@@erasable]sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2
    ))
: impl_zero_copy_map_group #ty vmatch #(map_group_choice (Ghost.reveal t1) (Ghost.reveal t2)) #(map_constraint_choice (Ghost.reveal fp1) (Ghost.reveal fp2))
#(either tgt1 tgt2) #(mg_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(mg_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (map_group_parser_spec_choice (Ghost.reveal ps1) (Ghost.reveal ps2) (mg_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (mg_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(either impl_tgt1 impl_tgt2) (rel_either r1 r2)
=
  (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  map_group_footprint_choice t1 t2 fp1 fp2;
  map_group_parser_spec_choice_eq (Ghost.reveal ps1) (Ghost.reveal ps2) (mg_spec_choice_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (mg_spec_choice_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) v1;
  let mut dummy = 0uL;
  let m1 = Ghost.hide (cbor_map_filter (fp1) v1);
  let cm1 = Ghost.hide (cbor_map_sub v1 m1);
  let v21 = Ghost.hide (cbor_map_union cm1 v2);
  let test1 = va1 c m1 v21 false dummy;
  if (MGOK? test1) {
    let w1 = pa1 c m1 v21;
    with z1 . assert (r1 w1 z1);
    let res : either impl_tgt1 impl_tgt2 = Inl w1;
    rel_either_eq_left r1 r2 w1 z1;
    Trade.rewrite_with_trade (r1 w1 z1) (rel_either r1 r2 res (Inl z1));
    Trade.trans _ _ (vmatch p c v);
    res
  } else {
    let m2 = Ghost.hide (cbor_map_filter (fp2) v1);
    let cm2 = Ghost.hide (cbor_map_sub v1 m2);
    let v22 = Ghost.hide (cbor_map_union cm2 v2);
    // FIXME: WHY WHY WHY those asserts?
    assert (pure (map_group_parser_spec_arg_prop t2 fp2 m2));
    assert (pure (cbor_map_disjoint m2 v22));
    assert (pure (cbor_map_disjoint_from_footprint v22 fp2));
    assert (pure (cbor_map_equal (cbor_map_union v1 v2) (cbor_map_union m2 v22)));
    let w2 = pa2 c m2 v22;
    with z2 . assert (r2 w2 z2);
    let res : either impl_tgt1 impl_tgt2 = Inr w2;
    rel_either_eq_right r1 r2 w2 z2;
    Trade.rewrite_with_trade (r2 w2 z2) (rel_either r1 r2 res (Inr z2));
    Trade.trans _ _ (vmatch p c v);
    res
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_map_zero_or_one
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (det_map_group))
    (#[@@@erasable]fp1: Ghost.erased map_constraint)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (map_group_parser_spec t1 fp1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (va1: impl_map_group_t vmatch t1 fp1)
    (pa1: impl_zero_copy_map_group vmatch ps1 r1)
    ([@@@erasable]sq: squash (
      map_group_footprint t1 fp1 /\
      MapGroupFail? (apply_map_group_det t1 cbor_map_empty)
    ))
: impl_zero_copy_map_group #ty vmatch #(map_group_zero_or_one (Ghost.reveal t1)) #(Ghost.reveal fp1)
#(option tgt1) #(map_group_size_zero_or_one (Ghost.reveal tgt_size1)) #(map_group_serializable_zero_or_one (Ghost.reveal tgt_serializable1)) (map_group_parser_spec_zero_or_one (Ghost.reveal ps1) ()) #(option impl_tgt1) (rel_option r1)
=
  (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  map_group_footprint_zero_or_one t1 fp1;
  map_group_parser_spec_choice_eq (Ghost.reveal ps1) mg_spec_nop.mg_parser (mg_spec_choice_size (Ghost.reveal tgt_size1) mg_spec_nop.mg_size) (mg_spec_choice_serializable (Ghost.reveal tgt_serializable1) mg_spec_nop.mg_serializable) v1;
  let mut dummy = 0uL;
  let m1 = Ghost.hide (cbor_map_filter (fp1) v1);
  let cm1 = Ghost.hide (cbor_map_sub v1 m1);
  let v21 = Ghost.hide (cbor_map_union cm1 v2);
  let test1 = va1 c m1 v21 false dummy;
  if (MGOK? test1) {
    let w1 = pa1 c m1 v21;
    with z1 . assert (r1 w1 z1);
    let res : option impl_tgt1 = Some w1;
    rel_option_eq_some r1 w1 z1;
    Trade.rewrite_with_trade (r1 w1 z1) (rel_option r1 res (Some z1));
    Trade.trans _ _ (vmatch p c v);
    res
  } else {
    let res : option impl_tgt1 = None #impl_tgt1;
    emp_unit (vmatch p c v);
    rel_option_eq_none r1;
    Trade.rewrite_with_trade (vmatch p c v) (rel_option r1 res None ** vmatch p c v);
    Trade.elim_hyp_r _ _ _;
    res
  }
}

let half_plus_half_eq
  (p: perm)
: Lemma
  (p /. 2.0R +. p /. 2.0R == p)
= ()

#push-options "--z3rlimit 16"

#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_map_concat
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (share: share_t vmatch)
  (gather: gather_t vmatch)
    (#[@@@erasable]t1: Ghost.erased (det_map_group))
    (#[@@@erasable]fp1: Ghost.erased map_constraint)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]tgt_size1: Ghost.erased (tgt1 -> nat))
    (#[@@@erasable]tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#[@@@erasable]ps1: Ghost.erased (map_group_parser_spec t1 fp1 tgt_size1 tgt_serializable1))
    ([@@@erasable]s1: Ghost.erased (map_group_serializer_spec ps1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_map_group vmatch ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (det_map_group))
    (#[@@@erasable]fp2: Ghost.erased map_constraint)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable]tgt_size2: Ghost.erased (tgt2 -> nat))
    (#[@@@erasable]tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#[@@@erasable]ps2: Ghost.erased (map_group_parser_spec t2 fp2 tgt_size2 tgt_serializable2))
    ([@@@erasable]s2: Ghost.erased (map_group_serializer_spec ps2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_map_group vmatch ps2 r2)
    ([@@@erasable]sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      (
        (map_constraint_disjoint fp1 fp2 /\
          map_group_parser_spec_domain_inj ps1 /\
          map_group_parser_spec_domain_inj ps2
        ) \/ map_constraint_disjoint_domains fp1 fp2 // this disjunction is provided for the future, if we ever want domain_inj to be governed by a Boolean argument on mg_spec rather than always holding.
      )
    ))
: impl_zero_copy_map_group #ty vmatch #(map_group_concat (Ghost.reveal t1) (Ghost.reveal t2)) #(map_constraint_choice (Ghost.reveal fp1) (Ghost.reveal fp2))
#(tgt1 & tgt2) #(mg_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(mg_spec_concat_serializable (Ghost.reveal s1) (Ghost.reveal s2)) (map_group_parser_spec_concat (Ghost.reveal s1) (Ghost.reveal s2) (mg_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (mg_spec_concat_serializable (Ghost.reveal s1) (Ghost.reveal s2))) #(impl_tgt1 & impl_tgt2) (rel_pair r1 r2)
=
  (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  map_group_footprint_concat t1 t2 fp1 fp2;
  map_group_parser_spec_concat_eq (Ghost.reveal s1) (Ghost.reveal s2) (mg_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (mg_spec_concat_serializable (Ghost.reveal s1) (Ghost.reveal s2)) v1;
  share c;
  intro
    (Trade.trade
      (vmatch (p /. 2.0R) c v ** vmatch (p /. 2.0R) c v)
      (vmatch p c v)
    )
    #emp
    fn _
  {
    gather c #(p /. 2.0R) #v #(p /. 2.0R) #v;
    half_plus_half_eq p;
    rewrite (vmatch (p /. 2.0R +. p /. 2.0R) c v)
      as (vmatch p c v)
  };
  let m1 = Ghost.hide (cbor_map_filter (fp1) v1);
  let cm1 = Ghost.hide (cbor_map_sub v1 m1);
  let v21 = Ghost.hide (cbor_map_union cm1 v2);
  // FIXME: WHY WHY WHY those asserts?
  assert (pure (map_group_parser_spec_arg_prop t1 fp1 m1));
  assert (pure (cbor_map_disjoint m1 v21));
  assert (pure (cbor_map_disjoint_from_footprint v21 fp1));
  assert (pure (cbor_map_equal (cbor_map_union v1 v2) (cbor_map_union m1 v21)));
  let w1 = pa1 c m1 v21;
  with z1 . assert (r1 w1 z1);
  Trade.trans_hyp_l _ _ _ _;
  let m2 = Ghost.hide (cbor_map_filter (fp2) v1);
  let cm2 = Ghost.hide (cbor_map_sub v1 m2);
  let v22 = Ghost.hide (cbor_map_union cm2 v2);
  // FIXME: WHY WHY WHY those asserts?
  assert (pure (map_group_parser_spec_arg_prop t2 fp2 m2));
  assert (pure (cbor_map_disjoint m2 v22));
  assert (pure (cbor_map_disjoint_from_footprint v22 fp2));
  assert (pure (cbor_map_equal (cbor_map_union v1 v2) (cbor_map_union m2 v22)));
  let w2 = pa2 c m2 v22;
  with z2 . assert (r2 w2 z2);
  Trade.trans_hyp_r _ _ _ _;
  let res = (w1, w2);
  rel_pair_eq r1 r2 w1 w2 z1 z2;
  Trade.rewrite_with_trade
    (r1 w1 z1 ** r2 w2 z2)
    (rel_pair r1 r2 res (z1, z2));
  Trade.trans _ _ (vmatch p c v);
  res
}

#pop-options

inline_for_extraction
fn impl_zero_copy_match_item_for_cont
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (get: map_get_t vmatch)
  ([@@@erasable]key: Ghost.erased cbor)
  ([@@@erasable]cut: Ghost.erased bool)
  (#[@@@erasable]value: Ghost.erased typ)
  (#[@@@erasable]tvalue: Type0)
  (#[@@@erasable]tvalue_ser: Ghost.erased (tvalue -> bool))
  (#[@@@erasable]pvalue: Ghost.erased (parser_spec value tvalue tvalue_ser))
  (#iv: Type0)
  (#[@@@erasable]r: rel iv tvalue)
  (ivalue: impl_zero_copy_parse vmatch pvalue r)
  (c: ty)
  (#p: perm)
  (#v: Ghost.erased cbor)
  (v1: Ghost.erased cbor_map)
  (v2: Ghost.erased cbor_map)
: with_cbor_literal_cont_t #ty vmatch (Ghost.reveal key)
        (
          vmatch p c v **
          pure (impl_zero_copy_map_group_pre (map_group_match_item_for (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal value)) (map_group_match_item_for_footprint (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal value)) v v1 v2)
        )
        iv
        (fun res -> exists* v' .
          r res v' **
          Trade.trade (r res v') (vmatch p c v) **
          pure (impl_zero_copy_map_group_post (map_group_parser_spec_match_item_for (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal pvalue) (mg_spec_match_item_for_size tvalue)) v v1 v2 v')
        )
=
  (pk: _)
  (ck: _)
{
  let ow = get c ck;
  let Some w = ow;
  unfold (map_get_post vmatch c p v key (Some w));
  unfold (map_get_post_some vmatch c p v key w);
  let res = ivalue w;
  Trade.trans _ _ (vmatch p c v);
  res
}

inline_for_extraction
fn impl_zero_copy_match_item_for
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (get: map_get_t vmatch)
  (#[@@@erasable]key: Ghost.erased cbor)
  (lkey: with_cbor_literal_t vmatch (Ghost.reveal key))
  ([@@@erasable]cut: Ghost.erased bool)
  (#[@@@erasable]value: Ghost.erased typ)
  (#[@@@erasable]tvalue: Type0)
  (#[@@@erasable]tvalue_ser: Ghost.erased (tvalue -> bool))
  (#[@@@erasable]pvalue: Ghost.erased (parser_spec value tvalue tvalue_ser))
  (#iv: Type0)
  (#[@@@erasable]r: rel iv tvalue)
  (ivalue: impl_zero_copy_parse vmatch pvalue r)
: impl_zero_copy_map_group #ty vmatch #(map_group_match_item_for (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal value)) #(map_group_match_item_for_footprint (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal value)) #tvalue #(mg_spec_match_item_for_size tvalue) #(Ghost.reveal tvalue_ser) (map_group_parser_spec_match_item_for (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal pvalue) (mg_spec_match_item_for_size tvalue)) #iv r
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  lkey _ _ _ (impl_zero_copy_match_item_for_cont get key cut ivalue c #p #v v1 v2)
}

#pop-options

module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest

noeq
type map_iterator_t
  (#ty: Type0) (#ty2: Type0) (cbor_map_iterator_t: Type0)
  (impl_elt1: Type0) (impl_elt2: Type0)
  (vmatch: perm -> ty -> cbor -> slprop)
  (vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  ([@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ([@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2)) // hopefully there should be at most one spec per impl_elt, otherwise Karamel monomorphization will introduce conflicts. Anyway, src_elt MUST NOT be extracted (it contains list types, etc.)
: Type0 = {
  cddl_map_iterator_contents: cbor_map_iterator_t;
  [@@@erasable]pm: perm;
  [@@@erasable]t1: Ghost.erased typ;
  [@@@erasable]sp1: Ghost.erased (spec t1 (dfst spec1) true); // I need to know that the parser is injective, to maintain the invariant on maps in rel_map_iterator
  [@@@erasable]eq1: Ghost.erased (EqTest.eq_test (dfst spec1));
  cddl_map_iterator_impl_validate1: impl_typ vmatch t1;
  cddl_map_iterator_impl_parse1: impl_zero_copy_parse vmatch sp1.parser (dsnd spec1);
  [@@@erasable]tex: Ghost.erased map_constraint;
  cddl_map_iterator_impl_validate_ex: impl_map_entry_cond vmatch2 tex;
  [@@@erasable]t2: Ghost.erased typ;
  [@@@erasable]ser2: Ghost.erased (dfst spec2 -> bool);
  [@@@erasable]ps2: Ghost.erased (parser_spec t2 (dfst spec2) ser2);
  cddl_map_iterator_impl_validate2: impl_typ vmatch t2;
  cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch ps2 (dsnd spec2);
}

inline_for_extraction
let cddl_map_iterator_impl_validate1
  (#ty: Type0) (#ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#[@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#[@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
: Tot (impl_typ vmatch i.t1)
= i.cddl_map_iterator_impl_validate1

inline_for_extraction
let cddl_map_iterator_impl_parse1
  (#ty: Type0) (#ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#[@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#[@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
: Tot (impl_zero_copy_parse vmatch i.sp1.parser (dsnd spec1))
= i.cddl_map_iterator_impl_parse1

inline_for_extraction
let cddl_map_iterator_impl_validate_ex
  (#ty: Type0) (#ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#[@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#[@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
: Tot (impl_map_entry_cond vmatch2 i.tex)
= i.cddl_map_iterator_impl_validate_ex

inline_for_extraction
let cddl_map_iterator_impl_validate2
  (#ty: Type0) (#ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#[@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#[@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
: Tot (impl_typ vmatch i.t2)
= i.cddl_map_iterator_impl_validate2

inline_for_extraction
let cddl_map_iterator_impl_parse2
  (#ty: Type0) (#ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#[@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#[@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
: Tot (impl_zero_copy_parse vmatch i.ps2 (dsnd spec2))
= i.cddl_map_iterator_impl_parse2

inline_for_extraction
let mk_map_iterator
  (#ty #ty2: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (cddl_map_iterator_contents: cbor_map_iterator_t)
  ([@@@erasable]pm: perm)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#[@@@erasable]src_elt1: Type0)
  (#[@@@erasable]r1: rel impl_elt1 src_elt1)
  (#[@@@erasable]t1: Ghost.erased typ)
  ([@@@erasable]sp1: Ghost.erased (spec t1 src_elt1 true))
  ([@@@erasable]eq1: Ghost.erased (EqTest.eq_test src_elt1))
  (cddl_map_iterator_impl_validate1: impl_typ vmatch t1)
  (cddl_map_iterator_impl_parse1: impl_zero_copy_parse vmatch sp1.parser r1)
  (#[@@@erasable]tex: Ghost.erased map_constraint)
  (cddl_map_iterator_impl_validate_ex: impl_map_entry_cond vmatch2 tex)
  (#[@@@erasable]src_elt2: Type0)
  (#[@@@erasable]r2: rel impl_elt2 src_elt2)
  (#[@@@erasable]t2: Ghost.erased typ)
  (#[@@@erasable]ser2: Ghost.erased (src_elt2 -> bool))
  (#[@@@erasable]ps2: Ghost.erased (parser_spec t2 src_elt2 ser2))
  (cddl_map_iterator_impl_validate2: impl_typ vmatch t2)
  (cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch ps2 r2)
: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 (Iterator.mk_spec r1) (Iterator.mk_spec r2)
= {
  cddl_map_iterator_contents = cddl_map_iterator_contents;
  pm = pm;
  t1 = t1;
  sp1 = sp1;
  eq1 = eq1;
  cddl_map_iterator_impl_validate1 = cddl_map_iterator_impl_validate1;
  cddl_map_iterator_impl_parse1 = cddl_map_iterator_impl_parse1;
  tex = tex;
  cddl_map_iterator_impl_validate_ex = cddl_map_iterator_impl_validate_ex;
  t2 = t2;
  ser2 = ser2;
  ps2 = ps2;
  cddl_map_iterator_impl_validate2 = cddl_map_iterator_impl_validate2;
  cddl_map_iterator_impl_parse2 = cddl_map_iterator_impl_parse2;
}

let mk_map_iterator_eq_postcond
  (#ty #ty2: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (cddl_map_iterator_contents: cbor_map_iterator_t)
  (pm: perm)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#src_elt1: Type0)
  (#r1: rel impl_elt1 src_elt1)
  (#t1: Ghost.erased typ)
  (sp1: Ghost.erased (spec t1 src_elt1 true))
  (eq1: Ghost.erased (EqTest.eq_test src_elt1))
  (tex: Ghost.erased map_constraint)
  (#src_elt2: Type0)
  (#r2: rel impl_elt2 src_elt2)
  (#t2: Ghost.erased typ)
  (#ser2: Ghost.erased (src_elt2 -> bool))
  (ps2: Ghost.erased (parser_spec t2 src_elt2 ser2))
  (res: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 (Iterator.mk_spec r1) (Iterator.mk_spec r2))
: Tot prop
=   res.cddl_map_iterator_contents == cddl_map_iterator_contents /\
    res.pm == pm /\
    res.t1 == t1 /\
    res.sp1 == sp1 /\
    res.tex == tex /\
    res.t2 == t2 /\
    res.ser2 == ser2 /\
    res.ps2 == ps2 /\
    True

let mk_map_iterator_eq
  (#ty #ty2: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (cddl_map_iterator_contents: cbor_map_iterator_t)
  (pm: perm)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#src_elt1: Type0)
  (#r1: rel impl_elt1 src_elt1)
  (#t1: Ghost.erased typ)
  (sp1: Ghost.erased (spec t1 src_elt1 true))
  (eq1: Ghost.erased (EqTest.eq_test src_elt1))
  (cddl_map_iterator_impl_validate1: impl_typ vmatch t1)
  (cddl_map_iterator_impl_parse1: impl_zero_copy_parse vmatch sp1.parser r1)
  (#tex: Ghost.erased map_constraint)
  (cddl_map_iterator_impl_validate_ex: impl_map_entry_cond vmatch2 tex)
  (#src_elt2: Type0)
  (#r2: rel impl_elt2 src_elt2)
  (#t2: Ghost.erased typ)
  (#ser2: Ghost.erased (src_elt2 -> bool))
  (#ps2: Ghost.erased (parser_spec t2 src_elt2 ser2))
  (cddl_map_iterator_impl_validate2: impl_typ vmatch t2)
  (cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch ps2 r2)
: Lemma
  (ensures (
    let res = mk_map_iterator cddl_map_iterator_contents pm sp1 eq1 cddl_map_iterator_impl_validate1 cddl_map_iterator_impl_parse1 cddl_map_iterator_impl_validate_ex cddl_map_iterator_impl_validate2 cddl_map_iterator_impl_parse2 in
    mk_map_iterator_eq_postcond cddl_map_iterator_contents pm sp1 eq1 tex ps2 res
  ))
  [SMTPat (mk_map_iterator cddl_map_iterator_contents pm sp1 eq1 cddl_map_iterator_impl_validate1 cddl_map_iterator_impl_parse1 cddl_map_iterator_impl_validate_ex cddl_map_iterator_impl_validate2 cddl_map_iterator_impl_parse2)]
= ()

module Map = CDDL.Spec.Map

let rec parse_table_entries
  (#src_elt1: Type0)
  (#t1: typ)
  (#ser1: (src_elt1 -> bool))
  (ps1: (parser_spec t1 src_elt1 ser1))
  (tex: map_constraint)
  (#src_elt2: Type0)
  (#t2: typ)
  (#ser2: (src_elt2 -> bool))
  (ps2: (parser_spec t2 src_elt2 ser2))
  (l: list (cbor & cbor))
: Tot (list (src_elt1 & src_elt2))
  (decreases l)
= match l with
  | [] -> []
  | (k, v) :: q ->
    let rq = parse_table_entries ps1 tex ps2 q in
    if t1 k && not (tex (k, v)) && t2 v
    then (ps1 k, ps2 v) :: rq
    else rq

let rec parse_table_entries_memP_key
  (#src_elt1: Type0)
  (#t1: typ)
  (sp1: spec t1 src_elt1 true)
  (tex: map_constraint)
  (#src_elt2: Type0)
  (#t2: typ)
  (#ser2: (src_elt2 -> bool))
  (ps2: (parser_spec t2 src_elt2 ser2))
  (l: list (cbor & cbor))
  (k: src_elt1)
: Lemma
  (requires (List.Tot.memP k (List.Tot.map fst (parse_table_entries sp1.parser tex ps2 l))))
  (ensures (
    sp1.serializable k /\
    List.Tot.memP (sp1.serializer k) (List.Tot.map fst l)
  ))
  (decreases l)
= match l with
  | (k', v') :: q ->
    if t1 k' && not (tex (k', v')) && t2 v' && FStar.StrongExcludedMiddle.strong_excluded_middle (sp1.parser k' == k)
    then ()
    else parse_table_entries_memP_key sp1 tex ps2 q k

let rec parse_table_entries_no_repeats
  (#src_elt1: Type0)
  (#t1: typ)
  (sp1: spec t1 src_elt1 true)
  (tex: map_constraint)
  (#src_elt2: Type0)
  (#t2: typ)
  (#ser2: (src_elt2 -> bool))
  (ps2: (parser_spec t2 src_elt2 ser2))
  (l: list (cbor & cbor))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l)
  ))
  (ensures (
    List.Tot.no_repeats_p (List.Tot.map fst (parse_table_entries sp1.parser tex ps2 l))
  ))
  (decreases l)
= match l with
  | [] -> ()
  | (k, v) :: q ->
    parse_table_entries_no_repeats sp1 tex ps2 q;
    if t1 k && not (tex (k, v)) && t2 v
    then Classical.move_requires (parse_table_entries_memP_key sp1 tex ps2 q) (sp1.parser k)
    else ()

let rel_map_iterator_cond
  (#ty #ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
  (s: Map.t (dfst spec1) (list (dfst spec2)))
  (l: list (cbor & cbor))
: Tot prop
= let l' = parse_table_entries i.sp1.parser i.tex i.ps2 l in
  s == map_of_list_pair i.eq1 l'
  /\ List.Tot.no_repeats_p (List.Tot.map fst l)

let rel_map_iterator_cond_post
  (#ty #ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
  (s: Map.t (dfst spec1) (list (dfst spec2)))
  (l: list (cbor & cbor))
: Lemma
  (requires (rel_map_iterator_cond i s l))
  (ensures (
    s == map_of_list_pair i.eq1 (parse_table_entries i.sp1.parser i.tex i.ps2 l)
  ))
= ()

let rel_map_iterator
  (#ty #ty2: Type0) (vmatch: perm -> ty -> cbor -> slprop)
  (vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (impl_elt1: Type0) (impl_elt2: Type0)
  (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: rel (map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2)))
= mk_rel (fun i s -> exists* (l: list (cbor & cbor)) . cbor_map_iterator_match i.pm i.cddl_map_iterator_contents l **
    pure (rel_map_iterator_cond i s l)
  )

inline_for_extraction
let rel_map_iterator_singletons
  (impl_elt1: Type0) (impl_elt2: Type0)
  (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec impl_elt1) -> [@@@erasable] Ghost.erased (Iterator.type_spec impl_elt2) -> Type0))
  (r: (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) -> (spec2: Ghost.erased (Iterator.type_spec impl_elt2)) -> iterator spec1 spec2 -> Map.t (dfst spec1) (list (dfst spec2)) -> slprop)
=
  (#spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ->
  (#spec2: Ghost.erased (Iterator.type_spec impl_elt2)) ->
  (i: iterator spec1 spec2) ->
  (s: Map.t (dfst spec1) (list (dfst spec2))) ->
  stt_ghost unit emp_inames
    (r spec1 spec2 i s)
    (fun _ -> r spec1 spec2 i s **
      pure (
        map_of_list_singletons s
      )
    )

inline_for_extraction
let rel_map_iterator_length
  (impl_elt1: Type0) (impl_elt2: Type0)
  (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec impl_elt1) -> [@@@erasable] Ghost.erased (Iterator.type_spec impl_elt2) -> Type0))
  (r: (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) -> (spec2: Ghost.erased (Iterator.type_spec impl_elt2)) -> iterator spec1 spec2 -> Map.t (dfst spec1) (list (dfst spec2)) -> slprop)
=
  (#spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ->
  (#spec2: Ghost.erased (Iterator.type_spec impl_elt2)) ->
  (i: iterator spec1 spec2) ->
  (s: Map.t (dfst spec1) (list (dfst spec2))) ->
  stt_ghost unit emp_inames
    (r spec1 spec2 i s)
    (fun _ -> r spec1 spec2 i s **
      pure (
        map_of_list_maps_to_nonempty s
      )
    )

ghost
fn rel_map_iterator_prop
  (#ty #ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
: rel_map_iterator_singletons impl_elt1 impl_elt2 (map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2) (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2)
=
  (#spec1: Ghost.erased (Iterator.type_spec impl_elt1))
  (#spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
  (s: Map.t (dfst spec1) (list (dfst spec2)))
{
  unfold (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i s);
  with l . assert (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents l);
  parse_table_entries_no_repeats i.sp1 i.tex i.ps2 l;
  map_of_list_pair_no_repeats_key i.eq1 (parse_table_entries i.sp1.parser i.tex i.ps2 l);  
  fold (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i s)
}

ghost
fn rel_map_iterator_prop'
  (#ty #ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
: rel_map_iterator_length impl_elt1 impl_elt2 (map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2) (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2)
=
  (#spec1: Ghost.erased (Iterator.type_spec impl_elt1))
  (#spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
  (s: Map.t (dfst spec1) (list (dfst spec2)))
{
  rel_map_iterator_prop cbor_map_iterator_match i s
}

inline_for_extraction noextract [@@noextract_to "krml"]
let cddl_map_iterator_is_empty_gen_t
  (impl_elt1: Type0) (impl_elt2: Type0)
  (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec impl_elt1) -> [@@@erasable] Ghost.erased (Iterator.type_spec impl_elt2) -> Type0))
  (r: (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) -> (spec2: Ghost.erased (Iterator.type_spec impl_elt2)) -> iterator spec1 spec2 -> Map.t (dfst spec1) (list (dfst spec2)) -> slprop)
=
  (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ->
  (spec2: Ghost.erased (Iterator.type_spec impl_elt2)) -> // taking `spec` as argument to the operator, rather than the type, guarantees that Karamel will produce it only (at most) once per `impl_elt` type.
  (i: iterator spec1 spec2) ->
  (#l: Ghost.erased (Map.t (dfst spec1) (list (dfst spec2)))) ->
  stt bool
    (r spec1 spec2 i l)
    (fun res ->
      r spec1 spec2 i l **
      pure (res == true <==> Ghost.reveal l == Map.empty (dfst spec1) (list (dfst spec2)))
    )

inline_for_extraction
let cddl_map_iterator_is_empty_t
  (#ty #ty2: Type0) (vmatch: perm -> ty -> cbor -> slprop)
  (vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (impl_elt1: Type0) (impl_elt2: Type0)
=
  cddl_map_iterator_is_empty_gen_t impl_elt1 impl_elt2
    (map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2)
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2)

#restart-solver

let rec rel_map_iterator_cond_is_empty
  (#ty #ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
  (s: Map.t (dfst spec1) (list (dfst spec2)))
  (l: list (cbor & cbor))
: Lemma
  (requires (
    let l' = parse_table_entries i.sp1.parser i.tex i.ps2 l in
    s == map_of_list_pair i.eq1 l'
  ))
  (ensures (
    s `Map.equal` Map.empty (dfst spec1) (list (dfst spec2)) <==> Nil? (parse_table_entries i.sp1.parser i.tex i.ps2 l)
  ))
  (decreases l)
= match l with
  | [] ->
    assert_norm (parse_table_entries i.sp1.parser i.tex i.ps2 [] == []);
    assert_norm (map_of_list_pair i.eq1 [] == Map.empty (dfst spec1) (list (dfst spec2)))
  | (k, v) :: q ->
    rel_map_iterator_cond_is_empty i (map_of_list_pair i.eq1 (parse_table_entries i.sp1.parser i.tex i.ps2 q)) q;
    let rq = parse_table_entries i.sp1.parser i.tex i.ps2 q in
    assert_norm (parse_table_entries i.sp1.parser i.tex i.ps2 ((k, v) :: q) == (
      if Ghost.reveal i.t1 k && not (Ghost.reveal i.tex (k, v)) && Ghost.reveal i.t2 v
      then (i.sp1.parser k, Ghost.reveal i.ps2 v) :: rq
      else rq
    ));
    if Ghost.reveal i.t1 k && not (Ghost.reveal i.tex (k, v)) && Ghost.reveal i.t2 v
    then begin
      map_of_list_pair_cons i.eq1 (i.sp1.parser k) (Ghost.reveal i.ps2 v) rq;
      ()
    end
    else ()

inline_for_extraction
fn cddl_map_iterator_is_empty
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_is_empty_t #ty #ty2 vmatch vmatch2 #cbor_map_iterator_t cbor_map_iterator_match impl_elt1 impl_elt2
=
  (spec1: _)
  (spec2: _)
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
  (#l: Ghost.erased (Map.t (dfst spec1) (list (dfst spec2))))
{
  unfold (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l);
  with li . assert (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li);
  Trade.refl (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li);
  let mut pj = i.cddl_map_iterator_contents;
  let mut pres = true;
  while (
    let res = !pres;
    if (res) {
      with gj lj . assert (pts_to pj gj ** cbor_map_iterator_match i.pm gj lj);
      let j = !pj;
      Trade.rewrite_with_trade (cbor_map_iterator_match i.pm gj lj)
        (cbor_map_iterator_match i.pm j lj);
      let test = map_is_empty j;
      let res = not test;
      Trade.elim _ (cbor_map_iterator_match i.pm gj lj);
      res
    } else {
      false
    }
  ) invariant b . exists* j lj res . (
    pts_to pj j **
    cbor_map_iterator_match i.pm j lj **
    Trade.trade
      (cbor_map_iterator_match i.pm j lj)
      (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li) **
    pts_to pres res **
    pure (
      Nil? (parse_table_entries i.sp1.parser i.tex i.ps2 li) == (res && Nil? (parse_table_entries i.sp1.parser i.tex i.ps2 lj))
    ) ** pure (
      b == (res && Cons? lj)
    )
  ) {
    let elt = map_next pj;
    Trade.trans _ _ (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li);
    let elt_key = map_entry_key elt;
    let test_key = cddl_map_iterator_impl_validate1 i elt_key;
    Trade.elim _ (vmatch2 _ elt _);
    if not test_key {
      Trade.elim_hyp_l _ _ _;
    } else {
      let test_ex = cddl_map_iterator_impl_validate_ex i elt;
      if test_ex {
        Trade.elim_hyp_l _ _ _;
      } else {
        let elt_value = map_entry_value elt;
        let test_value = cddl_map_iterator_impl_validate2 i elt_value;
        Trade.elim _ (vmatch2 _ elt _);
        Trade.elim_hyp_l _ _ _;
        pres := not test_value;
      }
    }
  };
  Trade.elim _ _;
  fold (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l);
  rel_map_iterator_cond_is_empty i l li;
  !pres
}

inline_for_extraction
let cddl_map_iterator_next_gen_t
  (impl_elt1: Type0) (impl_elt2: Type0)
  (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec impl_elt1) -> [@@@erasable] Ghost.erased (Iterator.type_spec impl_elt2) -> Type0))
  (r: (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) -> (spec2: Ghost.erased (Iterator.type_spec impl_elt2)) -> iterator spec1 spec2 -> Map.t (dfst spec1) (list (dfst spec2)) -> slprop)
=
  (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ->
  (spec2: Ghost.erased (Iterator.type_spec impl_elt2)) -> // taking `spec` as argument to the operator, rather than the type, guarantees that Karamel will produce it only (at most) once per `impl_elt` type.
  (pi: R.ref (iterator spec1 spec2)) ->
  (#i: Ghost.erased (iterator spec1 spec2)) ->
  (#l: Ghost.erased (Map.t (dfst spec1) (list (dfst spec2)))) ->
  stt (impl_elt1 & impl_elt2)
    (pts_to pi i **
      r spec1 spec2 i l **
      pure (~ (Ghost.reveal l == Map.empty (dfst spec1) (list (dfst spec2))))
    )
    (fun res -> exists* i' k v l' .
      pts_to pi i' **
      r spec1 spec2 i' l' **
      dsnd spec1 (fst res) k **
      dsnd spec2 (snd res) v **
      Trade.trade
        ((dsnd spec1 (fst res) k ** dsnd spec2 (snd res) v) ** r spec1 spec2 i' l')
        (r spec1 spec2 i l) **
      pure (exists eqtest .
        Ghost.reveal l == map_of_list_cons eqtest k v l'
      )
    )

inline_for_extraction
let cddl_map_iterator_next_t
  (#ty #ty2: Type0) (vmatch: perm -> ty -> cbor -> slprop)
  (vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)  
  (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (impl_elt1: Type0) (impl_elt2: Type0)
=
  cddl_map_iterator_next_gen_t impl_elt1 impl_elt2
    (map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2)
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2)

ghost
fn rel_map_iterator_fold
  (#ty #ty2: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)  
  (#cbor_map_iterator_t: Type0) 
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (#spec2: Ghost.erased (Iterator.type_spec impl_elt2))
  (i: map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2)
  (pm: perm)
  (contents: cbor_map_iterator_t)
  (li: list (cbor & cbor))
requires
  cbor_map_iterator_match pm contents li ** pure (
    i.pm == pm /. 2.0R /\
    i.cddl_map_iterator_contents == contents
    /\ List.Tot.no_repeats_p (List.Tot.map fst li)
  )
ensures exists* l .
  rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l **
  Trade.trade
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l)
    (cbor_map_iterator_match pm contents li) **
  pure (
    rel_map_iterator_cond i l li
  )
{
  let l' = parse_table_entries i.sp1.parser i.tex i.ps2 li;
  let l = map_of_list_pair i.eq1 l';
  map_share contents;
  rewrite (cbor_map_iterator_match (pm /. 2.0R) contents li)
    as (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li);
  fold (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l);
  intro
    (Trade.trade
      (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l)
      (cbor_map_iterator_match pm contents li)
    )
    #(cbor_map_iterator_match (pm /. 2.0R) contents li)
    fn _
  {
    unfold (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l);
    with li' . assert (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li');
    rewrite (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li')
      as (cbor_map_iterator_match (pm /. 2.0R) contents li');
    map_gather contents #(pm /. 2.0R) #li;
    rewrite (cbor_map_iterator_match (pm /. 2.0R +. pm /. 2.0R) contents li)
      as (cbor_map_iterator_match pm contents li)
  };
}
#pop-options
#show-options
#push-options "--z3rlimit_factor 4 --fuel 2 --ifuel 2 --split_queries always --query_stats"
inline_for_extraction
fn cddl_map_iterator_next
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_next_t #ty #ty2 vmatch vmatch2 #cbor_map_iterator_t cbor_map_iterator_match impl_elt1 impl_elt2
=
  (spec1: _)
  (spec2: _)
  (pi: _)
  (#gi: _)
  (#l: _)
{
  unfold (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l);
  with li . assert (cbor_map_iterator_match gi.pm gi.cddl_map_iterator_contents li);
  let i = !pi;
  rewrite (cbor_map_iterator_match gi.pm gi.cddl_map_iterator_contents li)
    as (cbor_map_iterator_match gi.pm i.cddl_map_iterator_contents li);
  intro
    (Trade.trade
      (cbor_map_iterator_match gi.pm i.cddl_map_iterator_contents li)
      (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l)
    )
    #emp
    fn _
  {
    rewrite (cbor_map_iterator_match gi.pm i.cddl_map_iterator_contents li)
      as (cbor_map_iterator_match gi.pm gi.cddl_map_iterator_contents li);
    fold (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l)
  };
  let mut pj = i.cddl_map_iterator_contents;
  let hd0 = map_next pj;
  Trade.trans _ _ (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l);
  let mut phd = hd0;
  while (
    with ghd pmhd vhd . assert (pts_to phd ghd ** vmatch2 pmhd ghd vhd);
    let hd = !phd;
    Trade.rewrite_with_trade (vmatch2 pmhd ghd vhd) (vmatch2 pmhd hd vhd);
    let hd_key = map_entry_key hd;
    let test_key = cddl_map_iterator_impl_validate1 i hd_key;
    Trade.elim (vmatch _ hd_key _) (vmatch2 pmhd hd vhd);
    if not test_key {
      Trade.elim (vmatch2 pmhd hd vhd) _;
      true
    } else {
      let hd_value = map_entry_value hd;
      let test_value = cddl_map_iterator_impl_validate2 i hd_value;
      Trade.elim (vmatch _ hd_value _) (vmatch2 pmhd hd vhd);
      if not test_value {
        Trade.elim (vmatch2 pmhd hd vhd) _;
        true
      } else {
        let test_ex = cddl_map_iterator_impl_validate_ex i hd;
        Trade.elim (vmatch2 pmhd hd vhd) _;
        test_ex
      }
    }
  ) invariant b . exists* hd pmhd vhd j lj .
    pts_to phd hd **
    vmatch2 pmhd hd vhd **
    pts_to pj j **
    cbor_map_iterator_match gi.pm j lj **
    Trade.trade
      (vmatch2 pmhd hd vhd ** cbor_map_iterator_match gi.pm j lj)
      (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l) **
    pure (
      List.Tot.no_repeats_p (List.Tot.map fst (vhd :: lj)) /\
      parse_table_entries i.sp1.parser i.tex i.ps2 li == parse_table_entries i.sp1.parser i.tex i.ps2 (vhd :: lj)
    ) ** pure (
      b == not (Ghost.reveal i.t1 (fst vhd) && not (Ghost.reveal i.tex (vhd)) && Ghost.reveal i.t2 (snd vhd))
    )
  {
    Trade.elim_hyp_l _ _ _;
    let hd = map_next pj;
    Trade.trans _ _ (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l);
    phd := hd
  };
  with pmhd ghd vhd . assert (pts_to phd ghd ** vmatch2 pmhd ghd vhd);
  let hd = !phd;
  Trade.rewrite_with_trade
    (vmatch2 pmhd ghd vhd)
    (vmatch2 pmhd hd vhd);
  Trade.trans_hyp_l _ _ _ _;
  map_entry_share hd;
  intro
    (Trade.trade
      (vmatch2 (pmhd /. 2.0R) hd vhd ** vmatch2 (pmhd /. 2.0R) hd vhd)
      (vmatch2 pmhd hd vhd)
    )
    #emp
    fn _
  {
    map_entry_gather hd;
    rewrite (vmatch2 (pmhd /. 2.0R +. pmhd /. 2.0R) hd vhd)
      as (vmatch2 pmhd hd vhd)
  };
  let hd_key = map_entry_key hd;
  Trade.trans_hyp_l _ _ _ (vmatch2 pmhd hd vhd);
  let hd_key_res = cddl_map_iterator_impl_parse1 i hd_key;
  Trade.trans_hyp_l _ _ _ (vmatch2 pmhd hd vhd);
  with vhd_key_res . assert (dsnd spec1 hd_key_res vhd_key_res);
  let hd_value = map_entry_value hd;
  Trade.trans_hyp_r _ _ _ (vmatch2 pmhd hd vhd);
  let hd_value_res = cddl_map_iterator_impl_parse2 i hd_value;
  Trade.trans_hyp_r _ _ _ (vmatch2 pmhd hd vhd);
  with vhd_value_res . assert (dsnd spec2 hd_value_res vhd_value_res);
  Trade.trans_hyp_l _ (vmatch2 _ _ _) _ _;
  with gj lj . assert (cbor_map_iterator_match gi.pm gj lj);
  let j = !pj;
  let i' : map_iterator_t cbor_map_iterator_t impl_elt1 impl_elt2 vmatch vmatch2 spec1 spec2 = { i with
    cddl_map_iterator_contents = j;
    pm = gi.pm /. 2.0R;
  };
  rel_map_iterator_fold map_share map_gather i' gi.pm _ _;
  Trade.trans_hyp_r _ _ _ _;
  pi := i';
  (hd_key_res, hd_value_res)
}

let list_assoc_no_repeats_mem'
  (#tk: eqtype)
  (#tv: Type)
  (l: list (tk & tv))
  (kv: (tk & tv))
: Lemma
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l) ==> (List.Tot.assoc (fst kv) l == Some (snd kv) <==> List.Tot.memP kv l)))
= CBOR.Spec.Util.list_assoc_no_repeats_mem l (fst kv) (snd kv)

let rec map_of_list_pair_parse_table_entries_mem
  (#tkey #tvalue: Type)
  (key_eq: EqTest.eq_test tkey)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint)
  (l: list (cbor & cbor))
  (sq: squash (
    List.Tot.no_repeats_p (List.Tot.map fst l)
  ))
  (kv: (tkey & list tvalue))
: Lemma
  (ensures (
    Map.mem kv (map_of_list_pair key_eq (parse_table_entries pkey.parser except pvalue.parser l)) <==> (
      pkey.serializable (fst kv) /\
      (
      exists kv' . List.Tot.memP kv' l /\
      (~ (except kv')) /\
      fst kv' == pkey.serializer (fst kv) /\
      value (snd kv') /\
      [pvalue.parser (snd kv')] == snd kv
  ))))
  (decreases l)
= parse_table_entries_no_repeats pkey except pvalue.parser l;
  map_of_list_pair_no_repeats_key key_eq (parse_table_entries pkey.parser except pvalue.parser l);
  match l with
  | [] -> ()
  | (k1, v1) :: q ->
    map_of_list_pair_parse_table_entries_mem key_eq pkey pvalue except q sq kv

let map_of_list_pair_parse_table_entries_correct
  (#tkey #tvalue: Type)
  (key_eq: EqTest.eq_test tkey)
  (#key #value: typ)
  (pkey: spec key tkey true)
  (#inj: bool)
  (pvalue: spec value tvalue inj)
  (except: map_constraint { map_constraint_value_injective key pvalue.parser except })
  (m1: map_group_parser_spec_arg (map_group_filtered_table key value except) (Util.andp (matches_map_group_entry key value) (Util.notp except)))
  (m2: cbor_map)
  (l: list (cbor & cbor))
: Lemma
  (requires (
    cbor_map_disjoint_from_footprint m2 (Util.andp (matches_map_group_entry key value) (Util.notp except)) /\
    (forall k . cbor_map_get (cbor_map_union m1 m2) k == List.Tot.assoc k l) /\
    List.Tot.no_repeats_p (List.Tot.map fst l)
  ))
  (ensures (
    map_of_list_pair key_eq (parse_table_entries pkey.parser except pvalue.parser l) `Map.equal` map_group_zero_or_more_match_item_parser pkey pvalue except m1
    // this also means that the order of elements in `l` is "erased" in the resulting map
  ))
= Classical.forall_intro (list_assoc_no_repeats_mem' l);
  let prf
    (kv: (tkey & list tvalue))
  : Lemma
    (Map.mem kv (map_of_list_pair key_eq (parse_table_entries pkey.parser except pvalue.parser l)) <==> Map.mem kv (map_group_zero_or_more_match_item_parser pkey pvalue except m1))
  = map_of_list_pair_parse_table_entries_mem key_eq pkey pvalue except l () kv;
    map_group_zero_or_more_match_item_parser'_mem pkey pvalue except m1 kv;
    ()
  in
  Classical.forall_intro prf

// FIXME: WHY WHY WHY is it SO tedious to prove this:
let impl_zero_copy_map_zero_or_more_aux
  (#ty #ty2: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)  
  (#cbor_map_iterator_t: Type0)
    (#key: Ghost.erased typ)
    (#tkey: Type0)
    (key_eq: Ghost.erased (EqTest.eq_test tkey))
    (sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (r1: rel ikey tkey)
    (#value: Ghost.erased typ)
    (#tvalue: Type0)
    (#inj: Ghost.erased bool)
    (sp2: Ghost.erased (spec value tvalue inj))
    (except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (#ivalue: Type0)
    (r2: rel ivalue tvalue)
    (v: cbor)
    (m1 m2: cbor_map)
    (pm: perm)
    (i: map_iterator_t cbor_map_iterator_t ikey ivalue vmatch vmatch2 (Iterator.mk_spec r1) (Iterator.mk_spec r2))
    (contents: cbor_map_iterator_t)
    (li: list (cbor & cbor))
    (s: Map.t (dfst (Iterator.mk_spec r1)) (list (dfst (Iterator.mk_spec r2))))
: Lemma
  (requires (
    impl_zero_copy_map_group_pre
      (map_group_filtered_table key value except)
      (Util.andp (matches_map_group_entry key value) (Util.notp except))
      v m1 m2 /\
    (forall k . cbor_map_get (cbor_map_union m1 m2) k == List.Tot.assoc k li) /\
    rel_map_iterator_cond i s li /\
    mk_map_iterator_eq_postcond contents pm sp1 key_eq except sp2.parser i
  ))
  (ensures (
    impl_zero_copy_map_group_post
      (map_group_zero_or_more_match_item_parser sp1 sp2 except)
      v m1 m2 s
  ))
= map_of_list_pair_parse_table_entries_correct key_eq sp1 sp2 except m1 m2 li;
  assert (rel_map_iterator_cond i s li);
  EqTest.eq_test_unique i.eq1 key_eq;
  rel_map_iterator_cond_post i s li;
  assert (s == map_of_list_pair i.eq1 (parse_table_entries i.sp1.parser i.tex i.ps2 li));
  assert (i.eq1 == key_eq);
  assert (sp1 == i.sp1);
  assert (except == i.tex);
  assert (i.t2 == value);
  assert (Ghost.reveal i.ser2 == coerce_eq (_ by (FStar.Tactics.norm [delta_only [`%dfst; `%Mkdtuple2?._1; `%Iterator.mk_spec;]; iota; primops]; FStar.Tactics.trefl ())) sp2.serializable);
  assert (sp2.parser == coerce_eq () (Ghost.reveal i.ps2));
  assert (parse_table_entries sp1.parser except sp2.parser li == parse_table_entries i.sp1.parser i.tex i.ps2 li);
  assert (s == map_of_list_pair key_eq (parse_table_entries sp1.parser except sp2.parser li));
  ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_map_zero_or_more'
  (#ty #ty2: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)  
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (map_iterator_start: map_iterator_start_t vmatch cbor_map_iterator_match)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    ([@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (va1: impl_typ vmatch key) // MUST be a function pointer
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_zero_copy_parse vmatch sp1.parser r1) // MUST be a function pointer
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    ([@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (va2: impl_typ vmatch value) // MUST be a function pointer
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_zero_copy_parse vmatch sp2.parser r2) // MUST be a function pointer
    (#[@@@erasable]except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2 except) // MUST be a function pointer
: impl_zero_copy_map_group
    #ty
    vmatch
    #(map_group_filtered_table (Ghost.reveal key) (Ghost.reveal value) (Ghost.reveal except))
    #(Util.andp (matches_map_group_entry (Ghost.reveal key) (Ghost.reveal value)) (Util.notp (Ghost.reveal except)))
    #(Map.t tkey (list tvalue))
    #(map_group_zero_or_more_match_item_length #tkey #tvalue)
    #(map_group_zero_or_more_match_item_serializable (Ghost.reveal sp1) (Ghost.reveal sp2) (Ghost.reveal except))
    (map_group_zero_or_more_match_item_parser (Ghost.reveal sp1) (Ghost.reveal sp2) (Ghost.reveal except))
    #(map_iterator_t cbor_map_iterator_t ikey ivalue vmatch vmatch2 (Iterator.mk_spec r1) (Iterator.mk_spec r2))
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2))
=
  (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  let i = map_iterator_start c;
  with pl l . assert (cbor_map_iterator_match pl i l);
  let res : map_iterator_t cbor_map_iterator_t ikey ivalue vmatch vmatch2 (Iterator.mk_spec r1) (Iterator.mk_spec r2) = mk_map_iterator i (pl /. 2.0R) sp1 key_eq va1 pa1 va_ex va2 pa2;
  mk_map_iterator_eq i (pl /. 2.0R) sp1 key_eq va1 pa1 va_ex va2 pa2;
  rel_map_iterator_fold map_share map_gather res pl i l;
  Trade.trans _ (cbor_map_iterator_match pl i l) _;
  with s . assert (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) res s);
  impl_zero_copy_map_zero_or_more_aux key_eq sp1 r1 sp2 except r2 v v1 v2 (pl /. 2.0R) res i l s;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_map_zero_or_more
  (#ty #ty2: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)  
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (map_iterator_start: map_iterator_start_t vmatch cbor_map_iterator_match)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    ([@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (va1: impl_typ vmatch key) // MUST be a function pointer
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_zero_copy_parse vmatch sp1.parser r1) // MUST be a function pointer
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    ([@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (va2: impl_typ vmatch value) // MUST be a function pointer
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_zero_copy_parse vmatch sp2.parser r2) // MUST be a function pointer
    (#[@@@erasable]except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2 except) // MUST be a function pointer
: impl_zero_copy_map_group
    #ty
    vmatch
    #(map_group_filtered_table (Ghost.reveal key) (Ghost.reveal value) (Ghost.reveal except))
    #(Util.andp (matches_map_group_entry (Ghost.reveal key) (Ghost.reveal value)) (Util.notp (Ghost.reveal except)))
    #(Map.t tkey (list tvalue))
    #(map_group_zero_or_more_match_item_length #tkey #tvalue)
    #(map_group_zero_or_more_match_item_serializable (Ghost.reveal sp1) (Ghost.reveal sp2) (Ghost.reveal except) )
    (map_group_zero_or_more_match_item_parser (Ghost.reveal sp1) (Ghost.reveal sp2) (Ghost.reveal except))
    #(either (slice (ikey & ivalue)) (map_iterator_t cbor_map_iterator_t ikey ivalue vmatch vmatch2 (Iterator.mk_spec r1) (Iterator.mk_spec r2)))
    (rel_either_left (rel_slice_of_table key_eq r1 r2) (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2)))
=
  (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  let rres = impl_zero_copy_map_zero_or_more' map_iterator_start map_share map_gather key_eq sp1 va1 pa1 sp2 va2 pa2 va_ex c v1 v2;
  with vres . assert (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) rres vres);
  let res : either (slice (ikey & ivalue)) (map_iterator_t cbor_map_iterator_t ikey ivalue vmatch vmatch2 (Iterator.mk_spec r1) (Iterator.mk_spec r2)) = Inr rres;
  Trade.rewrite_with_trade
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) rres vres)
    (rel_either_left (rel_slice_of_table key_eq r1 r2) (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2)) res vres);
  Trade.trans _ _ (vmatch p c v);
  res
}
#pop-options
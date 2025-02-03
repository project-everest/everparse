module CDDL.Pulse.Parse.MapGroup
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
  (f: typ)
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
  (#f: typ)
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
  (#f: typ)
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

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_map
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
    (#t: Ghost.erased (det_map_group))
    (#fp: Ghost.erased typ)
    (#tgt: Type0)
    (#tgt_size: Ghost.erased (tgt -> nat))
    (#tgt_serializable: Ghost.erased (tgt -> bool))
    (#ps: Ghost.erased (map_group_parser_spec t fp tgt_size tgt_serializable))
    (#impl_tgt: Type0)
    (#r: rel impl_tgt tgt)
    (pa: impl_zero_copy_map_group vmatch ps r)
    (sq: squash (
      map_group_footprint t fp
    ))
: impl_zero_copy_parse #ty vmatch #(t_map (Ghost.reveal t)) #tgt #(spec_map_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable)) (parser_spec_map_group (Ghost.reveal t) (Ghost.reveal ps) (spec_map_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable))) #impl_tgt r
=
  (c: _)
  (#p: _)
  (#v: _)
{
  let m : Ghost.erased cbor_map = Ghost.hide (CMap?.c (unpack v));
  let m1 : Ghost.erased cbor_map = Ghost.hide (cbor_map_filter (matches_map_group_entry fp any) m);
  let m2 : Ghost.erased cbor_map = Ghost.hide (cbor_map_filter (Util.notp (matches_map_group_entry fp any)) m);
  parser_spec_map_group_eq t ps (spec_map_group_serializable (Ghost.reveal tgt_size) (Ghost.reveal tgt_serializable)) v; // FIXME: WHY WHY WHY does the pattern not trigger?
  pa c m1 m2
}
```

#set-options "--print_implicits"

#push-options "--ifuel 8"

#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_map_choice
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
    (#t1: Ghost.erased (det_map_group))
    (#fp1: Ghost.erased typ)
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (map_group_parser_spec t1 fp1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (va1: impl_map_group_t vmatch t1 fp1)
    (pa1: impl_zero_copy_map_group vmatch ps1 r1)
    (#t2: Ghost.erased (det_map_group))
    (#fp2: Ghost.erased typ)
    (#tgt2: Type0)
    (#tgt_size2: Ghost.erased (tgt2 -> nat))
    (#tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#ps2: Ghost.erased (map_group_parser_spec t2 fp2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_map_group vmatch ps2 r2)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2
    ))
: impl_zero_copy_map_group #ty vmatch #(map_group_choice (Ghost.reveal t1) (Ghost.reveal t2)) #(t_choice (Ghost.reveal fp1) (Ghost.reveal fp2))
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
  let m1 = Ghost.hide (cbor_map_filter (matches_map_group_entry fp1 any) v1);
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
    let m2 = Ghost.hide (cbor_map_filter (matches_map_group_entry fp2 any) v1);
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_map_zero_or_one
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
    (#t1: Ghost.erased (det_map_group))
    (#fp1: Ghost.erased typ)
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (map_group_parser_spec t1 fp1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (va1: impl_map_group_t vmatch t1 fp1)
    (pa1: impl_zero_copy_map_group vmatch ps1 r1)
    (sq: squash (
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
  let m1 = Ghost.hide (cbor_map_filter (matches_map_group_entry fp1 any) v1);
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
```

let half_plus_half_eq
  (p: perm)
: Lemma
  (p /. 2.0R +. p /. 2.0R == p)
= ()

#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_zero_copy_map_concat
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (share: share_t vmatch)
  (gather: gather_t vmatch)
    (#t1: Ghost.erased (det_map_group))
    (#fp1: Ghost.erased typ)
    (#tgt1: Type0)
    (#tgt_size1: Ghost.erased (tgt1 -> nat))
    (#tgt_serializable1: Ghost.erased (tgt1 -> bool))
    (#ps1: Ghost.erased (map_group_parser_spec t1 fp1 tgt_size1 tgt_serializable1))
    (#impl_tgt1: Type0)
    (#r1: rel impl_tgt1 tgt1)
    (pa1: impl_zero_copy_map_group vmatch ps1 r1)
    (#t2: Ghost.erased (det_map_group))
    (#fp2: Ghost.erased typ)
    (#tgt2: Type0)
    (#tgt_size2: Ghost.erased (tgt2 -> nat))
    (#tgt_serializable2: Ghost.erased (tgt2 -> bool))
    (#ps2: Ghost.erased (map_group_parser_spec t2 fp2 tgt_size2 tgt_serializable2))
    (#impl_tgt2: Type0)
    (#r2: rel impl_tgt2 tgt2)
    (pa2: impl_zero_copy_map_group vmatch ps2 r2)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      typ_disjoint fp1 fp2
    ))
: impl_zero_copy_map_group #ty vmatch #(map_group_concat (Ghost.reveal t1) (Ghost.reveal t2)) #(t_choice (Ghost.reveal fp1) (Ghost.reveal fp2))
#(tgt1 & tgt2) #(mg_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) #(mg_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) (map_group_parser_spec_concat (Ghost.reveal ps1) (Ghost.reveal ps2) (mg_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (mg_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2))) #(impl_tgt1 & impl_tgt2) (rel_pair r1 r2)
=
  (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  map_group_footprint_concat t1 t2 fp1 fp2;
  map_group_parser_spec_concat_eq (Ghost.reveal ps1) (Ghost.reveal ps2) (mg_spec_concat_size (Ghost.reveal tgt_size1) (Ghost.reveal tgt_size2)) (mg_spec_concat_serializable (Ghost.reveal tgt_serializable1) (Ghost.reveal tgt_serializable2)) v1;
  share c;
  ghost fn aux (_: unit)
  requires emp ** (vmatch (p /. 2.0R) c v ** vmatch (p /. 2.0R) c v)
  ensures vmatch p c v
  {
    gather c #(p /. 2.0R) #v #(p /. 2.0R) #v;
    rewrite (vmatch (p /. 2.0R +. p /. 2.0R) c v)
      as (vmatch p c v)
  };
  Trade.intro _ _ _ aux;
  let m1 = Ghost.hide (cbor_map_filter (matches_map_group_entry fp1 any) v1);
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
  let m2 = Ghost.hide (cbor_map_filter (matches_map_group_entry fp2 any) v1);
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
```

inline_for_extraction
```pulse
fn impl_zero_copy_match_item_for_cont
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (get: map_get_t vmatch)
  (key: Ghost.erased cbor)
  (cut: Ghost.erased bool)
  (#value: Ghost.erased typ)
  (#tvalue: Type0)
  (#tvalue_ser: Ghost.erased (tvalue -> bool))
  (#pvalue: parser_spec value tvalue tvalue_ser)
  (#iv: Type0)
  (#r: rel iv tvalue)
  (ivalue: impl_zero_copy_parse vmatch pvalue r)
  (c: ty)
  (#p: perm)
  (#v: Ghost.erased cbor)
  (v1: Ghost.erased cbor_map)
  (v2: Ghost.erased cbor_map)
: with_cbor_literal_cont_t #ty vmatch (Ghost.reveal key)
        (
          vmatch p c v **
          pure (impl_zero_copy_map_group_pre (map_group_match_item_for (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal value)) (t_literal (Ghost.reveal key)) v v1 v2)
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
  unfold (map_get_post vmatch c p v key ow);
  unfold (map_get_post_some vmatch c p v key w);
  let res = ivalue w;
  Trade.trans _ _ (vmatch p c v);
  res
}
```

inline_for_extraction
```pulse
fn impl_zero_copy_match_item_for
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (get: map_get_t vmatch)
  (#key: Ghost.erased cbor)
  (lkey: with_cbor_literal_t vmatch (Ghost.reveal key))
  (cut: Ghost.erased bool)
  (#value: Ghost.erased typ)
  (#tvalue: Type0)
  (#tvalue_ser: Ghost.erased (tvalue -> bool))
  (#pvalue: parser_spec value tvalue tvalue_ser)
  (#iv: Type0)
  (#r: rel iv tvalue)
  (ivalue: impl_zero_copy_parse vmatch pvalue r)
: impl_zero_copy_map_group #ty vmatch #(map_group_match_item_for (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal value)) #(t_literal (Ghost.reveal key)) #tvalue #(mg_spec_match_item_for_size tvalue) #(Ghost.reveal tvalue_ser) (map_group_parser_spec_match_item_for (Ghost.reveal cut) (Ghost.reveal key) (Ghost.reveal pvalue) (mg_spec_match_item_for_size tvalue)) #iv r
= (c: _)
  (#p: _)
  (#v: _)
  (v1: _)
  (v2: _)
{
  lkey _ _ _ (impl_zero_copy_match_item_for_cont get key cut ivalue c #p #v v1 v2)
}
```

#pop-options

module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest

noeq
type map_iterator_t
  (#ty: Type0) (vmatch: perm -> ty -> cbor -> slprop) (cbor_map_iterator_t: Type0)
  (impl_elt1: Type0) (impl_elt2: Type0)
  (spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1)) (spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2)) // hopefully there should be at most one spec per impl_elt, otherwise Karamel monomorphization will introduce conflicts. Anyway, src_elt MUST NOT be extracted (it contains list types, etc.)
: Type0 = {
  cddl_map_iterator_contents: cbor_map_iterator_t;
  pm: perm;
  t1: Ghost.erased typ;
  sp1: Ghost.erased (spec t1 (dfst spec1) true); // I need to know that the parser is injective, to maintain the invariant on maps in rel_map_iterator
  eq1: Ghost.erased (EqTest.eq_test (dfst spec1));
  cddl_map_iterator_impl_validate1: impl_typ vmatch t1;
  cddl_map_iterator_impl_parse1: impl_zero_copy_parse vmatch sp1.parser (dsnd spec1);
  tex: Ghost.erased typ;
  cddl_map_iterator_impl_validate_ex: impl_typ vmatch tex;
  t2: Ghost.erased typ;
  sp2: Ghost.erased (spec t2 (dfst spec2) true); // same here
  cddl_map_iterator_impl_validate2: impl_typ vmatch t2;
  cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch sp2.parser (dsnd spec2);
}

inline_for_extraction
let cddl_map_iterator_impl_validate1
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1)) (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
: Tot (impl_typ vmatch i.t1)
= i.cddl_map_iterator_impl_validate1

inline_for_extraction
let cddl_map_iterator_impl_parse1
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1)) (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
: Tot (impl_zero_copy_parse vmatch i.sp1.parser (dsnd spec1))
= i.cddl_map_iterator_impl_parse1

inline_for_extraction
let cddl_map_iterator_impl_validate_ex
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1)) (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
: Tot (impl_typ vmatch i.tex)
= i.cddl_map_iterator_impl_validate_ex

inline_for_extraction
let cddl_map_iterator_impl_validate2
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1)) (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
: Tot (impl_typ vmatch i.t2)
= i.cddl_map_iterator_impl_validate2

inline_for_extraction
let cddl_map_iterator_impl_parse2
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1)) (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
: Tot (impl_zero_copy_parse vmatch i.sp2.parser (dsnd spec2))
= i.cddl_map_iterator_impl_parse2

inline_for_extraction
let mk_map_iterator
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
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
  (#tex: Ghost.erased typ)
  (cddl_map_iterator_impl_validate_ex: impl_typ vmatch tex)
  (#src_elt2: Type0)
  (#r2: rel impl_elt2 src_elt2)
  (#t2: Ghost.erased typ)
  (sp2: Ghost.erased (spec t2 src_elt2 true))
  (cddl_map_iterator_impl_validate2: impl_typ vmatch t2)
  (cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch sp2.parser r2)
: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 (Iterator.mk_spec r1) (Iterator.mk_spec r2)
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
  sp2 = sp2;
  cddl_map_iterator_impl_validate2 = cddl_map_iterator_impl_validate2;
  cddl_map_iterator_impl_parse2 = cddl_map_iterator_impl_parse2;
}

let mk_map_iterator_eq
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
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
  (#tex: Ghost.erased typ)
  (cddl_map_iterator_impl_validate_ex: impl_typ vmatch tex)
  (#src_elt2: Type0)
  (#r2: rel impl_elt2 src_elt2)
  (#t2: Ghost.erased typ)
  (sp2: Ghost.erased (spec t2 src_elt2 true))
  (cddl_map_iterator_impl_validate2: impl_typ vmatch t2)
  (cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch sp2.parser r2)
: Lemma
  (ensures (
    let res = mk_map_iterator cddl_map_iterator_contents pm sp1 eq1 cddl_map_iterator_impl_validate1 cddl_map_iterator_impl_parse1 cddl_map_iterator_impl_validate_ex sp2 cddl_map_iterator_impl_validate2 cddl_map_iterator_impl_parse2 in
    res.cddl_map_iterator_contents == cddl_map_iterator_contents /\
    res.pm == pm /\
    res.t1 == t1 /\
    res.sp1 == sp1 /\
    res.tex == tex /\
    res.t2 == t2 /\
    res.sp2 == sp2 /\
    True
  ))
  [SMTPat (mk_map_iterator cddl_map_iterator_contents pm sp1 eq1 cddl_map_iterator_impl_validate1 cddl_map_iterator_impl_parse1 cddl_map_iterator_impl_validate_ex sp2 cddl_map_iterator_impl_validate2 cddl_map_iterator_impl_parse2)]
= ()

module Map = CDDL.Spec.Map

let rec parse_table_entries
  (#src_elt1: Type0)
  (#t1: typ)
  (#ser1: (src_elt1 -> bool))
  (ps1: (parser_spec t1 src_elt1 ser1))
  (tex: typ)
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
    if t1 k && not (tex k) && t2 v
    then (ps1 k, ps2 v) :: rq
    else rq

let rel_map_iterator_cond
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1))
  (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
  (s: Map.t (dfst spec1) (list (dfst spec2)))
  (l: list (cbor & cbor))
: Tot prop
= let l' = parse_table_entries i.sp1.parser i.tex i.sp2.parser l in
  s == map_of_list_pair i.eq1 l'
  /\ map_of_list_singletons s

let rel_map_iterator
  (#ty: Type0) (vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (impl_elt1: Type0) (impl_elt2: Type0)
  (spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1))
  (spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
: rel (map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2)))
= mk_rel (fun i s -> exists* (l: list (cbor & cbor)) . cbor_map_iterator_match i.pm i.cddl_map_iterator_contents l **
    pure (rel_map_iterator_cond i s l)
  )

```pulse
ghost
fn rel_map_iterator_prop
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1))
  (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
  (s: Map.t (dfst spec1) (list (dfst spec2)))
requires
  rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i s
ensures
  rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i s **
  pure (
    map_of_list_singletons s
  )
{
  unfold (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i s);
  fold (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i s)
}
```

inline_for_extraction
let cddl_map_iterator_is_empty_t
  (#ty: Type0) (vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (impl_elt1: Type0) (impl_elt2: Type0)
=
  (spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1)) ->
  (spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2)) -> // taking `spec` as argument to the operator, rather than the type, guarantees that Karamel will produce it only (at most) once per `impl_elt` type.
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2) ->
  (#l: Ghost.erased (Map.t (dfst spec1) (list (dfst spec2)))) ->
  stt bool
    (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l)
    (fun res ->
      rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l **
      pure (res == true <==> Ghost.reveal l == Map.empty (dfst spec1) (list (dfst spec2)))
    )

#restart-solver

let rec rel_map_iterator_cond_is_empty
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1))
  (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
  (s: Map.t (dfst spec1) (list (dfst spec2)))
  (l: list (cbor & cbor))
: Lemma
  (requires (
    let l' = parse_table_entries i.sp1.parser i.tex i.sp2.parser l in
    s == map_of_list_pair i.eq1 l'
  ))
  (ensures (
    s `Map.equal` Map.empty (dfst spec1) (list (dfst spec2)) <==> Nil? (parse_table_entries i.sp1.parser i.tex i.sp2.parser l)
  ))
  (decreases l)
= match l with
  | [] ->
    assert_norm (parse_table_entries i.sp1.parser i.tex i.sp2.parser [] == []);
    assert_norm (map_of_list_pair i.eq1 [] == Map.empty (dfst spec1) (list (dfst spec2)))
  | (k, v) :: q ->
    rel_map_iterator_cond_is_empty i (map_of_list_pair i.eq1 (parse_table_entries i.sp1.parser i.tex i.sp2.parser q)) q;
    let rq = parse_table_entries i.sp1.parser i.tex i.sp2.parser q in
    assert_norm (parse_table_entries i.sp1.parser i.tex i.sp2.parser ((k, v) :: q) == (
      if Ghost.reveal i.t1 k && not (Ghost.reveal i.tex k) && Ghost.reveal i.t2 v
      then (i.sp1.parser k, i.sp2.parser v) :: rq
      else rq
    ));
    if Ghost.reveal i.t1 k && not (Ghost.reveal i.tex k) && Ghost.reveal i.t2 v
    then begin
      map_of_list_pair_cons i.eq1 (i.sp1.parser k) (i.sp2.parser v) rq;
      ()
    end
    else ()

inline_for_extraction
```pulse
fn cddl_map_iterator_is_empty
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_is_empty_t #ty vmatch #cbor_map_iterator_t cbor_map_iterator_match impl_elt1 impl_elt2
=
  (spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1))
  (spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
  (#l: Ghost.erased (Map.t (dfst spec1) (list (dfst spec2))))
{
  unfold (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l);
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
      b == (res && Cons? lj) /\
      Nil? (parse_table_entries i.sp1.parser i.tex i.sp2.parser li) == (res && Nil? (parse_table_entries i.sp1.parser i.tex i.sp2.parser lj))
    )
  ) {
    let elt = map_next pj;
    Trade.trans _ _ (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li);
    let elt_key = map_entry_key elt;
    let test_key = cddl_map_iterator_impl_validate1 i elt_key;
    if not test_key {
      Trade.elim _ (vmatch2 _ elt _);
      Trade.elim_hyp_l _ _ _;
    } else {
      let test_ex = cddl_map_iterator_impl_validate_ex i elt_key;
      Trade.elim _ (vmatch2 _ elt _);
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
  fold (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l);
  rel_map_iterator_cond_is_empty i l li;
  !pres
}
```

inline_for_extraction
let cddl_map_iterator_next_t
  (#ty: Type0) (vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (impl_elt1: Type0) (impl_elt2: Type0)
=
  (spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1)) ->
  (spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2)) -> // taking `spec` as argument to the operator, rather than the type, guarantees that Karamel will produce it only (at most) once per `impl_elt` type.
  (pi: R.ref (map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)) ->
  (#i: Ghost.erased (map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)) ->
  (#l: Ghost.erased (Map.t (dfst spec1) (list (dfst spec2)))) ->
  stt (impl_elt1 & impl_elt2)
    (pts_to pi i **
      rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l **
      pure (~ (Ghost.reveal l == Map.empty (dfst spec1) (list (dfst spec2))))
    )
    (fun res -> exists* i' kv' l' .
      pts_to pi i' **
      rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i' l' **
      rel_pair (dsnd spec1) (dsnd spec2) res kv' **
      Trade.trade
        (rel_pair (dsnd spec1) (dsnd spec2) res kv' ** rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i' l')
        (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l) **
      pure (
        Ghost.reveal l == map_of_list_cons i.eq1 (fst kv') (snd kv') l'
      )
    )

```pulse
ghost
fn rel_map_iterator_fold
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) 
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (map_share: map_iterator_share_t cbor_map_iterator_match)
  (map_gather: map_iterator_gather_t cbor_map_iterator_match)
  (#impl_elt1: Type0) (#impl_elt2: Type0)
  (#spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1))
  (#spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (i: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2)
  (pm: perm)
  (contents: cbor_map_iterator_t)
  (li: list (cbor & cbor))
requires
  cbor_map_iterator_match pm contents li ** pure (
    i.pm == pm /. 2.0R /\
    i.cddl_map_iterator_contents == contents
    /\ List.Tot.no_repeats_p (List.Tot.map fst (parse_table_entries i.sp1.parser i.tex i.sp2.parser li))
  )
ensures exists* l .
  rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l **
  Trade.trade
    (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l)
    (cbor_map_iterator_match pm contents li) **
  pure (
    rel_map_iterator_cond i l li
  )
{
  let l' = parse_table_entries i.sp1.parser i.tex i.sp2.parser li;
  let l = map_of_list_pair i.eq1 l';
  map_of_list_pair_no_repeats_key i.eq1 l';
  map_share contents;
  rewrite (cbor_map_iterator_match (pm /. 2.0R) contents li)
    as (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li);
  fold (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l);
  ghost fn aux (_: unit)
  requires cbor_map_iterator_match (pm /. 2.0R) contents li ** rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l
  ensures cbor_map_iterator_match pm contents li
  {
    unfold (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 i l);
    with li' . assert (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li');
    rewrite (cbor_map_iterator_match i.pm i.cddl_map_iterator_contents li')
      as (cbor_map_iterator_match (pm /. 2.0R) contents li');
    map_gather contents #(pm /. 2.0R) #li;
    rewrite (cbor_map_iterator_match (pm /. 2.0R +. pm /. 2.0R) contents li)
      as (cbor_map_iterator_match pm contents li)
  };
  Trade.intro _ _ _ aux
}
```

inline_for_extraction
```pulse
fn cddl_map_iterator_next
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_share: map_iterator_share_t cbor_map_iterator_match)
  (map_gather: map_iterator_gather_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_next_t #ty vmatch #cbor_map_iterator_t cbor_map_iterator_match impl_elt1 impl_elt2
=
  (spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1))
  (spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
  (pi: _)
  (#gi: _)
  (#l: _)
{
  unfold (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l);
  with li . assert (cbor_map_iterator_match gi.pm gi.cddl_map_iterator_contents li);
  map_of_list_pair_no_repeats_key gi.eq1 (parse_table_entries gi.sp1.parser gi.tex gi.sp2.parser li);
  let i = !pi;
  rewrite (cbor_map_iterator_match gi.pm gi.cddl_map_iterator_contents li)
    as (cbor_map_iterator_match gi.pm i.cddl_map_iterator_contents li);
  ghost fn aux (_: unit)
  requires emp ** cbor_map_iterator_match gi.pm i.cddl_map_iterator_contents li
  ensures rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l
  {
    rewrite (cbor_map_iterator_match gi.pm i.cddl_map_iterator_contents li)
      as (cbor_map_iterator_match gi.pm gi.cddl_map_iterator_contents li);
    fold (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l)
  };
  Trade.intro _ _ _ aux;
  let mut pj = i.cddl_map_iterator_contents;
  let hd0 = map_next pj;
  Trade.trans _ _ (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l);
  let mut phd = hd0;
  while (
    with ghd pmhd vhd . assert (pts_to phd ghd ** vmatch2 pmhd ghd vhd);
    let hd = !phd;
    Trade.rewrite_with_trade (vmatch2 pmhd ghd vhd) (vmatch2 pmhd hd vhd);
    let hd_key = map_entry_key hd;
    let test_key = cddl_map_iterator_impl_validate1 i hd_key;
    if not test_key {
      Trade.elim _ (vmatch2 pmhd hd vhd);
      Trade.elim (vmatch2 pmhd hd vhd) _;
      true
    } else {
      let test_ex = cddl_map_iterator_impl_validate_ex i hd_key;
      Trade.elim _ (vmatch2 pmhd hd vhd);
      if test_ex {
        Trade.elim (vmatch2 pmhd hd vhd) _;
        true
      } else {
        let hd_value = map_entry_value hd;
        let test_value = cddl_map_iterator_impl_validate2 i hd_value;
        Trade.elim _ (vmatch2 pmhd hd vhd);
        Trade.elim (vmatch2 pmhd hd vhd) _;
        not test_value
      }
    }
  ) invariant b . exists* hd pmhd vhd j lj .
    pts_to phd hd **
    vmatch2 pmhd hd vhd **
    pts_to pj j **
    cbor_map_iterator_match gi.pm j lj **
    Trade.trade
      (vmatch2 pmhd hd vhd ** cbor_map_iterator_match gi.pm j lj)
      (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l) **
    pure (
      b == not (Ghost.reveal i.t1 (fst vhd) && not (Ghost.reveal i.tex (fst vhd)) && Ghost.reveal i.t2 (snd vhd)) /\
      parse_table_entries i.sp1.parser i.tex i.sp2.parser li == parse_table_entries i.sp1.parser i.tex i.sp2.parser (vhd :: lj)
    )
  {
    Trade.elim_hyp_l _ _ _;
    let hd = map_next pj;
    Trade.trans _ _ (rel_map_iterator vmatch cbor_map_iterator_match impl_elt1 impl_elt2 spec1 spec2 gi l);
    phd := hd
  };
  with pmhd ghd vhd . assert (pts_to phd ghd ** vmatch2 pmhd ghd vhd);
  let hd = !phd;
  Trade.rewrite_with_trade
    (vmatch2 pmhd ghd vhd)
    (vmatch2 pmhd hd vhd);
  Trade.trans_hyp_l _ _ _ _;
  map_entry_share hd;
  ghost fn aux_hd (_: unit)
  requires emp ** (vmatch2 (pmhd /. 2.0R) hd vhd ** vmatch2 (pmhd /. 2.0R) hd vhd)
  ensures vmatch2 pmhd hd vhd
  {
    map_entry_gather hd;
    rewrite (vmatch2 (pmhd /. 2.0R +. pmhd /. 2.0R) hd vhd)
      as (vmatch2 pmhd hd vhd)
  };
  Trade.intro _ _ _ aux_hd;
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
  let res = (hd_key_res, hd_value_res);
  Trade.rewrite_with_trade
    (dsnd spec1 hd_key_res vhd_key_res ** dsnd spec2 hd_value_res vhd_value_res)
    (rel_pair (dsnd spec1) (dsnd spec2) res (vhd_key_res, vhd_value_res));
  Trade.trans _ _ (vmatch2 pmhd hd vhd);
  Trade.trans_hyp_l _ _ _ _;
  with gj lj . assert (cbor_map_iterator_match gi.pm gj lj);
  map_of_list_pair_no_repeats_key i.eq1 (parse_table_entries i.sp1.parser i.tex i.sp2.parser lj);
  let j = !pj;
  let i' : map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2 = { i with
    cddl_map_iterator_contents = j;
    pm = gi.pm /. 2.0R;
  };
  rel_map_iterator_fold map_share map_gather i' gi.pm _ _;
  Trade.trans_hyp_r _ _ _ _;
  pi := i';
  res
}
```


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
  ser1: Ghost.erased (dfst spec1 -> bool);
  ps1: Ghost.erased (parser_spec t1 (dfst spec1) ser1);
  eq1: Ghost.erased (EqTest.eq_test (dfst spec1));
  cddl_map_iterator_impl_validate1: impl_typ vmatch t1;
  cddl_map_iterator_impl_parse1: impl_zero_copy_parse vmatch ps1 (dsnd spec1);
  tex: Ghost.erased typ;
  cddl_map_iterator_impl_validate_ex: impl_typ vmatch tex;
  t2: Ghost.erased typ;
  ser2: Ghost.erased (dfst spec2 -> bool);
  ps2: Ghost.erased (parser_spec t2 (dfst spec2) ser2);
  cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch ps2 (dsnd spec2);
}

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
  (#ser1: Ghost.erased (src_elt1 -> bool))
  (#ps1: Ghost.erased (parser_spec t1 src_elt1 ser1))
  (eq1: Ghost.erased (EqTest.eq_test src_elt1))
  (cddl_map_iterator_impl_validate1: impl_typ vmatch t1)
  (cddl_map_iterator_impl_parse1: impl_zero_copy_parse vmatch ps1 r1)
  (#tex: Ghost.erased typ)
  (cddl_map_iterator_impl_validate_ex: impl_typ vmatch tex)
  (#src_elt2: Type0)
  (#r2: rel impl_elt2 src_elt2)
  (#t2: Ghost.erased typ)
  (#ser2: Ghost.erased (src_elt2 -> bool))
  (#ps2: Ghost.erased (parser_spec t2 src_elt2 ser2))
  (cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch ps2 r2)
: map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 (Iterator.mk_spec r1) (Iterator.mk_spec r2)
= {
  cddl_map_iterator_contents = cddl_map_iterator_contents;
  pm = pm;
  t1 = t1;
  ser1 = ser1;
  ps1 = ps1;
  eq1 = eq1;
  cddl_map_iterator_impl_validate1 = cddl_map_iterator_impl_validate1;
  cddl_map_iterator_impl_parse1 = cddl_map_iterator_impl_parse1;
  tex = tex;
  cddl_map_iterator_impl_validate_ex = cddl_map_iterator_impl_validate_ex;
  t2 = t2;
  ser2 = ser2;
  ps2 = ps2;
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
  (#ser1: Ghost.erased (src_elt1 -> bool))
  (#ps1: Ghost.erased (parser_spec t1 src_elt1 ser1))
  (eq1: Ghost.erased (EqTest.eq_test src_elt1))
  (cddl_map_iterator_impl_validate1: impl_typ vmatch t1)
  (cddl_map_iterator_impl_parse1: impl_zero_copy_parse vmatch ps1 r1)
  (#tex: Ghost.erased typ)
  (cddl_map_iterator_impl_validate_ex: impl_typ vmatch tex)
  (#src_elt2: Type0)
  (#r2: rel impl_elt2 src_elt2)
  (#t2: Ghost.erased typ)
  (#ser2: Ghost.erased (src_elt2 -> bool))
  (#ps2: Ghost.erased (parser_spec t2 src_elt2 ser2))
  (cddl_map_iterator_impl_parse2: impl_zero_copy_parse vmatch ps2 r2)
: Lemma
  (ensures (
    let res = mk_map_iterator cddl_map_iterator_contents pm eq1 cddl_map_iterator_impl_validate1 cddl_map_iterator_impl_parse1 cddl_map_iterator_impl_validate_ex cddl_map_iterator_impl_parse2 in
    res.cddl_map_iterator_contents == cddl_map_iterator_contents /\
    res.pm == pm /\
    res.t1 == t1 /\
    res.ser1 == ser1 /\
    res.ps1 == ps1 /\
    res.tex == tex /\
    res.t2 == t2 /\
    res.ser2 == ser2 /\
    res.ps2 == ps2 /\
    True
  ))
  [SMTPat (mk_map_iterator cddl_map_iterator_contents pm eq1 cddl_map_iterator_impl_validate1 cddl_map_iterator_impl_parse1 cddl_map_iterator_impl_validate_ex cddl_map_iterator_impl_parse2)]
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
= let l' = parse_table_entries i.ps1 i.tex i.ps2 l in
  s == map_of_list_pair i.eq1 l'

let rel_map_iterator
  (#ty: Type0) (vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (impl_elt1: Type0) (impl_elt2: Type0)
  (spec1: Ghost.erased (src_elt1: Type0 & rel impl_elt1 src_elt1))
  (spec2: Ghost.erased (src_elt2: Type0 & rel impl_elt2 src_elt2))
: rel (map_iterator_t vmatch cbor_map_iterator_t impl_elt1 impl_elt2 spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2)))
= mk_rel (fun i s -> exists* (l: list (cbor & cbor)) . cbor_map_iterator_match i.pm i.cddl_map_iterator_contents l **
    pure (rel_map_iterator_cond i s l)
  )

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


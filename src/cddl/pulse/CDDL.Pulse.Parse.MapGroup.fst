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

let rel_either_eq_left
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w1: low1)
  (z1: high1)
: Lemma
  (rel_either r1 r2 (Inl w1) (Inl z1) == r1 w1 z1)
= ()

let rel_either_eq_right
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w2: low2)
  (z2: high2)
: Lemma
  (rel_either r1 r2 (Inr w2) (Inr z2) == r2 w2 z2)
= ()

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

let rel_option_eq_some
  (#low #high: Type)
  (r: rel low high)
  (w: low)
  (z: high)
: Lemma
  (rel_option r (Some w) (Some z) == r w z)
= ()

let rel_option_eq_none
  (#low #high: Type)
  (r: rel low high)
: Lemma
  (rel_option r None None == emp)
= ()

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

let rel_pair_eq
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w1: low1)
  (w2: low2)
  (z1: high1)
  (z2: high2)
: Lemma
  (rel_pair r1 r2 (w1, w2) (z1, z2) == r1 w1 z1 ** r2 w2 z2)
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

#pop-options


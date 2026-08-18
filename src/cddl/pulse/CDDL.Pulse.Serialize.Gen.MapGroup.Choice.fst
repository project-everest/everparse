module CDDL.Pulse.Serialize.Gen.MapGroup.Choice
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
#lang-pulse

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

(* impl_serialize_map_group_nop *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_nop
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (_: unit)
: impl_serialize_map_group p minl maxl mg_spec_nop rel_unit
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  assert pure (cbor_map_union l (mg_spec_nop.mg_serializer v) == l);
  with w . assert (pts_to out w);
  with count . assert (pts_to out_count count);
  with size . assert (pts_to out_size size);
  assert pure (impl_serialize_map_group_pre p count size l w);
  assert pure (cbor_map_min_length_prop' p minl (U64.v count) w);
  assert pure (Some? (Ghost.reveal p (U64.v count) w));
  assert pure (~ (impl_serialize_map_group_invalid minl l mg_spec_nop v (Seq.length w)));
  true
}

(* impl_serialize_map_group_choice *)

#push-options "--z3rlimit 256"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_choice
  (#p: Ghost.erased bare_cbor_map_parser)
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group p minl maxl ps1 r1)
    (#[@@@erasable]t2: Ghost.erased det_map_group)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] fp2: Ghost.erased map_constraint)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (mg_spec t2 fp2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_map_group p minl maxl ps2 r2)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      map_group_choice_compatible t1 t2
    ))
: impl_serialize_map_group p minl maxl #_ #_ #_ #_ (mg_spec_choice ps1 ps2) #_ (rel_either r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  rel_either_cases r1 r2 c v;
  match c {
    norewrite
    Inl c1 -> {
      Trade.rewrite_with_trade (rel_either r1 r2 c v) (r1 c1 (Inl?.v v));
      let res = i1 c1 out out_count out_size l;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade (rel_either r1 r2 c v) (r2 c2 (Inr?.v v));
      let res = i2 c2 out out_count out_size l;
      Trade.elim _ _;
      res
    }
  }
}

(* impl_serialize_map_group_zero_or_one *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_zero_or_one
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group p minl maxl ps1 r1)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      MapGroupFail? (apply_map_group_det t1 cbor_map_empty)
    ))
: impl_serialize_map_group p minl maxl #_ #_ #_ #_ (mg_spec_zero_or_one ps1) #_ (rel_option r1)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  rel_option_cases r1 c v;
  match c {
    norewrite
    Some c1 -> {
      Trade.rewrite_with_trade (rel_option r1 c v) (r1 c1 (Some?.v v));
      let res = i1 c1 out out_count out_size l;
      Trade.elim _ _;
      res
    }
    norewrite
    None -> {
      true
    }
  }
}

#pop-options

(* impl_serialize_map_group_either_left *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_either_left
  (#p: Ghost.erased bare_cbor_map_parser)
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group p minl maxl ps1 r1)
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt1)
    (i2: impl_serialize_map_group p minl maxl ps1 r2)
: impl_serialize_map_group p minl maxl #_ #_ #_ #_ ps1 #_ (rel_either_left r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  match c {
    norewrite
    Inl c1 -> {
      Trade.rewrite_with_trade
        (rel_either_left r1 r2 c v)
        (r1 c1 v);
      let res = i1 c1 out out_count out_size l;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade
        (rel_either_left r1 r2 c v)
        (r2 c2 v);
      let res = i2 c2 out out_count out_size l;
      Trade.elim _ _;
      res
    }
  }
}

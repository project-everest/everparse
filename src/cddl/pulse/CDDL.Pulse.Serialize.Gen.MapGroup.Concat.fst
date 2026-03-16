module CDDL.Pulse.Serialize.Gen.MapGroup.Concat
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
#lang-pulse

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

(* impl_serialize_map_group_concat - helper lemmas *)

let cbor_map_disjoint_union_left (m1 m2 m3: cbor_map) : Lemma
  (requires cbor_map_disjoint m1 m3 /\ cbor_map_disjoint m2 m3)
  (ensures cbor_map_disjoint (cbor_map_union m1 m2) m3)
= ()

let cbor_map_disjoint_union_right (m1 m2 m3: cbor_map) : Lemma
  (requires cbor_map_disjoint m1 m2 /\ cbor_map_disjoint m1 m3)
  (ensures cbor_map_disjoint m1 (cbor_map_union m2 m3))
= ()

#push-options "--z3rlimit 32"

let mg_spec_concat_serializer_eq
  (#source1: det_map_group)
  (#source_fp1: map_constraint)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1)
  (#source2: det_map_group)
  (#source_fp2: map_constraint)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    map_constraint_disjoint source_fp1 source_fp2
  })
  (v: (target1 & target2))
: Lemma
  (ensures (
    let mg = mg_spec_concat p1 p2 in
    mg.mg_serializable v ==> (
    p1.mg_serializable (fst v) /\
    p2.mg_serializable (snd v) /\ (
    let m1 = p1.mg_serializer (fst v) in
    let m2 = p2.mg_serializer (snd v) in
    cbor_map_disjoint m1 m2 /\
    mg.mg_serializer v == cbor_map_union m1 m2
  ))))
= ()

#pop-options


#push-options "--z3rlimit 128 --split_queries always"

let impl_serialize_map_group_concat_false_helper
  (p: bare_cbor_map_parser)
  (minl: cbor -> nat) (maxl: cbor -> option nat)
  (#t1: det_map_group) (#fp1: map_constraint) (#tgt1: Type) (#inj1: bool)
  (ps1: mg_spec t1 fp1 tgt1 inj1)
  (#t2: det_map_group) (#fp2: map_constraint) (#tgt2: Type) (#inj2: bool)
  (ps2: mg_spec t2 fp2 tgt2 inj2)
  (sq: squash (
    map_group_footprint t1 fp1 /\
    map_group_footprint t2 fp2 /\
    map_constraint_disjoint fp1 fp2
  ))
  (l: cbor_map) (v: tgt1 & tgt2)
  (count: U64.t) (size: SZ.t) (w: Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_map_group_post p minl maxl count size l ps1 (fst v) w false
  ))
  (ensures (
    impl_serialize_map_group_post p minl maxl count size l (mg_spec_concat ps1 ps2) v w false
  ))
= mg_spec_concat_serializer_eq ps1 ps2 v;
  let ps = mg_spec_concat ps1 ps2 in
  if ps.mg_serializable v then begin
    let m1 = ps1.mg_serializer (fst v) in
    let m2 = ps2.mg_serializer (snd v) in
    Classical.move_requires (cbor_map_disjoint_union_left l m1) m2;
    Classical.move_requires (cbor_map_disjoint_union_right l m1) m2;
    Classical.move_requires (cbor_map_max_length_union maxl l) m1;
    Classical.move_requires (cbor_map_min_length_union minl l) m1;
    Classical.move_requires (cbor_map_length_disjoint_union l) m1;
    Classical.move_requires (cbor_map_max_length_union maxl (cbor_map_union l m1)) m2;
    Classical.move_requires (cbor_map_min_length_union minl (cbor_map_union l m1)) m2;
    Classical.move_requires (cbor_map_length_disjoint_union (cbor_map_union l m1)) m2
  end

let impl_serialize_map_group_concat_true_helper
  (p: bare_cbor_map_parser)
  (minl: cbor -> nat) (maxl: cbor -> option nat)
  (#t1: det_map_group) (#fp1: map_constraint) (#tgt1: Type) (#inj1: bool)
  (ps1: mg_spec t1 fp1 tgt1 inj1)
  (#t2: det_map_group) (#fp2: map_constraint) (#tgt2: Type) (#inj2: bool)
  (ps2: mg_spec t2 fp2 tgt2 inj2)
  (sq: squash (
    map_group_footprint t1 fp1 /\
    map_group_footprint t2 fp2 /\
    map_constraint_disjoint fp1 fp2
  ))
  (l: cbor_map) (v: tgt1 & tgt2)
  (count2: U64.t) (size2: SZ.t) (w2: Seq.seq U8.t)
  (res2: bool)
  (h_i1_not_invalid: squash (
    ~ (impl_serialize_map_group_invalid minl l ps1 (fst v) (Seq.length w2))
  ))
: Lemma
  (requires (
    impl_serialize_map_group_post p minl maxl count2 size2
      (cbor_map_union l (ps1.mg_serializer (fst v))) ps2 (snd v) w2 res2
  ))
  (ensures (
    impl_serialize_map_group_post p minl maxl count2 size2 l (mg_spec_concat ps1 ps2) v w2 res2
  ))
= mg_spec_concat_serializer_eq ps1 ps2 v;
  let ps = mg_spec_concat ps1 ps2 in
  if ps.mg_serializable v then begin
    let m1 = ps1.mg_serializer (fst v) in
    let m2 = ps2.mg_serializer (snd v) in
    Classical.move_requires (cbor_map_disjoint_union_left l m1) m2;
    Classical.move_requires (cbor_map_disjoint_union_right l m1) m2;
    Classical.move_requires (cbor_map_max_length_union maxl l) m1;
    Classical.move_requires (cbor_map_min_length_union minl l) m1;
    Classical.move_requires (cbor_map_length_disjoint_union l) m1;
    Classical.move_requires (cbor_map_max_length_union maxl (cbor_map_union l m1)) m2;
    Classical.move_requires (cbor_map_min_length_union minl (cbor_map_union l m1)) m2;
    Classical.move_requires (cbor_map_length_disjoint_union (cbor_map_union l m1)) m2
  end

#pop-options

#push-options "--z3rlimit 32 --split_queries always"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_concat
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
      map_constraint_disjoint fp1 fp2
    ))
: impl_serialize_map_group p minl maxl #_ #_ #_ #_ (mg_spec_concat ps1 ps2) #_ (rel_pair r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  norewrite let (c1, c2) = c;
  Trade.rewrite_with_trade (rel_pair r1 r2 c v) (r1 c1 (fst v) ** r2 c2 (snd v));
  let res1 = i1 c1 out out_count out_size l;
  S.pts_to_len out;
  mg_spec_concat_serializer_eq ps1 ps2 v;
  if (res1) {
    let res2 = i2 c2 out out_count out_size (cbor_map_union l (ps1.mg_serializer (fst v)));
    with w2 . assert (pts_to out w2);
    with count2 . assert (pts_to out_count count2);
    with size2 . assert (pts_to out_size size2);
    Trade.elim _ _;
    S.pts_to_len out;
    impl_serialize_map_group_concat_true_helper (Ghost.reveal p) minl maxl ps1 ps2 () l v count2 size2 w2 res2 ();
    res2
  } else {
    with w1 . assert (pts_to out w1);
    with count1 . assert (pts_to out_count count1);
    with size1 . assert (pts_to out_size size1);
    Trade.elim _ _;
    impl_serialize_map_group_concat_false_helper (Ghost.reveal p) minl maxl ps1 ps2 () l v count1 size1 w1;
    false
  }
}

#pop-options

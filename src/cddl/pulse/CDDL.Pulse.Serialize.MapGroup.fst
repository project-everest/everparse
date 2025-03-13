module CDDL.Pulse.Serialize.MapGroup
#lang-pulse

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map
   (cbor_det_serialize_map: cbor_det_serialize_map_t)
    (# [@@@erasable] t: Ghost.erased det_map_group)
    (# [@@@erasable] fp: Ghost.erased typ)
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_map_group s r)
    (sq: squash (map_group_footprint t fp))
: impl_serialize #_ #_ #_ (spec_map_group s) #_ r
=
  (c: _)
  (#v: _)
  (out: _)
{
  let mut pcount = 0uL;
  let mut psize = 0sz;
  Cbor.cbor_det_serialize_map_empty ();
  let res = i c out pcount psize cbor_map_empty;
  Classical.forall_intro (Classical.move_requires Cbor.cbor_det_serialize_map_length_gt_list);
  if (res) {
    let size = !psize;
    let count = !pcount;
    cbor_det_serialize_map count out (s.mg_serializer v) size
  } else {
    0sz
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_ext
    (#[@@@erasable]t: Ghost.erased (det_map_group))
    (# [@@@erasable] fp: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_map_group ps r)
    (#[@@@erasable]t': Ghost.erased (det_map_group))
    (# [@@@erasable] fp': Ghost.erased typ)
    (#[@@@erasable] inj': Ghost.erased bool)
    ([@@@erasable]ps': Ghost.erased (mg_spec t' fp' tgt inj'))
    ([@@@erasable]sq: squash (
      t' == t /\
      (forall (x: tgt) . (Ghost.reveal ps').mg_serializable x <==> (Ghost.reveal ps).mg_serializable x) /\
      (forall (x: tgt) . (Ghost.reveal ps').mg_serializable x ==> (
        (Ghost.reveal ps).mg_serializable x /\
        (Ghost.reveal ps').mg_serializer x `cbor_map_equal` (Ghost.reveal ps).mg_serializer x
      )) /\
      (forall (x: tgt) . (Ghost.reveal ps').mg_size x == (Ghost.reveal ps).mg_size x)
    ))
: impl_serialize_map_group #(Ghost.reveal t') #(Ghost.reveal fp') #tgt #inj' (Ghost.reveal ps') #impl_tgt r
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  i c out out_count out_size l
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_group_ext'
    (#[@@@erasable]t: Ghost.erased (det_map_group))
    (# [@@@erasable] fp: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_map_group ps r)
    ([@@@erasable] fp': Ghost.erased typ)
    (sq: squash (
      typ_equiv fp fp'
    ))
: impl_serialize_map_group #(Ghost.reveal t) #(Ghost.reveal fp') #tgt #inj (mg_spec_ext ps fp' ps.mg_size ps.mg_serializable) #impl_tgt r
= impl_serialize_map_group_ext i _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_choice
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased typ)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group ps1 r1)
    (#[@@@erasable]t2: Ghost.erased det_map_group)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] fp2: Ghost.erased typ)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (mg_spec t2 fp2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_map_group ps2 r2)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      map_group_choice_compatible t1 t2
    ))
: impl_serialize_map_group #_ #_ #_ #_ (mg_spec_choice ps1 ps2) #_ (rel_either r1 r2)
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

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_zero_or_one
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased typ)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group ps1 r1)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      MapGroupFail? (apply_map_group_det t1 cbor_map_empty)
    ))
: impl_serialize_map_group #_ #_ #_ #_ (mg_spec_zero_or_one ps1) #_ (rel_option r1)
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

let cbor_det_serialize_map_append_length_pat
  (m1 m2: cbor_map)
: Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures (Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union m1 m2)) == Seq.length (Cbor.cbor_det_serialize_map m1) + Seq.length (Cbor.cbor_det_serialize_map m2)))
  [SMTPat (cbor_map_union m1 m2)]
= Cbor.cbor_det_serialize_map_append_length m1 m2

let mg_spec_concat_serializer_eq
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#inj1: bool)
  (p1: mg_spec source1 source_fp1 target1 inj1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#inj2: bool)
  (p2: mg_spec source2 source_fp2 target2 inj2 {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2
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

let cbor_map_union_assoc_pat (m1 m2 m3: cbor_map) : Lemma
  (ensures (cbor_map_union (cbor_map_union m1 m2) m3 == cbor_map_union m1 (cbor_map_union m2 m3)))
  [SMTPatOr [
    [SMTPat (cbor_map_union (cbor_map_union m1 m2) m3)];
    [SMTPat (cbor_map_union m1 (cbor_map_union m2 m3))]
  ]]
= cbor_map_union_assoc m1 m2 m3

let cbor_map_length_disjoint_union_pat (m1 m2: cbor_map) : Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures (
    cbor_map_length (cbor_map_union m1 m2) == cbor_map_length m1 + cbor_map_length m2
  ))
  [SMTPat (cbor_map_union m1 m2)]
= cbor_map_length_disjoint_union m1 m2

#push-options "--z3rlimit 16"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_concat
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased typ)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group ps1 r1)
    (#[@@@erasable]t2: Ghost.erased det_map_group)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] fp2: Ghost.erased typ)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (mg_spec t2 fp2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_map_group ps2 r2)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      typ_disjoint fp1 fp2
    ))
: impl_serialize_map_group #_ #_ #_ #_ (mg_spec_concat ps1 ps2) #_ (rel_pair r1 r2)
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
    Trade.elim _ _;
    S.pts_to_len out;
    res2
  } else {
    Trade.elim _ _;
    false
  }
}

#pop-options

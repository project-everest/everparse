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

inline_for_extraction noextract [@@noextract_to "krml";
  FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
]
let pow2_64_m1 : U64.t = U64.uint_to_t (pow2 64 - 1)

let pow2_64_m1_eq : squash (U64.v pow2_64_m1 == pow2 64 - 1) = _ by (
  FStar.Tactics.norm [delta; zeta; iota; primops];
  FStar.Tactics.trefl ()
)

let mg_spec_match_item_for_serializer_eq
  (cut: bool)
  (k: cbor)
  (#ty: typ)
  (#target: Type)
  (#inj: bool)
  (p: spec ty target inj)
  (v: target)
: Lemma
  (ensures (p.serializable v ==> (
    let p' = mg_spec_match_item_for cut k p in
    p'.mg_serializable v /\
    p'.mg_serializer v == cbor_map_singleton k (p.serializer v)
  )))
= ()

let cbor_det_serialize_map_singleton_pat
  (key: cbor)
  (value: cbor)
: Lemma
  (ensures (Cbor.cbor_det_serialize_map (cbor_map_singleton key value) == Cbor.cbor_det_serialize key `Seq.append` Cbor.cbor_det_serialize value))
  [SMTPat (cbor_map_singleton key value)]
= Cbor.cbor_det_serialize_map_singleton key value

let seq_slice_append_pat
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
  [SMTPat (Seq.append s1 s2)]
= ()

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
fn impl_serialize_match_item_for
  (insert: cbor_det_serialize_map_insert_t)
  (#[@@@erasable]key: Ghost.erased cbor)
  (ik: impl_serialize (spec_literal key) rel_unit)
  ([@@@erasable]cut: Ghost.erased bool)
  (#[@@@erasable]value: Ghost.erased typ)
  (#[@@@erasable]tvalue: Type0)
  (#[@@@erasable]vinj: Ghost.erased bool)
  (#[@@@erasable]pvalue: Ghost.erased (spec value tvalue vinj))
  (#iv: Type0)
  (#[@@@erasable]r: rel iv tvalue)
  (ivalue: impl_serialize pvalue r)
: impl_serialize_map_group #_ #_ #_ #_ (mg_spec_match_item_for cut key pvalue) #_ r
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let count = !out_count;
  if (U64.lt count pow2_64_m1) {
    mg_spec_match_item_for_serializer_eq cut key pvalue v;
    with w0 . assert (pts_to out w0);
    let size0 = !out_size;
    Seq.lemma_split w0 (SZ.v size0);
    let (out0, out1) = S.split out size0;
    fold (rel_unit () ());
    let res1 = ik () out1;
    S.pts_to_len out1;
    unfold (rel_unit () ());
    S.join _ _ out;
    S.pts_to_len out;
    if (SZ.gt res1 0sz) {
      let size1 = SZ.add size0 res1;
      let (out01, out2) = S.split out size1;
      let res2 = ivalue c out2;
      S.pts_to_len out2;
      S.join _ _ out;
      S.pts_to_len out;
      if (SZ.gt res2 0sz) {
        let size2 = SZ.add size1 res2;
        let (out012, _) = S.split out size2;
        S.pts_to_len out012;
        let res = insert out012 l size0 key size1 (pvalue.serializer (Ghost.reveal v));
        S.pts_to_len out012;
        S.join _ _ out;
        S.pts_to_len out;
        if (res) {
          out_size := size2;
          out_count := U64.add count 1uL;
          true
        } else {
          false
        }
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}

#pop-options

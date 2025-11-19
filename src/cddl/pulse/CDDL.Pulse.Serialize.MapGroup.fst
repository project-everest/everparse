module CDDL.Pulse.Serialize.MapGroup
#lang-pulse
#push-options "--query_stats"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map
   (cbor_det_serialize_map: cbor_det_serialize_map_t)
    (# [@@@erasable] t: Ghost.erased det_map_group)
    (# [@@@erasable] fp: Ghost.erased map_constraint)
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
    (# [@@@erasable] fp: Ghost.erased map_constraint)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_map_group ps r)
    (#[@@@erasable]t': Ghost.erased (det_map_group))
    (# [@@@erasable] fp': Ghost.erased map_constraint)
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
    (# [@@@erasable] fp: Ghost.erased map_constraint)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_map_group ps r)
    ([@@@erasable] fp': Ghost.erased map_constraint)
    (sq: squash (
      map_constraint_equiv fp fp'
    ))
: impl_serialize_map_group #(Ghost.reveal t) #(Ghost.reveal fp') #tgt #inj (mg_spec_ext ps fp' ps.mg_size ps.mg_serializable) #impl_tgt r
= impl_serialize_map_group_ext i _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_nop
  (_: unit)
: impl_serialize_map_group #_ #_ #_ #_ mg_spec_nop #_ rel_unit
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  true
}

#push-options "--z3rlimit 32"
#restart-solver
#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 2 --query_stats --log_queries"

let compose_choice_l
    ([@@@erasable]t1: Ghost.erased det_map_group)
    ([@@@erasable]tgt1: Type0)
    ([@@@erasable] fp1: Ghost.erased map_constraint)
    ([@@@erasable] inj1: Ghost.erased bool)
    ([@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    ([@@@erasable]t2: Ghost.erased det_map_group)
    ([@@@erasable]tgt2: Type0)
    ([@@@erasable] fp2: Ghost.erased map_constraint)
    ([@@@erasable] inj2: Ghost.erased bool)
    ([@@@erasable]ps2: Ghost.erased (mg_spec t2 fp2 tgt2 inj2))
    (v l:_)
    (count size w res: _)
 : Lemma 
  (requires
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      map_group_choice_compatible t1 t2  /\
    impl_serialize_map_group_post
      count size l #t1 #fp1 #tgt1 #inj1 ps1 v w res)
  (ensures
    impl_serialize_map_group_post
      count size l #(map_group_choice t1 t2) #(map_constraint_choice fp1 fp2) #(either tgt1 tgt2) #(inj1 && inj2) 
        (mg_spec_choice ps1 ps2) (Inl v) w res)
  [SMTPat
      (impl_serialize_map_group_post
        count size l #(map_group_choice t1 t2) #(map_constraint_choice fp1 fp2) #(either tgt1 tgt2) #(inj1 && inj2) 
          (mg_spec_choice ps1 ps2) (Inl v) w res)]
= ()

let compose_choice_r
    ([@@@erasable]t1: Ghost.erased det_map_group)
    ([@@@erasable]tgt1: Type0)
    ([@@@erasable] fp1: Ghost.erased map_constraint)
    ([@@@erasable] inj1: Ghost.erased bool)
    ([@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    ([@@@erasable]t2: Ghost.erased det_map_group)
    ([@@@erasable]tgt2: Type0)
    ([@@@erasable] fp2: Ghost.erased map_constraint)
    ([@@@erasable] inj2: Ghost.erased bool)
    ([@@@erasable]ps2: Ghost.erased (mg_spec t2 fp2 tgt2 inj2))
    (v l:_)
    (count size w res: _)
 : Lemma 
  (requires
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      map_group_choice_compatible t1 t2  /\
    impl_serialize_map_group_post
      count size l #t2 #fp2 #tgt2 #inj2 ps2 v w res)
  (ensures
    impl_serialize_map_group_post
      count size l #(map_group_choice t1 t2) #(map_constraint_choice fp1 fp2) #(either tgt1 tgt2) #(inj1 && inj2) 
        (mg_spec_choice ps1 ps2) (Inr v) w res)
  [SMTPat
      (impl_serialize_map_group_post
        count size l #(map_group_choice t1 t2) #(map_constraint_choice fp1 fp2) #(either tgt1 tgt2) #(inj1 && inj2) 
          (mg_spec_choice ps1 ps2) (Inr   v) w res)]
= ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_choice
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group ps1 r1)
    (#[@@@erasable]t2: Ghost.erased det_map_group)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] fp2: Ghost.erased map_constraint)
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
      // compose_choice t1 tgt1 fp1 inj1 ps1 t2 tgt2 fp2 inj2 ps2 v l ();
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
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
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

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_either_left
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group ps1 r1)
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt1)
    (i2: impl_serialize_map_group ps1 r2)
: impl_serialize_map_group #_ #_ #_ #_ ps1 #_ (rel_either_left r1 r2)
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

let cbor_det_serialize_map_append_length_pat
  (m1 m2: cbor_map)
: Lemma
  (ensures (cbor_map_disjoint m1 m2 ==> Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union m1 m2)) == Seq.length (Cbor.cbor_det_serialize_map m1) + Seq.length (Cbor.cbor_det_serialize_map m2)))
  [SMTPat (cbor_map_union m1 m2)]
= Classical.move_requires (Cbor.cbor_det_serialize_map_append_length m1) m2

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

let cbor_map_union_assoc_pat (m1 m2 m3: cbor_map) : Lemma
  (ensures (cbor_map_union (cbor_map_union m1 m2) m3 == cbor_map_union m1 (cbor_map_union m2 m3)))
  [SMTPatOr [
    [SMTPat (cbor_map_union (cbor_map_union m1 m2) m3)];
    [SMTPat (cbor_map_union m1 (cbor_map_union m2 m3))]
  ]]
= cbor_map_union_assoc m1 m2 m3

let cbor_map_length_disjoint_union_pat (m1 m2: cbor_map) : Lemma
  (ensures (
    cbor_map_disjoint m1 m2 ==>
    cbor_map_length (cbor_map_union m1 m2) == cbor_map_length m1 + cbor_map_length m2
  ))
  [SMTPat (cbor_map_union m1 m2)]
= Classical.move_requires (cbor_map_length_disjoint_union m1) m2

#push-options "--z3rlimit 32"

#restart-solver
#push-options "--z3rlimit_factor 4 --split_queries always --query_stats"
inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_concat
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group ps1 r1)
    (#[@@@erasable]t2: Ghost.erased det_map_group)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] fp2: Ghost.erased map_constraint)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (mg_spec t2 fp2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_map_group ps2 r2)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      map_constraint_disjoint fp1 fp2
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

#push-options "--z3rlimit 64 --z3refresh --fuel 1 --ifuel 1 --split_queries always --query_stats"
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

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator_t
  (#ty #ty2: Type0) (vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch2: perm -> ty2 -> cbor & cbor -> slprop)
  (#cbor_map_iterator_t: Type0) (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
    (#key: typ)
    (#tkey: Type0)
    (sp1: (spec key tkey true))
    (#ikey: Type0)
    (r1: rel ikey tkey)
    (#value: typ)
    (#tvalue: Type0)
    (#inj: bool)
    (sp2: (spec value tvalue inj))
    (#ivalue: Type0)
    (r2: rel ivalue tvalue)
    (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
=
  impl_serialize_map_group #_ #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2))

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
let map_of_list_serializable_disjoint
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2) ==>
    (Map.disjoint m1 m2 <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2))
  ))
= ()

#pop-options

#push-options "--z3rlimit 32"

#restart-solver
let map_of_list_is_append_serializable_intro_serializable
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2 /\ Map.disjoint m1 m2) ==>
      sp.mg_serializable m
  ))
= ()

let cbor_map_mem_disjoint
  (m1 m2: cbor_map)
: Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures (forall kv . cbor_map_mem kv (cbor_map_union m1 m2) <==> (cbor_map_mem kv m1 \/ cbor_map_mem kv m2)))
= ()

let cbor_map_mem_ext
  (m1 m2: cbor_map)
: Lemma
  (requires (forall kv . cbor_map_mem kv m1 <==> cbor_map_mem kv m2))
  (ensures (m1 == m2))
= assert (forall k . match cbor_map_get m1 k with
  | Some v -> cbor_map_mem (k, v) m1
  | _ -> True
  );
  assert (forall k . match cbor_map_get m2 k with
  | Some v -> cbor_map_mem (k, v) m2
  | _ -> True
  );
  assert (cbor_map_equal m1 m2)

#restart-solver
let map_of_list_is_append_serializable_intro
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2 /\ (Map.disjoint m1 m2 \/ cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2))) ==>
    (Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2) /\
      sp.mg_serializable m /\
      sp.mg_serializer m == (sp.mg_serializer m1 `cbor_map_union` sp.mg_serializer m2)
    )
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro_serializable sp1 sp2 except m1 m2 m;
  map_of_list_serializable_disjoint sp1 sp2 except m1 m2;
  if sp.mg_serializable m1 && sp.mg_serializable m2 && cbor_map_disjoint_tot (sp.mg_serializer m1) (sp.mg_serializer m2)
  then begin
    assert (
      forall kv . (map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m kv <==> (map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m1 kv \/ map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m2 kv)
    ));
    cbor_map_mem_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2);
    cbor_map_mem_ext (sp.mg_serializer m) (sp.mg_serializer m1 `cbor_map_union` sp.mg_serializer m2)
  end

#pop-options

let map_of_list_is_append_snoc
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
: Lemma
  (map_of_list_is_append
    m1
    (Map.singleton k (key_eq k) [v])
    (map_of_list_snoc key_eq m1 k v)
  )
= ()

let map_of_list_is_append_cons
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m1: Map.t key (list value))
: Lemma
  (map_of_list_is_append
    (Map.singleton k (key_eq k) [v])
    m1
    (map_of_list_cons key_eq k v m1)
  )
= ()

#push-options "--z3rlimit 128 --split_queries always --fuel 0 --ifuel 1 --query_stats"

#restart-solver
let map_of_list_is_append_serializable_elim
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m /\
    map_of_list_maps_to_nonempty m1 /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m
    ) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  if sp.mg_serializable m
  then begin //defined in terms of Map.for_all; likely needs a lemma call to decompose
    assume (
      sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2
    );
    map_of_list_serializable_disjoint sp1 sp2 except m1 m2
  end

let map_of_list_is_append_serializable_elim'
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
  (sq: squash (map_of_list_is_append m1 m2 m))
  (sq1: squash (map_of_list_maps_to_nonempty m1))
  (sq2: squash (map_of_list_maps_to_nonempty m2))
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m
    ) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))
= map_of_list_is_append_serializable_elim sp1 sp2 except m1 m2 m

#restart-solver
#push-options "--ifuel 2 --fuel 1"
let w_serialize #s #sfp #t #i (sp:mg_spec s sfp t i) (m:_ { sp.mg_serializable m }) = 
  sp.mg_serializer m
#push-options "--z3rlimit 64"
#restart-solver
let map_of_list_is_append_serializable_singleton
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (k: key)
  (k_eq: EqTest.eq_test_for k)
  (v: value)
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m = EqTest.map_singleton k k_eq [v] in
    (sp.mg_serializable m <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v)))
    )) /\
    (sp.mg_serializable m ==> (
    sp.mg_serializer m == cbor_map_singleton (sp1.serializer k) (sp2.serializer v)
  ))))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let m = EqTest.map_singleton k k_eq [v] in
  assert (forall kv . Map.mem kv m <==> (fst kv == k /\ snd kv == [v]));
  assert (sp.mg_serializable m <==> (forall kv . Map.mem kv m ==> map_entry_serializable sp1 sp2 except kv));
  assert (sp.mg_serializable m <==> map_entry_serializable sp1 sp2 except (k, [v]));
  if sp.mg_serializable m
  then begin
    let m1 = w_serialize sp m in
    let m2 = (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)) in
    assert (forall (kv: cbor & cbor). cbor_map_mem kv m1 <==> cbor_map_mem kv m2);
    cbor_map_mem_ext
        (sp.mg_serializer m)
        (cbor_map_singleton (sp1.serializer k) (sp2.serializer v))
  end
  else admit()

#pop-options

let impl_serialize_map_group_valid_map_zero_or_more_snoc_length
  (ll lm1 lkv lm2: nat)
: Lemma
  ((ll + lm1) + (lkv + lm2) == (ll + (lm1 + lkv)) + lm2)
= ()

let impl_serialize_map_group_valid_map_zero_or_more_snoc_length_ge
  (ll lm1 lk lv lm2: nat)
: Lemma
  ((ll + lm1) + ((lk + lv) + lm2) >= ll + lm1 + lk + lv)
= ()

#push-options "--z3rlimit 128 --print_implicits"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_aux
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
      (
        sp1.serializable k /\
        sp2.serializable v /\
        (~ (except (sp1.serializer k, sp2.serializer v))) /\
        (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
      ) ==> (
      sp.mg_serializable (map_of_list_snoc key_eq m1 k v) /\
      cbor_map_disjoint l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) /\
      cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)) /\
      cbor_map_length (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_length (sp.mg_serializer m1) + 1
  ))))
= admit();
  let m2' = map_of_list_cons key_eq k v m2 in
  assert (map_of_list_maps_to_nonempty m2');
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_serializable_elim sp1 sp2 except mkv m2 m2';
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  if
        sp1.serializable k &&
        sp2.serializable v &&
        (not (except (sp1.serializer k, sp2.serializer v))) &&
        (not (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
  then begin
      assert (sp.mg_serializable m1');
      assert (cbor_map_disjoint l (sp.mg_serializer mkv));
      assert (cbor_map_disjoint l (sp.mg_serializer m1'));
      assert (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)));
      assert (cbor_map_length (sp.mg_serializer mkv) == 1);
      assert (cbor_map_length (sp.mg_serializer m1') == cbor_map_length (sp.mg_serializer m1) + 1)
  end

#pop-options

let map_of_list_maps_to_nonempty_singleton
  (#key: Type)
  (#value: Type)
  (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: list value)
  (sq: squash (Cons? v))
: Lemma
  (map_of_list_maps_to_nonempty (Map.singleton k k_eq v))
= ()

let map_of_list_maps_to_nonempty_cons
  (#key: Type)
  (#value: Type)
  (k_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m: Map.t key (list value))
  (sq: squash (map_of_list_maps_to_nonempty m))
: Lemma
  (map_of_list_maps_to_nonempty (map_of_list_cons k_eq k v m))
= ()

#push-options "--z3rlimit 256 --fuel 1 --ifuel 1 --split_queries always"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (sq: squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    sp1.serializable k /\
    sp2.serializable v /\
    (~ (except (sp1.serializer k, sp2.serializer v))) /\
    sp.mg_serializable m2 /\
    (~ (Map.defined k m2)) /\
    (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
  ))
: Tot (squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m1' = map_of_list_snoc key_eq m1 k v in    
    sp.mg_serializable m1' /\
    cbor_map_disjoint (sp.mg_serializer m1') (sp.mg_serializer m2) <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
  ))
= admit();
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  map_of_list_serializable_disjoint sp1 sp2 except m1 m2;
  map_of_list_serializable_disjoint sp1 sp2 except m1' m2;
  ()

#pop-options

#push-options "--z3rlimit 64"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_length1
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (sq: squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m2' = map_of_list_cons key_eq k v m2 in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\
    sp1.serializable k /\
    sp2.serializable v /\
    (~ (except (sp1.serializer k, sp2.serializer v))) /\
    sp.mg_serializable m2 /\
    (~ (Map.defined k m2)) /\
    (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
    sp.mg_serializable m2' /\
    cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')
  ))
: Tot (squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m1' = map_of_list_snoc key_eq m1 k v in    
    let m2' = map_of_list_cons key_eq k v m2 in
    sp.mg_serializable m1' /\
    sp.mg_serializable m2' /\
    cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') == cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) + cbor_map_length (sp.mg_serializer m2)
  ))
= admit();
  impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1 sp1 key_eq sp2 except l m1 k v m2 ();
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  let m2' = map_of_list_cons key_eq k v m2 in
  map_of_list_serializable_disjoint sp1 sp2 except m1' m2;
  map_of_list_serializable_disjoint sp1 sp2 except m1 m2';
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_is_append_cons key_eq k v m2;
  map_of_list_is_append_serializable_intro sp1 sp2 except mkv m2 m2';
  cbor_map_length_disjoint_union l (sp.mg_serializer m1');
  let ll = cbor_map_length l in
  cbor_map_length_disjoint_union (sp.mg_serializer m1) (sp.mg_serializer mkv);
  let lm1 = cbor_map_length (sp.mg_serializer m1) in
  cbor_map_length_disjoint_union l (sp.mg_serializer m1);
  cbor_map_length_disjoint_union (sp.mg_serializer mkv) (sp.mg_serializer m2);
  let lm2 = cbor_map_length (sp.mg_serializer m2) in
  impl_serialize_map_group_valid_map_zero_or_more_snoc_length ll lm1 1 lm2;
  ()

#pop-options

#push-options "--z3rlimit 256 --z3cliopt 'smt.qi.eager_threshold=100' --print_implicits --split_queries always"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc'
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (len: nat)
  (sq: squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2
  ))
: Tot (squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
      impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp (map_of_list_cons key_eq k v m2) len <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v))) /\
      FStar.UInt.fits (cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1) 64 /\
      Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) + Seq.length (Cbor.cbor_det_serialize (sp1.serializer k)) + Seq.length (Cbor.cbor_det_serialize (sp2.serializer v)) <= len /\
      (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
      (sp.mg_serializable (map_of_list_snoc key_eq m1 k v) ==>
        impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v))) sp m2 len
      )
    ))
  ))
= admit();
  impl_serialize_map_group_valid_map_zero_or_more_snoc_aux sp1 key_eq sp2 except l m1 k v m2 len;
  let m2' = map_of_list_cons key_eq k v m2 in
  map_of_list_is_append_cons key_eq k v m2;
  let sq1 : squash (map_of_list_maps_to_nonempty m2) =   assert (map_of_list_maps_to_nonempty m2) in
  let sq2 : squash (map_of_list_maps_to_nonempty m2') = map_of_list_maps_to_nonempty_cons key_eq k v m2 sq1 in
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_serializable_elim' sp1 sp2 except mkv m2 m2' () () sq2;
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  if
    sp1.serializable k &&
    sp2.serializable v &&
    (not (except (sp1.serializer k, sp2.serializer v)))
  then begin
    if sp.mg_serializable m2
    then begin
      map_of_list_serializable_disjoint sp1 sp2 except mkv m2;
      if Map.defined k m2
      then ()
      else begin
        map_of_list_is_append_cons key_eq k v m2;
        map_of_list_is_append_serializable_intro sp1 sp2 except mkv m2 m2';
        if cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))
        then begin
          assert (~ (cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')));
          assert (~ (impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))
        end
        else begin
          assert (cbor_map_disjoint l (sp.mg_serializer m1'));
          assert (cbor_map_disjoint l (sp.mg_serializer m2') <==> cbor_map_disjoint l (sp.mg_serializer m2));
          assert (cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2') <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2));
          map_of_list_is_append_snoc key_eq m1 k v;
          impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1 sp1 key_eq sp2 except l m1 k v m2 ();
          assert (cbor_map_disjoint (sp.mg_serializer m1') (sp.mg_serializer m2) <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2));
          assert (cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2') <==> cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2));
          if cbor_map_disjoint_tot (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')
          then begin
            cbor_map_length_disjoint_union l (sp.mg_serializer m1');
            impl_serialize_map_group_valid_map_zero_or_more_snoc_length1 sp1 key_eq sp2 except l m1 k v m2 ();
            assert (cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') == cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) + cbor_map_length (sp.mg_serializer m2));
            assert (cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') >= cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + 1);
            let sl = Seq.length (Cbor.cbor_det_serialize_map l) in
            let sm1 = Seq.length (Cbor.cbor_det_serialize_map (sp.mg_serializer m1)) in
            let sk = Seq.length (Cbor.cbor_det_serialize (sp1.serializer k)) in
            let sv = Seq.length (Cbor.cbor_det_serialize (sp2.serializer v)) in
            let skv = sk + sv in
            let sm2 = Seq.length (Cbor.cbor_det_serialize_map (sp.mg_serializer m2)) in
            assert (Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) == sl + sm1);
            assert (Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2'))) == (sl + sm1) + (skv + sm2));
            impl_serialize_map_group_valid_map_zero_or_more_snoc_length sl sm1 skv sm2;
            assert (Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2'))) == Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2))));
            impl_serialize_map_group_valid_map_zero_or_more_snoc_length_ge sl sm1 sk sv sm2;
            assert (Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2'))) >= Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) + sk + sv);
            assert (
      impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp (map_of_list_cons key_eq k v m2) len <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v))) /\
      FStar.UInt.fits (cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1) 64 /\
      Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) + Seq.length (Cbor.cbor_det_serialize (sp1.serializer k)) + Seq.length (Cbor.cbor_det_serialize (sp2.serializer v)) <= len /\
      (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
      (sp.mg_serializable (map_of_list_snoc key_eq m1 k v) ==>
        impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v))) sp m2 len
      )
            ));
            ()
          end
          else begin
            assert (~ (impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp m2' len));
            assert (~ (impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1')) sp m2 len))
          end
        end
      end
    end
    else begin
      assert (forall l' . ~ (impl_serialize_map_group_valid l' sp m2 len));
      assert (~ (impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))
    end
  end
  else assert (~ (impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))

#pop-options

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
      impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp (map_of_list_cons key_eq k v m2) len <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v))) /\
      FStar.UInt.fits (cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1) 64 /\
      Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) + Seq.length (Cbor.cbor_det_serialize (sp1.serializer k)) + Seq.length (Cbor.cbor_det_serialize (sp2.serializer v)) <= len /\
      (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
      (sp.mg_serializable (map_of_list_snoc key_eq m1 k v) ==>
        impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v))) sp m2 len
      )
    )) /\ (
      (
        sp1.serializable k /\
        sp2.serializable v /\
        (~ (except (sp1.serializer k, sp2.serializer v))) /\
        (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
      ) ==> (
      sp.mg_serializable (map_of_list_snoc key_eq m1 k v) /\
      cbor_map_disjoint l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) /\
      cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)) /\
      cbor_map_length (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_length (sp.mg_serializer m1) + 1
  ))))
=
  impl_serialize_map_group_valid_map_zero_or_more_snoc_aux sp1 key_eq sp2 except l m1 k v m2 len;
  impl_serialize_map_group_valid_map_zero_or_more_snoc' sp1 key_eq sp2 except l m1 k v m2 len ()

#restart-solver
let map_of_list_sub
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m: Map.t key (list value))
  (k: key)
  (v: value)
  (lv': list value)
: Pure (Map.t key (list value))
  (requires (
    Map.get m k == Some (v :: lv')
  ))
  (ensures fun m' ->
    (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m') /\
    m == map_of_list_cons key_eq k v m'
  )
= 
  let f (kv: (key & list value)) : bool =
    not (key_eq k (fst kv))
  in
  let m' : Map.t key (list value) = match lv' with
  | [] -> Map.filter f m
  | _ -> EqTest.map_set #key #(list value) m k (key_eq k) lv'
  in
  assert (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m');
  assert (Map.equal m (map_of_list_cons key_eq k v m'));
  m'

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_overflow
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\
    (~ (m2 == Map.empty _ _)) /\
    (~ (FStar.UInt.fits (cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1) 64))
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    ~ (impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp m2 len)
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let prf
    (k: key)
  : Lemma
    (requires (Map.defined k m2))
    (ensures (
      ~ (impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp m2 len)
    ))
  = assert (Some? (Map.get m2 k));
    let Some lv = Map.get m2 k in
    assert (Cons? lv);
    let v :: lv' = lv in
    let m2' = map_of_list_sub key_eq m2 k v lv' in
    map_of_list_is_append_cons key_eq k v m2';
    impl_serialize_map_group_valid_map_zero_or_more_snoc sp1 key_eq sp2 except l m1 k v m2' len;
    ()
  in
  Classical.forall_intro (Classical.move_requires prf);
  assert (~ (Map.equal m2 (Map.empty _ _)));
  ()

#restart-solver
let impl_serialize_map_group_insert_prf
  (w: Seq.seq U8.t)
  (l: cbor_map)
  (sz0: nat)
  (k: cbor)
  (sz1: nat)
  (v: cbor)
  (sz2: nat)
  (w2: Seq.seq U8.t)
: Lemma
  (requires (
    let sl = Cbor.cbor_det_serialize_map l in
    let sk = Cbor.cbor_det_serialize k in
    w == Seq.append sl (Seq.append sk w2) /\
    Seq.length sl == sz0 /\
    Seq.length sk == sz1 /\
    sz2 <= Seq.length w2 /\
    Seq.slice w2 0 sz2 == Cbor.cbor_det_serialize v /\
    SZ.fits (sz0 + sz1 + sz2)
  ))
  (ensures (
    SZ.fits (sz0 + sz1 + sz2) /\
    sz0 + sz1 + sz2 <= Seq.length w /\
    cbor_det_serialize_map_insert_pre l (SZ.uint_to_t sz0) k (SZ.uint_to_t (sz0 + sz1)) v (Seq.slice w 0 (sz0 + sz1 + sz2))
  ))
= let w' = Seq.slice w 0 (sz0 + sz1 + sz2) in
  let size0 = SZ.uint_to_t sz0 in
  let size1 = SZ.uint_to_t (sz0 + sz1) in
  let size2 = SZ.uint_to_t (sz0 + sz1 + sz2) in
            Seq.slice_slice w 0 (SZ.v size2) 0 (SZ.v size0);
            Seq.slice_slice w (SZ.v size0) (Seq.length w) 0 (sz1);
            Seq.slice_slice w 0 (SZ.v size2) (SZ.v size0) (SZ.v size1);
            Seq.slice_slice w (SZ.v size0) (Seq.length w) (sz1) (sz1 + Seq.length w2);
            Seq.slice_slice w (SZ.v size1) (Seq.length w) 0 (sz2);
            Seq.slice_slice w (SZ.v size1) (SZ.v size2) 0 (sz2);
            Seq.slice_slice w 0 (SZ.v size2) (SZ.v size1) (SZ.v size2);
  ()

let impl_serialize_map_group_insert_prf_post
  (w: Seq.seq U8.t)
  (l: cbor_map)
  (sz0: nat)
  (k: cbor)
  (sz1: nat)
  (v: cbor)
  (sz2: nat)
  (w2: Seq.seq U8.t)
: Tot prop
=
    SZ.fits (sz0 + sz1 + sz2) /\
    sz0 + sz1 + sz2 <= Seq.length w /\
    cbor_det_serialize_map_insert_pre l (SZ.uint_to_t sz0) k (SZ.uint_to_t (sz0 + sz1)) v (Seq.slice w 0 (sz0 + sz1 + sz2))

#restart-solver
let slice_split_post
  (#t: Type)
  (i: SZ.t)
  (v v1 v2: Seq.seq t)
: Tot prop
= SZ.v i <= Seq.length v /\
  v1 == Seq.slice v 0 (SZ.v i) /\
  v2 == Seq.slice v (SZ.v i) (Seq.length v) /\
  Seq.length v1 == SZ.v i /\
  Seq.length v2 == Seq.length v - SZ.v i /\
  v == Seq.append v1 v2

inline_for_extraction noextract [@@noextract_to "krml"]
fn slice_split (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t) (#v: Ghost.erased (Seq.seq t))
    requires pts_to s #p v ** pure (
      SZ.v i <= Seq.length v
    )
    returns res: (S.slice t & S.slice t)
    ensures (let (s1, s2) = res in exists* v1 v2 .
      pts_to s1 #p v1 **
      pts_to s2 #p v2 **
      S.is_split s s1 s2 **
      pure (slice_split_post i v v1 v2)
    )
{
  Seq.lemma_split v (SZ.v i);
  let (s1, s2) = S.split s i;
  (s1, s2)
}

module Util = CBOR.Spec.Util

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator_gen_t
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    ([@@@erasable]r1: rel ikey tkey)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    ([@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    ([@@@erasable] except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (#ivalue: Type0)
    ([@@@erasable]r2: rel ivalue tvalue)
    (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec ikey) -> [@@@erasable] Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
= impl_serialize_map_group #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (r (Iterator.mk_spec r1) (Iterator.mk_spec r2))

let impl_serialize_map_zero_or_more_iterator_inv
    (#key: typ)
    (#tkey: Type0)
    (sp1: (spec key tkey true))
    (#value: typ)
    (#tvalue: Type0)
    (#inj: bool)
    (sp2: (spec value tvalue inj))
    (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (v0: Map.t tkey (list tvalue))
  (l: cbor_map)
  (res: bool)
  (w: Seq.seq U8.t)
  (m1 m2 m2': Map.t tkey (list tvalue))
  (count: U64.t)
  (size: SZ.t)
: Tot prop
=
  let sp = (mg_zero_or_more_match_item sp1 sp2 except) in
      map_of_list_is_append m1 m2' v0 /\
      map_of_list_maps_to_nonempty m1 /\
      sp.mg_serializable m1 /\
      cbor_map_disjoint l (sp.mg_serializer m1) /\
      (res == true ==> (
        m2' == m2 /\
        impl_serialize_map_group_pre count size (cbor_map_union l (sp.mg_serializer m1)) w
      )) /\
      impl_serialize_map_group_valid l sp v0 (Seq.length w) == (res && impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1)) sp m2' (Seq.length w))

let seq_slice_length_zero_left
  (#t: Type)
  (s: Seq.seq t)
  (len: nat { len <= Seq.length s })
: Lemma
  (Seq.length (Seq.slice s 0 len) == len)
= ()

// #push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --query_stats --print_implicits --split_queries always"
#push-options "--admit_smt_queries true"

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_iterator_gen
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_det_parse_t vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_det_serialize_map_insert_t)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize sp2 r2)
    (#[@@@erasable] except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
    (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec ikey) -> [@@@erasable] Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
    (is_empty: cddl_map_iterator_is_empty_gen_t _ _ iterator r)
    (next: cddl_map_iterator_next_gen_t _ _ iterator r)
    (rel_len: rel_map_iterator_length _ _ iterator r)
: impl_serialize_map_zero_or_more_iterator_gen_t #key #tkey sp1 #ikey r1 #value #tvalue #inj sp2 except #ivalue r2 iterator r
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  admit (); // Pulse OOM even without SMT
(*  
  let sp = Ghost.hide (mg_zero_or_more_match_item sp1 sp2 except);
  let mut pc = c0;
  let pm1 = GR.alloc (Map.empty tkey (list tvalue));
  assert (pure (
    let m1 = Map.empty tkey (list tvalue) in
    sp.mg_serializable m1 /\
    sp.mg_serializer m1 `cbor_map_equal` cbor_map_empty
  ));
  let pm2 = GR.alloc (Ghost.reveal v0);
  let mut pres = true;
  Trade.refl (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0);
  while (
    let res = !pres;
    if (res) {
      with gc . assert (pts_to pc gc);
      let c = !pc;
      rewrite each (Ghost.reveal gc) as c;
      let em = is_empty (Iterator.mk_spec r1) (Iterator.mk_spec r2) c;
      not em
    } else {
      false
    }
  ) invariant b . exists* c m1 m2' (m2: Map.t (dfst (Iterator.mk_spec r1)) (list (dfst (Iterator.mk_spec r2)))) res w count size . ( // FIXME: WHY WHY WHY the type annotation on m2?
    pts_to pc c **
    GR.pts_to pm1 m1 **
    GR.pts_to pm2 m2' **
    pts_to pres res **
    pts_to out w **
    pts_to out_count count **
    pts_to out_size size **
    r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c m2 **
    Trade.trade 
      (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c m2)
      (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0) **
    pure (
      impl_serialize_map_zero_or_more_iterator_inv sp1 sp2 except v0 l res w m1 (Ghost.hide (Ghost.reveal m2)) m2' count size
    ) ** pure (
      b == (res && not (FStar.StrongExcludedMiddle.strong_excluded_middle (m2 == Map.empty _ _)))
    )
  ) {
    rel_len #(Iterator.mk_spec r1) #(Iterator.mk_spec r2) _ _;
    S.pts_to_len out;
    with m1 . assert (GR.pts_to pm1 m1);
    let count = !out_count;
    with c2_ m2_ . assert (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c2_ m2_);
    if (count = pow2_64_m1) {
      impl_serialize_map_group_valid_map_zero_or_more_snoc_overflow sp1 key_eq sp2 except l m1 m2_ (SZ.v (S.len out));
      pres := false
    } else {
      let count' = U64.add count 1uL;
      let (ck, cv) = next (Iterator.mk_spec r1) (Iterator.mk_spec r2) pc;
      with ke_ va_ . assert (dsnd (Iterator.mk_spec r1) (fst (ck, cv)) ke_ ** dsnd (Iterator.mk_spec r2) (snd (ck, cv)) va_);
      let ke : Ghost.erased tkey = Ghost.hide (Ghost.reveal ke_);
      let va : Ghost.erased tvalue = Ghost.hide (Ghost.reveal va_);
      Trade.rewrite_with_trade
        (dsnd (Iterator.mk_spec r1) (fst (ck, cv)) _ ** dsnd (Iterator.mk_spec r2) (snd (ck, cv)) _)
        (r1 ck ke ** r2 cv va);
      Trade.trans_hyp_l (r1 ck ke ** r2 cv va) _ _ _;
      Trade.trans _ _ (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0);
      with c2 m2 . assert (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c2 m2);
      rel_len #(Iterator.mk_spec r1) #(Iterator.mk_spec r2) _ _;
      impl_serialize_map_group_valid_map_zero_or_more_snoc sp1 key_eq sp2 except l m1 ke va m2 (SZ.v (S.len out));
      let mkv : Ghost.erased (Map.t tkey (list tvalue)) = EqTest.map_singleton (Ghost.reveal ke) (Ghost.reveal key_eq ke) [Ghost.reveal va];
      let m2' : Ghost.erased (Map.t tkey (list tvalue)) = map_of_list_cons key_eq (Ghost.reveal ke) (Ghost.reveal va) m2;
      Classical.forall_intro (EqTest.eq_test_unique key_eq);
      assert (pure (m2' == m2_));
//    map_of_list_is_append_serializable_elim sp1 key_except sp2 m1 m2' v0;
//    map_of_list_is_append_serializable_elim sp1 key_except sp2 mkv m2 m2';
      map_of_list_is_append_cons_snoc_equiv key_eq m1 ke va m2 v0;
      let m1' : Ghost.erased (Map.t tkey (list tvalue)) = map_of_list_snoc key_eq m1 (Ghost.reveal ke) (Ghost.reveal va);
//    map_of_list_is_append_serializable_intro sp1 key_except sp2 m1 mkv m1';
//    map_of_list_is_append_serializable_intro sp1 key_except sp2 m1' m2 v0;
      let size0 = !out_size;
      with w . assert (pts_to out w);
      Seq.lemma_split w (SZ.v size0);
      let sqw : squash (Seq.slice w 0 (SZ.v size0) == Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) = ();
      let (outl1, out1) = S.split out size0;
      with z1l . assert (pts_to outl1 z1l);
      let sz1 = pa1 ck out1;
      S.pts_to_len out1;
//    map_of_list_is_append_serializable_singleton sp1 key_except sp2 ke (Ghost.reveal key_eq ke) va;
      if (sz1 = 0sz) {
        S.join _ _ out;
        S.pts_to_len out;
        Trade.elim_hyp_l _ _ _;
        assert (pure (sp1.serializable ke ==> Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) + Seq.length (Cbor.cbor_det_serialize (sp1.serializer ke)) > Seq.length w));
        pres := false
      } else {
        with w1 . assert (pts_to out1 w1);
        Seq.lemma_split w1 (SZ.v sz1);
        let w1' = Ghost.hide (Seq.slice w1 (SZ.v sz1) (Seq.length w1));
        Cbor.cbor_det_serialize_parse' (sp1.serializer ke) w1';
        let (outl2, out2) = S.split out1 sz1;
        with z2l . assert (pts_to outl2 z2l);
        S.pts_to_len out2;
        let sz2 = pa2 cv out2;
        with w2 . assert (pts_to out2 w2);
        S.pts_to_len out2;
        S.pts_to_len outl2;
//        with w' . assert (pts_to out w');
//        assert (pure (w' == Seq.append (Seq.slice w 0 (SZ.v size0)) (Seq.append (Seq.slice w1 0 (SZ.v sz1)) w2)));
        Trade.elim_hyp_l _ _ _;
        if (sz2 = 0sz) {
          S.join _ _ out1;
          S.pts_to_len out1;
          S.pts_to_len outl1;
          S.join _ _ out;
          S.pts_to_len out;
          pres := false
        } else {
          Seq.lemma_split w2 (SZ.v sz2);
          let w2' = Ghost.hide (Seq.slice w2 (SZ.v sz2) (Seq.length w2));
          Cbor.cbor_det_serialize_parse' (sp2.serializer va) w2';
                                   //            assert (pure (SZ.v size2 == SZ.v size0 + (SZ.v sz1 + SZ.v sz2)));
          with vl . assert (pts_to outl2 vl);
          assert (pure (Seq.equal vl (CBOR.Spec.API.Format.cbor_det_serialize (sp1.serializer ke))));
          Seq.append_empty_r (CBOR.Spec.API.Format.cbor_det_serialize (sp1.serializer ke));
          assert (pure (Seq.append (CBOR.Spec.API.Format.cbor_det_serialize (sp1.serializer ke)) Seq.empty == vl));
          Cbor.cbor_det_serialize_parse' (sp1.serializer ke) Seq.empty;
//          assert (pure (Seq.length vl == SZ.v size2));
          S.pts_to_len outl2;
//          assert (pure (S.len outl == size2));
          let Some oo1 = parse outl2;
          norewrite let (o1, orem1) = oo1;
          rewrite (cbor_det_parse_post vmatch' outl2 1.0R vl (Some oo1))
            as (cbor_det_parse_post_some vmatch' outl2 1.0R vl o1 orem1);
          unfold (cbor_det_parse_post_some vmatch' outl2 1.0R vl o1 orem1);
          with ke' . assert (vmatch' 1.0R o1 ke');
          with w1'' . assert (pts_to orem1 w1'');
          Cbor.cbor_det_serialize_inj_strong ke' (sp1.serializer ke) w1'' Seq.empty;
          assert (pure (Ghost.reveal ke' == sp1.serializer ke));
          let Some oo2 = parse out2;
          norewrite let (o2, orem2) = oo2;
          rewrite (cbor_det_parse_post vmatch' out2 1.0R w2 (Some oo2))
            as (cbor_det_parse_post_some vmatch' out2 1.0R w2 o2 orem2);
          unfold (cbor_det_parse_post_some vmatch' out2 1.0R w2 o2 orem2);
          with va' . assert (vmatch' 1.0R o2 va');
          with (w2'' : Seq.seq U8.t) . assert (pts_to orem2 w2'');
          Cbor.cbor_det_serialize_inj_strong va' (sp2.serializer va) w2'' w2';
          assert (pure (Ghost.reveal va' == sp2.serializer va));
          let o = mk_map_entry o1 o2;
          let is_except = va_ex o;
          Trade.elim (vmatch2' 1.0R o _) _;
          Trade.elim (vmatch' 1.0R o2 va' ** pts_to orem2 w2'') (pts_to out2 w2);
          Trade.elim (vmatch' 1.0R o1 ke' ** pts_to orem1 _) (pts_to outl2 _);
          S.join outl2 out2 out1;
          S.join outl1 out1 out;
          S.pts_to_len out;
          if (is_except) {
            assert (pure (Ghost.reveal except ((sp1.serializer ke <: cbor), (sp2.serializer va <: cbor)) == true));
            pres := false
          } else {
            let size1 = SZ.add size0 sz1;
            let size2 = SZ.add size1 sz2;
            with w' . assert (pts_to out w');
            let (outl, outr) = slice_split out size2;
            S.pts_to_len outl;
            S.pts_to_len outr;
            let sqw2 : squash (Seq.slice w 0 (SZ.v size0) == Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) = sqw;
            seq_slice_length_zero_left w (SZ.v size0);
            assert (pure (Seq.length (Seq.slice w 0 (SZ.v size0)) == SZ.v size0));
            assert (pure (Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1))) == SZ.v size0));
            assert (pure (Seq.slice w1 0 (SZ.v sz1) == Cbor.cbor_det_serialize (sp1.serializer ke)));
            impl_serialize_map_group_insert_prf w' (cbor_map_union l (sp.mg_serializer m1)) (SZ.v size0) (sp1.serializer ke) (SZ.v sz1) (sp2.serializer va) (SZ.v sz2) w2;
            assert (pure (
              impl_serialize_map_group_insert_prf_post
                w' (cbor_map_union l (sp.mg_serializer m1)) (SZ.v size0) (sp1.serializer ke) (SZ.v sz1) (sp2.serializer va) (SZ.v sz2) w2
            ));
            let inserted = insert outl (cbor_map_union l (sp.mg_serializer m1)) size0 (sp1.serializer ke) size1 (sp2.serializer va);
            S.pts_to_len outl;
            with wl . assert (pts_to outl wl);
            assert (pure (Seq.length wl == SZ.v size2));
            with wr . assert (pts_to outr wr);
            S.join _ _ out;
            S.pts_to_len out;
            if (not inserted) {
              pres := false
            } else {
              GR.op_Colon_Equals pm1 m1';
              GR.op_Colon_Equals pm2 m2;
              out_count := count';
              out_size := size2;
              assert (pure (wl == Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1'))));
              with w_ . assert (pts_to out w_);
              seq_slice_append_pat wl wr;
              assert (pure (
                w_ == Seq.append wl wr
              ));
              assert (pure (
                Seq.slice w_ 0 (SZ.v size2) == Cbor.cbor_det_serialize_map (cbor_map_union l (sp.mg_serializer m1'))
              ));
              assert (pure (map_of_list_is_append m1' m2 v0));
              assert (pure (map_of_list_maps_to_nonempty m1'));
              assert (pure (sp.mg_serializable m1'));
              assert (pure (cbor_map_disjoint l (sp.mg_serializer m1')));
              assert (pure (      impl_serialize_map_group_pre count'
        size2
        (cbor_map_union l (sp.mg_serializer m1'))
        w_));
              assert (pure (
    impl_serialize_map_group_valid l
      sp
      v0
      (Seq.Base.length w_) ==
    (
    impl_serialize_map_group_valid (cbor_map_union l (sp.mg_serializer m1'))
      sp
      m2
      (Seq.Base.length w_))
                       ));
              ()
            }
          }
        }
      }
    }
  };
  Trade.elim _ _;
  with m1 . assert (GR.pts_to pm1 m1);
  GR.free pm1;
  GR.free pm2;
  Classical.move_requires (map_of_list_is_append_nil_r_elim m1) v0;
  !pres
*)
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_det_parse_t vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_det_serialize_map_insert_t)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize sp2 r2)
    (#[@@@erasable] except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_zero_or_more_iterator_t #ty vmatch #vmatch2 #cbor_map_iterator_t cbor_map_iterator_match #key #tkey sp1 #ikey r1 #value #tvalue #inj sp2 #ivalue r2 except
= impl_serialize_map_zero_or_more_iterator_gen
    parse
    mk_map_entry
    insert
    key_eq
    pa1
    pa2
    va_ex
    (map_iterator_t cbor_map_iterator_t _ _ vmatch vmatch2)
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match _ _)
    (cddl_map_iterator_is_empty map_is_empty map_next map_entry_key map_entry_value _ _)
    (cddl_map_iterator_next map_share map_gather map_next map_entry_key map_entry_value map_entry_share map_entry_gather _ _)
    (rel_map_iterator_prop' cbor_map_iterator_match)
    
inline_for_extraction
// noextract [@@noextract_to "krml"]
noeq
type map_slice_iterator_t
  (impl_elt1: Type0) (impl_elt2: Type0)
  ([@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ([@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: Type0
= {
  base: (slice (impl_elt1 & impl_elt2));
  key_eq: Ghost.erased (EqTest.eq_test (dfst spec1));
}

let rel_map_slice_iterator
  (impl_elt1: Type0) (impl_elt2: Type0)
  (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: rel (map_slice_iterator_t impl_elt1 impl_elt2 spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2)))
= mk_rel (fun s l -> rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) s.key_eq (dsnd spec1) (dsnd spec2) s.base l)

module SM = Pulse.Lib.SeqMatch

#push-options "--print_implicits"

inline_for_extraction noextract [@@noextract_to "krml"]
fn map_slice_iterator_is_empty
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_is_empty_gen_t _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (spec1: _)
  (spec2: _)
  (s: _)
  (#l: _)
{
  unfold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 s l);
  unfold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  s.key_eq (dsnd spec1) (dsnd spec2) s.base l);
  with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  unfold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  S.pts_to_len s.base.s;
  SM.seq_list_match_length (rel_pair (dsnd spec1) (dsnd spec2)) _ _;
  fold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  fold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  s.key_eq (dsnd spec1) (dsnd spec2) s.base l);
  fold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 s l);
  Classical.forall_intro (map_of_list_pair_mem_fst s.key_eq l');
  (S.len s.base.s = 0sz)
}

ghost
fn map_slice_iterator_length
  (impl_elt1: Type0) (impl_elt2: Type0)
: rel_map_iterator_length _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (#spec1: _)
  (#spec2: _)
  (i: _)
  (l: _)
{
  unfold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i l);
  unfold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  i.key_eq (dsnd spec1) (dsnd spec2) i.base l);
  with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  unfold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  S.pts_to_len i.base.s;
  SM.seq_list_match_length (rel_pair (dsnd spec1) (dsnd spec2)) _ _;
  fold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  fold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  i.key_eq (dsnd spec1) (dsnd spec2) i.base l);
  fold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i l);
  ()
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn map_slice_iterator_next
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_next_gen_t _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (spec1: _)
  (spec2: _)
  (pi: _)
  (#gi: _)
  (#m: _)
{
  let i = !pi;
  let r : rel (impl_elt1 & impl_elt2) (dfst spec1 & dfst spec2) = (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2));
  Trade.rewrite_with_trade
    (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 gi m)
    (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  with l . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l);
  rewrite (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l)
    as (rel_slice_of_list r false i.base l);
  unfold (rel_slice_of_list r false i.base l);
  S.pts_to_len i.base.s;
  with s . assert (pts_to i.base.s #i.base.p s);
  SM.seq_list_match_length r _ _;
  Seq.lemma_split s 1;
  SM.seq_list_match_cons_elim _ _ r;
  with gres gv . assert (r gres gv);
  let res = S.op_Array_Access i.base.s 0sz;
  rewrite each gres as res;
//  rewrite (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2) gres gv)
//  rel_pair (dsnd spec1) (dsnd spec2) gres gv)
//    as (rel_pair (dsnd spec1) (dsnd spec2) res gv);
  let (il, ir) = S.split i.base.s 1sz;
  with sl . assert (pts_to il #i.base.p sl);
  with sr . assert (pts_to ir #i.base.p sr);
//  S.share ir;
  let i' : map_slice_iterator_t impl_elt1 impl_elt2 spec1 spec2 = {
    base = {
      s = ir;
      p = i.base.p (* /. 2.0R *) ;
    };
    key_eq = i.key_eq;
  };
  rewrite (pts_to ir #(i.base.p (* /. 2.0R *) ) sr) as (pts_to i'.base.s #i'.base.p (Seq.tail s));
  fold (rel_slice_of_list r false i'.base (List.Tot.tl l));
  rewrite (rel_slice_of_list r false i'.base (List.Tot.tl l))
    as (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base (List.Tot.tl l));
  let m' = Ghost.hide (map_of_list_pair i'.key_eq (List.Tot.tl l));
  fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m');
  Trade.rewrite_with_trade
    (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m')
    (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i' m');
  intro
    (Trade.trade
      (
        r res gv ** rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m'
      )
      (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m)
    )
    #(S.is_split i.base.s il ir ** pts_to il #i.base.p sl (* ** pts_to ir #(i.base.p /. 2.0R) sr *) )
    fn _
  {
    unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m');
    with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base l');
    rewrite (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base l')
      as (rel_slice_of_list r false i'.base l');
    unfold (rel_slice_of_list r false i'.base l');
    with s' . assert (pts_to i'.base.s #i'.base.p s');
    SM.seq_list_match_cons_intro res (Ghost.reveal gv) s' l' r;
    with s1 s2 s . rewrite (S.is_split s1 s2 s) as S.is_split i.base.s il i'.base.s;
    S.join il i'.base.s i.base.s;
    with s1 . assert pts_to i.base.s #i.base.p s1;
    with s2 . rewrite SM.seq_list_match s2 (Ghost.reveal gv :: l') (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2))
      as SM.seq_list_match s1 (Ghost.reveal gv :: l') (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2));
    fold (rel_slice_of_list
      (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2))
      false
      i.base
      (Ghost.reveal gv :: l')
    );
    fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  };
  Trade.trans_hyp_r _ _ _ _;
  Trade.trans _ (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m) (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 gi m);
  Trade.rewrite_with_trade
    (r res gv)
    (dsnd spec1 (fst res) (fst gv) ** dsnd spec2 (snd res) (snd gv));
  Trade.trans_hyp_l _ (r res gv) _ _;
  pi := i';
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_slice
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_det_parse_t vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_det_serialize_map_insert_t)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize sp2 r2)
    (#[@@@erasable] except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_slice_of_table key_eq r1 r2)
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let i : map_slice_iterator_t ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) = {
    base = c0;
    key_eq = key_eq;
  };
  Trade.rewrite_with_trade
    (rel_slice_of_table key_eq r1 r2 c0 v0)
    (rel_map_slice_iterator ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) i v0);
  let mut pi = i;
  let res = impl_serialize_map_zero_or_more_iterator_gen
    parse
    mk_map_entry
    insert
    key_eq
    pa1
    pa2
    va_ex
    (map_slice_iterator_t _ _)
    (rel_map_slice_iterator _ _)
    (map_slice_iterator_is_empty _ _)
    (map_slice_iterator_next _ _)
    (map_slice_iterator_length _ _)
    i
    out
    out_count
    out_size
    l;
  Trade.elim _ _;
  res
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (#ty' #ty2': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_det_parse_t vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_det_serialize_map_insert_t)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize sp2 r2)
    (#[@@@erasable] except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_either_left (rel_slice_of_table key_eq r1 r2) (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2)))
= impl_serialize_map_group_either_left
    (impl_serialize_map_zero_or_more_slice
      parse
      mk_map_entry
      insert
      key_eq
      pa1
      pa2
      va_ex
    )
    (impl_serialize_map_zero_or_more_iterator
      map_share map_gather map_is_empty map_next map_entry_key map_entry_value map_entry_share map_entry_gather
      parse
      mk_map_entry
      insert
      key_eq
      pa1
      pa2
      va_ex
    )

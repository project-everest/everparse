module CDDL.Pulse.Serialize.ArrayGroup
#lang-pulse

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array
   (cbor_det_serialize_array: cbor_det_serialize_array_t)
    (# [@@@erasable] t: Ghost.erased (array_group None))
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_array_group s r)
: impl_serialize #_ #_ #_ (spec_array_group s) #_ r
=
  (c: _)
  (#v: _)
  (out: _)
{
  let mut pcount = 0uL;
  let mut psize = 0sz;
  Cbor.cbor_det_serialize_list_nil ();
  let res = i c out pcount psize [];
  Classical.forall_intro (Classical.move_requires Cbor.cbor_det_serialize_array_length_gt_list);
  if (res) {
    let size = !psize;
    let count = !pcount;
    cbor_det_serialize_array count out (s.ag_serializer v) size
  } else {
    0sz
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_ext
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group ps r)
    (#[@@@erasable]t': Ghost.erased (array_group None))
    (#[@@@erasable] inj': Ghost.erased bool)
    ([@@@erasable]ps': Ghost.erased (ag_spec t' tgt inj'))
    ([@@@erasable]sq: squash (
      (Ghost.reveal inj == true \/ Ghost.reveal inj' == true) /\
      array_group_equiv t' t /\
      (forall (x: list cbor) . array_group_parser_spec_refinement (Ghost.reveal t') x ==> ((Ghost.reveal ps'.ag_parser x <: tgt) == Ghost.reveal ps.ag_parser x))
    ))
: impl_serialize_array_group #(Ghost.reveal t') #tgt #inj' (Ghost.reveal ps') #impl_tgt r
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

inline_for_extraction noextract [@@noextract_to "krml";
  FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
]
let pow2_64_m1 : U64.t = U64.uint_to_t (pow2 64 - 1)

let pow2_64_m1_eq : squash (U64.v pow2_64_m1 == pow2 64 - 1) = _ by (
  FStar.Tactics.norm [delta; zeta; iota; primops];
  FStar.Tactics.trefl ()
)

let list_append_length_pat
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (List.Tot.length (List.Tot.append l1 l2) == List.Tot.length l1 + List.Tot.length l2)
  [SMTPat (List.Tot.append l1 l2)]
= List.Tot.append_length l1 l2

let impl_serialize_array_group_item_correct
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (ps: spec t tgt inj)
    (l: list Cbor.cbor)
    (v: tgt)
    (size': nat)
: Lemma
  ((
    ps.serializable v /\
    Seq.length (Cbor.cbor_det_serialize (ps.serializer v)) <= size'
  ) <==> (
    (ag_spec_item ps).ag_serializable v /\
    Seq.length (Cbor.cbor_det_serialize_list (List.Tot.append l ((ag_spec_item ps).ag_serializer v))) <= Seq.length (Cbor.cbor_det_serialize_list l) + size'
  ))
= assert (ps.serializable v == (ag_spec_item ps).ag_serializable v);
  if (ps.serializable v)
  then begin
    Cbor.cbor_det_serialize_list_snoc l (ps.serializer v)
  end

let seq_slice_append
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
= ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_item
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize ps r)
: impl_serialize_array_group #_ #_ #_ (ag_spec_item ps) #_ r
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
    let size = !out_size;
    with w . assert (pts_to out w);
    Seq.lemma_split w (SZ.v size);
    let (out0, out1) = S.split out size;
    let w0 = Ghost.hide (Cbor.cbor_det_serialize_list l);
    assert (pts_to out0 w0);
    let size1 = i c out1;
    S.pts_to_len out1;
    with w1 . assert (pts_to out1 w1);
    seq_slice_append w0 w1;
    S.join _ _ out;
    S.pts_to_len out;
    impl_serialize_array_group_item_correct ps l v (SZ.v (S.len out1));
    if (size1 = 0sz) {
      false
    } else {
      Cbor.cbor_det_serialize_list_snoc l (ps.serializer v);
      out_count := U64.add count 1uL;
      out_size := (SZ.add size size1);
      true
    }
  } else {
    false
  }
}

let list_append_assoc_pat
  (#t: Type)
  (l1 l2 l3: list t)
: Lemma
  (ensures (List.Tot.append l1 (List.Tot.append l2 l3) == List.Tot.append (List.Tot.append l1 l2) l3))
  [SMTPatOr [
    [SMTPat (List.Tot.append l1 (List.Tot.append l2 l3))];
    [SMTPat (List.Tot.append (List.Tot.append l1 l2) l3)];
  ]]
= List.Tot.append_assoc l1 l2 l3

let cbor_det_serialize_list_append_pat
  (l1 l2: list cbor)
: Lemma
  (ensures (Cbor.cbor_det_serialize_list (List.Tot.append l1 l2) == Seq.append (Cbor.cbor_det_serialize_list l1) (Cbor.cbor_det_serialize_list l2)))
  [SMTPat (Cbor.cbor_det_serialize_list (List.Tot.append l1 l2))]
= Cbor.cbor_det_serialize_list_append l1 l2

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_concat
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group ps2 r2)
    (sq: squash (
      array_group_concat_unique_weak t1 t2
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_concat ps1 ps2) #_ (rel_pair r1 r2)
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
  if (res1) {
    let res2 = i2 c2 out out_count out_size (List.Tot.append l (ps1.ag_serializer (fst v)));
    Trade.elim _ _;
    res2
  } else {
    Trade.elim _ _;
    false
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_choice
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group ps2 r2)
    (sq: squash (
      array_group_disjoint t1 t2
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_choice ps1 ps2) #_ (rel_either r1 r2)
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

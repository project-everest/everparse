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

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_ext'
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group ps r)
    ([@@@erasable]t': Ghost.erased (array_group None))
    ([@@@erasable]sq: squash (
      array_group_equiv t' t
    ))
: impl_serialize_array_group #(Ghost.reveal t') #tgt #inj (ag_spec_ext ps t') #impl_tgt r
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
fn impl_serialize_array_group_bij
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group ps r)
    (#[@@@erasable]tgt' : Type0)
    ([@@@erasable]f12: Ghost.erased (tgt -> tgt'))
    ([@@@erasable]f21: Ghost.erased (tgt' -> tgt))
    ([@@@erasable]fprf_21_12: (x: tgt) -> squash (Ghost.reveal f21 (Ghost.reveal f12 x) == x))
    ([@@@erasable]fprf_12_21: (x: tgt') -> squash (Ghost.reveal f12 (Ghost.reveal f21 x) == x))
    (#impl_tgt' : Type0)
    (g12: (impl_tgt -> impl_tgt'))
    (g21: (impl_tgt' -> impl_tgt))
    ([@@@erasable]gprf_21_12: (x: impl_tgt) -> squash (g21 (g12 x) == x))
    ([@@@erasable]gprf_12_21: (x: impl_tgt') -> squash (g12 (g21 x) == x))
: impl_serialize_array_group #(Ghost.reveal t) #tgt' #inj (ag_spec_inj ps f12 f21 fprf_21_12 fprf_12_21) #impl_tgt' (rel_fun r g21 f21)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let c' = g21 c;
  Trade.rewrite_with_trade
    (rel_fun r g21 f21 c v)
    (r c' (Ghost.reveal f21 v));
  let res = i c' #(Ghost.reveal f21 v) out out_count out_size l;
  Trade.elim _ _;
  res
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
fn impl_serialize_array_group_close_intro
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
: impl_serialize_array_group #_ #_ #_ (ag_spec_close_intro ps1) #_ r1
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  i1 c out out_count out_size l
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_close_elim
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec (close_array_group t1) tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
: impl_serialize_array_group #_ #_ #_ (ag_spec_close_elim ps1) #_ r1
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  i1 c out out_count out_size l
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

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_choice'
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
      array_group_disjoint t1 (close_array_group t2)
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_choice' ps1 ps2) #_ (rel_either r1 r2)
= impl_serialize_array_group_close_elim
    (impl_serialize_array_group_ext'
      (impl_serialize_array_group_close_intro
        (impl_serialize_array_group_choice
          i1
          (impl_serialize_array_group_close_intro i2)
          ()
        )
      )
      (close_array_group (array_group_choice t1 t2))
      ()
    )

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_zero_or_one
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_zero_or_one ps1) #_ (rel_option r1)
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

module SM = Pulse.Lib.SeqMatch.Util
module GR = Pulse.Lib.GhostReference

let list_append_nil_r_pat
  (#t: Type)
  (l1: list t)
: Lemma
  (List.Tot.append l1 [] == l1)
  [SMTPat (List.Tot.append l1 [])]
= List.Tot.append_l_nil l1

let rec ag_spec_zero_or_more_size_append
  (#target: Type)
  (p: target -> nat)
  (l1 l2: list target)
: Lemma
  (ensures (ag_spec_zero_or_more_size p (List.Tot.append l1 l2) == ag_spec_zero_or_more_size p l1 + ag_spec_zero_or_more_size p l2))
  (decreases l1)
= match l1 with
  | [] -> ()
  | hd :: tl -> ag_spec_zero_or_more_size_append p tl l2

let rec ag_spec_zero_or_more_serializer_append
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (ps1: (ag_spec source target inj) {
    array_group_concat_unique_strong source source
  })
  (l1 l2: list target)
: Lemma
  (requires (
    ag_spec_zero_or_more_serializable ps1.ag_serializable l1 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable l2
  ))
  (ensures (
    ag_spec_zero_or_more_serializable ps1.ag_serializable l1 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable l2 /\
    ag_spec_zero_or_more_serializable ps1.ag_serializable (List.Tot.append l1 l2) /\
    (ag_spec_zero_or_more ps1).ag_serializer (List.Tot.append l1 l2) ==
      List.Tot.append
        ((ag_spec_zero_or_more ps1).ag_serializer l1)
        ((ag_spec_zero_or_more ps1).ag_serializer l2)
  ))
  (decreases l1)
= 
  match l1 with
  | [] -> ()
  | hd :: tl -> ag_spec_zero_or_more_serializer_append ps1 tl l2

let ag_serializable_zero_or_more_append
    (#t1: (array_group None))
    (#tgt1: Type0)
    (#inj1: bool)
    (ps1: (ag_spec t1 tgt1 inj1))
    (l1 l2: list tgt1)
: Lemma
  (requires (array_group_is_nonempty t1 /\ array_group_concat_unique_strong t1 t1))
  (ensures (
    array_group_is_nonempty t1 /\ array_group_concat_unique_strong t1 t1 /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_size (List.Tot.append l1 l2) == ps.ag_size l1 + ps.ag_size l2 /\
    ps.ag_serializable (List.Tot.append l1 l2) == (ps.ag_serializable l1 && ps.ag_serializable l2)) /\
    ((ps.ag_serializable l1 /\ ps.ag_serializable l2) ==>
      ps.ag_serializer (List.Tot.append l1 l2) == List.Tot.append (ps.ag_serializer l1) (ps.ag_serializer l2)
    )
  )))
= ag_spec_zero_or_more_size_append ps1.ag_size l1 l2;
  List.Tot.for_all_append ps1.ag_serializable l1 l2;
  let ps = ag_spec_zero_or_more ps1 in
  if ps.ag_serializable l1 && ps.ag_serializable l2
  then begin
    ag_spec_zero_or_more_serializer_append ps1 l1 l2
  end;
  ()

#push-options "--z3rlimit 64"

let impl_serialize_array_group_valid_zero_or_more_false_intro
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (len: nat)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    impl_serialize_array_group_valid (List.Tot.append l (ps.ag_serializer l1)) ps1 x len == false
  ))))
  (ensures (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    impl_serialize_array_group_valid (List.Tot.append l (ps.ag_serializer l1)) ps (x :: l2) len == false
  ))))
= ag_serializable_zero_or_more_append ps1 l1 (x :: l2)

#pop-options

let impl_serialize_array_group_valid_zero_or_more_true_intro_length
  (x1 x2 x3 x4: nat)
: Lemma
  ((x1 + x2) + (x3 + x4) == (x1 + (x2 + x3)) + x4)
= ()

let impl_serialize_array_group_valid_zero_or_more_true_intro
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (ps1: ag_spec t tgt inj)
  (l1: list tgt)
  (x: tgt)
  (l2: list tgt)
  (count: U64.t)
  (size: SZ.t)
  (w: Seq.seq U8.t)
: Lemma
  (requires (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    impl_serialize_array_group_post count size (List.Tot.append l (ps.ag_serializer l1)) ps1 x w true
  ))))
  (ensures (
    array_group_is_nonempty t /\ array_group_concat_unique_strong t t /\ (
    let ps = ag_spec_zero_or_more ps1 in (
    ps.ag_serializable l1 /\
    ps.ag_serializable (List.Tot.append l1 [x]) /\
    impl_serialize_array_group_post count size (List.Tot.append l (ps.ag_serializer l1)) ps1 x w true /\
    impl_serialize_array_group_post count size l ps (List.Tot.append l1 [x]) w true /\
    impl_serialize_array_group_valid (List.Tot.append l (ps.ag_serializer l1)) ps (x :: l2) (Seq.length w) ==
    impl_serialize_array_group_valid (List.Tot.append l (ps.ag_serializer (List.Tot.append l1 [x]))) ps (l2) (Seq.length w)
  ))))
= let ps = ag_spec_zero_or_more ps1 in
  ag_serializable_zero_or_more_append ps1 l1 [x];
  assert (ps.ag_serializable (List.Tot.append l1 [x]));
  ag_spec_zero_or_more_serializer_append ps1 l1 [x];
  assert (let ps = ag_spec_zero_or_more ps1 in
    (ps.ag_serializer [x] <: list cbor) == List.Tot.append (ps1.ag_serializer x) [])
    by (FStar.Tactics.trefl ()); // FIXME: WHY WHY WHY?
  List.Tot.append_l_nil (ps1.ag_serializer x);
  assert ((ps.ag_serializer [x] <: list cbor) == ps1.ag_serializer x);
  assert ((ps.ag_size [x] <: nat) == ps1.ag_size x);
  ag_spec_zero_or_more_size_append ps1.ag_size l1 [x];
  List.Tot.append_assoc l (ps.ag_serializer l1) (ps1.ag_serializer x);
  assert (impl_serialize_array_group_post count size l ps (List.Tot.append l1 [x]) w true);
  List.Tot.append_length l (ps.ag_serializer l1);
  List.Tot.append_length l (ps.ag_serializer (List.Tot.append l1 [x]));
  List.Tot.append_length (ps.ag_serializer l1) (ps1.ag_serializer x);
  ag_serializable_zero_or_more_append ps1 [x] l2;
  assert (ps.ag_serializable (x :: l2) == ps.ag_serializable l2);
  if ps.ag_serializable l2
  then begin
    assert (
      let ps = ag_spec_zero_or_more ps1 in
      (ps.ag_serializer (x :: l2) <: list cbor) == List.Tot.append (ps1.ag_serializer x) (ps.ag_serializer l2)
    )
      by (FStar.Tactics.trefl ()); // FIXME: WHY WHY WHY?
    List.Tot.append_length (ps1.ag_serializer x) (ps.ag_serializer l2);
    let a = (List.Tot.length l + List.Tot.length (ps.ag_serializer l1)) + (List.Tot.length (ps1.ag_serializer x) + List.Tot.length (ps.ag_serializer l2)) in
    assert (
      List.Tot.length (List.Tot.append l (ps.ag_serializer l1)) + List.Tot.length (ps.ag_serializer (x :: l2)) ==
      a
    );
    let b = (List.Tot.length l + (List.Tot.length (ps.ag_serializer l1) + List.Tot.length (ps1.ag_serializer x))) + List.Tot.length (ps.ag_serializer l2) in
    assert (
      List.Tot.length (List.Tot.append l (ps.ag_serializer (List.Tot.append l1 [x]))) + List.Tot.length (ps.ag_serializer l2) ==
      b
    );
    impl_serialize_array_group_valid_zero_or_more_true_intro_length
      (List.Tot.length l)
      (List.Tot.length (ps.ag_serializer l1))
      (List.Tot.length (ps1.ag_serializer x))
      (List.Tot.length (ps.ag_serializer l2));
    assert (a == b);
    assert (
      List.Tot.length (List.Tot.append l (ps.ag_serializer l1)) + List.Tot.length (ps.ag_serializer (x :: l2)) ==
      List.Tot.length (List.Tot.append l (ps.ag_serializer (List.Tot.append l1 [x]))) + List.Tot.length (ps.ag_serializer l2)
    );
    assert (
      impl_serialize_array_group_valid (List.Tot.append l (ps.ag_serializer l1)) ps (x :: l2) (Seq.length w) ==
      impl_serialize_array_group_valid (List.Tot.append l (ps.ag_serializer (List.Tot.append l1 [x]))) ps (l2) (Seq.length w)
    );
    ()
  end
  else ()

#push-options "--z3rlimit 32"
#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_zero_or_more_slice
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_zero_or_more ps1) #_ (rel_slice_of_list r1 false)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let ps = Ghost.hide (ag_spec_zero_or_more ps1);
  unfold (rel_slice_of_list r1 false c v);
  with s . assert (pts_to c.s #c.p s ** SM.seq_list_match s v r1);
  intro
    (Trade.trade
      (pts_to c.s #c.p s ** SM.seq_list_match s v r1)
      (rel_slice_of_list r1 false c v)
    )
    #emp
    fn _
  {
    fold (rel_slice_of_list r1 false c v)
  };
  let pl1 : GR.ref (list tgt1) = GR.alloc (Nil #tgt1);
  let mut pres = true;
  let mut pi = 0sz;
  let slen = S.len c.s;
  Cbor.cbor_det_serialize_list_nil ();
  while (
    let res = !pres;
    if (res) {
      let i = !pi;
      S.pts_to_len c.s;
      (SZ.lt i slen)
    } else {
      false
    }
  ) invariant b. exists* l1 res i s2 l2 w count size . (
    GR.pts_to pl1 l1 **
    pts_to c.s #c.p s **
    pts_to pi i **
    SM.seq_list_match s2 l2 r1 **
    pts_to pres res **
    pts_to out w **
    pts_to out_count count **
    pts_to out_size size **
    Trade.trade
      (pts_to c.s #c.p s ** SM.seq_list_match s2 l2 r1)
      (rel_slice_of_list r1 false c v)
      **
    pure (
      SZ.v i <= Seq.length s /\
      Seq.equal s2 (Seq.slice s (SZ.v i) (Seq.length s)) /\
      Ghost.reveal v == List.Tot.append l1 l2 /\
      ps.ag_serializable l1 /\
      (impl_serialize_array_group_valid l ps v (Seq.length w) == (res && impl_serialize_array_group_valid (l `List.Tot.append` ps.ag_serializer l1) ps l2 (Seq.length w))) /\
      (res == true ==> impl_serialize_array_group_post count size l ps l1 w true) /\
      b == (res && (SZ.v i < Seq.length s))
    )
  ) {
    with s2 l2 . assert (SM.seq_list_match s2 l2 r1);
    S.pts_to_len c.s;
    SM.seq_list_match_length r1 s2 l2;
    let _ = SM.seq_list_match_cons_elim_trade s2 l2 r1;
    with s2' l2' . assert (SM.seq_list_match s2' l2' r1);
    let y = Ghost.hide (List.Tot.hd l2);
    let i = !pi;
    let x = S.op_Array_Access c.s i;
    Trade.rewrite_with_trade (r1 _ _) (r1 x y);
    Trade.trans_hyp_l (r1 x y) _ _ _;
    with l1 . assert (GR.pts_to pl1 l1);
    let res = i1 x out out_count out_size (List.Tot.append l (ps.ag_serializer l1));
    with w . assert (pts_to out w);
    S.pts_to_len c.s;
    ag_serializable_zero_or_more_append ps1 l1 l2;
    if (res) {
      ag_serializable_zero_or_more_append ps1 l1 [Ghost.reveal y];
      let i' = SZ.add i 1sz;
      pi := i';
      let l1' = Ghost.hide (List.Tot.append l1 [Ghost.reveal y]);
      GR.op_Colon_Equals pl1 l1';
      Trade.elim_hyp_l (r1 _ _) _ _;
      Trade.trans_hyp_r _ _ _ (rel_slice_of_list r1 false c v);
      with gcount . assert (pts_to out_count gcount);
      with gsize . assert (pts_to out_size gsize);
      impl_serialize_array_group_valid_zero_or_more_true_intro l ps1 l1 y l2' gcount gsize w;
      assert (pure (Seq.equal s2' (Seq.slice s (SZ.v i') (Seq.length s))));
      List.Tot.append_assoc l1 [Ghost.reveal y] l2';
      assert (pure (Ghost.reveal v == List.Tot.append l1' l2'));
      assert (pure (ps.ag_serializable l1'));
      assert (pure (impl_serialize_array_group_valid l ps v (Seq.length w) == (res && impl_serialize_array_group_valid (l `List.Tot.append` ps.ag_serializer l1') ps l2' (Seq.length w))));
      assert (pure (impl_serialize_array_group_post gcount gsize l ps l1' w true));
      ()
    } else {
      Trade.elim _ (SM.seq_list_match s2 l2 r1);
      impl_serialize_array_group_valid_zero_or_more_false_intro l ps1 l1 y l2' (Seq.length w);
      pres := false
    }
  };
  SM.seq_list_match_length r1 _ _;
  Trade.elim _ _;
  GR.free pl1;
  !pres
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_zero_or_more_iterator_t
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
=
  impl_serialize_array_group #_ #_ #_ (ag_spec_zero_or_more ps1) #(array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1)) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1))

#push-options "--print_implicits"

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"] fn 
impl_serialize_array_group_zero_or_more_iterator
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group_zero_or_more_iterator_t #cbor_array_iterator_t cbor_array_iterator_match #t1 #tgt1 #inj1 #ps1 #impl_tgt1 #r1 i1 sq
=
    (c0: array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1))
    (#v: Ghost.erased (list tgt1))
    (out: S.slice U8.t)
    (out_count: R.ref U64.t)
    (out_size: R.ref SZ.t)
    (l: Ghost.erased (list Cbor.cbor))
{
  let ps = Ghost.hide (ag_spec_zero_or_more ps1);
  let mut pc = c0;
  let pl1 : GR.ref (list tgt1) = GR.alloc (Nil #tgt1);
  let mut pres = true;
  Cbor.cbor_det_serialize_list_nil ();
  Trade.refl (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v);
  while (
    let res = !pres;
    if (res) {
      with gc l2 . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc l2);
      let c = !pc;
      rewrite each gc as c;
      let em = cddl_array_iterator_is_empty is_empty impl_tgt1 _ c;
      not em
    } else {
      false
    }
  ) invariant b. exists* l1 c res l2 w count size . (
    GR.pts_to pl1 l1 **
    pts_to pc c **
    rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c l2 **
    pts_to pres res **
    pts_to out w **
    pts_to out_count count **
    pts_to out_size size **
    Trade.trade
      (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c l2)
      (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v)
      **
    pure (
      (res == true ==> Ghost.reveal v == List.Tot.append l1 l2) /\
      ps.ag_serializable l1 /\
      (impl_serialize_array_group_valid l ps v (Seq.length w) == (res && impl_serialize_array_group_valid (l `List.Tot.append` ps.ag_serializer l1) ps l2 (Seq.length w))) /\
      (res == true ==> impl_serialize_array_group_post count size l ps l1 w true) /\
      b == (res && (Cons? l2))
    )
  ) {
    with gc l2 . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc l2);
    let x : impl_tgt1 = cddl_array_iterator_next length share gather truncate impl_tgt1 _ pc;
    with gc' l2' . assert (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) gc' l2');
    let z : Ghost.erased tgt1 = Ghost.hide (List.Tot.hd l2);
    Trade.rewrite_with_trade (dsnd (Iterator.mk_spec r1) _ _) (r1 x z);
    Trade.trans_hyp_l (r1 x z) _ _ _;
    with l1 . assert (GR.pts_to pl1 l1);
    let res = i1 x #z out out_count out_size (List.Tot.append l (ps.ag_serializer l1));
    Trade.elim_hyp_l _ _ _;
    Trade.trans _ _ (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c0 v);
    with w . assert (pts_to out w);
    ag_serializable_zero_or_more_append ps1 l1 l2;
    if (res) {
      ag_serializable_zero_or_more_append ps1 l1 [Ghost.reveal z];
      let l1' = Ghost.hide (List.Tot.append l1 [Ghost.reveal z]);
      GR.op_Colon_Equals pl1 l1';
      with gcount . assert (pts_to out_count gcount);
      with gsize . assert (pts_to out_size gsize);
      impl_serialize_array_group_valid_zero_or_more_true_intro l ps1 l1 z l2' gcount gsize w;
      List.Tot.append_assoc l1 [Ghost.reveal z] l2';
      assert (pure (Ghost.reveal v == List.Tot.append l1' l2'));
      assert (pure (ps.ag_serializable l1'));
      assert (pure (impl_serialize_array_group_valid l ps v (Seq.length w) == (res && impl_serialize_array_group_valid (l `List.Tot.append` ps.ag_serializer l1') ps l2' (Seq.length w))));
      assert (pure (impl_serialize_array_group_post gcount gsize l ps l1' w true));
      ()
    } else {
      impl_serialize_array_group_valid_zero_or_more_false_intro l ps1 l1 z l2' (Seq.length w);
      pres := false
    }
  };
  Trade.elim _ _;
  GR.free pl1;
  !pres
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_either_left
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt1)
    (i2: impl_serialize_array_group ps1 r2)
: impl_serialize_array_group #_ #_ #_ (ps1) #_ (rel_either_left r1 r2)
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
      Trade.rewrite_with_trade (rel_either_left r1 r2 c v) (r1 c1 v);
      let res = i1 c1 out out_count out_size l;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade (rel_either_left r1 r2 c v) (r2 c2 v);
      let res = i2 c2 out out_count out_size l;
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_zero_or_more
  (#cbor_array_iterator_t: Type)
  (#[@@@erasable]cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_zero_or_more ps1) #_ (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)))
= impl_serialize_array_group_either_left
    (impl_serialize_array_group_zero_or_more_slice i1 sq)
    (impl_serialize_array_group_zero_or_more_iterator is_empty length share gather truncate i1 sq)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_one_or_more_slice
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_one_or_more ps1) #_ (rel_slice_of_list r1 false)
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  unfold (rel_slice_of_list r1 false c v);
  S.pts_to_len c.s;
  SM.seq_list_match_length r1 _ _;
  fold (rel_slice_of_list r1 false c v);
  if (S.len c.s = 0sz) {
    false
  } else {
    impl_serialize_array_group_zero_or_more_slice i1 sq c out out_count out_size l
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_one_or_more_iterator_t
  (#cbor_array_iterator_t: Type)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
=
  impl_serialize_array_group #_ #(list tgt1) #_ (ag_spec_one_or_more ps1) #(array_iterator_t impl_tgt1 cbor_array_iterator_match (Iterator.mk_spec r1)) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1))

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_one_or_more_iterator
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group_one_or_more_iterator_t #cbor_array_iterator_t cbor_array_iterator_match #t1 #tgt1 #inj1 #ps1 #impl_tgt1 #r1 i1 sq
=
    (c: _)
    (#v: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let v' : Ghost.erased (list (dfst (Iterator.mk_spec r1))) = v;
  Trade.rewrite_with_trade
    (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c v)
    (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1) c v');
  let em = cddl_array_iterator_is_empty is_empty impl_tgt1 _ c;
  Trade.elim _ _;
  if (em) {
    false
  } else {
    impl_serialize_array_group_zero_or_more_iterator is_empty length share gather truncate i1 sq c out out_count out_size l
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group_one_or_more
  (#cbor_array_iterator_t: Type)
  (#[@@@erasable]cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (sq: squash (
      array_group_is_nonempty t1 /\
      array_group_concat_unique_strong t1 t1
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_one_or_more ps1) #_ (rel_either_left (rel_slice_of_list r1 false) (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec r1)))
= impl_serialize_array_group_either_left
    (impl_serialize_array_group_one_or_more_slice i1 sq)
    (impl_serialize_array_group_one_or_more_iterator is_empty length share gather truncate i1 sq)

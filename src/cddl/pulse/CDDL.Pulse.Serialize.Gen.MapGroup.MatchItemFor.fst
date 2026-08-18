module CDDL.Pulse.Serialize.Gen.MapGroup.MatchItemFor
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
#lang-pulse

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

(* impl_serialize_match_item_for *)

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

#push-options "--z3rlimit 64"

let impl_serialize_match_item_for_insert_pre_helper
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (pe: cbor_parser)
  (l: cbor_map)
  (key: cbor)
  (value: cbor)
  (w0 w1 w2: Seq.seq U8.t)
  (size0: SZ.t) (res1 res2: SZ.t)
: Lemma
  (requires (
    SZ.v size0 <= Seq.length w0 /\
    SZ.v res1 <= Seq.length w1 /\
    SZ.v res2 <= Seq.length w2 /\
    SZ.fits (SZ.v size0 + SZ.v res1) /\
    SZ.fits (SZ.v size0 + SZ.v res1 + SZ.v res2) /\
    p (cbor_map_length l) w0 == Some (l, SZ.v size0) /\
    pe (Seq.slice w1 0 (SZ.v res1)) == Some (key, SZ.v res1) /\
    pe (Seq.slice w2 0 (SZ.v res2)) == Some (value, SZ.v res2)
  ))
  (ensures (
    let size1_n = SZ.v size0 + SZ.v res1 in
    let size2_n = size1_n + SZ.v res2 in
    let v012 = Seq.slice (Seq.append (Seq.slice (Seq.append (Seq.slice w0 0 (SZ.v size0)) w1) 0 size1_n) w2) 0 size2_n in
    SZ.v size0 <= size1_n /\
    size1_n <= Seq.length v012 /\
    p (cbor_map_length l) (Seq.slice v012 0 (SZ.v size0)) == Some (l, SZ.v size0) /\
    pe (Seq.slice v012 (SZ.v size0) size1_n) == Some (key, size1_n - SZ.v size0) /\
    pe (Seq.slice v012 size1_n (Seq.length v012)) == Some (value, Seq.length v012 - size1_n)
  ))
= let size1 = SZ.v size0 + SZ.v res1 in
  let size2 = size1 + SZ.v res2 in
  let w_after_key = Seq.append (Seq.slice w0 0 (SZ.v size0)) w1 in
  let w_after_value = Seq.append (Seq.slice w_after_key 0 size1) w2 in
  let v012 = Seq.slice w_after_value 0 size2 in
  // Prove slice equalities (propositional)
  Seq.lemma_eq_elim (Seq.slice v012 0 (SZ.v size0)) (Seq.slice w0 0 (SZ.v size0));
  Seq.lemma_eq_elim (Seq.slice v012 (SZ.v size0) size1) (Seq.slice w1 0 (SZ.v res1));
  Seq.lemma_eq_elim (Seq.slice v012 size1 (Seq.length v012)) (Seq.slice w2 0 (SZ.v res2));
  // Use prefix property for the map parser
  let y = Seq.slice v012 0 (SZ.v size0) in
  Seq.lemma_eq_elim (Seq.slice w0 0 (SZ.v size0)) (Seq.slice y 0 (SZ.v size0));
  assert (cbor_parse_map_prefix_prop' p (cbor_map_length l) w0 y);
  assert (p (cbor_map_length l) y == Some (l, SZ.v size0))

#pop-options

#push-options "--z3rlimit 128"

let impl_serialize_match_item_for_post_true_helper
  (#minl: (cbor -> nat)) (#maxl: (cbor -> option nat))
  (p: cbor_map_parser minl maxl)
  (cut: bool)
  (key: cbor)
  (#ty: typ) (#tgt: Type) (#inj: bool)
  (pvalue: spec ty tgt inj)
  (l: cbor_map)
  (v: tgt { pvalue.serializable v })
  (count: U64.t)
  (size2: SZ.t)
  (v': Seq.seq U8.t) (rest: Seq.seq U8.t)
: Lemma
  (requires (
    let m' = cbor_map_union l (cbor_map_singleton key (pvalue.serializer v)) in
    cbor_map_length l == U64.v count /\
    U64.v count < pow2 64 - 1 /\
    cbor_serialize_map_insert_post p l key (pvalue.serializer v) true v' /\
    SZ.v size2 == Seq.length v'
  ))
  (ensures (
    let w = Seq.append v' rest in
    impl_serialize_map_group_post p minl maxl (U64.add count 1uL) size2 l (mg_spec_match_item_for cut key pvalue) v w true
  ))
= let s = mg_spec_match_item_for cut key pvalue in
  let m' = cbor_map_union l (cbor_map_singleton key (pvalue.serializer v)) in
  let w = Seq.append v' rest in
  assert (cbor_map_length m' == cbor_map_length l + 1);
  // Prefix property: p (cbor_map_length m') v' == Some (m', Seq.length v') ==> same for w
  Seq.lemma_eq_elim (Seq.slice v' 0 (Seq.length v')) v';
  Seq.lemma_eq_elim (Seq.slice w 0 (Seq.length v')) v';
  assert (cbor_parse_map_prefix_prop' p (cbor_map_length m') v' w);
  assert (p (cbor_map_length m') w == Some (m', SZ.v size2));
  // pre holds
  assert (impl_serialize_map_group_pre p (U64.add count 1uL) size2 m' w);
  // For invalid ==> false: insert returned true means key not defined in l
  assert (~ (cbor_map_defined key l));
  // Explicitly instantiate min_length_prop
  cbor_map_min_length_instantiate p minl (cbor_map_length m') w

#pop-options

// Helper to make max_length facts available. Calls key lemmas that context_pruning would remove.
#push-options "--z3rlimit 128"

let impl_serialize_match_item_for_false_helper
  (#minl: (cbor -> nat)) (#maxl: (cbor -> option nat))
  (p: cbor_map_parser minl maxl)
  (cut: bool) (key: cbor)
  (#ty: typ) (#tgt: Type) (#inj: bool)
  (pvalue: spec ty tgt inj)
  (l: cbor_map) (v: tgt)
  (w: Seq.seq U8.t) (sz: nat)
: Lemma
  (requires (
    p (cbor_map_length l) w == Some (l, sz)
  ))
  (ensures (
    cbor_map_max_length_prop' p maxl (cbor_map_length l) w
  ))
= cbor_map_max_length_instantiate p maxl (cbor_map_length l) w

#pop-options

// Call site 1: insert failed, key already defined in l, so disjoint is false
let impl_serialize_match_item_for_post_false_insert_failed
  (#pe: cbor_parser)
  (#minl: cbor_min_length pe) (#maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
  (cut: bool) (key: cbor)
  (#ty: typ) (#tgt: Type) (#inj: bool)
  (pvalue: spec ty tgt inj)
  (count: U64.t) (size: SZ.t) (l: cbor_map) (v: tgt)
  (w: Seq.seq U8.t)
: Lemma
  (requires cbor_map_defined key l)
  (ensures impl_serialize_map_group_post p minl maxl count size l (mg_spec_match_item_for cut key pvalue) v w false)
= mg_spec_match_item_for_serializer_eq cut key pvalue v;
  if pvalue.serializable v then
    cbor_map_disjoint_defined_false l key (pvalue.serializer v)

#push-options "--z3rlimit 16"

// Call site 2: value serialization returned 0
let impl_serialize_match_item_for_post_false_value_ser_failed
  (#pe: cbor_parser)
  (#minl: cbor_min_length pe) (#maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
  (cut: bool) (key: cbor)
  (#ty: typ) (#tgt: Type) (#inj: bool)
  (pvalue: spec ty tgt inj)
  (count: U64.t) (size: SZ.t) (l: cbor_map) (v: tgt)
  (w: Seq.seq U8.t)
  (szk: SZ.t) (w0 wk wv: Seq.seq U8.t) (res2: SZ.t)
: Lemma
  (requires (
    Seq.length w0 == Seq.length w /\
    impl_serialize_map_group_pre p count size l w0 /\
    SZ.v szk > 0 /\
    SZ.v size + SZ.v szk <= Seq.length w0 /\
    impl_serialize_post minl maxl (spec_literal key) () wk szk /\
    Seq.length wv == Seq.length w0 - SZ.v size - SZ.v szk /\
    SZ.v res2 == 0 /\
    impl_serialize_post minl maxl pvalue v wv res2
  ))
  (ensures impl_serialize_map_group_post p minl maxl count size l (mg_spec_match_item_for cut key pvalue) v w false)
= mg_spec_match_item_for_serializer_eq cut key pvalue v;
  if pvalue.serializable v then begin
    cbor_map_max_length_singleton maxl key (pvalue.serializer v);
    if cbor_map_disjoint_tot l (cbor_map_singleton key (pvalue.serializer v)) then
      cbor_map_max_length_union maxl l (cbor_map_singleton key (pvalue.serializer v))
  end

#pop-options

// Call site 3: key serialization returned 0
let impl_serialize_match_item_for_post_false_key_ser_failed
  (#pe: cbor_parser)
  (#minl: cbor_min_length pe) (#maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
  (cut: bool) (key: cbor)
  (#ty: typ) (#tgt: Type) (#inj: bool)
  (pvalue: spec ty tgt inj)
  (count: U64.t) (size: SZ.t) (l: cbor_map) (v: tgt)
  (w: Seq.seq U8.t)
  (szk: SZ.t) (w0 wk: Seq.seq U8.t)
: Lemma
  (requires (
    Seq.length w0 == Seq.length w /\
    impl_serialize_map_group_pre p count size l w0 /\
    SZ.v szk == 0 /\
    impl_serialize_post minl maxl (spec_literal key) () wk szk /\
    Seq.length wk == Seq.length w0 - SZ.v size
  ))
  (ensures impl_serialize_map_group_post p minl maxl count size l (mg_spec_match_item_for cut key pvalue) v w false)
= mg_spec_match_item_for_serializer_eq cut key pvalue v;
  if pvalue.serializable v then begin
    cbor_map_max_length_singleton maxl key (pvalue.serializer v);
    if cbor_map_disjoint_tot l (cbor_map_singleton key (pvalue.serializer v)) then
      cbor_map_max_length_union maxl l (cbor_map_singleton key (pvalue.serializer v))
  end

// Call site 4: count overflow (count >= pow2 64 - 1)
let impl_serialize_match_item_for_post_false_count_overflow
  (#pe: cbor_parser)
  (#minl: cbor_min_length pe) (#maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
  (cut: bool) (key: cbor)
  (#ty: typ) (#tgt: Type) (#inj: bool)
  (pvalue: spec ty tgt inj)
  (count: U64.t) (size: SZ.t) (l: cbor_map) (v: tgt)
  (w: Seq.seq U8.t)
: Lemma
  (requires (
    U64.v count >= pow2 64 - 1 /\
    cbor_map_length l == U64.v count
  ))
  (ensures impl_serialize_map_group_post p minl maxl count size l (mg_spec_match_item_for cut key pvalue) v w false)
= mg_spec_match_item_for_serializer_eq cut key pvalue v;
  if pvalue.serializable v then
    cbor_map_length_singleton key (pvalue.serializer v)

#push-options "--z3rlimit 512 --split_queries always"

inline_for_extraction
fn impl_serialize_match_item_for
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (insert: cbor_serialize_map_insert_t p pe)
  (#[@@@erasable]key: Ghost.erased cbor)
  (ik: impl_serialize minl maxl (spec_literal key) rel_unit)
  ([@@@erasable]cut: Ghost.erased bool)
  (#[@@@erasable]value: Ghost.erased typ)
  (#[@@@erasable]tvalue: Type0)
  (#[@@@erasable]vinj: Ghost.erased bool)
  (#[@@@erasable]pvalue: Ghost.erased (spec value tvalue vinj))
  (#iv: Type0)
  (#[@@@erasable]r: rel iv tvalue)
  (ivalue: impl_serialize minl maxl pvalue r)
: impl_serialize_map_group p minl maxl #_ #_ #_ #_ (mg_spec_match_item_for cut key pvalue) #_ r
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
    S.pts_to_len out;
    let size0 = !out_size;
    Seq.lemma_split w0 (SZ.v size0);
    let (out0, out1) = S.split out size0;
    fold (rel_unit () ());
    let res1 = ik () out1;
    with w1 . assert (pts_to out1 w1);
    S.pts_to_len out1;
    unfold (rel_unit () ());
    S.join _ _ out;
    S.pts_to_len out;
    if (SZ.gt res1 0sz) {
      let size1 = SZ.add size0 res1;
      let (out01, out2) = S.split out size1;
      let res2 = ivalue c out2;
      with w2 . assert (pts_to out2 w2);
      S.pts_to_len out2;
      S.join _ _ out;
      S.pts_to_len out;
      if (SZ.gt res2 0sz) {
        let size2 = SZ.add size1 res2;
        let (out012, out_rest) = S.split out size2;
        S.pts_to_len out012;
        impl_serialize_match_item_for_insert_pre_helper (Ghost.reveal p) (Ghost.reveal pe) l key (pvalue.serializer (Ghost.reveal v)) w0 w1 w2 size0 res1 res2;
        let res = insert out012 l size0 key size1 (pvalue.serializer (Ghost.reveal v));
        with v' . assert (pts_to out012 v');
        S.pts_to_len out012;
        with rest . assert (pts_to out_rest rest);
        S.join _ _ out;
        if (res) {
          impl_serialize_match_item_for_post_true_helper (Ghost.reveal p) cut key pvalue l v count size2 v' rest;
          out_size := size2;
          out_count := U64.add count 1uL;
          true
        } else {
          with wf . assert (pts_to out wf);
          with cf . assert (pts_to out_count cf);
          with sf . assert (pts_to out_size sf);
          cbor_map_disjoint_defined_false l key (pvalue.serializer (Ghost.reveal v));
          impl_serialize_match_item_for_post_false_insert_failed (Ghost.reveal p) cut key pvalue cf sf l v wf;
          false
        }
      } else {
        with wf . assert (pts_to out wf);
        with cf . assert (pts_to out_count cf);
        with sf . assert (pts_to out_size sf);
        impl_serialize_match_item_for_post_false_value_ser_failed (Ghost.reveal p) cut key pvalue cf sf l v wf res1 w0 w1 w2 res2;
        false
      }
    } else {
      with wf . assert (pts_to out wf);
      with cf . assert (pts_to out_count cf);
      with sf . assert (pts_to out_size sf);
      impl_serialize_match_item_for_post_false_key_ser_failed (Ghost.reveal p) cut key pvalue cf sf l v wf res1 w0 w1;
      false
    }
  } else {
    with wf . assert (pts_to out wf);
    with cf . assert (pts_to out_count cf);
    with sf . assert (pts_to out_size sf);
    impl_serialize_match_item_for_post_false_count_overflow (Ghost.reveal p) cut key pvalue cf sf l v wf;
    false
  }
}

#pop-options

module CDDL.Pulse.Serialize.Gen.MapGroup.Map
#lang-pulse

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

(* impl_det_serialize_map *)

let impl_det_serialize_map_false_helper
  (#t: det_map_group) (#fp: map_constraint) (#tgt: Type0) (#inj: bool)
  (s: mg_spec t fp tgt inj { map_group_footprint t fp })
  (v: tgt)
  (count: U64.t) (size: SZ.t) (w: Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_map_group_post Cbor.cbor_det_parse_map cbor_det_min_length cbor_det_max_length count size cbor_map_empty s v w false
  ))
  (ensures (
    impl_serialize_post cbor_det_min_length cbor_det_max_length (spec_map_group s) v w 0sz
  ))
= if (spec_map_group s).serializable v
  then begin
    cbor_map_det_max_length_eq (s.mg_serializer v);
    Classical.forall_intro (Classical.move_requires Cbor.cbor_det_serialize_map_length_gt_list)
  end

let impl_det_serialize_map_true_helper
  (#t: det_map_group) (#fp: map_constraint) (#tgt: Type0) (#inj: bool)
  (s: mg_spec t fp tgt inj { map_group_footprint t fp })
  (v: tgt)
  (count: U64.t) (size: SZ.t) (w: Seq.seq U8.t)
  (res: SZ.t)
  (w': Seq.seq U8.t)
: Lemma
  (requires (
    impl_serialize_map_group_post Cbor.cbor_det_parse_map cbor_det_min_length cbor_det_max_length count size cbor_map_empty s v w true /\
    cbor_det_serialize_map_postcond (s.mg_serializer v) res w'
  ))
  (ensures (
    impl_serialize_post cbor_det_min_length cbor_det_max_length (spec_map_group s) v w' res
  ))
= if SZ.v res > 0
  then begin
    cbor_det_parse_equiv (Seq.slice w' 0 (SZ.v res)) (Cbor.pack (Cbor.CMap (s.mg_serializer v))) (SZ.v res);
    ()
  end

#push-options "--z3rlimit_factor 16 --fuel 1 --ifuel 1"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_det_serialize_map
   (cbor_det_serialize_map: cbor_det_serialize_map_t)
    (# [@@@erasable] t: Ghost.erased det_map_group)
    (# [@@@erasable] fp: Ghost.erased map_constraint)
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (mg_spec t fp tgt inj) { map_group_footprint t fp })
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_map_group cbor_det_parse_map cbor_det_min_length cbor_det_max_length s r)
: impl_serialize #_ cbor_det_min_length cbor_det_max_length #_ #_ #_ (spec_map_group s) #_ r
=
  (c: _)
  (#v: _)
  (out: _)
{
  let mut pcount = 0uL;
  let mut psize = 0sz;
  Cbor.cbor_det_serialize_map_empty ();
  with w0 . assert (pts_to out w0);
  Cbor.cbor_det_parse_map_equiv 0 w0 cbor_map_empty 0;
  let res = i c out pcount psize cbor_map_empty;
  if (res) {
    let size = !psize;
    let count = !pcount;
    with w . assert (pts_to out w);
    Cbor.cbor_det_parse_map_equiv (U64.v count) w (s.mg_serializer v) (SZ.v size);
    Classical.forall_intro (Classical.move_requires Cbor.cbor_det_serialize_map_length_gt_list);
    let res2 = cbor_det_serialize_map count out (s.mg_serializer v) size;
    with w' . assert (pts_to out w');
    impl_det_serialize_map_true_helper s v count size w res2 w';
    res2
  } else {
    with w . assert (pts_to out w);
    with count . assert (pts_to pcount count);
    with size . assert (pts_to psize size);
    impl_det_serialize_map_false_helper s v count size w;
    0sz
  }
}

#pop-options

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


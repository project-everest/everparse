module CDDL.Pulse.Serialize.Gen.MapGroup.Ext
#lang-pulse

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

(* impl_serialize_map_group_ext *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_ext
  (#p: Ghost.erased bare_cbor_map_parser)
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
    (#[@@@erasable]t: Ghost.erased (det_map_group))
    (# [@@@erasable] fp: Ghost.erased map_constraint)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_map_group p minl maxl ps r)
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
: impl_serialize_map_group p minl maxl #(Ghost.reveal t') #(Ghost.reveal fp') #tgt #inj' (Ghost.reveal ps') #impl_tgt r
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

(* impl_serialize_map_group_ext' *)

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_group_ext'
  #p #minl #maxl #t #fp #tgt #inj #ps #impl_tgt #r i fp' sq
= impl_serialize_map_group_ext i _ ()

module CDDL.Pulse.Serialize.MapGroup
include CDDL.Pulse.Serialize.Base
include CDDL.Pulse.Parse.MapGroup
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest

let impl_serialize_map_group_pre
  (count: U64.t)
  (size: SZ.t)
  (l: cbor_map)
  (w: Seq.seq U8.t)
: Tot prop
= cbor_map_length l == U64.v count /\
  SZ.v size <= Seq.length w /\
  Seq.slice w 0 (SZ.v size) `Seq.equal` Cbor.cbor_det_serialize_map l

let impl_serialize_map_group_valid
  (l: cbor_map)
  (#t: det_map_group)
  (#fp: map_constraint)
  (#tgt: Type0)
  (#inj: bool)
  (s: mg_spec t fp tgt inj)
  (v: tgt)
  (len: nat)
: Tot bool
=   s.mg_serializable v &&
    cbor_map_disjoint_tot l (s.mg_serializer v) &&
    FStar.UInt.fits (cbor_map_length l + cbor_map_length (s.mg_serializer v)) 64 &&
    Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (s.mg_serializer v))) <= len

let impl_serialize_map_group_post
  (count: U64.t)
  (size: SZ.t)
  (l: cbor_map)
  (#t: det_map_group)
  (#fp: map_constraint)
  (#tgt: Type0)
  (#inj: bool)
  (s: mg_spec t fp tgt inj)
  (v: tgt)
  (w: Seq.seq U8.t)
  (res: bool)
: Tot prop
= (res == true <==> impl_serialize_map_group_valid l s v (Seq.length w)) /\
  (res == true ==> (
    impl_serialize_map_group_pre count size (cbor_map_union l (s.mg_serializer v)) w
  ))

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_group
    (#t: det_map_group)
    (#fp: map_constraint)
    (#tgt: Type0)
    (#inj: bool)
    (s: mg_spec t fp tgt inj)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
  (c: impl_tgt) ->
  (#v: Ghost.erased tgt) ->
  (out: S.slice U8.t) ->
  (out_count: R.ref U64.t) ->
  (out_size: R.ref SZ.t) ->
  (l: Ghost.erased (cbor_map)) ->
  stt bool
    (exists* w count size . r c v ** pts_to out w ** pts_to out_count count ** pts_to out_size size **
      pure (impl_serialize_map_group_pre count size l w)
    )
    (fun res -> exists* w count' size' . r c v ** pts_to out w ** pts_to out_count count' ** pts_to out_size size' ** pure (
      impl_serialize_map_group_post count' size' l s v w res
    ))

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map
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

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_ext
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

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_ext'
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

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_nop
  (_: unit)
: impl_serialize_map_group mg_spec_nop rel_unit

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_choice
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

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_zero_or_one
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

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_either_left
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

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_concat
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

inline_for_extraction
val impl_serialize_match_item_for
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

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_zero_or_more
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
    (#[@@@erasable]except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_either_left (rel_slice_of_table key_eq r1 r2) (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2)))

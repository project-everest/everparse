module CBOR.Pulse.Raw.EverParse.Nondet
#lang-pulse
include CBOR.Spec.Raw.Nondet
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Format
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
let impl_equiv_t
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
=
  (l1: S.slice byte) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (raw_data_item)) ->
  stt (option bool)
    (pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_raw_data_item) l2 #p2 gl2 **
      pure (raw_data_item_size gl1 + raw_data_item_size gl2 <= bound)
    )
    (fun res ->
      pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        raw_data_item_size gl1 + raw_data_item_size gl2 <= bound /\
        res == equiv gl1 gl2
      )
    )

inline_for_extraction
fn impl_check_equiv_list
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item))
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 }) -> option bool))
  (impl_equiv: impl_equiv_t (list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2) equiv)
requires
  pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v n2) serialize_raw_data_item) l2 #p2 gl2
returns res: option bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v n2) serialize_raw_data_item) l2 #p2 gl2 **
  pure (
    res == check_equiv_list gl1 gl2 equiv
  )
{
  if (n1 <> n2) {
    Some false
  } else {
    let mut pn = n1;
    let mut pl1 = l1;
    let mut pl2 = l2;
    Trade.refl
      (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1);
    pts_to_serialized_ext_trade
      (serialize_nlist (SZ.v n2) serialize_raw_data_item)
      (serialize_nlist (SZ.v n1) serialize_raw_data_item)
      l2;
    let mut pres = Some true;
    while (
      let res = !pres;
      let n = !pn;
      ((res = Some true) && SZ.gt n 0sz)
    )
    invariant b . exists* res n' l1' l2' gl1' gl2' .
      pts_to pres res **
      pts_to pn n' **
      pts_to pl1 l1' **
      pts_to pl2 l2' **
      pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l1' #p1 gl1' **
      Trade.trade
        (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l1' #p1 gl1')
        (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1) **
      pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l2' #p2 gl2' **
      Trade.trade
        (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l2' #p2 gl2')
        (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l2 #p2 gl2) **
      pure (
        b == ((res = Some true) && SZ.v n' > 0) /\
        list_sum raw_data_item_size gl1' + list_sum raw_data_item_size gl2' <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 /\
        check_equiv_list gl1 gl2 equiv == (if res = Some true then check_equiv_list gl1' gl2' equiv else res)
      )
    {
      let n = !pn;
      let l1' = !pl1;
      with gl1' . assert (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
      nlist_cons_as_nondep_then serialize_raw_data_item (SZ.v n) l1';
      Classical.forall_intro parse_raw_data_item_eq;
      pts_to_serialized_ext_nondep_then_left
        serialize_raw_data_item
        (serialize_synth _ synth_raw_data_item (serialize_dtuple2 serialize_header serialize_content) synth_raw_data_item_recip ())
        (serialize_nlist (SZ.v n - 1) serialize_raw_data_item)
        l1';
      Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
      pts_to_serialized_synth_l2r_nondep_then_left
        (serialize_dtuple2 serialize_header serialize_content)
        synth_raw_data_item
        synth_raw_data_item_recip
        (serialize_nlist (SZ.v n - 1) serialize_raw_data_item)
        l1';
      Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
      with w1 . assert (
        pts_to_serialized (serialize_nondep_then (serialize_dtuple2 serialize_header serialize_content) (serialize_nlist (SZ.v n - 1) serialize_raw_data_item)) l1' #p1 w1
      );
      pts_to_serialized_dtuple2_nondep_then_assoc_l2r
        serialize_header
        serialize_content
        (serialize_nlist (SZ.v n - 1) serialize_raw_data_item)
        l1';
      Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
      let l2' = !pl2;
      with gl2' . assert (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
      nlist_cons_as_nondep_then serialize_raw_data_item (SZ.v n) l2';
      admit ()
    };
    Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1);
    Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l2 #p2 gl2);
    !pres
  }
}

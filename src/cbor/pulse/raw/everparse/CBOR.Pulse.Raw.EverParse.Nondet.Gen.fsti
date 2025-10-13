module CBOR.Pulse.Raw.EverParse.Nondet.Gen
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
let impl_fun_with_invariant_t
  (#t: Type)
  (f: (x1: raw_data_item) -> t)
  (inv: slprop)
=
  (l1: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (raw_data_item)) ->
  stt t
    (inv ** pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1)
    (fun res ->
      inv ** pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1 **
      pure (
        res == f gl1
      )
    )

inline_for_extraction
let impl_equiv_t
  (#t: Type)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item) -> t)
=
  (l1: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (raw_data_item)) ->
  impl_fun_with_invariant_t
    (equiv gl1)
    (pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1)

let option_sz_v (x: option SZ.t) : GTot (option nat) =
  match x with
  | None -> None
  | Some x' -> Some (SZ.v x')

inline_for_extraction
let impl_equiv_hd_t
  (#t: Type)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item) -> t)
=
  (n1: Ghost.erased nat) ->
  (l1: S.slice byte) ->
  (n2: Ghost.erased nat) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (nlist n1 raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (nlist n2 raw_data_item)) ->
  stt t
    (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0
      )
    )
    (fun res ->
pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0 /\
        res == equiv (List.Tot.hd gl1) (List.Tot.hd gl2)
      )
    )

inline_for_extraction
let impl_check_equiv_map_hd_t
  (data_model: (raw_data_item -> raw_data_item -> bool))
=
  (map_bound: option SZ.t) ->
  impl_equiv_hd_t (check_equiv_map data_model (option_sz_v map_bound))

inline_for_extraction
val impl_check_equiv_map_hd_body
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_data_model: impl_equiv_hd_t data_model)
  (impl_check_equiv_map_hd: impl_check_equiv_map_hd_t data_model)
: impl_check_equiv_map_hd_t (Ghost.reveal data_model)

inline_for_extraction
let impl_check_equiv_list_t
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item) -> option bool)
=
  (n1: SZ.t) ->
  (l1: S.slice byte) ->
  (n2: SZ.t) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item)) ->
  stt (option bool)
    (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist (SZ.v n2) serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        SZ.v n1 > 0 /\ SZ.v n2 > 0
      )
    )
    (fun res ->
      pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist (SZ.v n2) serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        SZ.v n1 > 0 /\ SZ.v n2 > 0 /\
        res == check_equiv_list gl1 gl2 equiv
      )
    )

inline_for_extraction
val impl_check_equiv_list_map
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_check_equiv_map_hd: impl_check_equiv_map_hd_t data_model)
  (map_bound: option SZ.t)
: impl_check_equiv_list_t (check_equiv_map data_model (option_sz_v map_bound))

inline_for_extraction
val impl_check_equiv
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (map_bound: option SZ.t)
  (impl_check_equiv_list: impl_check_equiv_list_t (check_equiv_map data_model (option_sz_v map_bound)))
: impl_equiv_t #_ (check_equiv data_model (option_sz_v map_bound))

val impl_check_map_depth
  (bound: SZ.t)
  (n0: SZ.t)
  (l0: S.slice byte)
  (#pm: perm)
  (#gl0: Ghost.erased (nlist (SZ.v n0) raw_data_item))
: stt bool
(requires
  pts_to_serialized (serialize_nlist (SZ.v n0) serialize_raw_data_item) l0 #pm gl0
)
(ensures fun res ->
  pts_to_serialized (serialize_nlist (SZ.v n0) serialize_raw_data_item) l0 #pm gl0 **
  pure (
    res == check_map_depth (SZ.v bound) gl0
  )
)

inline_for_extraction
val impl_check_valid
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (map_bound: option SZ.t)
  (impl_check_equiv: impl_equiv_t #_ (check_equiv data_model (option_sz_v map_bound)))
  (strict_bound_check: bool)
: impl_fun_with_invariant_t #_
    (check_valid data_model (option_sz_v map_bound) strict_bound_check)
    emp

module CBOR.Pulse.Raw.EverParse.Nondet.Gen
include CBOR.Spec.Raw.Nondet
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base

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
    (inv ** PPB.pts_to_parsed parse_raw_data_item l1 #p1 gl1)
    (fun res ->
      inv ** PPB.pts_to_parsed parse_raw_data_item l1 #p1 gl1 **
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
    (PPB.pts_to_parsed parse_raw_data_item l1 #p1 gl1)

let option_sz_v (x: option SZ.t) : GTot (option nat) =
  match x with
  | None -> None
  | Some x' -> Some (SZ.v x')

inline_for_extraction
let impl_equiv_hd_t
  (#t: Type)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item) -> t)
=
  (n1: SZ.t) ->
  (l1: S.slice byte) ->
  (n2: SZ.t) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item)) ->
  stt t
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
      pure (
        SZ.v n1 > 0 /\ SZ.v n2 > 0
      )
    )
    (fun res ->
PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
      pure (
        SZ.v n1 > 0 /\ SZ.v n2 > 0 /\
        res == equiv (List.Tot.hd gl1) (List.Tot.hd gl2)
      )
    )

inline_for_extraction
val impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> option bool))
  (impl_equiv: impl_equiv_t equiv)
  (nl1: SZ.t)
  (l1: S.slice byte)
  (nl2: SZ.t)
  (l2: S.slice byte)
  (#pl1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v nl1) (raw_data_item & raw_data_item)))
  (#pl2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v nl2) (raw_data_item & raw_data_item)))
: stt (option bool)
(requires
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl1) (nondep_then parse_raw_data_item parse_raw_data_item)) l1 #pl1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl2) (nondep_then parse_raw_data_item parse_raw_data_item)) l2 #pl2 gl2
)
(ensures fun res ->
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl1) (nondep_then parse_raw_data_item parse_raw_data_item)) l1 #pl1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl2) (nondep_then parse_raw_data_item parse_raw_data_item)) l2 #pl2 gl2 **
  pure (
    res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv gl1) gl2
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
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2
    )
    (fun res ->
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
      pure (
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
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n0) parse_raw_data_item) l0 #pm gl0
)
(ensures fun res ->
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n0) parse_raw_data_item) l0 #pm gl0 **
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

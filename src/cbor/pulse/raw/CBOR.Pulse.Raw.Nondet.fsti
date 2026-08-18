module CBOR.Pulse.Raw.Nondet
include CBOR.Pulse.API.Nondet.Type
open CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives

module Spec = CBOR.Spec.API.Format
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module SM = Pulse.Lib.SeqMatch.Util

val cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop

inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_nondet_reset_perm (_: unit) : reset_perm_t #_ cbor_nondet_match

val cbor_nondet_share
  (_: unit)
: CBOR.Pulse.API.Base.share_t u#0 u#0 #_ #_ cbor_nondet_match

val cbor_nondet_gather
  (_: unit)
: CBOR.Pulse.API.Base.gather_t u#0 u#0 #_ #_ cbor_nondet_match

val cbor_nondet_validate (_: unit) : cbor_nondet_validate_t

val cbor_nondet_parse_valid (_: unit) : cbor_nondet_parse_valid_t #cbor_nondet_t cbor_nondet_match

val cbor_nondet_parse (_: unit) : cbor_nondet_parse_t #cbor_nondet_t cbor_nondet_match

val cbor_nondet_match_with_size
  (size: nat)
  (p: perm)
  (c: cbor_nondet_t)
  (v: Spec.cbor)
: Tot slprop

val cbor_nondet_match_with_size_intro (_: unit) : ghost_get_size_t #_ cbor_nondet_match cbor_nondet_match_with_size

val cbor_nondet_size (_: unit) : get_size_t #_ cbor_nondet_match_with_size

val cbor_nondet_serialize
  (_: unit)
: cbor_nondet_serialize_t #cbor_nondet_t cbor_nondet_match_with_size

(* Destructors *)

val cbor_nondet_major_type (_: unit) : get_major_type_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_simple_value (_: unit) : read_simple_value_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_simple (_: unit) : elim_simple_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_uint64 (_: unit) : read_uint64_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_int64 (_: unit) : elim_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_string_length (_: unit) : get_string_length_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_string (_: unit) : get_string_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_tagged_tag (_: unit) : get_tagged_tag_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_tagged_payload (_: unit) : get_tagged_payload_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_array_length (_: unit) : get_array_length_t u#0 #_ cbor_nondet_match

val cbor_nondet_array_iterator_match: perm -> cbor_nondet_array_iterator_t -> list Spec.cbor -> slprop

val cbor_nondet_array_iterator_start (_: unit) : array_iterator_start_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t u#0 #_ cbor_nondet_array_iterator_match

inline_for_extraction
val cbor_nondet_array_iterator_length (_: unit) : array_iterator_length_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_next (_: unit) : array_iterator_next_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_truncate (_: unit) : array_iterator_truncate_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_get_array_item (_: unit) : get_array_item_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_map_length (_: unit) : get_map_length_t u#0 #_ cbor_nondet_match

val cbor_nondet_map_iterator_match: perm -> cbor_nondet_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_nondet_map_iterator_start (_: unit) : map_iterator_start_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t u#0 #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_match: perm -> cbor_nondet_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_nondet_map_iterator_next (_: unit) : map_iterator_next_t #_ #_ cbor_nondet_map_entry_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_share
  (_: unit)
: share_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match

val cbor_nondet_map_entry_gather
  (_: unit)
: gather_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match

(* Equality *)

val cbor_nondet_equal
  (x1: cbor_nondet_t)
  (#p1: perm)
  (#v1: Ghost.erased Spec.cbor)
  (x2: cbor_nondet_t)
  (#p2: perm)
  (#v2: Ghost.erased Spec.cbor)
: stt bool
(requires
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2
)
(ensures fun res ->
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2 **
  pure (res == true <==> Ghost.reveal v1 == Ghost.reveal v2)
)

val cbor_nondet_map_get (_: unit)
: map_get_t #_ cbor_nondet_match

(* Constructors *)

val cbor_nondet_mk_simple_value (_: unit) : mk_simple_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_uint64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match Spec.cbor_major_type_uint64

val cbor_nondet_mk_neg_int64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match Spec.cbor_major_type_neg_int64

val cbor_nondet_mk_int64 (_: unit) : mk_signed_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_string (_: unit) : mk_string_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_tagged (_: unit) : mk_tagged_t #_ cbor_nondet_match

val cbor_nondet_mk_array (_: unit) : mk_array_t #_ cbor_nondet_match

val cbor_nondet_mk_map_entry (_: unit) : mk_map_entry_t #_ #_ cbor_nondet_match cbor_nondet_map_entry_match

inline_for_extraction
val dummy_cbor_nondet: cbor_nondet_t

val cbor_nondet_mk_map (_: unit)
: mk_map_gen_t #cbor_nondet_t #cbor_nondet_map_entry_t cbor_nondet_match cbor_nondet_map_entry_match

inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_nondet_map_get_multiple (_: unit) : cbor_map_get_multiple_t #_ cbor_nondet_match

(* SLProp-to-Prop abstraction vehicle to prove the correctness of type abstraction in the Rust API *)

[@@erasable]
noeq type cbor_nondet_case_t =
| CaseInt64
| CaseString
| CaseTagged
| CaseArray
| CaseMap
| CaseSimpleValue

val cbor_nondet_case: cbor_nondet_t -> cbor_nondet_case_t

noextract [@@noextract_to "krml"]
let cbor_nondet_case_correct_post
  (x: cbor_nondet_t)
  (v: Spec.cbor)
: Tot prop
= match cbor_nondet_case x, Spec.unpack v with
  | CaseInt64, Spec.CInt64 _ _
  | CaseString, Spec.CString _ _
  | CaseTagged, Spec.CTagged _ _
  | CaseArray, Spec.CArray _
  | CaseMap, Spec.CMap _
  | CaseSimpleValue, Spec.CSimple _
  -> True
  | _ -> False

val cbor_nondet_case_correct
  (x: cbor_nondet_t)
  (#p: perm)
  (#v: Spec.cbor)
: stt_ghost unit emp_inames
    (cbor_nondet_match p x v)
    (fun _ -> cbor_nondet_match p x v ** pure (cbor_nondet_case_correct_post x v))

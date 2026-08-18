module CBOR.Pulse.API.Nondet.C
include CBOR.Pulse.API.Nondet.Type
open CBOR.Spec.Constants
open CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives

module Spec = CBOR.Spec.API.Format
module SZ = FStar.SizeT
module U8 = FStar.UInt8
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

val cbor_nondet_parse (_: unit) : cbor_nondet_parse_from_arrayptr_t #cbor_nondet_t cbor_nondet_match

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
: cbor_nondet_serialize_to_arrayptr_t #cbor_nondet_t cbor_nondet_match_with_size

(* Destructors *)

val cbor_nondet_major_type (_: unit) : get_major_type_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_simple_value (_: unit) : read_simple_value_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_simple (_: unit) : elim_simple_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_uint64 (_: unit) : read_uint64_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_int64 (_: unit) : read_int64_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_int64 (_: unit) : elim_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_string (_: unit) : get_string_as_arrayptr_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_byte_string (_: unit) : get_string_as_arrayptr_safe_gen_t u#0 (Some cbor_major_type_byte_string) #_ cbor_nondet_match

val cbor_nondet_get_text_string (_: unit) : get_string_as_arrayptr_safe_gen_t u#0 (Some cbor_major_type_text_string) #_ cbor_nondet_match

val cbor_nondet_get_tagged (_: unit) : get_tagged_safe_t #_ cbor_nondet_match

val cbor_nondet_get_array_length (_: unit) : get_array_length_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_array_iterator_match: perm -> cbor_nondet_array_iterator_t -> list Spec.cbor -> slprop

val cbor_nondet_array_iterator_start (_: unit) : array_iterator_start_safe_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_length (_: unit) : array_iterator_length_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_next (_: unit) : array_iterator_next_safe_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_truncate (_: unit) : array_iterator_truncate_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_get_array_item (_: unit) : get_array_item_safe_t #_ cbor_nondet_match

val cbor_nondet_get_map_length (_: unit) : get_map_length_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_map_iterator_match: perm -> cbor_nondet_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_nondet_map_iterator_start (_: unit) : map_iterator_start_safe_t #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t u#0 #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_match: perm -> cbor_nondet_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_nondet_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_iterator_next (_: unit) : map_iterator_next_safe_t #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

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
: map_get_by_ref_safe_t #_ cbor_nondet_match

(* Constructors *)

val cbor_nondet_mk_simple_value (_: unit) : mk_simple_safe_t #_ cbor_nondet_match

val cbor_nondet_mk_uint64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match cbor_major_type_uint64

val cbor_nondet_mk_neg_int64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match cbor_major_type_neg_int64

val cbor_nondet_mk_int64 (_: unit) : mk_signed_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_byte_string (_: unit) : mk_string_from_arrayptr_t #_ cbor_nondet_match cbor_major_type_byte_string

val cbor_nondet_mk_text_string (_: unit) : mk_string_from_arrayptr_t #_ cbor_nondet_match cbor_major_type_text_string

val cbor_nondet_mk_tagged (_: unit) : mk_tagged_safe_t #_ cbor_nondet_match

val cbor_nondet_mk_array (_: unit) : mk_array_from_arrayptr_t #_ cbor_nondet_match

val cbor_nondet_mk_map_entry (_: unit) : mk_map_entry_t #_ #_ cbor_nondet_match cbor_nondet_map_entry_match

val cbor_nondet_mk_map (_: unit)
: mk_map_from_arrayptr_safe_t #cbor_nondet_t #cbor_nondet_map_entry_t cbor_nondet_match cbor_nondet_map_entry_match

type cbor_nondet_map_get_multiple_entry_t = cbor_map_get_multiple_entry_t cbor_nondet_t

val cbor_nondet_map_get_multiple (_: unit) : cbor_map_get_multiple_as_arrayptr_t #_ cbor_nondet_match cbor_nondet_map_get_multiple_entry_t

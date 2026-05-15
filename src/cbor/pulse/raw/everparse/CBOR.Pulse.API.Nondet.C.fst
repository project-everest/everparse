module CBOR.Pulse.API.Nondet.C
#lang-pulse

(* Implementation of CBOR.Pulse.API.Nondet.C using
   CBOR.Pulse.API.Nondet.Common, which provides slice-based helpers.
   This module wraps those helpers with the ArrayPtr-based combinators
   from CBOR.Pulse.API.Base.

   Re-exports of Common functions are written as direct aliases
   ([let f = Common.f] instead of [let f () = Common.f ()]) so that
   Karamel does not see top-level partial applications (which would
   trigger Warning 16). *)

friend CBOR.Pulse.API.Nondet.Type
friend CBOR.Pulse.API.Nondet.Common

module Common = CBOR.Pulse.API.Nondet.Common

(* ======== Match relation and basic ops ======== *)

[@@pulse_unfold]
let cbor_nondet_match = Common.cbor_nondet_match

let cbor_nondet_reset_perm = Common.cbor_nondet_reset_perm

let cbor_nondet_share = Common.cbor_nondet_share

let cbor_nondet_gather = Common.cbor_nondet_gather

(* ======== Parse / size / serialize ======== *)

let cbor_nondet_parse () =
  cbor_nondet_parse_from_arrayptr (Common.cbor_nondet_validate ()) (Common.cbor_nondet_parse_valid ())

[@@pulse_unfold]
let cbor_nondet_match_with_size = Common.cbor_nondet_match_with_size

let cbor_nondet_match_with_size_intro = Common.cbor_nondet_match_with_size_intro

let cbor_nondet_size = Common.cbor_nondet_size

let cbor_nondet_serialize () =
  cbor_nondet_serialize_to_arrayptr (Common.cbor_nondet_serialize_inner ())

(* ======== Destructors ======== *)

let cbor_nondet_major_type = Common.cbor_nondet_major_type

let cbor_nondet_read_simple_value = Common.cbor_nondet_read_simple_value

let cbor_nondet_elim_simple = Common.cbor_nondet_elim_simple

let cbor_nondet_read_uint64 = Common.cbor_nondet_read_uint64

let cbor_nondet_read_int64 = Common.cbor_nondet_read_int64

let cbor_nondet_elim_int64 = Common.cbor_nondet_elim_int64

let cbor_nondet_get_string () =
  get_string_as_arrayptr_safe (Common.cbor_nondet_major_type ())
    (Common.cbor_nondet_get_string_length ())
    (get_string_as_arrayptr (Common.cbor_nondet_get_string_unsafe ()))

let cbor_nondet_get_byte_string () =
  get_string_as_arrayptr_safe_gen (Common.cbor_nondet_major_type ()) (cbor_nondet_get_string ()) cbor_major_type_byte_string

let cbor_nondet_get_text_string () =
  get_string_as_arrayptr_safe_gen (Common.cbor_nondet_major_type ()) (cbor_nondet_get_string ()) cbor_major_type_text_string

let cbor_nondet_get_tagged = Common.cbor_nondet_get_tagged

let cbor_nondet_get_array_length = Common.cbor_nondet_get_array_length

[@@pulse_unfold]
let cbor_nondet_array_iterator_match = Common.cbor_nondet_array_iterator_match

let cbor_nondet_array_iterator_start = Common.cbor_nondet_array_iterator_start

let cbor_nondet_array_iterator_is_empty = Common.cbor_nondet_array_iterator_is_empty

let cbor_nondet_array_iterator_length = Common.cbor_nondet_array_iterator_length

let cbor_nondet_array_iterator_next = Common.cbor_nondet_array_iterator_next

let cbor_nondet_array_iterator_truncate = Common.cbor_nondet_array_iterator_truncate

let cbor_nondet_array_iterator_share = Common.cbor_nondet_array_iterator_share

let cbor_nondet_array_iterator_gather = Common.cbor_nondet_array_iterator_gather

let cbor_nondet_get_array_item = Common.cbor_nondet_get_array_item

let cbor_nondet_get_map_length = Common.cbor_nondet_get_map_length

[@@pulse_unfold]
let cbor_nondet_map_iterator_match = Common.cbor_nondet_map_iterator_match

let cbor_nondet_map_iterator_start = Common.cbor_nondet_map_iterator_start

let cbor_nondet_map_iterator_is_empty = Common.cbor_nondet_map_iterator_is_empty

[@@pulse_unfold]
let cbor_nondet_map_entry_match = Common.cbor_nondet_map_entry_match

let cbor_nondet_map_entry_key = Common.cbor_nondet_map_entry_key

let cbor_nondet_map_entry_value = Common.cbor_nondet_map_entry_value

let cbor_nondet_map_iterator_next = Common.cbor_nondet_map_iterator_next

let cbor_nondet_map_iterator_share = Common.cbor_nondet_map_iterator_share

let cbor_nondet_map_iterator_gather = Common.cbor_nondet_map_iterator_gather

let cbor_nondet_map_entry_share = Common.cbor_nondet_map_entry_share

let cbor_nondet_map_entry_gather = Common.cbor_nondet_map_entry_gather

(* ======== Equality ======== *)

let cbor_nondet_equal = Common.cbor_nondet_equal

let cbor_nondet_map_get = Common.cbor_nondet_map_get

(* ======== Constructors ======== *)

let cbor_nondet_mk_simple_value = Common.cbor_nondet_mk_simple_value

let cbor_nondet_mk_uint64 = Common.cbor_nondet_mk_uint64

let cbor_nondet_mk_neg_int64 = Common.cbor_nondet_mk_neg_int64

let cbor_nondet_mk_int64 = Common.cbor_nondet_mk_int64

let cbor_nondet_mk_byte_string () =
  mk_string_from_arrayptr (Common.cbor_nondet_mk_string ()) cbor_major_type_byte_string

let cbor_nondet_mk_text_string () =
  mk_string_from_arrayptr (Common.cbor_nondet_mk_string ()) cbor_major_type_text_string

let cbor_nondet_mk_tagged = Common.cbor_nondet_mk_tagged

let cbor_nondet_mk_array () =
  mk_array_from_arrayptr (Common.cbor_nondet_mk_array_inner ())

let cbor_nondet_mk_map_entry = Common.cbor_nondet_mk_map_entry

let cbor_nondet_mk_map () =
  cbor_mk_map_from_arrayptr_safe (Common.cbor_nondet_mk_map_gen ())

let cbor_nondet_map_get_multiple () =
  cbor_map_get_multiple_as_arrayptr cbor_nondet_map_get_multiple_entry_t
    (Common.cbor_nondet_major_type ()) (Common.cbor_nondet_map_get_multiple_inner ())

module CBOR.Pulse.API.Nondet.C
#lang-pulse

(* Implementation of CBOR.Pulse.API.Nondet.C using
   CBOR.Pulse.API.Nondet.Common, which provides slice-based helpers.
   This module wraps those helpers with the ArrayPtr-based combinators
   from CBOR.Pulse.API.Base.

   Re-exports of Common functions are written in one of three forms:

   1. Direct aliases (`let f = Common.f`) for ghost functions, for
      `inline_for_extraction noextract` helpers, and for the slprop
      match-relation definitions (kept compatible with the abstract
      `val` in the .fsti).

   2. Explicit eta-expansion (`let f () x ... #p ... = Common.f () x ... #p ...`)
      for operations whose `*_t` signature uses the match relation
      directly (so Pulse can unfold the alias via [@@pulse_unfold]).
      Karamel then emits proper top-level function declarations in
      the extracted .h, not values of function-pointer type.

   3. Reconstruction via `inline_for_extraction noextract` `*_safe`
      combinators from CBOR.Pulse.API.Base for the remaining
      operations whose post-condition wraps the match relation
      inside another function (e.g. `get_tagged_safe_post vmatch …`).
      The combinator is inlined by Karamel, producing a proper
      function body. The lower-level helpers are taken from Common
      via `friend Common`. *)

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

let cbor_nondet_size () x bound #p #x' #v =
  Common.cbor_nondet_size () x bound #p #x' #v

let cbor_nondet_serialize () =
  cbor_nondet_serialize_to_arrayptr (Common.cbor_nondet_serialize_inner ())

(* ======== Destructors ======== *)

let cbor_nondet_major_type () x #p #y =
  Common.cbor_nondet_major_type () x #p #y

let cbor_nondet_read_simple_value () x dest #p #y #vdest =
  Common.cbor_nondet_read_simple_value () x dest #p #y #vdest

let cbor_nondet_elim_simple = Common.cbor_nondet_elim_simple

let cbor_nondet_read_uint64 () x dest #p #y #vdest =
  Common.cbor_nondet_read_uint64 () x dest #p #y #vdest

let cbor_nondet_read_int64 () x dest #p #y #vdest =
  Common.cbor_nondet_read_int64 () x dest #p #y #vdest

let cbor_nondet_elim_int64 = Common.cbor_nondet_elim_int64

let cbor_nondet_get_string () =
  get_string_as_arrayptr_safe (Common.cbor_nondet_major_type ())
    (Common.cbor_nondet_get_string_length ())
    (get_string_as_arrayptr (Common.cbor_nondet_get_string_unsafe ()))

let cbor_nondet_get_byte_string () =
  get_string_as_arrayptr_safe_gen (Common.cbor_nondet_major_type ()) (cbor_nondet_get_string ()) cbor_major_type_byte_string

let cbor_nondet_get_text_string () =
  get_string_as_arrayptr_safe_gen (Common.cbor_nondet_major_type ()) (cbor_nondet_get_string ()) cbor_major_type_text_string

let cbor_nondet_get_tagged () =
  get_tagged_safe (Common.cbor_nondet_major_type ())
    (Common.cbor_nondet_get_tagged_tag ())
    (Common.cbor_nondet_get_tagged_payload ())

let cbor_nondet_get_array_length () x dest #p #y #vdest =
  Common.cbor_nondet_get_array_length () x dest #p #y #vdest

[@@pulse_unfold]
let cbor_nondet_array_iterator_match = Common.cbor_nondet_array_iterator_match

let cbor_nondet_array_iterator_start () =
  array_iterator_start_safe (Common.cbor_nondet_major_type ())
    (Common.cbor_nondet_array_iterator_start_unsafe ())

let cbor_nondet_array_iterator_is_empty () x #p #y =
  Common.cbor_nondet_array_iterator_is_empty () x #p #y

let cbor_nondet_array_iterator_length () x #p #y =
  Common.cbor_nondet_array_iterator_length () x #p #y

let cbor_nondet_array_iterator_next () =
  array_iterator_next_safe (cbor_nondet_array_iterator_is_empty ())
    (Common.cbor_nondet_array_iterator_next_unsafe ())

let cbor_nondet_array_iterator_truncate () x len #p #y =
  Common.cbor_nondet_array_iterator_truncate () x len #p #y

let cbor_nondet_array_iterator_share = Common.cbor_nondet_array_iterator_share

let cbor_nondet_array_iterator_gather = Common.cbor_nondet_array_iterator_gather

let cbor_nondet_get_array_item () =
  get_array_item_safe (Common.cbor_nondet_major_type ())
    (Common.cbor_nondet_get_array_length_unsafe ())
    (Common.cbor_nondet_get_array_item_unsafe ())

let cbor_nondet_get_map_length () x dest #p #y #vdest =
  Common.cbor_nondet_get_map_length () x dest #p #y #vdest

[@@pulse_unfold]
let cbor_nondet_map_iterator_match = Common.cbor_nondet_map_iterator_match

let cbor_nondet_map_iterator_start () =
  map_iterator_start_safe (Common.cbor_nondet_major_type ())
    (Common.cbor_nondet_map_iterator_start_unsafe ())

let cbor_nondet_map_iterator_is_empty () x #p #y =
  Common.cbor_nondet_map_iterator_is_empty () x #p #y

[@@pulse_unfold]
let cbor_nondet_map_entry_match = Common.cbor_nondet_map_entry_match

let cbor_nondet_map_entry_key () x #p #v2 =
  Common.cbor_nondet_map_entry_key () x #p #v2

let cbor_nondet_map_entry_value () x #p #v2 =
  Common.cbor_nondet_map_entry_value () x #p #v2

let cbor_nondet_map_iterator_next () =
  map_iterator_next_safe (cbor_nondet_map_iterator_is_empty ())
    (Common.cbor_nondet_map_iterator_next_unsafe ())
    (Common.cbor_nondet_map_entry_share_priv ())
    (Common.cbor_nondet_map_entry_gather_priv ())
    (cbor_nondet_map_entry_key ())
    (cbor_nondet_map_entry_value ())

let cbor_nondet_map_iterator_share = Common.cbor_nondet_map_iterator_share

let cbor_nondet_map_iterator_gather = Common.cbor_nondet_map_iterator_gather

let cbor_nondet_map_entry_share = Common.cbor_nondet_map_entry_share

let cbor_nondet_map_entry_gather = Common.cbor_nondet_map_entry_gather

(* ======== Equality ======== *)

let cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2 =
  Common.cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2

let cbor_nondet_map_get () =
  map_get_by_ref_safe (Common.cbor_nondet_major_type ())
    (Common.cbor_nondet_map_get_by_ref ())

(* ======== Constructors ======== *)

let cbor_nondet_mk_simple_value () =
  mk_simple_safe (Common.cbor_nondet_mk_simple_value_unsafe ())

let cbor_nondet_mk_uint64 () v =
  Common.cbor_nondet_mk_uint64 () v

let cbor_nondet_mk_neg_int64 () v =
  Common.cbor_nondet_mk_neg_int64 () v

let cbor_nondet_mk_int64 () v =
  Common.cbor_nondet_mk_int64 () v

let cbor_nondet_mk_byte_string () =
  mk_string_from_arrayptr (Common.cbor_nondet_mk_string ()) cbor_major_type_byte_string

let cbor_nondet_mk_text_string () =
  mk_string_from_arrayptr (Common.cbor_nondet_mk_string ()) cbor_major_type_text_string

let cbor_nondet_mk_tagged () =
  mk_tagged_safe (Common.cbor_nondet_mk_tagged_unsafe ())

let cbor_nondet_mk_array () =
  mk_array_from_arrayptr (Common.cbor_nondet_mk_array_inner ())

let cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv =
  Common.cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv

let cbor_nondet_mk_map () =
  cbor_mk_map_from_arrayptr_safe (Common.cbor_nondet_mk_map_gen ())

let cbor_nondet_map_get_multiple () =
  cbor_map_get_multiple_as_arrayptr cbor_nondet_map_get_multiple_entry_t
    (Common.cbor_nondet_major_type ()) (Common.cbor_nondet_map_get_multiple_inner ())

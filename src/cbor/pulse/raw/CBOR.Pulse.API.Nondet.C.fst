module CBOR.Pulse.API.Nondet.C
#lang-pulse
module Rust = CBOR.Pulse.API.Nondet.Rust

[@@pulse_unfold]
let cbor_nondet_match = Rust.cbor_nondet_match

let cbor_nondet_reset_perm () = Rust.cbor_nondet_reset_perm ()

let cbor_nondet_share = Rust.cbor_nondet_share

let cbor_nondet_gather = Rust.cbor_nondet_gather

let cbor_nondet_parse () = cbor_nondet_parse_from_arrayptr (Rust.cbor_nondet_validate ()) (Rust.cbor_nondet_parse_valid ())

let cbor_nondet_match_with_size = Rust.cbor_nondet_match_with_size

let cbor_nondet_match_with_size_intro () = Rust.cbor_nondet_match_with_size_intro ()

let cbor_nondet_size () x bound #p #x' #v = Rust.cbor_nondet_size () x bound #p #x' #v

let cbor_nondet_serialize () = cbor_nondet_serialize_to_arrayptr (Rust.cbor_nondet_serialize ())

let cbor_nondet_major_type () x #p #y = Rust.cbor_nondet_major_type () x #p #y

let cbor_nondet_read_simple_value () = read_simple_value_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_simple_value ())

let cbor_nondet_elim_simple () = Rust.cbor_nondet_elim_simple ()

let cbor_nondet_read_uint64 () = read_uint64_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_uint64 ())

let cbor_nondet_read_int64 () = read_int64_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_uint64 ())

let cbor_nondet_elim_int64 () = Rust.cbor_nondet_elim_int64 ()

let cbor_nondet_get_string () = get_string_as_arrayptr_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_string_length ()) (get_string_as_arrayptr (Rust.cbor_nondet_get_string ()))

let cbor_nondet_get_byte_string () = get_string_as_arrayptr_safe_gen (cbor_nondet_major_type ()) (cbor_nondet_get_string ()) _

let cbor_nondet_get_text_string () = get_string_as_arrayptr_safe_gen (cbor_nondet_major_type ()) (cbor_nondet_get_string ()) _

let cbor_nondet_get_tagged () = get_tagged_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_tagged_tag ()) (Rust.cbor_nondet_get_tagged_payload ())

let cbor_nondet_get_array_length () = get_array_length_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_array_length ())

let cbor_nondet_array_iterator_match = Rust.cbor_nondet_array_iterator_match

let cbor_nondet_array_iterator_start () = array_iterator_start_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_array_iterator_start ())

let cbor_nondet_array_iterator_is_empty () x #p #y = Rust.cbor_nondet_array_iterator_is_empty () x #p #y

let cbor_nondet_array_iterator_length () x #p #y = Rust.cbor_nondet_array_iterator_length () x #p #y

let cbor_nondet_array_iterator_next () = array_iterator_next_safe (cbor_nondet_array_iterator_is_empty ()) (Rust.cbor_nondet_array_iterator_next ())

let cbor_nondet_array_iterator_truncate () x len #p #y = Rust.cbor_nondet_array_iterator_truncate () x len #p #y

let cbor_nondet_array_iterator_share () = Rust.cbor_nondet_array_iterator_share ()

let cbor_nondet_array_iterator_gather () = Rust.cbor_nondet_array_iterator_gather ()

let cbor_nondet_get_array_item () = get_array_item_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_array_length ()) (Rust.cbor_nondet_get_array_item ())

let cbor_nondet_get_map_length () = get_map_length_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_map_length ())

let cbor_nondet_map_iterator_match = Rust.cbor_nondet_map_iterator_match

let cbor_nondet_map_iterator_start () = map_iterator_start_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_map_iterator_start ())

let cbor_nondet_map_iterator_is_empty () x #p #y = Rust.cbor_nondet_map_iterator_is_empty () x #p #y

let cbor_nondet_map_entry_match = Rust.cbor_nondet_map_entry_match

let cbor_nondet_map_entry_key () x #p #y = Rust.cbor_nondet_map_entry_key () x #p #y

let cbor_nondet_map_entry_value () x #p #y = Rust.cbor_nondet_map_entry_value () x #p #y

let cbor_nondet_map_iterator_next () = map_iterator_next_safe (cbor_nondet_map_iterator_is_empty ()) (Rust.cbor_nondet_map_iterator_next ()) (Rust.cbor_nondet_map_entry_share ()) (Rust.cbor_nondet_map_entry_gather ()) (cbor_nondet_map_entry_key ()) (cbor_nondet_map_entry_value ())

let cbor_nondet_map_iterator_share () = Rust.cbor_nondet_map_iterator_share ()

let cbor_nondet_map_iterator_gather () = Rust.cbor_nondet_map_iterator_gather ()

let cbor_nondet_map_entry_share () = Rust.cbor_nondet_map_entry_share ()

let cbor_nondet_map_entry_gather () = Rust.cbor_nondet_map_entry_gather ()

let cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2 = Rust.cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2

let cbor_nondet_map_get () = map_get_by_ref_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_map_get ())

let cbor_nondet_mk_simple_value () = mk_simple_safe (Rust.cbor_nondet_mk_simple_value ())

let cbor_nondet_mk_uint64 () v = Rust.cbor_nondet_mk_int64 () cbor_major_type_uint64 v

let cbor_nondet_mk_neg_int64 () v = Rust.cbor_nondet_mk_int64 () cbor_major_type_neg_int64 v

let cbor_nondet_mk_int64 () = mk_signed_int64 (Rust.cbor_nondet_mk_int64 ())

let cbor_nondet_mk_byte_string () = mk_string_from_arrayptr (Rust.cbor_nondet_mk_string ()) cbor_major_type_byte_string

let cbor_nondet_mk_text_string () = mk_string_from_arrayptr (Rust.cbor_nondet_mk_string ()) cbor_major_type_text_string

let cbor_nondet_mk_tagged () = mk_tagged_safe (Rust.cbor_nondet_mk_tagged ())

let cbor_nondet_mk_array () = mk_array_from_arrayptr (Rust.cbor_nondet_mk_array ())

let cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv = Rust.cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv

let cbor_nondet_mk_map () = cbor_mk_map_from_arrayptr_safe (Rust.cbor_nondet_mk_map_gen ())

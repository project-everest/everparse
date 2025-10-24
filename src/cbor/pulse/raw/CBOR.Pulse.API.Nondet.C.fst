module CBOR.Pulse.API.Nondet.C
#lang-pulse
module Rust = CBOR.Pulse.API.Nondet.Rust

[@@pulse_unfold]
let cbor_nondet_match = Rust.cbor_nondet_match

let cbor_nondet_reset_perm () = Rust.cbor_nondet_reset_perm ()

let cbor_nondet_share = Rust.cbor_nondet_share

let cbor_nondet_gather = Rust.cbor_nondet_gather

let cbor_nondet_validate () = cbor_nondet_validate_from_arrayptr (Rust.cbor_nondet_validate ())

let cbor_nondet_parse_valid () = cbor_nondet_parse_valid_from_arrayptr (Rust.cbor_nondet_parse_valid ())

let cbor_nondet_serialize () = cbor_nondet_serialize_to_arrayptr (Rust.cbor_nondet_serialize ())

let cbor_nondet_major_type () x #p #y = Rust.cbor_nondet_major_type () x #p #y

let cbor_nondet_read_simple_value () x #p #y = Rust.cbor_nondet_read_simple_value () x #p #y

let cbor_nondet_elim_simple () = Rust.cbor_nondet_elim_simple ()

let cbor_nondet_read_uint64 () x #p #y = Rust.cbor_nondet_read_uint64 () x #p #y

let cbor_nondet_elim_int64 () = Rust.cbor_nondet_elim_int64 ()

let cbor_nondet_get_string_length () x #p #y = Rust.cbor_nondet_get_string_length () x #p #y

let cbor_nondet_get_string () = get_string_as_arrayptr (Rust.cbor_nondet_get_string ())

let cbor_nondet_get_tagged_tag () x #p #y = Rust.cbor_nondet_get_tagged_tag () x #p #y

let cbor_nondet_get_tagged_payload () x #p #y = Rust.cbor_nondet_get_tagged_payload () x #p #y

let cbor_nondet_get_array_length () x #p #y = Rust.cbor_nondet_get_array_length () x #p #y

let cbor_nondet_array_iterator_match = Rust.cbor_nondet_array_iterator_match

let cbor_nondet_array_iterator_start () x #p #y = Rust.cbor_nondet_array_iterator_start () x #p #y

let cbor_nondet_array_iterator_is_empty () x #p #y = Rust.cbor_nondet_array_iterator_is_empty () x #p #y

let cbor_nondet_array_iterator_length () x #p #y = Rust.cbor_nondet_array_iterator_length () x #p #y

let cbor_nondet_array_iterator_next () x #y #py #z = Rust.cbor_nondet_array_iterator_next () x #y #py #z

let cbor_nondet_array_iterator_truncate () x len #p #y = Rust.cbor_nondet_array_iterator_truncate () x len #p #y

let cbor_nondet_array_iterator_share () = Rust.cbor_nondet_array_iterator_share ()

let cbor_nondet_array_iterator_gather () = Rust.cbor_nondet_array_iterator_gather ()

let cbor_nondet_get_array_item () x i #p #y = Rust.cbor_nondet_get_array_item () x i #p #y

let cbor_nondet_get_map_length () x #p #y = Rust.cbor_nondet_get_map_length () x #p #y

let cbor_nondet_map_iterator_match = Rust.cbor_nondet_map_iterator_match

let cbor_nondet_map_iterator_start () x #p #y = Rust.cbor_nondet_map_iterator_start () x #p #y

let cbor_nondet_map_iterator_is_empty () x #p #y = Rust.cbor_nondet_map_iterator_is_empty () x #p #y

let cbor_nondet_map_entry_match = Rust.cbor_nondet_map_entry_match

let cbor_nondet_map_iterator_next () x #y #py #z = Rust.cbor_nondet_map_iterator_next () x #y #py #z

let cbor_nondet_map_iterator_share () = Rust.cbor_nondet_map_iterator_share ()

let cbor_nondet_map_iterator_gather () = Rust.cbor_nondet_map_iterator_gather ()

let cbor_nondet_map_entry_key () x #p #y = Rust.cbor_nondet_map_entry_key () x #p #y

let cbor_nondet_map_entry_value () x #p #y = Rust.cbor_nondet_map_entry_value () x #p #y

let cbor_nondet_map_entry_share () = Rust.cbor_nondet_map_entry_share ()

let cbor_nondet_map_entry_gather () = Rust.cbor_nondet_map_entry_gather ()

let cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2 = Rust.cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2

fn cbor_nondet_map_get (_: unit) : map_get_by_ref_t #_ cbor_nondet_match =
  (x: _) (k: _) (dest: _) (#px: _) (#vx: _) (#pk: _) (#vk: _) (#vdest0: _)
{
  Rust.cbor_nondet_map_get () x k dest
}

let cbor_nondet_mk_simple_value () v = Rust.cbor_nondet_mk_simple_value () v

let cbor_nondet_mk_int64 () ty v = Rust.cbor_nondet_mk_int64 () ty v

let cbor_nondet_mk_string () = mk_string_from_arrayptr (Rust.cbor_nondet_mk_string ())

let cbor_nondet_mk_tagged () tag r #pr #v #pv #v' = Rust.cbor_nondet_mk_tagged () tag r #pr #v #pv #v'

let cbor_nondet_mk_array () = mk_array_from_arrayptr (Rust.cbor_nondet_mk_array ())

let cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv = Rust.cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv

let cbor_nondet_mk_map_gen () = cbor_mk_map_from_arrayptr_safe (Rust.cbor_nondet_mk_map_gen ())

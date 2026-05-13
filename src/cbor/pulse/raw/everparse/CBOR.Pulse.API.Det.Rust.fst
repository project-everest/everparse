module CBOR.Pulse.API.Det.Rust
#lang-pulse

(* STUB: this .fst file is a placeholder for the eventual implementation
   of CBOR.Pulse.API.Det.Rust.fsti against the new EverParse stack.

   The Det.Rust API is structurally very different from Det.C: it uses
   owned types (cbordet, cbor_det_array, cbor_det_map, ...) plus a
   destructor (cbor_det_destruct) returning a sum-type view. Implementing
   this on top of CBOR.Pulse.Raw.EverParse.* requires:

   - Concrete representations for cbordet, cbor_det_array, cbor_det_map,
     cbor_det_array_iterator_t, cbor_det_map_iterator_t, cbor_det_map_entry,
     cbor_det_view (probably wrapping the corresponding Det.Type/Det.Impl
     types with refinements like CaseArray? / CaseMap?).

   - A cbor_det_destruct primitive that case-splits on cbor_det_t's
     constructors and produces the cbor_det_view.

   - Implementations of cbor_det_get_array_item, cbor_det_map_get,
     and the full map iterator family (item 9, 10, 12 in the spec
     analysis), all of which are also missing in Det.Impl.

   For this incremental commit, every val is admitted to keep the
   build moving. The legacy reference is in
   src/cbor/pulse/raw/old/CBOR.Pulse.API.Det.Rust.fst (~620 lines)
   delegating to CBOR.Pulse.API.Det.Common (also legacy). *)

module Spec = CBOR.Spec.API.Format
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Base = CBOR.Pulse.API.Base

(* Abstract types: stub them with unit. They will be refined when the
   real implementation lands. *)

let cbordet = unit
let cbor_det_match = admit ()
let cbor_det_reset_perm () = admit ()
let cbor_det_share () = admit ()
let cbor_det_gather () = admit ()
let cbor_det_parse () = admit ()
let cbor_det_size = admit ()
let cbor_det_serialize () = admit ()
let cbor_det_mk_simple_value = admit ()
let cbor_det_mk_int64 = admit ()
let cbor_impl_utf8_correct () = admit ()
let cbor_det_mk_string = admit ()
let cbor_det_mk_tagged = admit ()
let cbor_det_map_entry = unit
let cbor_det_map_entry_match = admit ()
let cbor_det_mk_map_entry = admit ()
let cbor_det_mk_array = admit ()
let cbor_det_mk_map () = admit ()
let cbor_det_equal = admit ()
let cbor_det_major_type () = admit ()
let cbor_det_array = unit
let cbor_det_array_match = admit ()
let cbor_det_map = unit
let cbor_det_map_match = admit ()
let cbor_det_destruct = admit ()
let cbor_det_elim_int64 () = admit ()
let cbor_det_elim_simple_value () = admit ()
let cbor_det_get_array_length = admit ()
let cbor_det_array_iterator_t = unit
let cbor_det_array_iterator_match = admit ()
let cbor_det_array_iterator_start = admit ()
let cbor_det_array_iterator_is_empty = admit ()
let cbor_det_array_iterator_next = admit ()
let cbor_det_array_iterator_share = admit ()
let cbor_det_array_iterator_gather = admit ()
let cbor_det_array_iterator_length = admit ()
let cbor_det_array_iterator_truncate = admit ()
let cbor_det_get_array_item = admit ()
let cbor_det_map_length = admit ()
let cbor_det_map_iterator_t = unit
let cbor_det_map_iterator_match = admit ()
let cbor_det_map_iterator_start = admit ()
let cbor_det_map_iterator_is_empty = admit ()
let cbor_det_map_iterator_next = admit ()
let cbor_det_map_iterator_share = admit ()
let cbor_det_map_iterator_gather = admit ()
let cbor_det_map_entry_key = admit ()
let cbor_det_map_entry_value = admit ()
let cbor_det_map_entry_share = admit ()
let cbor_det_map_entry_gather = admit ()
let cbor_det_map_get = admit ()
let cbor_det_serialize_string = admit ()
let cbor_det_serialize_tag = admit ()
let cbor_det_serialize_array = admit ()
let cbor_det_serialize_map_insert = admit ()
let cbor_det_serialize_map = admit ()
let dummy_cbor_det_t () = ()

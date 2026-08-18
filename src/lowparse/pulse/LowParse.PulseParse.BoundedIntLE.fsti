module LowParse.PulseParse.BoundedIntLE
include LowParse.Spec.BoundedInt

module PPB = LowParse.PulseParse.Base

(* leaf_readers for the little-endian fixed-size integers parse_u16_le / parse_u32_le.
   These are not provided by LowParse.PulseParse.BoundedInt because the underlying
   synth functions of parse_u16_le / parse_u32_le are private to the spec module;
   this module befriends the spec to build them. *)

inline_for_extraction
val read_u16_le : PPB.leaf_reader parse_u16_le

inline_for_extraction
val read_u32_le : PPB.leaf_reader parse_u32_le

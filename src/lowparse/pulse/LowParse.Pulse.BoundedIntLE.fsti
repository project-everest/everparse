module LowParse.Pulse.BoundedIntLE
include LowParse.Spec.BoundedInt
open LowParse.Pulse.Base

(* l2r_leaf_writers for the little-endian fixed-size integers serialize_u16_le /
   serialize_u32_le. These are not provided by LowParse.Pulse.BoundedInt because the
   underlying synth functions of serialize_u16_le / serialize_u32_le are private to
   the spec module; this module befriends the spec to build them.  (An interface is
   required by F* whenever a module uses a `friend` declaration.) *)

inline_for_extraction
val l2r_leaf_write_u16_le : l2r_leaf_writer serialize_u16_le

inline_for_extraction
val l2r_leaf_write_u32_le : l2r_leaf_writer serialize_u32_le

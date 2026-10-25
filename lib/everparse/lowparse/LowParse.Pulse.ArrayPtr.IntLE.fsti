module LowParse.Pulse.ArrayPtr.IntLE
include LowParse.Spec.BoundedInt

module API = LowParse.Pulse.ArrayPtr.Int

(* ArrayPtr leaf readers for the little-endian fixed-size integers
   parse_u16_le / parse_u32_le. As in LowParse.PulseParse.BoundedIntLE, these
   live in their own module because the synth functions underlying
   parse_u16_le / parse_u32_le are private to the spec module, so building the
   readers requires befriending it, which in turn requires an interface. *)

inline_for_extraction
noextract
val read_u16_le : API.leaf_reader parse_u16_le

inline_for_extraction
noextract
val read_u32_le : API.leaf_reader parse_u32_le

module EverParse3d.CAbi.StdInt

module U64 = FStar.UInt64

(* <stdint.h>'s UINT64_MAX. Custard declares any external value that has no
   header (`extern uint64_t UINT64_MAX;`, which breaks on a macro), so name
   EverParseEndianness.h: generated code already includes it, and it includes
   <stdint.h>. *)
[@@CMacro; FStar.Attributes.custard_extern "UINT64_MAX"; FStar.Attributes.custard_c_header "EverParseEndianness.h"]
assume val uint64_max : (x: U64.t { U64.v x == pow2 64 - 1 })

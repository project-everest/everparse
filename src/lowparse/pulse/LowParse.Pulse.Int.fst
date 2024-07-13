module LowParse.Pulse.Int
include LowParse.Spec.Int
include LowParse.Pulse.Base
open LowParse.Pulse.Util

module E = LowParse.Pulse.Endianness
module EI = LowParse.Spec.Endianness.Instances
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice

inline_for_extraction
let validate_u8 : validator tot_parse_u8 =
  validate_total_constant_size tot_parse_u8 1sz

inline_for_extraction
let jump_u8 : jumper tot_parse_u8 =
  jump_constant_size tot_parse_u8 1sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_1 =  (E.mk_be_to_n EI.uint8 1)

inline_for_extraction
```pulse
fn read_u8' (_: unit) : leaf_reader #FStar.UInt8.t #parse_u8_kind #tot_parse_u8 tot_serialize_u8
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased FStar.UInt8.t)
{
  unfold (pts_to_serialized tot_serialize_u8 input #pm v);
  serialize_u8_spec_be v;
  let res = be_to_n_1 input 1sz;
  fold (pts_to_serialized tot_serialize_u8 input #pm v);
  res
}
```

inline_for_extraction
let read_u8 : reader tot_serialize_u8 = reader_of_leaf_reader (read_u8' ())

(*
inline_for_extraction
let validate_and_read_u8 : validate_and_read tot_parse_u8 =
  validate_and_read_intro validate_u8 read_u8
*)

inline_for_extraction
let validate_u16 : validator tot_parse_u16 =
  validate_total_constant_size tot_parse_u16 2sz

inline_for_extraction
let jump_u16 : jumper tot_parse_u16 =
  jump_constant_size tot_parse_u16 2sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_2 = (E.mk_be_to_n EI.uint16 2)

inline_for_extraction
```pulse
fn read_u16' (_: unit) : leaf_reader #FStar.UInt16.t #parse_u16_kind #tot_parse_u16 tot_serialize_u16
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased FStar.UInt16.t)
{
  unfold (pts_to_serialized tot_serialize_u16 input #pm v);
  serialize_u16_spec_be v;
  let res = be_to_n_2 input 2sz;
  fold (pts_to_serialized tot_serialize_u16 input #pm v);
  res
}
```

inline_for_extraction
let read_u16 : reader tot_serialize_u16 = reader_of_leaf_reader (read_u16' ())

(*
inline_for_extraction
let validate_and_read_u16 : validate_and_read tot_parse_u16 =
  validate_and_read_intro validate_u16 read_u16
*)

inline_for_extraction
let validate_u32 : validator tot_parse_u32 =
  validate_total_constant_size tot_parse_u32 4sz

inline_for_extraction
let jump_u32 : jumper tot_parse_u32 =
  jump_constant_size tot_parse_u32 4sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_4 = (E.mk_be_to_n EI.uint32 4)

inline_for_extraction
```pulse
fn read_u32' (_: unit) : leaf_reader #FStar.UInt32.t #parse_u32_kind #tot_parse_u32 tot_serialize_u32
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased FStar.UInt32.t)
{
  unfold (pts_to_serialized tot_serialize_u32 input #pm v);
  serialize_u32_spec_be v;
  let res = be_to_n_4 input 4sz;
  fold (pts_to_serialized tot_serialize_u32 input #pm v);
  res
}
```

inline_for_extraction
let read_u32 : reader tot_serialize_u32 = reader_of_leaf_reader (read_u32' ())

(*
inline_for_extraction
let validate_and_read_u32 : validate_and_read tot_parse_u32 =
  validate_and_read_intro validate_u32 read_u32
*)

inline_for_extraction
let validate_u64 : validator tot_parse_u64 =
  validate_total_constant_size tot_parse_u64 8sz

inline_for_extraction
let jump_u64 : jumper tot_parse_u64 =
  jump_constant_size tot_parse_u64 8sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_8 = (E.mk_be_to_n EI.uint64 8)

inline_for_extraction
```pulse
fn read_u64' (_: unit) : leaf_reader #FStar.UInt64.t #parse_u64_kind #tot_parse_u64 tot_serialize_u64
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased FStar.UInt64.t)
{
  unfold (pts_to_serialized tot_serialize_u64 input #pm v);
  serialize_u64_spec_be v;
  let res = be_to_n_8 input 8sz;
  fold (pts_to_serialized tot_serialize_u64 input #pm v);
  res
}
```

inline_for_extraction
let read_u64 : reader tot_serialize_u64 = reader_of_leaf_reader (read_u64' ())

(*
inline_for_extraction
let validate_and_read_u64 : validate_and_read tot_parse_u64 =
  validate_and_read_intro validate_u64 read_u64
*)

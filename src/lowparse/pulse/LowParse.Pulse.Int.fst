module LowParse.Pulse.Int
#lang-pulse
include LowParse.Spec.Int
include LowParse.Pulse.Base
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade

module E = LowParse.Pulse.Endianness
module EI = LowParse.Spec.Endianness.Instances
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice

inline_for_extraction
let validate_u8 : validator parse_u8 =
  validate_total_constant_size parse_u8 1sz

inline_for_extraction
let jump_u8 : jumper parse_u8 =
  jump_constant_size parse_u8 1sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_1 =  (E.mk_be_to_n EI.uint8 1)

inline_for_extraction
fn read_u8' (_: unit) : leaf_reader #FStar.UInt8.t #parse_u8_kind #parse_u8 serialize_u8
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased FStar.UInt8.t)
{
  unfold (pts_to_serialized serialize_u8 input #pm v);
  serialize_u8_spec_be v;
  let res = be_to_n_1 input 1sz;
  fold (pts_to_serialized serialize_u8 input #pm v);
  res
}

inline_for_extraction
let read_u8 : reader serialize_u8 = reader_of_leaf_reader (read_u8' ())

inline_for_extraction
let size_u8 (#t: Type) (vmatch: t -> FStar.UInt8.t -> slprop) : compute_remaining_size vmatch serialize_u8 =
  compute_remaining_size_constant_size vmatch serialize_u8 1sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let n_to_be_1 =  (E.mk_n_to_be EI.uint8 1)

inline_for_extraction
fn l2r_leaf_write_u8 (_: unit) : l2r_leaf_writer u#0 #FStar.UInt8.t #parse_u8_kind #parse_u8 serialize_u8
= (n: _)
  (x: _)
  (pos: SZ.t)
  (#v: Ghost.erased (Seq.seq byte))
{
  pts_to_len x;
  serialize_u8_spec_be n;
  let pos' = SZ.add pos 1sz;
  n_to_be_1 n x pos';
  pos'
}

inline_for_extraction
let validate_u16 : validator parse_u16 =
  validate_total_constant_size parse_u16 2sz

inline_for_extraction
let jump_u16 : jumper parse_u16 =
  jump_constant_size parse_u16 2sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_2 = (E.mk_be_to_n EI.uint16 2)

inline_for_extraction
fn read_u16' (_: unit) : leaf_reader #FStar.UInt16.t #parse_u16_kind #parse_u16 serialize_u16
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased FStar.UInt16.t)
{
  unfold (pts_to_serialized serialize_u16 input #pm v);
  serialize_u16_spec_be v;
  let res = be_to_n_2 input 2sz;
  fold (pts_to_serialized serialize_u16 input #pm v);
  res
}

inline_for_extraction
let read_u16 : reader serialize_u16 = reader_of_leaf_reader (read_u16' ())

inline_for_extraction
let size_u16 (#t: Type) (vmatch: t -> FStar.UInt16.t -> slprop) : compute_remaining_size vmatch serialize_u16 =
  compute_remaining_size_constant_size vmatch serialize_u16 2sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let n_to_be_2 =  (E.mk_n_to_be EI.uint16 2)

inline_for_extraction
fn l2r_leaf_write_u16 (_: unit) : l2r_leaf_writer u#0 #FStar.UInt16.t #parse_u16_kind #parse_u16 serialize_u16
= (n: _)
  (x: _)
  (pos: SZ.t)
  (#v: Ghost.erased (Seq.seq byte))
{
  pts_to_len x;
  serialize_u16_spec_be n;
  let pos' = SZ.add pos 2sz;
  n_to_be_2 n x pos';
  pos'
}

inline_for_extraction
let validate_u32 : validator parse_u32 =
  validate_total_constant_size parse_u32 4sz

inline_for_extraction
let jump_u32 : jumper parse_u32 =
  jump_constant_size parse_u32 4sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_4 = (E.mk_be_to_n EI.uint32 4)

inline_for_extraction
fn read_u32' (_: unit) : leaf_reader #FStar.UInt32.t #parse_u32_kind #parse_u32 serialize_u32
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased FStar.UInt32.t)
{
  unfold (pts_to_serialized serialize_u32 input #pm v);
  serialize_u32_spec_be v;
  let res = be_to_n_4 input 4sz;
  fold (pts_to_serialized serialize_u32 input #pm v);
  res
}

inline_for_extraction
let read_u32 : reader serialize_u32 = reader_of_leaf_reader (read_u32' ())

inline_for_extraction
let size_u32 (#t: Type) (vmatch: t -> FStar.UInt32.t -> slprop) : compute_remaining_size vmatch serialize_u32 =
  compute_remaining_size_constant_size vmatch serialize_u32 4sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let n_to_be_4 =  (E.mk_n_to_be EI.uint32 4)

inline_for_extraction
fn l2r_leaf_write_u32 (_: unit) : l2r_leaf_writer u#0 #FStar.UInt32.t #parse_u32_kind #parse_u32 serialize_u32
= (n: _)
  (x: _)
  (pos: SZ.t)
  (#v: Ghost.erased (Seq.seq byte))
{
  pts_to_len x;
  serialize_u32_spec_be n;
  let pos' = SZ.add pos 4sz;
  n_to_be_4 n x pos';
  pos'
}

inline_for_extraction
let validate_u64 : validator parse_u64 =
  validate_total_constant_size parse_u64 8sz

inline_for_extraction
let jump_u64 : jumper parse_u64 =
  jump_constant_size parse_u64 8sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_8 = (E.mk_be_to_n EI.uint64 8)

inline_for_extraction
fn read_u64' (_: unit) : leaf_reader #FStar.UInt64.t #parse_u64_kind #parse_u64 serialize_u64
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased FStar.UInt64.t)
{
  unfold (pts_to_serialized serialize_u64 input #pm v);
  serialize_u64_spec_be v;
  let res = be_to_n_8 input 8sz;
  fold (pts_to_serialized serialize_u64 input #pm v);
  res
}

inline_for_extraction
let read_u64 : reader serialize_u64 = reader_of_leaf_reader (read_u64' ())

inline_for_extraction
let size_u64 (#t: Type) (vmatch: t -> FStar.UInt64.t -> slprop) : compute_remaining_size vmatch serialize_u64 =
  compute_remaining_size_constant_size vmatch serialize_u64 8sz

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let n_to_be_8 =  (E.mk_n_to_be EI.uint64 8)

inline_for_extraction
fn l2r_leaf_write_u64 (_: unit) : l2r_leaf_writer u#0 #FStar.UInt64.t #parse_u64_kind #parse_u64 serialize_u64
= (n: _)
  (x: _)
  (pos: SZ.t)
  (#v: Ghost.erased (Seq.seq byte))
{
  pts_to_len x;
  serialize_u64_spec_be n;
  let pos' = SZ.add pos 8sz;
  n_to_be_8 n x pos';
  pos'
}

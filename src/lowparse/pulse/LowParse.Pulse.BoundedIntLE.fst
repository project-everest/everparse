module LowParse.Pulse.BoundedIntLE
#lang-pulse
include LowParse.Spec.BoundedInt
open Pulse.Lib.Pervasives
open LowParse.Pulse.Base

module E = LowParse.Pulse.Endianness
module EI = LowParse.Spec.Endianness.Instances
module LPC = LowParse.Pulse.Combinators
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module Cast = FStar.Int.Cast
module U32 = FStar.UInt32
module SpecE = LowParse.Endianness

let serialize_bounded_integer_le_unfold
  (sz: integer_size)
  (n: bounded_integer sz)
: Lemma
  (bare_serialize (serialize_bounded_integer_le sz) n == SpecE.n_to_le sz (U32.v n))
= serialize_bounded_integer_le_spec sz n

let serialize_bounded_integer_le_length
  (sz: integer_size)
  (n: bounded_integer sz)
: Lemma
  (Seq.length (serialize (serialize_bounded_integer_le sz) n) == sz)
= serialize_bounded_integer_le_unfold sz n

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let n_to_le_u32_1 = (E.mk_n_to_le EI.uint32 1)

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let n_to_le_u32_2 = (E.mk_n_to_le EI.uint32 2)

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let n_to_le_u32_3 = (E.mk_n_to_le EI.uint32 3)

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%E.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let n_to_le_u32_4 = (E.mk_n_to_le EI.uint32 4)

inline_for_extraction
fn write_bounded_integer_le_header
  (l: nat { 1 <= l /\ l <= 4 })
: E.n_to_le_t EI.uint32 l
= (n: FStar.UInt32.t)
  (x: S.slice FStar.UInt8.t)
  (#v: Ghost.erased (Seq.seq FStar.UInt8.t))
  (pos: SZ.t)
{
  if (l = 1) { n_to_le_u32_1 n x #v pos }
  else if (l = 2) { n_to_le_u32_2 n x #v pos }
  else if (l = 3) { n_to_le_u32_3 n x #v pos }
  else { n_to_le_u32_4 n x #v pos }
}

inline_for_extraction
fn l2r_leaf_write_bounded_integer_le
  (sz: integer_size)
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: l2r_leaf_writer u#0 #(bounded_integer sz) #(parse_bounded_integer_kind sz) #(parse_bounded_integer_le sz) (serialize_bounded_integer_le sz)
= (n: bounded_integer sz)
  (x: S.slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len x;
  serialize_bounded_integer_le_unfold sz n;
  bounded_integer_prop_equiv sz n;
  write_bounded_integer_le_header sz n x #v offset;
  SZ.add offset sz_sz
}

inline_for_extraction
let l2r_leaf_write_u16_le : l2r_leaf_writer serialize_u16_le =
  [@@inline_let] let _ = synth_u16_le_injective in
  [@@inline_let] let _ = synth_u16_le_inverse in
  LPC.l2r_leaf_write_synth' (l2r_leaf_write_bounded_integer_le 2 2sz) synth_u16_le synth_u16_le_recip

inline_for_extraction
let l2r_leaf_write_u32_le : l2r_leaf_writer serialize_u32_le =
  LPC.l2r_leaf_write_synth' (l2r_leaf_write_bounded_integer_le 4 4sz) synth_u32_le synth_u32_le_recip

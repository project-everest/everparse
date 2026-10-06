module EverParse3d.InputStream.LowstarExtern.Types
open Pulse.Lib.Pervasives
#lang-pulse

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module I = EverParse3d.InputStream.Base
module E = EverParse3d.Lowstar.ErrorCode

// Abstract client ABI types and ghost model, as in the old extern Base.fsti.
// The position indexing storage is ghost, NOT a client position-query API.
assume val extra_t : Type0
assume val input_stream_base : Type0
assume val get_all (base: input_stream_base)
  : GTot (s: Seq.seq U8.t { Seq.length s < E.position_limit })
assume val storage (base: input_stream_base) (position: nat) : slprop

// Preserve this named record during extraction as EVERPARSE_INPUT_BUFFER.
noeq type input_buffer = {
  base: input_stream_base;
  has_length: bool;
  length: U64.t;
}

inline_for_extraction noextract let base_t = input_buffer
inline_for_extraction noextract let len_t = unit
inline_for_extraction noextract let pos_t = R.ref U64.t

noextract
let view_ok (b: base_t) (c: Seq.seq U8.t) : prop =
  Seq.length c <= Seq.length (get_all b.base) /\
  Seq.equal c (Seq.slice (get_all b.base) 0 (Seq.length c)) /\
  (if b.has_length then U64.v b.length == Seq.length c
   else Seq.equal c (get_all b.base))

// Public ownership has no local reference. Its scalar position uses the
// original coordinates, including the caller's nonzero start.
let public_pts_to (b: base_t) (position: U64.t)
  (c v: Seq.seq U8.t) : slprop =
  storage b.base (U64.v position) **
  pure (view_ok b c /\ I.seq_is_suffix_of v c /\
        U64.v position + Seq.length v == Seq.length c)

let stream_pts_to (b: base_t) (_: len_t) (pos: pos_t)
  (c v: Seq.seq U8.t) : slprop =
  exists* position. R.pts_to pos position ** public_pts_to b position c v

// Truncation is only a view change. The token carries no raw client resource,
// and cannot manufacture it. The same local reference is retained.
let stream_is_prefix_of
  (bx: base_t) (_: len_t) (px: pos_t)
  (parent: base_t) (_: len_t) (py: pos_t)
  (c0 suffix: Seq.seq U8.t) : slprop =
  pure (bx.base == parent.base /\ px == py /\ view_ok parent c0 /\
        bx.has_length /\
        U64.v bx.length + Seq.length suffix == Seq.length c0 /\
        Seq.equal suffix
          (Seq.slice c0 (U64.v bx.length) (Seq.length c0)))

noextract inline_for_extraction
let pts_to_inst : I.input_stream_pts_to base_t len_t pos_t = {
  pts_to = stream_pts_to;
  is_prefix_of = stream_is_prefix_of;
}

inline_for_extraction
let make_input_buffer (base: input_stream_base) : base_t =
  { base = base; has_length = false; length = 0UL }

inline_for_extraction
let make_input_buffer_with_length (base: input_stream_base) (length: U64.t)
  : base_t = { base = base; has_length = true; length = length }

module LowParse.Pulse.ArrayPtr.Int
#lang-pulse
(* ArrayPtr leaf readers for the fixed-width integers.

   These mirror the readers of LowParse.Pulse.Int and
   LowParse.PulseParse.BoundedIntLE, but they read straight out of a
   [Pulse.Lib.ArrayPtr.ptr], so the extracted C is a sequence of plain [b[i]]
   loads with no intermediate slice records.

   Unlike the Slice readers, which are phrased against [pts_to_serialized],
   these are phrased directly against [parse]: every integer parser in
   LowParse.Spec.Int and LowParse.Spec.BoundedInt already comes with a
   parse-side specification in terms of [be_to_n] / [le_to_n], which is exactly
   what the [mk_be_to_n] / [mk_le_to_n] loops compute. *)

open Pulse.Lib.Pervasives
open LowParse.Spec.Base
open LowParse.Spec.Int
open LowParse.Spec.BoundedInt
open LowParse.Spec.Combinators

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module E = LowParse.Endianness
module EI = LowParse.Spec.Endianness.Instances
module SZ = FStar.SizeT
module AP = Pulse.Lib.ArrayPtr
module APE = LowParse.Pulse.ArrayPtr.Endianness

(* A reader for a constant-size strong-prefix parser, reading from the front of
   [x]. [x] is allowed to extend past the end of the field: validation has
   already established that at least [parser_kind_low] bytes are available, and
   the strong-prefix property makes the trailing bytes irrelevant. *)
inline_for_extraction
noextract
let leaf_reader
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
= (x: AP.ptr U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt t
    (AP.pts_to x #pm v ** pure (
      k.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low <= Seq.length v /\
      Some? (parse p v)
    ))
    (fun res -> AP.pts_to x #pm v ** pure (
      k.parser_kind_low <= Seq.length v /\
      parse p v == Some (res, k.parser_kind_low)
    ))

(* A constant-size strong-prefix parser consumes exactly [parser_kind_low]
   bytes. The parse-side specification lemmas below all apply to [v] directly,
   so this is the only bridging step the readers need. *)
let parse_constant_size_eq
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (v: bytes)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    Some? (parse p v)
  ))
  (ensures (
    Some? (parse p v) /\
    snd (Some?.v (parse p v)) == k.parser_kind_low
  ))
= parser_kind_prop_equiv k p

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%APE.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_1 = APE.mk_be_to_n EI.uint8 1

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%APE.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_2 = APE.mk_be_to_n EI.uint16 2

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%APE.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_4 = APE.mk_be_to_n EI.uint32 4

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%APE.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let be_to_n_8 = APE.mk_be_to_n EI.uint64 8

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%APE.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let le_to_n_2 = APE.mk_le_to_n EI.uint16 2

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%APE.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let le_to_n_4 = APE.mk_le_to_n EI.uint32 4

inline_for_extraction
noextract
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta_attr [`%APE.must_reduce]; iota; zeta; primops]; FStar.Tactics.trefl ())]
let le_to_n_8 = APE.mk_le_to_n EI.uint64 8

inline_for_extraction
noextract
fn read_u8 (_: unit) : leaf_reader parse_u8
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  parse_constant_size_eq parse_u8 v;
  parse_u8_spec v;
  be_to_n_1 x 1sz
}

inline_for_extraction
noextract
fn read_u16 (_: unit) : leaf_reader parse_u16
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  parse_constant_size_eq parse_u16 v;
  parse_u16_spec v;
  be_to_n_2 x 2sz
}

inline_for_extraction
noextract
fn read_u32 (_: unit) : leaf_reader parse_u32
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  parse_constant_size_eq parse_u32 v;
  parse_u32_spec v;
  be_to_n_4 x 4sz
}

inline_for_extraction
noextract
fn read_u64 (_: unit) : leaf_reader parse_u64
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  parse_constant_size_eq parse_u64 v;
  parse_u64_spec v;
  be_to_n_8 x 8sz
}

inline_for_extraction
noextract
fn read_u64_le (_: unit) : leaf_reader parse_u64_le
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  parse_constant_size_eq parse_u64_le v;
  parse_u64_le_spec v;
  le_to_n_8 x 0sz
}

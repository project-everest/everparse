module LowParse.PulseParse.Bytes
#lang-pulse
include LowParse.Spec.Bytes
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module PPCV = LowParse.PulseParse.VLData
module PPVG = LowParse.PulseParse.VLGen
module U32 = FStar.UInt32

inline_for_extraction
let validate_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: LPS.validator (parse_flbytes sz)
= LPS.validate_total_constant_size (parse_flbytes sz) sz_sz

inline_for_extraction
let jump_flbytes
  (sz: nat { sz < 4294967296 })
  (sz_sz: SZ.t { SZ.v sz_sz == sz })
: LPS.jumper (parse_flbytes sz)
= LPS.jump_constant_size (parse_flbytes sz) sz_sz

inline_for_extraction
fn jump_all_bytes
  (_: squash FStar.SizeT.fits_u64)
: LPS.jumper parse_all_bytes
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  parser_kind_prop_equiv parse_all_bytes_kind parse_all_bytes;
  len input
}

inline_for_extraction
fn validate_all_bytes
  (_: squash FStar.SizeT.fits_u64)
: LPS.validator parse_all_bytes
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  let offset_val = !poffset;
  let input_len = len input;
  let remaining = SZ.sub input_len offset_val;
  SZ.fits_u64_implies_fits_32 ();
  // parse_all_bytes succeeds only for inputs < 4294967296 bytes
  if SZ.gt remaining (SZ.uint32_to_sizet 4294967295ul) {
    false
  } else {
    poffset := input_len;
    true
  }
}

inline_for_extraction
let validate_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (_: squash FStar.SizeT.fits_u64)
: LPS.validator (parse_bounded_vlbytes' min max l)
= PPC.validate_synth
    (PPCV.validate_bounded_vldata_strong' min max l serialize_all_bytes (validate_all_bytes ()) lr ())
    (synth_bounded_vlbytes min max)

inline_for_extraction
let validate_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (_: squash FStar.SizeT.fits_u64)
: LPS.validator (parse_bounded_vlbytes min max)
= validate_bounded_vlbytes' min max (log256' max) lr ()

inline_for_extraction
let validate_bounded_vlgenbytes
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator (parse_bounded_vlgenbytes vmin vmax pk)
= PPC.validate_synth
    (PPVG.validate_bounded_vlgen vmin vmax vk rk serialize_all_bytes (validate_all_bytes ()) ())
    (synth_bounded_vlbytes vmin vmax)

module LPC = LowParse.Pulse.Combinators

inline_for_extraction
let jump_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: LPS.leaf_reader (serialize_bounded_integer l))
  (_: squash FStar.SizeT.fits_u64)
: LPS.jumper (parse_bounded_vlbytes' min max l)
= LPC.jump_synth
    (PPCV.jump_bounded_vldata_strong' min max l serialize_all_bytes lr ())
    (synth_bounded_vlbytes min max)

inline_for_extraction
let jump_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: LPS.leaf_reader (serialize_bounded_integer (log256' max)))
  (_: squash FStar.SizeT.fits_u64)
: LPS.jumper (parse_bounded_vlbytes min max)
= jump_bounded_vlbytes' min max (log256' max) lr ()

inline_for_extraction
let jump_bounded_vlgenbytes
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.jumper (parse_bounded_vlgenbytes vmin vmax pk)
= LPC.jump_synth
    (PPVG.jump_bounded_vlgen vmin vmax jk rk serialize_all_bytes ())
    (synth_bounded_vlbytes vmin vmax)

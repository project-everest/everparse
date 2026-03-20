module LowParse.PulseParse.VLGen
#lang-pulse
include LowParse.Spec.VLGen
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
module PPCF = LowParse.PulseParse.FLData
module U32 = FStar.UInt32

inline_for_extraction
fn validate_bounded_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator (parse_bounded_vlgen vmin vmax pk s)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_bounded_vlgen_unfold_aux vmin vmax pk s sinput;
  let offset_val = !poffset;
  let n_valid = vk input poffset;
  if n_valid {
    let off1 = !poffset;
    let len = PPB.read_parsed_from_validator_success rk input offset_val off1;
    SZ.fits_u64_implies_fits_32 ();
    PPCF.validate_fldata_strong s v (SZ.uint32_to_sizet len) input poffset
  } else {
    false
  }
}

inline_for_extraction
let validate_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond vmin vmax k })
  (v: LPS.validator p)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator (parse_vlgen vmin vmax pk s)
= PPC.validate_synth
    (validate_bounded_vlgen vmin vmax vk rk s v sq)
    (synth_vlgen vmin vmax s)

inline_for_extraction
fn validate_vlgen_weak
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator (parse_vlgen_weak vmin vmax pk p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_vlgen_weak_unfold vmin vmax pk p sinput;
  let offset_val = !poffset;
  let n_valid = vk input poffset;
  if n_valid {
    let off1 = !poffset;
    let len = PPB.read_parsed_from_validator_success rk input offset_val off1;
    SZ.fits_u64_implies_fits_32 ();
    PPCF.validate_fldata v (SZ.uint32_to_sizet len) input poffset
  } else {
    false
  }
}

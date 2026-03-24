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
module LPC = LowParse.Pulse.Combinators
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
= LPC.validate_synth
    (validate_bounded_vlgen vmin vmax vk rk s v sq)
    (synth_vlgen vmin vmax s)

#push-options "--z3rlimit 32"

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

#pop-options

(* ========== VLGen jumpers ========== *)

inline_for_extraction
fn jump_bounded_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.jumper (parse_bounded_vlgen vmin vmax pk s)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_bounded_vlgen_unfold_aux vmin vmax pk s sinput;
  pts_to_len input;
  let off1 = jk input offset;
  let len = PPB.read_parsed_from_validator_success rk input offset off1;
  SZ.fits_u64_implies_fits_32 ();
  PPCF.jump_fldata_strong s (SZ.uint32_to_sizet len) input off1
}

module LPC = LowParse.Pulse.Combinators

inline_for_extraction
let jump_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 })
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond vmin vmax k })
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.jumper (parse_vlgen vmin vmax pk s)
= LPC.jump_synth
    (jump_bounded_vlgen vmin vmax jk rk s sq)
    (synth_vlgen vmin vmax s)

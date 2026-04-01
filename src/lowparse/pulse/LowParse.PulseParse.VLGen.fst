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
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
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
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
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
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
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
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
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
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond vmin vmax k })
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.jumper (parse_vlgen vmin vmax pk s)
= LPC.jump_synth
    (jump_bounded_vlgen vmin vmax jk rk s sq)
    (synth_vlgen vmin vmax s)

(* ========== VLGen accessors ========== *)

include LowParse.CLens
module PPCV = LowParse.PulseParse.VLData

#push-options "--z3rlimit 128"

inline_for_extraction
fn accessor_bounded_vlgen_payload
  (vmin: Ghost.erased nat)
  (vmax: Ghost.erased nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.accessor (parse_bounded_vlgen vmin vmax pk s) p (PPCV.clens_bounded_vldata_strong vmin vmax s)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax s))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vlgen_unfold_aux vmin vmax pk s bytes;
  parser_kind_prop_equiv sk pk;
  let off1 = jk input 0sz;
  let len = PPB.read_parsed_from_validator_success rk input 0sz off1;
  let input_key, input_payload = split_trade input off1;
  with wb_key . assert (S.pts_to input_key #pm wb_key);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_key #pm wb_key) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk s) input #pm v);
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) k) (parse_fldata_strong s (U32.v len));
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) k) (parse_fldata p (U32.v len));
  parser_kind_prop_equiv k p;
  Seq.lemma_eq_elim wb_payload (Seq.slice wb_payload 0 (Seq.length wb_payload));
  PPB.pts_to_parsed_intro p input_payload (Ghost.reveal v <: t);
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v <: t)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk s) input #pm v);
  input_payload
}

inline_for_extraction
fn accessor_vlgen_payload
  (vmin: Ghost.erased nat)
  (vmax: Ghost.erased nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond vmin vmax k })
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.accessor (parse_vlgen vmin vmax pk s) p (clens_id t)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_vlgen_unfold vmin vmax pk s bytes;
  parser_kind_prop_equiv sk pk;
  let off1 = jk input 0sz;
  let len = PPB.read_parsed_from_validator_success rk input 0sz off1;
  let input_key, input_payload = split_trade input off1;
  with wb_key . assert (S.pts_to input_key #pm wb_key);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_key #pm wb_key) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_vlgen vmin vmax pk s) input #pm v);
  Seq.lemma_eq_elim wb_payload (Seq.slice bytes (SZ.v off1) (SZ.v off1 + U32.v len));
  PPB.pts_to_parsed_intro p input_payload (Ghost.reveal v);
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_vlgen vmin vmax pk s) input #pm v);
  input_payload
}

#pop-options

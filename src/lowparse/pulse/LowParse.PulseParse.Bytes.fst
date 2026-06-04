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
module LPC = LowParse.Pulse.Combinators
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
= LPC.validate_synth
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
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (vk: LPS.validator pk)
  (rk: PPB.leaf_reader pk)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator (parse_bounded_vlgenbytes vmin vmax pk)
= LPC.validate_synth
    (PPVG.validate_bounded_vlgen vmin vmax vk rk serialize_all_bytes (validate_all_bytes ()) ())
    (synth_bounded_vlbytes vmin vmax)


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
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (_: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.jumper (parse_bounded_vlgenbytes vmin vmax pk)
= LPC.jump_synth
    (PPVG.jump_bounded_vlgen vmin vmax jk rk serialize_all_bytes ())
    (synth_bounded_vlbytes vmin vmax)

module B32 = LowParse.Bytes32
module V = Pulse.Lib.Vec
module A = Pulse.Lib.Array

(* Copyful parsing for bytes: the left-hand side of the vmatch is a freshly
   allocated, owned (freeable) vector holding a copy of the parsed bytes.

   NOTE on the choice of left-hand-side type: a [Pulse.Lib.Slice.slice] is a
   borrowing *view* with no allocation/deallocation API, and a slice value does
   not let one recover its concrete backing array/vector at run time (the
   backing is existentially/ghost-bound). Consequently a [free_t] combinator,
   which only receives the left-hand-side value plus a ghost high-level value,
   cannot soundly free a bare slice. We therefore use an owned, freeable
   [Pulse.Lib.Vec.vec byte] as the left-hand side; a read-only slice view is
   always derivable on demand via [from_array (vec_to_array _)]. *)

let vmatch_copy_bytes
  (vc: V.vec byte)
  (v: B32.bytes)
: slprop
= V.pts_to vc (B32.reveal v) **
  pure (V.is_full_vec vc)

let flbytes_conv
  (sz: nat { sz < 4294967296 })
  (b: B32.bytes)
: GTot (option (B32.lbytes sz))
= if B32.length b = sz then Some (b <: B32.lbytes sz) else None

let vldata_all_bytes_conv
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (b: B32.bytes)
: GTot (option (parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes))
= if (let sz = Seq.length (serialize_all_bytes b) in min <= sz && sz <= max)
  then Some (b <: parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes)
  else None

let vlbytes_conv
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (b: B32.bytes)
: GTot (option (parse_bounded_vlbytes_t min max))
= if (min <= B32.length b && B32.length b <= max)
  then Some (b <: parse_bounded_vlbytes_t min max)
  else None

inline_for_extraction
fn free_copy_bytes
  (x: V.vec byte)
  (#v: Ghost.erased B32.bytes)
requires
  vmatch_copy_bytes x v
ensures
  emp
{
  unfold (vmatch_copy_bytes x v);
  V.free x
}

inline_for_extraction
fn alloc_and_copy
  (input: S.slice byte)
  (#pm: perm)
  (#w: Ghost.erased (Seq.seq byte))
requires
  S.pts_to input #pm w
returns vc: V.vec byte
ensures
  S.pts_to input #pm w **
  V.pts_to vc w **
  pure (V.is_full_vec vc)
{
  S.pts_to_len input;
  let length = S.len input;
  let vc = V.alloc 0uy length;
  V.to_array_pts_to vc;
  let tmp = S.from_array (V.vec_to_array vc) length;
  S.pts_to_len tmp;
  SZ.size_v_inj (S.len input);
  SZ.size_v_inj (S.len tmp);
  S.copy tmp input;
  S.to_array tmp;
  V.to_vec_pts_to vc;
  vc
}

inline_for_extraction
fn copyful_parse_all_bytes
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased B32.bytes)
requires
  PPB.pts_to_parsed parse_all_bytes input #pm v
returns vc: V.vec byte
ensures
  PPB.pts_to_parsed parse_all_bytes input #pm v **
  vmatch_copy_bytes vc v
{
  PPB.pts_to_parsed_elim input;
  with w. assert (S.pts_to input #pm w);
  let vc = alloc_and_copy input;
  Trade.elim (S.pts_to input #pm w) (PPB.pts_to_parsed parse_all_bytes input #pm v);
  assert (pure (Ghost.reveal w == B32.reveal v));
  rewrite (V.pts_to vc w) as (V.pts_to vc (B32.reveal v));
  fold (vmatch_copy_bytes vc v);
  vc
}

inline_for_extraction
fn copyful_parse_flbytes
  (sz: nat { sz < 4294967296 })
: PPB.copyful_parse #(V.vec byte) #B32.bytes #(B32.lbytes sz) vmatch_copy_bytes (parse_flbytes sz) (flbytes_conv sz)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (B32.lbytes sz))
{
  PPB.pts_to_parsed_elim input;
  with w. assert (S.pts_to input #pm w);
  let vc = alloc_and_copy input;
  Trade.elim (S.pts_to input #pm w) (PPB.pts_to_parsed (parse_flbytes sz) input #pm v);
  rewrite (V.pts_to vc w) as (V.pts_to vc (B32.reveal v));
  fold (vmatch_copy_bytes vc v);
  PPB.intro_vmatch_conv vmatch_copy_bytes (flbytes_conv sz) vc (Ghost.reveal v <: B32.bytes) (Ghost.reveal v);
  vc
}

inline_for_extraction
fn copyful_parse_bounded_vldata_strong_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse #(V.vec byte) #B32.bytes #(parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes) vmatch_copy_bytes (parse_bounded_vldata_strong' min max l serialize_all_bytes) (vldata_all_bytes_conv min max)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes))
{
  let result = PPCV.accessor_bounded_vldata_strong_payload' min max l serialize_all_bytes lr u input;
  with pm' v2. assert (PPB.pts_to_parsed parse_all_bytes result #pm' v2);
  let vc = copyful_parse_all_bytes result;
  Trade.elim
    (PPB.pts_to_parsed parse_all_bytes result #pm' v2)
    (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l serialize_all_bytes) input #pm v);
  rewrite (vmatch_copy_bytes vc v2) as (vmatch_copy_bytes vc v);
  PPB.intro_vmatch_conv vmatch_copy_bytes (vldata_all_bytes_conv min max) vc (Ghost.reveal v <: B32.bytes) (Ghost.reveal v);
  vc
}

inline_for_extraction
fn copyful_parse_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse #(V.vec byte) #B32.bytes #(parse_bounded_vlbytes_t min max) vmatch_copy_bytes (parse_bounded_vlbytes' min max l) (vlbytes_conv min max)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vlbytes_t min max))
{
  PPC.pts_to_parsed_synth_l2r_trade
    (parse_bounded_vldata_strong' min max l serialize_all_bytes)
    (synth_bounded_vlbytes min max)
    (synth_bounded_vlbytes_recip min max)
    input;
  let vc = copyful_parse_bounded_vldata_strong_payload min max l lr u input;
  Trade.elim
    (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l serialize_all_bytes) input #pm (synth_bounded_vlbytes_recip min max v))
    (PPB.pts_to_parsed (parse_bounded_vlbytes' min max l) input #pm v);
  PPB.elim_vmatch_conv vmatch_copy_bytes (vldata_all_bytes_conv min max) vc (synth_bounded_vlbytes_recip min max v);
  with vm . assert (vmatch_copy_bytes vc vm ** pure (vldata_all_bytes_conv min max vm == Some (synth_bounded_vlbytes_recip min max v)));
  PPB.intro_vmatch_conv vmatch_copy_bytes (vlbytes_conv min max) vc vm (Ghost.reveal v);
  vc
}

inline_for_extraction
let copyful_parse_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse #(V.vec byte) #B32.bytes #(parse_bounded_vlbytes_t min max) vmatch_copy_bytes (parse_bounded_vlbytes min max) (vlbytes_conv min max)
= copyful_parse_bounded_vlbytes' min max (log256' max) lr u

#push-options "--z3rlimit 128"

inline_for_extraction
fn accessor_bounded_vlgen_all_bytes_payload
  (vmin: Ghost.erased nat)
  (vmax: Ghost.erased nat { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.accessor (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) parse_all_bytes (PPCV.clens_bounded_vldata_strong vmin vmax serialize_all_bytes)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax #_ #_ #parse_all_bytes serialize_all_bytes))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vlgen_unfold_aux vmin vmax pk serialize_all_bytes bytes;
  parser_kind_prop_equiv sk pk;
  let off1 = jk input 0sz;
  let len = PPB.read_parsed_from_validator_success rk input 0sz off1;
  let input_key, input_payload = split_trade input off1;
  with wb_key . assert (S.pts_to input_key #pm wb_key);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_key #pm wb_key) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) input #pm v);
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) parse_all_bytes_kind) (parse_fldata_strong serialize_all_bytes (U32.v len));
  parser_kind_prop_equiv (parse_fldata_kind (U32.v len) parse_all_bytes_kind) (parse_fldata parse_all_bytes (U32.v len));
  parser_kind_prop_equiv parse_all_bytes_kind parse_all_bytes;
  Seq.lemma_eq_elim wb_payload (Seq.slice wb_payload 0 (Seq.length wb_payload));
  PPB.pts_to_parsed_intro parse_all_bytes input_payload (Ghost.reveal v <: B32.bytes);
  Trade.trans (PPB.pts_to_parsed parse_all_bytes input_payload #(pm /. 2.0R) (Ghost.reveal v <: B32.bytes)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) input #pm v);
  input_payload
}

#pop-options

inline_for_extraction
fn copyful_parse_bounded_vlgen_payload
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (sq: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.copyful_parse #(V.vec byte) #B32.bytes #(parse_bounded_vldata_strong_t vmin vmax #_ #_ #parse_all_bytes serialize_all_bytes) vmatch_copy_bytes (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) (vldata_all_bytes_conv vmin vmax)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t vmin vmax #_ #_ #parse_all_bytes serialize_all_bytes))
{
  let result = accessor_bounded_vlgen_all_bytes_payload vmin vmax jk rk sq input;
  with pm' v2. assert (PPB.pts_to_parsed parse_all_bytes result #pm' v2);
  let vc = copyful_parse_all_bytes result;
  Trade.elim
    (PPB.pts_to_parsed parse_all_bytes result #pm' v2)
    (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) input #pm v);
  rewrite (vmatch_copy_bytes vc v2) as (vmatch_copy_bytes vc v);
  PPB.intro_vmatch_conv vmatch_copy_bytes (vldata_all_bytes_conv vmin vmax) vc (Ghost.reveal v <: B32.bytes) (Ghost.reveal v);
  vc
}

inline_for_extraction
fn copyful_parse_bounded_vlgenbytes
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax > 0 /\ vmax < 4294967296 })
  (#sk: Ghost.erased parser_kind)
  (#pk: parser sk (bounded_int32 vmin vmax))
  (jk: LPS.jumper pk)
  (rk: PPB.leaf_reader pk)
  (u: squash (sk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.copyful_parse #(V.vec byte) #B32.bytes #(parse_bounded_vlbytes_t vmin vmax) vmatch_copy_bytes (parse_bounded_vlgenbytes vmin vmax pk) (vlbytes_conv vmin vmax)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vlbytes_t vmin vmax))
{
  PPC.pts_to_parsed_synth_l2r_trade
    (parse_bounded_vlgen vmin vmax pk serialize_all_bytes)
    (synth_bounded_vlbytes vmin vmax)
    (synth_bounded_vlbytes_recip vmin vmax)
    input;
  let vc = copyful_parse_bounded_vlgen_payload vmin vmax jk rk u input;
  Trade.elim
    (PPB.pts_to_parsed (parse_bounded_vlgen vmin vmax pk serialize_all_bytes) input #pm (synth_bounded_vlbytes_recip vmin vmax v))
    (PPB.pts_to_parsed (parse_bounded_vlgenbytes vmin vmax pk) input #pm v);
  PPB.elim_vmatch_conv vmatch_copy_bytes (vldata_all_bytes_conv vmin vmax) vc (synth_bounded_vlbytes_recip vmin vmax v);
  with vm . assert (vmatch_copy_bytes vc vm ** pure (vldata_all_bytes_conv vmin vmax vm == Some (synth_bounded_vlbytes_recip vmin vmax v)));
  PPB.intro_vmatch_conv vmatch_copy_bytes (vlbytes_conv vmin vmax) vc vm (Ghost.reveal v);
  vc
}

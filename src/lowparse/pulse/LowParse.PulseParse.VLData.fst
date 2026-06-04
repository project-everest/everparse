module LowParse.PulseParse.VLData
#lang-pulse
include LowParse.Spec.VLData
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

(* validate_vldata_gen: validate variable-length data with a bounded integer length prefix *)

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (f': (x: bounded_integer sz) -> (y: bool { y == f x }))
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (lr: PPB.leaf_reader (parse_bounded_integer sz))
  (u: squash FStar.SizeT.fits_u64)
: LPS.validator #t #(parse_vldata_gen_kind sz k) (parse_vldata_gen sz f p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_vldata_gen_eq sz f p sinput;
  parser_kind_prop_equiv (parse_bounded_integer_kind sz) (parse_bounded_integer sz);
  pts_to_len input;
  let offset_val = !poffset;
  SZ.fits_u64_implies_fits_32 ();
  let sz_sz = SZ.uint32_to_sizet (U32.uint_to_t sz);
  let input_len = len input;
  let remaining = SZ.sub input_len offset_val;
  if SZ.lt remaining sz_sz {
    false
  } else {
    LPS.validate_total_constant_size (parse_bounded_integer sz) sz_sz input poffset;
    let off1 = !poffset;
    let bi = PPB.read_parsed_from_validator_success lr input offset_val off1;
    if not (f' bi) {
      false
    } else {
      let len_payload = SZ.uint32_to_sizet bi;
      let remaining2 = SZ.sub input_len off1;
      if SZ.lt remaining2 len_payload {
        false
      } else {
        let payload_end = SZ.add off1 len_payload;
        let input3, input4 = split_trade input payload_end;
        with v4 . assert (pts_to input4 #pm v4);
        Trade.elim_hyp_r (pts_to input3 #pm _) (pts_to input4 #pm v4) (pts_to input #pm v_bytes);
        poffset := off1;
        let is_valid = v input3 poffset;
        if is_valid {
          let off2 = !poffset;
          Trade.elim (pts_to input3 #pm _) (pts_to input #pm v_bytes);
          if (off2 = payload_end) {
            true
          } else {
            false
          }
        } else {
          Trade.elim (pts_to input3 #pm _) (pts_to input #pm v_bytes);
          false
        }
      }
    }
  }
}

#pop-options

(* jump_vldata_gen: jump variable-length data with a bounded integer length prefix *)

#push-options "--z3rlimit 32"

inline_for_extraction
fn jump_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (lr: LPS.leaf_reader (serialize_bounded_integer sz))
  (u: squash FStar.SizeT.fits_u64)
: LPS.jumper #t #(parse_vldata_gen_kind sz k) (parse_vldata_gen sz f p)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_vldata_gen_eq sz f p sinput;
  parser_kind_prop_equiv (parse_bounded_integer_kind sz) (parse_bounded_integer sz);
  pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  let sz_sz = SZ.uint32_to_sizet (U32.uint_to_t sz);
  let off1 = SZ.add offset sz_sz;
  let len = LPS.read_from_validator_success lr input offset off1;
  let len_sz = SZ.uint32_to_sizet len;
  SZ.add off1 len_sz
}

(* jump_bounded_vldata': bounded variable-length data *)

inline_for_extraction
fn jump_bounded_vldata'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (lr: LPS.leaf_reader (serialize_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: LPS.jumper #t #(parse_bounded_vldata_strong_kind min max l k) (parse_bounded_vldata' min max l p)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parse_bounded_vldata_correct min max l p;
  jump_vldata_gen l (in_bounds min max) p lr () input offset
}

(* jump_bounded_vldata: bounded variable-length data with default log *)

inline_for_extraction
fn jump_bounded_vldata
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (lr: LPS.leaf_reader (serialize_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: LPS.jumper #t #(parse_bounded_vldata_strong_kind min max (log256' max) k) (parse_bounded_vldata min max p)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  jump_bounded_vldata' min max (log256' max) p lr () input offset
}

(* jump_bounded_vldata_strong': strong bounded variable-length data *)

inline_for_extraction
fn jump_bounded_vldata_strong'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (lr: LPS.leaf_reader (serialize_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: LPS.jumper #(parse_bounded_vldata_strong_t min max s) #(parse_bounded_vldata_strong_kind min max l k) (parse_bounded_vldata_strong' min max l s)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  jump_bounded_vldata' min max l p lr () input offset
}

(* jump_bounded_vldata_strong: strong bounded variable-length data with default log *)

inline_for_extraction
fn jump_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (lr: LPS.leaf_reader (serialize_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: LPS.jumper #(parse_bounded_vldata_strong_t min max s) #(parse_bounded_vldata_strong_kind min max (log256' max) k) (parse_bounded_vldata_strong min max s)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  jump_bounded_vldata_strong' min max (log256' max) s lr () input offset
}

#pop-options

(* validate_bounded_vldata': bounded variable-length data *)

inline_for_extraction
fn validate_bounded_vldata'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: LPS.validator #t #(parse_bounded_vldata_strong_kind min max l k) (parse_bounded_vldata' min max l p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  parse_bounded_vldata_correct min max l p;
  validate_vldata_gen l (in_bounds min max) (fun (i: bounded_integer l) -> if min = 0 then U32.lte i (U32.uint_to_t max) else (U32.lte (U32.uint_to_t min) i && U32.lte i (U32.uint_to_t max))) v lr () input poffset
}

(* validate_bounded_vldata: bounded variable-length data with default log *)

inline_for_extraction
fn validate_bounded_vldata
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: LPS.validator #t #(parse_bounded_vldata_strong_kind min max (log256' max) k) (parse_bounded_vldata min max p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  validate_bounded_vldata' min max (log256' max) v lr () input poffset
}

(* validate_vldata_payload: payload validator for variable-length data *)

inline_for_extraction
let validate_vldata_payload
  (sz: integer_size)
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (i: bounded_integer sz { f i == true })
  (_: squash FStar.SizeT.fits_u64)
: Tot (LPS.validator (parse_vldata_payload sz f p i))
= FStar.SizeT.fits_u64_implies_fits_32 ();
  LPS.validate_weaken (parse_vldata_payload_kind sz k) (PPCF.validate_fldata v (SZ.uint32_to_sizet i))

(* validate_bounded_vldata_strong': validates parse_bounded_vldata_strong' *)

inline_for_extraction
fn validate_bounded_vldata_strong'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: LPS.validator #(parse_bounded_vldata_strong_t min max s) #(parse_bounded_vldata_strong_kind min max l k) (parse_bounded_vldata_strong' min max l s)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  validate_bounded_vldata' min max l v lr () input poffset
}

(* validate_bounded_vldata_strong: default log version *)

inline_for_extraction
fn validate_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: LPS.validator #(parse_bounded_vldata_strong_t min max s) #(parse_bounded_vldata_strong_kind min max (log256' max) k) (parse_bounded_vldata_strong min max s)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  validate_bounded_vldata_strong' min max (log256' max) s v lr () input poffset
}

(* zero_copy_parse_bounded_vldata_payload': access the payload of bounded vldata *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn zero_copy_parse_bounded_vldata_payload'
  (#tl #t: Type0) (#vmatch: tl -> t -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (w: PPB.zero_copy_parse vmatch p)
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.zero_copy_parse vmatch (parse_bounded_vldata' min max l p)
= (input: _)
  (#pm: _)
  (#v: _)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  let l_sz = SZ.uint32_to_sizet (U32.uint_to_t l);
  parser_kind_prop_equiv (parse_bounded_integer_kind l) (parse_bounded_integer l);
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vldata_elim' min max l p bytes v (Seq.length bytes);
  let len = PPB.read_parsed_from_validator_success lr input 0sz l_sz;
  let input_prefix, input_payload = split_trade input l_sz;
  with wb_prefix . assert (S.pts_to input_prefix #pm wb_prefix);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_prefix #pm wb_prefix) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vldata' min max l p) input #pm v);
  Seq.lemma_eq_elim wb_payload (Seq.slice bytes (SZ.v l_sz) (SZ.v l_sz + U32.v len));
  PPB.pts_to_parsed_intro p input_payload v;
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) v) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vldata' min max l p) input #pm v);
  let res = w input_payload;
  Trade.trans (vmatch res v) (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) v) (PPB.pts_to_parsed (parse_bounded_vldata' min max l p) input #pm v);
  res
}

#pop-options

inline_for_extraction
let zero_copy_parse_bounded_vldata_payload
  (#tl #t: Type0) (#vmatch: tl -> t -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (w: PPB.zero_copy_parse vmatch p)
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.zero_copy_parse vmatch (parse_bounded_vldata min max p)
= zero_copy_parse_bounded_vldata_payload' min max (log256' max) w lr u

(* accessor_bounded_vldata_payload': accessor for bounded vldata payload *)

include LowParse.CLens

#push-options "--z3rlimit 64"

inline_for_extraction
fn accessor_bounded_vldata_payload'
  (#k: Ghost.erased parser_kind) (#t: Type0) (#p: parser k t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.accessor (parse_bounded_vldata' min max l p) p (clens_id t)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  let l_sz = SZ.uint32_to_sizet (U32.uint_to_t l);
  parser_kind_prop_equiv (parse_bounded_integer_kind l) (parse_bounded_integer l);
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vldata_elim' min max l p bytes v (Seq.length bytes);
  let len = PPB.read_parsed_from_validator_success lr input 0sz l_sz;
  let input_prefix, input_payload = split_trade input l_sz;
  with wb_prefix . assert (S.pts_to input_prefix #pm wb_prefix);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_prefix #pm wb_prefix) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vldata' min max l p) input #pm v);
  Seq.lemma_eq_elim wb_payload (Seq.slice bytes (SZ.v l_sz) (SZ.v l_sz + U32.v len));
  PPB.pts_to_parsed_intro p input_payload v;
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) v) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vldata' min max l p) input #pm v);
  input_payload
}

inline_for_extraction
let accessor_bounded_vldata_payload
  (#k: Ghost.erased parser_kind) (#t: Type0) (#p: parser k t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.accessor (parse_bounded_vldata min max p) p (clens_id t)
= accessor_bounded_vldata_payload' min max (log256' max) lr u

(* accessor_bounded_vldata_strong_payload: accessor for strong bounded vldata payload *)

let clens_bounded_vldata_strong
  (min: nat)
  (max: nat)
  (#k: Ghost.erased parser_kind) (#t: Type) (#p: parser k t)
  (s: serializer p)
: Tot (clens (parse_bounded_vldata_strong_t min max s) t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (x: parse_bounded_vldata_strong_t min max s) -> (x <: t));
}

inline_for_extraction
fn accessor_bounded_vldata_strong_payload'
  (#k: Ghost.erased parser_kind) (#t: Type0) (#p: parser k t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (s: serializer p)
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.accessor (parse_bounded_vldata_strong' min max l s) p (clens_bounded_vldata_strong min max s)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t min max s))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  let l_sz = SZ.uint32_to_sizet (U32.uint_to_t l);
  parser_kind_prop_equiv (parse_bounded_integer_kind l) (parse_bounded_integer l);
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vldata_elim' min max l p bytes (Ghost.reveal v <: t) (Seq.length bytes);
  let len = PPB.read_parsed_from_validator_success lr input 0sz l_sz;
  let input_prefix, input_payload = split_trade input l_sz;
  with wb_prefix . assert (S.pts_to input_prefix #pm wb_prefix);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_prefix #pm wb_prefix) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l s) input #pm v);
  Seq.lemma_eq_elim wb_payload (Seq.slice bytes (SZ.v l_sz) (SZ.v l_sz + U32.v len));
  PPB.pts_to_parsed_intro p input_payload (Ghost.reveal v <: t);
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v <: t)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l s) input #pm v);
  input_payload
}

inline_for_extraction
let accessor_bounded_vldata_strong_payload
  (#k: Ghost.erased parser_kind) (#t: Type0) (#p: parser k t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (s: serializer p)
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.accessor (parse_bounded_vldata_strong min max s) p (clens_bounded_vldata_strong min max s)
= accessor_bounded_vldata_strong_payload' min max (log256' max) s lr u

#pop-options

(* Copyful parse + free for bounded variable-length data.

   The length-prefix framing changes neither the high-level value nor its
   low-level (copyful) representation, so the payload's own [vmatch], copyful
   parser and [free_t] are reused unchanged for the non-strong combinators. For
   the strong combinators, whose high-level type [parse_bounded_vldata_strong_t]
   is a refinement of the payload type [t], the predicate [vmatch_vldata_strong]
   reuses the payload [vmatch] composed with the refinement upcast. *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn copyful_parse_bounded_vldata_payload'
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (#conv: tm -> GTot (option t))
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (w: PPB.copyful_parse vmatch p conv)
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse vmatch (parse_bounded_vldata' min max l p) conv
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  let l_sz = SZ.uint32_to_sizet (U32.uint_to_t l);
  parser_kind_prop_equiv (parse_bounded_integer_kind l) (parse_bounded_integer l);
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vldata_elim' min max l p bytes v (Seq.length bytes);
  let len = PPB.read_parsed_from_validator_success lr input 0sz l_sz;
  let input_prefix, input_payload = split_trade input l_sz;
  with wb_prefix . assert (S.pts_to input_prefix #pm wb_prefix);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_prefix #pm wb_prefix) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vldata' min max l p) input #pm v);
  Seq.lemma_eq_elim wb_payload (Seq.slice bytes (SZ.v l_sz) (SZ.v l_sz + U32.v len));
  PPB.pts_to_parsed_intro p input_payload v;
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) v) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vldata' min max l p) input #pm v);
  let res = w input_payload;
  Trade.elim (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) v) (PPB.pts_to_parsed (parse_bounded_vldata' min max l p) input #pm v);
  res
}

inline_for_extraction
let copyful_parse_bounded_vldata_payload
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (#conv: tm -> GTot (option t))
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (w: PPB.copyful_parse vmatch p conv)
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse vmatch (parse_bounded_vldata min max p) conv
= copyful_parse_bounded_vldata_payload' min max (log256' max) w lr u

(* Separation logic predicate for the strong variant: the low-level
   representation [xl] relates to the refined high-level value [xh] exactly when
   it relates (via the payload [vmatch]) to the underlying payload value. *)

(* Separation logic predicate for the strong variant: the size refinement on the
   high-level value is now carried entirely by [vldata_strong_conv], so the
   predicate is just the payload [vmatch] (right-hand-side type [tm] is the
   refinement-free payload mid type). *)

let vmatch_vldata_strong
  (#tl #tm: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: Ghost.erased parser_kind) (#t: Type0) (#p: parser k t)
  (s: serializer p)
  (vmatch: tl -> tm -> slprop)
  (xl: tl)
  (xh: tm)
: slprop
= vmatch xl xh

(* Partial conversion for the strong variant: the payload mid value [xm] is
   converted to the payload high value, then accepted as a bounded-vldata-strong
   value exactly when its serialization fits the size bounds. *)

let vldata_strong_conv
  (#tm #t: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (s: serializer p)
  (conv: tm -> GTot (option t))
  (xm: tm)
: GTot (option (parse_bounded_vldata_strong_t min max s))
= match conv xm with
  | Some x ->
    if (let sz = Seq.length (serialize s x) in min <= sz && sz <= max)
    then Some (x <: parse_bounded_vldata_strong_t min max s)
    else None
  | None -> None

inline_for_extraction
fn copyful_parse_bounded_vldata_strong_payload'
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (#conv: tm -> GTot (option t))
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (s: serializer p)
  (w: PPB.copyful_parse vmatch p conv)
  (lr: PPB.leaf_reader (parse_bounded_integer l))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse (vmatch_vldata_strong min max s vmatch) (parse_bounded_vldata_strong' min max l s) (vldata_strong_conv min max s conv)
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (parse_bounded_vldata_strong_t min max s))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  S.pts_to_len input;
  SZ.fits_u64_implies_fits_32 ();
  let l_sz = SZ.uint32_to_sizet (U32.uint_to_t l);
  parser_kind_prop_equiv (parse_bounded_integer_kind l) (parse_bounded_integer l);
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  parse_bounded_vldata_elim' min max l p bytes (Ghost.reveal v <: t) (Seq.length bytes);
  let len = PPB.read_parsed_from_validator_success lr input 0sz l_sz;
  let input_prefix, input_payload = split_trade input l_sz;
  with wb_prefix . assert (S.pts_to input_prefix #pm wb_prefix);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_prefix #pm wb_prefix) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l s) input #pm v);
  Seq.lemma_eq_elim wb_payload (Seq.slice bytes (SZ.v l_sz) (SZ.v l_sz + U32.v len));
  PPB.pts_to_parsed_intro p input_payload (Ghost.reveal v <: t);
  Trade.trans (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v <: t)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l s) input #pm v);
  let res = w input_payload;
  Trade.elim (PPB.pts_to_parsed p input_payload #(pm /. 2.0R) (Ghost.reveal v <: t)) (PPB.pts_to_parsed (parse_bounded_vldata_strong' min max l s) input #pm v);
  PPB.elim_vmatch_conv vmatch conv res (Ghost.reveal v <: t);
  with vm . assert (vmatch res vm ** pure (conv vm == Some (Ghost.reveal v <: t)));
  fold (vmatch_vldata_strong min max s vmatch res vm);
  PPB.intro_vmatch_conv (vmatch_vldata_strong min max s vmatch) (vldata_strong_conv min max s conv) res vm (Ghost.reveal v);
  res
}

inline_for_extraction
let copyful_parse_bounded_vldata_strong_payload
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (#conv: tm -> GTot (option t))
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (s: serializer p)
  (w: PPB.copyful_parse vmatch p conv)
  (lr: PPB.leaf_reader (parse_bounded_integer (log256' max)))
  (u: squash FStar.SizeT.fits_u64)
: PPB.copyful_parse (vmatch_vldata_strong min max s vmatch) (parse_bounded_vldata_strong min max s) (vldata_strong_conv min max s conv)
= copyful_parse_bounded_vldata_strong_payload' min max (log256' max) s w lr u

inline_for_extraction
fn free_vldata_strong
  (#tl #tm #t: Type0) (#vmatch: tl -> tm -> slprop)
  (#k: Ghost.erased parser_kind) (#p: parser k t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (s: serializer p)
  (free: PPB.free_t vmatch)
: PPB.free_t (vmatch_vldata_strong min max s vmatch)
=
  (x: tl)
  (#v: Ghost.erased tm)
{
  unfold (vmatch_vldata_strong min max s vmatch x v);
  free x #v;
}

#pop-options

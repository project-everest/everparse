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
  (#k: parser_kind)
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

(* validate_bounded_vldata': bounded variable-length data *)

inline_for_extraction
fn validate_bounded_vldata'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 })
  (#k: parser_kind)
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
  (#k: parser_kind)
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
  (#k: parser_kind)
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
  (#k: parser_kind)
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
  (#k: parser_kind)
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

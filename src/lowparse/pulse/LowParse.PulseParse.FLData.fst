module LowParse.PulseParse.FLData
#lang-pulse
include LowParse.Spec.FLData
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base

inline_for_extraction
fn validate_fldata
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (sz: SZ.t)
: LPS.validator #t #(parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  let offset_val = !poffset;
  let remaining = SZ.sub (len input) offset_val;
  if SZ.lt remaining sz {
    false
  } else {
    let split_point = SZ.add offset_val sz;
    let input1, input2 = split_trade input split_point;
    with v2 . assert (pts_to input2 #pm v2);
    Trade.elim_hyp_r (pts_to input1 #pm _) (pts_to input2 #pm v2) (pts_to input #pm v_bytes);
    let is_valid = v input1 poffset;
    if is_valid {
      let off = !poffset;
      Trade.elim (pts_to input1 #pm _) (pts_to input #pm v_bytes);
      if (off = split_point) {
        true
      } else {
        false
      }
    } else {
      Trade.elim (pts_to input1 #pm _) (pts_to input #pm v_bytes);
      false
    }
  }
}

inline_for_extraction
let validate_fldata_gen
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (sz: SZ.t)
: LPS.validator #t #(parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz))
= validate_fldata v sz

inline_for_extraction
let validate_fldata_consumes_all
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (sz: SZ.t)
  (_: squash (k.parser_kind_subkind == Some ParserConsumesAll))
: LPS.validator #t #(parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz))
= validate_fldata v sz

inline_for_extraction
fn validate_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: LPS.validator p)
  (sz: SZ.t)
: LPS.validator #(parse_fldata_strong_t s (SZ.v sz)) #(parse_fldata_kind (SZ.v sz) k) (parse_fldata_strong s (SZ.v sz))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  validate_fldata v sz input poffset
}

inline_for_extraction
fn jump_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: SZ.t)
: LPS.jumper #t #(parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz))
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parser_kind_prop_equiv (parse_fldata_kind (SZ.v sz) k) (parse_fldata p (SZ.v sz));
  pts_to_len input;
  SZ.add offset sz
}

inline_for_extraction
fn jump_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: SZ.t)
: LPS.jumper #(parse_fldata_strong_t s (SZ.v sz)) #(parse_fldata_kind (SZ.v sz) k) (parse_fldata_strong s (SZ.v sz))
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  parser_kind_prop_equiv (parse_fldata_kind (SZ.v sz) k) (parse_fldata_strong s (SZ.v sz));
  pts_to_len input;
  SZ.add offset sz
}

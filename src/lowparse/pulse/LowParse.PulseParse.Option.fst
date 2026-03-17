module LowParse.PulseParse.Option
#lang-pulse
include LowParse.Spec.Option
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
fn validate_option
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
: LPS.validator #(option t) #(parse_option_kind k) (parse_option p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let offset_val = !poffset;
  let is_valid = v input poffset;
  if is_valid {
    true
  } else {
    poffset := offset_val;
    true
  }
}

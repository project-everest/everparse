module LowParse.PulseParse.List
#lang-pulse
include LowParse.Spec.List
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base

let parse_consume (#k: parser_kind) (#t: Type) (p: parser k t) (b: bytes)
: GTot (option nat)
= match parse p b with
  | Some (_, consumed) -> Some consumed
  | None -> None

inline_for_extraction
fn validate_list
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (u: squash (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0
  ))
: LPS.validator #(list t) #(parse_list_kind k.parser_kind_injective) (parse_list p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  parser_kind_prop_equiv k p;
  let input_len = len input;
  let mut pcontinue = true;
  while (
    let c = !pcontinue;
    let off = !poffset;
    (c && SZ.lt off input_len)
  ) invariant exists* c off .
    R.pts_to pcontinue c **
    R.pts_to poffset off **
    pts_to input #pm v_bytes **
    pure (
      SZ.v off <= Seq.length v_bytes /\
      (c == true ==>
        (Some? (parse (parse_list p) (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes))) ==
         Some? (parse (parse_list p) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes))))) /\
      (c == false ==> None? (parse (parse_list p) (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes))))
    )
  {
    let off = !poffset;
    let s = Ghost.hide (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    parse_list_eq' p s;
    let is_valid = v input poffset;
    if (not is_valid) {
      pcontinue := false
    }
  };
  let off = !poffset;
  let c = !pcontinue;
  if c {
    parse_list_eq p (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    parser_kind_prop_equiv (parse_list_kind k.parser_kind_injective) (parse_list p);
    true
  } else {
    false
  }
}

module LowParse.PulseParse.ListUpTo
#lang-pulse
include LowParse.Spec.ListUpTo
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

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_list_up_to
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (cond: (t -> Tot bool))
  (prf: consumes_if_not_cond cond p)
  (v: LPS.validator p)
  (r: PPB.leaf_reader p)
  (u: squash (
    k.parser_kind_subkind == Some ParserStrong
  ))
: LPS.validator #(parse_list_up_to_t cond) #(parse_list_up_to_kind k) (parse_list_up_to cond p prf)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let mut pcontinue = true;
  let mut presult = true;
  while (
    let c = !pcontinue;
    c
  ) invariant exists* c res off .
    R.pts_to pcontinue c **
    R.pts_to presult res **
    R.pts_to poffset off **
    pts_to input #pm v_bytes **
    pure (
      SZ.v off <= Seq.length v_bytes /\
      SZ.v offset <= SZ.v off /\
      (c == true ==> res == true) /\
      (c == true ==>
        (match parse (parse_list_up_to cond p prf) (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes)) with
         | None -> None? (parse (parse_list_up_to cond p prf) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes)))
         | Some (_, consumed_all) ->
           (match parse (parse_list_up_to cond p prf) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes)) with
            | None -> False
            | Some (_, consumed_rest) -> consumed_all == (SZ.v off - SZ.v offset) + consumed_rest)
        )) /\
      (c == false ==>
        LPS.validator_postcond (parse_list_up_to cond p prf) offset v_bytes off res
      )
    )
  {
    let off = !poffset;
    let s = Ghost.hide (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    parse_list_up_to_eq cond p prf s;
    let is_valid = v input poffset;
    if is_valid {
      let off2 = !poffset;
      let x = PPB.read_parsed_from_validator_success r input off off2;
      Seq.lemma_eq_elim
        (Seq.slice s (SZ.v off2 - SZ.v off) (Seq.length s))
        (Seq.slice v_bytes (SZ.v off2) (Seq.length v_bytes));
      if (cond x) {
        pcontinue := false
      } else {
        prf s x (SZ.v off2 - SZ.v off)
      }
    } else {
      poffset := off;
      presult := false;
      pcontinue := false
    }
  };
  let res = !presult;
  res
}

#pop-options

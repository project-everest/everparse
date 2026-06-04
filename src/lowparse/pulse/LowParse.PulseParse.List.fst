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
module PPB = LowParse.PulseParse.Base
module PPVCL = LowParse.PulseParse.VCList
module V = Pulse.Lib.Vec
module SM = Pulse.Lib.SeqMatch
module Seq = FStar.Seq
module L = FStar.List.Tot

let parse_consume (#k: parser_kind) (#t: Type) (p: parser k t) (b: bytes)
: GTot (option nat)
= match parse p b with
  | Some (_, consumed) -> Some consumed
  | None -> None

inline_for_extraction
fn validate_list
  (#k: Ghost.erased parser_kind)
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

(* ============================================================================ *)
(* Copyful parser for byte-length-bounded lists                                 *)
(* ============================================================================ *)

(* Convert pts_to_parsed (parse_list p) into pts_to_parsed (parse_nlist (length v) p)
   over the same bytes, with a trade back. Built on parse_list_parse_nlist. *)

ghost
fn pts_to_parsed_list_to_nlist
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (list t))
  requires PPB.pts_to_parsed (parse_list p) input #pm v
  ensures exists* (v': PPVCL.nlist (L.length (Ghost.reveal v)) t) .
    PPB.pts_to_parsed (PPVCL.parse_nlist (L.length (Ghost.reveal v)) p) input #pm v' **
    Trade.trade
      (PPB.pts_to_parsed (PPVCL.parse_nlist (L.length (Ghost.reveal v)) p) input #pm v')
      (PPB.pts_to_parsed (parse_list p) input #pm v) **
    pure ((v' <: list t) == Ghost.reveal v)
{
  unfold (PPB.pts_to_parsed (parse_list p) input #pm v);
  with w . assert (pts_to input #pm w);
  PPVCL.parse_list_parse_nlist p w;
  let v' : Ghost.erased (PPVCL.nlist (L.length (Ghost.reveal v)) t) = Ghost.hide (Ghost.reveal v);
  fold (PPB.pts_to_parsed (PPVCL.parse_nlist (L.length (Ghost.reveal v)) p) input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed (PPVCL.parse_nlist (L.length (Ghost.reveal v)) p) input #pm v')
      (PPB.pts_to_parsed (parse_list p) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed (PPVCL.parse_nlist (L.length (Ghost.reveal v)) p) input #pm v');
      with w' . assert (pts_to input #pm w');
      PPVCL.parse_nlist_parse_list_full p (L.length (Ghost.reveal v)) w';
      fold (PPB.pts_to_parsed (parse_list p) input #pm v)
    };
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn copyful_parse_list
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#el #em: Type0)
  (#elem_vmatch: el -> em -> slprop)
  (#elem_conv: em -> GTot (option t))
  (w: PPB.copyful_parse elem_vmatch p elem_conv)
  (j: LPS.jumper p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (list t))
requires
  PPB.pts_to_parsed (parse_list p) input #pm v
returns res: PPVCL.vclist_lowtype el
ensures
  PPB.pts_to_parsed (parse_list p) input #pm v **
  PPB.vmatch_conv (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv)) (fun (x: list t) -> Some x) res (Ghost.reveal v)
{
  parser_kind_prop_equiv k p;
  (* count pass *)
  PPB.pts_to_parsed_elim input;
  with w_bytes . assert (S.pts_to input #pm w_bytes);
  pts_to_len input;
  let input_len = len input;
  let mut poffset = 0sz;
  let mut pcount = 0sz;
  while (
    let off = !poffset;
    SZ.lt off input_len
  ) invariant exists* off count .
    R.pts_to poffset off **
    R.pts_to pcount count **
    S.pts_to input #pm w_bytes **
    pure (
      SZ.v off <= Seq.length w_bytes /\
      SZ.v count <= SZ.v off /\
      Some? (parse (parse_list p) (Seq.slice w_bytes (SZ.v off) (Seq.length w_bytes))) /\
      SZ.v count +
        L.length (fst (Some?.v (parse (parse_list p) (Seq.slice w_bytes (SZ.v off) (Seq.length w_bytes)))))
        == L.length (Ghost.reveal v)
    )
  {
    let off = !poffset;
    let count = !pcount;
    let s = Ghost.hide (Seq.slice w_bytes (SZ.v off) (Seq.length w_bytes));
    parse_list_eq' p s;
    let off' = j input off;
    poffset := off';
    pcount := SZ.add count 1sz;
  };
  let off = !poffset;
  parse_list_eq p (Seq.slice w_bytes (SZ.v off) (Seq.length w_bytes));
  let n = !pcount;
  Trade.elim
    (S.pts_to input #pm w_bytes)
    (PPB.pts_to_parsed (parse_list p) input #pm v);
  if (SZ.gt n 0sz) {
    (* nonempty: convert to nlist, then fill the Vec *)
    pts_to_parsed_list_to_nlist p sq input;
    with v' . assert (PPB.pts_to_parsed (PPVCL.parse_nlist (L.length (Ghost.reveal v)) p) input #pm v');
    let vec = PPVCL.copyful_parse_nlist w j () (Ghost.hide (L.length (Ghost.reveal v))) n input;
    Trade.elim
      (PPB.pts_to_parsed (PPVCL.parse_nlist (L.length (Ghost.reveal v)) p) input #pm v')
      (PPB.pts_to_parsed (parse_list p) input #pm v);
    PPVCL.nlist_length_fact (L.length (Ghost.reveal v)) v';
    let res = PPVCL.vmatch_vclist_some_intro #el #t #(PPB.vmatch_conv elem_vmatch elem_conv) n vec v;
    PPB.intro_vmatch_conv (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv)) (fun (x: list t) -> Some x) res (Ghost.reveal v) (Ghost.reveal v);
    res
  } else {
    (* empty list *)
    PPVCL.nil_of_length_zero (Ghost.reveal v);
    let res : PPVCL.vclist_lowtype el = None #(SZ.t & V.vec el);
    fold (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (None #(SZ.t & V.vec el)) (Ghost.reveal v));
    rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (None #(SZ.t & V.vec el)) (Ghost.reveal v))
      as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) res (Ghost.reveal v));
    PPB.intro_vmatch_conv (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv)) (fun (x: list t) -> Some x) res (Ghost.reveal v) (Ghost.reveal v);
    res
  }
}

#pop-options

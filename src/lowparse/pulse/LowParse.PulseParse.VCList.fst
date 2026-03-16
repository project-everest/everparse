module LowParse.PulseParse.VCList
#lang-pulse
include LowParse.Spec.VCList
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice.Util
open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base
open LowParse.Spec.Combinators

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module LPV = LowParse.Pulse.VCList

(* pts_to_parsed for nlist 1: convert between pts_to_parsed p and pts_to_parsed (parse_nlist 1 p) *)

ghost
fn pts_to_parsed_nlist_1_intro
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires PPB.pts_to_parsed p input #pm v
  ensures exists* v' .
    PPB.pts_to_parsed (parse_nlist 1 p) input #pm v' **
    trade (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v')
      (PPB.pts_to_parsed p input #pm v) **
    pure ((v' <: list t) == [v])
{
  unfold (PPB.pts_to_parsed p input #pm v);
  with w . assert (pts_to input #pm w);
  parse_nlist_eq 1 p w;
  parse_synth_eq p LPV.synth_nlist_1 w;
  let v' : Ghost.erased (nlist 1 t) = Ghost.hide [v];
  fold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v')
      (PPB.pts_to_parsed p input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v');
      with w' . assert (pts_to input #pm w');
      parse_nlist_eq 1 p w';
      parse_synth_eq p LPV.synth_nlist_1 w';
      fold (PPB.pts_to_parsed p input #pm v)
    };
}

ghost
fn pts_to_parsed_nlist_1_elim
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#v: nlist 1 t)
  requires PPB.pts_to_parsed (parse_nlist 1 p) input #pm v
  ensures exists* v' .
    PPB.pts_to_parsed p input #pm v' **
    trade (PPB.pts_to_parsed p input #pm v')
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v) **
    pure (v == [v'])
{
  unfold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v);
  with w . assert (pts_to input #pm w);
  parse_nlist_eq 1 p w;
  parse_synth_eq p LPV.synth_nlist_1 w;
  let v' = Ghost.hide (List.Tot.hd v);
  fold (PPB.pts_to_parsed p input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed p input #pm v')
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed p input #pm v');
      with w' . assert (pts_to input #pm w');
      parse_nlist_eq 1 p w';
      parse_synth_eq p LPV.synth_nlist_1 w';
      fold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v)
    };
}

(* pts_to_parsed ext for nlist: convert between equivalent nlist parsers *)

let pts_to_parsed_nlist_ext_aux
  (#t: Type0)
  (#k1: parser_kind) (#p1: parser k1 t)
  (#k2: parser_kind) (#p2: parser k2 t)
  (n: nat)
  (prf: (b: bytes) -> Lemma (parse p1 b == parse p2 b))
  (b: bytes)
: Lemma (parse (parse_nlist n p1) b == parse (parse_nlist n p2) b)
= parse_nlist_ext n p1 p2 b (fun b' -> prf b')

ghost
fn pts_to_parsed_nlist_ext
  (#t: Type0)
  (#k1: parser_kind) (#p1: parser k1 t)
  (#k2: parser_kind) (#p2: parser k2 t)
  (n: nat)
  (prf: (b: bytes) -> Lemma (parse p1 b == parse p2 b))
  (input: slice byte)
  (#pm: perm)
  (#v: nlist n t)
  requires PPB.pts_to_parsed (parse_nlist n p1) input #pm v
  ensures PPB.pts_to_parsed (parse_nlist n p2) input #pm v
{
  Classical.forall_intro (pts_to_parsed_nlist_ext_aux #t #k1 #p1 #k2 #p2 n prf);
  PPB.pts_to_parsed_ext (parse_nlist n p2) input
}

(* nlist_hd_tl for pts_to_parsed: split a parsed nlist into head and tail sub-slices.
   Requires ParserStrong to split raw bytes at the correct boundary. *)

let nlist_hd_tl_post'
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (input: slice byte)
  (pm: perm)
  (v: (nlist n t))
  (hd tl: slice byte)
: slprop
= PPB.pts_to_parsed p hd #(pm /. 2.0R) (List.Tot.hd v) **
  PPB.pts_to_parsed (parse_nlist (n - 1) p) tl #(pm /. 2.0R) (List.Tot.tl v) **
  Trade.trade
    (PPB.pts_to_parsed p hd #(pm /. 2.0R) (List.Tot.hd v) **
      PPB.pts_to_parsed (parse_nlist (n - 1) p) tl #(pm /. 2.0R) (List.Tot.tl v))
    (PPB.pts_to_parsed (parse_nlist n p) input #pm v)

let nlist_hd_tl_post
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (input: slice byte)
  (pm: perm)
  (v: (nlist n t))
  (hd_tl: (slice byte & slice byte))
: slprop
= nlist_hd_tl_post' p sq n input pm v (fst hd_tl) (snd hd_tl)

inline_for_extraction
fn nlist_hd_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns res : (slice byte & slice byte)
ensures
  nlist_hd_tl_post p sq n input pm v res
{
  PPB.pts_to_parsed_elim input;
  with w . assert (pts_to input #pm w);
  parse_nlist_eq (Ghost.reveal n) p w;
  parser_kind_prop_equiv k p;
  let off = j input 0sz;
  let input1, input2 = split_trade input off;
  with w1 . assert (pts_to input1 #pm w1);
  with w2 . assert (pts_to input2 #pm w2);
  parse_strong_prefix p w w1;
  let vh = Ghost.hide (List.Tot.hd (Ghost.reveal v));
  let vt : Ghost.erased (nlist (n - 1) t) = Ghost.hide (List.Tot.tl (Ghost.reveal v));
  PPB.pts_to_parsed_intro p input1 vh;
  PPB.pts_to_parsed_intro (parse_nlist (n - 1) p) input2 vt;
  // Trade chain: (parsed hd ** parsed tl) -> (pts_to input1 ** pts_to input2) -> (pts_to input) -> (parsed nlist)
  Trade.prod
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh)
    (pts_to input1 #pm w1)
    (PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input2 #pm w2);
  Trade.trans
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh ** PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input1 #pm w1 ** pts_to input2 #pm w2)
    (pts_to input #pm w);
  // Use existing trade from pts_to_parsed_elim: (pts_to input #pm w) -> (parsed nlist)
  Trade.trans
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh ** PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input #pm w)
    (PPB.pts_to_parsed (parse_nlist n p) input #pm v);
  rewrite each vh as (List.Tot.hd (Ghost.reveal v));
  rewrite each vt as (List.Tot.tl (Ghost.reveal v));
  fold (nlist_hd_tl_post' p sq n input pm v input1 input2);
  fold (nlist_hd_tl_post p sq n input pm v (input1, input2));
  (input1, input2)
}

(* nlist_hd: get head element sub-slice *)

inline_for_extraction
fn nlist_hd
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns input' : slice byte
ensures exists* v' .
  PPB.pts_to_parsed p input' #(pm /. 2.0R) v' **
  trade (PPB.pts_to_parsed p input' #(pm /. 2.0R) v') (PPB.pts_to_parsed (parse_nlist n p) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.hd v
  )
{
  let (hd, tl) = nlist_hd_tl sq j n input;
  unfold (nlist_hd_tl_post p sq n input pm v (hd, tl));
  unfold (nlist_hd_tl_post' p sq n input pm v hd tl);
  Trade.elim_hyp_r _ _ _;
  hd
}

(* nlist_tl: get tail sub-slice *)

inline_for_extraction
fn nlist_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns input' : slice byte
ensures exists* v' .
  PPB.pts_to_parsed (parse_nlist (n - 1) p) input' #(pm /. 2.0R) v' **
  trade (PPB.pts_to_parsed (parse_nlist (n - 1) p) input' #(pm /. 2.0R) v') (PPB.pts_to_parsed (parse_nlist n p) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.tl v
  )
{
  let (hd, tl) = nlist_hd_tl sq j n input;
  unfold (nlist_hd_tl_post p sq n input pm v (hd, tl));
  unfold (nlist_hd_tl_post' p sq n input pm v hd tl);
  Trade.elim_hyp_l _ _ _;
  tl
}

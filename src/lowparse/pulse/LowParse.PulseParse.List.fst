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

(* ============================================================================ *)
(* l2r safe writer for byte-length-bounded lists                                *)
(* ============================================================================ *)

(* Pure helper lemmas *)

let rec splitAt_append_list (#a: Type) (i: nat) (l: list a)
  : Lemma (requires i <= L.length l)
    (ensures (Ghost.reveal l == L.append (fst (L.splitAt i l)) (snd (L.splitAt i l))))
    (decreases i)
  = if i = 0 then ()
    else (match l with x :: xs -> splitAt_append_list (i - 1) xs)

let rec splitAt_fst_snoc (#a: Type) (i: nat) (l: list a)
  : Lemma (requires i < L.length l)
    (ensures (fst (L.splitAt (i + 1) l) == L.append (fst (L.splitAt i l)) [L.index l i]))
    (decreases i)
  = if i = 0 then ()
    else (match l with x :: xs -> splitAt_fst_snoc (i - 1) xs)

let rec splitAt_hd_loc (#a: Type) (i: nat) (l: list a)
  : Lemma (requires i < L.length l)
    (ensures (L.lemma_splitAt_snd_length i l; L.hd (snd (L.splitAt i l)) == L.index l i))
    (decreases i)
  = if i = 0 then ()
    else (match l with x :: xs -> splitAt_hd_loc (i - 1) xs)

let rec splitAt_tl_loc (#a: Type) (i: nat) (l: list a)
  : Lemma (requires i < L.length l)
    (ensures (L.lemma_splitAt_snd_length i l; L.tl (snd (L.splitAt i l)) == snd (L.splitAt (i + 1) l)))
    (decreases i)
  = if i = 0 then ()
    else (match l with x :: xs -> splitAt_tl_loc (i - 1) xs)

(* The snoc-step identity used to extend the committed prefix bytes. *)
let snoc_step_lemma
  (#k: parser_kind) (#t: Type) (p: parser k t) (s: serializer p)
  (l: list t) (i: nat)
  : Lemma
    (requires (serialize_list_precond k /\ i < L.length l))
    (ensures (
      serialize (serialize_list p s) (fst (L.splitAt (i + 1) l)) ==
      Seq.append
        (serialize (serialize_list p s) (fst (L.splitAt i l)))
        (serialize s (L.index l i))))
  = splitAt_fst_snoc i l;
    serialize_list_append p s (fst (L.splitAt i l)) [L.index l i];
    serialize_list_singleton p s (L.index l i)

(* If the i-th element does not fit in the remaining room, the whole list does
   not fit. *)
let failure_length_lemma
  (#k: parser_kind) (#t: Type) (p: parser k t) (s: serializer p)
  (l: list t) (i: nat) (off: nat) (outlen: nat)
  : Lemma
    (requires (
      serialize_list_precond k /\ i < L.length l /\
      off == Seq.length (serialize (serialize_list p s) (fst (L.splitAt i l))) /\
      off <= outlen /\
      outlen - off < Seq.length (serialize s (L.index l i))))
    (ensures (outlen < Seq.length (serialize (serialize_list p s) l)))
  = splitAt_append_list i l;
    L.lemma_splitAt_snd_length i l;
    splitAt_hd_loc i l;
    splitAt_tl_loc i l;
    let pre = fst (L.splitAt i l) in
    let suf = snd (L.splitAt i l) in
    assert (Cons? suf);
    assert (suf == L.hd suf :: L.tl suf);
    serialize_list_append p s pre suf;
    serialize_list_cons p s (L.hd suf) (L.tl suf)

(* Local copy of the prefix-slice content lemma (originally in Combinators). *)
let slice_append_prefix (#a:Type) (x y: Seq.seq a) (j: nat)
  : Lemma
    (j <= Seq.length y ==>
      Seq.slice (Seq.append x y) 0 (Seq.length x + j) == Seq.append x (Seq.slice y 0 j))
  = if j <= Seq.length y
    then Seq.lemma_eq_intro (Seq.slice (Seq.append x y) 0 (Seq.length x + j)) (Seq.append x (Seq.slice y 0 j))
    else ()

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn l2r_safe_writer_list
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (#el #eh: Type0)
  (#elem_vmatch: el -> eh -> slprop)
  (#elem_conv: eh -> GTot (option t))
  (ew: PPB.l2r_safe_writer elem_vmatch s elem_conv)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0))
: PPB.l2r_safe_writer
    (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv))
    (serialize_list p s)
    (fun (x: list t) -> Some x)
=
  (x: PPVCL.vclist_lowtype el)
  (#y: Ghost.erased (list t))
  (out: slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
{
  match x {
    None -> {
      unfold (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (None #(SZ.t & V.vec el)) (Ghost.reveal y));
      serialize_list_nil p s;
      perr := false;
      fold (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (None #(SZ.t & V.vec el)) (Ghost.reveal y));
      rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (None #(SZ.t & V.vec el)) (Ghost.reveal y))
        as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal y));
      assert (pure (Seq.equal (Seq.slice (Ghost.reveal v) 0 0) (serialize (serialize_list p s) (Ghost.reveal y))));
      0sz
    }
    Some yy -> {
      unfold (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (Some yy) (Ghost.reveal y));
      let n = fst yy;
      with ss. assert (
        V.pts_to (snd yy) ss **
        SM.seq_list_match ss (Ghost.reveal y) (PPB.vmatch_conv elem_vmatch elem_conv));
      V.pts_to_len (snd yy);
      SM.seq_list_match_length (PPB.vmatch_conv elem_vmatch elem_conv) ss (Ghost.reveal y);
      SM.seq_list_match_seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Ghost.reveal y);
      SM.seq_seq_match_empty_intro (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) 0;
      perr := false;
      serialize_list_nil p s;
      S.pts_to_len out;
      let mut pi = 0sz;
      let mut poff = 0sz;
      while (
        let e = !perr;
        let i = !pi;
        ((not e) && SZ.lt i n)
      )
      invariant exists* (i: SZ.t) (off: SZ.t) (e: bool) (vout: Seq.seq byte) .
        R.pts_to pi i ** R.pts_to poff off ** R.pts_to perr e **
        S.pts_to out vout **
        V.pts_to (snd yy) ss **
        SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) 0 (SZ.v i) **
        SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i) (SZ.v n) **
        pure (
          SZ.v n == L.length (Ghost.reveal y) /\
          Seq.length ss == SZ.v n /\
          SZ.v i <= SZ.v n /\
          Seq.length vout == Seq.length (Ghost.reveal v) /\
          SZ.v off <= Seq.length vout /\
          SZ.v off == Seq.length (serialize (serialize_list p s) (fst (L.splitAt (SZ.v i) (Ghost.reveal y)))) /\
          Seq.slice vout 0 (SZ.v off) == serialize (serialize_list p s) (fst (L.splitAt (SZ.v i) (Ghost.reveal y))) /\
          (e == true ==> (SZ.v i < SZ.v n /\ Seq.length (Ghost.reveal v) < Seq.length (serialize (serialize_list p s) (Ghost.reveal y))))
        )
      {
        let i = !pi;
        let off = !poff;
        with vout. assert (
          S.pts_to out vout **
          SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) 0 (SZ.v i) **
          SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i) (SZ.v n));
        let xi = V.op_Array_Access (snd yy) i;
        SM.seq_seq_match_dequeue_left (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i) (SZ.v n);
        Seq.lemma_seq_of_list_index (Ghost.reveal y) (SZ.v i);
        rewrite (PPB.vmatch_conv elem_vmatch elem_conv (Seq.index ss (SZ.v i)) (Seq.index (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i)))
          as (PPB.vmatch_conv elem_vmatch elem_conv xi (Seq.index (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i)));
        PPB.elim_vmatch_conv elem_vmatch elem_conv xi (Seq.index (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i));
        with vm_i. assert (
          elem_vmatch xi vm_i **
          pure (elem_conv vm_i == Some (Seq.index (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i))));
        S.pts_to_len out;
        let left, right = S.split out off;
        S.pts_to_len right;
        let r = ew xi right perr;
        S.pts_to_len right;
        with vr ee. assert (
          S.pts_to right vr **
          elem_vmatch xi vm_i **
          R.pts_to perr ee **
          pure (PPB.l2r_safe_writer_postcond elem_conv s vm_i vr r ee));
        S.join left right out;
        with vout2. assert (S.pts_to out vout2);
        PPB.intro_vmatch_conv elem_vmatch elem_conv xi vm_i (Seq.index (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i));
        let ei = !perr;
        if ei {
          failure_length_lemma p s (Ghost.reveal y) (SZ.v i) (SZ.v off) (Seq.length vout2);
          assert (pure (Seq.equal (Seq.slice vout2 0 (SZ.v off)) (Seq.slice vout 0 (SZ.v off))));
          SM.seq_seq_match_enqueue_left (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i + 1) (SZ.v n) xi (Seq.index (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i));
          rewrite (SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) ((SZ.v i + 1) - 1) (SZ.v n))
            as (SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i) (SZ.v n));
        } else {
          let i1 = SZ.add i 1sz;
          SM.seq_seq_match_enqueue_right (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) 0 (SZ.v i) xi (Seq.index (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i));
          snoc_step_lemma p s (Ghost.reveal y) (SZ.v i);
          slice_append_prefix (Seq.slice vout 0 (SZ.v off)) vr (SZ.v r);
          assert (pure (Seq.equal (Seq.slice vout2 0 (SZ.v off + SZ.v r)) (serialize (serialize_list p s) (fst (L.splitAt (SZ.v i + 1) (Ghost.reveal y))))));
          rewrite (SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) 0 (SZ.v i + 1))
            as (SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) 0 (SZ.v i1));
          rewrite (SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i + 1) (SZ.v n))
            as (SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i1) (SZ.v n));
          poff := SZ.add off r;
          pi := i1;
        }
      };
      let i = !pi;
      let e = !perr;
      let off = !poff;
      with vout. assert (
        S.pts_to out vout **
        SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) 0 (SZ.v i) **
        SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) (SZ.v i) (SZ.v n));
      SM.seq_seq_match_join (PPB.vmatch_conv elem_vmatch elem_conv) ss (Seq.seq_of_list (Ghost.reveal y)) 0 (SZ.v i) (SZ.v n);
      SM.seq_seq_match_seq_list_match (PPB.vmatch_conv elem_vmatch elem_conv) ss (Ghost.reveal y);
      fold (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (Some yy) (Ghost.reveal y));
      rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (Some yy) (Ghost.reveal y))
        as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal y));
      if e {
        off
      } else {
        L.lemma_splitAt_snd_length (SZ.v n) (Ghost.reveal y);
        splitAt_append_list (SZ.v n) (Ghost.reveal y);
        assert (pure (snd (L.splitAt (SZ.v n) (Ghost.reveal y)) == []));
        L.append_l_nil (fst (L.splitAt (SZ.v n) (Ghost.reveal y)));
        assert (pure (fst (L.splitAt (SZ.v n) (Ghost.reveal y)) == Ghost.reveal y));
        off
      }
    }
  }
}

#pop-options

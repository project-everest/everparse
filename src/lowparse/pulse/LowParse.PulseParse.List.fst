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

(* ============================================================================ *)
(* l2r safe writer for count-prefixed variable-length lists (vclist)            *)
(* ============================================================================ *)

module U32 = FStar.UInt32
open LowParse.Spec.VCList

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

(* The serialized form of a vclist decomposes as HEADER (count) ++ BODY (list). *)
let serialize_vclist_decomp
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp { lk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 })
  (l: vlarray t min max)
: Lemma
  (ensures (
    serialize (serialize_vclist min max ls s) l ==
    Seq.append (serialize ls (U32.uint_to_t (L.length l))) (serialize (serialize_list p s) l)
  ))
= serialize_nlist_serialize_list (L.length l) s l

(* From the header/body writer facts (and the structural fact that the final
   output is HEADER ++ BODY), derive the success-form serializer facts about the
   full vclist serialization. *)
let vclist_compose_lemma
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp { lk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 })
  (l: vlarray t min max)
  (cnt: U32.t)
  (out': Seq.seq byte)
  (body_out: Seq.seq byte)
  (finalsz: SZ.t)
  (hsz: nat)
  (he be: bool)
: Lemma
  (requires (
    U32.v cnt == L.length l /\
    (he == true ==> (
      Seq.length out' < Seq.length (serialize ls cnt) /\ be == true
    )) /\
    (he == false ==> (
      hsz == Seq.length (serialize ls cnt) /\
      out' == Seq.append (serialize ls cnt) body_out /\
      (be == (Seq.length body_out < Seq.length (serialize (serialize_list p s) l))) /\
      (be == false ==> (
        SZ.v finalsz == hsz + Seq.length (serialize (serialize_list p s) l) /\
        Seq.slice body_out 0 (Seq.length (serialize (serialize_list p s) l)) == serialize (serialize_list p s) l
      ))
    ))
  ))
  (ensures (
    be == (Seq.length out' < Seq.length (serialize (serialize_vclist min max ls s) l)) /\
    (be == false ==> (SZ.v finalsz == Seq.length (serialize (serialize_vclist min max ls s) l) /\ Seq.slice out' 0 (Seq.length (serialize (serialize_vclist min max ls s) l)) == serialize (serialize_vclist min max ls s) l))
  ))
= serialize_vclist_decomp min max ls s l;
  let header = serialize ls cnt in
  let body = serialize (serialize_list p s) l in
  Seq.lemma_len_append header body;
  if he
  then ()
  else begin
    Seq.lemma_len_append header body_out;
    if be
    then ()
    else slice_append_prefix header body_out (Seq.length body)
  end

(* When conv succeeds (count in [min,max]), the success-form facts coincide with
   the full [l2r_safe_writer_postcond]. *)
let vclist_postcond_lemma
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp { lk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 })
  (l: vlarray t min max)
  (v': Seq.seq byte)
  (sz: SZ.t)
  (err: bool)
: Lemma
  (requires (
    err == (Seq.length v' < Seq.length (serialize (serialize_vclist min max ls s) l)) /\
    (err == false ==> (SZ.v sz == Seq.length (serialize (serialize_vclist min max ls s) l) /\ Seq.slice v' 0 (Seq.length (serialize (serialize_vclist min max ls s) l)) == serialize (serialize_vclist min max ls s) l))
  ))
  (ensures (
    PPB.l2r_safe_writer_postcond (PPVCL.vclist_conv min max) (serialize_vclist min max ls s) (l <: list t) v' sz err
  ))
= assert (PPVCL.vclist_conv min max (l <: list t) == Some l)

(* The core writer assuming the count is valid (conv = Some): write the count
   header with [cw], then split off the header and write the element list body
   with [l2r_safe_writer_list]. *)
inline_for_extraction
fn l2r_safe_writer_vclist_aux
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max })
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp)
  (cw: PPB.l2r_safe_writer (LPS.eq_as_slprop U32.t) ls (PPB.leaf_conv U32.t))
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (#el #em: Type0)
  (#elem_vmatch: el -> em -> slprop)
  (#elem_conv: em -> GTot (option t))
  (ew: PPB.l2r_safe_writer elem_vmatch s elem_conv)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0))
  (u: squash (lk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
  (x: PPVCL.vclist_lowtype el)
  (cnt: U32.t)
  (#y: Ghost.erased (vlarray t (U32.v min) (U32.v max)))
  (out: slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: R.ref bool)
requires
  (exists* err.
    PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal y <: list t) **
    S.pts_to out v ** R.pts_to perr err) **
  pure (U32.v cnt == L.length (Ghost.reveal y))
returns sz: SZ.t
ensures
  exists* v' err.
    PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal y <: list t) **
    S.pts_to out v' ** R.pts_to perr err **
    pure (
      err == (Seq.length v' < Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal y))) /\
      (err == false ==> (SZ.v sz == Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal y)) /\ Seq.slice v' 0 (Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal y))) == serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal y)))
    )
{
  S.pts_to_len out;
  (* ---- write the count header ---- *)
  fold (LPS.eq_as_slprop U32.t cnt cnt);
  let hsz = cw cnt out perr;
  unfold (LPS.eq_as_slprop U32.t cnt cnt);
  with vmid herr0. assert (
    S.pts_to out vmid ** R.pts_to perr herr0 **
    pure (PPB.l2r_safe_writer_postcond (PPB.leaf_conv U32.t) ls cnt vmid hsz herr0));
  S.pts_to_len out;
  let he = !perr;
  if he {
    (* header did not fit: the whole vclist does not fit either *)
    vclist_compose_lemma (U32.v min) (U32.v max) ls s (Ghost.reveal y) cnt vmid (Seq.empty #byte) hsz (Seq.length (serialize ls cnt)) true true;
    hsz
  } else {
    (* header fit: hsz == length (serialize ls cnt), slice vmid 0 hsz == header *)
    let hdr, body = S.split out hsz;
    with vhdr. assert (S.pts_to hdr vhdr);
    S.pts_to_len hdr;
    S.pts_to_len body;
    assert (pure (vhdr == serialize ls cnt));
    let bsz = l2r_safe_writer_list s ew () x body perr;
    with vbody berr. assert (
      S.pts_to body vbody ** R.pts_to perr berr **
      pure (PPB.l2r_safe_writer_postcond (fun (xx: list t) -> Some xx) (serialize_list p s) (Ghost.reveal y <: list t) vbody bsz berr));
    S.pts_to_len body;
    S.join hdr body out;
    with vout'. assert (S.pts_to out vout');
    S.pts_to_len out;
    assert (pure (vout' == Seq.append (serialize ls cnt) vbody));
    let be = !perr;
    if be {
      vclist_compose_lemma (U32.v min) (U32.v max) ls s (Ghost.reveal y) cnt vout' vbody hsz (SZ.v hsz) false true;
      hsz
    } else {
      SZ.fits_lte (SZ.v hsz + SZ.v bsz) (Seq.length vout');
      let fsz = SZ.add hsz bsz;
      vclist_compose_lemma (U32.v min) (U32.v max) ls s (Ghost.reveal y) cnt vout' vbody fsz (SZ.v hsz) false false;
      fsz
    }
  }
}

inline_for_extraction
fn l2r_safe_writer_vclist
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max })
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp)
  (cw: PPB.l2r_safe_writer (LPS.eq_as_slprop U32.t) ls (PPB.leaf_conv U32.t))
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (#el #em: Type0)
  (#elem_vmatch: el -> em -> slprop)
  (#elem_conv: em -> GTot (option t))
  (ew: PPB.l2r_safe_writer elem_vmatch s elem_conv)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0))
  (u: squash (lk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: PPB.l2r_safe_writer
    (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv))
    (serialize_vclist (U32.v min) (U32.v max) ls s)
    (PPVCL.vclist_conv (U32.v min) (U32.v max))
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
      fold (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (None #(SZ.t & V.vec el)) (Ghost.reveal y));
      if (U32.eq min 0ul) {
        let yv : Ghost.erased (vlarray t (U32.v min) (U32.v max)) = Ghost.hide (Ghost.reveal y <: vlarray t (U32.v min) (U32.v max));
        rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (None #(SZ.t & V.vec el)) (Ghost.reveal y))
          as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal yv <: list t));
        let sz = l2r_safe_writer_vclist_aux min max ls cw s ew () () x 0ul out perr;
        with v' err. assert (
          S.pts_to out v' ** R.pts_to perr err **
          pure (
            err == (Seq.length v' < Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal yv))) /\
            (err == false ==> (SZ.v sz == Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal yv)) /\ Seq.slice v' 0 (Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal yv))) == serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal yv)))));
        vclist_postcond_lemma (U32.v min) (U32.v max) ls s (Ghost.reveal yv) v' sz err;
        rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal yv <: list t))
          as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal y));
        sz
      } else {
        perr := true;
        rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (None #(SZ.t & V.vec el)) (Ghost.reveal y))
          as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal y));
        assert (pure (PPVCL.vclist_conv (U32.v min) (U32.v max) (Ghost.reveal y) == None));
        0sz
      }
    }
    Some yy -> {
      unfold (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (Some yy) (Ghost.reveal y));
      let n = fst yy;
      with ss. assert (
        V.pts_to (snd yy) ss **
        SM.seq_list_match ss (Ghost.reveal y) (PPB.vmatch_conv elem_vmatch elem_conv));
      fold (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (Some yy) (Ghost.reveal y));
      SZ.fits_u64_implies_fits_32 ();
      let smin = SZ.uint32_to_sizet min;
      let smax = SZ.uint32_to_sizet max;
      if (SZ.lte smin n && SZ.lte n smax) {
        let cnt = SZ.sizet_to_uint32 n;
        let yv : Ghost.erased (vlarray t (U32.v min) (U32.v max)) = Ghost.hide (Ghost.reveal y <: vlarray t (U32.v min) (U32.v max));
        rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (Some yy) (Ghost.reveal y))
          as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal yv <: list t));
        let sz = l2r_safe_writer_vclist_aux min max ls cw s ew () () x cnt out perr;
        with v' err. assert (
          S.pts_to out v' ** R.pts_to perr err **
          pure (
            err == (Seq.length v' < Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal yv))) /\
            (err == false ==> (SZ.v sz == Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal yv)) /\ Seq.slice v' 0 (Seq.length (serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal yv))) == serialize (serialize_vclist (U32.v min) (U32.v max) ls s) (Ghost.reveal yv)))));
        vclist_postcond_lemma (U32.v min) (U32.v max) ls s (Ghost.reveal yv) v' sz err;
        rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal yv <: list t))
          as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal y));
        sz
      } else {
        perr := true;
        rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) (Some yy) (Ghost.reveal y))
          as (PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) x (Ghost.reveal y));
        assert (pure (PPVCL.vclist_conv (U32.v min) (U32.v max) (Ghost.reveal y) == None));
        0sz
      }
    }
  }
}

#pop-options

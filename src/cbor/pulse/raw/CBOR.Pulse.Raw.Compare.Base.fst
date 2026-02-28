module CBOR.Pulse.Raw.Compare.Base
#lang-pulse
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Sort.Merge.Slice
module SM = Pulse.Lib.SeqMatch.Util
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module I16 = FStar.Int16
module Trade = Pulse.Lib.Trade.Util

let rec lex_compare
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
: Tot int
  (decreases l1)
= match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | a1 :: q1, [] -> 1
  | a1 :: q1, a2 :: q2 ->
    let c = compare a1 a2 in
    if c = 0
    then lex_compare compare q1 q2
    else c

let rec lex_compare'
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
  (i1 i2: nat)
: Tot int
  (decreases (let n = List.Tot.length l1 - i1 in if n < 0 then 0 else (n <: nat)))
= if i1 > List.Tot.length l1 || i2 > List.Tot.length l2
  then 0 (* dummy *)
  else if i1 = List.Tot.length l1
  then
    if i2 = List.Tot.length l2
    then 0
    else -1
  else if i2 = List.Tot.length l2
  then 1
  else
    let a1 = List.Tot.index l1 i1 in
    let a2 = List.Tot.index l2 i2 in
    let c = compare a1 a2 in
    if c = 0
    then lex_compare' compare l1 l2 (i1 + 1) (i2 + 1)
    else c

let rec list_length_append_cons
  (#t: Type)
  (ll: list t)
  (a: t)
  (lr: list t)
: Lemma
  (ensures (
    let l = List.Tot.append ll (a :: lr) in
    let i = List.Tot.length ll in
    i < List.Tot.length l /\
    List.Tot.index l i == a
  ))
  (decreases ll)
= List.Tot.append_length ll (a :: lr);
  match ll with
  | [] -> ()
  | a' :: ll' ->
    list_length_append_cons ll' a lr

let rec lex_compare'_correct'
  (#t: Type)
  (compare: t -> t -> int)
  (ll1 lr1 ll2 lr2: list t)
: Lemma
  (ensures (
    lex_compare' compare (List.Tot.append ll1 lr1) (List.Tot.append ll2 lr2) (List.Tot.length ll1) (List.Tot.length ll2) == lex_compare compare lr1 lr2
  ))
  (decreases lr1)
= List.Tot.append_length ll1 lr1;
  List.Tot.append_length ll2 lr2;
  match lr1 with
  | [] -> ()
  | a1 :: q1 ->
    match lr2 with
    | [] -> ()
    | a2 :: q2 ->
      list_length_append_cons ll1 a1 q1;
      list_length_append_cons ll2 a2 q2;
      List.Tot.append_assoc ll1 [a1] q1;
      List.Tot.append_assoc ll2 [a2] q2;
      let c = compare a1 a2 in
      if c = 0
      then lex_compare'_correct' compare (List.Tot.append ll1 [a1]) q1 (List.Tot.append ll2 [a2]) q2
      else ()

let lex_compare'_correct
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
: Lemma
  (lex_compare' compare l1 l2 0 0 == lex_compare compare l1 l2)
= lex_compare'_correct' compare [] l1 [] l2

noeq
type with_perm (t: Type0) = {
  v: t;
  p: perm;
}

let vmatch_slice_list
  (#tl #th: Type)
  (vmatch: tl -> th -> slprop)
  (sl: with_perm (S.slice tl))
  (sh: list th)
: slprop
= exists* vl . pts_to sl.v #sl.p vl **
  SM.seq_list_match vl sh vmatch

let same_sign (x1 x2: int) : Tot prop =
  (x1 < 0 <==> x2 < 0) /\
  (x1 == 0 <==> x2 == 0)

inline_for_extraction
fn impl_lex_compare
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: Ghost.erased (th -> th -> int))
  (impl_compare: A.impl_compare_t vmatch compare)
: A.impl_compare_t u#0 u#0 #_ #_ (vmatch_slice_list vmatch) (lex_compare compare)
= (s1: _)
  (s2: _)
  (#v1: _)
  (#v2: _)
{
  let mut pi1 = 0sz;
  let mut pi2 = 0sz;
  unfold (vmatch_slice_list vmatch s1 v1);
  unfold (vmatch_slice_list vmatch s2 v2);
  let n1 = S.len s1.v;
  let n2 = S.len s2.v;
  S.pts_to_len s1.v;
  S.pts_to_len s2.v;
  with c1 . assert (pts_to s1.v #s1.p c1 ** SM.seq_list_match c1 v1 vmatch);
  with c2 . assert (pts_to s2.v #s2.p c2 ** SM.seq_list_match c2 v2 vmatch);
  SM.seq_list_match_length vmatch c1 v1;
  SM.seq_list_match_length vmatch c2 v2;
  lex_compare'_correct compare v1 v2;
  let mut pres = (if SZ.lt 0sz n1 then if SZ.lt 0sz n2 then 0s else 1s else if SZ.lt 0sz n2 then -1s else 0s);
  while (
    let res = !pres;
    let i1 = !pi1;
    let i2 = !pi2;
    (res = 0s && SZ.lt i1 n1)
  ) invariant cont . exists* res i1 i2 . (
    pts_to s1.v #s1.p c1 ** SM.seq_list_match c1 v1 vmatch **
    pts_to s2.v #s2.p c2 ** SM.seq_list_match c2 v2 vmatch **
    pts_to pres res **
    pts_to pi1 i1 **
    pts_to pi2 i2 **
    pure (
      SZ.v i1 <= SZ.v n1 /\
      SZ.v i2 <= SZ.v n2 /\
      same_sign (lex_compare compare v1 v2) (if res = 0s then lex_compare' compare v1 v2 (SZ.v i1) (SZ.v i2) else I16.v res) /\
      (res == 0s ==> (SZ.lt i1 n1 == SZ.lt i2 n2))
    ) ** pure (
      cont == (res = 0s && SZ.lt i1 n1)
    )
  ) {
    let i1 = !pi1;
    let x1 = S.op_Array_Access s1.v i1;
    SM.seq_list_match_index_trade vmatch c1 v1 (SZ.v i1);
    Trade.rewrite_with_trade
      (vmatch (Seq.index c1 (SZ.v i1)) (List.Tot.index v1 (SZ.v i1)))
      (vmatch x1 (List.Tot.index v1 (SZ.v i1)));
    Trade.trans _ _ (SM.seq_list_match c1 v1 vmatch);
    let i2 = !pi2;
    let x2 = S.op_Array_Access s2.v i2;
    SM.seq_list_match_index_trade vmatch c2 v2 (SZ.v i2);
    Trade.rewrite_with_trade
      (vmatch (Seq.index c2 (SZ.v i2)) (List.Tot.index v2 (SZ.v i2)))
      (vmatch x2 (List.Tot.index v2 (SZ.v i2)));
    Trade.trans _ _ (SM.seq_list_match c2 v2 vmatch);
    let c = impl_compare x1 x2;
    Trade.elim _ (SM.seq_list_match c1 v1 vmatch);
    Trade.elim _ (SM.seq_list_match c2 v2 vmatch);
    if (c = 0s) {
      let i1' = SZ.add i1 1sz;
      let i2' = SZ.add i2 1sz;
      let ci1' = SZ.lt i1' n1;
      let ci2' = SZ.lt i2' n2;
      if (ci2' && not ci1') {
        pres := -1s;
      } else if (ci1' && not ci2') {
        pres := 1s;
      } else {
        pi1 := i1';
        pi2 := i2';
      }
    } else {
      pres := c;
    }
  };
  fold (vmatch_slice_list vmatch s1 v1);
  fold (vmatch_slice_list vmatch s2 v2);
  !pres
}

module I16 = FStar.Int16

inline_for_extraction
let impl_compare_scalar_t
  (#th: Type)
  (compare: th -> th -> int)
= (x1: th) ->
  (x2: th) ->
  stt I16.t
    emp
    (fun res -> pure (
      let v = compare x1 x2 in
      (v < 0 <==> I16.v res < 0) /\
      (v > 0 <==> I16.v res > 0)
    ))

let eq_as_slprop (t: Type) (x x': t) : slprop = pure (x == x')

inline_for_extraction
fn impl_compare_of_impl_compare_scalar
  (#th: Type0)
  (compare: Ghost.erased (th -> th -> int))
  (impl: impl_compare_scalar_t compare)
: A.impl_compare_t u#0 u#0 #_ #_ (eq_as_slprop th) (Ghost.reveal compare)
= (x1: _)
  (x2: _)
  (#v1: _)
  (#v2: _)
{
  unfold (eq_as_slprop th x1 v1);
  unfold (eq_as_slprop th x2 v2);
  let res = impl x1 x2;
  fold (eq_as_slprop th x1 v1);
  fold (eq_as_slprop th x2 v2);
  res
}

let vmatch_slice_list_scalar
  (#th: Type)
  (sl: with_perm (S.slice th))
  (sh: list th)
: slprop
= pts_to sl.v #sl.p (Seq.seq_of_list sh)

module Trade = Pulse.Lib.Trade.Util

ghost
fn rec seq_list_match_eq_as_slprop
  (#th: Type0)
  (s: Seq.seq th)
  (l: list th)
requires
  SM.seq_list_match s l (eq_as_slprop th)
ensures
  pure (s == Seq.seq_of_list l)
decreases l
{
  SM.seq_list_match_length (eq_as_slprop th) s l;
  if (Nil? l) {
    SM.seq_list_match_nil_elim s l (eq_as_slprop th);
    assert (pure (Seq.equal s (Seq.seq_of_list l)));
  } else {
    SM.seq_list_match_cons_elim s l (eq_as_slprop th);
    unfold (eq_as_slprop th (Seq.head s) (List.Tot.hd l));
    Seq.cons_head_tail s;
    seq_list_match_eq_as_slprop (Seq.tail s) (List.Tot.tl l)
  }
}

ghost
fn rec eq_as_slprop_seq_list_match
  (#th: Type0)
  (s: Seq.seq th)
  (l: list th)
requires
  pure (s == Seq.seq_of_list l)
ensures
  SM.seq_list_match s l (eq_as_slprop th)
decreases l
{
  match l {
    [] -> {
      SM.seq_list_match_nil_intro s l (eq_as_slprop th)
    }
    hd :: tl -> {
      Seq.cons_head_tail s;
      assert (pure (Seq.equal (Seq.tail s) (Seq.seq_of_list tl)));
      eq_as_slprop_seq_list_match (Seq.tail s) tl;
      fold (eq_as_slprop th (Seq.head s) hd);
      SM.seq_list_match_cons_intro (Seq.head s) hd (Seq.tail s) tl (eq_as_slprop th);
      rewrite each (hd :: tl) as l;
      rewrite each Seq.cons (Seq.head s) (Seq.tail s) as s;
      ()
    }
  }
}

ghost
fn vmatch_slice_list_of_vmatch_slice_list_scalar
  (#th: Type)
  (sl: with_perm (S.slice th))
  (sh: list th)
requires
  vmatch_slice_list_scalar sl sh
ensures
  vmatch_slice_list (eq_as_slprop th) sl sh
{
  unfold (vmatch_slice_list_scalar sl sh);
  eq_as_slprop_seq_list_match (Seq.seq_of_list sh) sh;
  fold (vmatch_slice_list (eq_as_slprop th) sl sh)
}

ghost
fn vmatch_slice_list_scalar_of_vmatch_slice_list
  (#th: Type)
  (sl: with_perm (S.slice th))
  (sh: list th)
requires
  vmatch_slice_list (eq_as_slprop th) sl sh
ensures
  vmatch_slice_list_scalar sl sh
{
  unfold (vmatch_slice_list (eq_as_slprop th) sl sh);
  seq_list_match_eq_as_slprop _ sh;
  fold (vmatch_slice_list_scalar sl sh)
}

ghost
fn vmatch_slice_list_of_vmatch_slice_list_scalar_trade
  (#th: Type)
  (sl: with_perm (S.slice th))
  (sh: list th)
requires
  vmatch_slice_list_scalar sl sh
ensures
  vmatch_slice_list (eq_as_slprop th) sl sh **
  Trade.trade
    (vmatch_slice_list (eq_as_slprop th) sl sh)
    (vmatch_slice_list_scalar sl sh)
{
  vmatch_slice_list_of_vmatch_slice_list_scalar sl sh;
  intro
    (Trade.trade
      (vmatch_slice_list (eq_as_slprop th) sl sh)
      (vmatch_slice_list_scalar sl sh)
    )
    #emp
    fn _
  {
    vmatch_slice_list_scalar_of_vmatch_slice_list sl sh
  };
}

inline_for_extraction
fn impl_lex_compare_scalar
  (#th: Type0)
  (compare: Ghost.erased (th -> th -> int))
  (impl_compare: impl_compare_scalar_t compare)
: A.impl_compare_t u#0 u#0 #_ #_ (vmatch_slice_list_scalar) (lex_compare compare)
= (s1: _)
  (s2: _)
  (#v1: _)
  (#v2: _)
{
  vmatch_slice_list_of_vmatch_slice_list_scalar_trade s1 v1;
  vmatch_slice_list_of_vmatch_slice_list_scalar_trade s2 v2;
  let res =
    impl_lex_compare _ _
      (impl_compare_of_impl_compare_scalar compare impl_compare)
      s1 s2;
  Trade.elim _ (vmatch_slice_list_scalar s1 _);
  Trade.elim _ (vmatch_slice_list_scalar s2 _);
  res
}

inline_for_extraction
fn lex_compare_slices
  (#th: Type0)
  (compare: Ghost.erased (th -> th -> int))
  (impl_compare: impl_compare_scalar_t compare)
  (s1: S.slice th)
  (s2: S.slice th)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased (Seq.seq th))
  (#v2: Ghost.erased (Seq.seq th))
requires
  pts_to s1 #p1 v1 ** pts_to s2 #p2 v2
returns res: I16.t
ensures
  pts_to s1 #p1 v1 ** pts_to s2 #p2 v2 ** pure (
    same_sign (I16.v res) (lex_compare compare (Seq.seq_to_list v1) (Seq.seq_to_list v2))
  )
{
  let sp1 = Mkwith_perm s1 p1;
  let sp2 = Mkwith_perm s2 p2;
  Trade.rewrite_with_trade
    (pts_to s1 #p1 v1)
    (vmatch_slice_list_scalar sp1 (Seq.seq_to_list v1));
  Trade.rewrite_with_trade
    (pts_to s2 #p2 v2)
    (vmatch_slice_list_scalar sp2 (Seq.seq_to_list v2));
  let res = impl_lex_compare_scalar compare impl_compare sp1 sp2;
  Trade.elim _ (pts_to s1 #p1 v1);
  Trade.elim _ (pts_to s2 #p2 v2);
  res
}

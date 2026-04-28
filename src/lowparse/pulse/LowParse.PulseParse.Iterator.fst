module LowParse.PulseParse.Iterator
#lang-pulse
include LowParse.PulseParse.Base
include LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module B = Pulse.Lib.Box
open Pulse.Lib.Trade

inline_for_extraction
let share_t
  (#t1 #t2: Type)
  (vmatch: perm -> t1 -> t2 -> slprop)
=
  (x1: t1) ->
  (#p: perm) ->
  (#x2: t2) ->
  stt_ghost unit emp_inames
  (vmatch p x1 x2)
  (fun _ ->
    let open FStar.Real in
    vmatch (p /. 2.0R) x1 x2 ** vmatch (p /. 2.0R) x1 x2
  )

inline_for_extraction
let gather_t
  (#t1 #t2: Type)
  (vmatch: perm -> t1 -> t2 -> slprop)
=
  (x1: t1) ->
  (#p: perm) ->
  (#x2: t2) ->
  (#p': perm) ->
  (#x2': t2) ->
  stt_ghost unit emp_inames
  (vmatch p x1 x2 ** vmatch p' x1 x2')
  (fun _ ->
    let open FStar.Real in
    vmatch (p +. p') x1 x2 **
    pure (x2 == x2')
  )

noeq
type base_iterator ([@@@strictly_positive] t: Type) =
| Empty
| Singleton: (sp: perm) -> (sv: perm) -> (sr: ref t) -> base_iterator t
| Slice: (sp: perm) -> (sv: perm) -> (ss: S.slice t) -> base_iterator t
| Serialized: (sp: perm) -> (count: SZ.t) -> (payload: S.slice U8.t) -> base_iterator t

noeq
type iterator ([@@@strictly_positive] t: Type) =
| Base of base_iterator t
| Append:
  (depth: Ghost.erased nat) ->
  (count: SZ.t) ->
  (before: base_iterator t) ->
  (ap: perm) ->
  (after: ref (iterator t)) ->
  iterator t

let iterator_depth (#t: Type) (i: iterator t) : GTot nat =
  match i with
  | Base _ -> 0
  | Append depth _ _ _ _ -> Ghost.reveal depth

module SM = Pulse.Lib.SeqMatch

let base_iterator_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
: Tot slprop
= match i with
  | Empty -> pure (Nil? l)
  | Singleton sp sv s -> exists* x y .
    pts_to s #(pm *. sp) x **
    vmatch (pm *. sv) x y **
    pure (l == [y])
  | Slice sp sv s -> exists* l' .
    pts_to s #(pm *. sp) l' **
    SM.seq_list_match l' l (vmatch (pm *. sv))
  | Serialized sp count pl -> exists* l' .
    pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #(pm *. sp) l' **
    pure ((l' <: list u) == l)

let rec iterator_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: iterator t)
  (l: list u)
: Tot slprop
  (decreases (iterator_depth i))
= match i with
  | Base i -> base_iterator_match vmatch p pm i l
  | Append depth count before ap after ->
    exists* i1 i2 l2 .
      base_iterator_match vmatch p pm before i1 **
      pts_to after #(pm *. ap) i2 **
      iterator_match vmatch p pm i2 l2 **
      pure (
        SZ.v count <= List.Tot.length i1 + List.Tot.length l2 /\
        l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1 l2)) /\
        iterator_depth i2 < Ghost.reveal depth
      )

// Alias for iterator_match used to disambiguate gather preconditions
let iterator_match' = iterator_match

// Alias for base_iterator_match used to disambiguate in trade bodies
let base_iterator_match' = base_iterator_match

let rec lemma_splitAt_fst_length (#a: Type) (n: nat) (l: list a)
  : Lemma
    (requires n <= List.Tot.length l)
    (ensures List.Tot.length (fst (List.Tot.splitAt n l)) == n)
    (decreases n)
  = if n = 0 then () else lemma_splitAt_fst_length (n - 1) (List.Tot.tl l)

fn base_iterator_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_iterator t)
  (#l: Ghost.erased (list u))
requires base_iterator_match vmatch p pm i l
returns res: SZ.t
ensures base_iterator_match vmatch p pm i l ** pure (SZ.v res == List.Tot.length l)
{
  match i {
    Empty -> {
      unfold (base_iterator_match vmatch p pm (Empty #t) l);
      fold (base_iterator_match vmatch p pm (Empty #t) l);
      rewrite (base_iterator_match vmatch p pm (Empty #t) l)
           as (base_iterator_match vmatch p pm i l);
      0sz
    }
    Singleton sp sv s -> {
      unfold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
      fold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
      rewrite (base_iterator_match vmatch p pm (Singleton sp sv s) l)
           as (base_iterator_match vmatch p pm i l);
      1sz
    }
    Slice sp sv sl -> {
      unfold (base_iterator_match vmatch p pm (Slice sp sv sl) l);
      SM.seq_list_match_length (vmatch (pm *. sv)) _ l;
      S.pts_to_len sl;
      let res = S.len sl;
      fold (base_iterator_match vmatch p pm (Slice sp sv sl) l);
      rewrite (base_iterator_match vmatch p pm (Slice sp sv sl) l)
           as (base_iterator_match vmatch p pm i l);
      res
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match vmatch p pm (Serialized sp count pl) l);
      fold (base_iterator_match vmatch p pm (Serialized sp count pl) l);
      rewrite (base_iterator_match vmatch p pm (Serialized sp count pl) l)
           as (base_iterator_match vmatch p pm i l);
      count
    }
  }
}

fn iterator_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: iterator t)
  (#l: Ghost.erased (list u))
requires iterator_match vmatch p pm i l
returns res: SZ.t
ensures iterator_match vmatch p pm i l ** pure (SZ.v res == List.Tot.length l)
{
  match i {
    Base bi -> {
      unfold (iterator_match vmatch p pm (Base bi) l);
      let res = base_iterator_length vmatch p pm bi;
      fold (iterator_match vmatch p pm (Base bi) l);
      rewrite (iterator_match vmatch p pm (Base bi) l)
           as (iterator_match vmatch p pm i l);
      res
    }
    Append depth count before ap after -> {
      unfold (iterator_match vmatch p pm (Append depth count before ap after) l);
      with _i1 _i2 _l2 . assert (
        base_iterator_match vmatch p pm before _i1 **
        pts_to after #(pm *. ap) _i2 **
        iterator_match vmatch p pm _i2 _l2 **
        pure (
          SZ.v count <= List.Tot.length _i1 + List.Tot.length _l2 /\
          Ghost.reveal l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append _i1 _l2)) /\
          iterator_depth _i2 < Ghost.reveal depth
        )
      );
      List.Tot.append_length _i1 _l2;
      lemma_splitAt_fst_length (SZ.v count) (List.Tot.append _i1 _l2);
      fold (iterator_match vmatch p pm (Append depth count before ap after) l);
      rewrite (iterator_match vmatch p pm (Append depth count before ap after) l)
           as (iterator_match vmatch p pm i l);
      count
    }
  }
}

fn iterator_is_empty
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: iterator t)
  (#l: Ghost.erased (list u))
requires iterator_match vmatch p pm i l
returns res: bool
ensures iterator_match vmatch p pm i l ** pure (res == Nil? l)
{
  let len = iterator_length vmatch p pm i;
  (len = 0sz)
}

ghost fn pts_to_parsed_strong_prefix_share
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: S.slice byte)
  (#pm: perm) (#v: t)
requires pts_to_parsed_strong_prefix p input #pm v
ensures pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v **
        pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v
{
  unfold (pts_to_parsed_strong_prefix p input #pm v);
  S.share input;
  fold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
  fold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
}

ghost fn pts_to_parsed_strong_prefix_gather
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: S.slice byte)
  (#pm: perm) (#v: t) (#pm': perm) (#v': t)
requires pts_to_parsed_strong_prefix p input #pm v **
         pts_to_parsed_strong_prefix p input #pm' v'
ensures pts_to_parsed_strong_prefix p input #(pm +. pm') v **
        pure (v == v')
{
  unfold (pts_to_parsed_strong_prefix p input #pm v);
  unfold (pts_to_parsed_strong_prefix p input #pm' v');
  S.gather input;
  fold (pts_to_parsed_strong_prefix p input #(pm +. pm') v);
}

ghost fn rec seq_list_match_share
  (#t #u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_share: share_t vmatch)
  (c: Seq.seq t)
  (l: list u)
  (#pm: perm)
requires SM.seq_list_match c l (vmatch pm)
ensures SM.seq_list_match c l (vmatch (pm /. 2.0R)) **
        SM.seq_list_match c l (vmatch (pm /. 2.0R))
decreases l
{
  SM.seq_list_match_length (vmatch pm) c l;
  if (Nil? l) {
    SM.seq_list_match_nil_elim c l (vmatch pm);
    SM.seq_list_match_nil_intro c l (vmatch (pm /. 2.0R));
    SM.seq_list_match_nil_intro c l (vmatch (pm /. 2.0R));
  } else {
    let _ = SM.seq_list_match_cons_elim c l (vmatch pm);
    vmatch_share (Seq.head c) #pm #(List.Tot.hd l);
    seq_list_match_share vmatch vmatch_share (Seq.tail c) (List.Tot.tl l) #pm;
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd l) (Seq.tail c) (List.Tot.tl l) (vmatch (pm /. 2.0R));
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd l) (Seq.tail c) (List.Tot.tl l) (vmatch (pm /. 2.0R));
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd l :: List.Tot.tl l) (vmatch (pm /. 2.0R)))
         as (SM.seq_list_match c l (vmatch (pm /. 2.0R)));
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd l :: List.Tot.tl l) (vmatch (pm /. 2.0R)))
         as (SM.seq_list_match c l (vmatch (pm /. 2.0R)));
  }
}

ghost fn rec seq_list_match_gather
  (#t #u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_gather: gather_t vmatch)
  (c: Seq.seq t)
  (l: list u)
  (#pm: perm)
  (l': list u)
  (#pm': perm)
requires SM.seq_list_match c l (vmatch pm) **
         SM.seq_list_match c l' (vmatch pm')
ensures SM.seq_list_match c l (vmatch (pm +. pm')) **
        pure (l == l')
decreases l
{
  SM.seq_list_match_length (vmatch pm) c l;
  SM.seq_list_match_length (vmatch pm') c l';
  if (Nil? l) {
    SM.seq_list_match_nil_elim c l (vmatch pm);
    SM.seq_list_match_nil_elim c l' (vmatch pm');
    SM.seq_list_match_nil_intro c l (vmatch (pm +. pm'));
  } else {
    let _ = SM.seq_list_match_cons_elim c l (vmatch pm);
    let _ = SM.seq_list_match_cons_elim c l' (vmatch pm');
    vmatch_gather (Seq.head c) #pm #(List.Tot.hd l) #pm' #(List.Tot.hd l');
    seq_list_match_gather vmatch vmatch_gather (Seq.tail c) (List.Tot.tl l) #pm (List.Tot.tl l') #pm';
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd l) (Seq.tail c) (List.Tot.tl l) (vmatch (pm +. pm'));
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd l :: List.Tot.tl l) (vmatch (pm +. pm')))
         as (SM.seq_list_match c l (vmatch (pm +. pm')));
  }
}

ghost fn base_iterator_match_share
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_share: share_t vmatch)
  (#k: parser_kind)
  (p: parser k u)
  (i: base_iterator t)
  (#pm: perm)
  (#l: Ghost.erased (list u))
requires base_iterator_match vmatch p pm i l
ensures base_iterator_match vmatch p (pm /. 2.0R) i l **
        base_iterator_match vmatch p (pm /. 2.0R) i l
{
  match i {
    Empty -> {
      unfold (base_iterator_match vmatch p pm (Empty #t) l);
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Empty #t) l);
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Empty #t) l);
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Empty #t) l **
               base_iterator_match vmatch p (pm /. 2.0R) (Empty #t) l)
           as (base_iterator_match vmatch p (pm /. 2.0R) i l **
               base_iterator_match vmatch p (pm /. 2.0R) i l);
    }
    Singleton sp sv s -> {
      unfold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
      with x y . assert (
        pts_to s #(pm *. sp) x **
        vmatch (pm *. sv) x y **
        pure (Ghost.reveal l == [y])
      );
      R.share s;
      rewrite (pts_to s #((pm *. sp) /. 2.0R) x) as (pts_to s #((pm /. 2.0R) *. sp) x);
      rewrite (pts_to s #((pm *. sp) /. 2.0R) x) as (pts_to s #((pm /. 2.0R) *. sp) x);
      vmatch_share x #(pm *. sv) #y;
      rewrite (vmatch ((pm *. sv) /. 2.0R) x y) as (vmatch ((pm /. 2.0R) *. sv) x y);
      rewrite (vmatch ((pm *. sv) /. 2.0R) x y) as (vmatch ((pm /. 2.0R) *. sv) x y);
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Singleton sp sv s) l);
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Singleton sp sv s) l);
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Singleton sp sv s) l **
               base_iterator_match vmatch p (pm /. 2.0R) (Singleton sp sv s) l)
           as (base_iterator_match vmatch p (pm /. 2.0R) i l **
               base_iterator_match vmatch p (pm /. 2.0R) i l);
    }
    Slice sp sv sl -> {
      unfold (base_iterator_match vmatch p pm (Slice sp sv sl) l);
      with l' . assert (
        pts_to sl #(pm *. sp) l' **
        SM.seq_list_match l' l (vmatch (pm *. sv))
      );
      S.share sl;
      rewrite (pts_to sl #((pm *. sp) /. 2.0R) l') as (pts_to sl #((pm /. 2.0R) *. sp) l');
      rewrite (pts_to sl #((pm *. sp) /. 2.0R) l') as (pts_to sl #((pm /. 2.0R) *. sp) l');
      seq_list_match_share vmatch vmatch_share l' l #(pm *. sv);
      rewrite (SM.seq_list_match l' l (vmatch ((pm *. sv) /. 2.0R)))
           as (SM.seq_list_match l' l (vmatch ((pm /. 2.0R) *. sv)));
      rewrite (SM.seq_list_match l' l (vmatch ((pm *. sv) /. 2.0R)))
           as (SM.seq_list_match l' l (vmatch ((pm /. 2.0R) *. sv)));
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Slice sp sv sl) l);
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Slice sp sv sl) l);
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Slice sp sv sl) l **
               base_iterator_match vmatch p (pm /. 2.0R) (Slice sp sv sl) l)
           as (base_iterator_match vmatch p (pm /. 2.0R) i l **
               base_iterator_match vmatch p (pm /. 2.0R) i l);
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match vmatch p pm (Serialized sp count pl) l);
      with l' . assert (
        pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #(pm *. sp) l'
      );
      pts_to_parsed_strong_prefix_share (parse_nlist (SZ.v count) p) pl #(pm *. sp) #l';
      rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #((pm *. sp) /. 2.0R) l')
           as (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #((pm /. 2.0R) *. sp) l');
      rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #((pm *. sp) /. 2.0R) l')
           as (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #((pm /. 2.0R) *. sp) l');
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count pl) l);
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count pl) l);
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count pl) l **
               base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count pl) l)
           as (base_iterator_match vmatch p (pm /. 2.0R) i l **
               base_iterator_match vmatch p (pm /. 2.0R) i l);
    }
  }
}

ghost fn base_iterator_match_gather
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_gather: gather_t vmatch)
  (#k: parser_kind)
  (p: parser k u)
  (i: base_iterator t)
  (#pm: perm)
  (#l: Ghost.erased (list u))
  (#pm': perm)
  (#l': Ghost.erased (list u))
requires base_iterator_match vmatch p pm i l **
         base_iterator_match vmatch p pm' i l'
ensures base_iterator_match vmatch p (pm +. pm') i l **
        pure (Ghost.reveal l == Ghost.reveal l')
{
  match i {
    Empty -> {
      unfold (base_iterator_match vmatch p pm (Empty #t) l);
      unfold (base_iterator_match vmatch p pm' (Empty #t) l');
      fold (base_iterator_match vmatch p (pm +. pm') (Empty #t) l);
      rewrite (base_iterator_match vmatch p (pm +. pm') (Empty #t) l)
           as (base_iterator_match vmatch p (pm +. pm') i l);
    }
    Singleton sp sv s -> {
      unfold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
      unfold (base_iterator_match vmatch p pm' (Singleton sp sv s) l');
      with x1 y1 . assert (
        pts_to s #(pm *. sp) x1 **
        vmatch (pm *. sv) x1 y1 **
        pure (Ghost.reveal l == [y1])
      );
      with x2 y2 . assert (
        pts_to s #(pm' *. sp) x2 **
        vmatch (pm' *. sv) x2 y2 **
        pure (Ghost.reveal l' == [y2])
      );
      R.gather s;
      rewrite (pts_to s #(pm *. sp +. pm' *. sp) x1) as (pts_to s #((pm +. pm') *. sp) x1);
      rewrite (vmatch (pm' *. sv) x2 y2) as (vmatch (pm' *. sv) x1 y2);
      vmatch_gather x1 #(pm *. sv) #y1 #(pm' *. sv) #y2;
      rewrite (vmatch (pm *. sv +. pm' *. sv) x1 y1) as (vmatch ((pm +. pm') *. sv) x1 y1);
      fold (base_iterator_match vmatch p (pm +. pm') (Singleton sp sv s) l);
      rewrite (base_iterator_match vmatch p (pm +. pm') (Singleton sp sv s) l)
           as (base_iterator_match vmatch p (pm +. pm') i l);
    }
    Slice sp sv sl -> {
      unfold (base_iterator_match vmatch p pm (Slice sp sv sl) l);
      unfold (base_iterator_match vmatch p pm' (Slice sp sv sl) l');
      with l1 . assert (
        pts_to sl #(pm *. sp) l1 **
        SM.seq_list_match l1 l (vmatch (pm *. sv))
      );
      with l2 . assert (
        pts_to sl #(pm' *. sp) l2 **
        SM.seq_list_match l2 l' (vmatch (pm' *. sv))
      );
      S.gather sl;
      rewrite (pts_to sl #(pm *. sp +. pm' *. sp) l1) as (pts_to sl #((pm +. pm') *. sp) l1);
      rewrite (SM.seq_list_match l2 l' (vmatch (pm' *. sv)))
           as (SM.seq_list_match l1 (Ghost.reveal l') (vmatch (pm' *. sv)));
      seq_list_match_gather vmatch vmatch_gather l1 l #(pm *. sv) (Ghost.reveal l') #(pm' *. sv);
      rewrite (SM.seq_list_match l1 l (vmatch (pm *. sv +. pm' *. sv)))
           as (SM.seq_list_match l1 l (vmatch ((pm +. pm') *. sv)));
      fold (base_iterator_match vmatch p (pm +. pm') (Slice sp sv sl) l);
      rewrite (base_iterator_match vmatch p (pm +. pm') (Slice sp sv sl) l)
           as (base_iterator_match vmatch p (pm +. pm') i l);
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match vmatch p pm (Serialized sp count pl) l);
      unfold (base_iterator_match vmatch p pm' (Serialized sp count pl) l');
      with v1 . assert (
        pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #(pm *. sp) v1
      );
      with v2 . assert (
        pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #(pm' *. sp) v2
      );
      pts_to_parsed_strong_prefix_gather (parse_nlist (SZ.v count) p) pl #(pm *. sp) #v1 #(pm' *. sp) #v2;
      rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #(pm *. sp +. pm' *. sp) v1)
           as (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) pl #((pm +. pm') *. sp) v1);
      fold (base_iterator_match vmatch p (pm +. pm') (Serialized sp count pl) l);
      rewrite (base_iterator_match vmatch p (pm +. pm') (Serialized sp count pl) l)
           as (base_iterator_match vmatch p (pm +. pm') i l);
    }
  }
}

ghost fn rec iterator_match_share
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_share: share_t vmatch)
  (#k: parser_kind)
  (p: parser k u)
  (i: iterator t)
  (#pm: perm)
  (#l: Ghost.erased (list u))
requires iterator_match vmatch p pm i l
ensures iterator_match vmatch p (pm /. 2.0R) i l **
        iterator_match vmatch p (pm /. 2.0R) i l
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match vmatch p pm (Base bi) l);
      base_iterator_match_share vmatch vmatch_share p bi;
      fold (iterator_match vmatch p (pm /. 2.0R) (Base bi) l);
      fold (iterator_match vmatch p (pm /. 2.0R) (Base bi) l);
      rewrite (iterator_match vmatch p (pm /. 2.0R) (Base bi) l **
               iterator_match vmatch p (pm /. 2.0R) (Base bi) l)
           as (iterator_match vmatch p (pm /. 2.0R) i l **
               iterator_match vmatch p (pm /. 2.0R) i l);
    }
    Append depth count before ap after -> {
      unfold (iterator_match vmatch p pm (Append depth count before ap after) l);
      with i1 i2 l2 . assert (
        base_iterator_match vmatch p pm before i1 **
        pts_to after #(pm *. ap) i2 **
        iterator_match vmatch p pm i2 l2 **
        pure (
          SZ.v count <= List.Tot.length i1 + List.Tot.length l2 /\
          Ghost.reveal l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1 l2)) /\
          iterator_depth i2 < Ghost.reveal depth
        )
      );
      base_iterator_match_share vmatch vmatch_share p before;
      R.share after;
      rewrite (pts_to after #((pm *. ap) /. 2.0R) i2) as (pts_to after #((pm /. 2.0R) *. ap) i2);
      rewrite (pts_to after #((pm *. ap) /. 2.0R) i2) as (pts_to after #((pm /. 2.0R) *. ap) i2);
      iterator_match_share vmatch vmatch_share p i2;
      fold (iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l);
      fold (iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l);
      rewrite (iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l **
               iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l)
           as (iterator_match vmatch p (pm /. 2.0R) i l **
               iterator_match vmatch p (pm /. 2.0R) i l);
    }
  }
}

[@@allow_ambiguous]
ghost fn rec iterator_match_gather
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_gather: gather_t vmatch)
  (#k: parser_kind)
  (p: parser k u)
  (i: iterator t)
  (pm: perm)
  (#l: Ghost.erased (list u))
  (pm': perm)
  (#l': Ghost.erased (list u))
requires iterator_match vmatch p pm i l **
         iterator_match' vmatch p pm' i l'
ensures iterator_match vmatch p (pm +. pm') i l **
        pure (Ghost.reveal l == Ghost.reveal l')
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match vmatch p pm (Base bi) l);
      rewrite (iterator_match' vmatch p pm' (Base bi) l')
           as (iterator_match vmatch p pm' (Base bi) l');
      unfold (iterator_match vmatch p pm' (Base bi) l');
      base_iterator_match_gather vmatch vmatch_gather p bi #pm #l #pm' #l';
      fold (iterator_match vmatch p (pm +. pm') (Base bi) l);
      rewrite (iterator_match vmatch p (pm +. pm') (Base bi) l)
           as (iterator_match vmatch p (pm +. pm') i l);
    }
    Append depth count before ap after -> {
      unfold (iterator_match vmatch p pm (Append depth count before ap after) l);
      rewrite (iterator_match' vmatch p pm' (Append depth count before ap after) l')
           as (iterator_match vmatch p pm' (Append depth count before ap after) l');
      unfold (iterator_match vmatch p pm' (Append depth count before ap after) l');
      with i1 i2 l2 . assert (
        base_iterator_match vmatch p pm before i1 **
        pts_to after #(pm *. ap) i2 **
        iterator_match vmatch p pm i2 l2 **
        pure (
          SZ.v count <= List.Tot.length i1 + List.Tot.length l2 /\
          Ghost.reveal l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1 l2)) /\
          iterator_depth i2 < Ghost.reveal depth
        )
      );
      with i1' i2' l2' . assert (
        base_iterator_match vmatch p pm' before i1' **
        pts_to after #(pm' *. ap) i2' **
        iterator_match vmatch p pm' i2' l2' **
        pure (
          SZ.v count <= List.Tot.length i1' + List.Tot.length l2' /\
          Ghost.reveal l' == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1' l2')) /\
          iterator_depth i2' < Ghost.reveal depth
        )
      );
      base_iterator_match_gather vmatch vmatch_gather p before #pm #i1 #pm' #i1';
      R.gather after;
      rewrite (pts_to after #(pm *. ap +. pm' *. ap) i2) as (pts_to after #((pm +. pm') *. ap) i2);
      rewrite (iterator_match vmatch p pm' i2' l2') as (iterator_match vmatch p pm' i2 l2');
      // Coerce existential witnesses to plain types to avoid decreases-refined type mismatch
      let l2p : list u = l2;
      rewrite (iterator_match vmatch p pm i2 l2) as (iterator_match vmatch p pm i2 l2p);
      let l2p' : list u = l2';
      rewrite (iterator_match vmatch p pm' i2 l2') as (iterator_match vmatch p pm' i2 l2p');
      rewrite (iterator_match vmatch p pm' i2 l2p')
           as (iterator_match' vmatch p pm' i2 l2p');
      iterator_match_gather vmatch vmatch_gather p i2 pm #l2p pm' #l2p';
      rewrite (iterator_match vmatch p (pm +. pm') i2 l2p) as (iterator_match vmatch p (pm +. pm') i2 l2);
      fold (iterator_match vmatch p (pm +. pm') (Append depth count before ap after) l);
      rewrite (iterator_match vmatch p (pm +. pm') (Append depth count before ap after) l)
           as (iterator_match vmatch p (pm +. pm') i l);
    }
  }
}

let rec lemma_splitAt_append (#a: Type) (n: nat) (l: list a) : Lemma
  (requires n <= List.Tot.length l)
  (ensures (let (l1, l2) = List.Tot.splitAt n l in
    List.Tot.length l1 == n /\ l1 `List.Tot.append` l2 == l))
  (decreases n)
= if n = 0 then () else lemma_splitAt_append (n-1) (List.Tot.tl l)

let rec lemma_splitAt_prefix (#a: Type) (m n: nat) (l: list a) : Lemma
  (requires m <= n /\ n <= List.Tot.length l)
  (ensures (
    lemma_splitAt_fst_length n l;
    fst (List.Tot.splitAt m (fst (List.Tot.splitAt n l))) == fst (List.Tot.splitAt m l)))
  (decreases m)
= lemma_splitAt_fst_length n l;
  if m = 0 then ()
  else begin
    match l with
    | _ :: tl -> lemma_splitAt_prefix (m-1) (n-1) tl
  end

let rec lemma_parse_nlist_prefix
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n len: nat)
  (w: bytes)
: Lemma
  (requires
    len <= n /\
    (parse_nlist_kind n k).parser_kind_subkind == Some ParserStrong /\
    Some? (parse (parse_nlist n p) w)
  )
  (ensures (
    Some? (parse (parse_nlist len p) w) /\
    (let Some (l_n, _) = parse (parse_nlist n p) w in
     let Some (l_len, _) = parse (parse_nlist len p) w in
     l_len == fst (List.Tot.splitAt len l_n))
  ))
  (decreases len)
= parse_nlist_kind_subkind n k;
  parse_nlist_eq n p w;
  parse_nlist_eq len p w;
  if len = 0 then ()
  else begin
    parse_nlist_kind_subkind (n-1) k;
    match parse p w with
    | Some (_, consumed) ->
      let w' = Seq.slice w consumed (Seq.length w) in
      lemma_parse_nlist_prefix p (n-1) (len-1) w'
    | _ -> ()
  end

#push-options "--z3rlimit 40"

fn base_iterator_truncate
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_iterator t)
  (#l: Ghost.erased (list u))
  (len: SZ.t)
requires base_iterator_match vmatch p pm i l ** pure (SZ.v len <= List.Tot.length l)
returns res: base_iterator t
ensures exists* pm_out .
  base_iterator_match vmatch p pm_out res (fst (List.Tot.splitAt (SZ.v len) l)) **
  (base_iterator_match vmatch p pm_out res (fst (List.Tot.splitAt (SZ.v len) l)) @==>
   base_iterator_match vmatch p pm i l)
{
  match i {
    Empty -> {
      unfold (base_iterator_match vmatch p pm (Empty #t) l);
      fold (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)));
      Trade.refl (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)));
      rewrite (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)))
           as (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               base_iterator_match vmatch p pm i l);
      Empty #t
    }
    Singleton sp sv s -> {
      unfold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
      if (len = 0sz) {
        with x y . assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y]));
        fold (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)));
        intro (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               base_iterator_match vmatch p pm (Singleton sp sv s) l)
          #(pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y]))
          fn _ {
            unfold (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)));
            fold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
          };
        rewrite (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
                 base_iterator_match vmatch p pm (Singleton sp sv s) l)
             as (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
                 base_iterator_match vmatch p pm i l);
        Empty #t
      } else {
        // len == 1, return same Singleton (fst (splitAt 1 [y]) == [y] == l)
        fold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
        rewrite (base_iterator_match vmatch p pm (Singleton sp sv s) l)
             as (base_iterator_match vmatch p pm (Singleton sp sv s) (fst (List.Tot.splitAt (SZ.v len) l)));
        Trade.refl (base_iterator_match vmatch p pm (Singleton sp sv s) (fst (List.Tot.splitAt (SZ.v len) l)));
        rewrite (base_iterator_match vmatch p pm (Singleton sp sv s) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
                 base_iterator_match vmatch p pm (Singleton sp sv s) (fst (List.Tot.splitAt (SZ.v len) l)))
             as (base_iterator_match vmatch p pm (Singleton sp sv s) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
                 base_iterator_match vmatch p pm i l);
        Singleton sp sv s
      }
    }
    Slice sp sv ss -> {
      unfold (base_iterator_match vmatch p pm (Slice sp sv ss) l);
      with l' . assert (S.pts_to ss #(pm *. sp) l' ** SM.seq_list_match l' l (vmatch (pm *. sv)));
      SM.seq_list_match_length (vmatch (pm *. sv)) l' l;
      let pair = S.split ss len;
      match pair { s1, s2 -> {
        let l1 : Ghost.erased (list u) = Ghost.hide (fst (List.Tot.splitAt (SZ.v len) (Ghost.reveal l)));
        let l2 : Ghost.erased (list u) = Ghost.hide (snd (List.Tot.splitAt (SZ.v len) (Ghost.reveal l)));
        Seq.lemma_split l' (SZ.v len);
        lemma_splitAt_append (SZ.v len) l;
        rewrite (SM.seq_list_match l' l (vmatch (pm *. sv)))
             as (SM.seq_list_match (Seq.append (Seq.slice l' 0 (SZ.v len)) (Seq.slice l' (SZ.v len) (Seq.length l'))) (List.Tot.append l1 l2) (vmatch (pm *. sv)));
        SM.seq_list_match_append_elim (vmatch (pm *. sv)) (Seq.slice l' 0 (SZ.v len)) l1 (Seq.slice l' (SZ.v len) (Seq.length l')) l2;
        fold (base_iterator_match vmatch p pm (Slice sp sv s1) l1);
        rewrite (base_iterator_match vmatch p pm (Slice sp sv s1) (Ghost.reveal l1))
             as (base_iterator_match vmatch p pm (Slice sp sv s1) (fst (List.Tot.splitAt (SZ.v len) l)));
        // Trade: stash s2, slm2, is_split, pure facts
        intro (base_iterator_match vmatch p pm (Slice sp sv s1) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               base_iterator_match vmatch p pm (Slice sp sv ss) l)
          #(S.pts_to s2 #(pm *. sp) (Seq.slice l' (SZ.v len) (Seq.length l')) **
            SM.seq_list_match (Seq.slice l' (SZ.v len) (Seq.length l')) l2 (vmatch (pm *. sv)) **
            S.is_split ss s1 s2 **
            pure (Seq.length (Seq.slice l' 0 (SZ.v len)) == List.Tot.length l1 /\
                  Seq.length (Seq.slice l' (SZ.v len) (Seq.length l')) == List.Tot.length l2))
          fn _ {
            rewrite (base_iterator_match vmatch p pm (Slice sp sv s1) (fst (List.Tot.splitAt (SZ.v len) l)))
                 as (base_iterator_match vmatch p pm (Slice sp sv s1) l1);
            unfold (base_iterator_match vmatch p pm (Slice sp sv s1) l1);
            with v1' . assert (S.pts_to s1 #(pm *. sp) v1');
            SM.seq_list_match_append_intro (vmatch (pm *. sv)) v1' l1 (Seq.slice l' (SZ.v len) (Seq.length l')) l2;
            S.join s1 s2 ss;
            rewrite (S.pts_to ss #(pm *. sp) (Seq.append v1' (Seq.slice l' (SZ.v len) (Seq.length l'))))
                 as (S.pts_to ss #(pm *. sp) (Seq.append v1' (Seq.slice l' (SZ.v len) (Seq.length l'))));
            rewrite (SM.seq_list_match (Seq.append v1' (Seq.slice l' (SZ.v len) (Seq.length l'))) (List.Tot.append l1 l2) (vmatch (pm *. sv)))
                 as (SM.seq_list_match (Seq.append v1' (Seq.slice l' (SZ.v len) (Seq.length l'))) l (vmatch (pm *. sv)));
            fold (base_iterator_match vmatch p pm (Slice sp sv ss) l);
          };
        rewrite (base_iterator_match vmatch p pm (Slice sp sv s1) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
                 base_iterator_match vmatch p pm (Slice sp sv ss) l)
             as (base_iterator_match vmatch p pm (Slice sp sv s1) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
                 base_iterator_match vmatch p pm i l);
        Slice sp sv s1
      }}
    }
    Serialized sp count payload -> {
      // Share the base_iterator_match to get two copies at pm /. 2.0R
      base_iterator_match_share vmatch vmatch_share p (Serialized sp count payload) #pm #l;
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l **
               base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l)
           as (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l **
               base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l);
      // Unfold one copy to access byte slice and parse fact
      unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l);
      with l' . assert (
        pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l' **
        pure ((l' <: list u) == l)
      );
      unfold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l');
      with w . assert (
        S.pts_to payload #((pm /. 2.0R) *. sp) w **
        pure (pts_to_parsed_strong_prefix_prop (parse_nlist (SZ.v count) p) w l')
      );
      // Establish prefix parse fact
      lemma_parse_nlist_prefix p (SZ.v count) (SZ.v len) w;
      parse_nlist_kind_subkind (SZ.v len) k;
      // Fold truncated pts_to_parsed_strong_prefix
      let prefix_l : Ghost.erased (list u) = Ghost.hide (fst (List.Tot.splitAt (SZ.v len) (Ghost.reveal l)));
      fold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v len) p) payload #((pm /. 2.0R) *. sp) prefix_l);
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp len payload) prefix_l);
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Serialized #t sp len payload) (Ghost.reveal prefix_l))
           as (base_iterator_match vmatch p (pm /. 2.0R) (Serialized #t sp len payload) (fst (List.Tot.splitAt (SZ.v len) l)));
      // Trade: stash the other copy, restore via gather
      intro (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp len payload) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
             base_iterator_match vmatch p pm (Serialized sp count payload) l)
        #(base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l)
        fn _ {
          // Unfold the hypothesis (truncated match)
          rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp len payload) (fst (List.Tot.splitAt (SZ.v len) l)))
               as (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp len payload) prefix_l);
          unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp len payload) prefix_l);
          with l1 . assert (
            pts_to_parsed_strong_prefix (parse_nlist (SZ.v len) p) payload #((pm /. 2.0R) *. sp) l1
          );
          unfold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v len) p) payload #((pm /. 2.0R) *. sp) l1);
          with w1 . assert (S.pts_to payload #((pm /. 2.0R) *. sp) w1);
          // Unfold the stashed copy (original match)
          unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l);
          with l2 . assert (
            pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l2
          );
          unfold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l2);
          // Gather byte slices to get full permission and prove w1 == w2
          S.gather payload;
          rewrite (S.pts_to payload #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) w1)
               as (S.pts_to payload #(pm *. sp) w1);
          // Use the stashed parse fact (w2 has the original parse fact, and w1 == w2)
          fold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l);
          fold (base_iterator_match vmatch p pm (Serialized sp count payload) l);
        };
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp len payload) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               base_iterator_match vmatch p pm (Serialized sp count payload) l)
           as (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp len payload) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               base_iterator_match vmatch p pm i l);
      Serialized sp len payload
    }
  }
}

#pop-options

#push-options "--z3rlimit 60"
fn iterator_truncate
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: iterator t)
  (#l: Ghost.erased (list u))
  (len: SZ.t)
requires iterator_match vmatch p pm i l ** pure (SZ.v len <= List.Tot.length l)
returns res: iterator t
ensures exists* pm_out .
  iterator_match vmatch p pm_out res (fst (List.Tot.splitAt (SZ.v len) l)) **
  (iterator_match vmatch p pm_out res (fst (List.Tot.splitAt (SZ.v len) l)) @==>
   iterator_match vmatch p pm i l)
{
  match i {
    Base bi -> {
      unfold (iterator_match vmatch p pm (Base #t bi) l);
      let res = base_iterator_truncate vmatch vmatch_share vmatch_gather p pm bi #l len;
      with pm_out . assert (
        base_iterator_match vmatch p pm_out res (fst (List.Tot.splitAt (SZ.v len) l)) **
        (base_iterator_match vmatch p pm_out res (fst (List.Tot.splitAt (SZ.v len) l)) @==>
         base_iterator_match vmatch p pm bi l)
      );
      fold (iterator_match vmatch p pm_out (Base #t res) (fst (List.Tot.splitAt (SZ.v len) l)));
      // Build trade: Base res @==> Base bi
      intro (iterator_match vmatch p pm_out (Base #t res) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
             iterator_match vmatch p pm (Base #t bi) l)
        #(base_iterator_match vmatch p pm_out res (fst (List.Tot.splitAt (SZ.v len) l)) @==>
          base_iterator_match vmatch p pm bi l)
        fn _ {
          unfold (iterator_match vmatch p pm_out (Base #t res) (fst (List.Tot.splitAt (SZ.v len) l)));
          Trade.elim
            (base_iterator_match vmatch p pm_out res (fst (List.Tot.splitAt (SZ.v len) l)))
            (base_iterator_match vmatch p pm bi l);
          fold (iterator_match vmatch p pm (Base #t bi) l);
        };
      rewrite (iterator_match vmatch p pm_out (Base #t res) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               iterator_match vmatch p pm (Base #t bi) l)
           as (iterator_match vmatch p pm_out (Base #t res) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               iterator_match vmatch p pm i l);
      Base #t res
    }
    Append depth count before ap after -> {
      // Share to get two copies at pm/2
      iterator_match_share vmatch vmatch_share p (Append depth count before ap after) #pm #l;
      rewrite (iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l **
               iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l)
           as (iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l **
               iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l);
      // Unfold one copy
      unfold (iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l);
      with i1 i2 l2 . assert (
        base_iterator_match vmatch p (pm /. 2.0R) before i1 **
        pts_to after #((pm /. 2.0R) *. ap) i2 **
        iterator_match vmatch p (pm /. 2.0R) i2 l2
      );
      // Establish prefix-of-prefix fact
      List.Tot.append_length i1 l2;
      lemma_splitAt_fst_length (SZ.v count) (List.Tot.append i1 l2);
      lemma_splitAt_prefix (SZ.v len) (SZ.v count) (List.Tot.append i1 l2);
      // Fold as Append with len instead of count
      fold (iterator_match vmatch p (pm /. 2.0R) (Append depth len before ap after) (fst (List.Tot.splitAt (SZ.v len) l)));
      rewrite (iterator_match vmatch p (pm /. 2.0R) (Append #t depth len before ap after) (fst (List.Tot.splitAt (SZ.v len) (Ghost.reveal l))))
           as (iterator_match vmatch p (pm /. 2.0R) (Append #t depth len before ap after) (fst (List.Tot.splitAt (SZ.v len) l)));
      // Trade: stash the other copy
      intro (iterator_match vmatch p (pm /. 2.0R) (Append depth len before ap after) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
             iterator_match vmatch p pm (Append depth count before ap after) l)
        #(iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l)
        fn _ {
          // Unfold the truncated match
          unfold (iterator_match vmatch p (pm /. 2.0R) (Append depth len before ap after) (fst (List.Tot.splitAt (SZ.v len) l)));
          with i1' i2' l2' . assert (
            base_iterator_match vmatch p (pm /. 2.0R) before i1' **
            pts_to after #((pm /. 2.0R) *. ap) i2' **
            iterator_match vmatch p (pm /. 2.0R) i2' l2'
          );
          // Rewrite first copy to primed aliases to disambiguate
          rewrite (iterator_match vmatch p (pm /. 2.0R) i2' l2')
               as (iterator_match' vmatch p (pm /. 2.0R) i2' l2');
          rewrite (base_iterator_match vmatch p (pm /. 2.0R) before i1')
               as (base_iterator_match' vmatch p (pm /. 2.0R) before i1');
          // Unfold the stashed copy — now base_iterator_match and iterator_match are unambiguous
          unfold (iterator_match vmatch p (pm /. 2.0R) (Append depth count before ap after) l);
          with i1b i2b l2b . assert (
            base_iterator_match vmatch p (pm /. 2.0R) before i1b **
            pts_to after #((pm /. 2.0R) *. ap) i2b **
            iterator_match vmatch p (pm /. 2.0R) i2b l2b **
            pure (
              SZ.v count <= List.Tot.length i1b + List.Tot.length l2b /\
              Ghost.reveal l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1b l2b)) /\
              iterator_depth i2b < Ghost.reveal depth
            )
          );
          // Rewrite primed aliases back
          rewrite (iterator_match' vmatch p (pm /. 2.0R) i2' l2')
               as (iterator_match vmatch p (pm /. 2.0R) i2' l2');
          rewrite (base_iterator_match' vmatch p (pm /. 2.0R) before i1')
               as (base_iterator_match vmatch p (pm /. 2.0R) before i1');
          // Gather base_iterator_match (pin first to i1')
          base_iterator_match_gather vmatch vmatch_gather p before
            #(pm /. 2.0R) #i1' #(pm /. 2.0R);
          rewrite (base_iterator_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) before i1')
               as (base_iterator_match vmatch p pm before i1');
          // Gather ref (pin first to i2')
          R.gather after #i2';
          rewrite (pts_to after #((pm /. 2.0R) *. ap +. (pm /. 2.0R) *. ap) i2')
               as (pts_to after #(pm *. ap) i2');
          // i2' == i2b from R.gather, rewrite stashed iterator_match
          rewrite (iterator_match vmatch p (pm /. 2.0R) i2b l2b)
               as (iterator_match vmatch p (pm /. 2.0R) i2' l2b);
          // Gather iterator_match — need type coercion and one primed, one non-primed
          let l2p : list u = l2';
          rewrite (iterator_match vmatch p (pm /. 2.0R) i2' l2')
               as (iterator_match vmatch p (pm /. 2.0R) i2' l2p);
          let l2bp : list u = l2b;
          rewrite (iterator_match vmatch p (pm /. 2.0R) i2' l2b)
               as (iterator_match vmatch p (pm /. 2.0R) i2' l2bp);
          rewrite (iterator_match vmatch p (pm /. 2.0R) i2' l2bp)
               as (iterator_match' vmatch p (pm /. 2.0R) i2' l2bp);
          iterator_match_gather vmatch vmatch_gather p i2'
            (pm /. 2.0R) #l2p (pm /. 2.0R) #l2bp;
          rewrite (iterator_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) i2' l2p)
               as (iterator_match vmatch p pm i2' l2');
          // Now fold the original Append at full pm
          List.Tot.append_length i1b l2b;
          lemma_splitAt_fst_length (SZ.v count) (List.Tot.append i1b l2b);
          fold (iterator_match vmatch p pm (Append depth count before ap after) l);
        };
      rewrite (iterator_match vmatch p (pm /. 2.0R) (Append depth len before ap after) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               iterator_match vmatch p pm (Append depth count before ap after) l)
           as (iterator_match vmatch p (pm /. 2.0R) (Append depth len before ap after) (fst (List.Tot.splitAt (SZ.v len) l)) @==>
               iterator_match vmatch p pm i l);
      Append depth len before ap after
    }
  }
}
#pop-options

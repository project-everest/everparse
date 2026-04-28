module LowParse.PulseParse.Iterator
#lang-pulse
include LowParse.PulseParse.Base
include LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module SZ = FStar.SizeT

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

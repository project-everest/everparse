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
module LPS = LowParse.Pulse.Base
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
   iterator_match vmatch p pm i l) **
  pure (iterator_depth res <= iterator_depth i)
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

// Helper: split a pts_to_parsed_strong_prefix of an nlist into head (pts_to_parsed) and tail (pts_to_parsed_strong_prefix)
#push-options "--z3rlimit 40"

fn nlist_hd_tl_strong_prefix
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  pts_to_parsed_strong_prefix (parse_nlist n p) input #pm v
returns res : (S.slice byte & S.slice byte)
ensures (
  let (hd_sl, tl_sl) = res in
  pts_to_parsed p hd_sl #(pm /. 2.0R) (List.Tot.hd v) **
  pts_to_parsed_strong_prefix (parse_nlist (n - 1) p) tl_sl #(pm /. 2.0R) (List.Tot.tl v) **
  Trade.trade
    (pts_to_parsed p hd_sl #(pm /. 2.0R) (List.Tot.hd v) **
     pts_to_parsed_strong_prefix (parse_nlist (n - 1) p) tl_sl #(pm /. 2.0R) (List.Tot.tl v))
    (pts_to_parsed_strong_prefix (parse_nlist n p) input #pm v)
)
{
  // 1. Unfold strong_prefix to raw bytes
  unfold (pts_to_parsed_strong_prefix (parse_nlist n p) input #pm v);
  with w . assert (S.pts_to input #pm w);
  // 2. Establish parse facts
  parse_nlist_eq (Ghost.reveal n) p w;
  parser_kind_prop_equiv k p;
  // 3. Jump to find first element boundary
  let off = j input 0sz;
  // 4. Split with trade
  let hd_sl, tl_sl = S.split_trade input off;
  with w1 . assert (S.pts_to hd_sl #pm w1);
  with w2 . assert (S.pts_to tl_sl #pm w2);
  // 5. Head parse fact
  parse_strong_prefix p w w1;
  let vh = Ghost.hide (List.Tot.hd (Ghost.reveal v));
  let vt : Ghost.erased (nlist (n - 1) t) = Ghost.hide (List.Tot.tl (Ghost.reveal v));
  // 6. pts_to_parsed_intro for head (gives #(pm/2))
  pts_to_parsed_intro p hd_sl vh;
  // 7. pts_to_parsed_strong_prefix_intro for tail (gives #(pm/2))
  parse_nlist_kind_subkind (Ghost.reveal n - 1) k;
  pts_to_parsed_strong_prefix_intro (parse_nlist (n - 1) p) tl_sl vt;
  // 8. Trade chain: (parsed hd ** strong_prefix tl) -> (pts_to hd ** pts_to tl) -> (pts_to input) -> (strong_prefix nlist)
  Trade.prod
    (pts_to_parsed p hd_sl #(pm /. 2.0R) vh)
    (S.pts_to hd_sl #pm w1)
    (pts_to_parsed_strong_prefix (parse_nlist (n - 1) p) tl_sl #(pm /. 2.0R) vt)
    (S.pts_to tl_sl #pm w2);
  Trade.trans
    (pts_to_parsed p hd_sl #(pm /. 2.0R) vh **
     pts_to_parsed_strong_prefix (parse_nlist (n - 1) p) tl_sl #(pm /. 2.0R) vt)
    (S.pts_to hd_sl #pm w1 ** S.pts_to tl_sl #pm w2)
    (S.pts_to input #pm w);
  // Chain with fold trade: (S.pts_to input) -> (strong_prefix nlist)
  intro (S.pts_to input #pm w @==>
         pts_to_parsed_strong_prefix (parse_nlist n p) input #pm v)
    #emp
    fn _ {
      fold (pts_to_parsed_strong_prefix (parse_nlist n p) input #pm v)
    };
  Trade.trans
    (pts_to_parsed p hd_sl #(pm /. 2.0R) vh **
     pts_to_parsed_strong_prefix (parse_nlist (n - 1) p) tl_sl #(pm /. 2.0R) vt)
    (S.pts_to input #pm w)
    (pts_to_parsed_strong_prefix (parse_nlist n p) input #pm v);
  rewrite each vh as (List.Tot.hd (Ghost.reveal v));
  rewrite each vt as (List.Tot.tl (Ghost.reveal v));
  (hd_sl, tl_sl)
}

#pop-options

// base_iterator_next: advance a base_iterator on a nonempty list
#push-options "--z3rlimit 60"

fn base_iterator_next
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (rd: (pv: perm) -> zero_copy_parse (vmatch pv) p)
  (pm: perm)
  (pi: R.ref (base_iterator t))
  (#i: Ghost.erased (base_iterator t))
  (#l: Ghost.erased (list u) { Cons? l })
requires
  R.pts_to pi i **
  base_iterator_match vmatch p pm i l
returns res: t
ensures exists* (i': base_iterator t) (pm_v: perm) .
  R.pts_to pi i' **
  base_iterator_match vmatch p pm i' (List.Tot.tl l) **
  vmatch pm_v res (List.Tot.hd l) **
  Trade.trade
    (base_iterator_match vmatch p pm i' (List.Tot.tl l) **
     vmatch pm_v res (List.Tot.hd l))
    (base_iterator_match vmatch p pm i l)
{
  let iv = !pi;
  match iv {
    Empty -> {
      // Contradiction: Empty means Nil? l, but we have Cons? l
      rewrite (base_iterator_match vmatch p pm i l)
           as (base_iterator_match vmatch p pm (Empty #t) l);
      unfold (base_iterator_match vmatch p pm (Empty #t) l);
      unreachable ()
    }
    Singleton sp sv sr -> {
      rewrite (base_iterator_match vmatch p pm i l)
           as (base_iterator_match vmatch p pm (Singleton sp sv sr) l);
      unfold (base_iterator_match vmatch p pm (Singleton sp sv sr) l);
      with x y . assert (
        R.pts_to sr #(pm *. sp) x **
        vmatch (pm *. sv) x y **
        pure (l == [y])
      );
      // Read the element
      let res = !sr;
      // Rewrite vmatch with hd l
      rewrite (vmatch (pm *. sv) res y) as (vmatch (pm *. sv) res (List.Tot.hd l));
      // Write pi to Empty
      R.forget_init pi;
      pi := Empty;
      // The tail is [], fold Empty match
      fold (base_iterator_match vmatch p pm (Empty #t) (List.Tot.tl l));
      // Trade: stash the ref permission, restore Singleton match
      intro (base_iterator_match vmatch p pm (Empty #t) (List.Tot.tl l) **
             vmatch (pm *. sv) res (List.Tot.hd l) @==>
             base_iterator_match vmatch p pm (Singleton sp sv sr) l)
        #(R.pts_to sr #(pm *. sp) res)
        fn _ {
          unfold (base_iterator_match vmatch p pm (Empty #t) (List.Tot.tl l));
          rewrite (vmatch (pm *. sv) res (List.Tot.hd l)) as (vmatch (pm *. sv) res y);
          fold (base_iterator_match vmatch p pm (Singleton sp sv sr) l)
        };
      rewrite (base_iterator_match vmatch p pm (Empty #t) (List.Tot.tl l) **
               vmatch (pm *. sv) res (List.Tot.hd l) @==>
               base_iterator_match vmatch p pm (Singleton sp sv sr) l)
           as (base_iterator_match vmatch p pm (Empty #t) (List.Tot.tl l) **
               vmatch (pm *. sv) res (List.Tot.hd l) @==>
               base_iterator_match vmatch p pm i l);
      res
    }
    Slice sp sv ss -> {
      rewrite (base_iterator_match vmatch p pm i l)
           as (base_iterator_match vmatch p pm (Slice sp sv ss) l);
      unfold (base_iterator_match vmatch p pm (Slice sp sv ss) l);
      with l' . assert (
        S.pts_to ss #(pm *. sp) l' **
        SM.seq_list_match l' l (vmatch (pm *. sv))
      );
      // l is Cons, so length l' > 0
      SM.seq_list_match_length (vmatch (pm *. sv)) l' l;
      SM.seq_list_match_cons_elim l' l (vmatch (pm *. sv));
      // Read the first element from the slice
      let res = S.op_Array_Access ss 0sz;
      // Split the slice at index 1
      let pair = S.split ss 1sz;
      let s1 = fst pair;
      let s2 = snd pair;
      let v1 = Ghost.hide (Seq.slice l' 0 1);
      let v2 = Ghost.hide (Seq.slice l' 1 (Seq.length l'));
      rewrite (S.pts_to (fst pair) #(pm *. sp) (Seq.slice l' 0 1))
           as (S.pts_to s1 #(pm *. sp) v1);
      rewrite (S.pts_to (snd pair) #(pm *. sp) (Seq.slice l' 1 (Seq.length l')))
           as (S.pts_to s2 #(pm *. sp) v2);
      rewrite (S.is_split ss (fst pair) (snd pair))
           as (S.is_split ss s1 s2);
      // Rewrite seq_list_match to use v2
      assert (pure (Seq.equal (Seq.tail l') (Ghost.reveal v2)));
      rewrite (SM.seq_list_match (Seq.tail l') (List.Tot.tl l) (vmatch (pm *. sv)))
           as (SM.seq_list_match v2 (List.Tot.tl l) (vmatch (pm *. sv)));
      // Also rewrite vmatch head
      rewrite (vmatch (pm *. sv) (Seq.head l') (List.Tot.hd l))
           as (vmatch (pm *. sv) res (List.Tot.hd l));
      // Write pi to point to tail slice
      R.forget_init pi;
      pi := Slice sp sv s2;
      // Fold tail match
      fold (base_iterator_match vmatch p pm (Slice sp sv s2) (List.Tot.tl l));
      // Trade: stash s1 pts_to and is_split, restore original Slice match
      intro (base_iterator_match vmatch p pm (Slice sp sv s2) (List.Tot.tl l) **
             vmatch (pm *. sv) res (List.Tot.hd l) @==>
             base_iterator_match vmatch p pm (Slice sp sv ss) l)
        #(S.pts_to s1 #(pm *. sp) v1 ** S.is_split ss s1 s2)
        fn _ {
          // Unfold the tail base_iterator_match
          unfold (base_iterator_match vmatch p pm (Slice sp sv s2) (List.Tot.tl l));
          with l2' . assert (
            S.pts_to s2 #(pm *. sp) l2' **
            SM.seq_list_match l2' (List.Tot.tl l) (vmatch (pm *. sv))
          );
          // Reassemble seq_list_match
          SM.seq_list_match_cons_intro res (List.Tot.hd l) l2' (List.Tot.tl l) (vmatch (pm *. sv));
          // Join the slices
          S.join s1 s2 ss;
          // After join: S.pts_to ss #(pm*sp) (Seq.append v1 l2')
          // seq_list_match uses (Seq.cons res l2')
          // Prove they are equal and rewrite
          assert (pure (Seq.equal (Seq.append v1 l2') (Seq.cons res l2')));
          rewrite (SM.seq_list_match (Seq.cons res l2') l (vmatch (pm *. sv)))
               as (SM.seq_list_match (Seq.append v1 l2') l (vmatch (pm *. sv)));
          // Fold the original Slice match
          fold (base_iterator_match vmatch p pm (Slice sp sv ss) l)
        };
      rewrite (base_iterator_match vmatch p pm (Slice sp sv s2) (List.Tot.tl l) **
               vmatch (pm *. sv) res (List.Tot.hd l) @==>
               base_iterator_match vmatch p pm (Slice sp sv ss) l)
           as (base_iterator_match vmatch p pm (Slice sp sv s2) (List.Tot.tl l) **
               vmatch (pm *. sv) res (List.Tot.hd l) @==>
               base_iterator_match vmatch p pm i l);
      res
    }
    Serialized sp count payload -> {
      rewrite (base_iterator_match vmatch p pm i l)
           as (base_iterator_match vmatch p pm (Serialized sp count payload) l);
      unfold (base_iterator_match vmatch p pm (Serialized sp count payload) l);
      with l' . assert (
        pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l' **
        pure ((l' <: list u) == l)
      );
      // Split into head and tail
      let n : Ghost.erased pos = Ghost.hide (SZ.v count);
      rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l')
           as (pts_to_parsed_strong_prefix (parse_nlist n p) payload #(pm *. sp) l');
      let hd_sl, tl_sl = nlist_hd_tl_strong_prefix sq j n payload;
      // Call reader on head slice; parse perm is (pm*sp)/2
      let pm_v = (pm *. sp) /. 2.0R;
      let res = rd pm_v hd_sl;
      // Rewrite l' to l in vmatch and trade
      rewrite (vmatch pm_v res (List.Tot.hd l'))
           as (vmatch pm_v res (List.Tot.hd l));
      rewrite (Trade.trade (vmatch pm_v res (List.Tot.hd l')) (pts_to_parsed p hd_sl #((pm *. sp) /. 2.0R) (List.Tot.hd l')))
           as (Trade.trade (vmatch pm_v res (List.Tot.hd l)) (pts_to_parsed p hd_sl #((pm *. sp) /. 2.0R) (List.Tot.hd l)));
      // Rewrite nlist_hd_tl trade from n back to SZ.v count
      rewrite (Trade.trade
                (pts_to_parsed p hd_sl #((pm *. sp) /. 2.0R) (List.Tot.hd l') **
                 pts_to_parsed_strong_prefix (parse_nlist (n - 1) p) tl_sl #((pm *. sp) /. 2.0R) (List.Tot.tl l'))
                (pts_to_parsed_strong_prefix (parse_nlist n p) payload #(pm *. sp) l'))
           as (Trade.trade
                (pts_to_parsed p hd_sl #((pm *. sp) /. 2.0R) (List.Tot.hd l) **
                 pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - 1) p) tl_sl #((pm *. sp) /. 2.0R) (List.Tot.tl l))
                (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l));
      // Write pi to point to tail with halved sp
      R.forget_init pi;
      pi := Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl;
      // Fold tail match at pm so that pm *. (sp /. 2.0R) == (pm *. sp) /. 2.0R
      fold (base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l));
      // Build trade for tail: unfold tail match to recover strong_prefix
      intro (base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l) @==>
             pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - 1) p) tl_sl #((pm *. sp) /. 2.0R) (List.Tot.tl l))
        #emp
        fn _ {
          unfold (base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l));
          with tl' . assert (
            pts_to_parsed_strong_prefix (parse_nlist (SZ.v (SZ.sub count 1sz)) p) tl_sl #(pm *. (sp /. 2.0R)) tl'
          );
          rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v (SZ.sub count 1sz)) p) tl_sl #(pm *. (sp /. 2.0R)) tl')
               as (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - 1) p) tl_sl #((pm *. sp) /. 2.0R) (List.Tot.tl l))
        };
      // Combine head trade (vmatch -> pts_to_parsed) and tail trade into product
      Trade.prod
        (vmatch pm_v res (List.Tot.hd l))
        (pts_to_parsed p hd_sl #((pm *. sp) /. 2.0R) (List.Tot.hd l))
        (base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l))
        (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - 1) p) tl_sl #((pm *. sp) /. 2.0R) (List.Tot.tl l));
      // Chain with nlist_hd_tl_strong_prefix trade
      Trade.trans
        (vmatch pm_v res (List.Tot.hd l) **
         base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l))
        (pts_to_parsed p hd_sl #((pm *. sp) /. 2.0R) (List.Tot.hd l) **
         pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - 1) p) tl_sl #((pm *. sp) /. 2.0R) (List.Tot.tl l))
        (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l);
      // Chain with fold trade
      intro (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l @==>
             base_iterator_match vmatch p pm (Serialized sp count payload) l)
        #emp
        fn _ {
          fold (base_iterator_match vmatch p pm (Serialized sp count payload) l)
        };
      Trade.trans
        (vmatch pm_v res (List.Tot.hd l) **
         base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l))
        (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l)
        (base_iterator_match vmatch p pm (Serialized sp count payload) l);
      // Swap hypothesis order: vmatch ** base_iterator_match -> base_iterator_match ** vmatch
      Trade.comm_l
        (vmatch pm_v res (List.Tot.hd l))
        (base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l))
        (base_iterator_match vmatch p pm (Serialized sp count payload) l);
      // Rewrite conclusion from (Serialized sp count payload) back to i
      rewrite (Trade.trade
                (base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l) **
                 vmatch pm_v res (List.Tot.hd l))
                (base_iterator_match vmatch p pm (Serialized sp count payload) l))
           as (Trade.trade
                (base_iterator_match vmatch p pm (Serialized (sp /. 2.0R) (SZ.sub count 1sz) tl_sl) (List.Tot.tl l) **
                 vmatch pm_v res (List.Tot.hd l))
                (base_iterator_match vmatch p pm i l));
      res
    }
  }
}

#pop-options

// Helper: splitAt with positive n gives Cons result and splits into hd/tl
let rec lemma_splitAt_cons (#a: Type) (n: pos) (l: list a)
  : Lemma
    (requires n <= List.Tot.length l /\ Cons? l)
    (ensures (
      Cons? (fst (List.Tot.splitAt n l)) /\
      List.Tot.hd (fst (List.Tot.splitAt n l)) == List.Tot.hd l /\
      List.Tot.tl (fst (List.Tot.splitAt n l)) == fst (List.Tot.splitAt (n - 1) (List.Tot.tl l))
    ))
  = ()

// Helper: Cons? prefix implies positive count
let lemma_Cons_splitAt_pos (#a: Type) (n: nat) (l: list a)
  : Lemma
    (requires n <= List.Tot.length l /\ Cons? (fst (List.Tot.splitAt n l)))
    (ensures n > 0)
  = ()

// Determinism of pts_to_parsed_strong_prefix: same slice at same perm implies same value
#push-options "--z3rlimit 20"
let pts_to_parsed_strong_prefix'
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: S.slice byte) (#pm: perm) (v: t) : slprop
  = pts_to_parsed_strong_prefix p input #pm v

let s_pts_to (#t: Type) (s: S.slice t) (#p: perm) (v: Seq.seq t) : slprop
  = S.pts_to s #p v

ghost fn pts_to_parsed_strong_prefix_det
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: S.slice byte)
  (#pm: perm) (#v1: Ghost.erased t) (#v2: Ghost.erased t)
requires
  pts_to_parsed_strong_prefix p input #pm v1 **
  pts_to_parsed_strong_prefix' p input #pm v2
ensures
  pts_to_parsed_strong_prefix p input #pm v1 **
  pts_to_parsed_strong_prefix' p input #pm v2 **
  pure (v1 == v2)
{
  unfold (pts_to_parsed_strong_prefix p input #pm v1);
  with w1 . assert (S.pts_to input #pm w1);
  rewrite (S.pts_to input #pm w1) as (s_pts_to input #pm w1);
  rewrite (pts_to_parsed_strong_prefix' p input #pm v2)
       as (pts_to_parsed_strong_prefix p input #pm v2);
  unfold (pts_to_parsed_strong_prefix p input #pm v2);
  with w2 . assert (S.pts_to input #pm w2);
  rewrite (s_pts_to input #pm w1) as (S.pts_to input #pm w1);
  S.gather input;
  S.share input;
  fold (pts_to_parsed_strong_prefix p input #pm v1);
  fold (pts_to_parsed_strong_prefix p input #pm v2);
  rewrite (pts_to_parsed_strong_prefix p input #pm v2)
       as (pts_to_parsed_strong_prefix' p input #pm v2);
}
#pop-options

#push-options "--z3rlimit 80"

fn rec iterator_next
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
  (#k: parser_kind)
  (p: parser k u)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (rd: (pv: perm) -> zero_copy_parse (vmatch pv) p)
  (pm: perm)
  (pi: R.ref (iterator t))
  (#i: Ghost.erased (iterator t))
  (#l: Ghost.erased (list u) { Cons? l })
requires
  R.pts_to pi i **
  iterator_match vmatch p pm i l
returns res: t
ensures exists* (i': iterator t) (pm_match: perm) (pm_v: perm) .
  R.pts_to pi i' **
  iterator_match vmatch p pm_match i' (List.Tot.tl l) **
  vmatch pm_v res (List.Tot.hd l) **
  Trade.trade
    (iterator_match vmatch p pm_match i' (List.Tot.tl l) **
     vmatch pm_v res (List.Tot.hd l))
    (iterator_match vmatch p pm i l)
decreases (iterator_depth i)
{
  let iv = !pi;
  match iv {
    Base bi -> {
      rewrite (iterator_match vmatch p pm i l)
           as (iterator_match vmatch p pm (Base bi) l);
      unfold (iterator_match vmatch p pm (Base bi) l);
      let mut pb = bi;
      let res = base_iterator_next vmatch p sq j rd pm pb;
      with bi_new pm_bi pm_v . assert (
        R.pts_to pb bi_new **
        base_iterator_match vmatch p pm_bi bi_new (List.Tot.tl l) **
        vmatch pm_v res (List.Tot.hd l) **
        Trade.trade
          (base_iterator_match vmatch p pm_bi bi_new (List.Tot.tl l) **
           vmatch pm_v res (List.Tot.hd l))
          (base_iterator_match vmatch p pm bi l)
      );
      let bi_val = !pb;
      R.forget_init pi;
      pi := Base bi_val;
      fold (iterator_match vmatch p pm_bi (Base #t bi_val) (List.Tot.tl l));
      intro (iterator_match vmatch p pm_bi (Base #t bi_val) (List.Tot.tl l) **
             vmatch pm_v res (List.Tot.hd l) @==>
             iterator_match vmatch p pm (Base #t bi) l)
        #(Trade.trade
            (base_iterator_match vmatch p pm_bi bi_val (List.Tot.tl l) **
             vmatch pm_v res (List.Tot.hd l))
            (base_iterator_match vmatch p pm bi l))
        fn _ {
          unfold (iterator_match vmatch p pm_bi (Base #t bi_val) (List.Tot.tl l));
          Trade.elim
            (base_iterator_match vmatch p pm_bi bi_val (List.Tot.tl l) **
             vmatch pm_v res (List.Tot.hd l))
            (base_iterator_match vmatch p pm bi l);
          fold (iterator_match vmatch p pm (Base #t bi) l);
        };
      rewrite (iterator_match vmatch p pm_bi (Base #t bi_val) (List.Tot.tl l) **
               vmatch pm_v res (List.Tot.hd l) @==>
               iterator_match vmatch p pm (Base #t bi) l)
           as (iterator_match vmatch p pm_bi (Base #t bi_val) (List.Tot.tl l) **
               vmatch pm_v res (List.Tot.hd l) @==>
               iterator_match vmatch p pm i l);
      res
    }
    Append depth count before ap after -> {
      rewrite (iterator_match vmatch p pm i l)
           as (iterator_match vmatch p pm (Append depth count before ap after) l);
      unfold (iterator_match vmatch p pm (Append depth count before ap after) l);
      with i1 i2 l2 . assert (
        base_iterator_match vmatch p pm before i1 **
        pts_to after #(pm *. ap) i2 **
        iterator_match vmatch p pm i2 l2 **
        pure (
          SZ.v count <= List.Tot.length i1 + List.Tot.length l2 /\
          l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1 l2)) /\
          iterator_depth i2 < Ghost.reveal depth
        )
      );
      let before_len = base_iterator_length vmatch p pm before;
      if (before_len = 0sz) {
        // === EMPTY BEFORE CASE ===
        List.Tot.append_length i1 l2;
        lemma_Cons_splitAt_pos (SZ.v count) (List.Tot.append i1 l2);
        // Read concrete i2 value from reference
        let i2_val = R.op_Bang after;
        rewrite (iterator_match vmatch p pm i2 l2)
             as (iterator_match vmatch p pm i2_val l2);
        let i_trunc = iterator_truncate vmatch vmatch_share vmatch_gather p pm i2_val #l2 count;
        with pm_trunc . assert (
          iterator_match vmatch p pm_trunc i_trunc (fst (List.Tot.splitAt (SZ.v count) l2))
        );
        rewrite (iterator_match vmatch p pm_trunc i_trunc (fst (List.Tot.splitAt (SZ.v count) l2)))
             as (iterator_match vmatch p pm_trunc i_trunc l);
        rewrite (iterator_match vmatch p pm_trunc i_trunc (fst (List.Tot.splitAt (SZ.v count) l2)) @==>
                 iterator_match vmatch p pm i2_val l2)
             as (iterator_match vmatch p pm_trunc i_trunc l @==>
                 iterator_match vmatch p pm i2_val l2);
        let mut local = i_trunc;
        let res = iterator_next vmatch vmatch_share vmatch_gather p sq j rd pm_trunc local;
        with i_next pm_next pm_v . assert (
          R.pts_to local i_next **
          iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
          vmatch pm_v res (List.Tot.hd l) **
          Trade.trade
            (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
             vmatch pm_v res (List.Tot.hd l))
            (iterator_match vmatch p pm_trunc i_trunc l)
        );
        let i_next_val = !local;
        R.forget_init pi;
        pi := i_next_val;
        // Chain: (pm_next, i_next, tl l) -> (pm_trunc, i_trunc, l) -> (pm, i2_val, l2)
        Trade.trans
          (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
           vmatch pm_v res (List.Tot.hd l))
          (iterator_match vmatch p pm_trunc i_trunc l)
          (iterator_match vmatch p pm i2_val l2);
        // Rewrite trade conclusion from i2_val to i2
        rewrite (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
                 vmatch pm_v res (List.Tot.hd l) @==>
                 iterator_match vmatch p pm i2_val l2)
             as (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
                 vmatch pm_v res (List.Tot.hd l) @==>
                 iterator_match vmatch p pm i2 l2);
        // Build: (pm, i2, l2) -> iterator_match pm (Append ...) l
        intro (iterator_match vmatch p pm i2 l2 @==>
               iterator_match vmatch p pm (Append depth count before ap after) l)
          #(base_iterator_match vmatch p pm before i1 **
            pts_to after #(pm *. ap) i2 **
            pure (
              SZ.v count <= List.Tot.length i1 + List.Tot.length l2 /\
              Ghost.reveal l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1 l2)) /\
              iterator_depth i2 < Ghost.reveal depth
            ))
          fn _ {
            fold (iterator_match vmatch p pm (Append depth count before ap after) l);
          };
        Trade.trans
          (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
           vmatch pm_v res (List.Tot.hd l))
          (iterator_match vmatch p pm i2 l2)
          (iterator_match vmatch p pm (Append depth count before ap after) l);
        rewrite (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
                 vmatch pm_v res (List.Tot.hd l) @==>
                 iterator_match vmatch p pm (Append depth count before ap after) l)
             as (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
                 vmatch pm_v res (List.Tot.hd l) @==>
                 iterator_match vmatch p pm i l);
        res
      } else {
        // === NON-EMPTY BEFORE CASE ===
        let mut pb = before;
        let res = base_iterator_next vmatch p sq j rd pm pb;
        with bi_new pm_v . assert (
          R.pts_to pb bi_new **
          base_iterator_match vmatch p pm bi_new (List.Tot.tl i1) **
          vmatch pm_v res (List.Tot.hd i1) **
          Trade.trade
            (base_iterator_match vmatch p pm bi_new (List.Tot.tl i1) **
             vmatch pm_v res (List.Tot.hd i1))
            (base_iterator_match vmatch p pm before i1)
        );
        // hd i1 == hd l
        List.Tot.append_length i1 l2;
        assert (pure (Cons? (fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1 l2)))));
        lemma_Cons_splitAt_pos (SZ.v count) (List.Tot.append i1 l2);
        assert (pure (Cons? (List.Tot.append i1 l2)));
        lemma_splitAt_cons (SZ.v count) (List.Tot.append i1 l2);
        rewrite (vmatch pm_v res (List.Tot.hd i1))
             as (vmatch pm_v res (List.Tot.hd l));
        rewrite (Trade.trade
                  (base_iterator_match vmatch p pm bi_new (List.Tot.tl i1) **
                   vmatch pm_v res (List.Tot.hd i1))
                  (base_iterator_match vmatch p pm before i1))
             as (Trade.trade
                  (base_iterator_match vmatch p pm bi_new (List.Tot.tl i1) **
                   vmatch pm_v res (List.Tot.hd l))
                  (base_iterator_match vmatch p pm before i1));
        let bi_new_val = !pb;
        R.forget_init pi;
        pi := Append depth (SZ.sub count 1sz) bi_new_val ap after;
        lemma_splitAt_fst_length (SZ.v count) (List.Tot.append i1 l2);
        // Share everything to fold at pm/2 and stash the other halves
        // Share base_iterator_match: pm -> pm/2 x2
        base_iterator_match_share vmatch vmatch_share p bi_new;
        rewrite (base_iterator_match vmatch p (pm /. 2.0R) bi_new (List.Tot.tl i1))
             as (base_iterator_match vmatch p (pm /. 2.0R) bi_new_val (List.Tot.tl i1));
        // Share pts_to after: pm*ap -> (pm*ap)/2 x2
        R.share after;
        // Share iterator_match: pm -> pm/2 x2
        iterator_match_share vmatch vmatch_share p i2;
        // Fold new Append at pm/2
        fold (iterator_match vmatch p (pm /. 2.0R) (Append #t depth (SZ.sub count 1sz) bi_new_val ap after) (List.Tot.tl l));
        // Trade: unfold at pm/2, gather with stashed pm/2 halves, use Tb, fold original
        intro (iterator_match vmatch p (pm /. 2.0R) (Append #t depth (SZ.sub count 1sz) bi_new_val ap after) (List.Tot.tl l) **
               vmatch pm_v res (List.Tot.hd l) @==>
               iterator_match vmatch p pm (Append #t depth count before ap after) l)
          #(Trade.trade
              (base_iterator_match vmatch p pm bi_new (List.Tot.tl i1) **
               vmatch pm_v res (List.Tot.hd l))
              (base_iterator_match vmatch p pm before i1) **
            base_iterator_match vmatch p (pm /. 2.0R) bi_new (List.Tot.tl i1) **
            pts_to after #((pm *. ap) /. 2.0R) i2 **
            iterator_match vmatch p (pm /. 2.0R) i2 l2 **
            pure (
              SZ.v count <= List.Tot.length i1 + List.Tot.length l2 /\
              Ghost.reveal l == fst (List.Tot.splitAt (SZ.v count) (List.Tot.append i1 l2)) /\
              iterator_depth i2 < Ghost.reveal depth
            ))
          fn _ {
            // Rewrite stashed base_iterator_match to primed alias before unfold
            rewrite (base_iterator_match vmatch p (pm /. 2.0R) bi_new (List.Tot.tl i1))
                 as (base_iterator_match' vmatch p (pm /. 2.0R) bi_new (List.Tot.tl i1));
            unfold (iterator_match vmatch p (pm /. 2.0R) (Append #t depth (SZ.sub count 1sz) bi_new_val ap after) (List.Tot.tl l));
            with i1_new i2_new l2_new . assert (
              base_iterator_match vmatch p (pm /. 2.0R) bi_new_val i1_new **
              pts_to after #((pm /. 2.0R) *. ap) i2_new **
              iterator_match vmatch p (pm /. 2.0R) i2_new l2_new
            );
            // Gather base_iterator_match: (pm/2 + pm/2) = pm
            rewrite (base_iterator_match vmatch p (pm /. 2.0R) bi_new_val i1_new)
                 as (base_iterator_match vmatch p (pm /. 2.0R) bi_new i1_new);
            let i1p : list u = i1_new;
            let i1bp : list u = List.Tot.tl i1;
            rewrite (base_iterator_match vmatch p (pm /. 2.0R) bi_new i1_new)
                 as (base_iterator_match vmatch p (pm /. 2.0R) bi_new i1p);
            rewrite (base_iterator_match' vmatch p (pm /. 2.0R) bi_new (List.Tot.tl i1))
                 as (base_iterator_match vmatch p (pm /. 2.0R) bi_new i1bp);
            base_iterator_match_gather vmatch vmatch_gather p bi_new
              #(pm /. 2.0R) #i1p #(pm /. 2.0R) #i1bp;
            // Now: base_iterator_match (pm/2 + pm/2) bi_new i1p, pure (i1p == i1bp)
            // i1_new == tl i1
            rewrite (base_iterator_match vmatch p (pm /. 2.0R +. pm /. 2.0R) bi_new i1p)
                 as (base_iterator_match vmatch p pm bi_new (List.Tot.tl i1));
            // Gather pts_to after
            R.gather after;
            rewrite (pts_to after #((pm /. 2.0R) *. ap +. (pm *. ap) /. 2.0R) i2_new)
                 as (pts_to after #(pm *. ap) i2);
            // Gather iterator_match
            let l2p : list u = l2_new;
            rewrite (iterator_match vmatch p (pm /. 2.0R) i2_new l2_new)
                 as (iterator_match vmatch p (pm /. 2.0R) i2_new l2p);
            rewrite (iterator_match vmatch p (pm /. 2.0R) i2_new l2p)
                 as (iterator_match vmatch p (pm /. 2.0R) i2 l2p);
            let l2bp : list u = l2;
            rewrite (iterator_match vmatch p (pm /. 2.0R) i2 l2)
                 as (iterator_match vmatch p (pm /. 2.0R) i2 l2bp);
            rewrite (iterator_match vmatch p (pm /. 2.0R) i2 l2bp)
                 as (iterator_match' vmatch p (pm /. 2.0R) i2 l2bp);
            rewrite (iterator_match vmatch p (pm /. 2.0R) i2 l2p)
                 as (iterator_match vmatch p (pm /. 2.0R) i2 l2p);
            iterator_match_gather vmatch vmatch_gather p i2
              (pm /. 2.0R) #l2p (pm /. 2.0R) #l2bp;
            rewrite (iterator_match vmatch p (pm /. 2.0R +. pm /. 2.0R) i2 l2p)
                 as (iterator_match vmatch p pm i2 l2);
            // Now use Tb
            Trade.elim
              (base_iterator_match vmatch p pm bi_new (List.Tot.tl i1) **
               vmatch pm_v res (List.Tot.hd l))
              (base_iterator_match vmatch p pm before i1);
            List.Tot.append_length i1 l2;
            lemma_splitAt_fst_length (SZ.v count) (List.Tot.append i1 l2);
            fold (iterator_match vmatch p pm (Append #t depth count before ap after) l);
          };
        rewrite (iterator_match vmatch p (pm /. 2.0R) (Append #t depth (SZ.sub count 1sz) bi_new_val ap after) (List.Tot.tl l) **
                 vmatch pm_v res (List.Tot.hd l) @==>
                 iterator_match vmatch p pm (Append #t depth count before ap after) l)
             as (iterator_match vmatch p (pm /. 2.0R) (Append #t depth (SZ.sub count 1sz) bi_new_val ap after) (List.Tot.tl l) **
                 vmatch pm_v res (List.Tot.hd l) @==>
                 iterator_match vmatch p pm i l);
        res
      }
    }
  }
}

#pop-options

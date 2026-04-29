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
module LPS = LowParse.Pulse.Base
open Pulse.Lib.Trade

let share_t = LowParse.PulseParse.Base.share_t

let gather_t = LowParse.PulseParse.Base.gather_t

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

let base_iterator_length
  (#t: Type)
  (i: base_iterator t)
: Tot SZ.t
= match i with
  | Empty -> 0sz
  | Singleton _ _ _ -> 1sz
  | Slice _ _ sl -> S.len sl
  | Serialized _ count _ -> count

ghost fn base_iterator_length_correct
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_iterator t)
  (#l: Ghost.erased (list u))
requires base_iterator_match vmatch p pm i l
ensures base_iterator_match vmatch p pm i l ** pure (SZ.v (base_iterator_length i) == List.Tot.length l)
{
  match i {
    Empty -> {
      unfold (base_iterator_match vmatch p pm (Empty #t) l);
      fold (base_iterator_match vmatch p pm (Empty #t) l);
      rewrite (base_iterator_match vmatch p pm (Empty #t) l)
           as (base_iterator_match vmatch p pm i l);
    }
    Singleton sp sv s -> {
      unfold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
      fold (base_iterator_match vmatch p pm (Singleton sp sv s) l);
      rewrite (base_iterator_match vmatch p pm (Singleton sp sv s) l)
           as (base_iterator_match vmatch p pm i l);
    }
    Slice sp sv sl -> {
      unfold (base_iterator_match vmatch p pm (Slice sp sv sl) l);
      SM.seq_list_match_length (vmatch (pm *. sv)) _ l;
      S.pts_to_len sl;
      fold (base_iterator_match vmatch p pm (Slice sp sv sl) l);
      rewrite (base_iterator_match vmatch p pm (Slice sp sv sl) l)
           as (base_iterator_match vmatch p pm i l);
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match vmatch p pm (Serialized sp count pl) l);
      fold (base_iterator_match vmatch p pm (Serialized sp count pl) l);
      rewrite (base_iterator_match vmatch p pm (Serialized sp count pl) l)
           as (base_iterator_match vmatch p pm i l);
    }
  }
}

let iterator_length
  (#t: Type)
  (i: iterator t)
: Tot SZ.t
= match i with
  | Base bi -> base_iterator_length bi
  | Append _ count _ _ _ -> count

ghost fn iterator_length_correct
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: iterator t)
  (#l: Ghost.erased (list u))
requires iterator_match vmatch p pm i l
ensures iterator_match vmatch p pm i l ** pure (SZ.v (iterator_length i) == List.Tot.length l)
{
  match i {
    Base bi -> {
      unfold (iterator_match vmatch p pm (Base bi) l);
      base_iterator_length_correct vmatch p pm bi;
      fold (iterator_match vmatch p pm (Base bi) l);
      rewrite (iterator_match vmatch p pm (Base bi) l)
           as (iterator_match vmatch p pm i l);
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
  iterator_length_correct vmatch p pm i;
  let len = iterator_length i;
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

let s_pts_to_explicit (#t: Type) (s: S.slice t) (p: perm) (v: Seq.seq t) : slprop
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
      base_iterator_length_correct vmatch p pm before;
      let before_len = base_iterator_length before;
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

// Helper: splitAt at full length is identity
let rec lemma_splitAt_length (#a: Type) (l: list a) : Lemma
  (ensures (fst (List.Tot.splitAt (List.Tot.length l) l) == l))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: tl -> lemma_splitAt_length tl

#push-options "--z3rlimit 80"

// Insert an element before the current iterator position.
// Result iterator matches (v :: l) at pm/2.
// Trade restores original iterator_match, spare ref, and Singleton resources.
fn iterator_insert_before
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pi: R.ref (iterator t))
  (#i: Ghost.erased (iterator t))
  (#l: Ghost.erased (list u))
  (spare: R.ref (iterator t))
  (#i_spare: Ghost.erased (iterator t))
  (elem_ref: R.ref t)
  (#elem: Ghost.erased t)
  (pm_v: perm)
  (#v: Ghost.erased u)
requires
  R.pts_to pi i **
  iterator_match vmatch p pm i l **
  R.pts_to spare i_spare **
  R.pts_to elem_ref elem **
  vmatch pm_v elem v **
  pure (SZ.fits (List.Tot.length (Ghost.reveal l) + 1))
returns _: unit
ensures exists* (i': iterator t) .
  R.pts_to pi i' **
  iterator_match vmatch p (pm /. 2.0R) i' (Ghost.reveal v :: Ghost.reveal l) **
  Trade.trade
    (iterator_match vmatch p (pm /. 2.0R) i' (Ghost.reveal v :: Ghost.reveal l))
    (iterator_match vmatch p pm i l **
     R.pts_to spare (Ghost.reveal i) **
     base_iterator_match vmatch p pm (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v])
{
  let i_val = !pi;

  // Compute count for the Append
  iterator_length_correct vmatch p pm i_val;
  let len = iterator_length i_val;
  let count = SZ.add len 1sz;

  let depth : Ghost.erased nat = Ghost.hide (1 + iterator_depth i_val);

  // Write current iterator to spare (for Append's after)
  R.forget_init spare;
  spare := i_val;

  // Rewrite elem_ref and vmatch permissions for Singleton fold
  rewrite (R.pts_to elem_ref (Ghost.reveal elem))
       as (R.pts_to elem_ref #(pm *. (1.0R /. pm)) (Ghost.reveal elem));
  rewrite (vmatch pm_v (Ghost.reveal elem) (Ghost.reveal v))
       as (vmatch (pm *. (pm_v /. pm)) (Ghost.reveal elem) (Ghost.reveal v));

  // Fold base_iterator_match for the Singleton
  fold (base_iterator_match vmatch p pm (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v]);

  // Rewrite pts_to spare permission: 1.0R = pm *. (1.0R /. pm)
  rewrite (R.pts_to spare i_val)
       as (R.pts_to spare #(pm *. (1.0R /. pm)) i_val);

  // Prove splitAt constraint for the Append fold
  lemma_splitAt_length (Ghost.reveal v :: Ghost.reveal l);

  // Share everything for the trade pattern (pm -> pm/2 x2)
  base_iterator_match_share vmatch vmatch_share p (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref);

  R.share spare;
  rewrite (R.pts_to spare #((pm *. (1.0R /. pm)) /. 2.0R) i_val)
       as (R.pts_to spare #((pm /. 2.0R) *. (1.0R /. pm)) i_val);

  iterator_match_share vmatch vmatch_share p i_val;

  // Fold Append at pm/2
  fold (iterator_match vmatch p (pm /. 2.0R)
    (Append #t depth count (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare)
    (Ghost.reveal v :: Ghost.reveal l));

  // Write pi
  R.forget_init pi;
  pi := Append depth count (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare;

  // Build trade: unfold at pm/2, gather with stashed pm/2 halves, produce output
  intro (iterator_match vmatch p (pm /. 2.0R)
           (Append #t depth count (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare)
           (Ghost.reveal v :: Ghost.reveal l) @==>
         iterator_match vmatch p pm i l **
         R.pts_to spare (Ghost.reveal i) **
         base_iterator_match vmatch p pm (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v])
    #(base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v] **
      R.pts_to spare #((pm *. (1.0R /. pm)) /. 2.0R) i_val **
      iterator_match vmatch p (pm /. 2.0R) i_val (Ghost.reveal l) **
      pure (
        SZ.v count <= 1 + List.Tot.length (Ghost.reveal l) /\
        i_val == Ghost.reveal i
      ))
    fn _ {
      // Rewrite stashed resources to primed aliases BEFORE unfold
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v])
           as (base_iterator_match' vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v]);

      // Unfold Append at pm/2
      unfold (iterator_match vmatch p (pm /. 2.0R)
        (Append #t depth count (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare)
        (Ghost.reveal v :: Ghost.reveal l));
      with i1 i2 l2 . assert (
        base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) i1 **
        R.pts_to spare #((pm /. 2.0R) *. (1.0R /. pm)) i2 **
        iterator_match vmatch p (pm /. 2.0R) i2 l2
      );

      // Gather base_iterator_match: (pm/2 + pm/2) = pm
      let i1p : list u = i1;
      rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) i1)
           as (base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) i1p);
      let i1stash : list u = [Ghost.reveal v];
      rewrite (base_iterator_match' vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v])
           as (base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) i1stash);
      base_iterator_match_gather vmatch vmatch_gather p (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref)
        #(pm /. 2.0R) #i1p #(pm /. 2.0R) #i1stash;
      rewrite (base_iterator_match vmatch p (pm /. 2.0R +. pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) i1p)
           as (base_iterator_match vmatch p pm (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v]);

      // Gather R.pts_to spare: proves i2 == i_val
      R.gather spare;
      rewrite (R.pts_to spare #((pm /. 2.0R) *. (1.0R /. pm) +. (pm *. (1.0R /. pm)) /. 2.0R) i2)
           as (R.pts_to spare #(pm *. (1.0R /. pm)) i2);
      rewrite (R.pts_to spare #(pm *. (1.0R /. pm)) i2)
           as (R.pts_to spare i2);
      rewrite (R.pts_to spare i2)
           as (R.pts_to spare (Ghost.reveal i));

      // Gather iterator_match: proves l2 == Ghost.reveal l
      let l2p : list u = l2;
      rewrite (iterator_match vmatch p (pm /. 2.0R) i2 l2)
           as (iterator_match vmatch p (pm /. 2.0R) i2 l2p);
      rewrite (iterator_match vmatch p (pm /. 2.0R) i2 l2p)
           as (iterator_match vmatch p (pm /. 2.0R) i_val l2p);
      let l_stash : list u = Ghost.reveal l;
      rewrite (iterator_match vmatch p (pm /. 2.0R) i_val (Ghost.reveal l))
           as (iterator_match vmatch p (pm /. 2.0R) i_val l_stash);
      rewrite (iterator_match vmatch p (pm /. 2.0R) i_val l_stash)
           as (iterator_match' vmatch p (pm /. 2.0R) i_val l_stash);
      iterator_match_gather vmatch vmatch_gather p i_val
        (pm /. 2.0R) #l2p (pm /. 2.0R) #l_stash;
      rewrite (iterator_match vmatch p (pm /. 2.0R +. pm /. 2.0R) i_val l2p)
           as (iterator_match vmatch p pm i l);
    };
  ()
}

#pop-options

// Comparison function type: returns true iff lt_ord v1 v2
let lt_impl_t (#t #u: Type0) (vmatch: perm -> t -> u -> slprop) (lt_ord: u -> u -> bool) =
  (#pm1: perm) -> (x1: t) -> (#v1: Ghost.erased u) ->
  (#pm2: perm) -> (x2: t) -> (#v2: Ghost.erased u) ->
  stt bool
    (vmatch pm1 x1 v1 ** vmatch pm2 x2 v2)
    (fun b -> vmatch pm1 x1 v1 ** vmatch pm2 x2 v2 **
              pure (b == lt_ord (Ghost.reveal v1) (Ghost.reveal v2)))

// =====================================================================
// Full-list sorted insertion: insert v into sorted l, returning
// an iterator over the full sorted result take k l ++ (v :: drop k l).
// =====================================================================

// Pure function: compute the insertion position in a sorted list.
// Returns None for duplicates, Some k for the insertion position.
let rec sorted_insert_pos (#t: Type) (lt_ord: t -> t -> bool) (v: t) (l: list t) : option nat =
  match l with
  | [] -> Some 0
  | hd :: tl ->
    if lt_ord v hd then Some 0
    else if lt_ord hd v then
      match sorted_insert_pos lt_ord v tl with
      | None -> None
      | Some k -> Some (k + 1)
    else None

// Lemma: sorted_insert_pos returns a valid position
let rec lemma_sorted_insert_pos_bound (#t: Type) (lt_ord: t -> t -> bool) (v: t) (l: list t)
  : Lemma
    (ensures (match sorted_insert_pos lt_ord v l with
              | None -> True
              | Some k -> k <= List.Tot.length l))
    (decreases l)
= match l with
  | [] -> ()
  | hd :: tl ->
    if lt_ord v hd then ()
    else if lt_ord hd v then
      (match sorted_insert_pos lt_ord v tl with
       | None -> ()
       | Some _ -> lemma_sorted_insert_pos_bound lt_ord v tl)
    else ()

// Lemma: inserting at the sorted_insert_pos position preserves sortedness
let rec lemma_sorted_insert_sorted (#t: Type) (lt_ord: t -> t -> bool) (v: t) (l: list t)
  : Lemma
    (requires List.Tot.sorted lt_ord l /\ Some? (sorted_insert_pos lt_ord v l))
    (ensures (
      let Some k = sorted_insert_pos lt_ord v l in
      k <= List.Tot.length l /\
      List.Tot.sorted lt_ord
        (List.Tot.append (fst (List.Tot.splitAt k l)) (v :: snd (List.Tot.splitAt k l)))))
    (decreases l)
= match l with
  | [] -> ()
  | hd :: tl ->
    if lt_ord v hd then ()
    else if lt_ord hd v then begin
      lemma_sorted_insert_sorted lt_ord v tl;
      let Some k_tl = sorted_insert_pos lt_ord v tl in
      lemma_sorted_insert_pos_bound lt_ord v tl;
      lemma_splitAt_append k_tl tl
    end
    else ()

// Lemma: parse_nlist_eq consequence for jumping
let lemma_parse_nlist_jump_step
  (#k: parser_kind) (#t: Type) (p: parser k t) (n: pos) (w: bytes)
  : Lemma
    (requires Some? (parse (parse_nlist n p) w) /\ k.parser_kind_subkind == Some ParserStrong)
    (ensures (
      parse_nlist_eq n p w;
      Some? (parse p w) /\ (
      let Some (_, consumed_hd) = parse p w in
      consumed_hd <= Seq.length w /\
      Some? (parse (parse_nlist (n - 1) p) (Seq.slice w consumed_hd (Seq.length w))))))
= parse_nlist_eq n p w;
  parser_kind_prop_equiv k p

#push-options "--z3rlimit 120"

// count_insert_pos: scan the iterator using iterator_next, find the insertion
// position for v (or detect duplicate), and fully restore the iterator.
fn rec count_insert_pos
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
  (lt_ord: (u -> u -> bool))
  (lt_impl: lt_impl_t vmatch lt_ord)
  (pm: perm)
  (pi: R.ref (iterator t))
  (#i: Ghost.erased (iterator t))
  (#l: Ghost.erased (list u))
  (elem_ref: R.ref t)
  (#elem: Ghost.erased t)
  (pm_v: perm)
  (#v: Ghost.erased u)
requires
  R.pts_to pi i **
  iterator_match vmatch p pm i l **
  R.pts_to elem_ref elem **
  vmatch pm_v elem v **
  pure (List.Tot.sorted lt_ord (Ghost.reveal l) /\
        SZ.fits (List.Tot.length (Ghost.reveal l) + 1))
returns res: option SZ.t
ensures
  R.pts_to pi i **
  iterator_match vmatch p pm i l **
  R.pts_to elem_ref elem **
  vmatch pm_v elem v **
  pure (
    match res with
    | None -> sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l) == None
    | Some k -> sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l) == Some (SZ.v k) /\
                SZ.v k <= List.Tot.length (Ghost.reveal l)
  )
decreases (List.Tot.length (Ghost.reveal l))
{
  let saved_i = !pi;
  rewrite (iterator_match vmatch p pm i l)
       as (iterator_match vmatch p pm saved_i l);

  let is_empty = iterator_is_empty vmatch p pm saved_i;
  if is_empty {
    // Empty list: insert at position 0
    rewrite (iterator_match vmatch p pm saved_i l)
         as (iterator_match vmatch p pm i l);
    Some 0sz
  } else {
    // Get head element
    rewrite (iterator_match vmatch p pm saved_i l)
         as (iterator_match vmatch p pm i l);
    let head = iterator_next vmatch vmatch_share vmatch_gather p sq j rd pm pi;

    with i_next pm_next pm_v_next . assert (
      R.pts_to pi i_next **
      iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
      vmatch pm_v_next head (List.Tot.hd l) **
      Trade.trade
        (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
         vmatch pm_v_next head (List.Tot.hd l))
        (iterator_match vmatch p pm i l)
    );

    // Read elem_ref to get concrete value for comparison
    let elem_val = !elem_ref;

    // Compare: is v < head?
    let b_lt = lt_impl elem_val head;
    // Compare: is head < v?
    let b_gt = lt_impl head elem_val;

    if b_lt {
      // v < head: insert at position 0
      // Elim advance trade to restore original iterator
      Trade.elim
        (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
         vmatch pm_v_next head (List.Tot.hd l))
        (iterator_match vmatch p pm i l);

      // Restore pi
      R.forget_init pi;
      pi := saved_i;
      rewrite (R.pts_to pi saved_i) as (R.pts_to pi (Ghost.reveal i));

      Some 0sz
    } else {
      if b_gt {
        // head < v: recurse on tail
        let res = count_insert_pos vmatch vmatch_share vmatch_gather p sq j rd
          lt_ord lt_impl pm_next pi elem_ref pm_v;

        // Elim advance trade to restore original iterator
        Trade.elim
          (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
           vmatch pm_v_next head (List.Tot.hd l))
          (iterator_match vmatch p pm i l);

        // Restore pi
        R.forget_init pi;
        pi := saved_i;
        rewrite (R.pts_to pi saved_i) as (R.pts_to pi (Ghost.reveal i));

        match res {
          None -> { None #SZ.t }
          Some k_tail -> {
            // k_tail <= length (tl l) = length l - 1
            // so k_tail + 1 <= length l <= length l + 1, and SZ.fits (length l + 1) holds
            Some (SZ.add k_tail 1sz)
          }
        }
      } else {
        // Neither v < head nor head < v: duplicate
        Trade.elim
          (iterator_match vmatch p pm_next i_next (List.Tot.tl l) **
           vmatch pm_v_next head (List.Tot.hd l))
          (iterator_match vmatch p pm i l);

        // Restore pi
        R.forget_init pi;
        pi := saved_i;
        rewrite (R.pts_to pi saved_i) as (R.pts_to pi (Ghost.reveal i));

        None #SZ.t
      }
    }
  }
}

#pop-options

#push-options "--z3rlimit 80"

// Suffix value lemma: after jumping k elements, the suffix parses as drop k l
let rec lemma_parse_nlist_suffix
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: nat)
  (kk: nat)
  (w: bytes)
: Lemma
  (requires
    kk <= n /\
    k.parser_kind_subkind == Some ParserStrong /\
    Some? (parse (parse_nlist n p) w)
  )
  (ensures (
    lemma_parse_nlist_prefix p n kk w;
    let Some (l, consumed) = parse (parse_nlist n p) w in
    let Some (_, consumed_prefix) = parse (parse_nlist kk p) w in
    consumed_prefix <= Seq.length w /\
    (let suffix = Seq.slice w consumed_prefix (Seq.length w) in
    Some? (parse (parse_nlist (n - kk) p) suffix) /\
    (let Some (l_suffix, consumed_suffix) = parse (parse_nlist (n - kk) p) suffix in
     l_suffix == snd (List.Tot.splitAt kk l) /\
     consumed == consumed_prefix + consumed_suffix))
  ))
  (decreases kk)
= parse_nlist_kind_subkind n k;
  lemma_parse_nlist_prefix p n kk w;
  if kk = 0 then begin
    parse_nlist_eq 0 p w
  end else begin
    parse_nlist_eq n p w;
    parse_nlist_eq kk p w;
    parser_kind_prop_equiv k p;
    match parse p w with
    | Some (_, consumed_hd) ->
      parse_nlist_kind_subkind (n - 1) k;
      let w' = Seq.slice w consumed_hd (Seq.length w) in
      lemma_parse_nlist_suffix p (n - 1) (kk - 1) w';
      // IH gives us: parse_nlist (kk-1) on w' has consumed_prefix' bytes,
      // and suffix at consumed_prefix' in w' parses as drop (kk-1) of tail l
      // We know: consumed_prefix in w = consumed_hd + consumed_prefix' in w'
      // And: Seq.slice w consumed_prefix ... = Seq.slice w' consumed_prefix' ...
      let Some (l_full, consumed_full) = parse (parse_nlist n p) w in
      let Some (l_tail, consumed_tail) = parse (parse_nlist (n - 1) p) w' in
      let Some (_, consumed_prefix_tail) = parse (parse_nlist (kk - 1) p) w' in
      let Some (_, consumed_prefix) = parse (parse_nlist kk p) w in
      assert (consumed_prefix == consumed_hd + consumed_prefix_tail);
      assert (Seq.equal
        (Seq.slice w consumed_prefix (Seq.length w))
        (Seq.slice w' consumed_prefix_tail (Seq.length w')))
    | _ -> ()
  end

// Prefix consumed bytes lemma: the prefix parse consumed bytes equal the jump offset
let lemma_parse_nlist_prefix_consumed
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: nat)
  (kk: nat)
  (w: bytes)
: Lemma
  (requires
    kk <= n /\
    k.parser_kind_subkind == Some ParserStrong /\
    Some? (parse (parse_nlist n p) w)
  )
  (ensures (
    lemma_parse_nlist_prefix p n kk w;
    let Some (_, consumed_prefix) = parse (parse_nlist kk p) w in
    let Some (l, _) = parse (parse_nlist n p) w in
    consumed_prefix <= Seq.length w /\
    fst (List.Tot.splitAt kk l) == (let Some (v, _) = parse (parse_nlist kk p) w in v)
  ))
= lemma_parse_nlist_prefix p n kk w;
  parse_nlist_kind_subkind n k;
  parser_kind_prop_equiv (parse_nlist_kind kk k) (parse_nlist kk p)

#pop-options

// Extending an nlist parse by one more element: if nlist m parses w consuming consumed_m bytes,
// and one more element parses at offset consumed_m, then nlist (m+1) parses w consuming consumed_m + c_elem.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"

let rec lemma_parse_nlist_append_consumed
  (#k: parser_kind) (#t: Type) (p: parser k t) (m: nat) (w: bytes) (consumed_m: nat)
: Lemma
  (requires
    k.parser_kind_subkind == Some ParserStrong /\
    Some? (parse (parse_nlist m p) w) /\
    consumed_m <= Seq.length w /\
    consumed_m == snd (Some?.v (parse (parse_nlist m p) w)) /\
    Some? (parse p (Seq.slice w consumed_m (Seq.length w)))
  )
  (ensures (
    let c_elem = snd (Some?.v (parse p (Seq.slice w consumed_m (Seq.length w)))) in
    Some? (parse (parse_nlist (m + 1) p) w) /\
    snd (Some?.v (parse (parse_nlist (m + 1) p) w)) == consumed_m + c_elem
  ))
  (decreases m)
= parse_nlist_kind_subkind m k;
  parser_kind_prop_equiv (parse_nlist_kind m k) (parse_nlist m p);
  parser_kind_prop_equiv k p;
  if m = 0 then begin
    parse_nlist_eq 0 p w;
    parse_nlist_eq 1 p w;
    let Some (_, c1) = parse p w in
    parse_nlist_eq 0 p (Seq.slice w c1 (Seq.length w))
  end else begin
    parse_nlist_eq m p w;
    parse_nlist_eq (m + 1) p w;
    let Some (_, c1) = parse p w in
    let w' = Seq.slice w c1 (Seq.length w) in
    parse_nlist_kind_subkind (m - 1) k;
    parser_kind_prop_equiv (parse_nlist_kind (m - 1) k) (parse_nlist (m - 1) p);
    let Some (_, consumed_m1) = parse (parse_nlist (m - 1) p) w' in
    lemma_parse_nlist_append_consumed p (m - 1) w' consumed_m1
  end

#pop-options

// Jump n elements forward in a serialized payload, returning the byte offset
// after n elements. Payload is a slice with S.pts_to, and we need parse facts.
#push-options "--z3rlimit 200"

// Helper: if nlist n parses at offset off in w, then jumper_pre' holds for element at off
let lemma_nlist_jumper_pre
  (#k: parser_kind) (#t: Type) (p: parser k t) (n: pos) (off: SZ.t) (w: bytes)
  : Lemma
    (requires
      n > 0 /\
      SZ.v off <= Seq.length w /\
      Some? (parse (parse_nlist n p) (Seq.slice w (SZ.v off) (Seq.length w))) /\
      k.parser_kind_subkind == Some ParserStrong)
    (ensures
      LPS.jumper_pre' p off w)
= parse_nlist_eq n p (Seq.slice w (SZ.v off) (Seq.length w));
  parser_kind_prop_equiv k p

// Helper: validator_success gives the next parse position for nlist
let lemma_nlist_jump_advance
  (#k: parser_kind) (#t: Type) (p: parser k t) (n: pos) (off: SZ.t) (off_next: SZ.t) (w: bytes)
  : Lemma
    (requires
      SZ.v off <= Seq.length w /\
      Some? (parse (parse_nlist n p) (Seq.slice w (SZ.v off) (Seq.length w))) /\
      k.parser_kind_subkind == Some ParserStrong /\
      LPS.validator_success p off w off_next)
    (ensures (
      SZ.v off_next <= Seq.length w /\
      Some? (parse (parse_nlist (n - 1) p) (Seq.slice w (SZ.v off_next) (Seq.length w)))))
= parse_nlist_eq n p (Seq.slice w (SZ.v off) (Seq.length w));
  parser_kind_prop_equiv k p;
  let w' = Seq.slice w (SZ.v off) (Seq.length w) in
  match parse p w' with
  | Some (_, consumed) ->
    assert (SZ.v off + consumed == SZ.v off_next);
    let w_tail = Seq.slice w' consumed (Seq.length w') in
    assert (Seq.equal w_tail (Seq.slice w (SZ.v off_next) (Seq.length w)))
  | None -> ()

// Predicate for consumed bytes in nlist parse (avoids ill-typed elaboration in Pulse invariants)
let nlist_consumed_eq
  (#k: parser_kind) (#t: Type) (p: parser k t)
  (kk: nat) (w: bytes) (consumed: nat)
: prop
= Some? (parse (parse_nlist kk p) w) /\
  snd (Some?.v (parse (parse_nlist kk p) w)) <= Seq.length w /\
  snd (Some?.v (parse (parse_nlist kk p) w)) == consumed

fn jump_n
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (pm: perm)
  (payload: S.slice byte)
  (w: Ghost.erased (Seq.seq byte))
  (n: SZ.t)
  (kk: SZ.t)
  (off: SZ.t)
requires
  s_pts_to_explicit payload pm w **
  pure (
    SZ.v kk <= SZ.v n /\
    SZ.v off <= Seq.length w /\
    Some? (parse (parse_nlist (SZ.v n) p) (Seq.slice (Ghost.reveal w) (SZ.v off) (Seq.length (Ghost.reveal w)))) /\
    k.parser_kind_subkind == Some ParserStrong
  )
returns res: SZ.t
ensures
  s_pts_to_explicit payload pm w **
  pure (
    SZ.v kk <= SZ.v n /\
    SZ.v off <= Seq.length (Ghost.reveal w) /\
    SZ.v res <= Seq.length (Ghost.reveal w) /\
    SZ.v off <= SZ.v res /\
    Some? (parse (parse_nlist (SZ.v n - SZ.v kk) p) (Seq.slice (Ghost.reveal w) (SZ.v res) (Seq.length (Ghost.reveal w)))) /\
    nlist_consumed_eq p (SZ.v kk) (Seq.slice (Ghost.reveal w) (SZ.v off) (Seq.length (Ghost.reveal w))) (SZ.v res - SZ.v off)
  )
{
  let mut cur_off = off;
  let mut cur_n = n;
  let mut cur_kk = kk;
  let w_off : Ghost.erased bytes = Ghost.hide (Seq.slice (Ghost.reveal w) (SZ.v off) (Seq.length (Ghost.reveal w)));
  parse_nlist_eq 0 p (Ghost.reveal w_off);
  unfold (s_pts_to_explicit payload pm w);
  while (
    let kk_val = !cur_kk;
    (kk_val <> 0sz)
  ) invariant exists* off_v n_v kk_v .
      R.pts_to cur_off off_v **
      R.pts_to cur_n n_v **
      R.pts_to cur_kk kk_v **
      S.pts_to payload #pm (Ghost.reveal w) **
      pure (
        SZ.v kk_v <= SZ.v n_v /\
        SZ.v kk_v <= SZ.v kk /\
        SZ.v off <= SZ.v off_v /\
        SZ.v off_v <= Seq.length w /\
        Some? (parse (parse_nlist (SZ.v n_v) p) (Seq.slice (Ghost.reveal w) (SZ.v off_v) (Seq.length (Ghost.reveal w)))) /\
        SZ.v n_v - SZ.v kk_v == SZ.v n - SZ.v kk /\
        k.parser_kind_subkind == Some ParserStrong /\
        nlist_consumed_eq p (SZ.v kk - SZ.v kk_v) (Ghost.reveal w_off) (SZ.v off_v - SZ.v off)
      )
  {
    let off_v = !cur_off;
    let n_v = !cur_n;
    let kk_v = !cur_kk;
    lemma_nlist_jumper_pre p (SZ.v n_v) off_v (Ghost.reveal w);
    let off_next = j payload off_v;
    lemma_nlist_jump_advance p (SZ.v n_v) off_v off_next (Ghost.reveal w);
    // Extend consumed tracking: nlist (kk - kk_v) parsed w_off with consumed (off_v - off),
    // jumper parsed one element at off_v with consumed (off_next - off_v),
    // so nlist (kk - kk_v + 1) parses w_off with consumed (off_next - off).
    lemma_parse_nlist_append_consumed p (SZ.v kk - SZ.v kk_v) (Ghost.reveal w_off) (SZ.v off_v - SZ.v off);
    cur_off := off_next;
    cur_n := SZ.sub n_v 1sz;
    cur_kk := SZ.sub kk_v 1sz;
  };
  fold (s_pts_to_explicit payload pm w);
  !cur_off
}

#pop-options

#push-options "--z3rlimit 160 --fuel 2 --ifuel 1"

let lemma_parse_nlist_length
  (#k: parser_kind) (#t: Type) (p: parser k t) (n: nat) (w: bytes)
: Lemma
  (requires Some? (parse (parse_nlist n p) w))
  (ensures List.Tot.length (fst (Some?.v (parse (parse_nlist n p) w))) == n)
= ()

let list_prefix (#a: Type) (n: nat) (l: list a) : list a =
  fst (List.Tot.splitAt n l)

let list_suffix (#a: Type) (n: nat) (l: list a) : list a =
  snd (List.Tot.splitAt n l)

let lemma_list_prefix_length (#a: Type) (n: nat) (l: list a)
: Lemma
  (requires n <= List.Tot.length l)
  (ensures List.Tot.length (list_prefix n l) == n)
= lemma_splitAt_fst_length n l

let rec lemma_list_suffix_length (#a: Type) (n: nat) (l: list a)
: Lemma
  (requires n <= List.Tot.length l)
  (ensures List.Tot.length (list_suffix n l) == List.Tot.length l - n)
  (decreases n)
= if n = 0 then () else lemma_list_suffix_length (n - 1) (List.Tot.tl l)

let lemma_splitAt_list_prefix_suffix (#a: Type) (n: nat) (l: list a)
: Lemma
  (fst (List.Tot.splitAt n l) == list_prefix n l /\
   snd (List.Tot.splitAt n l) == list_suffix n l)
= ()

// Ghost helper: fold strong_prefix for a sub-slice (allows passing nlist-typed value)
ghost fn serialized_split_at_fold_prefix
  (#u: Type0)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (input: S.slice byte)
  (pm: perm)
  (#w: bytes)
  (#l: nlist n u)
requires
  S.pts_to input #pm w **
  pure (pts_to_parsed_strong_prefix_prop (parse_nlist n p) w l)
ensures
  pts_to_parsed_strong_prefix (parse_nlist n p) input #(pm /. 2.0R) l **
  Trade.trade
    (pts_to_parsed_strong_prefix (parse_nlist n p) input #(pm /. 2.0R) l)
    (S.pts_to input #pm w)
{
  pts_to_parsed_strong_prefix_intro (parse_nlist n p) input l;
}

#pop-options

// Helper lemma: connects prefix parsed value to list_prefix
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let lemma_serialized_split_prefix
  (#k: parser_kind) (#u: Type) (p: parser k u)
  (n: nat) (kk: nat) (w: bytes) (w1: bytes) (l: list u) (consumed: nat)
: Lemma
  (requires
    kk <= n /\
    k.parser_kind_subkind == Some ParserStrong /\
    Some? (parse (parse_nlist n p) w) /\
    fst (Some?.v (parse (parse_nlist n p) w)) == l /\
    Some? (parse (parse_nlist kk p) w) /\
    snd (Some?.v (parse (parse_nlist kk p) w)) == consumed /\
    consumed <= Seq.length w1 /\
    Seq.slice w 0 consumed == Seq.slice w1 0 consumed
  )
  (ensures
    Some? (parse (parse_nlist kk p) w1) /\
    (fst (Some?.v (parse (parse_nlist kk p) w1)) <: list u) == list_prefix kk l
  )
= lemma_parse_nlist_prefix_consumed p n kk w;
  parse_nlist_kind_subkind kk k;
  parser_kind_prop_equiv (parse_nlist_kind kk k) (parse_nlist kk p);
  parse_strong_prefix (parse_nlist kk p) w w1

let lemma_serialized_split_suffix
  (#k: parser_kind) (#u: Type) (p: parser k u)
  (n: nat) (kk: nat) (w: bytes) (w2: bytes) (l: list u) (consumed: nat)
: Lemma
  (requires
    kk <= n /\
    k.parser_kind_subkind == Some ParserStrong /\
    Some? (parse (parse_nlist n p) w) /\
    fst (Some?.v (parse (parse_nlist n p) w)) == l /\
    Some? (parse (parse_nlist kk p) w) /\
    snd (Some?.v (parse (parse_nlist kk p) w)) == consumed /\
    consumed <= Seq.length w /\
    w2 == Seq.slice w consumed (Seq.length w)
  )
  (ensures
    Some? (parse (parse_nlist (n - kk) p) w2) /\
    (fst (Some?.v (parse (parse_nlist (n - kk) p) w2)) <: list u) == list_suffix kk l
  )
= lemma_parse_nlist_prefix_consumed p n kk w;
  lemma_parse_nlist_suffix p n kk w
#pop-options

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"

// Split a Serialized base_iterator at position kk into prefix and suffix base_iterators.
fn serialized_split_at
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (pm: perm)
  (sp: perm)
  (count: SZ.t)
  (payload: S.slice byte)
  (kk: SZ.t { SZ.v kk <= SZ.v count })
  (#l: Ghost.erased (list u))
requires
  base_iterator_match vmatch p pm (Serialized sp count payload) l
returns res: (S.slice byte & S.slice byte)
ensures (
  let (prefix_sl, suffix_sl) = res in
  base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) (list_prefix (SZ.v kk) l) **
  base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) (list_suffix (SZ.v kk) l) **
  Trade.trade
    (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) (list_prefix (SZ.v kk) l) **
     base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) (list_suffix (SZ.v kk) l))
    (base_iterator_match vmatch p pm (Serialized sp count payload) l)
)
{
  // 1. Share base_iterator_match manually for Serialized case
  unfold (base_iterator_match vmatch p pm (Serialized sp count payload) l);
  with l' . assert (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l');
  pts_to_parsed_strong_prefix_share (parse_nlist (SZ.v count) p) payload #(pm *. sp) #l';
  rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm *. sp) /. 2.0R) l')
       as (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l');
  rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm *. sp) /. 2.0R) l')
       as (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l');
  fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l);
  fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l);

  // 2. Unfold copy 1 → get pts_to_parsed_strong_prefix → unfold → raw S.pts_to
  unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l);
  with l' . assert (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l');
  unfold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l');
  with w . assert (S.pts_to payload #((pm /. 2.0R) *. sp) w);
  rewrite (S.pts_to payload #((pm /. 2.0R) *. sp) w)
       as (S.pts_to payload #((pm *. sp) /. 2.0R) w);

  // Establish length of l' from parse properties
  lemma_parse_nlist_length p (SZ.v count) w;

  // 3. Jump to find byte offset of position kk
  fold (s_pts_to_explicit payload ((pm *. sp) /. 2.0R) w);
  let pos_k = jump_n sq j ((pm *. sp) /. 2.0R) payload w count kk 0sz;
  unfold (s_pts_to_explicit payload ((pm *. sp) /. 2.0R) w);

  // 4. Split S.pts_to at pos_k → prefix + suffix slices + trade
  let prefix_sl, suffix_sl = S.split_trade payload pos_k;
  with w1 . assert (S.pts_to prefix_sl #((pm *. sp) /. 2.0R) w1);
  with w2 . assert (S.pts_to suffix_sl #((pm *. sp) /. 2.0R) w2);

  // 5. Prove the parse facts for prefix and suffix
  lemma_parse_nlist_prefix p (SZ.v count) (SZ.v kk) w;
  lemma_parse_nlist_suffix p (SZ.v count) (SZ.v kk) w;
  lemma_parse_nlist_prefix_consumed p (SZ.v count) (SZ.v kk) w;
  parse_nlist_kind_subkind (SZ.v kk) k;
  parse_nlist_kind_subkind (SZ.v count - SZ.v kk) k;
  parser_kind_prop_equiv (parse_nlist_kind (SZ.v kk) k) (parse_nlist (SZ.v kk) p);
  Seq.lemma_eq_intro (Seq.slice (Ghost.reveal w) 0 (Seq.length (Ghost.reveal w))) (Ghost.reveal w);
  parse_strong_prefix (parse_nlist (SZ.v kk) p) (Ghost.reveal w) (Ghost.reveal w1);

  // 6. Compute ghost prefix/suffix values from w1 and w2
  let prefix_parsed : Ghost.erased (nlist (SZ.v kk) u) =
    Ghost.hide (fst (Some?.v (parse (parse_nlist (SZ.v kk) p) (Ghost.reveal w1))));
  let suffix_parsed : Ghost.erased (nlist (SZ.v count - SZ.v kk) u) =
    Ghost.hide (fst (Some?.v (parse (parse_nlist (SZ.v count - SZ.v kk) p) (Ghost.reveal w2))));

  // 7. Intro strong_prefix for prefix and suffix → halves permission
  pts_to_parsed_strong_prefix_intro (parse_nlist (SZ.v kk) p) prefix_sl prefix_parsed;
  pts_to_parsed_strong_prefix_intro (parse_nlist (SZ.v count - SZ.v kk) p) suffix_sl suffix_parsed;

  // 8. Fold as base_iterator_match for prefix and suffix
  // Permission: ((pm*sp)/2)/2 = (pm*sp)/4 = (pm/2)*(sp/2)
  fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) (list_prefix (SZ.v kk) l));
  fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) (list_suffix (SZ.v kk) l));

  // 9. Build trade: (prefix_match ** suffix_match) ~~> base_iterator_match at pm
  // Retained: copy 2 of base_iterator_match at pm/2, plus intro trades and split trade
  intro
    (Trade.trade
      (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) (list_prefix (SZ.v kk) l) **
       base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) (list_suffix (SZ.v kk) l))
      (base_iterator_match vmatch p pm (Serialized sp count payload) l)
    )
    #(base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l **
      Trade.trade
        (pts_to_parsed_strong_prefix (parse_nlist (SZ.v kk) p) prefix_sl #(((pm *. sp) /. 2.0R) /. 2.0R)
          prefix_parsed)
        (S.pts_to prefix_sl #((pm *. sp) /. 2.0R) w1) **
      Trade.trade
        (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - SZ.v kk) p) suffix_sl #(((pm *. sp) /. 2.0R) /. 2.0R)
          suffix_parsed)
        (S.pts_to suffix_sl #((pm *. sp) /. 2.0R) w2) **
      Trade.trade
        (S.pts_to prefix_sl #((pm *. sp) /. 2.0R) w1 ** S.pts_to suffix_sl #((pm *. sp) /. 2.0R) w2)
        (S.pts_to payload #((pm *. sp) /. 2.0R) w)
    )
    fn _ {
      // Unfold trigger sub-iterators → strong_prefix at (pm/2)*(sp/2)
      unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) (list_prefix (SZ.v kk) l));
      unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) (list_suffix (SZ.v kk) l));
      with l'_pre . assert (pts_to_parsed_strong_prefix (parse_nlist (SZ.v kk) p) prefix_sl #((pm /. 2.0R) *. (sp /. 2.0R)) l'_pre);
      rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v kk) p) prefix_sl #((pm /. 2.0R) *. (sp /. 2.0R)) l'_pre)
           as (pts_to_parsed_strong_prefix (parse_nlist (SZ.v kk) p) prefix_sl #(((pm *. sp) /. 2.0R) /. 2.0R) prefix_parsed);
      with l'_suf . assert (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - SZ.v kk) p) suffix_sl #((pm /. 2.0R) *. (sp /. 2.0R)) l'_suf);
      rewrite (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - SZ.v kk) p) suffix_sl #((pm /. 2.0R) *. (sp /. 2.0R)) l'_suf)
           as (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - SZ.v kk) p) suffix_sl #(((pm *. sp) /. 2.0R) /. 2.0R) suffix_parsed);

      // Elim intro trades to recover S.pts_to for prefix and suffix slices
      Trade.elim
        (pts_to_parsed_strong_prefix (parse_nlist (SZ.v kk) p) prefix_sl #(((pm *. sp) /. 2.0R) /. 2.0R)
          prefix_parsed)
        (S.pts_to prefix_sl #((pm *. sp) /. 2.0R) w1);
      Trade.elim
        (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count - SZ.v kk) p) suffix_sl #(((pm *. sp) /. 2.0R) /. 2.0R)
          suffix_parsed)
        (S.pts_to suffix_sl #((pm *. sp) /. 2.0R) w2);

      // Elim split trade to recover S.pts_to for payload (copy 1 at half perm)
      Trade.elim
        (S.pts_to prefix_sl #((pm *. sp) /. 2.0R) w1 ** S.pts_to suffix_sl #((pm *. sp) /. 2.0R) w2)
        (S.pts_to payload #((pm *. sp) /. 2.0R) w);

      // Unfold retained copy 2 to get S.pts_to + parse fact
      unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized sp count payload) l);
      with l2 . assert (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l2);
      unfold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #((pm /. 2.0R) *. sp) l2);

      // Gather the two halves
      S.gather payload;
      rewrite (S.pts_to payload #((pm *. sp) /. 2.0R +. (pm /. 2.0R) *. sp) w) as (S.pts_to payload #(pm *. sp) w);

      // Refold using l (the parameter), like base_iterator_truncate does
      fold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l);
      fold (base_iterator_match vmatch p pm (Serialized sp count payload) l);
    };

  (prefix_sl, suffix_sl)
}

#pop-options

// Helper lemma: splitAt at full length returns the whole list
let rec lemma_splitAt_full (#a: Type) (n: nat) (l: list a) : Lemma
  (requires n == List.Tot.length l)
  (ensures fst (List.Tot.splitAt n l) == l /\ snd (List.Tot.splitAt n l) == [])
  (decreases l)
= match l with
  | [] -> ()
  | _ :: tl -> lemma_splitAt_full (n - 1) tl

// Helper lemma: append prefix with v::suffix has length = length l + 1
let lemma_insert_length (#a: Type) (kk: nat) (l: list a) (v: a) : Lemma
  (requires kk <= List.Tot.length l)
  (ensures (
    lemma_list_prefix_length kk l;
    lemma_list_suffix_length kk l;
    List.Tot.length (List.Tot.append (list_prefix kk l) (v :: list_suffix kk l)) == List.Tot.length l + 1))
= lemma_list_prefix_length kk l;
  lemma_list_suffix_length kk l;
  List.Tot.append_length (list_prefix kk l) (v :: list_suffix kk l)

// Helper lemma: splitAt at n on (prefix ++ (v :: suffix)) where n == |l| + 1
// gives back the full list
let lemma_insert_splitAt (#a: Type) (kk: nat) (l: list a) (v: a) (n: nat) : Lemma
  (requires kk <= List.Tot.length l /\ n == List.Tot.length l + 1)
  (ensures (
    lemma_insert_length kk l v;
    let result = List.Tot.append (list_prefix kk l) (v :: list_suffix kk l) in
    fst (List.Tot.splitAt n result) == result))
= lemma_insert_length kk l v;
  let result = List.Tot.append (list_prefix kk l) (v :: list_suffix kk l) in
  lemma_splitAt_full n result

#push-options "--z3rlimit 800 --fuel 2 --ifuel 1"

fn iterator_insert_sorted_full
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
  (lt_ord: (u -> u -> bool))
  (lt_impl: lt_impl_t vmatch lt_ord)
  (pm: perm)
  (sp: perm)
  (count: SZ.t)
  (payload: S.slice byte)
  (pi: R.ref (iterator t))
  (#l: Ghost.erased (list u))
  (spare1: R.ref (iterator t))
  (#i_spare1: Ghost.erased (iterator t))
  (spare2: R.ref (iterator t))
  (#i_spare2: Ghost.erased (iterator t))
  (elem_ref: R.ref t)
  (#elem: Ghost.erased t)
  (pm_v: perm)
  (#v: Ghost.erased u)
requires
  R.pts_to pi (Base #t (Serialized sp count payload)) **
  iterator_match vmatch p pm (Base #t (Serialized sp count payload)) l **
  R.pts_to spare1 i_spare1 **
  R.pts_to spare2 i_spare2 **
  R.pts_to elem_ref elem **
  vmatch pm_v elem v **
  pure (List.Tot.sorted lt_ord (Ghost.reveal l) /\
        SZ.fits (List.Tot.length (Ghost.reveal l) + 1))
returns res: bool
ensures
  (if res then (
    let kk_v = Some?.v (sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l)) in
    let result_list = List.Tot.append (list_prefix kk_v (Ghost.reveal l))
      (Ghost.reveal v :: list_suffix kk_v (Ghost.reveal l)) in
    exists* (i': iterator t) (s1: iterator t) (s2: iterator t) .
      R.pts_to pi i' **
      iterator_match vmatch p (pm /. 2.0R) i' result_list **
      Trade.trade
        (iterator_match vmatch p (pm /. 2.0R) i' result_list)
        (iterator_match vmatch p pm (Base #t (Serialized sp count payload)) l **
         R.pts_to spare1 s1 **
         R.pts_to spare2 s2 **
         R.pts_to elem_ref elem **
         vmatch pm_v elem v) **
      pure (Some? (sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l)) /\
            List.Tot.sorted lt_ord result_list))
  else (
    R.pts_to pi (Base #t (Serialized sp count payload)) **
    iterator_match vmatch p pm (Base #t (Serialized sp count payload)) l **
    R.pts_to spare1 i_spare1 **
    R.pts_to spare2 i_spare2 **
    R.pts_to elem_ref elem **
    vmatch pm_v elem v **
    pure (sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l) == None)))
{
  // Step 1: count_insert_pos to find insertion position
  let kk_opt = count_insert_pos vmatch vmatch_share vmatch_gather p sq j rd
    lt_ord lt_impl pm pi elem_ref pm_v;
  match kk_opt {
    None -> {
      // Duplicate found
      false
    }
    Some kk -> {
      // Step 2: Unfold iterator to get base_iterator_match for Serialized
      unfold (iterator_match vmatch p pm (Base #t (Serialized sp count payload)) l);

      // Step 2b: Extract length fact from base_iterator_match
      // Serialized case has pts_to_parsed_strong_prefix which implies length l == count
      unfold (base_iterator_match vmatch p pm (Serialized sp count payload) l);
      with l' . assert (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l');
      unfold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l');
      with w . assert (S.pts_to payload #(pm *. sp) w);
      lemma_parse_nlist_length p (SZ.v count) w;
      assert (pure (List.Tot.length (Ghost.reveal l) == SZ.v count));
      fold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v count) p) payload #(pm *. sp) l');
      fold (base_iterator_match vmatch p pm (Serialized sp count payload) l);

      // Step 3: Split the Serialized at position kk
      let prefix_sl, suffix_sl = serialized_split_at vmatch p sq j pm sp count payload kk;

      // prefix_bi at pm/2, suffix_bi at pm/2, split_trade
      // NOTE: We do NOT let-bind base_iterators or iterators for use in fold/unfold.
      // Pulse cannot reduce match on let-bound variables.

      // Step 4: Fold suffix as Base iterator at pm/2
      fold (iterator_match vmatch p (pm /. 2.0R)
        (Base #t (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl))
        (list_suffix (SZ.v kk) l));

      // Step 5: Write suffix_iter to spare1 and share
      let suffix_iter : iterator t = Base #t (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl);
      R.forget_init spare1;
      spare1 := suffix_iter;
      R.share spare1;
      // Now have: R.pts_to spare1 #0.5R suffix_iter (x2)

      // Step 6: Build Singleton for the element
      // Share elem_ref and vmatch: keep 0.5R/pm_v/2 for trade body, use 0.5R/pm_v/2 for Singleton
      R.share elem_ref;
      vmatch_share (Ghost.reveal elem) #pm_v #(Ghost.reveal v);
      // R.pts_to elem_ref #0.5R (Ghost.reveal elem) (x2)
      // vmatch (pm_v /. 2.0R) (Ghost.reveal elem) (Ghost.reveal v) (x2)

      rewrite (R.pts_to elem_ref #(1.0R /. 2.0R) (Ghost.reveal elem))
           as (R.pts_to elem_ref #((pm /. 2.0R) *. (1.0R /. pm)) (Ghost.reveal elem));
      rewrite (vmatch (pm_v /. 2.0R) (Ghost.reveal elem) (Ghost.reveal v))
           as (vmatch ((pm /. 2.0R) *. (pm_v /. pm)) (Ghost.reveal elem) (Ghost.reveal v));
      fold (base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) [Ghost.reveal v]);

      // Step 7: Fold inner Append: Singleton + suffix
      // count - kk + 1 <= count + 1 == length l + 1, so SZ.fits holds
      let count_inner = SZ.add (SZ.sub count kk) 1sz;
      let depth_inner : Ghost.erased nat = Ghost.hide 1;

      // spare1: fold uses 0.5R, with ap_inner = 1.0R /. pm
      // (pm/2) * (1/pm) = 1/(2) = 0.5R
      rewrite (R.pts_to spare1 #(1.0R /. 2.0R) suffix_iter)
           as (R.pts_to spare1 #((pm /. 2.0R) *. (1.0R /. pm)) suffix_iter);

      // Rewrite iterator_match to use suffix_iter
      rewrite (iterator_match vmatch p (pm /. 2.0R)
        (Base #t (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl))
        (list_suffix (SZ.v kk) l))
           as (iterator_match vmatch p (pm /. 2.0R) suffix_iter (list_suffix (SZ.v kk) l));

      lemma_splitAt_length (Ghost.reveal v :: list_suffix (SZ.v kk) (Ghost.reveal l));
      lemma_list_suffix_length (SZ.v kk) (Ghost.reveal l);

      fold (iterator_match vmatch p (pm /. 2.0R)
        (Append #t depth_inner count_inner (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare1)
        (Ghost.reveal v :: list_suffix (SZ.v kk) (Ghost.reveal l)));

      let inner_iter : iterator t = Append depth_inner count_inner (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare1;

      // Step 8: Write inner_iter to spare2 and share
      R.forget_init spare2;
      spare2 := inner_iter;
      R.share spare2;
      // Now have: R.pts_to spare2 #0.5R inner_iter (x2)

      // spare2: fold uses 0.5R, with ap_outer = 1.0R /. pm
      rewrite (R.pts_to spare2 #(1.0R /. 2.0R) inner_iter)
           as (R.pts_to spare2 #((pm /. 2.0R) *. (1.0R /. pm)) inner_iter);

      // Rewrite iterator_match to use inner_iter
      rewrite (iterator_match vmatch p (pm /. 2.0R)
        (Append #t depth_inner count_inner (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare1)
        (Ghost.reveal v :: list_suffix (SZ.v kk) (Ghost.reveal l)))
           as (iterator_match vmatch p (pm /. 2.0R) inner_iter (Ghost.reveal v :: list_suffix (SZ.v kk) (Ghost.reveal l)));

      // Step 9: Fold outer Append: prefix + inner
      // count + 1 == length l + 1, so SZ.fits holds from precondition
      let count_total = SZ.add count 1sz;
      let depth_outer : Ghost.erased nat = Ghost.hide 2;

      lemma_sorted_insert_pos_bound lt_ord (Ghost.reveal v) (Ghost.reveal l);
      lemma_insert_splitAt (SZ.v kk) (Ghost.reveal l) (Ghost.reveal v) (SZ.v count + 1);
      lemma_list_prefix_length (SZ.v kk) (Ghost.reveal l);
      lemma_list_suffix_length (SZ.v kk) (Ghost.reveal l);

      let result_list : Ghost.erased (list u) = Ghost.hide (
        List.Tot.append (list_prefix (SZ.v kk) (Ghost.reveal l))
          (Ghost.reveal v :: list_suffix (SZ.v kk) (Ghost.reveal l)));

      fold (iterator_match vmatch p (pm /. 2.0R)
        (Append #t depth_outer count_total (Serialized (sp /. 2.0R) kk prefix_sl) (1.0R /. pm) spare2)
        (Ghost.reveal result_list));

      let outer_iter : iterator t = Append depth_outer count_total (Serialized (sp /. 2.0R) kk prefix_sl) (1.0R /. pm) spare2;

      // Rewrite to use outer_iter let-binding
      rewrite (iterator_match vmatch p (pm /. 2.0R)
        (Append #t depth_outer count_total (Serialized (sp /. 2.0R) kk prefix_sl) (1.0R /. pm) spare2)
        (Ghost.reveal result_list))
           as (iterator_match vmatch p (pm /. 2.0R) outer_iter (Ghost.reveal result_list));

      // Step 10: Write outer_iter to pi
      R.forget_init pi;
      pi := outer_iter;

      // Step 11: Build the grand trade
      // Retained: spare1@0.5R, spare2@0.5R, elem_ref@0.5R, vmatch@pm_v/2, split_trade
      intro
        (Trade.trade
          (iterator_match vmatch p (pm /. 2.0R) outer_iter (Ghost.reveal result_list))
          (iterator_match vmatch p pm (Base #t (Serialized sp count payload)) l **
           R.pts_to spare1 suffix_iter **
           R.pts_to spare2 inner_iter **
           R.pts_to elem_ref elem **
           vmatch pm_v elem v))
        #(R.pts_to spare1 #(1.0R /. 2.0R) suffix_iter **
          R.pts_to spare2 #(1.0R /. 2.0R) inner_iter **
          R.pts_to elem_ref #(1.0R /. 2.0R) (Ghost.reveal elem) **
          vmatch (pm_v /. 2.0R) (Ghost.reveal elem) (Ghost.reveal v) **
          Trade.trade
            (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) (list_prefix (SZ.v kk) l) **
             base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) (list_suffix (SZ.v kk) l))
            (base_iterator_match vmatch p pm (Serialized sp count payload) l))
        fn _ {
          // Rewrite outer_iter back to constructor for unfold
          rewrite (iterator_match vmatch p (pm /. 2.0R) outer_iter (Ghost.reveal result_list))
               as (iterator_match vmatch p (pm /. 2.0R)
                 (Append #t depth_outer count_total (Serialized (sp /. 2.0R) kk prefix_sl) (1.0R /. pm) spare2)
                 (Ghost.reveal result_list));
          // Unfold outer Append
          unfold (iterator_match vmatch p (pm /. 2.0R)
            (Append #t depth_outer count_total (Serialized (sp /. 2.0R) kk prefix_sl) (1.0R /. pm) spare2)
            (Ghost.reveal result_list));
          with _i1 _i2 _l2 . assert (
            base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) _i1 **
            R.pts_to spare2 #((pm /. 2.0R) *. (1.0R /. pm)) _i2 **
            iterator_match vmatch p (pm /. 2.0R) _i2 _l2
          );

          // Gather spare2: retained 0.5R + unfold 0.5R → 1.0R, proves _i2 == inner_iter
          rewrite (R.pts_to spare2 #((pm /. 2.0R) *. (1.0R /. pm)) _i2)
               as (R.pts_to spare2 #(1.0R /. 2.0R) _i2);
          R.gather spare2;
          // R.pts_to spare2 #1.0R _i2, with _i2 == inner_iter (from gather postcondition)
          rewrite (R.pts_to spare2 _i2)
               as (R.pts_to spare2 inner_iter);

          // Rewrite inner: _i2 → inner_iter
          rewrite (iterator_match vmatch p (pm /. 2.0R) _i2 _l2)
               as (iterator_match vmatch p (pm /. 2.0R) inner_iter _l2);

          // Unfold inner Append
          rewrite (iterator_match vmatch p (pm /. 2.0R) inner_iter _l2)
               as (iterator_match vmatch p (pm /. 2.0R)
                 (Append #t depth_inner count_inner (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare1)
                 _l2);
          unfold (iterator_match vmatch p (pm /. 2.0R)
            (Append #t depth_inner count_inner (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) (1.0R /. pm) spare1)
            _l2);
          with _j1 _j2 _m2 . assert (
            base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) _j1 **
            R.pts_to spare1 #((pm /. 2.0R) *. (1.0R /. pm)) _j2 **
            iterator_match vmatch p (pm /. 2.0R) _j2 _m2
          );

          // Gather spare1: retained 0.5R + unfold 0.5R → 1.0R, proves _j2 == suffix_iter
          rewrite (R.pts_to spare1 #((pm /. 2.0R) *. (1.0R /. pm)) _j2)
               as (R.pts_to spare1 #(1.0R /. 2.0R) _j2);
          R.gather spare1;
          rewrite (R.pts_to spare1 _j2)
               as (R.pts_to spare1 suffix_iter);

          // Unfold Singleton EARLY to get _j1 == [_y] (length 1)
          unfold (base_iterator_match vmatch p (pm /. 2.0R) (Singleton (1.0R /. pm) (pm_v /. pm) elem_ref) _j1);
          with _x _y . assert (
            R.pts_to elem_ref #((pm /. 2.0R) *. (1.0R /. pm)) _x **
            vmatch ((pm /. 2.0R) *. (pm_v /. pm)) _x _y
          );
          // pure (_j1 == [_y]) consumed as hypothesis; SMT knows length _j1 == 1

          // Rewrite suffix: _j2 → suffix_iter
          rewrite (iterator_match vmatch p (pm /. 2.0R) _j2 _m2)
               as (iterator_match vmatch p (pm /. 2.0R) suffix_iter _m2);

          // Unfold suffix iterator (Base)
          rewrite (iterator_match vmatch p (pm /. 2.0R) suffix_iter _m2)
               as (iterator_match vmatch p (pm /. 2.0R)
                 (Base #t (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl))
                 _m2);
          unfold (iterator_match vmatch p (pm /. 2.0R)
            (Base #t (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl))
            _m2);

          // Extract length fact from suffix Serialized: unfold, get refinement, fold back
          unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) _m2);
          with l_suf . assert (
            pts_to_parsed_strong_prefix (parse_nlist (SZ.v (SZ.sub count kk)) p) suffix_sl #((pm /. 2.0R) *. (sp /. 2.0R)) l_suf
          );
          // l_suf == _m2, length l_suf == SZ.v (SZ.sub count kk)
          fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) _m2);

          // Extract length fact from prefix Serialized similarly
          unfold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) _i1);
          with l_pre . assert (
            pts_to_parsed_strong_prefix (parse_nlist (SZ.v kk) p) prefix_sl #((pm /. 2.0R) *. (sp /. 2.0R)) l_pre
          );
          // l_pre == _i1, length l_pre == SZ.v kk
          fold (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) _i1);

          // Establish key equalities via explicit lemma calls
          // Inner: _l2 == _j1 ++ _m2 (via splitAt at full length)
          List.Tot.append_length _j1 _m2;
          lemma_splitAt_full (SZ.v count_inner) (List.Tot.append _j1 _m2);

          // Outer: result_list == _i1 ++ _l2 (via splitAt at full length)
          List.Tot.append_length _i1 _l2;
          lemma_splitAt_full (SZ.v count_total) (List.Tot.append _i1 _l2);

          // Decompose via append injectivity:
          // _i1 ++ _l2 == list_prefix kk l ++ (v :: list_suffix kk l)
          // length _i1 == length (list_prefix kk l) == kk
          // => _i1 == list_prefix kk l, _l2 == v :: list_suffix kk l
          // => _m2 == list_suffix kk l (from _l2 == _j1 ++ _m2 == _y :: _m2)
          lemma_list_prefix_length (SZ.v kk) (Ghost.reveal l);
          FStar.List.Tot.Properties.append_length_inv_head _i1 _l2
            (list_prefix (SZ.v kk) (Ghost.reveal l))
            (Ghost.reveal v :: list_suffix (SZ.v kk) (Ghost.reveal l));

          // Rewrite existentials to known values
          rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) _m2)
               as (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) (list_suffix (SZ.v kk) l));

          rewrite (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) _i1)
               as (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) (list_prefix (SZ.v kk) l));

          // Elim split trade: prefix + suffix → original
          Trade.elim
            (base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) kk prefix_sl) (list_prefix (SZ.v kk) l) **
             base_iterator_match vmatch p (pm /. 2.0R) (Serialized (sp /. 2.0R) (SZ.sub count kk) suffix_sl) (list_suffix (SZ.v kk) l))
            (base_iterator_match vmatch p pm (Serialized sp count payload) l);

          // Fold back as iterator
          fold (iterator_match vmatch p pm (Base #t (Serialized sp count payload)) l);

          // Recover elem_ref via gather: retained 0.5R + Singleton's 0.5R → 1.0R
          rewrite (R.pts_to elem_ref #((pm /. 2.0R) *. (1.0R /. pm)) _x)
               as (R.pts_to elem_ref #(1.0R /. 2.0R) _x);
          R.gather elem_ref;
          // R.pts_to elem_ref #1.0R _x, with _x == Ghost.reveal elem (from gather)
          rewrite (R.pts_to elem_ref _x) as (R.pts_to elem_ref elem);

          // Recover vmatch via gather: retained pm_v/2 + Singleton's pm_v/2 → pm_v
          rewrite (vmatch ((pm /. 2.0R) *. (pm_v /. pm)) _x _y)
               as (vmatch (pm_v /. 2.0R) _x _y);
          rewrite (vmatch (pm_v /. 2.0R) _x _y)
               as (vmatch (pm_v /. 2.0R) (Ghost.reveal elem) _y);
          vmatch_gather (Ghost.reveal elem) #(pm_v /. 2.0R) #_y #(pm_v /. 2.0R) #(Ghost.reveal v);
          rewrite (vmatch (pm_v /. 2.0R +. pm_v /. 2.0R) (Ghost.reveal elem) _y)
               as (vmatch pm_v elem v);
        };

      // Step 12: Prove sortedness
      lemma_sorted_insert_sorted lt_ord (Ghost.reveal v) (Ghost.reveal l);

      // Step 13: Rewrite result_list to match ensures expression (Pulse needs exact match)
      rewrite (iterator_match vmatch p (pm /. 2.0R) outer_iter (Ghost.reveal result_list))
           as (iterator_match vmatch p (pm /. 2.0R) outer_iter
             (List.Tot.append
               (list_prefix (Some?.v (sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l))) (Ghost.reveal l))
               (Ghost.reveal v :: list_suffix (Some?.v (sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l))) (Ghost.reveal l))));
      rewrite (Trade.trade
          (iterator_match vmatch p (pm /. 2.0R) outer_iter (Ghost.reveal result_list))
          (iterator_match vmatch p pm (Base #t (Serialized sp count payload)) l **
           R.pts_to spare1 suffix_iter **
           R.pts_to spare2 inner_iter **
           R.pts_to elem_ref elem **
           vmatch pm_v elem v))
           as (Trade.trade
          (iterator_match vmatch p (pm /. 2.0R) outer_iter
             (List.Tot.append
               (list_prefix (Some?.v (sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l))) (Ghost.reveal l))
               (Ghost.reveal v :: list_suffix (Some?.v (sorted_insert_pos lt_ord (Ghost.reveal v) (Ghost.reveal l))) (Ghost.reveal l))))
          (iterator_match vmatch p pm (Base #t (Serialized sp count payload)) l **
           R.pts_to spare1 suffix_iter **
           R.pts_to spare2 inner_iter **
           R.pts_to elem_ref elem **
           vmatch pm_v elem v));

      true
    }
  }
}

#pop-options

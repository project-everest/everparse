module LowParse.PulseParse.Projectors
include LowParse.PulseParse.Combinators
#lang-pulse
open Pulse.Lib.Pervasives

inline_for_extraction noextract
noeq
type pair_proj (t0 t1: Type) = {
  pair_proj_get: t0 -> t1;
  pair_proj_set: t0 -> t1 -> t0;
  pair_proj_get_set: (x0: t0) -> (x1: t1) -> Lemma
    (pair_proj_get (pair_proj_set x0 x1) == x1);
  pair_proj_set_set: (x0: t0) -> (x1: t1) -> (x1': t1) -> Lemma
    (pair_proj_set (pair_proj_set x0 x1) x1' == pair_proj_set x0 x1');
  pair_proj_set_get: (x0: t0) -> Lemma
    (pair_proj_set x0 (pair_proj_get x0) == x0);
}

let pair_proj_vmatch_indep
  (#t0 #t1 #t': Type)
  (p: pair_proj t0 t1)
  (r: t0 -> t' -> slprop)
: Tot Type
= (x0: t0) ->
  (x': t') ->
  (x1: t1) ->
  stt_ghost unit emp_inames
    (r x0 x')
    (fun _ -> r (p.pair_proj_set x0 x1) x')

ghost fn pair_proj_vmatch_indep_recip
  (#t0 #t1 #t': Type0)
  (#p: pair_proj t0 t1)
  (#r: t0 -> t' -> slprop)
  (indep: pair_proj_vmatch_indep p r)
  (x0: t0)
  (x': t')
  (x1: t1)
requires
  r (p.pair_proj_set x0 x1) x'
ensures
  r x0 x'
{
  indep (p.pair_proj_set x0 x1) x' (p.pair_proj_get x0);
  p.pair_proj_set_set x0 x1 (p.pair_proj_get x0);
  p.pair_proj_set_get x0;
  with x0' . rewrite (r x0' x') as (r x0 x');
}

let vmatch_with_pair_proj
  (#t0 #t1 #t': Type)
  (r1: t1 -> t' -> slprop)
  (p: pair_proj t0 t1)
  (x0: t0)
  (x': t')
: Tot slprop
= r1 (p.pair_proj_get x0) x'

let vmatch_pair_with_proj
  (#t0 #t1 #t1' #t2': Type)
  (r1: t1 -> t1' -> slprop)
  (p: pair_proj t0 t1)
  (r2: t0 -> t2' -> slprop)
  (x0: t0)
  (x': (t1' & t2'))
: Tot slprop
= r1 (p.pair_proj_get x0) (fst x') ** r2 x0 (snd x')

let vmatch_dep_pair_with_proj
  (#t0 #t1 #t1': Type)
  (#t2': (t1' -> Type))
  (r1: t1 -> t1' -> slprop)
  (p: pair_proj t0 t1)
  (r2: ((x1': t1') -> t0 -> t2' x1' -> slprop))
  (x0: t0)
  (x': dtuple2 t1' t2')
: Tot slprop
= r1 (p.pair_proj_get x0) (dfst x') ** r2 (dfst x') x0 (dsnd x')

let vmatch_with_dep_cond_left_or_true
  (#t #t': Type)
  (cond: t -> bool)
  (r: (x: t { cond x }) -> t' -> slprop)
  (x: t)
  (x': t')
: Tot slprop
= if cond x
  then r x x'
  else emp

let vmatch_and
  (#t #t': Type)
  (r1 r2: t -> t' -> slprop)
  (x: t)
  (x': t')
: Tot slprop
= r1 x x' ** r2 x x'

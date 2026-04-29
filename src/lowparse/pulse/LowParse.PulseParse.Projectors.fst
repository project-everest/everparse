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

(* ========== zero_copy_parse_strong_prefix with projector ========== *)

module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base

let vmatch_dep_pair_with_proj_content
  (#t0 #t1 #t1': Type0)
  (#t2': (t1' -> Type0))
  (r1: t1 -> t1' -> slprop)
  (proj: pair_proj t0 t1)
  (r2: ((x1': t1') -> t0 -> t2' x1' -> slprop))
  (xh: t1')
  (x0: t0)
  (xh2: t2' xh)
: Tot slprop
= r1 (proj.pair_proj_get x0) xh ** r2 xh x0 xh2

#push-options "--z3rlimit 64"

inline_for_extraction
fn read_and_zero_copy_parse_strong_prefix_dtuple2_with_proj
  (#t0 #t1 #t1': Type0)
  (#t2': (t1' -> Type0))
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t1')
  (#k2: Ghost.erased parser_kind)
  (#p2: (x: t1') -> parser k2 (t2' x))
  (r1: t1 -> t1' -> slprop)
  (proj: pair_proj t0 t1)
  (r2: ((x1': t1') -> t0 -> t2' x1' -> slprop))
  (j1: LPS.jumper p1)
  (rd1: PPB.leaf_reader p1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (w2: (xh: t1') -> PPB.zero_copy_parse_strong_prefix #t0 #(t2' xh)
    (vmatch_dep_pair_with_proj_content r1 proj r2 xh)
    #k2 (p2 xh))
: PPB.zero_copy_parse_strong_prefix #t0 #(dtuple2 t1' t2')
    (vmatch_dep_pair_with_proj r1 proj r2)
    #(and_then_kind k1 k2)
    (parse_dtuple2 p1 p2)
= (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dtuple2 t1' t2'))
{
  PPB.pts_to_parsed_strong_prefix_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_dtuple2_eq p1 p2 w;
  parser_kind_prop_equiv k1 p1;
  let off1 = j1 input 0sz;
  let input1, input2 = Pulse.Lib.Slice.Util.split_trade input off1;
  with wb1 . assert (S.pts_to input1 #pm wb1);
  with wb2 . assert (S.pts_to input2 #pm wb2);
  Trade.trans (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (S.pts_to input #pm w) (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v);
  parse_strong_prefix p1 w wb1;
  PPB.pts_to_parsed_intro p1 input1 (dfst v);
  PPB.pts_to_parsed_strong_prefix_intro (p2 (dfst v)) input2 (dsnd v);
  Trade.prod (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) (dfst v)) (S.pts_to input1 #pm wb1) (PPB.pts_to_parsed_strong_prefix (p2 (dfst v)) input2 #(pm /. 2.0R) (dsnd v)) (S.pts_to input2 #pm wb2);
  Trade.trans (PPB.pts_to_parsed p1 input1 #(pm /. 2.0R) (dfst v) ** PPB.pts_to_parsed_strong_prefix (p2 (dfst v)) input2 #(pm /. 2.0R) (dsnd v)) (S.pts_to input1 #pm wb1 ** S.pts_to input2 #pm wb2) (PPB.pts_to_parsed_strong_prefix (parse_dtuple2 p1 p2) input #pm v);
  let v1 = rd1 input1;
  Trade.elim_hyp_l _ _ _;
  rewrite each (dfst v) as v1;
  let res = w2 v1 input2;
  Trade.trans (vmatch_dep_pair_with_proj_content r1 proj r2 v1 res _) _ _;
  Trade.rewrite_with_trade
    (vmatch_dep_pair_with_proj_content r1 proj r2 v1 res _)
    (vmatch_dep_pair_with_proj r1 proj r2 res v);
  Trade.trans (vmatch_dep_pair_with_proj r1 proj r2 res v) _ _;
  res
}

#pop-options

let vmatch_with_perm_guard
  (#guard_t: Type)
  (guard: guard_t)
  (#t #t': Type)
  (vmatch: (perm -> t -> (x': t' { x' << guard }) -> slprop))
  (pm: perm)
  (x: t)
  (x': t')
: Tot slprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (x' << guard)
  then vmatch pm x x'
  else pure False

let rec vmatch_with_perm_rec
  (#t #t': Type)
  (vmatch_body: (perm -> t -> t' -> slprop) -> (perm -> t -> t' -> slprop))
  (pm: perm)
  (x: t)
  (x': t')
: Tot slprop
  (decreases x')
= vmatch_body
    (vmatch_with_perm_guard x' (vmatch_with_perm_rec vmatch_body))
    pm x x'

ghost fn vmatch_with_perm_guard_unfold
  (#guard_t: Type0)
  (guard: guard_t)
  (#t #t': Type0)
  (vmatch: (perm -> t -> (x': t' { x' << guard }) -> slprop))
  (pm: perm)
  (x: t)
  (x': t')
requires vmatch_with_perm_guard guard vmatch pm x x'
returns res: squash (x' << guard)
ensures vmatch pm x x'
{
  let test = FStar.StrongExcludedMiddle.strong_excluded_middle (x' << guard);
  if (test) {
     let res: squash (x' << guard) = ();
     rewrite (vmatch_with_perm_guard guard vmatch pm x x') as (vmatch pm x x');
     res
  } else {
     rewrite (vmatch_with_perm_guard guard vmatch pm x x') as pure False;
     let res: squash (x' << guard) = false_elim ();
     rewrite pure False as vmatch pm x x';
     res
  }
}

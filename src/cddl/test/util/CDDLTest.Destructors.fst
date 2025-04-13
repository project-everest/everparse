module CDDLTest.Destructors
#lang-pulse
open Pulse.Lib
open Pulse.Lib.Pervasives
open CDDL.Pulse.Parse.Base
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
open CDDL.Pulse.Types
module T = CDDL.Pulse.AST.Tactics
open CDDL.Pulse.AST.Bundle
open CBOR.Spec.API.Type
open CDDL.Spec.Base
open Pulse.Lib.Trade

[@@pulse_unfold]
unfold
let my_unfold (#a:Type) (s:string) (p:a) = norm [delta_only [s]; hnf; iota; primops] p

ghost
fn unfold_with_trade (s:string) (p:slprop)
requires p
ensures my_unfold s p ** Trade.trade (my_unfold s p) p
{
  norm_spec [delta_only [s]; hnf; iota; primops] p;
  Trade.Util.rewrite_with_trade p (my_unfold s p);
}

ghost
fn fold_with_trade (s:string) (p k:slprop)
requires my_unfold s p ** Trade.trade (my_unfold s p) k
ensures p ** Trade.trade p k
{
  norm_spec [delta_only [s]; hnf; iota; primops] p;
  rewrite each (my_unfold s p) as p;
}

ghost
fn fold_last_relation
   (#a0 #b0 #a1 #b1:Type0)
   (#r:rel a0 b0)
   (s:string)
   (p:rel a1 b1)
   (#x:_)
   (#y:_)
   (#res:slprop)
requires 
  rel_pair r (my_unfold s p) x y **
  Trade.trade (rel_pair r (my_unfold s p) x y) res
ensures rel_pair r p x y ** Trade.trade (rel_pair r p x y) res
{
  norm_spec [delta_only [s]; hnf; iota; primops] p;
  rewrite each (my_unfold s p) as p;
}

ghost
fn elim_validate_and_parse_post_some
  (#t: typ)
  (#tgt: Type0)
  (#tgt_serializable: (tgt -> bool))
  (#ps: parser_spec t tgt tgt_serializable)
  (#impl_tgt': Type0)
  (#tgt': Type0)
  (#r: rel impl_tgt' tgt')
  (#s: S.slice U8.t)
  (#p: perm)
  (#w: Seq.seq U8.t)
  (x: impl_tgt')
  (rem: S.slice U8.t)
requires
  validate_and_parse_post ps r s p w (Some (x, rem))
ensures
  exists* wx wr. 
    r x wx **
    pts_to rem #p wr **
    Trade.trade
      (r x wx ** pts_to rem #p wr)
      (pts_to s #p w) **
    pure (validate_and_parse_postcond_some ps w wx wr)
{
  unfold validate_and_parse_post;
}

ghost
fn destruct_pair (#l0 #l1 #h0 #h1:Type0) (r0:rel l0 h0) (r1:rel l1 h1) (xl: (l0 & l1)) (xh: (h0 & h1)) ()
requires 
  rel_pair r0 r1 xl xh
ensures 
  r0 (fst xl) (fst xh) **
  r1 (snd xl) (snd xh) **
  Trade.trade (r0 (fst xl) (fst xh) ** r1 (snd xl) (snd xh))
              (rel_pair r0 r1 xl xh)
{
  rel_pair_eq r0 r1 (fst xl) (snd xl) (fst xh) (snd xh);
  Trade.rewrite_with_trade
    (rel_pair r0 r1 xl xh)
    (r0 (fst xl) (fst xh) ** r1 (snd xl) (snd xh));
}

fn destruct_rel_option (#a #b:Type0) (r:rel a b) (x:option a) (y:erased (option b))
requires 
  rel_option r x y ** pure (Some? x)
returns
  xx:a
ensures
  exists* (yy:b).
    pure (y == Some yy /\ x == Some xx) **
    r xx yy **
    Trade.trade (r xx yy) (rel_option r x y)
{
  rel_option_cases r _ _;
  let xx = Some?.v x;
  let yy = hide <| Some?.v y;
  rewrite each x as (Some xx);
  rel_option_eq_some r xx yy;
  Trade.rewrite_with_trade 
    (rel_option r (Some xx) y)
    (r xx yy);
  rewrite each (Some xx) as x;
  xx
}

ghost
fn destruct_rel_fun 
  (#a #b #a' #b':Type0) (r:rel a b) (x:a') (y:b')
  (f:a' -> a) (g:b' -> b)
requires rel_fun r f g x y
ensures r (f x) (g y) ** Trade.trade (r (f x) (g y)) (rel_fun r f g x y)
{
  Trade.rewrite_with_trade
    (rel_fun r f g x y)
    (r (f x) (g y));
}

ghost
fn destruct_fst (#l0 #l1 #h0 #h1:Type0) (r0:rel l0 h0) (r1:rel l1 h1) (xl: (l0 & l1)) (xh: (h0 & h1)) (res:slprop)
requires 
  rel_pair r0 r1 xl xh **
  Trade.trade (rel_pair r0 r1 xl xh) res
ensures 
  r0 (fst xl) (fst xh) **
  Trade.trade (r0 (fst xl) (fst xh)) res
{
  destruct_pair _ _ xl xh ();
  Trade.Util.elim_hyp_r _ _ (rel_pair r0 r1 xl xh);
  Trade.trade_compose _ _ res;
}

ghost
fn destruct_snd (#l0 #l1 #h0 #h1:Type0) (r0:rel l0 h0) (r1:rel l1 h1) (xl: (l0 & l1)) (xh: (h0 & h1)) (res:slprop)
requires 
  rel_pair r0 r1 xl xh **
  Trade.trade (rel_pair r0 r1 xl xh) res
ensures 
  r1 (snd xl) (snd xh) **
  Trade.trade (r1 (snd xl) (snd xh)) res
{
  destruct_pair _ _ xl xh ();
  Trade.Util.elim_hyp_l _ _ (rel_pair r0 r1 xl xh);
  Trade.trade_compose _ _ res;
}

let either_slprop #a #b (x:either a b) (p: a -> slprop) (q: b -> slprop)
: slprop
= match x with
  | Inl x -> p x
  | Inr x -> q x

fn destruct_pair_concrete_nest (#l0 #l1 #h0 #h1:Type0)
  (r0:rel l0 h0) 
  (r1:rel l1 h1)
  (xl: (l0 & l1))
  (xh: erased (h0 & h1)) (res:slprop) (rest:slprop) 
requires 
  rel_pair r0 r1 xl xh **
  Trade.trade (rel_pair r0 r1 xl xh ** rest) res
returns v:(l0 & l1)
ensures 
  r0 (fst v) (fst xh) **
  r1 (snd v) (snd xh) **
  Trade.trade (r0 (fst v) (fst xh) ** (r1 (snd v) (snd xh) ** rest)) res **
  pure (v == xl)
{
  destruct_pair _ _ xl xh ();
  Trade.Util.trans_hyp_l _ _ _ res;
  let v = (fst xl, snd xl);
  rewrite each xl as v;
  Trade.Util.assoc_hyp_r _ _ _ res;
  v
}

fn destruct_pair_concrete (#l0 #l1 #h0 #h1:Type0) (r0:rel l0 h0) (r1:rel l1 h1) (xl: (l0 & l1)) (xh: erased (h0 & h1)) (res:slprop)
requires 
  rel_pair r0 r1 xl xh **
  Trade.trade (rel_pair r0 r1 xl xh) res
returns v:(l0 & l1)
ensures 
  r0 (fst v) (fst xh) **
  r1 (snd v) (snd xh) **
  Trade.trade (r0 (fst v) (fst xh) ** r1 (snd v) (snd xh)) res **
  pure (v == xl)
{
  slprop_equivs();
  rewrite each (rel_pair r0 r1 xl xh) as (rel_pair r0 r1 xl xh ** emp);
  let v = destruct_pair_concrete_nest r0 r1 xl xh res emp;
  v
}

fn trade_emp_hyp_r (p q:_)
requires
  trade p q
ensures
  trade (p ** emp) q
{
  slprop_equivs();
  rewrite each p as (p ** emp);
}

fn trade_emp_hyp_r_elim (p q r:_)
requires
  trade (p ** (emp ** q)) r
ensures
  trade (p ** q) r
{
  slprop_equivs();
  rewrite each (emp ** q) as q;
}

ghost
fn rewrite_with_trade_trans
  (p1 p2 res: slprop)
  requires p1 ** trade p1 res ** pure (p1 == p2)
  ensures p2 ** trade p2 res
{
  rewrite each p1 as p2;
}

ghost
fn destruct_rel_either_left 
    (#a #b #a' #b':Type0) 
    (r:rel a b)
    (r':rel a' b')
    (x:either a a')
    (y:erased (either b b'))
    (res:slprop)
requires 
  rel_either r r' x y **
  pure (Inl? x) **
  Trade.trade (rel_either r r' x y) res
returns
  xx:a
ensures
  exists* (yy:b).
    pure (y == Inl yy /\ x == Inl xx) **
    r xx yy **
    Trade.trade (r xx yy) res
{
  rel_either_cases _ _ _ _;
  let xx = Inl?.v x;
  let yy = hide <| Inl?.v y;
  rewrite each x as (Inl xx);
  rel_either_eq_left r r' xx yy;
  Trade.rewrite_with_trade 
    (rel_either r r' (Inl xx) y)
    (r xx yy);
  rewrite each (Inl #a #a' xx) as x;
  Trade.trade_compose _ _ res;
  xx
}

fn destruct_rel_either_right
    (#a #b #a' #b':Type0) 
    (r:rel a b)
    (r':rel a' b')
    (x:either a a')
    (y:erased (either b b'))
    (res:slprop)
requires 
  rel_either r r' x y **
  pure (Inr? x) **
  Trade.trade (rel_either r r' x y) res
returns
  xx:a'
ensures
  exists* (yy:b').
    pure (y == Inr yy /\ x == Inr xx) **
    r' xx yy **
    Trade.trade (r' xx yy) res
{
  rel_either_cases _ _ _ _;
  let xx = Inr?.v x;
  let yy = hide <| Inr?.v y;
  rewrite each x as (Inr xx);
  rel_either_eq_right r r' xx yy;
  Trade.rewrite_with_trade 
    (rel_either r r' (Inr xx) y)
    (r' xx yy);
  rewrite each (Inr #a #a' xx) as x;
  Trade.trade_compose _ _ res;
  xx
}

fn fst_pair_concrete (#l0 #l1 #h0 #h1:Type0)
  (r0:rel l0 h0) 
  (r1:rel l1 h1)
  (xl: (l0 & l1))
  (xh: erased (h0 & h1)) (res:slprop)
requires 
  rel_pair r0 r1 xl xh **
  Trade.trade (rel_pair r0 r1 xl xh) res
returns v:l0
ensures 
  r0 v (fst xh) ** 
  Trade.trade (r0 v (fst xh)) res **
  pure (v == fst xl)
{
  let f, s = destruct_pair_concrete _ _ _ _ _;
  Trade.Util.elim_hyp_r _ _ res;
  fst (f, s)
}

fn snd_pair_concrete (#l0 #l1 #h0 #h1:Type0)
  (r0:rel l0 h0) 
  (r1:rel l1 h1)
  (xl: (l0 & l1))
  (xh: erased (h0 & h1)) (res:slprop)
requires 
  rel_pair r0 r1 xl xh **
  Trade.trade (rel_pair r0 r1 xl xh) res
returns v:l1
ensures 
  r1 v (snd xh) ** 
  Trade.trade (r1 v (snd xh)) res **
  pure (v == snd xl)
{
  let f, s = destruct_pair_concrete _ _ _ _ _;
  Trade.Util.elim_hyp_l _ _ res;
  snd (f, s)
}
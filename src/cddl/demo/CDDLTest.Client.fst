module CDDLTest.Client
#lang-pulse
open CDDLTest.Test
open Pulse.Lib.Pervasives

module I32 = FStar.Int32
module A = Pulse.Lib.Array
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice

open CDDL.Pulse.Types

ghost fn rel_pure_intro
  (#t: Type0)
  (x: t)
requires emp
ensures rel_pure t x x
{
  rel_pure_eq x x;
  fold (rel_pure _ x x)
}

ghost fn rel_option_some_intro
  (#t1 #t2: Type0)
  (r: rel t1 t2)
  (x: t1)
  (y: t2)
requires r x y
ensures rel_option r (Some x) (Some y)
{
  rel_option_eq_some r x y;
  rewrite (r x y) as (rel_option r (Some x) (Some y))
}

ghost fn rel_pair_intro
  (#tl1 #th1 #tl2 #th2: Type0)
  (r1: rel tl1 th1)
  (x1: tl1)
  (y1: th1)
  (r2: rel tl2 th2)
  (x2: tl2)
  (y2: th2)
requires r1 x1 y1 ** r2 x2 y2
ensures rel_pair r1 r2 (x1, x2) (y1, y2)
{
  rel_pair_eq r1 r2 x1 x2 y1 y2;
  rewrite (r1 x1 y1 ** r2 x2 y2) as (rel_pair r1 r2 (x1, x2) (y1, y2))
}

fn main
  (_: unit)
requires emp
returns res: I32.t
ensures emp
{
  let w: evercddl_test1 = (18uL, Some 42uL);
  let mut out_a = [| 0uy; 32sz |];
  let out = S.from_array out_a 32sz;
  rel_pure_intro 18uL;
  rel_pure_intro 42uL;
  rel_option_some_intro (rel_pure U64.t) 42uL 42uL;
  rel_pair_intro (rel_pure U64.t) 18uL 18uL (rel_option (rel_pure U64.t)) (Some 42uL) (Some 42uL);
  let wi : bundle_test1.b_impl_type = w;
  let ws : Ghost.erased bundle_test1.b_spec_type = Ghost.hide w;
  rewrite
    (rel_pair (rel_pure U64.t) (rel_option (rel_pure U64.t)) (18uL, Some 42uL) (18uL, Some 42uL))
    as (bundle_test1.b_rel wi ws);
  let _ = serialize_test1' wi out;
  drop_ (bundle_test1.b_rel wi ws);
  S.to_array out;
  0l
}

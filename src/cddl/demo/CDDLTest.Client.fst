module CDDLTest.Client
#lang-pulse
open CDDL.Pulse.Types
open CDDLTest.Test
open Pulse.Lib.Pervasives

module I32 = FStar.Int32
module A = Pulse.Lib.Array
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice

open CDDL.Pulse.Types

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

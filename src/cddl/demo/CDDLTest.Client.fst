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

#set-options "--warn_error -276"

#push-options "--z3rlimit 16"

fn main
  (_: unit)
requires emp
returns res: I32.t
ensures emp
{
  let mut out_a = [| 0uy; 32sz |];
  A.pts_to_len out_a;
  let out = S.from_array out_a 32sz;
  rel_pure_intro 18uL;
  rel_pure_intro 42uL;
  rel_option_some_intro (rel_pure U64.t) 42uL 42uL;
  rel_pair_intro (rel_pure U64.t) 18uL 18uL (rel_option (rel_pure U64.t)) (Some 42uL) (Some 42uL);
  let wi : evercddl_test1_pretty = Mkevercddl_test1_pretty0 (Mkevercddl_uint_pretty0 18uL) (Some (Mkevercddl_uint_pretty0 42uL));
  let ws : Ghost.erased spect_evercddl_test1_pretty = Ghost.hide (Mkspect_evercddl_test1_pretty0 (Mkspect_evercddl_uint_pretty0 18uL) (Some (Mkspect_evercddl_uint_pretty0 42uL)));
  rewrite
    (rel_pair (rel_pure U64.t) (rel_option (rel_pure U64.t)) (18uL, Some 42uL) (18uL, Some 42uL))
    as (rel_evercddl_test1 wi ws);
  let _ = serialize_test1' wi out;
  drop_ (rel_evercddl_test1 wi ws);
  S.to_array out;
  0l
}

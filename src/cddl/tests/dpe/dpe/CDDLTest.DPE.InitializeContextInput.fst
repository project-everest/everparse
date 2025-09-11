module CDDLTest.DPE.InitializeContextInput
module EqTest = CDDL.Spec.EqTest
open CDDLTest.Test
open Pulse.Lib
open Pulse.Lib.Pervasives
open CDDLTest.Destructors
#lang-pulse
let test (x:nat) = assert (x + 1 > 0)

open CDDL.Pulse.Parse.Base
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
open CDDL.Pulse.Types
module T = CDDL.Pulse.AST.Tactics

open CDDL.Pulse.AST.Bundle
open CBOR.Spec.API.Type
open CDDL.Spec.Base
open CDDLTest.DPE.Common

ghost
fn unfold_rel_initialize_context_input_args
    (x:initialize_context_input_args)
    (y:spect_initialize_context_input_args)
requires rel_initialize_context_input_args x y
ensures 
  rel_pair (rel_pair (rel_pair (rel_option rel_evercddl_bool)
                (rel_option rel_evercddl_bool))
            (rel_option rel_bytes))
            tstr_any
  (initialize_context_input_args_left x)
  (spect_initialize_context_input_args_left y) **
  Trade.trade
    (rel_pair (rel_pair (rel_pair (rel_option rel_evercddl_bool)
                (rel_option rel_evercddl_bool))
            (rel_option rel_bytes))
            tstr_any
      (initialize_context_input_args_left x)
      (spect_initialize_context_input_args_left y))
  (rel_initialize_context_input_args x y)
{
  Trade.rewrite_with_trade
    (rel_initialize_context_input_args x y)
    (rel_pair (rel_pair (rel_pair (rel_option rel_evercddl_bool)
                (rel_option rel_evercddl_bool))
            (rel_option rel_bytes))
            tstr_any
      (initialize_context_input_args_left x)
      (spect_initialize_context_input_args_left y));
}


let proj_1_4 (x:(('a & 'b) & 'c) & 'd) = fst (fst (fst x))
let proj_2_4 (x:(('a & 'b) & 'c) & 'd) = snd (fst (fst x))
let proj_3_4 (x:(('a & 'b) & 'c) & 'd) = snd (fst x)
let proj_4_4 (x:(('a & 'b) & 'c) & 'd) = snd x
open Pulse.Lib.Trade
ghost
fn trans_hyp_l_2
  (p1 p2 q1 q2 r: slprop)
requires
  trade p1 p2 **
  trade ((p2 ** q1) ** q2) r
ensures
  trade ((p1 ** q1) ** q2) r
{
  slprop_equivs();
  rewrite each ((p2 ** q1) ** q2) as (p2 ** (q1 ** q2));
  Trade.Util.trans_hyp_l _ _ _ r;
}

ghost
fn destruct_quad 
    (#l0 #l1 #l2 #l3 #h0 #h1 #h2 #h3:Type0)
    (r0:rel l0 h0) (r1:rel l1 h1) (r2:rel l2 h2) (r3:rel l3 h3)
    (x:((l0 & l1) & l2) & l3)
    (y:((h0 & h1) & h2) & h3)
requires 
  rel_pair (rel_pair (rel_pair r0 r1) r2) r3 x y
ensures
  (((r0 (proj_1_4 x) (proj_1_4 y) **
  r1 (proj_2_4 x) (proj_2_4 y)) **
  r2 (proj_3_4 x) (proj_3_4 y)) **
  r3 (proj_4_4 x) (proj_4_4 y)) **
  Trade.trade
    (((r0 (proj_1_4 x) (proj_1_4 y) **
    r1 (proj_2_4 x) (proj_2_4 y)) **
    r2 (proj_3_4 x) (proj_3_4 y)) **
    r3 (proj_4_4 x) (proj_4_4 y))
    (rel_pair (rel_pair (rel_pair r0 r1) r2) r3 x y)
{
  destruct_pair _ r3 _ _ ();
  destruct_pair _ r2 _ _ ();
  Trade.Util.trans_hyp_l _ _ _ (rel_pair (rel_pair (rel_pair r0 r1) r2) r3 x y);
  destruct_pair _ r1 _ _ ();
  trans_hyp_l_2 _ _ _ _ (rel_pair (rel_pair (rel_pair r0 r1) r2) r3 x y);
  rewrite each (fst (fst (fst x))) as (proj_1_4 x);
  rewrite each (snd (fst (fst x))) as (proj_2_4 x);
  rewrite each (snd (fst x)) as (proj_3_4 x);
  rewrite each (snd x) as (proj_4_4 x);

  rewrite each (fst (fst (fst y))) as (proj_1_4 y);
  rewrite each (snd (fst (fst y))) as (proj_2_4 y);
  rewrite each (snd (fst y)) as (proj_3_4 y);
  rewrite each (snd y) as (proj_4_4 y);
}

let is_uds_bytes (uds:Seq.seq UInt8.t) (w:Seq.seq UInt8.t) =
  exists (wx:spect_initialize_context_input_args) (wr:Seq.seq UInt8.t).
          validate_and_parse_postcond_some bundle_initialize_context_input_args.b_spec.parser
          w
          wx
          wr 
          /\
          wx.seed ==
          Some (spect_bytes_right (spect_bstr_right uds))
        
let parsed_initialize_context_input 
    (s:Slice.slice UInt8.t) (#p:perm) (w:erased _)
    (seed:option (Slice.slice UInt8.t))
: slprop
= match seed with
  | None -> pts_to s #p w
  | Some seed -> 
    exists* perm (uds:Seq.seq UInt8.t).
      pts_to seed #perm uds **
      Trade.trade (pts_to seed #perm uds) (pts_to s #p w) **
      pure (is_uds_bytes uds w)
            
fn parse_initialize_context_input_args (s:Slice.slice UInt8.t) (#p:perm) (#w:erased _)
requires pts_to s #p w
returns x:option (Slice.slice UInt8.t) //todo, check that slice_len is uds_len
ensures parsed_initialize_context_input s #p w x
{
  let res = validate_and_parse_initialize_context_input_args s;
  match res {
    None -> {
      unfold validate_and_parse_post;
      fold (parsed_initialize_context_input s #p w None);
      None
    }

    Some xrem -> {
      let (x, rem) = xrem;
      elim_validate_and_parse_post_some x rem;
      unfold_rel_initialize_context_input_args _ _;
      destruct_quad _ _ _ _ _ _;
      Trade.Util.elim_hyp_r _ _ (pts_to s #p w);
      Trade.trade_compose _ _ (pts_to s #p w);
      Trade.trade_compose _ _ (pts_to s #p w);
      Trade.Util.elim_hyp_r _ _ (pts_to s #p w);
      Trade.Util.assoc_hyp_r _ _ _ (pts_to s #p w);
      Trade.Util.elim_hyp_l _ _ (pts_to s #p w);
      Trade.Util.elim_hyp_l _ _ (pts_to s #p w);
      rel_option_cases (rel_bytes) _ _;
      match proj_3_4 (initialize_context_input_args_left x) {
        None -> {
          Trade.elim_trade _ _;
          fold (parsed_initialize_context_input s #p w None);
          None
        }
        Some _ -> {
          let seed = destruct_rel_option (rel_bytes) _ _;
          let seed = extract_bytes seed _;
          Trade.trade_compose _ _ (pts_to s #p w);
          Trade.trade_compose _ _ (pts_to s #p w);
          fold (parsed_initialize_context_input s #p w (Some seed));
          Some seed
        }
      }
    }
  }
}

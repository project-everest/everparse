module CDDLTest.UseDPE
module EqTest = CDDL.Spec.EqTest
open CDDLTest.Test
open Pulse.Lib
open Pulse.Lib.Pervasives

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

let tstr_any = 
  rel_either_left (rel_slice_of_table (mk_eq_test_bij spect_aux_env15_type_1_pretty_right
                    spect_aux_env15_type_1_pretty_left
                    spect_aux_env15_type_1_pretty_left_right
                    spect_aux_env15_type_1_pretty_right_left
                    (mk_eq_test_bij spect_evercddl_uint_pretty_right
                        spect_evercddl_uint_pretty_left
                        spect_evercddl_uint_pretty_left_right
                        spect_evercddl_uint_pretty_right_left
                        (EqTest.eqtype_eq UInt64.t)))
                rel_aux_env15_type_1
                rel_aux_env15_type_3)
            (rel_map_iterator CBOR.Pulse.API.Det.C.cbor_det_match
                CBOR.Pulse.API.Det.C.cbor_det_map_iterator_match
                aux_env15_type_1_pretty
                aux_env15_type_3_pretty
                (CDDL.Pulse.Iterator.Base.mk_spec rel_aux_env15_type_1)
                (CDDL.Pulse.Iterator.Base.mk_spec rel_aux_env15_type_3))

ghost
fn unfold_rel_initialize_context_input_args
    (x:evercddl_initialize_context_input_args_pretty)
    (y:spect_evercddl_initialize_context_input_args_pretty)
requires rel_evercddl_initialize_context_input_args x y
ensures 
  rel_pair (rel_pair (rel_pair (rel_option rel_evercddl_bool)
                (rel_option rel_evercddl_bool))
            (rel_option rel_evercddl_bytes))
            tstr_any
  (evercddl_initialize_context_input_args_pretty_left x)
  (spect_evercddl_initialize_context_input_args_pretty_left y) **
  Trade.trade
    (rel_pair (rel_pair (rel_pair (rel_option rel_evercddl_bool)
                (rel_option rel_evercddl_bool))
            (rel_option rel_evercddl_bytes))
            tstr_any
      (evercddl_initialize_context_input_args_pretty_left x)
      (spect_evercddl_initialize_context_input_args_pretty_left y))
  (rel_evercddl_initialize_context_input_args x y)
{
  Trade.rewrite_with_trade
    (rel_evercddl_initialize_context_input_args x y)
    (rel_pair (rel_pair (rel_pair (rel_option rel_evercddl_bool)
                (rel_option rel_evercddl_bool))
            (rel_option rel_evercddl_bytes))
            tstr_any
      (evercddl_initialize_context_input_args_pretty_left x)
      (spect_evercddl_initialize_context_input_args_pretty_left y));
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
  trade (p2 ** q1 ** q2) r
ensures
  trade (p1 ** q1 ** q2) r
{
  slprop_equivs();
  rewrite each (p2 ** q1 ** q2) as (p2 ** (q1 ** q2));
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
  r0 (proj_1_4 x) (proj_1_4 y) **
  r1 (proj_2_4 x) (proj_2_4 y) **
  r2 (proj_3_4 x) (proj_3_4 y) **
  r3 (proj_4_4 x) (proj_4_4 y) **
  Trade.trade (r0 (proj_1_4 x) (proj_1_4 y) **
               r1 (proj_2_4 x) (proj_2_4 y) **
               r2 (proj_3_4 x) (proj_3_4 y) **
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

fn extract_bytes x (y:erased _)
requires rel_evercddl_bytes x y
returns xx:slice UInt8.t
ensures 
  exists* yy. 
    rel_slice_of_seq false xx yy **
    Trade.trade 
      (rel_slice_of_seq false xx yy)
      (rel_evercddl_bytes x y)
{
  unfold (rel_evercddl_bytes x y);
  destruct_rel_fun _ _ _ _ _;
  with xx yy. unfold (rel_evercddl_bstr xx yy);
  destruct_rel_fun _ _ _ _ _;
  with (res:slice UInt8.t) (resy:_). assert (rel_slice_of_seq false res resy);
  Trade.trade_compose _ _ (rel_fun rel_evercddl_bstr
          evercddl_bytes_pretty_left
          spect_evercddl_bytes_pretty_left
          x
          y);
  res
}

let parsed_initialize_context_input 
    (s:Slice.slice UInt8.t) (#p:perm) (w:erased _)
    (seed:option (slice UInt8.t))
: slprop
= match seed with
  | None -> pts_to s #p w
  | Some seed -> 
    exists* uds. //relate uds to w?
      rel_slice_of_seq false seed uds **
      Trade.trade
        (rel_slice_of_seq false seed uds)
        (pts_to s #p w)


fn parse_initialize_context_input_args (s:Slice.slice UInt8.t) (#p:perm) (#w:erased _)
requires pts_to s #p w
returns x:option (slice UInt8.t) //todo, check that slice_len is uds_len
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
      rel_option_cases (rel_evercddl_bytes) _ _;
      match proj_3_4 (evercddl_initialize_context_input_args_pretty_left x) {
        None -> {
          Trade.elim_trade _ _;
          fold (parsed_initialize_context_input s #p w None);
          None
        }
        Some _ -> {
          let seed = destruct_rel_option (rel_evercddl_bytes) _ _;
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

ghost
fn unfold_with_trade (p:slprop) (s:string)
requires p
ensures norm [delta_only [s]; hnf; iota; primops] p ** Trade.trade (norm [delta_only [s]; hnf; iota; primops] p) p
{
  norm_spec [delta_only [s]; hnf; iota; primops] p;
  Trade.Util.rewrite_with_trade p (norm [delta_only [s]; hnf; iota; primops] p);
  // rewrite norm [delta_once [s]] p as p;
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


fn extract_derice_context_input_args x (w:erased _)
requires rel_evercddl_derive_context_input_args x w
ensures emp
{
  unfold (rel_evercddl_derive_context_input_args x w);
  destruct_rel_fun _ _ _ _ _;
  // with r0 r1 x y. assert (rel_pair r0 r1 
  //     (evercddl_derive_context_input_args_pretty_left x)
  //     (spect_evercddl_derive_context_input_args_pretty_left w)
  // );
  destruct_fst _ _ 
      (evercddl_derive_context_input_args_pretty_left x)
      (spect_evercddl_derive_context_input_args_pretty_left w)
      _;
  destruct_fst _ _ _ _ _;
  destruct_fst _ _ _ _ _;
  destruct_fst _ _ _ _ _;
  destruct_fst _ _ _ _ _;
  destruct_fst _ _ _ _ _;
  destruct_fst _ _ _ _ _;
  destruct_fst _ _ _ _ _;
  destruct_snd _ _ _ _ _;
  admit()
}

fn parse_derive_context_input_args (s:Slice.slice UInt8.t) (#p:perm) (#w:erased _)
requires pts_to s #p w
returns x:option (slice UInt8.t) //todo, check that slice_len is uds_len
ensures pts_to s #p w
{
  let res = validate_and_parse_derive_context_input_args s;
  match res {
    None -> {
      unfold validate_and_parse_post;
      None
    }
    Some xrem -> {
      let (x, rem) = xrem;
      elim_validate_and_parse_post_some x rem;
      extract_derice_context_input_args x _;
      admit()
    }
  }
}
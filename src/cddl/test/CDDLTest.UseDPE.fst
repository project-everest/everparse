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


[@@pulse_unfold]
unfold
let my_unfold (s:string) (p:slprop) = norm [delta_only [s]; hnf; iota; primops] p

ghost
fn unfold_with_trade (s:string) (p:slprop)
requires p
ensures my_unfold s p ** Trade.trade (my_unfold s p) p
{
  norm_spec [delta_only [s]; hnf; iota; primops] p;
  Trade.Util.rewrite_with_trade p (my_unfold s p);
}

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
      // Trade.trade_compose _ _ (pts_to s #p w);
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

noeq
type engine_record_t = {
  l0_image_header:slice UInt8.t;
  l0_image_header_sig:slice UInt8.t;
  l0_binary:slice UInt8.t;
  l0_binary_hash:slice UInt8.t;
  l0_image_auth_pubkey:slice UInt8.t;
}

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

fn destruct_evercddl_bytes_head 
    (x:evercddl_bytes_pretty)
    (w:erased _)
    (rest done res:slprop)
requires
  rel_evercddl_bytes x w **
  Trade.trade ((rel_evercddl_bytes x w ** rest) ** done) res
returns xx:slice UInt8.t
ensures
  exists* ws. 
  rel_slice_of_seq false xx ws **
  Trade.trade (rest ** (done ** rel_slice_of_seq false xx ws)) res
{
  Trade.Util.assoc_hyp_r _ _ _ _;
  let xx = extract_bytes x w;
  Trade.Util.trans_hyp_l _ _ _ res;
  slprop_equivs();
  with ws. assert (rel_slice_of_seq false xx ws);
  with p. rewrite Trade.trade p res as Trade.trade (rest ** (done ** rel_slice_of_seq false xx ws)) res;
  xx
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

let is_engine_record (e:engine_record_t) (res:slprop) : slprop =
  exists* hdr hdr_sig bin bin_hash pk p.
    rel_slice_of_seq false e.l0_image_header hdr **
    rel_slice_of_seq false e.l0_image_header_sig hdr_sig **
    rel_slice_of_seq false e.l0_binary bin **
    rel_slice_of_seq false e.l0_binary_hash bin_hash **
    rel_slice_of_seq false e.l0_image_auth_pubkey pk **
    Trade.trade p res ** 
    pure (p == (rel_slice_of_seq false e.l0_image_header hdr **
                rel_slice_of_seq false e.l0_image_header_sig hdr_sig **
                rel_slice_of_seq false e.l0_binary bin **
                rel_slice_of_seq false e.l0_binary_hash bin_hash **
                rel_slice_of_seq false e.l0_image_auth_pubkey pk))

fn extract_derive_context_engine_record x (w:erased _)
requires rel_evercddl_derive_context_engine_record x w
returns e:engine_record_t
ensures is_engine_record e (rel_evercddl_derive_context_engine_record x w)
{
  unfold_with_trade (`%rel_evercddl_derive_context_engine_record) (rel_evercddl_derive_context_engine_record x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_evercddl_derive_context_engine_record x w);
  let rest, pk = destruct_pair_concrete _ _ _ _ _;
  let rest, bin_hash = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, bin = destruct_pair_concrete_nest _ _ _ _ _ _;
  let hdr, hdr_sig = destruct_pair_concrete_nest _ _ _ _ _ _;
  trade_emp_hyp_r _ _;
  let hdr = destruct_evercddl_bytes_head _ _ _ _ _;
  // trade_emp_hyp_r_elim _ _ _;
  let hdr_sig = destruct_evercddl_bytes_head _ _ _ _ _;
  let bin = destruct_evercddl_bytes_head _ _ _ _ _;
  let bin_hash = destruct_evercddl_bytes_head _ _ _ _ _;
  Trade.Util.assoc_hyp_l _ _ _ _;
  let pk = destruct_evercddl_bytes_head _ _ _ _ _;
  let res = 
    { l0_image_header = hdr;
      l0_image_header_sig = hdr_sig;
      l0_binary = bin;
      l0_binary_hash = bin_hash;
      l0_image_auth_pubkey = pk };
  rewrite each
    hdr as res.l0_image_header,
    hdr_sig as res.l0_image_header_sig,
    bin as res.l0_binary,
    bin_hash as res.l0_binary_hash,
    pk as res.l0_image_auth_pubkey;
  slprop_equivs();
  fold (is_engine_record res);
  res
}

fn destruct_evercddl_nint_head 
    (x:evercddl_nint_pretty)
    (w:erased _)
    (rest done res:slprop)
requires
  rel_evercddl_nint x w **
  Trade.trade ((rel_evercddl_nint x w ** rest) ** done) res
returns xx:UInt64.t
ensures
  pure (xx == evercddl_nint_pretty_left x /\ xx == spect_evercddl_nint_pretty_left w) **
  Trade.trade (rest ** done) res
{
  rewrite each (rel_evercddl_nint x w) as pure (evercddl_nint_pretty_left x == spect_evercddl_nint_pretty_left w);
  Trade.Util.assoc_hyp_r _ _ _ _;
  Trade.Util.elim_hyp_l (pure _) _ _;
  evercddl_nint_pretty_left x
}

fn destruct_evercddl_tstr_head 
    (x:evercddl_tstr_pretty)
    (w:erased _)
    (rest done res:slprop)
requires
  rel_evercddl_tstr x w **
  Trade.trade ((rel_evercddl_tstr x w ** rest) ** done) res
returns xx:slice UInt8.t
ensures exists* ws. 
  rel_slice_of_seq false xx ws **
  Trade.trade (rest ** (done ** rel_slice_of_seq false xx ws)) res
{
  unfold_with_trade (`%rel_evercddl_tstr) (rel_evercddl_tstr x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_evercddl_tstr x w);
  Trade.Util.assoc_hyp_r _ _ _ _;
  Trade.Util.trans_hyp_l _ _ _ res;
  slprop_equivs();
  with (xx:slice UInt8.t) ws. assert (rel_slice_of_seq false xx ws);
  with p. rewrite Trade.trade p res as Trade.trade (rest ** (done ** rel_slice_of_seq false xx ws)) res;
  xx
}

noeq
type device_id_csr_ingredients_t = {
  ku : UInt64.t;
  version: UInt64.t;
  s_common: slice UInt8.t;
  s_org: slice UInt8.t;
  s_country: slice UInt8.t;
}

let is_device_id_csr_ingredients (e:device_id_csr_ingredients_t) (res:slprop) : slprop =
  exists* com org cnt p.
    rel_slice_of_seq false e.s_common com **
    rel_slice_of_seq false e.s_org org **
    rel_slice_of_seq false e.s_country cnt **
    Trade.trade p res ** 
    pure (p == (rel_slice_of_seq false e.s_common com **
                rel_slice_of_seq false e.s_org org **
                rel_slice_of_seq false e.s_country cnt))

fn extract_device_id_csr_ingredients x (w:erased _)
requires rel_evercddl_device_id_csr_ingredients x w
returns res:device_id_csr_ingredients_t
ensures is_device_id_csr_ingredients res (rel_evercddl_device_id_csr_ingredients x w)
{
  unfold_with_trade (`%rel_evercddl_device_id_csr_ingredients) (rel_evercddl_device_id_csr_ingredients x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_evercddl_device_id_csr_ingredients x w);

  let rest, country = destruct_pair_concrete _ _ _ _ _;
  let rest, org = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, common = destruct_pair_concrete_nest _ _ _ _ _ _;
  let ku, version = destruct_pair_concrete_nest _ _ _ _ _ _;

  trade_emp_hyp_r _ _;
  let ku = destruct_evercddl_nint_head _ _ _ _ _;
  let version =  destruct_evercddl_nint_head _ _ _ _ _;
  let s_common = destruct_evercddl_tstr_head _ _ _ _ _;
  let s_org = destruct_evercddl_tstr_head _ _ _ _ _;
  Trade.Util.assoc_hyp_l _ _ _ _;
  let s_country = destruct_evercddl_tstr_head _ _ _ _ _;

 let res = { ku; version; s_common; s_org; s_country };
 rewrite each
    s_common as res.s_common,
    s_org as res.s_org,
    s_country as res.s_country;
  slprop_equivs();
  fold (is_device_id_csr_ingredients res);
  res
}

noeq
type alias_key_crt_ingredients_t = {
  version: UInt64.t;
  serialNumber: slice UInt8.t;
  i_common: slice UInt8.t;
  i_org: slice UInt8.t;
  notBefore: slice UInt8.t;
  notAfter: slice UInt8.t;
  s_common: slice UInt8.t;
  s_org: slice UInt8.t;
  s_country: slice UInt8.t;
  ku: UInt64.t;
  l0_version: UInt64.t
}

[@@pulse_unfold]
unfold
let is_alias_key_crt_ingredients_core (e:alias_key_crt_ingredients_t) sn c o nb na com org cnt : slprop =
  rel_slice_of_seq false e.serialNumber sn **
  rel_slice_of_seq false e.i_common c **
  rel_slice_of_seq false e.i_org o **
  rel_slice_of_seq false e.notBefore nb **
  rel_slice_of_seq false e.notAfter na **
  rel_slice_of_seq false e.s_common com **
  rel_slice_of_seq false e.s_org org **
  rel_slice_of_seq false e.s_country cnt

#push-options "--query_stats"
fn make_alias_key_crt_ingredients 
    (version:UInt64.t)
    serialNumber
    i_common
    i_org
    notBefore
    notAfter
    s_common
    s_org
    s_country
    (ku
     l0_version: UInt64.t)
requires 
  rel_slice_of_seq false serialNumber 'n **
  rel_slice_of_seq false i_common 'c **
  rel_slice_of_seq false i_org 'o **
  rel_slice_of_seq false notBefore 'nb **
  rel_slice_of_seq false notAfter 'na **
  rel_slice_of_seq false s_common 'com **
  rel_slice_of_seq false s_org 'org **
  rel_slice_of_seq false s_country 'cnt
returns 
  e:alias_key_crt_ingredients_t
ensures
  is_alias_key_crt_ingredients_core e 'n 'c 'o 'nb 'na 'com 'org 'cnt **
  pure (e == { ku; s_country; s_org; s_common; i_org; i_common; notAfter; notBefore; version; serialNumber; l0_version })
{
  let res = { ku; s_country; s_org; s_common; i_org; i_common; notAfter; notBefore; version; serialNumber; l0_version };
  rewrite each
    i_common as res.i_common,
    i_org as res.i_org,
    notBefore as res.notBefore,
    notAfter as res.notAfter,
    version as res.version,
    serialNumber as res.serialNumber,
    l0_version as res.l0_version,
    ku as res.ku,
    s_common as res.s_common,
    s_org as res.s_org,
    s_country as res.s_country;
  res
}

let is_alias_key_crt_ingredients (e:alias_key_crt_ingredients_t) (res:slprop) : slprop =
  exists* sn c o nb na com org cnt.
    is_alias_key_crt_ingredients_core e sn c o nb na com org cnt **
    Trade.trade (is_alias_key_crt_ingredients_core e sn c o nb na com org cnt) res

#push-options "--query_stats --ext nothing"
fn extract_alias_key_crt_ingredients x (w:erased _)
requires rel_evercddl_alias_key_crt_ingredients x w
returns res:alias_key_crt_ingredients_t
ensures is_alias_key_crt_ingredients res (rel_evercddl_alias_key_crt_ingredients x w)
{
  unfold_with_trade (`%rel_evercddl_alias_key_crt_ingredients) (rel_evercddl_alias_key_crt_ingredients x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_evercddl_alias_key_crt_ingredients x w);

  let rest, l0_version = destruct_pair_concrete _ _ _ _ _;
  let rest, ku = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, country = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, org = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, common = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, notAfter = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, notBefore = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, org = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, common = destruct_pair_concrete_nest _ _ _ _ _ _;
  let version, serialNumber = destruct_pair_concrete_nest _ _ _ _ _ _;

  trade_emp_hyp_r _ _;
  let version =  destruct_evercddl_nint_head _ _ _ _ _;
  let serialNumber =  destruct_evercddl_bytes_head _ _ _ _ _;
  let i_common =  destruct_evercddl_tstr_head _ _ _ _ _;
  let i_org =  destruct_evercddl_tstr_head _ _ _ _ _;
  let notBefore = destruct_evercddl_bytes_head _ _ _ _ _;
  let notAfter = destruct_evercddl_bytes_head _ _ _ _ _;
  let s_common =  destruct_evercddl_tstr_head _ _ _ _ _;
  let s_org =  destruct_evercddl_tstr_head _ _ _ _ _;
  let s_country =  destruct_evercddl_tstr_head _ _ _ _ _;
  let ku = destruct_evercddl_nint_head _ _ _ _ _;
  Trade.Util.assoc_hyp_l _ _ _ _;
  let l0_version = destruct_evercddl_nint_head _ _ _ _ _;

  let res = make_alias_key_crt_ingredients 
    version
    serialNumber
    i_common
    i_org
    notBefore
    notAfter
    s_common
    s_org
    s_country
    ku
    l0_version;
  slprop_equivs();
  fold (is_alias_key_crt_ingredients res (rel_evercddl_alias_key_crt_ingredients x w));
  res

}


noeq
type derive_context_l0_record_t = {
  fwid: slice UInt8.t;
  device_id_label: slice UInt8.t;
  alias_key_label: slice UInt8.t;
  device_id_csr_ingredients: device_id_csr_ingredients_t;
  alias_key_crt_ingredients: alias_key_crt_ingredients_t;
}

[@@pulse_unfold]
unfold
let is_derive_context_l0_record_core (e:derive_context_l0_record_t) fid did akl : slprop =
  rel_slice_of_seq false e.fwid fid **
  rel_slice_of_seq false e.device_id_label did **
  rel_slice_of_seq false e.alias_key_label akl

let is_derive_context_l0_record (e:derive_context_l0_record_t) (k:slprop) =
  exists* fid did akl k1 k2.
    is_derive_context_l0_record_core e fid did akl **
    is_device_id_csr_ingredients e.device_id_csr_ingredients k1 **
    is_alias_key_crt_ingredients e.alias_key_crt_ingredients k2 **
    Trade.trade (is_derive_context_l0_record_core e fid did akl ** k1 ** k2) k

fn make_derive_context_l0_record
    fwid device_id_label alias_key_label
    device_id_csr_ingredients
    alias_key_crt_ingredients
requires 
  rel_slice_of_seq false fwid 'fid **
  rel_slice_of_seq false device_id_label 'did **
  rel_slice_of_seq false alias_key_label 'akl **
  is_device_id_csr_ingredients device_id_csr_ingredients 'k1 **
  is_alias_key_crt_ingredients alias_key_crt_ingredients 'k2
returns 
  e:derive_context_l0_record_t
ensures
  is_derive_context_l0_record_core e 'fid 'did 'akl **
  is_device_id_csr_ingredients e.device_id_csr_ingredients 'k1 **
  is_alias_key_crt_ingredients e.alias_key_crt_ingredients 'k2 **
  pure (e == { fwid; device_id_label; alias_key_label; device_id_csr_ingredients; alias_key_crt_ingredients })
{
  let res = { fwid; device_id_label; alias_key_label; device_id_csr_ingredients; alias_key_crt_ingredients };
  rewrite each
    fwid as res.fwid,
    device_id_label as res.device_id_label,
    alias_key_label as res.alias_key_label,
    device_id_csr_ingredients as res.device_id_csr_ingredients,
    alias_key_crt_ingredients as res.alias_key_crt_ingredients;
  res
}

fn extract_derive_context_l0_record x (w:erased _)
requires rel_evercddl_derive_context_l0_record x w
returns res:derive_context_l0_record_t
ensures is_derive_context_l0_record res (rel_evercddl_derive_context_l0_record x w)
{
  unfold_with_trade (`%rel_evercddl_derive_context_l0_record) (rel_evercddl_derive_context_l0_record x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_evercddl_derive_context_l0_record x w);

  let rest, ak_i = destruct_pair_concrete _ _ _ _ _;
  let rest, did_i = destruct_pair_concrete_nest _ _ _ _ _ _;
  let rest, akl = destruct_pair_concrete_nest _ _ _ _ _ _;
  let fwid, did_l = destruct_pair_concrete_nest _ _ _ _ _ _;

  trade_emp_hyp_r _ _;

  let fwid = destruct_evercddl_bytes_head _ _ _ _ _;
  let device_id_label = destruct_evercddl_bytes_head _ _ _ _ _;
  let alias_key_label = destruct_evercddl_bytes_head _ _ _ _ _;
  let device_id_csr_ingredients = extract_device_id_csr_ingredients _ _;
  Trade.Util.assoc_hyp_l _ _ _ _;
  let alias_key_crt_ingredients = extract_alias_key_crt_ingredients _ _;
  let res = make_derive_context_l0_record 
    fwid
    device_id_label
    alias_key_label
    device_id_csr_ingredients
    alias_key_crt_ingredients;
  slprop_equivs();
  fold (is_derive_context_l0_record res (rel_evercddl_derive_context_l0_record x w));
  res
}

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

ghost
fn is_engine_record_compose (e:engine_record_t) (res res':slprop)
requires is_engine_record e res ** Trade.trade res res'
ensures is_engine_record e res'
{
  unfold is_engine_record;
  Trade.trade_compose _ _ res';
  fold is_engine_record;
}

ghost
fn is_derive_context_l0_record_compose e res res'
requires is_derive_context_l0_record e res ** Trade.trade res res'
ensures is_derive_context_l0_record e res'
{
  unfold is_derive_context_l0_record;
  Trade.trade_compose _ _ res';
  fold is_derive_context_l0_record
}

let is_derive_context_input_args 
    (e:either engine_record_t derive_context_l0_record_t) 
    (res:slprop) 
: slprop
= match e with
  | Inl e -> is_engine_record e res
  | Inr e -> is_derive_context_l0_record e res

fn extract_derive_context_input_args_data x (w:erased _)
requires rel_evercddl_derive_context_input_args_data x w
returns e:either engine_record_t derive_context_l0_record_t
ensures is_derive_context_input_args e (rel_evercddl_derive_context_input_args_data x w)
{
  unfold_with_trade (`%rel_evercddl_derive_context_input_args_data) (rel_evercddl_derive_context_input_args_data _ _);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_evercddl_derive_context_input_args_data x w);
  rel_either_cases _ _ _ _;
  match (evercddl_derive_context_input_args_data_pretty_left x) {
    Inl _ -> {
      let _ = destruct_rel_either_left _ _ _ _ _;
      let engine_record = extract_derive_context_engine_record _ _;
      is_engine_record_compose _ _ _;
      fold (is_derive_context_input_args (Inl engine_record));
      Inl engine_record
    }

    Inr l0 -> {
      let _ = destruct_rel_either_right _ _ _ _ _;
      let l0_record = extract_derive_context_l0_record _ _;
      is_derive_context_l0_record_compose _ _ _;
      fold (is_derive_context_input_args (Inr l0_record));
      Inr l0_record
    }
  }
}

ghost
fn fold_with_trade (s:string) (p:slprop)
requires my_unfold s p
ensures p
{
  norm_spec [delta_only [s]; hnf; iota; primops] p;
  rewrite (my_unfold s p) as p;
}


[@@pulse_unfold]
unfold
let my_unfold_any (#a:Type) (s:string) (p:a) = norm [delta_only [s]; hnf; iota; primops] p

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
  rel_pair r (my_unfold_any s p) x y **
  Trade.trade (rel_pair r (my_unfold_any s p) x y) res
ensures rel_pair r p x y **   Trade.trade (rel_pair r p x y) res
{
  norm_spec [delta_only [s]; hnf; iota; primops] p;
  rewrite each (my_unfold_any s p) as p;
}


// fn test_fold x y
// requires
//  rel_either_left (rel_slice_of_table (mk_eq_test_bij spect_aux_env15_type_1_pretty_right
//                     spect_aux_env15_type_1_pretty_left
//                     spect_aux_env15_type_1_pretty_left_right
//                     spect_aux_env15_type_1_pretty_right_left
//                     (mk_eq_test_bij spect_evercddl_uint_pretty_right
//                         spect_evercddl_uint_pretty_left
//                         spect_evercddl_uint_pretty_left_right
//                         spect_evercddl_uint_pretty_right_left
//                         (EqTest.eqtype_eq UInt64.t)))
//                 rel_aux_env15_type_1
//                 rel_aux_env15_type_3)
//             (rel_map_iterator CBOR.Pulse.API.Det.C.cbor_det_match
//                 CBOR.Pulse.API.Det.C.cbor_det_map_iterator_match
//                 aux_env15_type_1_pretty
//                 aux_env15_type_3_pretty
//                 (CDDL.Pulse.Iterator.Base.mk_spec rel_aux_env15_type_1)
//                 (CDDL.Pulse.Iterator.Base.mk_spec rel_aux_env15_type_3))
//                 x y
// ensures
//   tstr_any x y
// {
//   fold_with_trade (`%tstr_any) (tstr_any x y);
// }


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

let is_derive_context_input
    (res:option (either engine_record_t derive_context_l0_record_t))
    (dflt:slprop) =
  match res with
  | None -> dflt
  | Some e -> is_derive_context_input_args e dflt

ghost
fn trans_is_derive_context_input_args
     e res res'
requires is_derive_context_input_args e res ** Trade.trade res res'
ensures is_derive_context_input_args e res'
{
  unfold is_derive_context_input_args;
  match e {
    Inl e -> {
      assert (is_engine_record e res);
      is_engine_record_compose e res res';
      fold (is_derive_context_input_args (Inl e));
    }
    Inr e -> {
      assert (is_derive_context_l0_record e res);
      is_derive_context_l0_record_compose e res res';
      fold (is_derive_context_input_args (Inr e));
    }
  }
}

fn extract_option_derive_context_input_args_data x (w:erased _) res
requires rel_option (rel_evercddl_derive_context_input_args_data) x w **
         Trade.trade (rel_option (rel_evercddl_derive_context_input_args_data) x w)
                      res
returns e:option (either engine_record_t derive_context_l0_record_t)
ensures is_derive_context_input e res
{
  rel_option_cases _ _ _;
  match x {
    None -> {
      Trade.elim_trade _ _;
      fold (is_derive_context_input None res);
      None    
    }
    Some x -> {
     let xx = destruct_rel_option _ _ _;
     Trade.trade_compose _ _ res;
     let ret = extract_derive_context_input_args_data _ _;
     trans_is_derive_context_input_args _ _ _;
     fold (is_derive_context_input (Some ret) res);
     Some ret
    }
  }
}

fn extract_derive_context_input_args x (w:erased _)
requires rel_evercddl_derive_context_input_args x w
returns e:option (either engine_record_t derive_context_l0_record_t)
ensures is_derive_context_input e (rel_evercddl_derive_context_input_args x w)
{
  unfold_with_trade
    (`%rel_evercddl_derive_context_input_args) 
    (rel_evercddl_derive_context_input_args x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_evercddl_derive_context_input_args x w);
  fold_last_relation (`%tstr_any) tstr_any;  
  let rest_12 = fst_pair_concrete _ _ _ _ _;
  let rest_11 = fst_pair_concrete _ _ _ _ _;
  let rest_10 = fst_pair_concrete _ _ _ _ _;
  let rest_9 = fst_pair_concrete _ _ _ _ _;
  let rest_8 = fst_pair_concrete _ _ _ _ _;
  let rest_7 = fst_pair_concrete _ _ _ _ _;
  let rest_6 = fst_pair_concrete _ _ _ _ _;
  let input_data = snd_pair_concrete _ _ _ _ _;
  rewrite each  
    (Tactics.PrettifyType.named "intkey6"
          evercddl_derive_context_input_args_data_pretty)
  as evercddl_derive_context_input_args_data_pretty;
  extract_option_derive_context_input_args_data _ _ _;
}

ghost
fn trans_is_derive_context_input
     e res res'
requires is_derive_context_input e res ** Trade.trade res res'
ensures is_derive_context_input e res'
{
  unfold is_derive_context_input;
  match e {
    None -> {
      Trade.elim_trade _ _;
      fold (is_derive_context_input None res');
    }
    Some e -> {
      assert (is_derive_context_input_args e res);
      trans_is_derive_context_input_args e res res';
      fold (is_derive_context_input (Some e) res');
    }
  }
}


fn parse_derive_context_input_args (s:Slice.slice UInt8.t) (#p:perm) (#w:erased _)
requires pts_to s #p w
returns e:option (either engine_record_t derive_context_l0_record_t)
ensures is_derive_context_input e (pts_to s #p w)
{
  let res = validate_and_parse_derive_context_input_args s;
  match res {
    None -> {
      unfold validate_and_parse_post;
      fold (is_derive_context_input None (pts_to s #p w));
      None
    }
    Some xrem -> {
      let (x, rem) = xrem;
      elim_validate_and_parse_post_some x rem;
      let res = extract_derive_context_input_args x _;
      Trade.Util.elim_hyp_r _ _ _;
      trans_is_derive_context_input _ _ _;
      res
    }
  }
}
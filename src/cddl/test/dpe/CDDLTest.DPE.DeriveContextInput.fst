module CDDLTest.DPE.DeriveContextInput
module EqTest = CDDL.Spec.EqTest
open CDDLTest.Test
open Pulse.Lib
open Pulse.Lib.Pervasives
open CDDLTest.Destructors
#lang-pulse
open CDDL.Pulse.Parse.Base
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
open CDDL.Pulse.Types
module T = CDDL.Pulse.AST.Tactics
open CDDL.Pulse.AST.Bundle
open CBOR.Spec.API.Type
open CDDL.Spec.Base
open CDDLTest.DPE.Common
// 

noeq
type engine_record_t = {
  l0_image_header:slice UInt8.t;
  l0_image_header_sig:slice UInt8.t;
  l0_binary:slice UInt8.t;
  l0_binary_hash:slice UInt8.t;
  l0_image_auth_pubkey:slice UInt8.t;
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
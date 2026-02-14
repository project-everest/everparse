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
  l0_image_header:Slice.slice UInt8.t;
  l0_image_header_sig:Slice.slice UInt8.t;
  l0_binary:Slice.slice UInt8.t;
  l0_binary_hash:Slice.slice UInt8.t;
  l0_image_auth_pubkey:Slice.slice UInt8.t;
}

let engine_record = derive_context_engine_record
let spec_engine_record = spect_derive_context_engine_record
let is_engine_record_core
      (e:engine_record)
      (wx:spec_engine_record)
: slprop
= (((rel_bytes e.l0_image_header wx.l0_image_header **
  rel_bytes e.l0_image_header_sig wx.l0_image_header_sig) **
  rel_bytes e.l0_binary wx.l0_binary) **
  rel_bytes e.l0_binary_hash wx.l0_binary_hash) **
  rel_bytes e.l0_image_auth_pubkey wx.l0_image_auth_pubkey

[@@pulse_unfold]
let is_engine_record (e:engine_record) (se:spec_engine_record) res : slprop =
  is_engine_record_core e se **
  Trade.trade (is_engine_record_core e se) res


ghost
fn extract_derive_context_engine_record x (w: _)
requires rel_derive_context_engine_record x w
ensures is_engine_record x w (rel_derive_context_engine_record x w)
{
  Trade.rewrite_with_trade 
    (rel_derive_context_engine_record x w)
    (is_engine_record_core x w);
}

let spec_device_id_csr_ingredients = spect_device_id_csr_ingredients
let is_device_id_csr_ingredients_core (e:device_id_csr_ingredients) (se:spec_device_id_csr_ingredients) : slprop =
    (((rel_nint e.ku se.ku **
    rel_nint e.version se.version) **
    rel_tstr e.s_common se.s_common) **
    rel_tstr e.s_org se.s_org) **
    rel_tstr e.s_country se.s_country

[@@pulse_unfold]
let is_device_id_csr_ingredients (e:device_id_csr_ingredients) (se:spec_device_id_csr_ingredients) res : slprop =
    is_device_id_csr_ingredients_core e se **
    Trade.trade (is_device_id_csr_ingredients_core e se) res
    
ghost 
fn extract_device_id_csr_ingredients x (w:erased _)
requires rel_device_id_csr_ingredients x w
ensures is_device_id_csr_ingredients x w (rel_device_id_csr_ingredients x w)
{
  Trade.rewrite_with_trade 
    (rel_device_id_csr_ingredients x w)
    (is_device_id_csr_ingredients_core x w);
}

let spec_alias_key_crt_ingredients = spect_alias_key_crt_ingredients

let is_alias_key_crt_ingredients_core (e:alias_key_crt_ingredients) (s:spec_alias_key_crt_ingredients) =
  (((((((((rel_nint e.version s.version **
  rel_bytes e.serial_number s.serial_number) **
  rel_tstr e.i_common s.i_common) **
  rel_tstr e.i_org s.i_org) **
  rel_bytes e.not_before s.not_before) **
  rel_bytes e.not_after s.not_after) **
  rel_tstr e.s_common s.s_common) **
  rel_tstr e.s_org s.s_org) **
  rel_tstr e.s_country s.s_country) **
  rel_nint e.ku s.ku) **
  rel_nint e.l0_version s.l0_version

[@@pulse_unfold]
let is_alias_key_crt_ingredients (e:alias_key_crt_ingredients) (s:spec_alias_key_crt_ingredients) (res:slprop) : slprop =
  is_alias_key_crt_ingredients_core e s **
  Trade.trade (is_alias_key_crt_ingredients_core e s) res

ghost
fn extract_alias_key_crt_ingredients x (w:erased _)
requires rel_alias_key_crt_ingredients x w
ensures is_alias_key_crt_ingredients x w (rel_alias_key_crt_ingredients x w)
{
  Trade.rewrite_with_trade 
    (rel_alias_key_crt_ingredients x w)
    (is_alias_key_crt_ingredients_core x w);
}

let l0_record = derive_context_l0_record
let spec_l0_record = spect_derive_context_l0_record
let is_l0_record_core (e:l0_record) (wx:spec_l0_record) : slprop =
  (((rel_bytes e.fwid wx.fwid **
  rel_bytes e.device_id_label wx.device_id_label) **
  rel_bytes e.alias_key_label wx.alias_key_label) **
  is_device_id_csr_ingredients_core e.device_id_csr_ingredients wx.device_id_csr_ingredients) **
  is_alias_key_crt_ingredients_core e.alias_key_crt_ingredients wx.alias_key_crt_ingredients

[@@pulse_unfold]
let is_l0_record (e:l0_record) (se:spec_l0_record) res : slprop =
  is_l0_record_core e se **
  Trade.trade (is_l0_record_core e se) res

ghost
fn extract_derive_context_l0_record x (w: _)
requires rel_derive_context_l0_record x w
ensures is_l0_record x w (rel_derive_context_l0_record x w)
{
  Trade.rewrite_with_trade 
    (rel_derive_context_l0_record x w)
    (is_l0_record_core x w);
}

let is_derive_context_input_args_data
    (e:either engine_record l0_record) 
    (res:either spec_engine_record spec_l0_record)
    (k:slprop)
: slprop
= match e, res with
  | Inl er, Inl s_er ->
    is_engine_record er s_er k 
  | Inr l0, Inr s_l0 ->
    is_l0_record l0 s_l0 k
  | _ -> pure False

ghost
fn is_dci_cases e res k
requires is_derive_context_input_args_data e res k
ensures is_derive_context_input_args_data e res k **
        pure (Inl? e <==> Inl? res)
{
  match e {
    Inl e' -> {
      match res {
        Inr _ -> {
          unfold is_derive_context_input_args_data;
          assert pure (False);
          unreachable ()
        }
        Inl res' -> {
          unfold is_derive_context_input_args_data;
          fold (is_derive_context_input_args_data (Inl e') (Inl res') k);
          rewrite (is_derive_context_input_args_data (Inl e') (Inl res') k)
          as is_derive_context_input_args_data e res k;
        }
      }
    }

    Inr e' -> {
      match res {
        Inl _ -> {
          unfold is_derive_context_input_args_data;
          assert pure (False);
          unreachable ()
        }
        Inr res' -> {
          unfold is_derive_context_input_args_data;
          fold (is_derive_context_input_args_data (Inr e') (Inr res') k);
          rewrite (is_derive_context_input_args_data (Inr e') (Inr res') k)
          as is_derive_context_input_args_data e res k;
        }
      }
    }
  }
}

ghost
fn claim_is_dci e s k
requires is_derive_context_input_args_data e s k
ensures k
{
  is_dci_cases _ _ _;
  match e {
    Inl eng -> {
      let Inl spec_l = s;
      unfold is_derive_context_input_args_data;
      assert (is_engine_record_core eng spec_l);
      Trade.elim_trade _ _;
    }
    Inr l0 -> {
      let Inr spec_r = s;
      unfold is_derive_context_input_args_data;
      assert (is_l0_record_core l0 spec_r);
      Trade.elim_trade _ _;
    }
  }
}

ghost
fn trans_is_derive_context_input
    (e:either engine_record l0_record) 
    (res:either spec_engine_record spec_l0_record)
    (k k':slprop)
requires 
  is_derive_context_input_args_data e res k **
  Trade.trade k k'
ensures
  is_derive_context_input_args_data e res k'
{
  unfold (is_derive_context_input_args_data e res k);
  match e {
    Inl x -> {
      match res {
        Inr _ -> { 
          assert pure (False);
          unreachable ()
        }

        Inl w -> {
          Trade.trade_compose _ _ k';
          fold (is_derive_context_input_args_data (Inl x) (Inl w) k');
          rewrite (is_derive_context_input_args_data (Inl x) (Inl w) k')
          as is_derive_context_input_args_data e res k';
        }
      }

    }
  
    Inr x -> {
      match res {
        Inl _ -> { 
          assert pure (False);
          unreachable ()
        }

        Inr w -> {
          Trade.trade_compose _ _ k';
          fold (is_derive_context_input_args_data (Inr x) (Inr w) k');
          rewrite (is_derive_context_input_args_data (Inr x) (Inr w) k')
          as is_derive_context_input_args_data e res k';
        }
      }

    }
  }
}

[@@pulse_unfold]
let norm_token = emp

ghost
fn destruct_rel_either_left 
    (#a #b #a' #b':Type0) 
    (r:rel a b)
    (r':rel a' b')
    (x:either a a')
    (y:either b b')
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

ghost
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
fn extract_derive_context_input_args_data x (w:_)
requires rel_derive_context_input_args_data x w
ensures is_derive_context_input_args_data 
          (derive_context_input_args_data_left x)
          (spect_derive_context_input_args_data_left w)
          (rel_derive_context_input_args_data x w)
{
  unfold_with_trade (`%rel_derive_context_input_args_data) (rel_derive_context_input_args_data _ _);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_derive_context_input_args_data x w);
  rel_either_cases _ _ _ _;
  match (derive_context_input_args_data_left x) {
    Inl _ -> {
      let _ = destruct_rel_either_left _ _ _ _ _;
      let engine_record = extract_derive_context_engine_record _ _;
      with xx yy. assert (is_engine_record_core xx yy);
      Trade.trade_compose _ _ (rel_derive_context_input_args_data x w);
      rewrite each x as (derive_context_input_args_data_right (Inl xx));
      rewrite each w as (spect_derive_context_input_args_data_right (Inl yy));
      fold (is_derive_context_input_args_data (Inl xx) (Inl yy));
      with k' . rewrite (is_derive_context_input_args_data (Inl xx) (Inl yy) k')
      as is_derive_context_input_args_data 
          (derive_context_input_args_data_left x)
          (spect_derive_context_input_args_data_left w)
          (rel_derive_context_input_args_data x w);
    }

    Inr l0 -> {
      let _ = destruct_rel_either_right _ _ _ _ _;
      let l0_record = extract_derive_context_l0_record _ _;
      with xx yy. assert (is_l0_record_core xx yy);
      Trade.trade_compose _ _ (rel_derive_context_input_args_data x w);
      rewrite each x as (derive_context_input_args_data_right (Inr xx));
      rewrite each w as (spect_derive_context_input_args_data_right (Inr yy));
      fold (is_derive_context_input_args_data (Inr xx) (Inr yy));
      with k' . rewrite (is_derive_context_input_args_data (Inr xx) (Inr yy) k')
      as is_derive_context_input_args_data 
          (derive_context_input_args_data_left x)
          (spect_derive_context_input_args_data_left w)
          (rel_derive_context_input_args_data x w);
    }
  }
}

let is_record_opt
      (e:option (either engine_record l0_record)) 
      (res:option (either spec_engine_record spec_l0_record))
      k : slprop =
  match e, res with
  | None, None -> k
  | Some ee, Some eres -> 
    is_derive_context_input_args_data ee eres k
  | _, _ -> pure False

ghost
fn is_record_opt_cases e s k
requires is_record_opt e s k
ensures  is_record_opt e s k ** pure (Some? e <==> Some? s)
{
  match e {
    None -> {
      match s {
        Some _ -> {
          unfold is_record_opt;
          assert pure (False);
          unreachable ()
        }
        None -> {
          unfold is_record_opt;
          fold (is_record_opt None None k);
          rewrite (is_record_opt None None k)
          as is_record_opt e s k;
        }
      }
    }

    Some e' -> {
      match s {
        None -> {
          unfold is_record_opt;
          assert pure (False);
          unreachable ()
        }
        Some s' -> {
          unfold is_record_opt;
          fold (is_record_opt (Some e') (Some s') k);
          rewrite (is_record_opt (Some e') (Some s') k)
          as is_record_opt e s k;
        }
      }
    }
  }
} 

ghost
fn elim_is_record_opt_none s k
requires is_record_opt None s k
ensures pure (s == None) ** k
{
  is_record_opt_cases _ _ _;
  let None = s;
  unfold is_record_opt;
}

ghost
fn elim_is_record_opt_some r s k
requires is_record_opt (Some r) s k
returns _:squash (Some? s)
ensures is_derive_context_input_args_data r (Some?.v s) k
{
  is_record_opt_cases _ _ _;
  let Some s' = s;
  unfold is_record_opt;
  rewrite is_derive_context_input_args_data r s' k
  as is_derive_context_input_args_data r (Some?.v s) k;
}

ghost
fn is_record_opt_compose
    (e:option (either engine_record l0_record)) 
    (res:option (either spec_engine_record spec_l0_record))
    k k'
requires is_record_opt e res k ** Trade.trade k k'
ensures is_record_opt e res k'
{
  unfold (is_record_opt e res k);
  match e {
    None -> {
      match res {
        None -> {  
          Trade.elim_trade _ _;
          fold (is_record_opt None None k');
          rewrite (is_record_opt None None k')
          as is_record_opt e res k';
        }
        Some _ -> { 
          assert pure (False);
          unreachable ()
        }
      }
    }

    Some e' -> {
      match res {
        None -> { 
          assert pure (False);
          unreachable ()
        }
        Some res' -> {
          trans_is_derive_context_input _ _ _ _;
          fold (is_record_opt (Some e') (Some res') k');
          rewrite (is_record_opt (Some e') (Some res') k')
          as is_record_opt e res k';
        }
      }
    }
  }
}

inline_for_extraction
let map_opt (x:option 'a) (f:'a -> 'b) : option 'b = 
  match x with
  | None -> None
  | Some v -> Some (f v)


ghost
fn destruct_rel_option (#a #b:Type0) (r:rel a b) (x:option a) (y:option b)
requires 
  rel_option r x y ** pure (Some? x)
returns _:squash (Some? y /\ Some? x)
ensures
    r (Some?.v x) (Some?.v y) **
    Trade.trade (r (Some?.v x) (Some?.v y)) (rel_option r x y)
{
  rel_option_cases r _ _;
  rel_option_eq_some r (Some?.v x) (Some?.v y);
  Trade.rewrite_with_trade 
    (rel_option r x y)
    (r (Some?.v x) (Some?.v y));
  ()
}

ghost
fn extract_derive_context_input_args_data_opt x w
requires rel_option rel_derive_context_input_args_data x w
ensures 
  is_record_opt 
    (map_opt x derive_context_input_args_data_left)
    (map_opt w spect_derive_context_input_args_data_left)
    (rel_option rel_derive_context_input_args_data x w)
{
  rel_option_cases _ _ _;
  match x {
    None -> { 
      rewrite each w as None;
      fold (is_record_opt None None (rel_option rel_derive_context_input_args_data None None));
      with k' . rewrite (is_record_opt None None k')
      as is_record_opt 
        (map_opt x derive_context_input_args_data_left)
        (map_opt w spect_derive_context_input_args_data_left)
        (rel_option rel_derive_context_input_args_data x w);
      ()
    }
    Some v -> { 
      rewrite each (Some v) as x;
      destruct_rel_option _ _ _;
      extract_derive_context_input_args_data _ _;
      trans_is_derive_context_input _ _ _ (rel_option rel_derive_context_input_args_data x w);
      with xx yy k. assert (is_derive_context_input_args_data xx yy k);
      fold (is_record_opt (Some xx) (Some yy));
      rewrite
        is_record_opt (Some (derive_context_input_args_data_left (Some?.v x)))
        (Some (spect_derive_context_input_args_data_left (Some?.v w)))
        (rel_option rel_derive_context_input_args_data x w)
      as is_record_opt (map_opt x derive_context_input_args_data_left)
      (map_opt w spect_derive_context_input_args_data_left)
      (rel_option rel_derive_context_input_args_data x w);
    }
  }
}


ghost
fn fst_pair (#l0 #l1 #h0 #h1:Type0)
  (r0:rel l0 h0) 
  (r1:rel l1 h1)
  (xl: (l0 & l1))
  (xh: (h0 & h1)) (res:slprop)
requires 
  rel_pair r0 r1 xl xh **
  Trade.trade (rel_pair r0 r1 xl xh) res
ensures 
  r0 (fst xl) (fst xh) ** 
  Trade.trade (r0 (fst xl) (fst xh)) res
{
  Trade.Util.rewrite_with_trade 
    (rel_pair r0 r1 xl xh)
    (r0 (fst xl) (fst xh) ** r1 (snd xl) (snd xh));
  Trade.trade_compose _ _ res;
  Trade.Util.elim_hyp_r _ _ res;
}

ghost
fn snd_pair (#l0 #l1 #h0 #h1:Type0)
  (r0:rel l0 h0) 
  (r1:rel l1 h1)
  (xl: (l0 & l1))
  (xh: (h0 & h1)) (res:slprop)
requires 
  rel_pair r0 r1 xl xh **
  Trade.trade (rel_pair r0 r1 xl xh) res
ensures 
  r1 (snd xl) (snd xh) ** 
  Trade.trade (r1 (snd xl) (snd xh)) res
{
  Trade.Util.rewrite_with_trade 
    (rel_pair r0 r1 xl xh)
    (r0 (fst xl) (fst xh) ** r1 (snd xl) (snd xh));
  Trade.trade_compose _ _ res;
  Trade.Util.elim_hyp_l _ _ res;
}

ghost
fn extract_derive_context_input_args x w
requires rel_derive_context_input_args x w
ensures 
  is_record_opt 
    (map_opt x.input_data derive_context_input_args_data_left)
    (map_opt w.input_data spect_derive_context_input_args_data_left) 
    (rel_derive_context_input_args x w)
{
  unfold_with_trade
    (`%rel_derive_context_input_args) 
    (rel_derive_context_input_args x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_derive_context_input_args x w);
  fold_last_relation (`%tstr_any) tstr_any;  
  let rest_12 = fst_pair _ _ _ _ _;
  let rest_11 = fst_pair _ _ _ _ _;
  let rest_10 = fst_pair _ _ _ _ _;
  let rest_9 = fst_pair _ _ _ _ _;
  let rest_8 = fst_pair _ _ _ _ _;
  let rest_7 = fst_pair _ _ _ _ _;
  let rest_6 = fst_pair _ _ _ _ _;
  let input_data = snd_pair _ _ _ _ _;
  rewrite each  
    (Tactics.PrettifyType.named "input_data"
          derive_context_input_args_data)
  as derive_context_input_args_data;
  rewrite each  
    (Tactics.PrettifyType.named "input_data"
          spect_derive_context_input_args_data)
  as spect_derive_context_input_args_data;
  extract_derive_context_input_args_data_opt _ _;
  is_record_opt_compose _ _ _ _;
  with k l m . rewrite is_record_opt k l m
  as is_record_opt (map_opt x.input_data derive_context_input_args_data_left)
      (map_opt w.input_data spect_derive_context_input_args_data_left)
      (rel_derive_context_input_args x w);
}


let is_input_args_data w se = 
  exists (wx:spect_derive_context_input_args) 
         (wr:Seq.seq UInt8.t).
    validate_and_parse_postcond_some bundle_derive_context_input_args.b_spec.parser w wx wr /\
    se == map_opt wx.input_data spect_derive_context_input_args_data_left

fn parse_derive_context_input_args (s:Slice.slice UInt8.t) (#p:perm) (#w:erased _)
requires pts_to s #p w
returns e:(option (either engine_record l0_record) & bool)
ensures (
  match e with
  | _, false -> pts_to s #p w
  | e, _ -> 
    exists* se.
      is_record_opt e se (pts_to s #p w) **
      pure (is_input_args_data w se)
  )
{
  let res = validate_and_parse_derive_context_input_args s;
  match res {
    None -> {
      unfold validate_and_parse_post;
      (None, false)
    }
    Some xrem -> {
      let (x, rem) = xrem;
      unfold validate_and_parse_post;
      extract_derive_context_input_args x _;
      Trade.Util.elim_hyp_r _ _ _;
      is_record_opt_compose _ _ _ _;
      (map_opt x.input_data derive_context_input_args_data_left, true)
    }
  }
}



module CDDLTest.DPE.Common
module EqTest = CDDL.Spec.EqTest
open CDDLTest.Test
open Pulse.Lib
open Pulse.Lib.Pervasives
open CDDLTest.Destructors
#lang-pulse
open CDDL.Pulse.Parse.Base
open CDDL.Pulse.Types
open CDDL.Pulse.AST.Bundle
open CBOR.Spec.API.Type
open CDDL.Spec.Base

let tstr_any = 
  rel_either_left (rel_slice_of_table (mk_eq_test_bij spect_aux_env18_type_1_pretty_right
                    spect_aux_env18_type_1_pretty_left
                    spect_aux_env18_type_1_pretty_left_right
                    spect_aux_env18_type_1_pretty_right_left
                    (mk_eq_test_bij spect_evercddl_uint_pretty_right
                        spect_evercddl_uint_pretty_left
                        spect_evercddl_uint_pretty_left_right
                        spect_evercddl_uint_pretty_right_left
                        (EqTest.eqtype_eq UInt64.t)))
                rel_aux_env18_type_1
                rel_aux_env18_type_3)
            (rel_map_iterator CBOR.Pulse.API.Det.C.cbor_det_match
                CBOR.Pulse.API.Det.C.cbor_det_map_iterator_match
                aux_env18_type_1_pretty
                aux_env18_type_3_pretty
                (CDDL.Pulse.Iterator.Base.mk_spec rel_aux_env18_type_1)
                (CDDL.Pulse.Iterator.Base.mk_spec rel_aux_env18_type_3))


let bytes_of_evercddl_bytes (yy:Seq.seq UInt8.t) (ww:spect_evercddl_bytes_pretty) =
  yy == spect_evercddl_bstr_pretty_left (spect_evercddl_bytes_pretty_left ww)

fn extract_bytes x (y:erased _)
requires rel_evercddl_bytes x y
returns xx:Slice.slice UInt8.t
ensures 
  exists* p yy. 
    pts_to xx #p yy **
    Trade.trade (pts_to xx #p yy) (rel_evercddl_bytes x y) **
    pure (bytes_of_evercddl_bytes yy y)
{
  unfold (rel_evercddl_bytes x y);
  destruct_rel_fun _ _ _ _ _;
  with xx yy. unfold (rel_evercddl_bstr xx yy);
  destruct_rel_fun _ _ _ _ _;
  with (res:slice UInt8.t) (resy:_). assert (rel_slice_of_seq false res resy);
  rewrite each (rel_slice_of_seq false res resy) as (pts_to res.s #res.p resy ** pure (false == false));
  Trade.trade_compose _ _ (rel_fun rel_evercddl_bstr
          evercddl_bytes_pretty_left
          spect_evercddl_bytes_pretty_left
          x
          y);
  Trade.Util.elim_hyp_r _ _ _;
  res.s
}

fn destruct_evercddl_bytes_head 
    (x:evercddl_bytes_pretty)
    (w:erased _)
    (rest done res:slprop)
requires
  rel_evercddl_bytes x w **
  Trade.trade ((rel_evercddl_bytes x w ** rest) ** done) res
returns xx:Slice.slice UInt8.t
ensures
  exists* p ws. 
    pts_to xx #p ws **
    Trade.trade (rest ** (done ** pts_to xx #p ws)) res **
    pure (bytes_of_evercddl_bytes ws w)
{
  Trade.Util.assoc_hyp_r _ _ _ _;
  let xx = extract_bytes x w;
  Trade.Util.trans_hyp_l _ _ _ res;
  slprop_equivs();
  with perm ws. assert (pts_to xx #perm ws);
  with p. rewrite Trade.trade p res as Trade.trade (rest ** (done ** pts_to xx #perm ws)) res;
  xx
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

let is_slice_opt 
    (sl:option (Slice.slice UInt8.t))
    (dflt:slprop)
: slprop
= match sl with
  | None -> dflt
  | Some sl -> 
    exists* perm b. //relate uds to w?
      pts_to sl #perm b **
      Trade.trade (pts_to sl #perm b) dflt

let pretty_bytes (x:Seq.seq UInt8.t) =
  spect_evercddl_bytes_pretty_right (spect_evercddl_bstr_pretty_right x)

let pretty_slice (x:slice UInt8.t) =
  evercddl_bytes_pretty_right (evercddl_bstr_pretty_right x)

let of_bytes (#p:perm) (x:evercddl_bytes_pretty) (s:Slice.slice UInt8.t) =
  let x = evercddl_bstr_pretty_left (evercddl_bytes_pretty_left x) in
  x.s == s /\
  x.p == p

let of_bytes_option #p (x:option evercddl_bytes_pretty) (s:option (Slice.slice UInt8.t)) =
  match x, s with
  | None, None -> True
  | Some x, Some s -> of_bytes #p x s
  | _ -> False

fn mk_evercddl_bytes_pretty
    (x:Slice.slice UInt8.t)
    (#p #w:erased _)
requires
  pts_to x #p w
returns res:_
ensures
  rel_option rel_evercddl_bytes res (Some <| pretty_bytes w) **
  pure (of_bytes_option #p res (Some x))
{
  let res : slice UInt8.t = { s = x; p = p };
  rewrite (pts_to x #p w ** pure (false == false))
  as (rel_option rel_evercddl_bytes (Some <| pretty_slice res) (Some <| pretty_bytes w));
  Some (pretty_slice res)
}

fn mk_evercddl_bytes_pretty_none ()
requires emp
ensures
  rel_option rel_evercddl_bytes None None
{
  rewrite emp as rel_option rel_evercddl_bytes None None;
}

[@@pulse_unfold]
unfold
let my_unfold_l (#a:Type) (s:list string) (p:a) = norm [delta_only s; iota; primops] p

ghost
fn fold_l (s:list string) (p:slprop)
requires my_unfold_l s p
ensures p
{
  norm_spec [delta_only s; iota; primops] p;
  rewrite each (my_unfold_l s p) as p;
}

ghost
fn unfold_l (s:list string) (p:slprop)
requires p
ensures my_unfold_l s p
{
  norm_spec [delta_only s; iota; primops] p;
  rewrite each p as (my_unfold_l s p);
}

ghost
fn mk_rel_pair (#a0 #b0 #a1 #b1:Type0) (r0:rel a0 b0) (r1:rel a1 b1) (x0:a0) (#y0:b0) (x1:a1) (#y1:b1)
requires
  r0 x0 y0 ** r1 x1 y1
ensures
  rel_pair r0 r1 (x0, x1) (y0, y1)
{
  rewrite (r0 x0 y0 ** r1 x1 y1)
  as (rel_pair r0 r1 (x0, x1) (y0, y1));
}

ghost
fn fold_rel_option (#a #b:Type0) (r:rel a b) (x:a) (y:b)
requires
  r x y
ensures
  rel_option r (Some x) (Some y)
{
  rewrite (r x y) as (rel_option r (Some x) (Some y));
}

let norm_token = emp
ghost
fn intro_norm ()
requires emp
ensures norm_token
{
  fold norm_token;
}

ghost
fn force_norm ()
requires norm_token
ensures emp
{
  unfold norm_token;
}

ghost 
fn extract_bytes_ghost x (y:erased _)
requires rel_evercddl_bytes x y
returns xx:Slice.slice UInt8.t
ensures 
  exists* p yy. 
    pts_to xx #p yy **
    pure (bytes_of_evercddl_bytes yy y /\ of_bytes #p x xx)

{
  unfold_l [`%rel_fun; `%rel_evercddl_bytes; `%rel_evercddl_bstr; `%mk_rel; `%rel_slice_of_seq]
            (rel_evercddl_bytes x y);
  with (x:Slice.slice UInt8.t) #p y. assert pts_to x #p y;
  x
}


// // let pretty_bytes (x:Seq.seq UInt8.t) =
// //   spect_evercddl_bytes_pretty_right (spect_evercddl_bstr_pretty_right x)

// let pretty_slice (x:slice UInt8.t) =
//   evercddl_bytes_pretty_right (evercddl_bstr_pretty_right x)
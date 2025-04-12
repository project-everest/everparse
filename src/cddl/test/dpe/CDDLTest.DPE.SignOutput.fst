module CDDLTest.DPE.SignOutput
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

let pretty_bytes (x:Seq.seq UInt8.t) =
  spect_evercddl_bytes_pretty_right (spect_evercddl_bstr_pretty_right x)

let pretty_slice (x:slice UInt8.t) =
  evercddl_bytes_pretty_right (evercddl_bstr_pretty_right x)

let _ = rel_evercddl_signoutputargs


let struct_has_sig
    (hres:spect_evercddl_signoutputargs_pretty) 
    (sig :Seq.seq UInt8.t) =
  hres._x0 == Some (pretty_bytes sig) /\
  hres._x1 == None

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

ghost
fn fold_sign_output_args (x:_) (w:erased _)
requires
  rel_pair (rel_option rel_evercddl_bytes) (rel_option rel_evercddl_bytes)
          x w
ensures 
  rel_evercddl_signoutputargs
    (evercddl_signoutputargs_pretty_right x)
    (spect_evercddl_signoutputargs_pretty_right w)
{
  rewrite (rel_pair (rel_option rel_evercddl_bytes) (rel_option rel_evercddl_bytes)
                  x w)
  as (rel_evercddl_signoutputargs 
             (evercddl_signoutputargs_pretty_right x)
             (spect_evercddl_signoutputargs_pretty_right w));
}

let res_has_sig
    (res:evercddl_signoutputargs_pretty)
    (sig:Slice.slice UInt8.t) p =
  of_bytes_option #p res.intkey1 (Some sig) /\
  of_bytes_option #1.0R res.intkey2 None

fn prepare_sign_output
    (sign:Slice.slice UInt8.t)
    (#s:erased _) (#p:perm)
requires
    pts_to sign #p s
returns res:_
ensures
  exists* hres. 
    rel_evercddl_signoutputargs res hres **
    pure (struct_has_sig hres s /\
          res_has_sig res sign p)
{
  let pk = mk_evercddl_bytes_pretty sign;
  mk_evercddl_bytes_pretty_none ();
  mk_rel_pair (rel_option rel_evercddl_bytes)
              (rel_option rel_evercddl_bytes) _ None;
  fold_sign_output_args _ _;
  with res hres. assert (rel_evercddl_signoutputargs res hres);
  res
}
 
let is_serialized_sign_output hres w =
  exists sz.
    impl_serialize_post (coerce_spec bundle_signoutputargs
                .b_spec
              spect_evercddl_signoutputargs_pretty
              ())
          hres
          w
          sz

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
fn extract_bytes x (y:erased _)
requires rel_evercddl_bytes x y
returns xx:Slice.slice UInt8.t
ensures 
  exists* p yy. 
    pts_to xx #p yy **
    pure (bytes_of_evercddl_bytes yy y /\ of_bytes #p x xx)

{
  unfold_l [`%rel_fun; `%rel_evercddl_bytes; `%rel_evercddl_bstr; `%mk_rel; `%rel_slice_of_seq]
            (rel_evercddl_bytes x y);
  with (x:Slice.slice UInt8.t) #p y. assert S.pts_to x #p y;
  x
}

ghost
fn destruct_signoutputargs x hres sign p s
requires
    rel_evercddl_signoutputargs x hres **
    pure (of_bytes_option #p x.intkey1 (Some sign) /\
          of_bytes_option #1.0R x.intkey2 None /\
          struct_has_sig hres s)
ensures
    pts_to sign #p s
{
  rewrite (rel_evercddl_signoutputargs x hres) as
          (rel_evercddl_bytes (Some?.v x.intkey1) (Some?.v hres._x0) **
           emp);
  let xx = extract_bytes (Some?.v x.intkey1) _;
  rewrite each xx as sign;
  ()
}

let is_serialized_sig (out sig:Seq.seq UInt8.t) =
  exists hres.
    is_serialized_sign_output hres out /\
    struct_has_sig hres sig

fn write_certify_key_output_alt
    (out:Slice.slice UInt8.t)
    (sign:Slice.slice UInt8.t)
    (#s:erased _) (#p:perm)
requires
  exists* w.
    pts_to sign #p s **
    pts_to out w
returns res:bool
ensures
  exists* w.
    pts_to sign #p s **
    pts_to out w **
    pure (res ==> is_serialized_sig w s)
{
  let res = prepare_sign_output sign;
  let sz = serialize_signoutputargs' _ out;
  destruct_signoutputargs res _ sign p s;
  if (sz = 0sz) {
     false
  }
  else {
    true
  }
}

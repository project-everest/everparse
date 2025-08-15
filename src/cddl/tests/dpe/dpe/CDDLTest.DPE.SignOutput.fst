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

let struct_has_sig
    (hres:spect_evercddl_signoutputargs_pretty) 
    (sig :Seq.seq UInt8.t) =
  hres._x0 == Some (pretty_bytes sig) /\
  hres._x1 == None

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
  let xx = extract_bytes_ghost (Some?.v x.intkey1) _;
  rewrite each xx as sign;
  ()
}

let is_serialized_sig (out sig:Seq.seq UInt8.t) =
  exists hres.
    is_serialized_sign_output hres out /\
    struct_has_sig hres sig

fn write_sign_output
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

module CDDLTest.DPE.CertifyKeyOutput
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

let struct_has_pubkey_and_cert (hres:spect_evercddl_certifykeyoutputargs_pretty) (pk cert:Seq.seq UInt8.t) =
  hres._x0 == Some (pretty_bytes pk) /\
  hres._x1 == Some (pretty_bytes cert) /\
  hres._x2 == None

ghost
fn fold_certify_key_output_args (x:_) (w:erased _)
requires
  rel_pair (rel_pair (rel_option rel_evercddl_bytes) (rel_option rel_evercddl_bytes))
           (rel_option rel_evercddl_bytes)
          x w
ensures 
  rel_evercddl_certifykeyoutputargs 
    (evercddl_certifykeyoutputargs_pretty_right x)
    (spect_evercddl_certifykeyoutputargs_pretty_right w)
{
  rewrite (rel_pair (rel_pair (rel_option rel_evercddl_bytes) (rel_option rel_evercddl_bytes))
                    (rel_option rel_evercddl_bytes)
                  x w)
  as (rel_evercddl_certifykeyoutputargs 
             (evercddl_certifykeyoutputargs_pretty_right x)
             (spect_evercddl_certifykeyoutputargs_pretty_right w));
}

let res_has_pk_and_cert (res:evercddl_certifykeyoutputargs_pretty) (pk cert:Slice.slice UInt8.t) p q =
  of_bytes_option #p res.intkey1 (Some pk) /\
  of_bytes_option #q res.intkey2 (Some cert) /\
  of_bytes_option #q res.intkey3 None

fn prepare_certify_key_output
    (pubkey:Slice.slice UInt8.t)
    (cert:Slice.slice UInt8.t)
    (#pk #c:erased _) (#p #q:perm)
requires
    pts_to pubkey #p pk **
    pts_to cert #q c
returns res:_
ensures
  exists* hres. 
    rel_evercddl_certifykeyoutputargs res hres **
    pure (struct_has_pubkey_and_cert hres pk c /\ 
          res_has_pk_and_cert res pubkey cert p q)
{
  let pk = mk_evercddl_bytes_pretty pubkey;
  let cert = mk_evercddl_bytes_pretty cert;
  mk_rel_pair (rel_option rel_evercddl_bytes) (rel_option rel_evercddl_bytes) pk cert;
  mk_evercddl_bytes_pretty_none ();
  mk_rel_pair (rel_pair (rel_option rel_evercddl_bytes) (rel_option rel_evercddl_bytes)) (rel_option rel_evercddl_bytes) _ None;
  fold_certify_key_output_args _ _;
  with res hres. assert (rel_evercddl_certifykeyoutputargs res hres);
  res
}
 
let is_serialized_certify_key_output hres w =
  exists sz.
    impl_serialize_post (coerce_spec bundle_certifykeyoutputargs
                .b_spec
              spect_evercddl_certifykeyoutputargs_pretty
              ())
          hres
          w
          sz


ghost
fn destruct_certifykeyoutputargs x hres pubkey cert p q pk c
requires
    rel_evercddl_certifykeyoutputargs x hres **
    pure (of_bytes_option #p x.intkey1 (Some pubkey) /\
          of_bytes_option #q x.intkey2 (Some cert) /\
          of_bytes_option #q x.intkey3 None /\
          struct_has_pubkey_and_cert hres pk c)
ensures
    pts_to pubkey #p pk **
    pts_to cert #q c
{
  rewrite (rel_evercddl_certifykeyoutputargs x hres) as
          (rel_evercddl_bytes (Some?.v x.intkey1) (Some?.v hres._x0) **
           rel_evercddl_bytes (Some?.v x.intkey2) (Some?.v hres._x1) **
           emp);
  let xx = extract_bytes_ghost (Some?.v x.intkey1) _;
  let yy = extract_bytes_ghost (Some?.v x.intkey2) _;
  rewrite each xx as pubkey, yy as cert;
  ()
}

fn write_certify_key_output
    (out:Slice.slice UInt8.t)
    (pubkey:Slice.slice UInt8.t)
    (cert:Slice.slice UInt8.t)
    (#pk #c:erased _) (#p #q:perm)
requires
  exists* w.
    pts_to pubkey #p pk **
    pts_to cert #q c **
    pts_to out w
returns res:bool
ensures
  exists* w.
    pts_to pubkey #p pk **
    pts_to cert #q c **
    pts_to out w **
    pure (exists hres. res ==> 
          is_serialized_certify_key_output hres w /\
          struct_has_pubkey_and_cert hres pk c)
{
  let res = prepare_certify_key_output pubkey cert;
  let sz = serialize_certifykeyoutputargs' _ out;
  destruct_certifykeyoutputargs res _ pubkey cert p q pk c;
  if (sz = 0sz) {
     false
  }
  else {
    true
  }
}

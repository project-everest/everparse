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

let pretty_bytes (x:Seq.seq UInt8.t) =
  spect_evercddl_bytes_pretty_right (spect_evercddl_bstr_pretty_right x)

let _ = rel_evercddl_certifykeyoutputargs


let struct_has_pubkey_and_cert (hres:spect_evercddl_certifykeyoutputargs_pretty) (pk cert:Seq.seq UInt8.t) =
  hres._x0 == Some (pretty_bytes pk) /\
  hres._x1 == Some (pretty_bytes cert) /\
  hres._x2 == None

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
  admit()
}

fn mk_evercddl_bytes_pretty_none ()
requires emp
ensures
  rel_option rel_evercddl_bytes None None
{
  admit()
}

// ghost
// fn mk_rel_pair #a0 #b0 #a1 #b1 (r1:rel a0 b0) (r1:rel a1 b1)
// requires
//    r0 x0 y0 ** r1 x1 y1
// ensures

//     (x:Slice.slice UInt8.t)
//     (#p #w:erased _)
// requires
//   pts_to x #p w
// returns res:_
// ensures
//   rel_option rel_evercddl_bytes res (Some <| pretty_bytes w)
// {
//   admit()
// }


fn mk_tstr_any_empty ()
requires emp
returns res:_
ensures exists* w. tstr_any res w
{
  admit()
}

[@@pulse_unfold]
unfold
let my_unfold_l (#a:Type) (s:list string) (p:a) = norm [delta_only s; hnf; iota; primops] p

ghost
fn fold_l (s:list string) (p:slprop)
requires my_unfold_l s p
ensures p
{
  norm_spec [delta_only s; hnf; iota; primops] p;
  rewrite each (my_unfold_l s p) as p;
}

ghost
fn unfold_l (s:list string) (p:slprop)
requires p
ensures my_unfold_l s p
{
  norm_spec [delta_only s; hnf; iota; primops] p;
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

fn fold_certify_key_output_args (x:_) (w:erased _)
requires
  rel_pair (rel_pair (rel_option rel_evercddl_bytes) (rel_option rel_evercddl_bytes))
           (rel_option rel_evercddl_bytes)
          x w
returns res:_
ensures exists* (hres:spect_evercddl_certifykeyoutputargs_pretty).
      rel_evercddl_certifykeyoutputargs res hres **
      pure (hres._x0 == (fst (fst w)) /\
            hres._x1 == (snd (fst w)) /\
            hres._x2 == snd w /\
            res.intkey1 ==  (fst (fst x)) /\
            res.intkey2 ==  (snd (fst x)) /\
            res.intkey3 == None)
{
  admit()
}

let res_has_pk_and_cert (res:evercddl_certifykeyoutputargs_pretty) (pk cert:Slice.slice UInt8.t) p q =
  of_bytes_option #p res.intkey1 (Some pk) /\
  of_bytes_option #q res.intkey2 (Some cert) /\
  of_bytes_option #q res.intkey3 None

fn write_certify_key_output
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
  let res = fold_certify_key_output_args _ _;
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

fn write_certify_key_output_main
    (out:Slice.slice UInt8.t)
    (pubkey:Slice.slice UInt8.t)
    (cert:Slice.slice UInt8.t)
    (#pk #c:erased _) (#p #q:perm)
requires
  exists* w.
    pts_to pubkey #p pk **
    pts_to cert #q c **
    pts_to out w
returns res:(_ & bool)
ensures
  exists* hres w.
    rel_evercddl_certifykeyoutputargs (fst res) hres **
    pts_to out w **
    pure (struct_has_pubkey_and_cert hres pk c /\
          res_has_pk_and_cert (fst res) pubkey cert p q) **
    pure (snd res ==>  is_serialized_certify_key_output hres w)
{
  let res = write_certify_key_output pubkey cert;
  let sz = serialize_certifykeyoutputargs' _ out;
  if (sz = 0sz) {
    (res, false)
  }
  else {
    (res, true)
  }
}

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
  slprop_equivs();
  unfold (rel_evercddl_certifykeyoutputargs x hres);
  destruct_rel_fun _ _ _ _ _;
  drop_ (Trade.trade _ _);
  destruct_pair _ _ ((evercddl_certifykeyoutputargs_pretty_left x)) _ ();
  drop_ (Trade.trade _ _);
  destruct_pair (rel_option rel_evercddl_bytes) (rel_option rel_evercddl_bytes) (fst (evercddl_certifykeyoutputargs_pretty_left x)) (fst (spect_evercddl_certifykeyoutputargs_pretty_left hres)) ();
  show_proof_state;
}

fn write_certify_key_output_alt
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
  let res = write_certify_key_output pubkey cert;
  let sz = serialize_certifykeyoutputargs' _ out;
  destruct_certifykeyoutputargs res _ pubkey cert p q pk c;
  if (sz = 0sz) {
     false
  }
  else {
    true
  }
}

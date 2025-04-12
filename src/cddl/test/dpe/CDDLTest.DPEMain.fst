module CDDLTest.DPEMain
open Pulse.Lib
open Pulse.Lib.Pervasives
// open DPETypes
// open EngineTypes
// open EngineCore
// open L0Types
// open L0Core

module G = FStar.Ghost
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
#lang-pulse

module I = CDDLTest.DPE.InitializeContextInput
// module DC = CDDLTest.DPE.DeriveContextInput
// module SI = CDDLTest.DPE.SignInput
module CK = CDDLTest.DPE.CertifyKeyInput
open CDDL.Pulse.Types
open FStar.Seq
open DPESlice
module U8 = FStar.UInt8
module D = CDDLTest.Destructors

let norm_token = emp

ghost
fn intro_norm ()
requires emp
ensures norm_token
{ fold norm_token; () }


ghost
fn force_norm ()
requires norm_token
ensures emp
{ unfold norm_token; () }

fn initialize_context
  (#sid:sid_t)
  (#t:G.erased trace { trace_valid_for_initialize_context t })
  (#p:perm)
  (#w:erased _)
  (input:Slice.slice U8.t)
requires 
  pts_to input #p w **
  sid_pts_to trace_ref sid t
returns ok:bool
ensures (
  if ok 
  then (
    exists* (uds:seq U8.t).
      initialize_context_client_perm sid uds **
      pts_to input #p w **
      pure (I.is_uds_bytes uds w)
  )
  else (
    pts_to input #p w **
    sid_pts_to trace_ref sid t
  )  
)
{ 
  let uds_opt = I.parse_initialize_context_input_args input;
  match uds_opt {
    None -> {
      unfold (I.parsed_initialize_context_input);
      false
    }
    Some uds_slice -> {
      unfold (I.parsed_initialize_context_input);
      if (Slice.len uds_slice <> EngineTypes.uds_len)
      {
        Trade.elim_trade _ _;
        false
      }
      else
      {
        DPESlice.initialize_context sid t uds_slice;
        Trade.elim_trade _ _;
        true
      }
    }
  }
}

module CKO = CDDLTest.DPE.CertifyKeyOutput

assume
val max_cert_len : SZ.t

fn certify_key
    (sid:sid_t)
    (out:Slice.slice U8.t)
    (#t:G.erased trace { trace_valid_for_certify_key t })
requires sid_pts_to trace_ref sid t
requires exists* w. pts_to out w
returns ok:bool
ensures certify_key_client_perm sid t
ensures exists* w.
    pts_to out w **
    pure (ok ==> (exists pk cert hres.
          CKO.is_serialized_certify_key_output hres w /\
          CKO.struct_has_pubkey_and_cert hres pk cert))
{
  let mut pk_out = [| 0uy; 32sz |];
  let mut cert_out = [| 0uy; max_cert_len |];
  let pk_out_slice = Slice.from_array pk_out 32sz;
  let cert_out_slice = Slice.from_array cert_out max_cert_len;
  Slice.pts_to_len pk_out_slice;
  Slice.pts_to_len cert_out_slice;
  let _ = DPESlice.certify_key sid pk_out_slice cert_out_slice t;
  let ok = CKO.write_certify_key_output_alt out pk_out_slice cert_out_slice;
  Slice.to_array pk_out_slice;
  Slice.to_array cert_out_slice;
  ok
}

module CDDLTest.DPEMain
open Pulse.Lib
open Pulse.Lib.Pervasives
// open DPETypes
// open EngineTypes
// open EngineCore
// open L0Types
// open L0Core

module G = FStar.Ghost
// module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
// module PM = Pulse.Lib.PCMMap
// module FP = Pulse.Lib.PCM.FractionalPreorder
// module A = Pulse.Lib.Array
// module PHT = Pulse.Lib.HashTable.Spec
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

// noextract
// let trace_valid_for_derive_child (t:trace)  : prop =
//   match current_state t, r with
//   | G_Available (Engine_context_repr _)
//   | G_Available (L0_context_repr _) -> True
//   | _ -> False

// fn derive_child
//   (#sid:sid_t)
//   (#t:G.erased trace { trace_valid_for_derive_child t })
//   (#p:perm)
//   (input:slice U8.t)
// requires
//   pts_to input #p w **
//   sid_pts_to trace_ref sid t
// returns ok:bool
// ensures
//   cond ok
//   (
//     derive_child_client_perm sid t rrepr b
//   )
//   (
//     pts_to input #p w **
//     sid_pts_to trace_ref sid t
//   )
//         (ensures fun b ->
//            derive_child_client_perm sid t rrepr b)

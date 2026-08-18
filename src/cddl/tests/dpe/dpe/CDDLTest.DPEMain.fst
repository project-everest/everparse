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
module DC = CDDLTest.DPE.DeriveContextInput
module CKO = CDDLTest.DPE.CertifyKeyOutput
module SI = CDDLTest.DPE.SignInput
module SO = CDDLTest.DPE.SignOutput
open CDDL.Pulse.Types
open FStar.Seq
open DPESlice
module U8 = FStar.UInt8
module D = CDDLTest.Destructors

(*
assume
val max_cert_len : SZ.t
*)
inline_for_extraction let max_cert_len : SZ.t = 1024sz // for extraction purposes

assume
val size_t_fits_in_u32 (z:SZ.t)
: Lemma (SZ.v z < pow2 32)


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

type derive_context_result =
  | Input_parsing_failure
  | Missing_arguments
  | Incorrect_state
  | Session_error
  | Success

[@@pulse_unfold]
let derive_context_post 
  (sid:sid_t)
  (t:G.erased trace { trace_valid_for_derive_context t })
  (p:perm)
  (w:erased _)
  (input:Slice.slice U8.t)
  (res:derive_context_result)
: slprop
= match res with
  | Input_parsing_failure ->
    sid_pts_to trace_ref sid t
  | Missing_arguments -> 
    sid_pts_to trace_ref sid t **
    pure (DC.is_input_args_data w None)
  | Incorrect_state ->
    sid_pts_to trace_ref sid t **
    pure (exists (spec_record:DPESlice.spec_record_t).
              {:pattern (DC.is_input_args_data w (Some spec_record))}
            DC.is_input_args_data w (Some spec_record) /\
            ~(trace_and_record_valid_for_derive_context t spec_record))
  | _ -> 
    exists* (spec_record:DPESlice.spec_record_t).
        pure (DC.is_input_args_data w (Some spec_record) /\
              trace_and_record_valid_for_derive_context t spec_record) **
        derive_context_client_perm sid t spec_record (Success? res)

ghost
fn take_record_perm 
  (record:record_t)
  (spec:spec_record_t)
  (k:slprop)
requires DC.is_derive_context_input_args_data record spec k
ensures record_perm record spec ** Trade.trade (record_perm record spec) k
{ 
  DC.is_dci_cases _ _ _;
  match record {
    Inl eng -> {
      let Inl spec_l = spec;
      unfold DC.is_derive_context_input_args_data;
      assert (DC.is_engine_record_core eng spec_l);
      rewrite 
        each (DC.is_engine_record_core eng spec_l)
           as (record_perm record spec);
    }
    Inr l0 -> {
      let Inr spec_r = spec;
      unfold DC.is_derive_context_input_args_data;
      assert (DC.is_l0_record_core l0 spec_r);
      rewrite 
        each (DC.is_l0_record_core l0 spec_r)
           as (record_perm record spec);
    }
  }
}

fn derive_context_aux
  (sid:sid_t)
  (#t:G.erased trace)
  (#p:perm)
  (#w:erased _)
  (input:Slice.slice U8.t)
  (record:record_t)
  (#spec:erased spec_record_t { trace_and_record_valid_for_derive_context t spec })
requires
  DC.is_derive_context_input_args_data record spec (pts_to input #p w) **
  sid_pts_to trace_ref sid t **
  pure (DC.is_input_args_data w (Some #spec_record_t spec))
returns res:derive_context_result
ensures pts_to input #p w
ensures derive_context_post sid t p w input res
{
  take_record_perm _ _ _;
  let res = derive_context sid t record;
  Trade.elim_trade _ _;
  match res {
    true -> { Success }
    false -> { Session_error }
  }
}

#push-options "--z3rlimit 32"

fn derive_context
  (sid:sid_t)
  (#t:G.erased trace { trace_valid_for_derive_context t })
  (#p:perm)
  (#w:erased _)
  (input:Slice.slice U8.t)
requires
  pts_to input #p w **
  sid_pts_to trace_ref sid t
returns res:derive_context_result
ensures pts_to input #p w
ensures derive_context_post sid t p w input res
{
  let record_opt, ok = DC.parse_derive_context_input_args input;
  match ok {
    false -> {
      Input_parsing_failure
    }

    true -> {
      DC.is_record_opt_cases _ _ _;
      match record_opt {
        None -> {
          DC.elim_is_record_opt_none _ _;
          Missing_arguments
        }

        Some record -> {
          DC.elim_is_record_opt_some _ _ _;
          DC.is_dci_cases _ _ _;
          let is_l0 = check_state_l0 sid;
          if is_l0
          {
            match record {
              Inl _ -> {
                DC.claim_is_dci _ _ _;
                Incorrect_state
              }

              Inr l0 -> {
                derive_context_aux sid #t #p #w input (Inr l0);
              }
            }
          }
          else
          {
            match record {
              Inl eng -> {
                derive_context_aux sid #t #p #w input (Inl eng)
              }

              Inr l0 -> {
                DC.claim_is_dci _ _ _;
                Incorrect_state
              }
            }
          }
        }
      }
    }
  }
}

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
  let ok = CKO.write_certify_key_output out pk_out_slice cert_out_slice;
  Slice.to_array pk_out_slice;
  Slice.to_array cert_out_slice;
  ok
}


type sign_result =
  | Parse_failed
  | Sig_failed
  | Sig_success

fn sign
    (sid:sid_t)
    (input:Slice.slice U8.t)
    (out:Slice.slice U8.t)
    (#t:G.erased trace { trace_valid_for_sign t })
    (#p:perm)
    (#w wout:erased _)
requires
  sid_pts_to trace_ref sid t **
  pts_to input #p w **
  pts_to out wout
returns ok:sign_result
ensures (
  match ok with
  | Parse_failed -> 
    sid_pts_to trace_ref sid t **
    pts_to input #p w **
    pts_to out wout **
    pure (SI.parse_failed w)

  | Sig_failed -> (
    exists* wout.
      certify_key_client_perm sid t **
      pts_to input #p w **
      pts_to out wout **
      pure (exists tbs_bytes. SI.is_tbs_bytes tbs_bytes w)
  )

  | Sig_success -> (
    exists* (out_bytes:_).
      certify_key_client_perm sid t **
      pts_to input #p w **
      pts_to out out_bytes **
      pure (exists sig tbs_bytes.
        SI.is_tbs_bytes tbs_bytes w /\
        is_signature sig tbs_bytes /\
        SO.is_serialized_sig out_bytes sig
      )
  )
)
{
  let tbs_opt = SI.parse_sign_input_args input;
  match tbs_opt {
    None -> {
      Parse_failed
    }
    Some tbs_slice -> {
      let mut sign_out = [| 0uy; 64sz |];
      let sign_out_slice = Slice.from_array sign_out 64sz;
      Slice.pts_to_len sign_out_slice;
      size_t_fits_in_u32 (Slice.len tbs_slice);
      sign sid sign_out_slice tbs_slice t;
      let ok = SO.write_sign_output out sign_out_slice;
      Slice.to_array sign_out_slice;
      Trade.elim_trade _ _;
      if ok { Sig_success } else { Sig_failed }
    }
  }
}

#pop-options

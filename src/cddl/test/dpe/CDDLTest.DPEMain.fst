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

let trace_valid_for_derive_context (t:trace) : prop =
  match current_state t with
  | G_Available (Engine_context_spec _)
  | G_Available (L0_context_spec _) -> True
  | _ -> False

type derive_context_result =
  | Input_parsing_failure
  | Missing_arguments
  | Incorrect_state
  | Session_error
  | Success

ghost
fn is_record_opt_cases e s k
requires DC.is_record_opt e s k
ensures  DC.is_record_opt e s k ** pure (Some? e <==> Some? s)
{
  admit()
}

ghost
fn elim_is_record_opt_none (s:option spec_record_t) k
requires DC.is_record_opt None s k
ensures pure (s == None) ** k
{
  admit()
}

ghost
fn elim_is_record_opt_some (r:record_t) (s:option spec_record_t) k
requires DC.is_record_opt (Some r) s k
returns _:squash (Some? s)
ensures DC.is_derive_context_input_args_data r (Some?.v s) k
{
  admit()
}


ghost
fn claim_is_record_opt (e:option record_t) (s:option spec_record_t) k
requires DC.is_record_opt e s k
ensures k
{
  admit()
}

ghost
fn claim_is_dci (e:record_t) (s:spec_record_t) k
requires DC.is_derive_context_input_args_data e s k
ensures k
{
  admit()
}

ghost
fn is_dci_cases
    (e:record_t)
    (res:spec_record_t)
    (k:slprop)
requires DC.is_derive_context_input_args_data e res k
ensures DC.is_derive_context_input_args_data e res k **
        pure (Inl? e <==> Inl? res)
{
  admit()
}

let current_state_is_l0 (t:trace {trace_valid_for_derive_context t}) : prop =
  match current_state t with
  | G_Available (L0_context_spec _) -> True
  | G_Available (Engine_context_spec _) -> False

fn check_state_l0
  (sid:sid_t)
  (#t:G.erased trace { trace_valid_for_derive_context t })
requires
  sid_pts_to trace_ref sid t
returns ok:bool
ensures
  sid_pts_to trace_ref sid t
ensures pure (ok <==> current_state_is_l0 t)
{
  admit()
}

let trace_and_record_invalid_engine
    (t:trace {trace_valid_for_derive_context t})
    (e:spec_record_t)
: Lemma 
  (requires current_state_is_l0 t /\ Inl? e)
  (ensures ~(trace_and_record_valid_for_derive_child t e))
= ()

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
            ~(trace_and_record_valid_for_derive_child t spec_record))
  | _ -> 
    exists* (spec_record:DPESlice.spec_record_t).
        pure (DC.is_input_args_data w (Some spec_record) /\
              trace_and_record_valid_for_derive_child t spec_record) **
        derive_child_client_perm sid t spec_record (Success? res)

#push-options "--query_stats"

ghost
fn take_record_perm 
  (record:record_t)
  (spec:spec_record_t)
  (k:slprop)
requires DC.is_derive_context_input_args_data record spec k
ensures record_perm record spec ** Trade.trade (record_perm record spec) k
{ 
  admit() //  Trade.Util.rewrite_with_trade k (record_perm record spec);
}

fn derive_context_aux
  (sid:sid_t)
  (#t:G.erased trace)
  (#p:perm)
  (#w:erased _)
  (input:Slice.slice U8.t)
  (record:record_t)
  (#spec:erased spec_record_t { trace_and_record_valid_for_derive_child t spec })
requires
  DC.is_derive_context_input_args_data record spec (pts_to input #p w) **
  sid_pts_to trace_ref sid t **
  pure (DC.is_input_args_data w (Some #spec_record_t spec))
returns res:derive_context_result
ensures pts_to input #p w
ensures derive_context_post sid t p w input res
{
  take_record_perm _ _ _;
  let res = derive_child sid t record;
  Trade.elim_trade _ _;
  match res {
    true -> { Success }
    false -> { Session_error }
  }
}

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
      is_record_opt_cases _ _ _;
      match record_opt {
        None -> {
          elim_is_record_opt_none _ _;
          Missing_arguments
        }

        Some record -> {
          elim_is_record_opt_some _ _ _;
          is_dci_cases _ _ _;
          let is_l0 = check_state_l0 sid;
          if is_l0
          {
            match record {
              Inl _ -> {
                claim_is_dci _ _ _;
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
                claim_is_dci _ _ _;
                Incorrect_state
              }
            }
          }
        }
      }
    }
  }
}

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

(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module DPESlice
open Pulse.Lib.Pervasives
open DPETypes
open EngineTypes
open EngineCore
open L0Types
open L0Core
#lang-pulse
module G = FStar.Ghost
module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module PM = Pulse.Lib.PCM.Map
module FP = Pulse.Lib.PCM.FractionalPreorder
module Slice = Pulse.Lib.Slice
module PHT = Pulse.Lib.HashTable.Spec

open PulseCore.Preorder
open Pulse.Lib.OnRange
open Pulse.Lib.HashTable.Type
open Pulse.Lib.HashTable

type sid_t : eqtype = U16.t

//
// A session may be in one of the following states
//
// InUse is never returned to the client
//
[@@ Rust_derive "Clone"]
noeq
type session_state =
  | SessionStart
  | Available { context:context_t }
  | InUse
  | SessionClosed
  | SessionError

type ht_t = ht_t sid_t session_state

//
// DPE state
// A counter for next sid
//   and a hashtable mapping sids to session state
//
noeq
type st = { st_ctr:sid_t; st_tbl:ht_t; }

//
// Ghost state set up
//

module DK = CDDLTest.DPE.DeriveContextInput
let record_t = either DK.engine_record DK.l0_record
let spec_record_t = either DK.spec_engine_record DK.spec_l0_record

val cdi_functional_correctness : c0:Seq.seq U8.t -> uds_bytes:Seq.seq U8.t -> repr:DK.spec_engine_record -> prop
val l0_is_authentic : repr:DK.spec_engine_record -> prop

val l0_context_spec_t : Type u#0
val engine_record_of_l0_context (r:l0_context_spec_t) : GTot DK.spec_engine_record
val uds_of_l0 (r:l0_context_spec_t) : GTot (Seq.seq U8.t)
val cdi_of_l0 (r:l0_context_spec_t) : GTot (Seq.seq U8.t)

val l1_context_spec_t : Type u#0
val l0_record_of_l1_context (r:l1_context_spec_t) : GTot DK.spec_l0_record
val cdi_of_l1 (r:l1_context_spec_t) : GTot (Seq.seq U8.t)

noeq
type spec_context_t = 
  | Engine_context_spec : uds:Seq.seq U8.t -> spec_context_t
  | L0_context_spec     : r:l0_context_spec_t -> spec_context_t
  | L1_context_spec     : r:l1_context_spec_t -> spec_context_t

//
// Ghost session state
//
// Has a 1-1 correspondence with the concrete session state
//   except it has an G_UnInitialized
//
[@@ erasable]
noeq
type g_session_state : Type u#1 =
  | G_UnInitialized : g_session_state
  | G_SessionStart : g_session_state
  | G_Available : repr:spec_context_t -> g_session_state
  | G_InUse : g_session_state -> g_session_state
  | G_SessionClosed : g_session_state -> g_session_state
  | G_SessionError : g_session_state -> g_session_state

//
// A relation between context reprs that follow each other
//
// L0 repr should use the same UDS as the engine repr,
//   and L1 repr should use the same CDI as the L0 repr
//
noextract
let next_spec (r1 r2:spec_context_t) : prop =
  match r1, r2 with
  | Engine_context_spec uds, L0_context_spec l0_repr ->
    uds == uds_of_l0 l0_repr
  | L0_context_spec l0_repr, L1_context_spec l1_repr ->
    cdi_of_l0 l0_repr == cdi_of_l1 l1_repr
  | _ -> False

//
// State machine
//
noextract
let rec next (s0 s1:g_session_state) : prop =
  match s0, s1 with
  //
  // UnInitialized may only go to SessionStart
  // No other incoming/outgoing edges to/from it
  //
  | G_UnInitialized, G_SessionStart -> True
  | G_UnInitialized, _
  | _, G_UnInitialized -> False

  //
  // SessionStart may go to Available with engine repr
  //
  | G_SessionStart, G_Available (Engine_context_spec _) -> True

  //
  // Available r0 may go to Available r1,
  //   as long as repr r1 follows repr r0
  //
  | G_Available r0, G_Available r1 ->
    next_spec r0 r1 \/
    (L1_context_spec? r0 /\ r0 == r1)

  //
  // SessionClosed is a terminal state
  //
  | G_SessionClosed _, _ -> False

  //
  // From any state we can go to InUse, SessionClosed, or SessionError
  //
  // These states capture the previous state
  //
  | _, G_InUse s -> s == s0
  | _, G_SessionClosed s
  | _, G_SessionError s -> s == s0

  //
  // From InUse s we can go to s1, as long as s can go to s1
  //
  | G_InUse s, s1 -> next s s1

  | _ -> False


//
// Defining traces
//

noextract
let rec well_formed_trace (l:list g_session_state) : prop =
  match l with
  | []
  | [G_SessionStart] -> True
  | s1::s0::tl -> next s0 s1 /\ well_formed_trace (s0::tl)
  | _ -> False

noextract
type trace_elt : Type u#1 = l:list g_session_state { well_formed_trace l }

noextract
let trace_extension (t0 t1:trace_elt) : prop =
  Cons? t1 /\ t0 == List.Tot.tail t1

noextract
let trace_preorder : FStar.Preorder.preorder trace_elt =
  FStar.ReflexiveTransitiveClosure.closure trace_extension

noextract
type trace = hist trace_preorder

noextract
type trace_pcm_t : Type u#1 = FP.pcm_carrier trace_preorder

//
// Trace PCM is fractional preorder PCM,
//   with trace preorder
//
noextract
let trace_pcm : FStar.PCM.pcm trace_pcm_t = FP.fp_pcm trace_preorder

//
// Current state of a trace
//
// We use UnInitialized as the current state of empty trace
//
noextract
let current_state (t:trace) : g_session_state =
  match t with
  | [] -> G_UnInitialized
  | hd::_ ->
    match hd with
    | [] -> G_UnInitialized
    | s::_ -> s

//
// Given a trace t, valid_transition t s means that
//   current state of t may go to s in the state machine
//
noextract
let valid_transition (t:trace) (s:g_session_state) : prop =
  next (current_state t) s

//
// The next trace after a transition
//
noextract
let next_trace (t:trace) (s:g_session_state { valid_transition t s }) : trace =
  match t with
  | [] -> [[s]]
  | hd::tl ->
    match hd with
    | [] -> [s]::t
    | l -> (s::l)::t

val dpe_pcm_carrier_t : Type u#1
val dpe_pcm : PCM.pcm dpe_pcm_carrier_t
let dpe_ghost_state = ghost_pcm_ref dpe_pcm
val sid_pts_to (r:dpe_ghost_state) (sid:sid_t) (t:trace) : slprop
val trace_ref : dpe_ghost_state

//
// The DPE API
//

let open_session_client_perm (s:option sid_t) : slprop =
  match s with
  | None -> emp
  | Some s ->
    exists* t. sid_pts_to trace_ref s t ** pure (current_state t == G_SessionStart)

val open_session ()
  : stt (option sid_t)
        (requires emp)
        (ensures fun r -> open_session_client_perm r)

noextract
let trace_valid_for_initialize_context (t:trace) : prop =
  current_state t == G_SessionStart

let initialize_context_client_perm (sid:sid_t) (uds:Seq.seq U8.t) =
  exists* t. sid_pts_to trace_ref sid t **
             pure (current_state t == G_Available (Engine_context_spec uds))

val initialize_context (sid:sid_t) 
  (t:G.erased trace { trace_valid_for_initialize_context t })
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  (uds:Slice.slice U8.t { Slice.len uds == uds_len })
  : stt unit
        (requires
           pts_to uds #p uds_bytes **
           sid_pts_to trace_ref sid t)
        (ensures fun b ->
           pts_to uds #p uds_bytes **
           initialize_context_client_perm sid uds_bytes)

let record_perm (record:record_t) (spec:spec_record_t)  : slprop = 
  match record, spec with
  | Inl er, Inl s_er -> DK.is_engine_record_core er s_er
  | Inr l0, Inr s_l0 -> DK.is_l0_record_core l0 s_l0
  | _ -> pure False

let trace_valid_for_derive_context (t:trace) : prop =
  match current_state t with
  | G_Available (Engine_context_spec _)
  | G_Available (L0_context_spec _) -> True
  | _ -> False

let trace_and_record_valid_for_derive_context (t:trace) (r:spec_record_t) : prop =
  match current_state t, r with
  | G_Available (Engine_context_spec _), Inl _
  | G_Available (L0_context_spec _), Inr _ -> True
  | _ -> False

let derive_context_post_trace (r:spec_record_t) (t:trace) =
  match r, current_state t with
  | Inl r, G_Available (L0_context_spec l0_ctxt) ->
    r == engine_record_of_l0_context l0_ctxt
  | Inr r, G_Available (L1_context_spec l1_ctxt) ->
    r == l0_record_of_l1_context l1_ctxt
  | _ -> False

let derive_context_client_perm (sid:sid_t) (t0:trace) (repr:spec_record_t) (res:bool)
  : slprop =
  match res with
  | false ->
    exists* t1. sid_pts_to trace_ref sid t1 **
                pure (current_state t1 == G_SessionError (G_InUse (current_state t0)))
  | true ->
    exists* t1. sid_pts_to trace_ref sid t1 **
                pure (derive_context_post_trace repr t1)

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


val derive_context (sid:sid_t)
  (t:G.erased trace)
  (record:record_t)
  (#rrepr:erased spec_record_t { trace_valid_for_derive_context t })
  : stt bool
    (requires
      record_perm record rrepr **
      sid_pts_to trace_ref sid t)
    (ensures fun b ->
      record_perm record rrepr **
      derive_context_client_perm sid t rrepr b)


noextract
let trace_valid_for_certify_key (t:trace) : prop =
  match current_state t with
  | G_Available (L1_context_spec _) -> True
  | _ -> False

let certify_key_client_perm (sid:sid_t) (t0:trace) : slprop =
  exists* t1. sid_pts_to trace_ref sid t1 **
              pure (current_state t1 == current_state t0)

val certify_key (sid:sid_t)
  (pub_key:Slice.slice U8.t { Slice.len pub_key == 32sz })
  (crt:Slice.slice U8.t)
  (t:G.erased trace { trace_valid_for_certify_key t })
  : stt U32.t
        (requires
           sid_pts_to trace_ref sid t **
           (exists* pub_key_repr crt_repr.
              pts_to pub_key pub_key_repr **
              pts_to crt crt_repr))
        (ensures fun _ ->
           certify_key_client_perm sid t **
           (exists* pub_key_repr crt_repr.
              pts_to pub_key pub_key_repr **
              pts_to crt crt_repr))

noextract
let trace_valid_for_sign (t:trace) : prop =
  match current_state t with
  | G_Available (L1_context_spec _) -> True
  | _ -> False

let sign_client_perm (sid:sid_t) (t0:trace) : slprop =
  exists* t1. sid_pts_to trace_ref sid t1 **
              pure (current_state t1 == current_state t0)

val is_signature (sign tbs:Seq.seq UInt8.t) : prop

fn sign 
  (sid:sid_t)
  (signature:Slice.slice U8.t { Slice.len signature == 64sz })
  (msg:Slice.slice U8.t { SZ.v <| Slice.len msg < pow2 32 })
  (t:G.erased trace { trace_valid_for_sign t })
  (#tbs:erased (Seq.seq U8.t))
  (#p:perm)
requires 
  sid_pts_to trace_ref sid t **
  pts_to msg #p tbs **
  (exists* w. pts_to signature w)
ensures 
  exists* sign. 
    certify_key_client_perm sid t **
    pts_to msg #p tbs **
    pts_to signature sign **
    pure (is_signature sign tbs)

noextract
let trace_valid_for_close (t:trace) : prop =
  match current_state t with
  | G_UnInitialized
  | G_SessionClosed _
  | G_InUse _ -> False
  | _ -> True

let session_closed_client_perm (sid:sid_t) (t0:trace) =
  exists* t1. sid_pts_to trace_ref sid t1 **
              pure (current_state t1 == G_SessionClosed (G_InUse (current_state t0)))

val close_session
  (sid:sid_t)
  (t:G.erased trace { trace_valid_for_close t })
  : stt unit
        (requires
           sid_pts_to trace_ref sid t)
        (ensures fun m ->
           session_closed_client_perm sid t)

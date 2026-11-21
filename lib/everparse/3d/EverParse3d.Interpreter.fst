(*
   Copyright 2021 Microsoft Research

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
module EverParse3d.Interpreter
#lang-pulse

(* This is the Pulse interpreter for the 3d combinator language.

   It defines a strongly typed abstract syntax for an intermediate
   representation of 3D programs, the type `typ`, together with a threefold
   denotation:

     1. `as_type` interprets a `typ` as an F* type;
     2. `as_parser` interprets a `t:typ` as a parser of values of the type
        denotation of `t`;
     3. `as_validator` interprets a `t:typ` as a Pulse validator corresponding
        to the parser denotation of `t`, and functionally correct with respect
        to the spec denotation of `t`, `as_vspec`, which specifies the effect
        of the actions of `t` on the action state (see
        `EverParse3d.Actions.Spec`).

   Partially evaluating `as_validator` at a concrete `t` yields an EverParse
   validator specialized to `t`, which Custard extracts to C (an instance of
   the 1st Futamura projection).

   Differences with the Low* interpreter:

   - Memory locations and invariants are gone. The Low* triple of indices
     (`inv_index`, `disj_index`, `loc_index`) is replaced with a single
     `state_dict` `d`, which is *uniform* over the whole `typ`/`dtyp`/`action`
     tree rather than computed by joins at every node. `forevery_state` is a
     separating conjunction, so a join would carry a key-disjointness side
     condition at every node; keeping `d` uniform pushes all weakening to the
     action leaves, where `A.action_weaken` discharges the obligation by
     normalization over literal string keys. No SMT reasoning about memory
     disjointness is involved anywhere.

   - `Action_probe_then_validate` is not a constructor of `atomic_action`.
     Storing the (necessarily different) `state_dict` of the probed type inside
     the AST would raise its universe. Instead, probe-then-validate is built by
     the top-level smart constructor `t_probe_then_validate` and injected with
     `Action_call`. This is also where the copy buffer shows up as its own
     keyed `state_dict` entry, disjoint from the state of the probed type: that
     is exactly what forbids a nested probe from reusing the same copy buffer.

   - There is no backend flag. Following the type class discipline, the
     backend-specific operations (`field_ptr`, `field_ptr_after`, ...) are
     passed as `option` arguments, and the corresponding constructors take a
     `squash (Some? ...)`.

   - The error handler macro is a parameter of the denotations, since the
     Pulse combinators take it as an argument rather than linking against a
     per-backend module.
*)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module A = EverParse3d.Actions.Base
module S = EverParse3d.Actions.Spec
module VS = EverParse3d.Actions.ValueSpec
module E = EverParse3d.ErrorCode
module P = EverParse3d.Prelude
module T = FStar.Tactics
module I = EverParse3d.InputStream.Base
module CP = EverParse3d.CopyBuffer
module PA = EverParse3d.ProbeActions
module Bool = EverParse3d.Boolean
open Pulse.Lib.Pervasives
open EverParse3d.State
open EverParse3d.Actions.Common
open FStar.List.Tot

(* An attribute to control partial evaluation *)
let specialize = ()


////////////////////////////////////////////////////////////////////////////////
// Primitive types
////////////////////////////////////////////////////////////////////////////////

type itype =
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | UInt8BE
  | UInt16BE
  | UInt32BE
  | UInt64BE
  | Unit
  | AllBytes
  | AllZeros

let pointer_size_t = i:itype { i == UInt32 \/ i == UInt64 }

[@@specialize]
let itype_as_type (i:itype)
  : Type
  = match i with
    | UInt8 -> P.___UINT8
    | UInt16 -> P.___UINT16
    | UInt32 -> P.___UINT32
    | UInt64 -> P.___UINT64
    | UInt8BE -> P.___UINT8BE
    | UInt16BE -> P.___UINT16BE
    | UInt32BE -> P.___UINT32BE
    | UInt64BE -> P.___UINT64BE
    | Unit -> unit
    | AllBytes -> P.all_bytes
    | AllZeros -> P.all_zeros

[@@specialize]
let parser_kind_nz_of_itype (i:itype)
  : bool
  = match i with
    | Unit
    | AllBytes
    | AllZeros -> false
    | _ -> true

[@@specialize]
let parser_weak_kind_of_itype (i:itype)
  : P.weak_kind
  = match i with
    | AllBytes
    | AllZeros -> P.WeakKindConsumesAll
    | _ -> P.WeakKindStrongPrefix

[@@specialize]
let parser_kind_of_itype (i:itype)
  : P.parser_kind (parser_kind_nz_of_itype i)
                  (parser_weak_kind_of_itype i)
  = match i with
    | UInt8 -> P.kind____UINT8
    | UInt16 -> P.kind____UINT16
    | UInt32 -> P.kind____UINT32
    | UInt64 -> P.kind____UINT64
    | UInt8BE -> P.kind____UINT8BE
    | UInt16BE -> P.kind____UINT16BE
    | UInt32BE -> P.kind____UINT32BE
    | UInt64BE -> P.kind____UINT64BE
    | Unit -> P.kind_unit
    | AllBytes -> P.kind_all_bytes
    | AllZeros -> P.kind_all_zeros

let itype_as_parser (i:itype)
  : P.parser (parser_kind_of_itype i) (itype_as_type i)
  = match i with
    | UInt8 -> P.parse____UINT8
    | UInt16 -> P.parse____UINT16
    | UInt32 -> P.parse____UINT32
    | UInt64 -> P.parse____UINT64
    | UInt8BE -> P.parse____UINT8BE
    | UInt16BE -> P.parse____UINT16BE
    | UInt32BE -> P.parse____UINT32BE
    | UInt64BE -> P.parse____UINT64BE
    | Unit -> P.parse_unit
    | AllBytes -> P.parse_all_bytes
    | AllZeros -> P.parse_all_zeros

[@@specialize]
let allow_reader_of_itype (i:itype)
  : bool
  = match i with
    | AllBytes
    | AllZeros -> false
    | _ -> true

[@@specialize]
let itype_as_leaf_reader
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (i:itype { allow_reader_of_itype i })
  : A.leaf_reader #base_t #len_t #pos_t (itype_as_parser i)
  = match i with
    | UInt8 -> A.read____UINT8
    | UInt16 -> A.read____UINT16
    | UInt32 -> A.read____UINT32
    | UInt64 -> A.read____UINT64
    | UInt8BE -> A.read____UINT8BE
    | UInt16BE -> A.read____UINT16BE
    | UInt32BE -> A.read____UINT32BE
    | UInt64BE -> A.read____UINT64BE
    | Unit -> A.read_unit

[@@specialize]
let itype_as_validator
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (#[@@@erasable] d: state_dict)
  (#use_error_handler:bool)
  (name: string)
  (i:itype)
  : A.validate_with_action_t #base_t #len_t #pos_t
      (itype_as_parser i)
      d
      false
      (allow_reader_of_itype i)
      use_error_handler
      (S.vspec_of_parser (itype_as_parser i))
  = match i
    returns
      A.validate_with_action_t #base_t #len_t #pos_t #inst
        (itype_as_parser i)
        d
        false
        (allow_reader_of_itype i)
        use_error_handler
        (S.vspec_of_parser (itype_as_parser i))
    with
    | UInt8 -> A.validate____UINT8 name
    | UInt16 -> A.validate____UINT16 name
    | UInt32 -> A.validate____UINT32 name
    | UInt64 -> A.validate____UINT64 name
    | UInt8BE -> A.validate____UINT8BE name
    | UInt16BE -> A.validate____UINT16BE name
    | UInt32BE -> A.validate____UINT32BE name
    | UInt64BE -> A.validate____UINT64BE name
    | Unit -> A.validate_unit_no_read
    | AllBytes -> A.validate_all_bytes
    | AllZeros -> A.validate_all_zeros

////////////////////////////////////////////////////////////////////////////////
// Type contexts
////////////////////////////////////////////////////////////////////////////////

let leaf_reader
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t |}
  #nz #wk (#k: P.parser_kind nz wk) #t (p:P.parser k t)
  = _:squash (wk == P.WeakKindStrongPrefix /\ hasEq t) &
    A.leaf_reader #base_t #len_t #pos_t p

(* The denotation of a top-level name: a quintuple of
   {type, parser, spec, validator, optional reader}. *)
noeq
type global_binding
  (base_t: Type0) (len_t: Type0) (pos_t: Type0)
  (inst: I.input_stream_inst base_t len_t pos_t)
  ([@@@erasable] d: state_dict)
  (use_error_handler:bool)
= {
  //Parser metadata
  parser_kind_nz:bool; // Does it consume non-zero bytes?
  parser_weak_kind: P.weak_kind;
  parser_kind: P.parser_kind parser_kind_nz parser_weak_kind;
  parser_has_action: bool;
  //Its type denotation
  p_t : Type0;
  //Its parser denotation
  p_p : P.parser parser_kind p_t;
  //Whether the type can be read -- to avoid double fetches
  p_reader: option (leaf_reader #base_t #len_t #pos_t #inst p_p);
  //Its spec denotation
  p_s : S.vspec d;
  //Its validate-with-action denotation
  p_v : A.validate_with_action_t #base_t #len_t #pos_t #inst
          p_p
          d
          parser_has_action
          (Some? p_reader)
          use_error_handler
          p_s;
  //Its value-level spec denotation, refined by `p_s`
  p_vs : VS.value_spec d p_t;
  p_wf : squash (VS.vspec_wf parser_has_action p_p p_s p_vs);
}

let projector_names : list string = [
  `%Mkglobal_binding?.parser_kind_nz;
  `%Mkglobal_binding?.parser_weak_kind;
  `%Mkglobal_binding?.parser_kind;
  `%Mkglobal_binding?.parser_has_action;
  `%Mkglobal_binding?.p_t;
  `%Mkglobal_binding?.p_p;
  `%Mkglobal_binding?.p_reader;
  `%Mkglobal_binding?.p_s;
  `%Mkglobal_binding?.p_v;
  `%Mkglobal_binding?.p_vs;
  `%Mkglobal_binding?.p_wf;
]

let nz_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.parser_kind_nz g
let wk_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.parser_weak_kind g
let pk_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.parser_kind g
let has_action_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.parser_has_action g
let type_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.p_t g
let parser_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.p_p g
let leaf_reader_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.p_reader g
let spec_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.p_s g
let validator_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.p_v g
let value_spec_of_binding #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) = Mkglobal_binding?.p_vs g

let has_reader #base_t #len_t #pos_t #inst #d (#use_error_handler:bool) (g:global_binding base_t len_t pos_t inst d use_error_handler) =
  match leaf_reader_of_binding g with
  | Some _ -> true
  | _ -> false

[@@specialize]
let get_leaf_reader #base_t #len_t #pos_t #inst #d (#use_error_handler:bool)
                    (r:global_binding base_t len_t pos_t inst d use_error_handler { has_reader r })
  : leaf_reader #base_t #len_t #pos_t #inst (parser_of_binding r)
  = Some?.v (leaf_reader_of_binding r)

////////////////////////////////////////////////////////////////////////////////
// Denoted types
////////////////////////////////////////////////////////////////////////////////

noeq
type dtyp
  (base_t: Type0) (len_t: Type0) (pos_t: Type0)
  (inst: I.input_stream_inst base_t len_t pos_t)
  ([@@@erasable] d: state_dict)
  (use_error_handler:bool)
  : #nz:bool -> #wk:P.weak_kind ->
    P.parser_kind nz wk ->
    has_action:bool ->
    has_reader:bool ->
    Type =
  | DT_IType:
      i:itype ->
      dtyp base_t len_t pos_t inst d use_error_handler
           (parser_kind_of_itype i)
           false
           (allow_reader_of_itype i)

  | DT_App:
      #nz:bool ->
      #wk:P.weak_kind ->
      pk:P.parser_kind nz wk ->
      ha:bool ->
      hr:bool ->
      x:global_binding base_t len_t pos_t inst d use_error_handler ->
      _:squash (nz == nz_of_binding x /\
                wk == wk_of_binding x /\
                pk == pk_of_binding x /\
                ha == has_action_of_binding x /\
                hr == has_reader x) ->
      dtyp base_t len_t pos_t inst d use_error_handler #nz #wk pk ha hr

[@@specialize]
let dtyp_as_type #base_t #len_t #pos_t #inst #d (#use_error_handler:bool)
                 #nz #wk (#pk:P.parser_kind nz wk) #ha #hr
                 (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha hr)
  : Type
  = match t with
    | DT_IType i -> itype_as_type i
    | DT_App _ _ _ b _ -> type_of_binding b

let dtyp_as_eqtype_lemma #base_t #len_t #pos_t #inst #d (#use_error_handler:bool)
                         #nz #wk (#pk:P.parser_kind nz wk) #ha
                         (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha true)
  : Lemma
    (ensures hasEq (dtyp_as_type t))
    [SMTPat (hasEq (dtyp_as_type t))]
  = match t with
    | DT_IType i -> ()
    | DT_App _ _ _ b _ -> let (| _, _ |) = get_leaf_reader b in ()

let dtyp_as_parser #base_t #len_t #pos_t #inst #d (#use_error_handler:bool)
                   #nz #wk (#pk:P.parser_kind nz wk) #ha #hr
                   (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha hr)
  : P.parser pk (dtyp_as_type t)
  = match t returns Tot (P.parser pk (dtyp_as_type t)) with
    | DT_IType i -> itype_as_parser i
    | DT_App _ _ _ b _ -> parser_of_binding b

let dtyp_as_vspec #base_t #len_t #pos_t #inst #d (#use_error_handler:bool)
                   #nz #wk (#pk:P.parser_kind nz wk) #ha #hr
                   (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha hr)
  : S.vspec d
  = match t with
    | DT_IType i -> S.vspec_of_parser (itype_as_parser i)
    | DT_App _ _ _ b _ -> spec_of_binding b

let dtyp_as_value_spec #base_t #len_t #pos_t #inst #d (#use_error_handler:bool)
                   #nz #wk (#pk:P.parser_kind nz wk) #ha #hr
                   (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha hr)
  : VS.value_spec d (dtyp_as_type t)
  = match t returns VS.value_spec d (dtyp_as_type t) with
    | DT_IType i -> VS.vs_true
    | DT_App _ _ _ b _ -> value_spec_of_binding b

let dtyp_wf #base_t #len_t #pos_t #inst #d (#use_error_handler:bool)
                   #nz #wk (#pk:P.parser_kind nz wk) #ha #hr
                   (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha hr)
  : Lemma (VS.vspec_wf ha (dtyp_as_parser t) (dtyp_as_vspec t) (dtyp_as_value_spec t))
  = match t with
    | DT_IType i -> VS.wf_of_parser #d false (itype_as_parser i)
    | DT_App _ _ _ b _ -> let _ = b.p_wf in ()

[@@specialize]
let dtyp_as_validator #base_t #len_t #pos_t (#inst: I.input_stream_inst base_t len_t pos_t) (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t) (#[@@@erasable] d: state_dict) (#use_error_handler:bool)
                      #nz #wk (#pk:P.parser_kind nz wk) (#ha #hr:_)
                      (name: string)
                      (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha hr)
  : A.validate_with_action_t #base_t #len_t #pos_t #inst #nz #wk #pk #(dtyp_as_type t)
        (dtyp_as_parser t)
        d
        ha hr use_error_handler
        (dtyp_as_vspec t)
  = match t
    returns
      A.validate_with_action_t #base_t #len_t #pos_t #inst #nz #wk #pk #(dtyp_as_type t)
        (dtyp_as_parser t)
        d
        ha hr use_error_handler
        (dtyp_as_vspec t)
    with
    | DT_IType i -> itype_as_validator #base_t #len_t #pos_t #inst #_extra #d #use_error_handler name i
    | DT_App _ _ _ b _ -> validator_of_binding b

(* At `hr = true`, `validate_with_action_t` reduces to the non-consuming
   validator, which is what the combinators that are followed by a leaf reader
   expect. *)
[@@specialize]
let dtyp_as_validator_no_read #base_t #len_t #pos_t (#inst: I.input_stream_inst base_t len_t pos_t) (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t) (#[@@@erasable] d: state_dict) (#use_error_handler:bool)
                      #nz #wk (#pk:P.parser_kind nz wk) (#ha:_)
                      (name: string)
                      (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha true)
  : A.validate_with_action_no_read #base_t #len_t #pos_t #inst
        (dtyp_as_parser t)
        d
        ha use_error_handler
        (dtyp_as_vspec t)
  = dtyp_as_validator name t

[@@specialize]
let dtyp_as_leaf_reader #base_t #len_t #pos_t (#inst: I.input_stream_inst base_t len_t pos_t) (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t) (#[@@@erasable] d: state_dict) (#use_error_handler:bool)
                        #nz (#pk:P.parser_kind nz P.WeakKindStrongPrefix) #ha
                        (t:dtyp base_t len_t pos_t inst d use_error_handler pk ha true)
  : A.leaf_reader #base_t #len_t #pos_t #inst (dtyp_as_parser t)
  = match t with
    | DT_IType i -> itype_as_leaf_reader #base_t #len_t #pos_t #inst #_extra i
    | DT_App _ _ _ b _ -> let (| _, lr |) = get_leaf_reader b in lr

////////////////////////////////////////////////////////////////////////////////
// Probe actions
////////////////////////////////////////////////////////////////////////////////

(* The type of atomic probe actions.

   Unlike the Low* version, everything is indexed by the input-stream and
   copy-buffer type class instances: the probe combinators are typeclass
   polymorphic, and the instances are picked by the frontend-provided backend.
*)
noeq
type atomic_probe_action
  (copy_buffer_t: Type0)
  (base_t: Type0) (len_t: Type0) (pos_t: Type0)
  (inst: I.input_stream_inst base_t len_t pos_t)
  (cbinst: CP.copy_buffer copy_buffer_t base_t len_t pos_t)
  (boolean_t: Type0)
  (boolean_inst: Bool.boolean_repr boolean_t)
  : Type0 -> Type u#1 =
  | Atomic_probe_and_copy :
      bytes_to_read : U64.t ->
      probe_fn: PA.probe_fn_incremental #copy_buffer_t #base_t #len_t #pos_t #inst #cbinst #boolean_t #boolean_inst ->
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst unit
  | Atomic_probe_and_read :
      #t:Type0 ->
      #sz:U64.t { sz <> 0uL } ->
      reader : PA.probe_and_read_at_offset_t #copy_buffer_t #base_t #len_t #pos_t #inst #cbinst #boolean_t #boolean_inst t sz ->
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst t
  | Atomic_probe_write_at_offset :
      #t:Type0 ->
      #sz:U64.t { sz <> 0uL } ->
      v:t ->
      writer : PA.write_at_offset_t #copy_buffer_t #base_t #len_t #pos_t #inst #cbinst #boolean_t #boolean_inst t sz ->
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst unit
  | Atomic_probe_call_pure :
      #t:Type0 ->
      f:PA.pure_external_action t ->
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst t
  | Atomic_probe_skip_read:
      n:U64.t ->
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst unit
  | Atomic_probe_skip_write:
      n:U64.t ->
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst unit
  | Atomic_probe_return:
      #t:Type0 ->
      v:t ->
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst t
  | Atomic_probe_fail:
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst unit

[@@specialize]
let atomic_probe_action_as_probe_m
      (#copy_buffer_t #base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
      (#cbinst: CP.copy_buffer copy_buffer_t base_t len_t pos_t)
      (#boolean_t: Type0)
      {| boolean_inst: Bool.boolean_repr boolean_t |}
      (#use_error_handler:bool) (#t:Type0)
      (error_handler_macro: error_handler #base_t #len_t #pos_t #inst)
      (p:atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst t)
: PA.probe_m #_ #_ #_ #_ #inst #cbinst #boolean_t #boolean_inst t true false use_error_handler
= match p with
  | Atomic_probe_and_copy bytes_to_read probe_fn_incremental ->
    PA.probe_fn_incremental_as_probe_m probe_fn_incremental bytes_to_read
  | Atomic_probe_and_read reader ->
    PA.probe_and_read_at_offset_m error_handler_macro reader
  | Atomic_probe_write_at_offset v writer ->
    PA.write_at_offset_m writer v
  | Atomic_probe_call_pure f ->
    PA.lift_pure_external_action f
  | Atomic_probe_skip_read n ->
    PA.skip_read n
  | Atomic_probe_skip_write n ->
    PA.skip_write n
  | Atomic_probe_return v ->
    PA.return_probe_m v
  | Atomic_probe_fail ->
    PA.fail

noeq
type probe_action
  (copy_buffer_t: Type0)
  (base_t: Type0) (len_t: Type0) (pos_t: Type0)
  (inst: I.input_stream_inst base_t len_t pos_t)
  (cbinst: CP.copy_buffer copy_buffer_t base_t len_t pos_t)
  (boolean_t: Type0)
  (boolean_inst: Bool.boolean_repr boolean_t)
  (use_error_handler:bool)
  : bool -> Type u#1 =
  | Probe_action_atomic :
      atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst unit ->
      probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false
  | Probe_action_var :
      PA.probe_m #_ #_ #_ #_ #inst #cbinst #boolean_t #boolean_inst unit true false use_error_handler ->
      probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false
  | Probe_action_seq:
      detail:string ->
      m1: probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false ->
      m2: probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false ->
      probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false
  | Probe_action_let:
      #t:Type0 ->
      detail:string ->
      m1: atomic_probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst t ->
      m2: (t -> probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false) ->
      probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false
  | Probe_action_ite:
      cond:bool ->
      m1: probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false ->
      m2: probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false ->
      probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false
  | Probe_action_array:
      bytes_len:U64.t ->
      element_probe:probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false ->
      probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false
  | Probe_action_copy_init_sz:
      probe_fn:PA.probe_fn_incremental #copy_buffer_t #base_t #len_t #pos_t #inst #cbinst #boolean_t #boolean_inst ->
      probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler false

[@@specialize]
let rec probe_action_as_probe_m
      (#copy_buffer_t #base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
      (#cbinst: CP.copy_buffer copy_buffer_t base_t len_t pos_t)
      (#boolean_t: Type0)
      {| boolean_inst: Bool.boolean_repr boolean_t |}
      (#use_error_handler:bool) (#maybe_zero:bool)
      (error_handler_macro: error_handler #base_t #len_t #pos_t #inst)
      (p:probe_action copy_buffer_t base_t len_t pos_t inst cbinst boolean_t boolean_inst use_error_handler maybe_zero)
: Tot (PA.probe_m #_ #_ #_ #_ #inst #cbinst #boolean_t #boolean_inst unit true maybe_zero use_error_handler)
      (decreases p)
= match p with
  | Probe_action_atomic a ->
    atomic_probe_action_as_probe_m error_handler_macro a
  | Probe_action_var m ->
    m
  | Probe_action_seq detail m1 m2 ->
    PA.seq_probe_m error_handler_macro detail ()
      (probe_action_as_probe_m error_handler_macro m1)
      (probe_action_as_probe_m error_handler_macro m2)
  | Probe_action_let detail m1 m2 ->
    let k x : PA.probe_m #_ #_ #_ #_ #inst #cbinst #boolean_t #boolean_inst unit true false use_error_handler =
      probe_action_as_probe_m error_handler_macro (m2 x)
    in
    PA.bind_probe_m error_handler_macro detail ()
      (atomic_probe_action_as_probe_m error_handler_macro m1) k
  | Probe_action_ite cond m1 m2 ->
    PA.if_then_else cond
      (probe_action_as_probe_m error_handler_macro m1)
      (probe_action_as_probe_m error_handler_macro m2)
  | Probe_action_array len body ->
    PA.probe_array error_handler_macro len
      (probe_action_as_probe_m error_handler_macro body)
  | Probe_action_copy_init_sz probe_fn ->
    PA.probe_and_copy_init_sz error_handler_macro probe_fn

////////////////////////////////////////////////////////////////////////////////
// Actions
////////////////////////////////////////////////////////////////////////////////

(* The Pulse `A.action` carries neither the `on_success` nor the
   `return_true` index of its Low* counterpart. We nevertheless keep both
   booleans on the AST, since the 3D front-end's internal representation
   still tracks them and they discipline where an action may be placed. They
   are simply ignored by the denotation. *)

[@@specialize]
let action_binding
      (base_t: Type0) (len_t: Type0) (pos_t: Type0)
      (inst: I.input_stream_inst base_t len_t pos_t)
      ([@@@erasable] d: state_dict)
      (use_error_handler:bool)
      (a:Type0)
  : Type u#0
  = A.action #base_t #len_t #pos_t #inst d a use_error_handler S.aspec_unknown

[@@specialize]
let extern_action ([@@@erasable] d: state_dict) (t: Type0) = A.external_action d t

(* An external action, declared at whatever `state_dict` it actually needs,
   weakened into the ambient dictionary of the enclosing type. The weakening
   obligation `state_dict_weaken_prop` is a decidable computation over the
   literal string keys, discharged by normalization rather than by SMT. *)
[@@specialize]
let mk_action_binding
    (#base_t #len_t #pos_t: Type0)
    (#inst: I.input_stream_inst base_t len_t pos_t)
    (#use_error_handler:bool)
    (#t: Type0)
    (#[@@@erasable] d': state_dict)
    ($f: extern_action d' t)
    ([@@@erasable] d: state_dict)
    (sq: squash (state_dict_weaken_prop d' d))
  : action_binding base_t len_t pos_t inst d use_error_handler t
  = A.action_forget_spec (A.action_weaken #base_t #len_t #pos_t #inst (A.mk_external_action f) d sq)

(* The field-pointer setter is an external action in disguise: `write_to` runs
   at the output type's own `state_dict`, not at the ambient one. Building it
   as an `atomic_action` node pinned the whole enclosing `Action_seq` to that
   dictionary, so a sibling `Action_assignment` on an unrelated mutable
   parameter could no longer discharge its own weakening obligation. Take the
   callee's dictionary as an argument and weaken here, exactly as
   `mk_action_binding` does; the result is stored via `Action_call`, which is
   what keeps `atomic_action` in universe 1. *)
[@@specialize]
let mk_field_ptr_after_with_setter
    (#base_t #len_t #pos_t: Type0)
    (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
    (#use_error_handler:bool)
    (#ptr_t: Type0)
    (#[@@@erasable] d': state_dict)
    ($f: option (A.field_ptr_after_setter_t base_t len_t pos_t #inst d' ptr_t))
    (_: squash (Some? f))
    (sz: U64.t)
    (write_to: (ptr_t -> extern_action d' unit))
    ([@@@erasable] d: state_dict)
    (sq: squash (state_dict_weaken_prop d' d))
  : action_binding base_t len_t pos_t inst d use_error_handler bool
  = A.action_forget_spec (A.action_weaken #base_t #len_t #pos_t #inst
      (A.action_field_ptr_after_with_setter #_ #_ #_ #inst (Some?.v f) sz write_to)
      d sq)

noeq
type atomic_action
  (base_t: Type0) (len_t: Type0) (pos_t: Type0)
  (inst: I.input_stream_inst base_t len_t pos_t)
  ([@@@erasable] d: state_dict)
  (use_error_handler:bool)
  : bool -> bool -> Type0 -> Type u#1 =
  | Action_return:
      #a:Type0 ->
      x:a ->
      atomic_action base_t len_t pos_t inst d use_error_handler false false a

  | Action_return_true:
      atomic_action base_t len_t pos_t inst d use_error_handler false true bool

  | Action_abort:
      atomic_action base_t len_t pos_t inst d use_error_handler false false bool

  | Action_field_pos_64:
      atomic_action base_t len_t pos_t inst d use_error_handler false false U64.t

  | Action_field_pos_32:
      atomic_action base_t len_t pos_t inst d use_error_handler false false U32.t

  | Action_field_ptr:
      f:option (A.field_ptr_t base_t len_t pos_t #inst) ->
      _:squash (Some? f) ->
      atomic_action base_t len_t pos_t inst d use_error_handler true false EverParse3d.PtrModel.ptr

  | Action_field_ptr_after:
      #ptr_t:Type0 ->
      f:option (A.field_ptr_after_t base_t len_t pos_t #inst ptr_t) ->
      _:squash (Some? f) ->
      name:Ghost.erased string ->
      sz:U64.t ->
      write_to:ref ptr_t ->
      _:squash (state_dict_weaken_prop
                  (state_dict_singleton name (pts_to write_to #1.0R)) d) ->
      atomic_action base_t len_t pos_t inst d use_error_handler false false bool

  | Action_deref:
      #a:Type0 ->
      name:Ghost.erased string ->
      x:ref a ->
      _:squash (state_dict_weaken_prop (state_dict_singleton name (pts_to x #1.0R)) d) ->
      atomic_action base_t len_t pos_t inst d use_error_handler false false a

  | Action_deref_map:
      #a:Type0 ->
      #b:Type0 ->
      decode:(a -> Tot b) ->
      name:Ghost.erased string ->
      x:ref a ->
      _:squash (state_dict_weaken_prop (state_dict_singleton name (pts_to x #1.0R)) d) ->
      atomic_action base_t len_t pos_t inst d use_error_handler false false b

  | Action_assignment:
      #a:Type0 ->
      name:Ghost.erased string ->
      x:ref a ->
      rhs:a ->
      _:squash (state_dict_weaken_prop (state_dict_singleton name (pts_to x #1.0R)) d) ->
      atomic_action base_t len_t pos_t inst d use_error_handler false false unit

  (* The escape hatch: an already-denoted action at the ambient dictionary.
     Both external actions (via `mk_action_binding`) and probe-then-validate
     (via the `t_probe_then_validate` smart constructor) go through here. This
     is what keeps `atomic_action` in universe 1: storing the callee's own
     `state_dict` in the AST would raise it. The spec of the action is stored
     along with it (it is `S.aspec_unknown` for external actions.) *)
  | Action_call:
      #b:bool ->
      #t:Type0 ->
      #sp:S.action_spec d t ->
      A.action #base_t #len_t #pos_t #inst d t use_error_handler sp ->
      atomic_action base_t len_t pos_t inst d use_error_handler b false t

let action_spec_of
   (#base_t #len_t #pos_t: Type0)
   (#inst: I.input_stream_inst base_t len_t pos_t)
   (#d: state_dict)
   (#t: Type0)
   (#use_error_handler:bool)
   (#sp: S.action_spec d t)
   (a: A.action #base_t #len_t #pos_t #inst d t use_error_handler sp)
: Tot (S.action_spec d t)
= sp

(* The spec denotation of atomic actions. *)
let atomic_action_as_spec
   (#base_t #len_t #pos_t: Type0)
   (#inst: I.input_stream_inst base_t len_t pos_t)
   (#d: state_dict)
   (#use_error_handler:bool)
   (#b #rt #t:_)
   (a:atomic_action base_t len_t pos_t inst d use_error_handler b rt t)
  : Tot (S.action_spec d t)
  = match a
    returns Tot (S.action_spec d t)
    with
    | Action_return x -> S.aspec_return x
    | Action_return_true -> S.aspec_return true
    | Action_abort -> S.aspec_return false
    | Action_field_pos_64 -> S.aspec_field_pos_64
    | Action_field_pos_32 -> S.aspec_field_pos_32
    | Action_field_ptr f sq -> S.aspec_field_ptr
    | Action_field_ptr_after f sq name sz write_to sq' ->
      S.aspec_weaken S.aspec_unknown d sq'
    | Action_deref name x sq ->
      S.aspec_weaken (S.aspec_deref name (pts_to x #1.0R)) d sq
    | Action_deref_map decode name x sq ->
      S.aspec_weaken (S.aspec_deref_map decode name (pts_to x #1.0R)) d sq
    | Action_assignment name x rhs sq ->
      S.aspec_weaken (S.aspec_assignment name (pts_to x #1.0R) rhs) d sq
    | Action_call c -> action_spec_of c

[@@specialize]
let atomic_action_as_action
   (#base_t #len_t #pos_t: Type0)
   (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
   (#[@@@erasable] d: state_dict)
   (#use_error_handler:bool)
   (#b #rt #t:_)
   (a:atomic_action base_t len_t pos_t inst d use_error_handler b rt t)
  : Tot (A.action #base_t #len_t #pos_t #inst d t use_error_handler (atomic_action_as_spec a))
  = match a
    returns Tot (A.action #base_t #len_t #pos_t #inst d t use_error_handler (atomic_action_as_spec a))
    with
    | Action_return x ->
      A.action_return x
    | Action_return_true ->
      A.action_return_true
    | Action_abort ->
      A.action_abort
    | Action_field_pos_64 ->
      A.action_field_pos_64
    | Action_field_pos_32 ->
      A.action_field_pos_32
    | Action_field_ptr f sq ->
      A.action_field_ptr (Some?.v f)
    | Action_field_ptr_after f sq name sz write_to sq' ->
      A.action_weaken (A.action_field_ptr_after (Some?.v f) name sz write_to) d sq'
    | Action_deref name x sq ->
      A.action_weaken (A.action_deref name x) d sq
    | Action_deref_map decode name x sq ->
      A.action_weaken (A.action_deref_map decode name x) d sq
    | Action_assignment name x rhs sq ->
      A.action_weaken (A.action_assignment name x rhs) d sq
    | Action_call c ->
      c

(* A sub-language of monadic actions. *)
noeq
type action
  (base_t: Type0) (len_t: Type0) (pos_t: Type0)
  (inst: I.input_stream_inst base_t len_t pos_t)
  ([@@@erasable] d: state_dict)
  (use_error_handler:bool)
  : bool -> bool -> Type0 -> Type u#1 =
  | Atomic_action:
      #b:_ -> #rt:_ -> #t:_ ->
      atomic_action base_t len_t pos_t inst d use_error_handler b rt t ->
      action base_t len_t pos_t inst d use_error_handler b rt t

  | Action_seq:
      #b0:_ -> #rt1:_ ->
      hd:atomic_action base_t len_t pos_t inst d use_error_handler b0 rt1 unit ->
      #b1:_ -> #rt2:_ -> #t:_ ->
      tl:action base_t len_t pos_t inst d use_error_handler b1 rt2 t ->
      action base_t len_t pos_t inst d use_error_handler (b0 || b1) rt2 t

  | Action_ite :
      hd:bool ->
      #b0:_ -> #rt0:_ -> #t:_ ->
      then_:(squash (hd == true) -> action base_t len_t pos_t inst d use_error_handler b0 rt0 t) ->
      #b1:_ -> #rt1:_ ->
      else_:(squash (hd == false) -> action base_t len_t pos_t inst d use_error_handler b1 rt1 t) ->
      action base_t len_t pos_t inst d use_error_handler (b0 || b1) (rt0 && rt1) t

  | Action_let:
      #b0:_ -> #rt1:_ -> #t0:_ ->
      head:atomic_action base_t len_t pos_t inst d use_error_handler b0 rt1 t0 ->
      #b1:_ -> #rt2:_ -> #t1:_ ->
      k:(t0 -> action base_t len_t pos_t inst d use_error_handler b1 rt2 t1) ->
      action base_t len_t pos_t inst d use_error_handler (b0 || b1) rt2 t1

  | Action_act:
      #b0:_ -> #rt0:_ ->
      act:action base_t len_t pos_t inst d use_error_handler b0 rt0 unit ->
      action base_t len_t pos_t inst d use_error_handler b0 true bool

let rec action_as_spec
   (#base_t #len_t #pos_t: Type0)
   (#inst: I.input_stream_inst base_t len_t pos_t)
   (#d: state_dict)
   (#use_error_handler:bool)
   (#b #rt #t:_)
   (a:action base_t len_t pos_t inst d use_error_handler b rt t)
  : Tot (S.action_spec d t)
    (decreases a)
  = match a with
    | Atomic_action a -> atomic_action_as_spec a
    | Action_seq hd tl -> S.aspec_seq (atomic_action_as_spec hd) (action_as_spec tl)
    | Action_ite hd t e ->
      S.aspec_ite hd (fun x -> action_as_spec (t x)) (fun x -> action_as_spec (e x))
    | Action_let hd k ->
      S.aspec_bind (atomic_action_as_spec hd) (fun x -> action_as_spec (k x))
    | Action_act a -> S.aspec_seq (action_as_spec a) (S.aspec_return true)

[@@specialize]
let rec action_as_action
   (#base_t #len_t #pos_t: Type0)
   (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
   (#[@@@erasable] d: state_dict)
   (#use_error_handler:bool)
   (#b #rt #t:_)
   (a:action base_t len_t pos_t inst d use_error_handler b rt t)
  : Tot (A.action #base_t #len_t #pos_t #inst d t use_error_handler (action_as_spec a))
    (decreases a)
  = match a
    returns Tot (A.action #base_t #len_t #pos_t #inst d t use_error_handler (action_as_spec a))
    with
    | Atomic_action a ->
      atomic_action_as_action a

    | Action_seq hd tl ->
      let a1 = atomic_action_as_action hd in
      let tl = action_as_action tl in
      A.action_seq a1 tl

    | Action_ite hd t e ->
      assert_norm (action_as_spec (Action_ite #base_t #len_t #pos_t #inst #d #use_error_handler hd t e) ==
                   S.aspec_ite hd (fun x -> action_as_spec (t x)) (fun x -> action_as_spec (e x)));
      let then_ (x:squash (hd == true)) = action_as_action (t x) in
      let else_ (x:squash (hd == false)) = action_as_action (e x) in
      A.action_ite hd then_ else_

    | Action_let hd k ->
      assert_norm (action_as_spec (Action_let #base_t #len_t #pos_t #inst #d #use_error_handler hd k) ==
                   S.aspec_bind (atomic_action_as_spec hd) (fun x -> action_as_spec (k x)));
      let head = atomic_action_as_action hd in
      let k x = action_as_action (k x) in
      A.action_bind "hd" head k

    | Action_act a ->
      A.action_seq (action_as_action a) A.action_return_true

////////////////////////////////////////////////////////////////////////////////
// Types
////////////////////////////////////////////////////////////////////////////////

(* Some AST nodes contain source comments that we propagate to the output *)
let comments = string

(* The `allow_reading` index below is the Pulse reading of the Low* one:
   `true` means the validator does not consume the input stream, so that a
   leaf reader may subsequently read the value. Note that, unlike in Low*,
   the two flavours are genuinely distinct types in Pulse, so `as_validator`
   inserts `A.validate_without_reading_gen` wherever a sub-type at an
   arbitrary `allow_reading` feeds a combinator expecting a consuming
   validator. *)

[@@ no_auto_projectors]
noeq
type typ
  (base_t: Type0) (len_t: Type0) (pos_t: Type0)
  (inst: I.input_stream_inst base_t len_t pos_t)
  ([@@@erasable] d: state_dict)
  (use_error_handler:bool)
  : #nz:bool -> #wk:P.weak_kind ->
    P.parser_kind nz wk ->
    bool ->
    bool ->
    Type =
  | T_false:
      fieldname:string ->
      typ base_t len_t pos_t inst d use_error_handler P.impos_kind false true

  | T_denoted :
      fieldname:string ->
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #ha:_ -> #has_reader:_ ->
      td:dtyp base_t len_t pos_t inst d use_error_handler pk ha has_reader ->
      typ base_t len_t pos_t inst d use_error_handler pk ha has_reader

  | T_pair:
      first_fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #ha1:_ -> #b1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #ha2:_ -> #b2:_ ->
      k1_const: bool ->
      t1:typ base_t len_t pos_t inst d use_error_handler pk1 ha1 b1 ->
      k2_const: bool ->
      t2:typ base_t len_t pos_t inst d use_error_handler pk2 ha2 b2 ->
      typ base_t len_t pos_t inst d use_error_handler
          (P.and_then_kind pk1 pk2) (ha1 || ha2) false

  | T_dep_pair:
      first_fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #ha1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #ha2:_ -> #b2:bool ->
      //the first component is a pre-denoted type with a reader
      t1:dtyp base_t len_t pos_t inst d use_error_handler pk1 ha1 true ->
      //the second component is a function from denotations of t1
      t2:(dtyp_as_type t1 -> typ base_t len_t pos_t inst d use_error_handler pk2 ha2 b2) ->
      typ base_t len_t pos_t inst d use_error_handler
          (P.and_then_kind pk1 pk2) (ha1 || ha2) false

  | T_refine:
      fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #ha1:_ ->
      base:dtyp base_t len_t pos_t inst d use_error_handler pk1 ha1 true ->
      refinement:(dtyp_as_type base -> bool) ->
      err:(dtyp_as_type base -> E.constraint_error_code) ->
      typ base_t len_t pos_t inst d use_error_handler (P.filter_kind pk1) ha1 false

  | T_refine_with_action:
      fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #ha1:_ -> #b2:_ -> #rt2:_ ->
      base:dtyp base_t len_t pos_t inst d use_error_handler pk1 ha1 true ->
      refinement:(dtyp_as_type base -> bool) ->
      err:(dtyp_as_type base -> E.constraint_error_code) ->
      act:(dtyp_as_type base -> action base_t len_t pos_t inst d use_error_handler b2 rt2 bool) ->
      typ base_t len_t pos_t inst d use_error_handler (P.filter_kind pk1) true false

  | T_dep_pair_with_refinement:
      first_fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #ha1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #ha2:_ -> #b2:_ ->
      base:dtyp base_t len_t pos_t inst d use_error_handler pk1 ha1 true ->
      refinement:(dtyp_as_type base -> bool) ->
      err:(dtyp_as_type base -> E.constraint_error_code) ->
      k:(x:dtyp_as_type base { refinement x } ->
         typ base_t len_t pos_t inst d use_error_handler pk2 ha2 b2) ->
      typ base_t len_t pos_t inst d use_error_handler
          (P.and_then_kind (P.filter_kind pk1) pk2) (ha1 || ha2) false

  | T_dep_pair_with_action:
      fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #ha1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #ha2:_ -> #b2:_ ->
      #b3:_ -> #rt3:_ ->
      base:dtyp base_t len_t pos_t inst d use_error_handler pk1 ha1 true ->
      k:(x:dtyp_as_type base -> typ base_t len_t pos_t inst d use_error_handler pk2 ha2 b2) ->
      act:(dtyp_as_type base -> action base_t len_t pos_t inst d use_error_handler b3 rt3 bool) ->
      typ base_t len_t pos_t inst d use_error_handler
          (P.and_then_kind pk1 pk2) true false

  | T_dep_pair_with_refinement_and_action:
      first_fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #ha1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #ha2:_ -> #b2:_ ->
      #b3:_ -> #rt3:_ ->
      base:dtyp base_t len_t pos_t inst d use_error_handler pk1 ha1 true ->
      refinement:(dtyp_as_type base -> bool) ->
      err:(dtyp_as_type base -> E.constraint_error_code) ->
      k:(x:dtyp_as_type base { refinement x } ->
         typ base_t len_t pos_t inst d use_error_handler pk2 ha2 b2) ->
      act:(dtyp_as_type base -> action base_t len_t pos_t inst d use_error_handler b3 rt3 bool) ->
      typ base_t len_t pos_t inst d use_error_handler
          (P.and_then_kind (P.filter_kind pk1) pk2) true false

  | T_if_else:
      #nz1:_ -> #wk1:_ -> #pk1:P.parser_kind nz1 wk1 ->
      #b1:_ -> #ha1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #b2:_ -> #ha2:_ ->
      b:bool -> //A bool, rather than an expression
      t1:(squash b -> typ base_t len_t pos_t inst d use_error_handler pk1 ha1 b1) ->
      t2:(squash (not b) -> typ base_t len_t pos_t inst d use_error_handler pk2 ha2 b2) ->
      typ base_t len_t pos_t inst d use_error_handler (P.glb pk1 pk2) (ha1 || ha2) false

  | T_cases:
      #nz1:_ -> #wk1:_ -> #pk1:P.parser_kind nz1 wk1 ->
      #b1:_ -> #ha1:_ ->
      #nz2:_ -> #wk2:_ -> #pk2:P.parser_kind nz2 wk2 ->
      #b2:_ -> #ha2:_ ->
      b:bool -> //A bool, rather than an expression
      t1:typ base_t len_t pos_t inst d use_error_handler pk1 ha1 b1 ->
      t2:typ base_t len_t pos_t inst d use_error_handler pk2 ha2 b2 ->
      typ base_t len_t pos_t inst d use_error_handler (P.glb pk1 pk2) (ha1 || ha2) false

  | T_with_action:
      fieldname:string ->
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #b1:_ -> #ha1:_ ->
      #b2:_ -> #rt2:_ ->
      base:typ base_t len_t pos_t inst d use_error_handler pk ha1 b1 ->
      act:action base_t len_t pos_t inst d use_error_handler b2 rt2 bool ->
      typ base_t len_t pos_t inst d use_error_handler pk true false

  | T_with_dep_action:
      fieldname:string ->
      #nz1:_ -> #pk1:P.parser_kind nz1 P.WeakKindStrongPrefix ->
      #ha1:_ ->
      #b2:_ -> #rt2:_ ->
      head:dtyp base_t len_t pos_t inst d use_error_handler pk1 ha1 true ->
      act:(typename:string -> dtyp_as_type head ->
           action base_t len_t pos_t inst d use_error_handler b2 rt2 bool) ->
      typ base_t len_t pos_t inst d use_error_handler pk1 true false

  | T_drop:
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #b:_ -> #ha:_ ->
      t:typ base_t len_t pos_t inst d use_error_handler pk ha b ->
      typ base_t len_t pos_t inst d use_error_handler pk ha false

  | T_with_comment:
      fieldname:string ->
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #b:_ -> #ha:_ ->
      t:typ base_t len_t pos_t inst d use_error_handler pk ha b ->
      c:comments ->
      typ base_t len_t pos_t inst d use_error_handler pk ha b

  | T_nlist:
      fieldname:string ->
      #wk:_ -> #pk:P.parser_kind true wk ->
      #b:_ -> #ha:_ ->
      n:U32.t ->
      n_is_constant:option nat { P.memoizes_n_as_const n_is_constant n } ->
      payload_is_constant_size:bool ->
      t:typ base_t len_t pos_t inst d use_error_handler pk ha b ->
      typ base_t len_t pos_t inst d use_error_handler (P.kind_nlist pk n_is_constant) ha false

  | T_at_most:
      fieldname:string ->
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #b:_ -> #ha:_ ->
      n:U32.t ->
      t:typ base_t len_t pos_t inst d use_error_handler pk ha b ->
      typ base_t len_t pos_t inst d use_error_handler P.kind_t_at_most ha false

  | T_exact:
      fieldname:string ->
      #nz:_ -> #wk:_ -> #pk:P.parser_kind nz wk ->
      #b:_ -> #ha:_ ->
      n:U32.t ->
      t:typ base_t len_t pos_t inst d use_error_handler pk ha b ->
      typ base_t len_t pos_t inst d use_error_handler P.kind_t_exact ha false

  | T_string:
      fieldname:string ->
      #pk1:P.parser_kind true P.WeakKindStrongPrefix ->
      #ha:_ ->
      element_type:dtyp base_t len_t pos_t inst d use_error_handler pk1 ha true ->
      terminator:dtyp_as_type element_type ->
      typ base_t len_t pos_t inst d use_error_handler P.parse_string_kind ha false

(* Type denotation of `typ` *)
let rec as_type
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#[@@@erasable] d: state_dict)
          (#use_error_handler:bool)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : Tot Type0
    (decreases t)
  = match t with
    | T_false _ -> False

    | T_denoted _ td ->
      dtyp_as_type td

    | T_pair _ _ t1 _ t2 ->
      as_type t1 & as_type t2

    | T_dep_pair _ i t
    | T_dep_pair_with_action _ i t _ ->
      x:dtyp_as_type i & as_type (t x)

    | T_refine _ base refinement _ ->
      P.refine (dtyp_as_type base) refinement

    | T_refine_with_action _ base refinement _ _ ->
      P.refine (dtyp_as_type base) refinement

    | T_dep_pair_with_refinement _ base refinement _ t ->
      x:P.refine (dtyp_as_type base) refinement & as_type (t x)

    | T_dep_pair_with_refinement_and_action _ base refinement _ t _ ->
      x:P.refine (dtyp_as_type base) refinement & as_type (t x)

    | T_if_else b t0 t1 ->
      P.t_ite b (fun _ -> as_type (t0()))
                (fun _ -> as_type (t1()))

    | T_cases b t0 t1 ->
      P.t_ite b (fun _ -> as_type t0) (fun _ -> as_type t1)

    | T_drop t
    | T_with_action _ t _
    | T_with_comment _ t _ ->
      as_type t

    | T_with_dep_action _ i _ ->
      dtyp_as_type i

    | T_nlist _fn n _n_is_const _plconst t ->
      P.nlist n (as_type t)

    | T_at_most _ n t ->
      P.t_at_most n (as_type t)

    | T_exact _ n t ->
      P.t_exact n (as_type t)

    | T_string _ elt_t terminator ->
      P.cstring (dtyp_as_type elt_t) terminator

(* Parser denotation of `typ` *)
let rec as_parser
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#[@@@erasable] d: state_dict)
          (#use_error_handler:bool)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : Tot (P.parser pk (as_type t))
        (decreases t)
  = match t returns Tot (P.parser pk (as_type t)) with
    | T_false _ ->
      P.parse_impos()

    | T_denoted _ dt ->
      dtyp_as_parser dt

    | T_pair _ _ t1 _ t2 ->
      let p1 = as_parser t1 in
      let p2 = as_parser t2 in
      P.parse_pair p1 p2

    | T_dep_pair _ i t
    | T_dep_pair_with_action _ i t _ ->
      let pi = dtyp_as_parser i in
      P.parse_dep_pair pi (fun (x:dtyp_as_type i) -> as_parser (t x))

    | T_refine _ base refinement _
    | T_refine_with_action _ base refinement _ _ ->
      let pi = dtyp_as_parser base in
      P.parse_filter pi refinement

    | T_dep_pair_with_refinement _ base refinement _ k ->
      P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x)))

    | T_dep_pair_with_refinement_and_action _ base refinement _ k _ ->
      P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x)))

    | T_if_else b t0 t1 ->
      let p0 (_:squash b) =
        P.parse_weaken_right (as_parser (t0())) _
      in
      let p1 (_:squash (not b)) =
        P.parse_weaken_left (as_parser (t1())) _
      in
      P.parse_ite b p0 p1

    | T_cases b t0 t1 ->
      let p0 (_:squash b) =
        P.parse_weaken_right (as_parser t0) _
      in
      let p1 (_:squash (not b)) =
        P.parse_weaken_left (as_parser t1) _
      in
      P.parse_ite b p0 p1

    | T_with_action _ t a ->
      as_parser t

    | T_with_dep_action _ i a ->
      dtyp_as_parser i

    | T_drop t ->
      as_parser t

    | T_with_comment _ t c ->
      as_parser t

    | T_nlist _fn n n_is_const _plconst t ->
      P.parse_nlist n n_is_const (as_parser t)

    | T_at_most _ n t ->
      P.parse_t_at_most n (as_parser t)

    | T_exact _ n t ->
      P.parse_t_exact n (as_parser t)

    | T_string _ elt_t terminator ->
      P.parse_string (dtyp_as_parser elt_t) terminator

[@@specialize]
let rec as_reader
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
          (#[@@@erasable] d: state_dict)
          (#use_error_handler:bool)
          #nz (#pk:P.parser_kind nz P.WeakKindStrongPrefix) #ha
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha true)
  : leaf_reader #base_t #len_t #pos_t #inst (as_parser t)
  = match t with
    | T_denoted _n dt ->
      assert_norm (as_type (T_denoted #base_t #len_t #pos_t #inst #d #use_error_handler _n dt) == dtyp_as_type dt);
      assert_norm (as_parser (T_denoted #base_t #len_t #pos_t #inst #d #use_error_handler _n dt) == dtyp_as_parser dt);
      (| (), dtyp_as_leaf_reader dt |)
    | T_with_comment _n t _c ->
      assert_norm (as_type (T_with_comment #base_t #len_t #pos_t #inst #d #use_error_handler _n t _c) == as_type t);
      assert_norm (as_parser (T_with_comment #base_t #len_t #pos_t #inst #d #use_error_handler _n t _c) == as_parser t);
      as_reader t
    | T_false _n ->
      assert_norm (as_type (T_false #base_t #len_t #pos_t #inst #d #use_error_handler _n) == False);
      assert_norm (as_parser (T_false #base_t #len_t #pos_t #inst #d #use_error_handler _n) == P.parse_impos());
      (| (), A.read_impos () |)

(* Spec denotation of `typ`: the purely functional specification of the
   validator denotation, including the effect of its actions on the action
   state. It mirrors the control flow of `as_validator`, including the
   choices of fast paths.

   Like `as_validator`, it takes the name of the enclosing type, on which the
   actions of `T_with_dep_action` may depend. *)
let rec as_vspec
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          (typename: string)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : Tot (S.vspec d)
        (decreases t)
  = match t with
    | T_false _ ->
      S.vspec_of_parser (P.parse_impos ())

    | T_denoted _ td ->
      dtyp_as_vspec td

    | T_pair _ #_ #_ #ha1 #_ #_ #_ #_ #ha2 #_ k1_const t1 k2_const t2 ->
      S.vspec_pair (as_parser t1) k1_const ha1 (as_vspec typename t1)
                   (as_parser t2) k2_const ha2 (as_vspec typename t2)

    | T_dep_pair _ i t ->
      S.vspec_dep_pair (dtyp_as_parser i) (dtyp_as_vspec i) (fun x -> as_vspec typename (t x))

    | T_refine _ base f _ ->
      S.vspec_filter (dtyp_as_parser base) (dtyp_as_vspec base) f None

    | T_refine_with_action _ base f _ a ->
      S.vspec_filter (dtyp_as_parser base) (dtyp_as_vspec base) f
        (Some (fun x -> action_as_spec (a x)))

    | T_dep_pair_with_refinement _ #_ #_ #ha1 #_ #_ #_ #_ #_ base f _ k ->
      S.vspec_dep_pair_with_refinement_gen (not ha1)
        (dtyp_as_parser base) (dtyp_as_vspec base) f None
        (fun x -> as_vspec typename (k x))

    | T_dep_pair_with_action _ base t a ->
      S.vspec_dep_pair_with_action (dtyp_as_parser base) (dtyp_as_vspec base)
        (fun x -> action_as_spec (a x))
        (fun x -> as_vspec typename (t x))

    | T_dep_pair_with_refinement_and_action _ #_ #_ #ha1 #_ #_ #_ #_ #_ #_ #_ base f _ k a ->
      S.vspec_dep_pair_with_refinement_gen (not ha1)
        (dtyp_as_parser base) (dtyp_as_vspec base) f
        (Some (fun x -> action_as_spec (a x)))
        (fun x -> as_vspec typename (k x))

    | T_if_else b t0 t1 ->
      S.vspec_ite b (fun _ -> as_vspec typename (t0 ())) (fun _ -> as_vspec typename (t1 ()))

    | T_cases b t0 t1 ->
      S.vspec_ite b (fun _ -> as_vspec typename t0) (fun _ -> as_vspec typename t1)

    | T_with_action _ t a ->
      S.vspec_with_success_action (as_parser t) (as_vspec typename t) (action_as_spec a)

    | T_with_dep_action _ i a ->
      S.vspec_with_dep_action (dtyp_as_parser i) (dtyp_as_vspec i) (fun x -> action_as_spec (a typename x))

    | T_drop t ->
      as_vspec typename t

    | T_with_comment _ t _ ->
      as_vspec typename t

    | T_nlist _ n n_is_const _ t ->
      S.vspec_nlist ha n n_is_const (as_parser t) (as_vspec typename t)

    | T_at_most _ n t ->
      S.vspec_t_at_most n (as_vspec typename t)

    | T_exact _ n t ->
      S.vspec_t_exact n (as_parser t) (as_vspec typename t)

    | T_string _ elt_t terminator ->
      S.vspec_string ha (dtyp_as_parser elt_t) terminator (dtyp_as_vspec elt_t)

(* Value-level spec denotation of `typ`: the effect of the actions of a
   type, as a function of the parsed value (see
   `EverParse3d.Actions.ValueSpec`). *)
let rec as_value_spec
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          (typename: string)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : Tot (VS.value_spec d (as_type t))
        (decreases t)
  = match t returns Tot (VS.value_spec d (as_type t)) with
    | T_false _ ->
      VS.vs_true

    | T_denoted _ td ->
      dtyp_as_value_spec td

    | T_pair _ _ t1 _ t2 ->
      VS.vs_pair (as_parser t1) (as_value_spec typename t1) (as_value_spec typename t2)

    | T_dep_pair _ i t ->
      VS.vs_dep_pair (dtyp_as_parser i) (dtyp_as_value_spec i) (fun x -> as_value_spec typename (t x))

    | T_refine _ base f _ ->
      VS.vs_filter (dtyp_as_value_spec base) f None

    | T_refine_with_action _ base f _ a ->
      VS.vs_filter (dtyp_as_value_spec base) f (Some (fun x -> action_as_spec (a x)))

    | T_dep_pair_with_refinement _ base f _ k ->
      VS.vs_dep_pair_with_refinement (dtyp_as_parser base) (dtyp_as_value_spec base) f None
        (fun x -> as_value_spec typename (k x))

    | T_dep_pair_with_action _ base t a ->
      VS.vs_dep_pair_with_action (dtyp_as_parser base) (dtyp_as_value_spec base)
        (fun x -> action_as_spec (a x))
        (fun x -> as_value_spec typename (t x))

    | T_dep_pair_with_refinement_and_action _ base f _ k a ->
      VS.vs_dep_pair_with_refinement (dtyp_as_parser base) (dtyp_as_value_spec base) f
        (Some (fun x -> action_as_spec (a x)))
        (fun x -> as_value_spec typename (k x))

    | T_if_else b t0 t1 ->
      VS.vs_ite b (fun _ -> as_value_spec typename (t0 ())) (fun _ -> as_value_spec typename (t1 ()))

    | T_cases b t0 t1 ->
      VS.vs_ite b (fun _ -> as_value_spec typename t0) (fun _ -> as_value_spec typename t1)

    | T_with_action _ t a ->
      VS.vs_with_action (as_value_spec typename t) (action_as_spec a)

    | T_with_dep_action _ i a ->
      VS.vs_with_dep_action (dtyp_as_value_spec i) (fun x -> action_as_spec (a typename x))

    | T_drop t ->
      as_value_spec typename t

    | T_with_comment _ t _ ->
      as_value_spec typename t

    | T_nlist _ n _ _ t ->
      VS.vs_nlist n (as_parser t) (as_value_spec typename t)

    | T_at_most _ n t ->
      VS.vs_t_at_most n (as_value_spec typename t)

    | T_exact _ n t ->
      VS.vs_t_exact n (as_value_spec typename t)

    | T_string _ elt_t terminator ->
      VS.vs_string (dtyp_as_parser elt_t) terminator (dtyp_as_value_spec elt_t)

let kind_of_typ
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : P.parser_kind nz wk
  = pk

let has_action_of_typ
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : bool
  = ha

let kind_of_typ_f
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          (#a: Type)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t: a -> typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : P.parser_kind nz wk
  = pk

let has_action_of_typ_f
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          (#a: Type)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t: a -> typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : bool
  = ha

(* The value-level spec denotation is refined by the spec denotation. *)
#push-options "--z3rlimit 32"
#restart-solver
let rec as_vspec_wf
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          (typename: string)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : Lemma
    (ensures (VS.vspec_wf ha (as_parser t) (as_vspec typename t) (as_value_spec typename t)))
    (decreases t)
  = match t with
    | T_false _ ->
      VS.wf_of_parser #d false (P.parse_impos ())

    | T_denoted _ td ->
      dtyp_wf td

    | T_pair _ #_ #_ #ha1 #_ #_ #_ #_ #ha2 #_ k1_const t1 k2_const t2 ->
      as_vspec_wf typename t1;
      as_vspec_wf typename t2;
      VS.wf_pair (as_parser t1) k1_const ha1 (as_vspec typename t1) (as_value_spec typename t1)
                 (as_parser t2) k2_const ha2 (as_vspec typename t2) (as_value_spec typename t2)

    | T_dep_pair fldname #_ #_ #ha1 #_ #_ #_ #ha2 i t ->
      dtyp_wf i;
      assert_norm (as_type (T_dep_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname i t) == x:dtyp_as_type i & as_type (t x));
      assert_norm (as_parser (T_dep_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname i t) == P.parse_dep_pair (dtyp_as_parser i) (fun (x:dtyp_as_type i) -> as_parser (t x)));
      assert_norm (as_vspec typename (T_dep_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname i t) == S.vspec_dep_pair (dtyp_as_parser i) (dtyp_as_vspec i) (fun x -> as_vspec typename (t x)));
      assert_norm (as_value_spec typename (T_dep_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname i t) == VS.vs_dep_pair (dtyp_as_parser i) (dtyp_as_value_spec i) (fun x -> as_value_spec typename (t x)));
      let aux (x: dtyp_as_type i) : Lemma (VS.vspec_wf ha2 (as_parser (t x)) (as_vspec typename (t x)) (as_value_spec typename (t x))) =
        as_vspec_wf typename (t x)
      in
      Classical.forall_intro aux;
      VS.wf_dep_pair (dtyp_as_parser i) ha1 (dtyp_as_vspec i) (dtyp_as_value_spec i)
        (fun x -> as_parser (t x)) ha2 (fun x -> as_vspec typename (t x)) (fun x -> as_value_spec typename (t x))

    | T_refine fldname #_ #_ #ha1 base f err ->
      dtyp_wf base;
      assert_norm (as_type (T_refine #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err) == P.refine (dtyp_as_type base) f);
      assert_norm (as_parser (T_refine #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err) == P.parse_filter (dtyp_as_parser base) f);
      assert_norm (as_vspec typename (T_refine #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err) == S.vspec_filter (dtyp_as_parser base) (dtyp_as_vspec base) f None);
      assert_norm (as_value_spec typename (T_refine #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err) == VS.vs_filter (dtyp_as_value_spec base) f None);
      VS.wf_filter ha1 (dtyp_as_parser base) (dtyp_as_vspec base) (dtyp_as_value_spec base) f None

    | T_refine_with_action fldname #_ #_ #ha1 base f err a ->
      dtyp_wf base;
      assert_norm (as_type (T_refine_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err a) == P.refine (dtyp_as_type base) f);
      assert_norm (as_parser (T_refine_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err a) == P.parse_filter (dtyp_as_parser base) f);
      assert_norm (as_vspec typename (T_refine_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err a) == S.vspec_filter (dtyp_as_parser base) (dtyp_as_vspec base) f (Some (fun x -> action_as_spec (a x))));
      assert_norm (as_value_spec typename (T_refine_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err a) == VS.vs_filter (dtyp_as_value_spec base) f (Some (fun x -> action_as_spec (a x))));
      VS.wf_filter ha1 (dtyp_as_parser base) (dtyp_as_vspec base) (dtyp_as_value_spec base) f
        (Some (fun x -> action_as_spec (a x)))

    | T_dep_pair_with_refinement fldname #_ #_ #ha1 #_ #_ #_ #ha2 #_ base f err k ->
      dtyp_wf base;
      assert_norm (as_type (T_dep_pair_with_refinement #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err k) == x:P.refine (dtyp_as_type base) f & as_type (k x));
      assert_norm (as_parser (T_dep_pair_with_refinement #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err k) == P.parse_dep_pair (P.parse_filter (dtyp_as_parser base) f) (fun x -> as_parser (k x)));
      assert_norm (as_vspec typename (T_dep_pair_with_refinement #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err k) == S.vspec_dep_pair_with_refinement_gen (not ha1) (dtyp_as_parser base) (dtyp_as_vspec base) f None (fun x -> as_vspec typename (k x)));
      assert_norm (as_value_spec typename (T_dep_pair_with_refinement #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err k) == VS.vs_dep_pair_with_refinement (dtyp_as_parser base) (dtyp_as_value_spec base) f None (fun x -> as_value_spec typename (k x)));
      let aux (x: P.refine (dtyp_as_type base) f) : Lemma (VS.vspec_wf ha2 (as_parser (k x)) (as_vspec typename (k x)) (as_value_spec typename (k x))) =
        as_vspec_wf typename (k x)
      in
      Classical.forall_intro aux;
      VS.wf_dep_pair_with_refinement (dtyp_as_parser base) ha1 (dtyp_as_vspec base) (dtyp_as_value_spec base) f None
        (fun x -> as_parser (k x)) ha2 (fun x -> as_vspec typename (k x)) (fun x -> as_value_spec typename (k x))

    | T_dep_pair_with_action fldname #_ #_ #ha1 #_ #_ #_ #ha2 base t a ->
      dtyp_wf base;
      assert_norm (as_type (T_dep_pair_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base t a) == x:dtyp_as_type base & as_type (t x));
      assert_norm (as_parser (T_dep_pair_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base t a) == P.parse_dep_pair (dtyp_as_parser base) (fun (x:dtyp_as_type base) -> as_parser (t x)));
      assert_norm (as_vspec typename (T_dep_pair_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base t a) == S.vspec_dep_pair_with_action (dtyp_as_parser base) (dtyp_as_vspec base) (fun x -> action_as_spec (a x)) (fun x -> as_vspec typename (t x)));
      assert_norm (as_value_spec typename (T_dep_pair_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base t a) == VS.vs_dep_pair_with_action (dtyp_as_parser base) (dtyp_as_value_spec base) (fun x -> action_as_spec (a x)) (fun x -> as_value_spec typename (t x)));
      let aux (x: dtyp_as_type base) : Lemma (VS.vspec_wf ha2 (as_parser (t x)) (as_vspec typename (t x)) (as_value_spec typename (t x))) =
        as_vspec_wf typename (t x)
      in
      Classical.forall_intro aux;
      VS.wf_dep_pair_with_action (dtyp_as_parser base) ha1 (dtyp_as_vspec base) (dtyp_as_value_spec base)
        (fun x -> action_as_spec (a x))
        (fun x -> as_parser (t x)) ha2 (fun x -> as_vspec typename (t x)) (fun x -> as_value_spec typename (t x))

    | T_dep_pair_with_refinement_and_action fldname #_ #_ #ha1 #_ #_ #_ #ha2 #_ base f err k a ->
      dtyp_wf base;
      assert_norm (as_type (T_dep_pair_with_refinement_and_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err k a) == x:P.refine (dtyp_as_type base) f & as_type (k x));
      assert_norm (as_parser (T_dep_pair_with_refinement_and_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err k a) == P.parse_dep_pair (P.parse_filter (dtyp_as_parser base) f) (fun x -> as_parser (k x)));
      assert_norm (as_vspec typename (T_dep_pair_with_refinement_and_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err k a) == S.vspec_dep_pair_with_refinement_gen (not ha1) (dtyp_as_parser base) (dtyp_as_vspec base) f (Some (fun x -> action_as_spec (a x))) (fun x -> as_vspec typename (k x)));
      assert_norm (as_value_spec typename (T_dep_pair_with_refinement_and_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base f err k a) == VS.vs_dep_pair_with_refinement (dtyp_as_parser base) (dtyp_as_value_spec base) f (Some (fun x -> action_as_spec (a x))) (fun x -> as_value_spec typename (k x)));
      let aux (x: P.refine (dtyp_as_type base) f) : Lemma (VS.vspec_wf ha2 (as_parser (k x)) (as_vspec typename (k x)) (as_value_spec typename (k x))) =
        as_vspec_wf typename (k x)
      in
      Classical.forall_intro aux;
      VS.wf_dep_pair_with_refinement (dtyp_as_parser base) ha1 (dtyp_as_vspec base) (dtyp_as_value_spec base) f
        (Some (fun x -> action_as_spec (a x)))
        (fun x -> as_parser (k x)) ha2 (fun x -> as_vspec typename (k x)) (fun x -> as_value_spec typename (k x))

    | T_if_else b t0 t1 ->
      let pk1 = kind_of_typ_f t0 in
      let pk2 = kind_of_typ_f t1 in
      let ha1 = has_action_of_typ_f t0 in
      let ha2 = has_action_of_typ_f t1 in
      assert_norm (as_type (T_if_else #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == P.t_ite b (fun _ -> as_type (t0())) (fun _ -> as_type (t1 ())));
      let unfold p0 (_:squash b) = P.parse_weaken_right (as_parser (t0 ())) _ in
      let unfold p1 (_:squash (not b)) = P.parse_weaken_left (as_parser (t1 ())) _ in
      assert_norm (as_parser (T_if_else #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == P.parse_ite b p0 p1);
      assert_norm (as_vspec typename (T_if_else #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == S.vspec_ite b (fun _ -> as_vspec typename (t0 ())) (fun _ -> as_vspec typename (t1 ())));
      assert_norm (as_value_spec typename (T_if_else #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == VS.vs_ite b (fun _ -> as_value_spec typename (t0 ())) (fun _ -> as_value_spec typename (t1 ())));
      if b
      then begin
        as_vspec_wf typename (t0 ());
        VS.wf_ha ha1 ha (as_parser (t0 ())) (as_vspec typename (t0 ())) (as_value_spec typename (t0 ()));
        VS.wf_weaken_right ha (as_parser (t0 ())) (as_vspec typename (t0 ())) (as_value_spec typename (t0 ())) pk2
      end else begin
        as_vspec_wf typename (t1 ());
        VS.wf_ha ha2 ha (as_parser (t1 ())) (as_vspec typename (t1 ())) (as_value_spec typename (t1 ()));
        VS.wf_weaken_left ha (as_parser (t1 ())) (as_vspec typename (t1 ())) (as_value_spec typename (t1 ())) pk1
      end;
      VS.wf_ite ha b
        p0 p1
        (fun _ -> as_vspec typename (t0 ())) (fun _ -> as_vspec typename (t1 ()))
        (fun _ -> as_value_spec typename (t0 ())) (fun _ -> as_value_spec typename (t1 ()))

    | T_cases b t0 t1 ->
      let pk1 = kind_of_typ t0 in
      let pk2 = kind_of_typ t1 in
      let ha1 = has_action_of_typ t0 in
      let ha2 = has_action_of_typ t1 in
      assert_norm (as_type (T_cases #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == P.t_ite b (fun _ -> as_type t0) (fun _ -> as_type t1));
      let unfold p0 (_:squash b) = P.parse_weaken_right (as_parser t0) _ in
      let unfold p1 (_:squash (not b)) = P.parse_weaken_left (as_parser t1) _ in
      assert_norm (as_parser (T_cases #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == P.parse_ite b p0 p1);
      assert_norm (as_vspec typename (T_cases #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == S.vspec_ite b (fun _ -> as_vspec typename t0) (fun _ -> as_vspec typename t1));
      assert_norm (as_value_spec typename (T_cases #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == VS.vs_ite b (fun _ -> as_value_spec typename t0) (fun _ -> as_value_spec typename t1));
      if b
      then begin
        as_vspec_wf typename t0;
        VS.wf_ha ha1 ha (as_parser t0) (as_vspec typename t0) (as_value_spec typename t0);
        VS.wf_weaken_right ha (as_parser t0) (as_vspec typename t0) (as_value_spec typename t0) pk2
      end else begin
        as_vspec_wf typename t1;
        VS.wf_ha ha2 ha (as_parser t1) (as_vspec typename t1) (as_value_spec typename t1);
        VS.wf_weaken_left ha (as_parser t1) (as_vspec typename t1) (as_value_spec typename t1) pk1
      end;
      VS.wf_ite ha b
        p0 p1
        (fun _ -> as_vspec typename t0) (fun _ -> as_vspec typename t1)
        (fun _ -> as_value_spec typename t0) (fun _ -> as_value_spec typename t1)

    | T_with_action _ #_ #_ #_ #_ #ha1 t a ->
      as_vspec_wf typename t;
      VS.wf_with_action ha1 (as_parser t) (as_vspec typename t) (as_value_spec typename t) (action_as_spec a)

    | T_with_dep_action _ #_ #_ #ha1 i a ->
      dtyp_wf i;
      VS.wf_with_dep_action ha1 (dtyp_as_parser i) (dtyp_as_vspec i) (dtyp_as_value_spec i) (fun x -> action_as_spec (a typename x))

    | T_drop t ->
      as_vspec_wf typename t

    | T_with_comment _ t _ ->
      as_vspec_wf typename t

    | T_nlist _ n n_is_const _ t ->
      as_vspec_wf typename t;
      VS.wf_nlist ha n n_is_const (as_parser t) (as_vspec typename t) (as_value_spec typename t)

    | T_at_most _ n t ->
      as_vspec_wf typename t;
      VS.wf_t_at_most ha n (as_parser t) (as_vspec typename t) (as_value_spec typename t)

    | T_exact _ n t ->
      as_vspec_wf typename t;
      VS.wf_t_exact ha n (as_parser t) (as_vspec typename t) (as_value_spec typename t)

    | T_string _ elt_t terminator ->
      dtyp_wf elt_t;
      VS.wf_string ha (dtyp_as_parser elt_t) terminator (dtyp_as_vspec elt_t) (dtyp_as_value_spec elt_t)
#pop-options

(* Client-facing corollary: if the parser succeeds on the input with value
   `v`, then the spec of the validator is determined by the value-level spec
   of `v`. (If the parser fails, then the validator fails.) *)
let as_vspec_value_spec
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          (typename: string)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
          (i: S.vinput) (x: forevery_values d)
  : Lemma
    (requires (VS.vinput_ok i))
    (ensures (match P.parse (as_parser t) i.S.rest with
      | Some (v, _) -> as_vspec typename t i x == VS.vres_of_sres (as_value_spec typename t (S.venv i) v x)
      | None -> True))
  = as_vspec_wf typename t;
    VS.vspec_wf_elim ha (as_parser t) (as_vspec typename t) (as_value_spec typename t) i x

(* Weakening, as used by the code generated by the 3D frontend for `dtyp_X`. *)
let as_value_spec_weaken
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          (typename: string)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
          (d2: state_dict) (sq: squash (state_dict_weaken_prop d d2))
  : VS.value_spec d2 (as_type t)
  = VS.vs_weaken (as_value_spec typename t) d2 sq

let as_vspec_wf_weaken
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
          (#d: state_dict)
          (#use_error_handler:bool)
          (typename: string)
          #nz #wk (#pk:P.parser_kind nz wk) #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
          (d2: state_dict) (sq: squash (state_dict_weaken_prop d d2))
  : squash (VS.vspec_wf ha (as_parser t) (S.vspec_weaken (as_vspec typename t) d2 sq) (as_value_spec_weaken typename t d2 sq))
  = as_vspec_wf typename t;
    VS.wf_weaken ha (as_parser t) (as_vspec typename t) (as_value_spec typename t) d2 sq

(* The main result: a validator denotation of `typ`, related by construction
   to the parser and type denotations. *)
#push-options "--z3rlimit_factor 4 --z3cliopt 'smt.qi.eager_threshold=100'"
#restart-solver
[@@specialize]
let rec as_validator
          (#base_t #len_t #pos_t: Type0)
          (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
          (#[@@@erasable] d: state_dict)
          (#use_error_handler:bool)
          (ehm: error_handler #base_t #len_t #pos_t #inst)
          (typename:string)
          #nz #wk (#pk:P.parser_kind nz wk)
          #ha #b
          (t:typ base_t len_t pos_t inst d use_error_handler pk ha b)
  : Tot (A.validate_with_action_t #base_t #len_t #pos_t #inst #nz #wk #pk #(as_type t)
            (as_parser t)
            d
            ha b use_error_handler
            (as_vspec typename t))
        (decreases t)
  = match t
    returns Tot (A.validate_with_action_t #base_t #len_t #pos_t #inst #nz #wk #pk #(as_type t) (as_parser t) d ha b use_error_handler (as_vspec typename t))
    with
    | T_false fldname ->
      assert_norm (as_vspec typename (T_false #base_t #len_t #pos_t #inst #d #use_error_handler fldname) == S.vspec_of_parser (P.parse_impos ()));
      A.validate_with_error_handler_no_read ehm typename fldname (A.validate_impos_no_read #base_t #len_t #pos_t #inst #d #use_error_handler ())

    | T_denoted fldname td ->
      assert_norm (as_type (T_denoted #base_t #len_t #pos_t #inst #d #use_error_handler fldname td) == dtyp_as_type td);
      assert_norm (as_parser (T_denoted #base_t #len_t #pos_t #inst #d #use_error_handler fldname td) == dtyp_as_parser td);
      assert_norm (as_vspec typename (T_denoted #base_t #len_t #pos_t #inst #d #use_error_handler fldname td) == dtyp_as_vspec td);
      A.validate_with_error_handler_gen ehm typename fldname _
        (A.validate_eta_gen _ (dtyp_as_validator fldname td))

    | T_pair fldname #_ #_ #ha1 #_ #_ #_ #_ #ha2 #_ k1_const t1 k2_const t2 ->
      assert_norm (as_vspec typename (T_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname k1_const t1 k2_const t2) ==
                   S.vspec_pair (as_parser t1) k1_const ha1 (as_vspec typename t1) (as_parser t2) k2_const ha2 (as_vspec typename t2));
      assert_norm (as_type (T_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname k1_const t1 k2_const t2) == as_type t1 & as_type t2);
      assert_norm (as_parser (T_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname k1_const t1 k2_const t2) == P.parse_pair (as_parser t1) (as_parser t2));
      A.validate_pair ehm typename fldname
          k1_const
          (A.validate_without_reading_gen _ (as_validator ehm typename t1))
          k2_const
          (A.validate_without_reading_gen _ (as_validator ehm typename t2))

    | T_dep_pair fldname i t ->
      assert_norm (as_type (T_dep_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname i t) == x:dtyp_as_type i & as_type (t x));
      assert_norm (as_parser (T_dep_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname i t) ==
                   P.parse_dep_pair (dtyp_as_parser i) (fun (x:dtyp_as_type i) -> as_parser (t x)));
      assert_norm (as_vspec typename (T_dep_pair #base_t #len_t #pos_t #inst #d #use_error_handler fldname i t) ==
                   S.vspec_dep_pair (dtyp_as_parser i) (dtyp_as_vspec i) (fun x -> as_vspec typename (t x)));
      A.validate_dep_pair fldname
          (A.validate_with_error_handler_no_read ehm typename fldname (dtyp_as_validator_no_read fldname i))
          (dtyp_as_leaf_reader i)
          (fun x -> A.validate_without_reading_gen _ (as_validator ehm typename (t x)))

    | T_refine fldname #_ #_ #ha1 t f err ->
      assert_norm (as_type (T_refine #base_t #len_t #pos_t #inst #d #use_error_handler fldname t f err) == P.refine (dtyp_as_type t) f);
      assert_norm (as_parser (T_refine #base_t #len_t #pos_t #inst #d #use_error_handler fldname t f err) == P.parse_filter (dtyp_as_parser t) f);
      assert_norm (as_vspec typename (T_refine #base_t #len_t #pos_t #inst #d #use_error_handler fldname t f err) == S.vspec_filter (dtyp_as_parser t) (dtyp_as_vspec t) f None);
      let v2 : A.validate_with_action_read (P.parse_filter (dtyp_as_parser t) f) d ha1 use_error_handler (S.vspec_filter (dtyp_as_parser t) (dtyp_as_vspec t) f None) =
        A.validate_filter fldname (dtyp_as_validator_no_read fldname t)
          (dtyp_as_leaf_reader t)
          f err "reading field_value" "checking constraint" in
      A.validate_with_error_handler ehm typename fldname v2

    | T_refine_with_action fldname t f err a ->
      assert_norm (as_type (T_refine_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname t f err a) == P.refine (dtyp_as_type t) f);
      assert_norm (as_parser (T_refine_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname t f err a) == P.parse_filter (dtyp_as_parser t) f);
      assert_norm (as_vspec typename (T_refine_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname t f err a) ==
                   S.vspec_filter (dtyp_as_parser t) (dtyp_as_vspec t) f (Some (fun x -> action_as_spec (a x))));
      let v2 : A.validate_with_action_read (P.parse_filter (dtyp_as_parser t) f) d true use_error_handler
                 (S.vspec_filter (dtyp_as_parser t) (dtyp_as_vspec t) f (Some (fun x -> action_as_spec (a x)))) =
        A.validate_filter_with_action fldname
          (dtyp_as_validator_no_read fldname t)
          (dtyp_as_leaf_reader t)
          f err "reading field_value" "checking constraint"
          (fun x -> action_as_action (a x)) in
      A.validate_with_error_handler ehm typename fldname v2

    | T_dep_pair_with_refinement fldname #_ #_ #ha1 #_ #_ #_ #_ #_ base refinement err k ->
      assert_norm (as_type (T_dep_pair_with_refinement #base_t #len_t #pos_t #inst #d #use_error_handler fldname base refinement err k) ==
                        x:P.refine (dtyp_as_type base) refinement & as_type (k x));
      assert_norm (as_parser (T_dep_pair_with_refinement #base_t #len_t #pos_t #inst #d #use_error_handler fldname base refinement err k) ==
                        P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x))));
      assert_norm (as_vspec typename (T_dep_pair_with_refinement #base_t #len_t #pos_t #inst #d #use_error_handler fldname base refinement err k) ==
                   S.vspec_dep_pair_with_refinement_gen (not ha1) (dtyp_as_parser base) (dtyp_as_vspec base) refinement None (fun x -> as_vspec typename (k x)));
      let v2 : A.validate_with_action_read P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x))) d ha use_error_handler
                 (S.vspec_dep_pair_with_refinement_gen (not ha1) (dtyp_as_parser base) (dtyp_as_vspec base) refinement None (fun x -> as_vspec typename (k x))) =
        A.validate_dep_pair_with_refinement (not ha1) fldname
            (dtyp_as_validator_no_read fldname base)
            (dtyp_as_leaf_reader base)
            refinement err
            (fun x -> A.validate_without_reading_gen _ (as_validator ehm typename (k x))) in
      A.validate_with_error_handler ehm typename fldname v2

    | T_dep_pair_with_action fldname base t act ->
      assert_norm (as_type (T_dep_pair_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base t act) ==
                        x:dtyp_as_type base & as_type (t x));
      assert_norm (as_parser (T_dep_pair_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base t act) ==
                        P.(dtyp_as_parser base `parse_dep_pair` (fun x -> as_parser (t x))));
      assert_norm (as_vspec typename (T_dep_pair_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base t act) ==
                   S.vspec_dep_pair_with_action (dtyp_as_parser base) (dtyp_as_vspec base) (fun x -> action_as_spec (act x)) (fun x -> as_vspec typename (t x)));
      A.validate_with_error_handler ehm typename fldname
        (A.validate_dep_pair_with_action
            (dtyp_as_validator_no_read fldname base)
            (dtyp_as_leaf_reader base)
            (fun x -> action_as_action (act x))
            (fun x -> A.validate_without_reading_gen _ (as_validator ehm typename (t x))))

    | T_dep_pair_with_refinement_and_action fldname #_ #_ #ha1 #_ #_ #_ #_ #_ #_ #_ base refinement err k act ->
      assert_norm (as_type (T_dep_pair_with_refinement_and_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base refinement err k act) ==
                        x:P.refine (dtyp_as_type base) refinement & as_type (k x));
      assert_norm (as_parser (T_dep_pair_with_refinement_and_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base refinement err k act) ==
                        P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x))));
      assert_norm (as_vspec typename (T_dep_pair_with_refinement_and_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname base refinement err k act) ==
                   S.vspec_dep_pair_with_refinement_gen (not ha1) (dtyp_as_parser base) (dtyp_as_vspec base) refinement
                     (Some (fun x -> action_as_spec (act x))) (fun x -> as_vspec typename (k x)));
      let v2 : A.validate_with_action_read P.((dtyp_as_parser base `parse_filter` refinement) `parse_dep_pair` (fun x -> as_parser (k x))) d true use_error_handler
                 (S.vspec_dep_pair_with_refinement_gen (not ha1) (dtyp_as_parser base) (dtyp_as_vspec base) refinement
                     (Some (fun x -> action_as_spec (act x))) (fun x -> as_vspec typename (k x))) =
        A.validate_dep_pair_with_refinement_and_action (not ha1) fldname
            (A.validate_with_error_handler_no_read ehm typename fldname
              (dtyp_as_validator_no_read fldname base))
            (dtyp_as_leaf_reader base)
            refinement err
            (fun x -> action_as_action (act x))
            (fun x -> A.validate_without_reading_gen _ (as_validator ehm typename (k x))) in
      v2

    | T_if_else b t0 t1 ->
      assert_norm (as_type (T_if_else #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == P.t_ite b (fun _ -> as_type (t0())) (fun _ -> as_type (t1 ())));
      let unfold p0 (_:squash b) = P.parse_weaken_right (as_parser (t0())) _ in
      let unfold p1 (_:squash (not b)) = P.parse_weaken_left (as_parser (t1())) _ in
      assert_norm (as_parser (T_if_else #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == P.parse_ite b p0 p1);
      assert_norm (as_vspec typename (T_if_else #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == S.vspec_ite b (fun _ -> as_vspec typename (t0 ())) (fun _ -> as_vspec typename (t1 ())));
      let v0 (_:squash b) =
        A.validate_weaken_right (A.validate_without_reading_gen _ (as_validator ehm typename (t0()))) _
      in
      let v1 (_:squash (not b)) =
        A.validate_weaken_left (A.validate_without_reading_gen _ (as_validator ehm typename (t1()))) _
      in
      A.validate_ite b p0 v0 p1 v1

    | T_cases b t0 t1 ->
      assert_norm (as_type (T_cases #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == P.t_ite b (fun _ -> as_type t0) (fun _ -> as_type t1));
      let unfold p0 (_:squash b) = P.parse_weaken_right (as_parser t0) _ in
      let unfold p1 (_:squash (not b)) = P.parse_weaken_left (as_parser t1) _ in
      assert_norm (as_parser (T_cases #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == P.parse_ite b p0 p1);
      assert_norm (as_vspec typename (T_cases #base_t #len_t #pos_t #inst #d #use_error_handler b t0 t1) == S.vspec_ite b (fun _ -> as_vspec typename t0) (fun _ -> as_vspec typename t1));
      let v0 (_:squash b) =
        A.validate_weaken_right (A.validate_without_reading_gen _ (as_validator ehm typename t0)) _
      in
      let v1 (_:squash (not b)) =
        A.validate_weaken_left (A.validate_without_reading_gen _ (as_validator ehm typename t1)) _
      in
      A.validate_ite b p0 v0 p1 v1

    | T_with_action fldname t a ->
      assert_norm (as_type (T_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname t a) == as_type t);
      assert_norm (as_parser (T_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname t a) == as_parser t);
      assert_norm (as_vspec typename (T_with_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname t a) == S.vspec_with_success_action (as_parser t) (as_vspec typename t) (action_as_spec a));
      A.validate_with_error_handler ehm typename fldname
        (A.validate_with_success_action fldname
          (A.validate_without_reading_gen _ (as_validator ehm typename t))
          (action_as_action a))

    | T_with_dep_action fldname i a ->
      assert_norm (as_type (T_with_dep_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname i a) == dtyp_as_type i);
      assert_norm (as_parser (T_with_dep_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname i a) == dtyp_as_parser i);
      assert_norm (as_vspec typename (T_with_dep_action #base_t #len_t #pos_t #inst #d #use_error_handler fldname i a) == S.vspec_with_dep_action (dtyp_as_parser i) (dtyp_as_vspec i) (fun x -> action_as_spec (a typename x)));
      A.validate_with_error_handler ehm typename fldname
        (A.validate_with_dep_action fldname
            (dtyp_as_validator_no_read fldname i)
            (dtyp_as_leaf_reader i)
            (fun x -> action_as_action (a typename x)))

    | T_drop t ->
      assert_norm (as_type (T_drop #base_t #len_t #pos_t #inst #d #use_error_handler t) == as_type t);
      assert_norm (as_parser (T_drop #base_t #len_t #pos_t #inst #d #use_error_handler t) == as_parser t);
      assert_norm (as_vspec typename (T_drop #base_t #len_t #pos_t #inst #d #use_error_handler t) == as_vspec typename t);
      A.validate_without_reading_gen _ (as_validator ehm typename t)

    | T_with_comment fldname t c ->
      assert_norm (as_type (T_with_comment #base_t #len_t #pos_t #inst #d #use_error_handler fldname t c) == as_type t);
      assert_norm (as_parser (T_with_comment #base_t #len_t #pos_t #inst #d #use_error_handler fldname t c) == as_parser t);
      assert_norm (as_vspec typename (T_with_comment #base_t #len_t #pos_t #inst #d #use_error_handler fldname t c) == as_vspec typename t);
      A.validate_with_comment_gen c _ (as_validator ehm typename t)

    | T_nlist fldname n n_is_const payload_is_constant_size t ->
      assert_norm (as_type (T_nlist #base_t #len_t #pos_t #inst #d #use_error_handler fldname n n_is_const payload_is_constant_size t) == P.nlist n (as_type t));
      assert_norm (as_parser (T_nlist #base_t #len_t #pos_t #inst #d #use_error_handler fldname n n_is_const payload_is_constant_size t) == P.parse_nlist n n_is_const (as_parser t));
      assert_norm (as_vspec typename (T_nlist #base_t #len_t #pos_t #inst #d #use_error_handler fldname n n_is_const payload_is_constant_size t) == S.vspec_nlist ha n n_is_const (as_parser t) (as_vspec typename t));
      let body = A.validate_without_reading_gen _ (as_validator ehm typename t) in
      (match ha
      returns (A.validate_with_action_read #base_t #len_t #pos_t (P.parse_nlist n n_is_const (as_parser t)) d ha use_error_handler (S.vspec_nlist ha n n_is_const (as_parser t) (as_vspec typename t)))
      with
      | true -> A.validate_with_error_handler ehm typename fldname (A.validate_nlist n n_is_const body)
      | false -> A.validate_with_error_handler ehm typename fldname
                    (A.validate_nlist_constant_size_without_actions n n_is_const payload_is_constant_size body))

    | T_at_most fldname n t ->
      assert_norm (as_type (T_at_most #base_t #len_t #pos_t #inst #d #use_error_handler fldname n t) == P.t_at_most n (as_type t));
      assert_norm (as_parser (T_at_most #base_t #len_t #pos_t #inst #d #use_error_handler fldname n t) == P.parse_t_at_most n (as_parser t));
      assert_norm (as_vspec typename (T_at_most #base_t #len_t #pos_t #inst #d #use_error_handler fldname n t) == S.vspec_t_at_most n (as_vspec typename t));
      A.validate_with_error_handler ehm typename fldname
        (A.validate_t_at_most n (A.validate_without_reading_gen _ (as_validator ehm typename t)))

    | T_exact fldname n t ->
      assert_norm (as_type (T_exact #base_t #len_t #pos_t #inst #d #use_error_handler fldname n t) == P.t_exact n (as_type t));
      assert_norm (as_parser (T_exact #base_t #len_t #pos_t #inst #d #use_error_handler fldname n t) == P.parse_t_exact n (as_parser t));
      assert_norm (as_vspec typename (T_exact #base_t #len_t #pos_t #inst #d #use_error_handler fldname n t) == S.vspec_t_exact n (as_parser t) (as_vspec typename t));
      A.validate_with_error_handler ehm typename fldname
        (A.validate_t_exact n (A.validate_without_reading_gen _ (as_validator ehm typename t)))

    | T_string fldname elt_t terminator ->
      assert_norm (as_type (T_string #base_t #len_t #pos_t #inst #d #use_error_handler fldname elt_t terminator) == P.cstring (dtyp_as_type elt_t) terminator);
      assert_norm (as_parser (T_string #base_t #len_t #pos_t #inst #d #use_error_handler fldname elt_t terminator) == P.parse_string (dtyp_as_parser elt_t) terminator);
      assert_norm (as_vspec typename (T_string #base_t #len_t #pos_t #inst #d #use_error_handler fldname elt_t terminator) == S.vspec_string ha (dtyp_as_parser elt_t) terminator (dtyp_as_vspec elt_t));
      A.validate_with_error_handler ehm typename fldname
        (A.validate_string (dtyp_as_validator_no_read fldname elt_t)
                           (dtyp_as_leaf_reader elt_t)
                           terminator)
#pop-options

////////////////////////////////////////////////////////////////////////////////
// Smart constructors and specialization
////////////////////////////////////////////////////////////////////////////////

[@@specialize]
let atomic_action_call
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
      (#[@@@erasable] d: state_dict)
      (#use_error_handler:bool)
      (#t:Type0)
      (#sp: S.action_spec d t)
      (a: A.action #base_t #len_t #pos_t #inst d t use_error_handler sp)
  : atomic_action base_t len_t pos_t inst d use_error_handler true false t
  = Action_call a

(* Same, but at `b = false`, for calls to external actions. Unlike
   `action_binding` in the Low* interpreter, the Pulse one is not indexed by
   `b`, so at those call sites `b` would otherwise be unsolvable. `false`
   is what the Low* `mk_action_binding` returns. *)
[@@specialize]
let atomic_action_call_extern
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
      (#[@@@erasable] d: state_dict)
      (#use_error_handler:bool)
      (#t:Type0)
      (#sp: S.action_spec d t)
      (a: A.action #base_t #len_t #pos_t #inst d t use_error_handler sp)
  : atomic_action base_t len_t pos_t inst d use_error_handler false false t
  = Action_call a

[@@specialize]
inline_for_extraction
let coerce (#[@@@erasable]a:Type)
           (#[@@@erasable]b:Type)
           ( [@@@erasable]pf:squash (a == b))
           (x:a)
  : b
  = x

(* Fix the (ghost) spec index of a validator. Used by generated code to
   determine the spec of `validate_X` when it is coerced into a `dtyp`. *)
[@@specialize]
inline_for_extraction
let with_vspec
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
      (#nz:_) (#wk:_) (#k:P.parser_kind nz wk) (#t:Type0) (#p:P.parser k t)
      (#[@@@erasable] d: state_dict)
      (#ha #ar #eh: bool)
      ([@@@erasable] s: S.vspec d)
      (v: A.validate_with_action_t #base_t #len_t #pos_t #inst p d ha ar eh s)
  : A.validate_with_action_t #base_t #len_t #pos_t #inst p d ha ar eh s
  = v

(* Probe-then-validate.

   This is deliberately *not* a constructor of `atomic_action`: the probed
   type lives at its own `state_dict` `es`, which must exclude the copy
   buffer's key, whereas the enclosing type lives at
   `state_dict_prod es (copy_buffer_state_dict dest_name dest)`. Storing `es`
   in the AST would raise the universe of `atomic_action`; binding it here, at
   the level of a top-level function, keeps everything in `Type u#1`.

   The disjointness argument `sq` is what rules out a nested probe reusing the
   same copy buffer: the inner type's dictionary would then already contain
   `dest_name`. It is a decidable computation over literal string keys. *)
[@@specialize]
let t_probe_then_validate
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#copy_buffer_t: Type0)
      (#cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t)
      (#boolean_t: Type0)
      {| boolean_inst: Bool.boolean_repr boolean_t |}
      (#use_error_handler:bool)
      (ehm: error_handler #base_t #len_t #pos_t #inst)
      (pointer_size:pointer_size_t)
      (nullable:bool)
      (fldname:string)
      (init_cb:PA.init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst #boolean_t #boolean_inst)
      (dest_sz:U64.t)
      (#mz:bool)
      (probe:PA.probe_m #_ #_ #_ #_ #inst #cb_inst #boolean_t #boolean_inst unit true mz use_error_handler)
      (dest_name:Ghost.erased string)
      (dest:copy_buffer_t)
      (as_u64:itype_as_type pointer_size -> PA.pure_external_action U64.t)
      (#nz #wk:_) (#pk:P.parser_kind nz wk)
      (#ha #has_reader:_)
      (#[@@@erasable] es: state_dict)
      (td:dtyp base_t len_t pos_t inst es use_error_handler pk ha has_reader)
      (sq: squash (forall x .
        ~ (es.state_p x /\
           (A.copy_buffer_state_dict #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst dest_name dest).state_p x)))
 : typ base_t len_t pos_t inst
       (state_dict_prod es (A.copy_buffer_state_dict #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst dest_name dest))
       use_error_handler
       (parser_kind_of_itype pointer_size)
       true
       false
 = T_with_dep_action fldname
     (DT_IType pointer_size)
     (fun typename src ->
        Atomic_action (atomic_action_call
          (A.probe_then_validate ehm typename fldname
             (A.validate_without_reading_gen has_reader (dtyp_as_validator fldname td))
             src as_u64 nullable dest_name dest init_cb dest_sz probe sq)))

[@@specialize]
let t_probe_then_validate_alt
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#copy_buffer_t: Type0)
      (#cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t)
      (#boolean_t: Type0)
      {| boolean_inst: Bool.boolean_repr boolean_t |}
      (#use_error_handler:bool)
      (ehm: error_handler #base_t #len_t #pos_t #inst)
      (pointer_size:pointer_size_t)
      (nullable:bool)
      (fldname:string)
      (init_cb:PA.init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst #boolean_t #boolean_inst)
      (dest_sz:U64.t)
      (#mz:bool)
      (probe:probe_action copy_buffer_t base_t len_t pos_t inst cb_inst boolean_t boolean_inst use_error_handler mz)
      (dest_name:Ghost.erased string)
      (dest:copy_buffer_t)
      (as_u64:itype_as_type pointer_size -> PA.pure_external_action U64.t)
      (#nz #wk:_) (#pk:P.parser_kind nz wk)
      (#ha #has_reader:_)
      (#[@@@erasable] es: state_dict)
      (td:dtyp base_t len_t pos_t inst es use_error_handler pk ha has_reader)
      (sq: squash (forall x .
        ~ (es.state_p x /\
           (A.copy_buffer_state_dict #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst dest_name dest).state_p x)))
 : typ base_t len_t pos_t inst
       (state_dict_prod es (A.copy_buffer_state_dict #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst dest_name dest))
       use_error_handler
       (parser_kind_of_itype pointer_size)
       true
       false
 = t_probe_then_validate ehm pointer_size nullable fldname init_cb dest_sz
     (probe_action_as_probe_m ehm probe) dest_name dest as_u64 td sq

(* `t_probe_then_validate` produces a `typ` at the dictionary
   `state_dict_prod es cb`, where `es` is the dictionary of the probed type and
   `cb` the singleton dictionary of the destination copy buffer. Every node of
   a `typ` tree, however, lives at one uniform ambient dictionary `d`. These
   generalized versions therefore take `d` explicitly, together with a proof
   that `state_dict_prod es cb` is a sub-dictionary of it, and weaken the
   underlying action accordingly. *)

[@@specialize]
let t_probe_then_validate_gen
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#copy_buffer_t: Type0)
      (#cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t)
      (#boolean_t: Type0)
      {| boolean_inst: Bool.boolean_repr boolean_t |}
      (#use_error_handler:bool)
      (ehm: error_handler #base_t #len_t #pos_t #inst)
      (pointer_size:pointer_size_t)
      (nullable:bool)
      (fldname:string)
      (init_cb:PA.init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst #boolean_t #boolean_inst)
      (dest_sz:U64.t)
      (#mz:bool)
      (probe:PA.probe_m #_ #_ #_ #_ #inst #cb_inst #boolean_t #boolean_inst unit true mz use_error_handler)
      (dest_name:Ghost.erased string)
      (dest:copy_buffer_t)
      (as_u64:itype_as_type pointer_size -> PA.pure_external_action U64.t)
      (#nz #wk:_) (#pk:P.parser_kind nz wk)
      (#ha #has_reader:_)
      ([@@@erasable] es: state_dict)
      (td:dtyp base_t len_t pos_t inst es use_error_handler pk ha has_reader)
      (sq: squash (forall x .
        ~ (es.state_p x /\
           (A.copy_buffer_state_dict #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst dest_name dest).state_p x)))
      ([@@@erasable] d: state_dict)
      (sq_weaken: squash (state_dict_weaken_prop
        (state_dict_prod es (A.copy_buffer_state_dict #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst dest_name dest))
        d))
 : typ base_t len_t pos_t inst d
       use_error_handler
       (parser_kind_of_itype pointer_size)
       true
       false
 = T_with_dep_action fldname
     (DT_IType pointer_size)
     (fun typename src ->
        Atomic_action (atomic_action_call
          (A.action_weaken
            (A.probe_then_validate ehm typename fldname
               (A.validate_without_reading_gen has_reader (dtyp_as_validator fldname td))
               src as_u64 nullable dest_name dest init_cb dest_sz probe sq)
            d
            sq_weaken)))

[@@specialize]
let t_probe_then_validate_alt_gen
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#copy_buffer_t: Type0)
      (#cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t)
      (#boolean_t: Type0)
      {| boolean_inst: Bool.boolean_repr boolean_t |}
      (#use_error_handler:bool)
      (ehm: error_handler #base_t #len_t #pos_t #inst)
      (pointer_size:pointer_size_t)
      (nullable:bool)
      (fldname:string)
      (init_cb:PA.init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst #boolean_t #boolean_inst)
      (dest_sz:U64.t)
      (#mz:bool)
      (probe:probe_action copy_buffer_t base_t len_t pos_t inst cb_inst boolean_t boolean_inst use_error_handler mz)
      (dest_name:Ghost.erased string)
      (dest:copy_buffer_t)
      (as_u64:itype_as_type pointer_size -> PA.pure_external_action U64.t)
      (#nz #wk:_) (#pk:P.parser_kind nz wk)
      (#ha #has_reader:_)
      ([@@@erasable] es: state_dict)
      (td:dtyp base_t len_t pos_t inst es use_error_handler pk ha has_reader)
      (sq: squash (forall x .
        ~ (es.state_p x /\
           (A.copy_buffer_state_dict #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst dest_name dest).state_p x)))
      ([@@@erasable] d: state_dict)
      (sq_weaken: squash (state_dict_weaken_prop
        (state_dict_prod es (A.copy_buffer_state_dict #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst dest_name dest))
        d))
 : typ base_t len_t pos_t inst d
       use_error_handler
       (parser_kind_of_itype pointer_size)
       true
       false
 = t_probe_then_validate_gen ehm pointer_size nullable fldname init_cb dest_sz
     (probe_action_as_probe_m ehm probe) dest_name dest as_u64 es td sq d sq_weaken

[@@noextract_to "krml"; specialize]
inline_for_extraction noextract
let validator_of
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
      ([@@@erasable] d: state_dict)
      (use_error_handler:bool)
      (typename: string)
      #ha #allow_reading #nz #wk (#k:P.parser_kind nz wk)
      (t:typ base_t len_t pos_t inst d use_error_handler k ha allow_reading)
  = A.validate_with_action_t #base_t #len_t #pos_t #inst
      (as_parser t)
      d
      ha
      allow_reading
      use_error_handler
      (as_vspec typename t)

[@@noextract_to "krml"; specialize]
inline_for_extraction noextract
let dtyp_of
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
      ([@@@erasable] d: state_dict)
      (use_error_handler:bool)
      #nz #wk (#k:P.parser_kind nz wk)
      #ha #b (t:typ base_t len_t pos_t inst d use_error_handler k ha b)
  = dtyp base_t len_t pos_t inst d use_error_handler k ha b

let specialization_steps =
  [nbe;
   zeta;
   primops;
   iota;
   delta_attr [`%specialize; `%EverParse3d.Actions.Common.specialize_backend];
   delta_only ([`%Some?;
                `%Some?.v;
                `%as_validator;
                `%nz_of_binding;
                `%wk_of_binding;
                `%pk_of_binding;
                `%has_action_of_binding;
                `%has_reader;
                `%type_of_binding;
                `%parser_of_binding;
                `%validator_of_binding;
                `%leaf_reader_of_binding;
                `%fst;
                `%snd;
                `%Mktuple2?._1;
                `%Mktuple2?._2]@projector_names)]

let specialize_tac steps (_:unit)
  : T.Tac unit
  = let open FStar.List.Tot in
    T.norm (steps@specialization_steps);
    T.trefl()

[@@specialize]
let mk_global_binding
      (#base_t #len_t #pos_t: Type0)
      (inst: I.input_stream_inst base_t len_t pos_t)
      ([@@@erasable] d: state_dict)
      (use_error_handler:bool)
      #nz #wk
      (pk:P.parser_kind nz wk)
      ([@@@erasable] p_t : Type0)
      ([@@@erasable] p_p : P.parser pk p_t)
      (p_reader: option (leaf_reader #base_t #len_t #pos_t #inst p_p))
      (#ha b:bool)
      (#[@@@erasable] p_s: S.vspec d)
      (p_v : A.validate_with_action_t #base_t #len_t #pos_t #inst p_p d ha b use_error_handler p_s)
      ([@@@erasable] pf:squash (b == Some? p_reader))
      ([@@@erasable] p_vs: VS.value_spec d p_t)
      ([@@@erasable] pf_wf: squash (VS.vspec_wf ha p_p p_s p_vs))
   : global_binding base_t len_t pos_t inst d use_error_handler
   = {
       parser_kind_nz = nz;
       parser_weak_kind = wk;
       parser_kind = pk;
       parser_has_action = ha;
       p_t = p_t;
       p_p = p_p;
       p_reader = p_reader;
       p_s = p_s;
       p_v = p_v;
       p_vs = p_vs;
       p_wf = pf_wf
     }

[@@specialize]
let mk_dt_app
      (#base_t #len_t #pos_t: Type0)
      (#inst: I.input_stream_inst base_t len_t pos_t)
      (#[@@@erasable] d: state_dict)
      (#use_error_handler:bool)
      #nz #wk (pk:P.parser_kind nz wk) (ha b:bool)
      (x:global_binding base_t len_t pos_t inst d use_error_handler)
      ([@@@erasable] pf:squash (nz == nz_of_binding x /\
                                wk == wk_of_binding x /\
                                pk == pk_of_binding x /\
                                ha == has_action_of_binding x /\
                                b == has_reader x))
    : dtyp base_t len_t pos_t inst d use_error_handler #nz #wk pk ha b
    = DT_App pk ha b x pf

[@@specialize]
let mk_dtyp_app
      (#base_t #len_t #pos_t: Type0)
      (inst: I.input_stream_inst base_t len_t pos_t)
      ([@@@erasable] d: state_dict)
      (use_error_handler:bool)
      #nz #wk
      (pk:P.parser_kind nz wk)
      ([@@@erasable] p_t : Type0)
      ([@@@erasable] p_p : P.parser pk p_t)
      (p_reader: option (leaf_reader #base_t #len_t #pos_t #inst p_p))
      (ha b:bool)
      (#[@@@erasable] p_s: S.vspec d)
      (p_v : A.validate_with_action_t #base_t #len_t #pos_t #inst p_p d ha b use_error_handler p_s)
      ([@@@erasable] pf:squash (b == Some? p_reader))
      ([@@@erasable] p_vs: VS.value_spec d p_t)
      ([@@@erasable] pf_wf: squash (VS.vspec_wf ha p_p p_s p_vs))
   : dtyp base_t len_t pos_t inst d use_error_handler #nz #wk pk ha b
   = let gb = {
       parser_kind_nz = nz;
       parser_weak_kind = wk;
       parser_kind = pk;
       parser_has_action = ha;
       p_t = p_t;
       p_p = p_p;
       p_reader = p_reader;
       p_s = p_s;
       p_v = p_v;
       p_vs = p_vs;
       p_wf = pf_wf
     } in
     DT_App pk ha b gb ()

//attribute to tag the state_dict indexes of type definitions
let specialize_state_dict = ()

let coerce_validator steps : T.Tac unit =
  let open FStar.List.Tot in
  T.norm [delta_only (steps @ [`%parser_kind_of_itype;
                               `%parser_kind_nz_of_itype;
                               `%fst;
                               `%snd;
                               `%Mktuple2?._1;
                               `%Mktuple2?._2;
                               `%coerce;
                               `%validator_of;
                               `%dtyp_of;
                              ]);
           delta_attr [`%specialize_state_dict];
           zeta;
           iota;
           primops];
  T.trefl()

let coerce_dt_app (steps:_) : T.Tac unit =
  let open FStar.List.Tot in
  T.norm [delta_only (steps@[`%nz_of_binding;
                        `%wk_of_binding;
                        `%pk_of_binding;
                        `%has_reader;
                        `%leaf_reader_of_binding;
                        `%mk_global_binding]@projector_names);
          zeta;
          iota;
          simplify];
  T.trivial()

(* Re-exported for the code generated by the 3D frontend, which opens
   `EverParse3d.Interpreter` but not `EverParse3d.ProbeActions`. *)
inline_for_extraction
noextract
let as_u64_identity = PA.as_u64_identity

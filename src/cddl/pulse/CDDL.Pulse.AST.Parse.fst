module CDDL.Pulse.AST.Parse
include CDDL.Pulse.AST.Base
include CDDL.Pulse.AST.Literal
include CDDL.Pulse.AST.Parse.ElemType
include CDDL.Pulse.Parse.ArrayGroup
include CDDL.Pulse.Parse.MapGroup
include CDDL.Pulse.AST.Types
include CDDL.Pulse.AST.Env
open Pulse.Lib.Pervasives
module Cbor = CBOR.Spec.API.Format
module Bundle = CDDL.Pulse.Bundle.Base // for bundle_attr

[@@sem_attr; Bundle.bundle_attr]
let ancillary_validate_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (se: sem_env)
= (t: typ { typ_bounded se.se_bound t}) -> option (impl_typ vmatch (typ_sem se t))

[@@sem_attr; Bundle.bundle_attr]
let ancillary_validate_env_bool
  (se: name_env)
= (t: typ { typ_bounded se t }) -> bool

[@@sem_attr; Bundle.bundle_attr]
let ancillary_validate_env_is_some
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#se: sem_env)
  (env: ancillary_validate_env vmatch se)
: Tot (ancillary_validate_env_bool se.se_bound)
= fun t -> Some? (env t)

[@@sem_attr; Bundle.bundle_attr]
let ancillary_validate_env_extend
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#se: sem_env)
  (env1: ancillary_validate_env vmatch se)
  (se2: sem_env {
    sem_env_included se se2
  })
: Tot (ancillary_validate_env vmatch se2)
= fun t ->
  if typ_bounded se.se_bound t
  then begin
    (env1 t)
  end
  else None

[@@sem_attr; Bundle.bundle_attr]
let ancillary_validate_env_set
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#se: sem_env)
  (env: ancillary_validate_env vmatch se)
  (t': typ { typ_bounded se.se_bound t'})
  (i: impl_typ vmatch (typ_sem se t'))
: Tot (ancillary_validate_env vmatch se)
= fun t ->
  if t = t'
  then Some i
  else env t

[@@sem_attr]
let ancillary_parse_env_bool
  (se: sem_env)
= (t: typ) -> (t_wf: ast0_wf_typ t { spec_wf_typ se true t t_wf }) -> bool

[@@sem_attr]
let ancillary_parse_array_group_env_bool
  (se: sem_env)
= (t: group) -> (t_wf: ast0_wf_array_group t { spec_wf_array_group se t t_wf }) -> bool

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module I64 = FStar.Int64
module V = CDDL.Pulse.AST.Validate
module SZ = FStar.SizeT

[@@base_attr]
noeq
type ask_for' =
| AskForType: t: typ -> t_wf: ast0_wf_typ t -> bool -> ask_for'
| AskForArrayGroup: t: group -> t_wf: ast0_wf_array_group t -> ask_for'

let ask_for_spec
  (se: sem_env)
  (a: ask_for')
: Tot prop
= match a with
  | AskForType t t_wf guarded -> spec_wf_typ se guarded t t_wf
  | AskForArrayGroup t t_wf -> spec_wf_array_group se t t_wf

let ask_for
  (se: sem_env)
= (a: ask_for' { ask_for_spec se a })

[@@base_attr]
let option_ask_for_is_type
  (v_sem_env: sem_env)
  (a: option (ask_for v_sem_env))
: Tot prop
= match a with
  | Some (AskForType _ _ _) -> True
  | _ -> False

[@@sem_attr]
let validate_ask_for_type
  (#t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (#v_sem_env: sem_env)
  (env: validator_env vmatch v_sem_env { SZ.fits_u64 })
  (a: option (ask_for v_sem_env))
  (sq: squash (option_ask_for_is_type v_sem_env a))
: impl_typ vmatch (typ_sem v_sem_env (AskForType?.t (Some?.v a)))
= let Some (AskForType t t_wf guarded) = a in
  V.validate_typ impl env guarded t t_wf

[@@sem_attr; Bundle.bundle_attr]
let ancillary_validate_env_set_ask_for
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#se: sem_env)
  (env: ancillary_validate_env vmatch se)
  (a: option (ask_for se))
  (sq: squash (option_ask_for_is_type se a))
  (i: impl_typ vmatch (typ_sem se (AskForType?.t (Some?.v a))))
: Tot (ancillary_validate_env vmatch se)
= ancillary_validate_env_set env _ i

[@@base_attr]
let option_ask_for_is_array_group
  (v_sem_env: sem_env)
  (a: option (ask_for v_sem_env))
: Tot prop
= match a with
  | Some (AskForArrayGroup _ _) -> True
  | _ -> False

[@@sem_attr]
let validate_ask_for_array_group
  (#t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (#v_sem_env: sem_env)
  (env: validator_env vmatch v_sem_env { SZ.fits_u64 })
  (a: option (ask_for v_sem_env))
  (sq: squash (option_ask_for_is_array_group v_sem_env a))
: impl_array_group cbor_array_iterator_match (array_group_sem v_sem_env (AskForArrayGroup?.t (Some?.v a)))
= let Some (AskForArrayGroup t t_wf) = a in
  V.validate_array_group impl env t t_wf

#push-options "--z3rlimit 1024 --query_stats"

#restart-solver

[@@Bundle.bundle_attr]
let rec ask_zero_copy_wf_type
  (#se: sem_env)
  (ancillary_v: ancillary_validate_env_bool se.se_bound)
  (ancillary: ancillary_parse_env_bool se)
  (ancillary_ag: ancillary_parse_array_group_env_bool se)
  (#t: typ)
  (t_wf: ast0_wf_typ t {
    spec_wf_typ se true t t_wf
  })
: Tot (option (ask_for se))
    (decreases t_wf)
= match t_wf with
  | WfTRewrite _ _ s ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag s
  | WfTTagged tg _ s ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag s
  | WfTChoice _ _ s1 s2 ->
    begin match ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag s1 with
    | Some ask -> Some ask
    | _ -> ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag s2
    end
  | WfTElem e -> None
  | WfTDetCbor _ _ s ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag s
  | WfTStrSize k _ _ lo hi -> None
  | WfTIntRange _ _ _ lo hi -> None
  | WfTDef n -> None
  | WfTArray _ s ->
    ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag s
  | WfTMap _ _ s ->
    ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag s

and ask_zero_copy_wf_array_group
  (#se: sem_env)
  (ancillary_v: ancillary_validate_env_bool se.se_bound)
  (ancillary: ancillary_parse_env_bool se)
  (ancillary_ag: ancillary_parse_array_group_env_bool se)
  (#t: group)
  (t_wf: ast0_wf_array_group t {
    spec_wf_array_group se t t_wf
  })
: Tot (option (ask_for se))
    (decreases t_wf)
= match t_wf with
  | WfAElem _ _ _ t_wf' ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag t_wf'
  | WfAZeroOrOne _ t_wf' ->
    ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag t_wf'
  | WfAZeroOrOneOrMore _ t_wf' g' ->
    // HERE I need function pointers, so I MUST NOT do a recursive call
    if ancillary_ag _ t_wf'
    then None
    else Some (AskForArrayGroup _ t_wf')
  | WfAConcat _ _ t_wf1 t_wf2 ->
    begin match ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag t_wf1 with
    | Some ask -> Some ask
    | None ->
      ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag t_wf2
    end
  | WfAChoice _ _ t_wf1 t_wf2 ->
    begin match ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag t_wf1 with
    | Some ask -> Some ask
    | None ->
      ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag t_wf2
    end
  | WfARewrite _ _ t_wf2 ->
    ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag t_wf2

and ask_zero_copy_wf_map_group
  (#se: sem_env)
  (ancillary_v: ancillary_validate_env_bool se.se_bound)
  (ancillary: ancillary_parse_env_bool se)
  (ancillary_ag: ancillary_parse_array_group_env_bool se)
  (#t: elab_map_group)
  (t_wf: ast0_wf_parse_map_group t {
    spec_wf_parse_map_group se t t_wf
  })
: Tot (option (ask_for se))
    (decreases t_wf)
= match t_wf with
  | WfMChoice _ s1 _ s2 ->
    begin match ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag s1 with
    | Some a -> Some a
    | None ->
      ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag s2
    end
  | WfMConcat _ s1 _ s2 ->
    begin match ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag s1 with
    | Some a -> Some a
    | None ->
      ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag s2
    end
  | WfMZeroOrOne _ s1 ->
    ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag s1
  | WfMLiteral cut key _ s ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag s
  | WfMZeroOrMore _ key_except _ s_key s_key_except s_value ->
    if not (ancillary _ s_key)
    then Some (AskForType _ s_key true)
    else if not (ancillary_v key_except)
    then Some (AskForType _ s_key_except false)
    else if not (ancillary _ s_value)
    then Some (AskForType _ s_value true)
    else None

[@@base_attr]
let option_ask_for_is_guarded_type
  (v_sem_env: sem_env)
  (a: option (ask_for v_sem_env))
: Tot prop
= match a with
  | Some (AskForType _ _ true) -> True
  | _ -> False

let option_ask_for_is_guarded_type_is_type
  (v_sem_env: sem_env)
  (a: option (ask_for v_sem_env))
: Lemma
  (requires (option_ask_for_is_guarded_type v_sem_env a))
  (ensures (option_ask_for_is_type v_sem_env a))
  [SMTPat (option_ask_for_is_guarded_type v_sem_env a)]
= ()

[@@Bundle.bundle_attr]
let ask_zero_copy_ask_for_option
  (#se: sem_env)
  (ancillary_v: ancillary_validate_env_bool se.se_bound)
  (ancillary: ancillary_parse_env_bool se)
  (ancillary_ag: ancillary_parse_array_group_env_bool se)
  (a: option (ask_for se))
: Tot (option (ask_for se))
= match a with
  | None -> None
  | Some (AskForType _ _ false) -> None
  | Some (AskForType t t_wf _) ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag t_wf
  | Some (AskForArrayGroup t t_wf) ->
    ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag t_wf

#pop-options

module CDDL.Pulse.AST.Ancillaries
include CDDL.Pulse.Attr
include CDDL.Spec.AST.Base

[@@sem_attr; bundle_attr]
let ancillary_validate_env_bool
  (se: name_env)
= (t: typ { typ_bounded se t }) -> bool

[@@sem_attr]
let ancillary_parse_env_bool
  (se: sem_env)
= (t: typ) -> (t_wf: ast0_wf_typ t { spec_wf_typ se true t t_wf }) -> bool

[@@sem_attr]
let ancillary_parse_array_group_env_bool
  (se: sem_env)
= (t: group) -> (t_wf: ast0_wf_array_group t { spec_wf_array_group se t t_wf }) -> bool

[@@sem_attr; bundle_attr]
let ancillary_map_constraint_env_bool
  (se: name_env)
= (t: map_constraint { bounded_map_constraint se t }) -> bool

[@@base_attr]
noeq
type ask_for' =
| AskForType: t: typ -> t_wf: ast0_wf_typ t -> bool -> ask_for'
| AskForArrayGroup: t: group -> t_wf: ast0_wf_array_group t -> ask_for'
| AskForMapConstraint: t: map_constraint -> t_wf: ast0_wf_map_constraint t -> ask_for'

let ask_for_spec
  (se: sem_env)
  (a: ask_for')
: Tot prop
= match a with
  | AskForType t t_wf guarded -> spec_wf_typ se guarded t t_wf
  | AskForArrayGroup t t_wf -> spec_wf_array_group se t t_wf
  | AskForMapConstraint t t_wf -> spec_wf_map_constraint se t t_wf

let option_ask_for_spec
  (se: sem_env)
  (a: option ask_for')
: Tot prop
= match a with
  | None -> True
  | Some a' -> ask_for_spec se a'

let option_ask_for
  (se: sem_env)
= (a: option ask_for' { option_ask_for_spec se a })

[@@base_attr]
let option_ask_for_is_type
  (a: option ask_for')
: Tot prop
= match a with
  | Some (AskForType _ _ _) -> True
  | _ -> False

let option_ask_for_get_type
  (v_sem_env: sem_env)
  (a: option_ask_for v_sem_env)
  (sq: squash (option_ask_for_is_type a))
: Tot (Ghost.erased CDDL.Spec.Base.typ)
= typ_sem v_sem_env (AskForType?.t (Some?.v a))

[@@base_attr]
let option_ask_for_is_array_group
  (a: option ask_for')
: Tot prop
= match a with
  | Some (AskForArrayGroup _ _) -> True
  | _ -> False

[@@base_attr]
let option_ask_for_is_map_constraint
  (a: option ask_for')
: Tot prop
= match a with
  | Some (AskForMapConstraint _ _) -> True
  | _ -> False

let option_ask_for_get_map_constraint
  (v_sem_env: sem_env)
  (a: option_ask_for v_sem_env)
  (sq: squash (option_ask_for_is_map_constraint a))
: Tot (Ghost.erased CDDL.Spec.MapGroup.map_constraint)
= map_constraint_sem v_sem_env (AskForMapConstraint?.t (Some?.v a))

[@@bundle_attr]
let is_TDef
  (t: typ)
: Tot bool
= match t with
  | TDef _
  | TNamed _ (TDef _)
    -> true
  | _ -> false

#push-options "--z3rlimit 1024 --query_stats"

#restart-solver

[@@bundle_attr]
let rec ask_zero_copy_wf_type
  (#se: sem_env)
  (ancillary_v: ancillary_validate_env_bool se.se_bound)
  (ancillary: ancillary_parse_env_bool se)
  (ancillary_ag: ancillary_parse_array_group_env_bool se)
  (ancillary_mg: ancillary_map_constraint_env_bool se.se_bound)
  (#t: typ)
  (t_wf: ast0_wf_typ t {
    spec_wf_typ se true t t_wf
  })
: Tot (option_ask_for se)
    (decreases t_wf)
= match t_wf with
  | WfTRewrite _ _ s ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag ancillary_mg s
  | WfTTagged tg _ s ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag ancillary_mg s
  | WfTChoice _ _ s1 s2 ->
    begin match ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag ancillary_mg s1 with
    | Some ask -> Some ask
    | _ -> ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag ancillary_mg s2
    end
  | WfTElem e -> None
  | WfTDetCbor _ _ s ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag ancillary_mg s
  | WfTStrSize k _ _ lo hi -> None
  | WfTIntRange _ _ _ lo hi -> None
  | WfTDef n -> None
  | WfTArray _ s ->
    ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag ancillary_mg s
  | WfTMap _ _ s ->
    ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag ancillary_mg s

and ask_zero_copy_wf_array_group
  (#se: sem_env)
  (ancillary_v: ancillary_validate_env_bool se.se_bound)
  (ancillary: ancillary_parse_env_bool se)
  (ancillary_ag: ancillary_parse_array_group_env_bool se)
  (ancillary_mg: ancillary_map_constraint_env_bool se.se_bound)
  (#t: group)
  (t_wf: ast0_wf_array_group t {
    spec_wf_array_group se t t_wf
  })
: Tot (option_ask_for se)
    (decreases t_wf)
= match t_wf with
  | WfAElem _ _ _ t_wf' ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag ancillary_mg t_wf'
  | WfAZeroOrOne _ t_wf' ->
    ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag ancillary_mg t_wf'
  | WfAZeroOrOneOrMore _ t_wf' g' ->
    // HERE I need function pointers, so I MUST NOT do a recursive call
    if ancillary_ag _ t_wf'
    then None
    else Some (AskForArrayGroup _ t_wf')
  | WfAConcat _ _ t_wf1 t_wf2 ->
    begin match ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag ancillary_mg t_wf1 with
    | Some ask -> Some ask
    | None ->
      ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag ancillary_mg t_wf2
    end
  | WfAChoice _ _ t_wf1 t_wf2 ->
    begin match ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag ancillary_mg t_wf1 with
    | Some ask -> Some ask
    | None ->
      ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag ancillary_mg t_wf2
    end
  | WfARewrite _ _ t_wf2 ->
    ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag ancillary_mg t_wf2

and ask_zero_copy_wf_map_group
  (#se: sem_env)
  (ancillary_v: ancillary_validate_env_bool se.se_bound)
  (ancillary: ancillary_parse_env_bool se)
  (ancillary_ag: ancillary_parse_array_group_env_bool se)
  (ancillary_mg: ancillary_map_constraint_env_bool se.se_bound)
  (#t: elab_map_group)
  (t_wf: ast0_wf_parse_map_group t {
    spec_wf_parse_map_group se t t_wf
  })
: Tot (option_ask_for se)
    (decreases t_wf)
= match t_wf with
  | WfMNop _ -> None
  | WfMChoice _ s1 _ s2 ->
    begin match ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag ancillary_mg s1 with
    | Some a -> Some a
    | None ->
      ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag ancillary_mg s2
    end
  | WfMConcat _ s1 _ s2 ->
    begin match ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag ancillary_mg s1 with
    | Some a -> Some a
    | None ->
      ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag ancillary_mg s2
    end
  | WfMZeroOrOne _ s1 ->
    ask_zero_copy_wf_map_group ancillary_v ancillary ancillary_ag ancillary_mg s1
  | WfMLiteral cut _ key _ s ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag ancillary_mg s
  | WfMZeroOrMore tkey tvalue except s_key s_value s_except ->
    if not (is_TDef tkey || ancillary _ s_key)
    then Some (AskForType _ s_key true)
    else if not (is_TDef tvalue || ancillary _ s_value)
    then Some (AskForType _ s_value true)
    else if not (ancillary_mg except)
    then Some (AskForMapConstraint _ s_except)
    else None

[@@base_attr]
let option_ask_for_is_guarded_type
  (a: option ask_for')
: Tot prop
= match a with
  | Some (AskForType _ _ true) -> True
  | _ -> False

let option_ask_for_is_guarded_type_is_type
  (a: option ask_for')
: Lemma
  (requires (option_ask_for_is_guarded_type a))
  (ensures (option_ask_for_is_type a))
  [SMTPat (option_ask_for_is_guarded_type a)]
= ()

[@@bundle_attr]
let ask_zero_copy_ask_for_option
  (#se: sem_env)
  (ancillary_v: ancillary_validate_env_bool se.se_bound)
  (ancillary: ancillary_parse_env_bool se)
  (ancillary_ag: ancillary_parse_array_group_env_bool se)
  (ancillary_mg: ancillary_map_constraint_env_bool se.se_bound)
  (a: option_ask_for se)
: Tot (option_ask_for se)
= match a with
  | None -> None
  | Some (AskForType _ _ false) -> None
  | Some (AskForType t t_wf _) ->
    ask_zero_copy_wf_type ancillary_v ancillary ancillary_ag ancillary_mg t_wf
  | Some (AskForArrayGroup t t_wf) ->
    ask_zero_copy_wf_array_group ancillary_v ancillary ancillary_ag ancillary_mg t_wf
  | Some (AskForMapConstraint t t_wf) -> None


#pop-options



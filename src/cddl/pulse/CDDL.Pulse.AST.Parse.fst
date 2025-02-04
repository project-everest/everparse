module CDDL.Pulse.AST.Parse
include CDDL.Pulse.AST.Base
include CDDL.Pulse.AST.Literal
include CDDL.Pulse.AST.Parse.ElemType
include CDDL.Pulse.Parse.ArrayGroup
include CDDL.Pulse.Parse.MapGroup
include CDDL.Pulse.AST.Types
open Pulse.Lib.Pervasives
module Cbor = CBOR.Spec.API.Format

[@@sem_attr]
type parse_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#se: sem_env)
  (#s_env: target_type_env se.se_bound)
  (r_env: rel_env s_env)
  (sp_env: spec_env se s_env.te_type)
= (n: typ_name se.se_bound) -> impl_zero_copy_parse vmatch (sp_env.tp_spec_typ n).parser (r_env n).sem_rel

[@@sem_attr]
let ancillary_validate_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (se: sem_env)
= (t: typ) -> (t_wf: ast0_wf_typ t { spec_wf_typ se false t t_wf }) -> option (impl_typ vmatch (typ_sem se t))

[@@sem_attr]
let ancillary_validate_env_extend
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#se: sem_env)
  (env1: ancillary_validate_env vmatch se)
  (se2: sem_env {
    sem_env_included se se2
  })
: Tot (ancillary_validate_env vmatch se2)
= fun t t_wf ->
  if bounded_wf_typ se.se_bound t t_wf
  then begin
    (env1 t t_wf)
  end
  else None

[@@sem_attr]
let ancillary_parse_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop)  
  (#cbor_map_iterator_t: Type0)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (Cbor.cbor & Cbor.cbor) -> slprop)
  (#se: sem_env)
  (#s_env: target_type_env se.se_bound)
  (r_env: rel_env s_env)
  (sp_env: spec_env se s_env.te_type)
= (t: typ) -> (t_wf: ast0_wf_typ t { spec_wf_typ se true t t_wf }) -> option (impl_typ vmatch (typ_sem se t) & impl_zero_copy_parse vmatch (spec_of_wf_typ sp_env t_wf).parser (impl_type_sem vmatch cbor_array_iterator_match cbor_map_iterator_match r_env (target_type_of_wf_typ t_wf)).sem_rel)

[@@sem_attr]
let ancillary_parse_env_extend
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop)  
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (Cbor.cbor & Cbor.cbor) -> slprop)
  (#se: sem_env)
  (#s_env: target_type_env se.se_bound)
  (#r_env: rel_env s_env)
  (#sp_env: spec_env se s_env.te_type)
  (env1: ancillary_parse_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env sp_env)
  (#se2: sem_env)
  (#s_env2: target_type_env se2.se_bound)
  (r_env2: rel_env s_env2 {
    rel_env_included r_env r_env2
  })
  (sp_env2: spec_env se2 s_env2.te_type {
    spec_env_included sp_env sp_env2
  })
: Tot (ancillary_parse_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env2 sp_env2)
= fun t t_wf ->
  if bounded_wf_typ se.se_bound t t_wf
  then begin
    (env1 t t_wf)
  end
  else None

[@@sem_attr]
let ancillary_parse_array_group_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop)  
  (#cbor_map_iterator_t: Type0)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (Cbor.cbor & Cbor.cbor) -> slprop)
  (#se: sem_env)
  (#s_env: target_type_env se.se_bound)
  (r_env: rel_env s_env)
  (sp_env: spec_env se s_env.te_type)
= (t: group) -> (t_wf: ast0_wf_array_group t { spec_wf_array_group se t t_wf }) -> option (impl_array_group cbor_array_iterator_match (array_group_sem se t) & impl_zero_copy_array_group cbor_array_iterator_match (spec_of_wf_array_group sp_env t_wf).ag_parser (impl_type_sem vmatch cbor_array_iterator_match cbor_map_iterator_match r_env (target_type_of_wf_array_group t_wf)).sem_rel)

[@@sem_attr]
let ancillary_parse_array_group_env_extend
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop)  
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (Cbor.cbor & Cbor.cbor) -> slprop)
  (#se: sem_env)
  (#s_env: target_type_env se.se_bound)
  (#r_env: rel_env s_env)
  (#sp_env: spec_env se s_env.te_type)
  (env1: ancillary_parse_array_group_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env sp_env)
  (#se2: sem_env)
  (#s_env2: target_type_env se2.se_bound)
  (r_env2: rel_env s_env2 {
    rel_env_included r_env r_env2
  })
  (sp_env2: spec_env se2 s_env2.te_type {
    spec_env_included sp_env sp_env2
  })
: Tot (ancillary_parse_array_group_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env2 sp_env2)
= fun t t_wf ->
  if bounded_wf_array_group se.se_bound t t_wf
  then begin
    (env1 t t_wf)
  end
  else None

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module I64 = FStar.Int64
module V = CDDL.Pulse.AST.Validate
module SZ = FStar.SizeT

noeq
type ask_for =
| AskForType: t: typ -> ast0_wf_typ t -> bool -> ask_for
| AskForArrayGroup: t: group -> ast0_wf_array_group t -> ask_for

let ask_for_spec
  (se: sem_env)
  (a: ask_for)
: Tot prop
= match a with
  | AskForType t t_wf guarded -> spec_wf_typ se guarded t t_wf
  | AskForArrayGroup t t_wf -> spec_wf_array_group se t t_wf

#push-options "--z3rlimit 1024 --query_stats"

#restart-solver

[@@sem_attr]
let rec impl_zero_copy_wf_type
  (#cbor_t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> cbor_t -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (#se: sem_env)
  (v_env: V.validator_env vmatch se)
  (#s_env: target_type_env se.se_bound)
  (r_env: rel_env s_env)
  (sp_env: spec_env se s_env.te_type)
  (p_env: parse_env vmatch r_env sp_env)
  (ancillary_v: ancillary_validate_env vmatch se)
  (ancillary: ancillary_parse_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env sp_env)
  (ancillary_ag: ancillary_parse_array_group_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env sp_env)
  (#t: typ)
  (t_wf: ast0_wf_typ t {
    spec_wf_typ se true t t_wf /\ SZ.fits_u64
  })
: Pure (either (impl_zero_copy_parse vmatch (spec_of_wf_typ sp_env t_wf).parser (impl_type_sem vmatch cbor_array_iterator_match cbor_map_iterator_match r_env (target_type_of_wf_typ t_wf)).sem_rel) (ask_for))
    (requires True)
    (ensures (fun res -> match res with
    | Inl _ -> True
    | Inr a -> ask_for_spec se a
    ))
    (decreases t_wf)
= match t_wf with
  | WfTRewrite _ _ s ->
    impl_zero_copy_wf_type impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s
  | WfTTagged tg _ s ->
    begin match impl_zero_copy_wf_type impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s with
    | Inr ask -> Inr ask
    | Inl p ->
      begin match tg with
      | None -> Inl (impl_zero_copy_tagged_none impl.cbor_get_tagged_tag impl.cbor_get_tagged_payload p)
      | Some tag -> Inl (impl_zero_copy_tagged_some impl.cbor_get_tagged_payload (U64.uint_to_t tag) p)
      end
    end
  | WfTChoice _ _ s1 s2 ->
    begin match impl_zero_copy_wf_type impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s1 with
    | Inr ask -> Inr ask
    | Inl p1 ->
      begin match impl_zero_copy_wf_type impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s2 with
      | Inr ask -> Inr ask
      | Inl p2 -> Inl (impl_zero_copy_choice (V.validate_typ impl v_env true _ s1) p1 p2)
      end
    end
  | WfTElem e -> Inl (impl_zero_copy_elem_type vmatch impl.cbor_get_major_type impl.cbor_destr_int64 impl.cbor_get_string impl.cbor_destr_simple e)
  | WfTDetCbor _ _ s ->
    begin match impl_zero_copy_wf_type impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s with
    | Inr ask -> Inr ask
    | Inl p ->
      Inl (impl_zero_copy_det_cbor impl.cbor_get_string impl.cbor_det_parse _ p)
    end
  | WfTStrSize k _ _ lo hi ->
    Inl (impl_zero_copy_str_size impl.cbor_get_string (U8.uint_to_t k) (U64.uint_to_t lo) (U64.uint_to_t hi))
  | WfTIntRange _ _ _ lo hi ->
    if hi < 0
    then Inl (impl_copyful_pure_as_zero_copy (impl_copyful_int_range_neg_int64 impl.cbor_destr_int64 (U64.uint_to_t ((-1) - lo)) (U64.uint_to_t ((-1) - hi))))
    else if lo >= 0
    then Inl (impl_copyful_pure_as_zero_copy (impl_copyful_int_range_uint64 impl.cbor_destr_int64 (U64.uint_to_t lo) (U64.uint_to_t hi)))
    else Inl (impl_copyful_pure_as_zero_copy (impl_copyful_int_range_int64 impl.cbor_get_major_type impl.cbor_destr_int64 (I64.int_to_t lo) (I64.int_to_t hi)))
  | WfTDef n -> Inl (p_env n)
  | WfTArray _ s ->
    begin match impl_zero_copy_wf_array_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s with
    | Inr a -> Inr a
    | Inl ps -> Inl (impl_zero_copy_array impl.cbor_array_iterator_init ps)
    end
  | WfTMap _ _ s ->
    begin match impl_zero_copy_wf_map_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s with
    | Inr a -> Inr a
    | Inl ps -> Inl (impl_zero_copy_map ps ())
    end

and impl_zero_copy_wf_array_group
  (#cbor_t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> cbor_t -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (#se: sem_env)
  (v_env: V.validator_env vmatch se)
  (#s_env: target_type_env se.se_bound)
  (r_env: rel_env s_env)
  (sp_env: spec_env se s_env.te_type)
  (p_env: parse_env vmatch r_env sp_env)
  (ancillary_v: ancillary_validate_env vmatch se)
  (ancillary: ancillary_parse_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env sp_env)
  (ancillary_ag: ancillary_parse_array_group_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env sp_env)
  (#t: group)
  (t_wf: ast0_wf_array_group t {
    spec_wf_array_group se t t_wf /\ SZ.fits_u64
  })
: Pure (either (impl_zero_copy_array_group cbor_array_iterator_match (spec_of_wf_array_group sp_env t_wf).ag_parser (impl_type_sem vmatch cbor_array_iterator_match cbor_map_iterator_match r_env (target_type_of_wf_array_group t_wf)).sem_rel) (ask_for))
    (requires True)
    (ensures (fun res -> match res with
    | Inl _ -> True
    | Inr a -> ask_for_spec se a
    ))
    (decreases t_wf)
= match t_wf with
  | WfAElem _ _ _ t_wf' ->
    begin match impl_zero_copy_wf_type impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag t_wf' with
    | Inl pt ->
      Inl (impl_zero_copy_array_group_item impl.cbor_array_iterator_next pt)
    | Inr ask -> Inr ask
    end
  | WfAZeroOrOne _ t_wf' ->
    begin match impl_zero_copy_wf_array_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag t_wf' with
    | Inr ask -> Inr ask
    | Inl pe ->
      Inl (impl_zero_copy_array_group_zero_or_one pe (V.validate_array_group impl v_env _ t_wf'))
    end
  | WfAZeroOrOneOrMore _ t_wf' g' ->
    // HERE I need function pointers, so I MUST NOT do a recursive call
    begin match ancillary_ag _ t_wf' with
    | None -> Inr (AskForArrayGroup _ t_wf')
    | Some (ve, pe) ->
      begin match g' with
      | GZeroOrMore _ ->
        Inl (impl_zero_copy_array_group_zero_or_more impl.cbor_array_iterator_share impl.cbor_array_iterator_gather ve pe ())
      | _ ->
        Inl (impl_zero_copy_array_group_one_or_more impl.cbor_array_iterator_share impl.cbor_array_iterator_gather ve pe ())
      end
    end
  | WfAConcat _ _ t_wf1 t_wf2 ->
    begin match impl_zero_copy_wf_array_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag t_wf1 with
    | Inr ask -> Inr ask
    | Inl pg1 ->
      begin match impl_zero_copy_wf_array_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag t_wf2 with
      | Inr ask -> Inr ask
      | Inl pg2 -> Inl (impl_zero_copy_array_group_concat impl.cbor_array_iterator_length impl.cbor_array_iterator_share impl.cbor_array_iterator_gather impl.cbor_array_iterator_truncate pg1 (V.validate_array_group impl v_env _ t_wf1) pg2 ())
      end
    end
  | WfAChoice _ _ t_wf1 t_wf2 ->
    begin match impl_zero_copy_wf_array_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag t_wf1 with
    | Inr ask -> Inr ask
    | Inl pg1 ->
      begin match impl_zero_copy_wf_array_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag t_wf2 with
      | Inr ask -> Inr ask
      | Inl pg2 -> Inl (impl_zero_copy_array_group_choice pg1 (V.validate_array_group impl v_env _ t_wf1) pg2)
      end
    end
  | WfARewrite _ _ t_wf2 ->
    impl_zero_copy_wf_array_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag t_wf2

and impl_zero_copy_wf_map_group
  (#cbor_t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> cbor_t -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (#se: sem_env)
  (v_env: V.validator_env vmatch se)
  (#s_env: target_type_env se.se_bound)
  (r_env: rel_env s_env)
  (sp_env: spec_env se s_env.te_type)
  (p_env: parse_env vmatch r_env sp_env)
  (ancillary_v: ancillary_validate_env vmatch se)
  (ancillary: ancillary_parse_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env sp_env)
  (ancillary_ag: ancillary_parse_array_group_env vmatch cbor_array_iterator_match cbor_map_iterator_match r_env sp_env)
  (#t: elab_map_group)
  (t_wf: ast0_wf_parse_map_group t {
    spec_wf_parse_map_group se t t_wf /\ SZ.fits_u64
  })
: Pure (either (impl_zero_copy_map_group vmatch (spec_of_wf_map_group sp_env t_wf).mg_parser (impl_type_sem vmatch cbor_array_iterator_match cbor_map_iterator_match r_env (target_type_of_wf_map_group t_wf)).sem_rel) (ask_for))
    (requires True)
    (ensures (fun res -> match res with
    | Inl _ -> True
    | Inr a -> ask_for_spec se a
    ))
    (decreases t_wf)
= match t_wf with
  | WfMChoice _ s1 _ s2 ->
    begin match impl_zero_copy_wf_map_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s1 with
    | Inr a -> Inr a
    | Inl ps1 ->
      begin match impl_zero_copy_wf_map_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s2 with
      | Inr a -> Inr a
      | Inl ps2 ->
        Inl (impl_zero_copy_map_choice (V.validate_map_group impl v_env _ s1) ps1 ps2 ())
      end
    end
  | WfMConcat _ s1 _ s2 ->
    begin match impl_zero_copy_wf_map_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s1 with
    | Inr a -> Inr a
    | Inl ps1 ->
      begin match impl_zero_copy_wf_map_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s2 with
      | Inr a -> Inr a
      | Inl ps2 ->
        Inl (impl_zero_copy_map_concat impl.cbor_share impl.cbor_gather ps1 ps2 ())
      end
    end
  | WfMZeroOrOne _ s1 ->
    begin match impl_zero_copy_wf_map_group impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s1 with
    | Inr a -> Inr a
    | Inl ps1 ->
      Inl
        (impl_zero_copy_map_ext
          (impl_zero_copy_map_zero_or_one (V.validate_map_group impl v_env _ s1) ps1 ())
          #_ #_ #(spec_of_wf_map_group sp_env t_wf).mg_size #(spec_of_wf_map_group sp_env t_wf).mg_serializable
          (spec_of_wf_map_group sp_env t_wf).mg_parser
          ()
        )
    end
  | WfMLiteral cut key _ s ->
    begin match impl_zero_copy_wf_type impl v_env r_env sp_env p_env ancillary_v ancillary ancillary_ag s with
    | Inr a -> Inr a
    | Inl ps1 ->
      Inl
        (impl_zero_copy_match_item_for
          impl.cbor_map_get
          (with_literal
            impl.cbor_mk_int64
            impl.cbor_elim_int64
            impl.cbor_mk_simple
            impl.cbor_elim_simple
            impl.cbor_mk_string
            key
          )
          cut
          ps1
        )
    end
  | WfMZeroOrMore _ _ _ s_key s_key_except s_value ->
    begin match ancillary _ s_key with
    | None -> Inr (AskForType _ s_key true)
    | Some (v_key, p_key) ->
      begin match ancillary_v _ s_key_except with
      | None -> Inr (AskForType _ s_key_except false)
      | Some (v_key_except) ->
        begin match ancillary _ s_value with
        | None -> Inr (AskForType _ s_value true)
        | Some (v_value, p_value) ->
          Inl
            (impl_zero_copy_map_zero_or_more
              impl.cbor_map_iterator_init
              impl.cbor_map_iterator_share
              impl.cbor_map_iterator_gather
              (target_type_eq s_env (target_type_of_wf_typ s_key))
              (spec_of_wf_typ sp_env s_key)
              v_key
              p_key
              v_key_except
              (spec_of_wf_typ sp_env s_value)
              v_value
              p_value
            )
        end
      end
    end

#pop-options

module CDDL.Pulse.AST.Parse
include CDDL.Pulse.AST.Base
include CDDL.Pulse.AST.Parse.ElemType
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
let ancillary_parse_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop)  
  (#se: sem_env)
  (#s_env: target_type_env se.se_bound)
  (r_env: rel_env s_env)
  (sp_env: spec_env se s_env.te_type)
= (t: typ) -> (t_wf: ast0_wf_typ t { spec_wf_typ se true t t_wf }) -> option (impl_zero_copy_parse vmatch (spec_of_wf_typ sp_env t_wf).parser (impl_type_sem vmatch cbor_array_iterator_match r_env (target_type_of_wf_typ t_wf)).sem_rel)

[@@sem_attr]
let ancillary_parse_env_extend
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop)  
  (#se: sem_env)
  (#s_env: target_type_env se.se_bound)
  (#r_env: rel_env s_env)
  (#sp_env: spec_env se s_env.te_type)
  (env1: ancillary_parse_env vmatch cbor_array_iterator_match r_env sp_env)
  (#se2: sem_env)
  (#s_env2: target_type_env se2.se_bound)
  (r_env2: rel_env s_env2 {
    rel_env_included r_env r_env2
  })
  (sp_env2: spec_env se2 s_env2.te_type {
    spec_env_included sp_env sp_env2
  })
: Tot (ancillary_parse_env vmatch cbor_array_iterator_match r_env2 sp_env2)
= fun t t_wf ->
  if bounded_wf_typ se.se_bound t t_wf
  then begin
    (env1 t t_wf)
  end
  else None

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module I64 = FStar.Int64
module V = CDDL.Pulse.AST.Validate
module SZ = FStar.SizeT

[@@sem_attr]
let rec impl_zero_copy_type
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
  (ancillary: ancillary_parse_env vmatch cbor_array_iterator_match r_env sp_env)
  (#t: typ)
  (t_wf: ast0_wf_typ t {
    spec_wf_typ se true t t_wf /\ SZ.fits_u64
  })
: Pure (either (impl_zero_copy_parse vmatch (spec_of_wf_typ sp_env t_wf).parser (impl_type_sem vmatch cbor_array_iterator_match r_env (target_type_of_wf_typ t_wf)).sem_rel) (t': typ & ast0_wf_typ t'))
    (requires True)
    (ensures (fun res -> match res with
    | Inl _ -> True
    | Inr (| t', t_wf' |) -> spec_wf_typ se true t' t_wf'
    ))
    (decreases t_wf)
= match t_wf with
  | WfTRewrite _ _ s ->
    impl_zero_copy_type impl v_env r_env sp_env p_env ancillary s
  | WfTTagged tg _ s ->
    begin match impl_zero_copy_type impl v_env r_env sp_env p_env ancillary s with
    | Inr ask -> Inr ask
    | Inl p ->
      begin match tg with
      | None -> Inl (impl_zero_copy_tagged_none impl.cbor_get_tagged_tag impl.cbor_get_tagged_payload p)
      | Some tag -> Inl (impl_zero_copy_tagged_some impl.cbor_get_tagged_payload (U64.uint_to_t tag) p)
      end
    end
  | WfTChoice _ _ s1 s2 ->
    begin match impl_zero_copy_type impl v_env r_env sp_env p_env ancillary s1 with
    | Inr ask -> Inr ask
    | Inl p1 ->
      begin match impl_zero_copy_type impl v_env r_env sp_env p_env ancillary s2 with
      | Inr ask -> Inr ask
      | Inl p2 -> Inl (impl_zero_copy_choice (V.validate_typ impl v_env true _ s1) p1 p2)
      end
    end
  | WfTElem e -> Inl (impl_zero_copy_elem_type vmatch impl.cbor_get_major_type impl.cbor_destr_int64 impl.cbor_get_string impl.cbor_destr_simple e)
  | WfTDetCbor _ _ s ->
    begin match impl_zero_copy_type impl v_env r_env sp_env p_env ancillary s with
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
  | WfTArray _ _ -> admit ()
  | WfTMap _ _ _ -> admit ()

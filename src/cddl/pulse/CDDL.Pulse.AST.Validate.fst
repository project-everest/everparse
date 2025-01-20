module CDDL.Pulse.AST.Validate
include CDDL.Pulse.Misc
include CDDL.Pulse.MapGroup
include CDDL.Pulse.ArrayGroup
include CDDL.Pulse.AST.ElemType
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module AST = CDDL.Spec.AST.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

[@@AST.sem_attr]
noeq
type validator_env
  (#t: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
= {
  v_sem_env: AST.sem_env;
  v_validator: ((n: AST.typ_name v_sem_env.se_bound) -> impl_typ vmatch (AST.sem_of_type_sem (v_sem_env.se_env n)));
}

[@@AST.sem_attr]
noeq
type cbor_impl
  (#t #t2 #t_arr #t_map: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
  (vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
= {
  cbor_get_major_type: get_major_type_t vmatch;
  cbor_destr_int64: read_uint64_t vmatch;
  cbor_get_string: get_string_t vmatch;
  cbor_destr_simple: read_simple_value_t vmatch;
  cbor_get_tagged_tag: get_tagged_tag_t vmatch;
  cbor_get_tagged_payload: get_tagged_payload_t vmatch;
  cbor_det_parse: cbor_det_parse_t vmatch; // TODO: support mixtures where non-deterministic CBOR objects contain .det-cbor deterministically serialized CBOR objects
  cbor_array_iterator_init: array_iterator_start_t vmatch cbor_array_iterator_match;
  cbor_array_iterator_is_done: array_iterator_is_empty_t cbor_array_iterator_match;
  cbor_array_iterator_next: array_iterator_next_t vmatch cbor_array_iterator_match;
  cbor_get_map_length: get_map_length_t vmatch;
  cbor_map_get: map_get_t vmatch;
  cbor_mk_int64: mk_int64_t vmatch;
  cbor_elim_int64: elim_int64_t vmatch;
  cbor_mk_simple: mk_simple_t vmatch;
  cbor_elim_simple: elim_simple_t vmatch;
  cbor_mk_string: mk_string_t vmatch;
  cbor_map_iterator_init: map_iterator_start_t vmatch cbor_map_iterator_match;
  cbor_map_iterator_is_empty: map_iterator_is_empty_t cbor_map_iterator_match;
  cbor_map_iterator_next: map_iterator_next_t vmatch2 cbor_map_iterator_match;
  cbor_map_entry_key: map_entry_key_t vmatch2 vmatch;
  cbor_map_entry_value: map_entry_value_t vmatch2 vmatch;
}

[@@AST.sem_attr]
let sz_uint_to_t
  (x: nat)
  (sq: squash (SZ.fits x))
: Tot SZ.t
= SZ.uint_to_t x

[@@AST.sem_attr]
let rec validate_typ
  (#t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (env: validator_env vmatch)
  (guard_choices: bool)
  (ty: AST.typ)
  (wf: AST.ast0_wf_typ ty { AST.spec_wf_typ env.v_sem_env guard_choices ty wf /\ SZ.fits_u64 })
: Tot (impl_typ vmatch (AST.typ_sem env.v_sem_env ty))
  (decreases wf)
= match wf with
  | AST.WfTRewrite _ ty' s ->
    impl_ext  (validate_typ impl env guard_choices ty' s) _
  | AST.WfTElem e ->
    impl_elem_type impl.cbor_get_major_type impl.cbor_destr_int64 impl.cbor_get_string impl.cbor_destr_simple e
  | AST.WfTChoice _ _ s1 s2 ->
    impl_t_choice
      (validate_typ impl env guard_choices _ s1)
      (validate_typ impl env guard_choices _ s2)
  | AST.WfTStrSize k _ _ lo hi ->
    impl_str_size
      impl.cbor_get_major_type
      impl.cbor_get_string
      (U8.uint_to_t k)
      (sz_uint_to_t lo (SZ.fits_u64_implies_fits hi))
      (SZ.uint_to_t hi)
  | AST.WfTTagged None _ s' ->
    impl_tagged_none
      impl.cbor_get_major_type
      impl.cbor_get_tagged_payload
      (validate_typ impl env true _ s')
  | AST.WfTTagged (Some tag) _ s' ->
    impl_tagged_some
      impl.cbor_get_major_type
      impl.cbor_get_tagged_tag
      impl.cbor_get_tagged_payload
      (U64.uint_to_t tag)
      (validate_typ impl env true _ s')
  | AST.WfTDetCbor _ _ s' ->
    impl_det_cbor
      impl.cbor_get_major_type
      impl.cbor_get_string
      impl.cbor_det_parse
      (validate_typ impl env true _ s')
  | AST.WfTIntRange
    _ _ _ from to ->
    if to < 0
    then impl_neg_int_range impl.cbor_get_major_type impl.cbor_destr_int64 (U64.uint_to_t ((-1) - from)) (U64.uint_to_t ((-1) - to))
    else if from >= 0
    then impl_uint_range impl.cbor_get_major_type impl.cbor_destr_int64 (U64.uint_to_t from) (U64.uint_to_t to)
    else
      impl_ext
        (impl_t_choice
          (impl_neg_int_range impl.cbor_get_major_type impl.cbor_destr_int64 (U64.uint_to_t ((-1) - from)) 0uL)
          (impl_uint_range impl.cbor_get_major_type impl.cbor_destr_int64 0uL (U64.uint_to_t to))
        )
        _
  | AST.WfTArray g s ->
    impl_t_array
      impl.cbor_get_major_type
      impl.cbor_array_iterator_init
      impl.cbor_array_iterator_is_done
      (validate_array_group  impl env _ s)
  | AST.WfTMap g g2 s2 ->
    impl_t_map_group
      impl.cbor_get_major_type
      impl.cbor_get_map_length
      (validate_map_group impl env g2 s2)
      ()
  | AST.WfTDef n -> env.v_validator n

and validate_array_group
  (#t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (env: validator_env vmatch)
  (ty: AST.group)
  (wf: AST.ast0_wf_array_group ty { AST.spec_wf_array_group env.v_sem_env ty wf /\ SZ.fits_u64 })
: Tot (impl_array_group cbor_array_iterator_match (AST.array_group_sem env.v_sem_env ty))
  (decreases wf)
= match wf with
  | AST.WfAElem _ _ _ s' ->
    impl_array_group_item
      impl.cbor_array_iterator_is_done
      impl.cbor_array_iterator_next
      (validate_typ impl env true _ s')
  | AST.WfAZeroOrOne _ s' ->
    impl_array_group_zero_or_one
      (validate_array_group impl env _ s')
  | AST.WfAChoice _ _ s1' s2' ->
    impl_array_group_choice
      (validate_array_group impl env _ s1')
      (validate_array_group impl env _ s2')
  | AST.WfARewrite _ _ s2' ->
    impl_array_group_ext
      (validate_array_group impl env _ s2')
      _
      ()
  | AST.WfAConcat _ _ s1' s2' ->
    impl_array_group_concat
      (validate_array_group impl env _ s1')
      (validate_array_group impl env _ s2')
  | AST.WfAZeroOrOneOrMore _ s' (AST.GZeroOrMore _) ->
    impl_array_group_zero_or_more
      (validate_array_group impl env _ s')
  | AST.WfAZeroOrOneOrMore _ s' (AST.GOneOrMore _) ->
    impl_array_group_one_or_more
      (validate_array_group impl env _ s')

and validate_map_group
  (#t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (env: validator_env vmatch)
  (ty: AST.elab_map_group)
  (wf: AST.ast0_wf_parse_map_group ty { AST.spec_wf_parse_map_group env.v_sem_env ty wf /\ SZ.fits_u64 })
: Tot (impl_map_group_t vmatch (AST.elab_map_group_sem env.v_sem_env ty) (AST.spec_map_group_footprint env.v_sem_env ty))
  (decreases wf)
= match wf with
  | AST.WfMChoice _ s1' _ s2' ->
    impl_map_group_ext
      (impl_map_group_choice
        (validate_map_group impl env _ s1')
        (validate_map_group impl env _ s2')
        ()
      )
      _ _ ()
  | AST.WfMConcat _ s1' _ s2' ->
    impl_map_group_concat
      (validate_map_group impl env _ s1')
      (validate_map_group impl env _ s2')
      ()
  | AST.WfMZeroOrOne _ s' ->
    impl_map_group_ext
      (impl_map_group_zero_or_one
        (validate_map_group impl env _ s')
        ()
      )
      _ _ ()
  | AST.WfMLiteral cut key value s' ->
    impl_map_group_match_item_for
      impl.cbor_map_get
      cut
      (with_literal
        impl.cbor_mk_int64
        impl.cbor_elim_int64
        impl.cbor_mk_simple
        impl.cbor_elim_simple
        impl.cbor_mk_string
        key
      )
      (validate_typ impl env true _ s')
  | AST.WfMZeroOrMore key key_except value s_key s_key_except s_value ->
    impl_zero_or_more_map_group_match_item_except
      impl.cbor_map_iterator_init
      impl.cbor_map_iterator_is_empty
      impl.cbor_map_iterator_next
      impl.cbor_map_entry_key
      impl.cbor_map_entry_value
      (validate_typ impl env true _ s_key)
      (validate_typ impl env true _ s_value)
      (validate_typ impl env false _ s_key_except)
module CDDL.Pulse.AST.Bundle
include CDDL.Pulse.Bundle.ArrayGroup
include CDDL.Pulse.Bundle.MapGroup
include CDDL.Pulse.Bundle.Misc
include CDDL.Pulse.AST.Base
include CDDL.Pulse.AST.Literal
include CDDL.Spec.AST.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type

module Env = CDDL.Pulse.AST.Env // for validator_env
module Parse = CDDL.Pulse.AST.Parse // for ancillary_validate_env

let bundle_env'
  (#t: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
  (env: name_env)
= (n: typ_name env) -> bundle vmatch

let target_spec_env_of_bundle_env
  (#t: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (se: name_env)
  (be: bundle_env' vmatch se)
: Tot (target_spec_env se)
= fun n -> (be n).b_spec_type

let spec_env_of_bundle_env
  (#t: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (se: sem_env)
  (be: bundle_env' vmatch se.se_bound)
: Pure (spec_env se (target_spec_env_of_bundle_env se.se_bound be))
    (requires forall n . (Ghost.reveal (be n).b_typ == sem_of_type_sem (se.se_env n)))
    (ensures fun _ -> True)
= {
  tp_spec_typ = fun n -> (be n).b_spec
}

[@@bundle_attr; sem_attr] // sem_attr for validate_typw
noeq type bundle_env
  (#t: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
= {
  be_ast: wf_ast_env;
  be_v: Env.validator_env vmatch be_ast.e_sem_env;
  be_b: bundle_env' vmatch be_ast.e_sem_env.se_bound;
  be_b_correct: (n: typ_name be_ast.e_sem_env.se_bound) -> Lemma
    (Ghost.reveal (be_b n).b_typ == sem_of_type_sem (be_ast.e_sem_env.se_env n));
}

let bundle_env_correct
  (#t: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (be: bundle_env vmatch)
  (n: typ_name be.be_ast.e_sem_env.se_bound)
: Lemma
  (ensures (Ghost.reveal (be.be_b n).b_typ == sem_of_type_sem (be.be_ast.e_sem_env.se_env n)))
  [SMTPat (be.be_b n)]
= be.be_b_correct n

let empty_bundle_env'
  (#t: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
  (n: typ_name empty_name_env)
: Tot (bundle vmatch)
= false_elim ()

let empty_bundle_env'_correct
  (#t: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
  (n: typ_name empty_name_env)
: Lemma
  (Ghost.reveal (empty_bundle_env' vmatch n).b_typ == sem_of_type_sem (empty_sem_env.se_env n))
= ()

[@@bundle_attr; sem_attr] // sem_attr for validate_typ
let empty_bundle_env
  (#t: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
: bundle_env vmatch
= {
  be_ast = empty_ast_env;
  be_v = Env.empty_validator_env _;
  be_b = empty_bundle_env' _;
  be_b_correct = empty_bundle_env'_correct vmatch;
}

let bundle_env_included
  (#t: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (b1 b2: bundle_env vmatch)
: Tot prop
= ast_env_included b1.be_ast b2.be_ast /\
  (forall (n: typ_name b1.be_ast.e_sem_env.se_bound) .
    b1.be_b n == b2.be_b n
  )

let spec_env_of_bundle_env_included
  (#t: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (b1 b2: bundle_env vmatch)
: Lemma
  (requires (bundle_env_included b1 b2))
  (ensures (spec_env_included (spec_env_of_bundle_env b1.be_ast.e_sem_env b1.be_b) (spec_env_of_bundle_env b2.be_ast.e_sem_env b2.be_b)))
= ()

[@@bundle_attr]
let extend_bundle_env'
  (#t: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (#se: name_env)
  (be: bundle_env' vmatch se)
  (n: string { None? (se n) })
  (b: bundle vmatch)
: Tot (bundle_env' vmatch (extend_name_env se n NType))
= fun n' -> if n = n' then b else be n'

let sem_of_typ_sem_wf_ast_env_extend_typ_with_weak
  (e: wf_ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf
  })
: Lemma
  (let e' = (wf_ast_env_extend_typ_with_weak e new_name t t_wf) in
    sem_of_type_sem (e'.e_sem_env.se_env new_name) == typ_sem e.e_sem_env t
  )
= let e' = (wf_ast_env_extend_typ_with_weak e new_name t t_wf) in
  assert_norm (sem_of_type_sem (e'.e_sem_env.se_env new_name) == typ_sem e.e_sem_env t)

[@@bundle_attr; sem_attr] // sem_attr for validate_typ
let bundle_env_extend_typ_with_weak
  (#cbor_t: Type0)
  (#vmatch: (perm -> cbor_t -> cbor -> slprop))
  (e: bundle_env vmatch)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    wf_ast_env_extend_typ_with_weak_pre e.be_ast new_name t t_wf
  })
  (w: impl_typ vmatch (typ_sem e.be_ast.e_sem_env t))
  (p: bundle vmatch {
    Ghost.reveal p.b_typ == typ_sem e.be_ast.e_sem_env t
  })
: Tot (e': bundle_env vmatch {
      bundle_env_included e e' /\
      e'.be_ast == wf_ast_env_extend_typ_with_weak e.be_ast new_name t t_wf
  })
= {
    be_ast = wf_ast_env_extend_typ_with_weak e.be_ast new_name t t_wf;
    be_v = Env.extend_validator_env_with_typ_weak e.be_v new_name () t () w;
    be_b = extend_bundle_env' e.be_b new_name p;
    be_b_correct = (fun n' -> if n' = new_name then sem_of_typ_sem_wf_ast_env_extend_typ_with_weak e.be_ast new_name t t_wf else e.be_b_correct n');
}

[@@bundle_attr; sem_attr] // sem_attr for validate_typ
let bundle_env_extend_group
  (#cbor_t: Type0)
  (#vmatch: (perm -> cbor_t -> cbor -> slprop))
  (e: bundle_env vmatch)
  (new_name: string)
  (t: group)
  (sq1: squash (e.be_ast.e_sem_env.se_bound new_name == None))
  (sq2: squash (group_bounded e.be_ast.e_sem_env.se_bound t))
: Tot (e': bundle_env vmatch {
      bundle_env_included e e' /\
      e'.be_ast == wf_ast_env_extend_group e.be_ast new_name t sq1 sq2
  })
=
  {
    be_ast = wf_ast_env_extend_group e.be_ast new_name t sq1 sq2;
    be_v = Env.extend_validator_env_with_group e.be_v new_name t () ();
    be_b = e.be_b;
    be_b_correct = e.be_b_correct;
  }

[@@bundle_attr; sem_attr] // sem_attr for ask
let ancillary_bundle_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> cbor -> slprop)
  (se: sem_env)
= (t: typ) -> (t_wf: ast0_wf_typ t {
      spec_wf_typ se true t t_wf
  }) -> Pure (option (impl_typ vmatch (typ_sem se t) & bundle vmatch))
    (requires True)
    (ensures fun res -> spec_wf_typ se true t t_wf /\
      begin match res with
      | None -> True
      | Some (_, b) -> Ghost.reveal b.b_typ == typ_sem se t
      end
    )

[@@sem_attr]
let ancillary_bundle_env_is_some
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (#se: sem_env)
  (env: ancillary_bundle_env vmatch se)
: Tot (Parse.ancillary_parse_env_bool se)
= fun t t_wf -> Some? (env t t_wf)

[@@bundle_attr; sem_attr] // sem_attr for ask
let ancillary_bundle_env_extend
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (#se: sem_env)
  (env1: ancillary_bundle_env vmatch se)
  (se2: sem_env {
    sem_env_included se se2
  })
: Tot (ancillary_bundle_env vmatch se2)
= fun t t_wf ->
  if bounded_wf_typ se.se_bound t t_wf
  then begin
    (env1 t t_wf)
  end
  else None

[@@bundle_attr; sem_attr] // sem_attr for ask
let ancillary_bundle_env_set
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (#se: sem_env)
  (env1: ancillary_bundle_env vmatch se)
  (t': typ)
  (t_wf': ast0_wf_typ t' { spec_wf_typ se true t' t_wf' })
  (v: impl_typ vmatch (typ_sem se t'))
  (b: bundle vmatch { Ghost.reveal b.b_typ == typ_sem se t' })
: Tot (ancillary_bundle_env vmatch se)
= fun t t_wf -> if t = t' && t_wf = t_wf' then Some (v, b) else env1 t t_wf

[@@bundle_attr; sem_attr] // sem_attr for ask
let ancillary_array_bundle_env
  (#cbor_t: Type)
  (cbor_array_iterator_match: perm -> cbor_t -> list cbor -> slprop)
  (se: sem_env)
= (t: group) -> (t_wf: ast0_wf_array_group t {
      spec_wf_array_group se t t_wf
  }) -> Pure (option (impl_array_group cbor_array_iterator_match (array_group_sem se t) & array_bundle cbor_array_iterator_match))
    (requires True)
    (ensures fun res -> spec_wf_array_group se t t_wf /\
      begin match res with
      | None -> True
      | Some (_, b) -> Ghost.reveal b.ab_typ == array_group_sem se t
      end
    )

[@@sem_attr]
let ancillary_array_bundle_env_is_some
  (#cbor_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_t -> list cbor -> slprop)
  (#se: sem_env)
  (env: ancillary_array_bundle_env cbor_array_iterator_match se)
: Tot (Parse.ancillary_parse_array_group_env_bool se)
= fun t t_wf -> Some? (env t t_wf)

[@@bundle_attr; sem_attr] // sem_attr for ask
let ancillary_array_bundle_env_extend
  (#cbor_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_t -> list cbor -> slprop)
  (#se: sem_env)
  (env1: ancillary_array_bundle_env cbor_array_iterator_match se)
  (se2: sem_env {
    sem_env_included se se2
  })
: Tot (ancillary_array_bundle_env cbor_array_iterator_match se2)
= fun t t_wf ->
  if bounded_wf_array_group se.se_bound t t_wf
  then begin
    (env1 t t_wf)
  end
  else None

[@@bundle_attr; sem_attr] // sem_attr for ask
let ancillary_array_bundle_env_set
  (#cbor_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_t -> list cbor -> slprop)
  (#se: sem_env)
  (env1: ancillary_array_bundle_env cbor_array_iterator_match se)
  (t': group)
  (t_wf': ast0_wf_array_group t' { spec_wf_array_group se t' t_wf' })
  (v: impl_array_group cbor_array_iterator_match (array_group_sem se t'))
  (b: array_bundle cbor_array_iterator_match { Ghost.reveal b.ab_typ == array_group_sem se t' })
: Tot (ancillary_array_bundle_env cbor_array_iterator_match se)
= fun t t_wf -> if t = t' && t_wf = t_wf' then Some (v, b) else env1 t t_wf

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module I64 = FStar.Int64
module V = CDDL.Pulse.AST.Validate
module SZ = FStar.SizeT
open CBOR.Pulse.API.Base

[@@bundle_attr]
let impl_bundle_elem_type
  (#ty: Type0)
  (vmatch: (perm -> ty -> cbor -> slprop))
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_get_string: get_string_t vmatch)
  (cbor_destr_simple: read_simple_value_t vmatch)
  (l: elem_typ)
: Pure (bundle vmatch)
    (requires wf_elem_typ l)
    (ensures fun res ->
      wf_elem_typ l /\
      Ghost.reveal res.b_typ == elem_typ_sem l
    )
= match l with
  | ELiteral l -> bundle_unit _ (spec_literal (eval_literal l))
  | EBool -> bundle_bool cbor_destr_simple
  | ESimple -> bundle_simple cbor_destr_simple
  | EByteString -> bundle_bytes cbor_get_string
  | ETextString -> bundle_text cbor_get_string
  | EUInt -> bundle_uint cbor_destr_int64
  | ENInt -> bundle_nint cbor_destr_int64
  | EAlwaysFalse -> bundle_always_false _ (spec_always_false (fun _ -> true))
  | EAny -> bundle_any _

#push-options "--z3rlimit 1024 --query_stats --ifuel 4 --fuel 4 --split_queries always"

[@@bundle_attr]
let rec impl_bundle_wf_type
  (#cbor_t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> cbor_t -> cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (env: bundle_env vmatch)
  (ancillary_v: Parse.ancillary_validate_env vmatch env.be_ast.e_sem_env)
  (ancillary: ancillary_bundle_env vmatch env.be_ast.e_sem_env)
  (ancillary_ag: ancillary_array_bundle_env cbor_array_iterator_match env.be_ast.e_sem_env)
  (#t: typ)
  (t_wf: ast0_wf_typ t)
: Pure (bundle vmatch)
    (requires 
    spec_wf_typ env.be_ast.e_sem_env true t t_wf /\ SZ.fits_u64
    /\ None? (Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some ancillary_v) (ancillary_bundle_env_is_some ancillary) (ancillary_array_bundle_env_is_some ancillary_ag) t_wf)
    )
    (ensures fun res ->
      spec_wf_typ env.be_ast.e_sem_env true t t_wf /\
      Ghost.reveal res.b_typ == typ_sem env.be_ast.e_sem_env t
    )
    (decreases t_wf)
= match t_wf with
  | WfTRewrite _ _ s ->
    bundle_type_ext (impl_bundle_wf_type impl env ancillary_v ancillary ancillary_ag s) (typ_sem env.be_ast.e_sem_env t) ()
  | WfTTagged tg _ s ->
    let p = impl_bundle_wf_type impl env ancillary_v ancillary ancillary_ag s in
    begin match tg with
    | None -> bundle_tagged_none impl.cbor_get_tagged_tag impl.cbor_get_tagged_payload p
    | Some tag -> bundle_tagged_some impl.cbor_get_tagged_payload (U64.uint_to_t tag) p
    end
  | WfTChoice _ _ s1 s2 ->
    let p1 = impl_bundle_wf_type impl env ancillary_v ancillary ancillary_ag s1 in
    let p2 = impl_bundle_wf_type impl env ancillary_v ancillary ancillary_ag s2 in
    (bundle_choice p1 (V.validate_typ impl env.be_v true _ s1) p2 ())
  | WfTElem e -> (impl_bundle_elem_type vmatch impl.cbor_get_major_type impl.cbor_destr_int64 impl.cbor_get_string impl.cbor_destr_simple e)
  | WfTDetCbor _ _ s ->
    let p = impl_bundle_wf_type impl env ancillary_v ancillary ancillary_ag s in
    bundle_type_ext
      (bundle_det_cbor impl.cbor_get_string impl.cbor_det_parse p)
      (typ_sem env.be_ast.e_sem_env t) ()
  | WfTStrSize k base range lo hi ->
    bundle_type_ext
      (bundle_str_size impl.cbor_get_string (U8.uint_to_t k) (U64.uint_to_t lo) (U64.uint_to_t hi))
      (typ_sem env.be_ast.e_sem_env t) ()
  | WfTIntRange _ _ _ lo hi ->
    if hi < 0
    then (bundle_int_range_neg_int64 impl.cbor_destr_int64 (U64.uint_to_t ((-1) - lo)) (U64.uint_to_t ((-1) - hi)))
    else if lo >= 0
    then (bundle_int_range_uint64 impl.cbor_destr_int64 (U64.uint_to_t lo) (U64.uint_to_t hi))
    else (bundle_int_range_int64 impl.cbor_get_major_type impl.cbor_destr_int64 (I64.int_to_t lo) (I64.int_to_t hi))
  | WfTDef n -> env.be_b n
  | WfTArray _ s ->
    let ps = impl_bundle_wf_array_group impl env ancillary_v ancillary ancillary_ag s in
    (bundle_array impl.cbor_array_iterator_init ps)
  | WfTMap _ _ s ->
    let ps = impl_bundle_wf_map_group impl env ancillary_v ancillary ancillary_ag s in
    (bundle_map ps)

and impl_bundle_wf_array_group
  (#cbor_t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> cbor_t -> cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (env: bundle_env vmatch)
  (ancillary_v: Parse.ancillary_validate_env vmatch env.be_ast.e_sem_env)
  (ancillary: ancillary_bundle_env vmatch env.be_ast.e_sem_env)
  (ancillary_ag: ancillary_array_bundle_env cbor_array_iterator_match env.be_ast.e_sem_env)
  (#t: group)
  (t_wf: ast0_wf_array_group t)
: Pure (array_bundle cbor_array_iterator_match)
    (requires 
    spec_wf_array_group env.be_ast.e_sem_env t t_wf /\ SZ.fits_u64
    /\ None? (Parse.ask_zero_copy_wf_array_group (Parse.ancillary_validate_env_is_some ancillary_v) (ancillary_bundle_env_is_some ancillary) (ancillary_array_bundle_env_is_some ancillary_ag) t_wf)
    )
    (ensures fun res ->
      spec_wf_array_group env.be_ast.e_sem_env t t_wf /\
      Ghost.reveal res.ab_typ == array_group_sem env.be_ast.e_sem_env t
    )
    (decreases t_wf)
= match t_wf with
  | WfAElem _ _ _ t_wf' ->
    let pt = impl_bundle_wf_type impl env ancillary_v ancillary ancillary_ag t_wf' in
    (bundle_array_group_item impl.cbor_array_iterator_next pt)
  | WfAZeroOrOne _ t_wf' ->
    let pe = impl_bundle_wf_array_group impl env ancillary_v ancillary ancillary_ag t_wf' in
    (bundle_array_group_zero_or_one pe (V.validate_array_group impl env.be_v _ t_wf') ())
  | WfAZeroOrOneOrMore _ t_wf' g' ->
    // HERE I need function pointers, so I MUST NOT do a recursive call
    let Some (ve, be) = ancillary_ag _ t_wf' in
      begin match g' with
      | GZeroOrMore _ ->
        (bundle_array_group_zero_or_more impl.cbor_array_iterator_share impl.cbor_array_iterator_gather be ve ())
      | _ ->
        (bundle_array_group_one_or_more impl.cbor_array_iterator_share impl.cbor_array_iterator_gather be ve ())
      end
  | WfAConcat _ _ t_wf1 t_wf2 ->
    let pg1 = impl_bundle_wf_array_group impl env ancillary_v ancillary ancillary_ag t_wf1 in
    let pg2 = impl_bundle_wf_array_group impl env ancillary_v ancillary ancillary_ag t_wf2 in
    (bundle_array_group_concat impl.cbor_array_iterator_length impl.cbor_array_iterator_share impl.cbor_array_iterator_gather impl.cbor_array_iterator_truncate pg1 (V.validate_array_group impl env.be_v _ t_wf1) pg2 ())
  | WfAChoice _ _ t_wf1 t_wf2 ->
    let pg1 = impl_bundle_wf_array_group impl env ancillary_v ancillary ancillary_ag t_wf1 in
    let pg2 = impl_bundle_wf_array_group impl env ancillary_v ancillary ancillary_ag t_wf2 in
    (bundle_array_group_choice pg1 (V.validate_array_group impl env.be_v _ t_wf1) pg2 ())
  | WfARewrite _ _ t_wf2 ->
    bundle_array_group_ext'
      (impl_bundle_wf_array_group impl env ancillary_v ancillary ancillary_ag t_wf2)
      (array_group_sem env.be_ast.e_sem_env t) ()

and impl_bundle_wf_map_group
  (#cbor_t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> cbor_t -> cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (env: bundle_env vmatch)
  (ancillary_v: Parse.ancillary_validate_env vmatch env.be_ast.e_sem_env)
  (ancillary: ancillary_bundle_env vmatch env.be_ast.e_sem_env)
  (ancillary_ag: ancillary_array_bundle_env cbor_array_iterator_match env.be_ast.e_sem_env)
  (#t: elab_map_group)
  (t_wf: ast0_wf_parse_map_group t)
: Pure (map_bundle vmatch)
    (requires 
    spec_wf_parse_map_group env.be_ast.e_sem_env t t_wf /\ SZ.fits_u64
    /\ None? (Parse.ask_zero_copy_wf_map_group (Parse.ancillary_validate_env_is_some ancillary_v) (ancillary_bundle_env_is_some ancillary) (ancillary_array_bundle_env_is_some ancillary_ag) t_wf)
    )
    (ensures fun res ->
      spec_wf_parse_map_group env.be_ast.e_sem_env t t_wf /\
      Ghost.reveal res.mb_typ == elab_map_group_sem env.be_ast.e_sem_env t /\
      res.mb_footprint == spec_map_group_footprint env.be_ast.e_sem_env t
    )
    (decreases t_wf)
= match t_wf with
  | WfMChoice _ s1 _ s2 ->
    let ps1 = impl_bundle_wf_map_group impl env ancillary_v ancillary ancillary_ag s1 in
    let ps2 = impl_bundle_wf_map_group impl env ancillary_v ancillary ancillary_ag s2 in
    (bundle_map_choice ps1 (V.validate_map_group impl env.be_v _ s1) ps2 ())
  | WfMConcat _ s1 _ s2 ->
    let ps1 = impl_bundle_wf_map_group impl env ancillary_v ancillary ancillary_ag s1 in
    let ps2 = impl_bundle_wf_map_group impl env ancillary_v ancillary ancillary_ag s2 in
    (bundle_map_concat impl.cbor_share impl.cbor_gather ps1 ps2 ())
  | WfMZeroOrOne _ s1 ->
    let ps1 = impl_bundle_wf_map_group impl env ancillary_v ancillary ancillary_ag s1 in
    bundle_map_ext'
      (bundle_map_zero_or_one
        ps1
        (V.validate_map_group impl env.be_v _ s1)
        ()
      )
      (t_choice ps1.mb_footprint t_always_false)
      ()
  | WfMLiteral cut key _ s ->
    let ps1 = impl_bundle_wf_type impl env ancillary_v ancillary ancillary_ag s in
        (bundle_map_match_item_for
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
  | WfMZeroOrMore _ key_except _ s_key s_key_except s_value ->
    let Some (v_key, p_key) = ancillary _ s_key in
    let Some (v_key_except) = ancillary_v key_except in
    let Some (v_value, p_value) = ancillary _ s_value in
            (bundle_map_zero_or_more
              impl.cbor_map_iterator_init
              impl.cbor_map_iterator_share
              impl.cbor_map_iterator_gather
              p_key
              v_key
              v_key_except
              p_value
              v_value
            )

#pop-options

[@@bundle_attr]
let impl_bundle_wf_type' 
  (#cbor_t #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> cbor_t -> cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
  (impl: cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)
  (env: bundle_env vmatch)
  (ancillary_v: Parse.ancillary_validate_env vmatch env.be_ast.e_sem_env)
  (ancillary: ancillary_bundle_env vmatch env.be_ast.e_sem_env)
  (ancillary_ag: ancillary_array_bundle_env cbor_array_iterator_match env.be_ast.e_sem_env)
  (#t: typ)
  (t_wf: ast0_wf_typ t {
    spec_wf_typ env.be_ast.e_sem_env true t t_wf /\ SZ.fits_u64
  })
  (_: squash (
    None? (Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some ancillary_v) (ancillary_bundle_env_is_some ancillary) (ancillary_array_bundle_env_is_some ancillary_ag) t_wf)
  ))
: Tot (res: bundle vmatch {
      spec_wf_typ env.be_ast.e_sem_env true t t_wf /\
      Ghost.reveal res.b_typ == typ_sem env.be_ast.e_sem_env t
  })
= impl_bundle_wf_type impl env ancillary_v ancillary ancillary_ag t_wf

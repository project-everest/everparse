module CDDL.Pulse.AST.Env
include CDDL.Pulse.AST.Types
open Pulse.Lib.Pervasives
module Cbor = CBOR.Spec.API.Type

module V = CDDL.Pulse.AST.Validate
module P = CDDL.Pulse.AST.Parse

[@@sem_attr]
noeq
type spec_and_impl_env
  (#t1 #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t1 -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (impl: Ghost.erased (CDDL.Pulse.AST.Base.cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)) // for unification only
= {
  si_ast: wf_ast_env;
  si_st: target_type_env si_ast.e_sem_env.se_bound;
  si_sp: spec_env si_ast.e_sem_env si_st.te_type;
  si_r: rel_env si_st;
  si_v: V.validator_env vmatch si_ast.e_sem_env;
  si_p: P.parse_env vmatch si_r si_sp;
}

[@@sem_attr]
let empty_spec_and_impl_env
  (#t1 #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t1 -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (impl: Ghost.erased (CDDL.Pulse.AST.Base.cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)) // for unification only
: spec_and_impl_env impl = {
  si_ast = empty_wf_ast_env;
  si_st = empty_target_type_env;
  si_sp = empty_spec_env _;
  si_r = empty_rel_env;
  si_v = V.empty_validator_env _;
  si_p = P.empty_parse_env _;
}

let spec_and_impl_env_included
  (#t1 #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t1 -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (#impl: Ghost.erased (CDDL.Pulse.AST.Base.cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)) // for unification only
  (s1 s2: spec_and_impl_env impl)
: Tot prop
= ast_env_included s1.si_ast s2.si_ast /\
  target_spec_env_included s1.si_st.te_type s2.si_st.te_type /\
  spec_env_included s1.si_sp s2.si_sp /\
  rel_env_included s1.si_r s2.si_r

[@@sem_attr]
let spec_and_impl_env_extend_typ_with_weak
  (#t1 #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t1 -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (#impl: Ghost.erased (CDDL.Pulse.AST.Base.cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)) // for unification only
  (e: spec_and_impl_env impl)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    wf_ast_env_extend_typ_with_weak_pre e.si_ast new_name t t_wf
  })
  (w: impl_typ vmatch (typ_sem e.si_ast.e_sem_env t))
  (p: impl_zero_copy_parse vmatch (spec_of_wf_typ e.si_sp t_wf).parser (impl_type_sem vmatch cbor_array_iterator_match cbor_map_iterator_match e.si_r (target_type_of_wf_typ t_wf)).sem_rel)
: Tot (e': spec_and_impl_env impl {
      spec_and_impl_env_included e e' /\
      e'.si_ast == wf_ast_env_extend_typ_with_weak e.si_ast new_name t t_wf
  })
=
  let tt = target_type_of_wf_typ t_wf in
  let eq = target_type_eq e.si_st tt in
  let u = impl_type_sem vmatch cbor_array_iterator_match cbor_map_iterator_match e.si_r tt in
  {
    si_ast = wf_ast_env_extend_typ_with_weak e.si_ast new_name t t_wf;
    si_st = target_type_env_extend _ e.si_st new_name NType _ eq;
    si_sp = spec_env_extend_typ e.si_ast new_name _ t_wf e.si_sp;
    si_r = extend_rel_env_gen e.si_r new_name NType _ eq u;
    si_v = V.extend_validator_env_with_typ_weak e.si_v new_name () t () w;
    si_p = (fun n -> if n = new_name then p else e.si_p n);
  }

[@@sem_attr]
let spec_and_impl_env_extend_group
  (#t1 #t2 #t_arr #t_map: Type0)
  (#vmatch: (perm -> t1 -> Cbor.cbor -> slprop))
  (#vmatch2: (perm -> t2 -> (Cbor.cbor & Cbor.cbor) -> slprop))
  (#cbor_array_iterator_match: (perm -> t_arr -> list Cbor.cbor -> slprop))
  (#cbor_map_iterator_match: (perm -> t_map -> list (Cbor.cbor & Cbor.cbor) -> slprop))
  (#impl: Ghost.erased (CDDL.Pulse.AST.Base.cbor_impl vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match)) // for unification only
  (e: spec_and_impl_env impl)
  (new_name: string)
  (t: group)
  (sq1: squash (e.si_ast.e_sem_env.se_bound new_name == None))
  (sq2: squash (group_bounded e.si_ast.e_sem_env.se_bound t))
: Tot (e': spec_and_impl_env impl {
      spec_and_impl_env_included e e' /\
      e'.si_ast == wf_ast_env_extend_group e.si_ast new_name t sq1 sq2
  })
=
  let si_ast' = wf_ast_env_extend_group e.si_ast new_name t sq1 sq2 in
  let si_st' : target_type_env si_ast'.e_sem_env.se_bound = {
    te_type = (fun (x: typ_name si_ast'.e_sem_env.se_bound) -> e.si_st.te_type x);
    te_eq = (fun x -> e.si_st.te_eq x);
  }
  in
  {
    si_ast = si_ast';
    si_st = si_st';
    si_sp = {
      tp_spec_typ = (fun (n: typ_name si_ast'.e_sem_env.se_bound) -> (e.si_sp.tp_spec_typ n <: spec _ (si_st'.te_type n) true));
    };
    si_r = e.si_r;
    si_v = V.extend_validator_env_with_group e.si_v new_name t () ();
    si_p = e.si_p;
  }

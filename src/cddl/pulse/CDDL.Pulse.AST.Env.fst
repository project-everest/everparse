module CDDL.Pulse.AST.Env
include CDDL.Pulse.AST.Types
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
module Impl = CDDL.Pulse.AST.Base

[@@sem_attr]
let validator_env
  (#t: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
  (v_sem_env: sem_env)
= ((n: typ_name v_sem_env.se_bound) -> impl_typ vmatch (sem_of_type_sem (v_sem_env.se_env n)))

let empty_validator_env
  (#t: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
: validator_env vmatch empty_sem_env
= (fun _ -> false_elim ())

[@@sem_attr]
let extend_validator_env_with_typ_weak
  (#t: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (#v_sem_env: sem_env)
  (env: validator_env vmatch v_sem_env)
  (new_name: string)
  (new_name_is_type: squash (v_sem_env.se_bound new_name == None))
  (ty: typ)
  (ty_bounded: squash (typ_bounded v_sem_env.se_bound ty))
  (w: impl_typ vmatch (typ_sem v_sem_env ty))
: validator_env vmatch (sem_env_extend_gen v_sem_env new_name NType (ast_env_elem0_sem v_sem_env ty))
= let v_sem_env' = sem_env_extend_gen v_sem_env new_name NType (ast_env_elem0_sem v_sem_env ty) in
  (fun n -> if n = new_name then w else (env n))

[@@sem_attr]
let extend_validator_env_with_group
  (#t: Type0)
  (#vmatch: (perm -> t -> cbor -> slprop))
  (#v_sem_env: sem_env)
  (env: validator_env vmatch v_sem_env)
  (new_name: string)
  (g: group)
  (new_name_is_type: squash (v_sem_env.se_bound new_name == None))
  (sq: squash (group_bounded v_sem_env.se_bound g))
: validator_env vmatch (sem_env_extend_gen v_sem_env new_name NGroup (ast_env_elem0_sem v_sem_env g))
= let v_sem_env' = sem_env_extend_gen v_sem_env new_name NGroup (ast_env_elem0_sem v_sem_env g) in
  (fun (n: typ_name v_sem_env'.se_bound) -> (env n))

[@@sem_attr]
type parse_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> cbor -> slprop)
  (#se: sem_env)
  (#s_env: target_type_env se.se_bound)
  (r_env: rel_env s_env)
  (sp_env: spec_env se s_env.te_type)
= (n: typ_name se.se_bound) -> impl_zero_copy_parse vmatch (sp_env.tp_spec_typ n).parser (r_env n).sem_rel

let empty_parse_env
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> cbor -> slprop)
: parse_env vmatch empty_rel_env (empty_spec_env _)
= fun _ -> false_elim ()

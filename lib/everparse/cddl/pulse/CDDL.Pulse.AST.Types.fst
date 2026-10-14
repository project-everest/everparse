module CDDL.Pulse.AST.Types
include CDDL.Pulse.Parse.ArrayGroup
include CDDL.Pulse.Parse.MapGroup
include CDDL.Spec.AST.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.SeqMatch
module S = Pulse.Lib.Slice.Util
module V = Pulse.Lib.Vec
module Spec = CDDL.Spec.Base
module Cbor = CBOR.Spec.API.Format
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module I64 = FStar.Int64
module V = Pulse.Lib.Vec
module Trade = Pulse.Lib.Trade
module Iterator = CDDL.Pulse.Iterator.Base

(* Zero-copy parsing only. (Thus, for serialization, it is the responsibility of the user to build values with the right lifetimes before calling the serializer.) *)

[@@sem_attr]
let impl_elem_type_sem
  (cbor_t: Type0)
  (t: target_elem_type)
: Tot Type0
= match t with
  | TTUInt8 -> U8.t
  | TTUInt64 -> U64.t
  | TTInt64 -> I64.t
  | TTUnit -> unit
  | TTBool -> bool
  | TTString -> slice U8.t // with perm
  | TTAny -> cbor_with_perm cbor_t
  | TTAlwaysFalse -> squash False

let rel_elem_type_sem
  (#cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (t: target_elem_type)
: Tot (rel (impl_elem_type_sem cbor_t t) (target_elem_type_sem t))
= match t returns rel (impl_elem_type_sem cbor_t t) (target_elem_type_sem t) with
  | TTUInt8 -> rel_pure _
  | TTUInt64 -> rel_pure _
  | TTInt64 -> rel_pure _
  | TTUnit -> rel_unit
  | TTBool -> rel_pure _
  | TTString -> rel_slice_of_seq #U8.t false
  | TTAny -> rel_cbor_not_freeable vmatch false
  | TTAlwaysFalse -> rel_always_false _ _

[@sem_attr]
noeq
type target_impl_sem (sem_spec_type: Type0) = {
  sem_impl_type: Type0;
  sem_rel: rel sem_impl_type sem_spec_type;
}

[@sem_attr]
type rel_env
  (#bound: name_env)
  (s_env: target_type_env bound)
= (n: typ_name bound) -> target_impl_sem (s_env.te_type n)

let empty_rel_env : rel_env empty_target_type_env = fun _ -> false_elim ()

[@sem_attr]
let rec impl_type_sem
  (#bound: name_env)
  (#cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#cbor2_t: Type0)
  (vmatch2: perm -> cbor2_t -> Cbor.cbor & Cbor.cbor -> slprop)
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop)
  (#cbor_map_iterator_t: Type0)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (Cbor.cbor & Cbor.cbor) -> slprop)
  (#s_env: target_type_env bound)
  (env: rel_env s_env)
  (t: target_type { target_type_bounded bound t })
: Pure (target_impl_sem (target_type_sem s_env.te_type t))
    (requires target_type_bounded bound t)
    (ensures fun _ -> True)
    (decreases t)
= match t with
  | TTDef s -> env s
  | TTElem elt -> { sem_impl_type = impl_elem_type_sem cbor_t elt; sem_rel = rel_elem_type_sem vmatch elt }
  | TTOption t ->
    let it = impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env t in {
      sem_impl_type = option it.sem_impl_type;
      sem_rel = rel_option it.sem_rel
    }
  | TTPair t1 t2 ->
    let it1 = impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env t1 in
    let it2 = impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env t2 in {
      sem_impl_type = (it1.sem_impl_type & it2.sem_impl_type);
      sem_rel = rel_pair it1.sem_rel it2.sem_rel
    }
  | TTUnion t1 t2 ->
    let it1 = impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env t1 in
    let it2 = impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env t2 in {
      sem_impl_type = (it1.sem_impl_type `either` it2.sem_impl_type);
      sem_rel = rel_either it1.sem_rel it2.sem_rel
    }
  | TTArray t ->
    let it = impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env t in {
      sem_impl_type =
        either
          (slice it.sem_impl_type)
          (array_iterator_t it.sem_impl_type cbor_array_iterator_match (Iterator.mk_spec it.sem_rel)) // HERE the relation on the element types is used in the implementation array type
          ;
      sem_rel =
        rel_either_left
          (rel_slice_of_list it.sem_rel false)
          (rel_array_iterator cbor_array_iterator_match (Iterator.mk_spec it.sem_rel))
          ;
    }
  | TTTable t1 t2 ->
    let it1 = impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env t1 in
    let it2 = impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env t2 in {
      sem_impl_type =
        either
          (slice (it1.sem_impl_type & it2.sem_impl_type))
          (map_iterator_t cbor_map_iterator_t it1.sem_impl_type it2.sem_impl_type vmatch vmatch2 (Iterator.mk_spec it1.sem_rel) (Iterator.mk_spec it2.sem_rel))
          ; // HERE the relation on the element types is used in the implementation map type
      sem_rel = 
        rel_either_left
          (rel_slice_of_table (target_type_eq s_env t1) it1.sem_rel it2.sem_rel)
          (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match it1.sem_impl_type it2.sem_impl_type (Iterator.mk_spec it1.sem_rel) (Iterator.mk_spec it2.sem_rel))
          ;
    }

let rel_env_included
  (#bound1: name_env)
  (#s_env1: target_type_env bound1)
  (r1: rel_env s_env1)
  (#bound2: name_env)
  (#s_env2: target_type_env bound2)
  (r2: rel_env s_env2)
: Tot prop
= target_spec_env_included s_env1.te_type s_env2.te_type /\
  (forall (n: typ_name bound1) . r1 n == coerce_eq () (r2 n))

[@sem_attr]
let extend_rel_env_gen
  (#bound: name_env)
  (#s_env: target_type_env bound)
  (env: rel_env s_env)
  (n: string { ~ (name_mem n bound) })
  (s: name_env_elem)
  (st: Type0)
  (st_eq: eq_test st)
  (tt: target_impl_sem st)
: Pure (rel_env (target_type_env_extend bound s_env n s st st_eq))
    (requires True)
    (ensures fun env'  -> rel_env_included env env' )
= fun n' -> if n' = n then tt else env n'

let rec impl_type_sem_incr
  (#bound1: name_env)
  (cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#cbor2_t: Type0)
  (vmatch2: perm -> cbor2_t -> Cbor.cbor & Cbor.cbor -> slprop)
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list Cbor.cbor -> slprop)
  (#cbor_map_iterator_t: Type0)
  (cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (Cbor.cbor & Cbor.cbor) -> slprop)
  (#s_env1: target_type_env bound1)
  (env1: rel_env s_env1)
  (#bound2: name_env)
  (#s_env2: target_type_env bound2)
  (env2: rel_env s_env2)
  (t: target_type)
: Lemma
  (requires rel_env_included env1 env2 /\
    target_type_bounded bound1 t
  )
  (ensures impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env1 t == coerce_eq () (impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env2 t)) // FIXME: WHY WHY WHY do we have this coerce_eq?
  (decreases t)
  [SMTPatOr [
    [SMTPat (rel_env_included env1 env2); SMTPat (impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env1 t);];
    [SMTPat (rel_env_included env1 env2); SMTPat (impl_type_sem vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env2 t);];
  ]]
= match t with
  | TTOption t1
  | TTArray t1
    -> impl_type_sem_incr cbor_t vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env1 env2 t1
  | TTPair t1 t2
  | TTUnion t1 t2
  | TTTable t1 t2 ->
    eq_test_unique (target_type_eq s_env1 t1) (coerce_eq () (target_type_eq s_env2 t1));
    impl_type_sem_incr cbor_t vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env1 env2 t1;
    impl_type_sem_incr cbor_t vmatch vmatch2 cbor_array_iterator_match cbor_map_iterator_match env1 env2 t2
  | _ -> ()

module CDDL.Pulse.AST.Types
include CDDL.Pulse.Types
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
type target_impl_env (bound: name_env) =
  (typ_name bound -> Tot Type0)

[@sem_attr]
let rec impl_type_sem
  (#bound: name_env)
  (cbor_t: Type0)
  (env: target_impl_env bound)
  (t: target_type)
: Pure Type0
    (requires target_type_bounded bound t)
    (ensures fun _ -> True)
    (decreases t)
= match t with
  | TTDef s -> env s
  | TTElem elt -> impl_elem_type_sem cbor_t elt
  | TTOption t -> option (impl_type_sem cbor_t env t)
  | TTPair t1 t2 -> (impl_type_sem cbor_t env t1 & impl_type_sem cbor_t env t2)
  | TTUnion t1 t2 -> either (impl_type_sem cbor_t env t1) (impl_type_sem cbor_t env t2)
  | TTArray t -> slice (impl_type_sem cbor_t env t) // TODO: allow iterable CBOR array objects
  | TTTable t1 t2 -> slice (impl_type_sem cbor_t env t1 & impl_type_sem cbor_t env t2) // TODO: allow iterable CBOR map objects

let target_impl_env_included
  (#bound1: name_env)
  (s_env1: target_impl_env bound1)
  (#bound2: name_env)
  (s_env2: target_impl_env bound2)
: Tot prop
= name_env_included bound1 bound2 /\
  (forall (x: typ_name bound1) . s_env1 x == s_env2 x)

let rec impl_type_sem_incr
  (#bound1: name_env)
  (cbor_t: Type0)
  (env1: target_impl_env bound1)
  (#bound2: name_env)
  (env2: target_impl_env bound2)
  (t: target_type)
: Lemma
  (requires (target_impl_env_included env1 env2 /\
    target_type_bounded bound1 t
  ))
  (ensures (
    impl_type_sem cbor_t env1 t == impl_type_sem cbor_t env2 t
  ))
  [SMTPatOr [
    [SMTPat (target_impl_env_included env1 env2); SMTPat (impl_type_sem cbor_t env1 t);];
    [SMTPat (target_impl_env_included env1 env2); SMTPat (impl_type_sem cbor_t env2 t);];
  ]]
= match t with
  | TTOption t1
  | TTArray t1
    -> impl_type_sem_incr cbor_t env1 env2 t1
  | TTPair t1 t2
  | TTUnion t1 t2
  | TTTable t1 t2
    ->
      impl_type_sem_incr cbor_t env1 env2 t1;
      impl_type_sem_incr cbor_t env1 env2 t2
  | _ -> ()

[@sem_attr]
noeq
type rel_env
  (#bound: name_env)
  (s_env: target_type_env bound)
= {
  r_type: target_impl_env bound;
  r_rel: (n: typ_name bound) -> rel (r_type n) (s_env.te_type n);
}

let rec rel_type_sem
  (#bound: name_env)
  (cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#s_env: target_type_env bound)
  (env: rel_env s_env)
  (t: target_type { target_type_bounded bound t })
: Tot (rel (impl_type_sem cbor_t env.r_type t) (target_type_sem s_env.te_type t) )
  (decreases t)
= match t returns rel (impl_type_sem cbor_t env.r_type t) (target_type_sem s_env.te_type t) with
  | TTDef s -> env.r_rel s
  | TTElem elt -> rel_elem_type_sem vmatch elt
  | TTOption t -> rel_option (rel_type_sem cbor_t vmatch env t)
  | TTPair t1 t2 -> rel_pair (rel_type_sem cbor_t vmatch env t1) (rel_type_sem cbor_t vmatch env t2)
  | TTUnion t1 t2 -> rel_either (rel_type_sem cbor_t vmatch env t1) (rel_type_sem cbor_t vmatch env t2)
  | TTArray t -> rel_slice_of_list (rel_type_sem cbor_t vmatch env t) false
  | TTTable t1 t2 -> rel_slice_of_table (target_type_eq s_env t1) (rel_type_sem cbor_t vmatch env t1) (rel_type_sem cbor_t vmatch env t2)

let rel_env_included
  (#bound1: name_env)
  (#s_env1: target_type_env bound1)
  (r1: rel_env s_env1)
  (#bound2: name_env)
  (#s_env2: target_type_env bound2)
  (r2: rel_env s_env2)
: Tot prop
= target_spec_env_included s_env1.te_type s_env2.te_type /\
  target_impl_env_included r1.r_type r2.r_type /\
  (forall (n: typ_name bound1) . r1.r_rel n == coerce_eq () (r2.r_rel n))

let rec rel_type_sem_incr
  (#bound1: name_env)
  (cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
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
  (ensures rel_type_sem cbor_t vmatch env1 t == coerce_eq () (rel_type_sem cbor_t vmatch env2 t)) // FIXME: WHY WHY WHY do we have this coerce_eq?
  (decreases t)
  [SMTPatOr [
    [SMTPat (rel_env_included env1 env2); SMTPat (rel_type_sem cbor_t vmatch env1 t);];
    [SMTPat (rel_env_included env1 env2); SMTPat (rel_type_sem cbor_t vmatch env2 t);];
  ]]
= match t with
  | TTOption t1
  | TTArray t1
    -> rel_type_sem_incr cbor_t vmatch env1 env2 t1
  | TTPair t1 t2
  | TTUnion t1 t2
  | TTTable t1 t2 ->
    eq_test_unique (target_type_eq s_env1 t1) (coerce_eq () (target_type_eq s_env2 t1));
    rel_type_sem_incr cbor_t vmatch env1 env2 t1;
    rel_type_sem_incr cbor_t vmatch env1 env2 t2
  | _ -> ()

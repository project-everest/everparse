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
  | TTString -> vec U8.t // TODO: allow zero-copy parsing
  | TTAny -> cbor_copy_t cbor_t // TODO: allow zero_copy parsing
  | TTAlwaysFalse -> squash False

let rel_elem_type_sem
  (cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (t: target_elem_type)
  (freeable: bool)
: Tot (rel (impl_elem_type_sem cbor_t t) (target_elem_type_sem t))
= match t with
  | TTUInt8 -> rel_pure _
  | TTUInt64 -> rel_pure _
  | TTInt64 -> rel_pure _
  | TTUnit -> rel_unit
  | TTBool -> rel_pure _
  | TTString -> rel_vec_of_seq #U8.t
  | TTAny -> rel_cbor_copy cbor_t vmatch freeable
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
  | TTArray t -> vec_or_slice (impl_type_sem cbor_t env t)
  | TTTable t1 t2 -> vec_or_slice (impl_type_sem cbor_t env t1 & impl_type_sem cbor_t env t2)

[@sem_attr]
noeq
type rel_env
  (#bound: name_env)
  (s_env: target_type_env bound)
= {
  r_type: target_impl_env bound;
  r_rel: (n: typ_name bound) -> (freeable: bool) -> rel (r_type n) (s_env.te_type n);
  free: (n: typ_name bound) -> (x: r_type n) -> (y: s_env.te_type n) -> stt unit (r_rel n true x y) (fun _ -> emp);
}

let rec rel_type_sem
  (#bound: name_env)
  (cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (#s_env: target_type_env bound)
  (env: rel_env s_env)
  (t: target_type { target_type_bounded bound t })
  (freeable: bool)
: Tot (rel (impl_type_sem cbor_t env.r_type t) (target_type_sem s_env.te_type t) )
  (decreases t)
= match t with
  | TTDef s -> env.r_rel s freeable
  | TTElem elt -> rel_elem_type_sem cbor_t vmatch elt freeable
  | TTOption t -> rel_option (rel_type_sem cbor_t vmatch env t freeable)
  | TTPair t1 t2 -> rel_pair (rel_type_sem cbor_t vmatch env t1 freeable) (rel_type_sem cbor_t vmatch env t2 freeable)
  | TTUnion t1 t2 -> rel_either (rel_type_sem cbor_t vmatch env t1 freeable) (rel_type_sem cbor_t vmatch env t2 freeable)
  | TTArray t -> rel_vec_or_slice_of_list (rel_type_sem cbor_t vmatch env t freeable) freeable
  | TTTable t1 t2 -> rel_vec_or_slice_of_table (target_type_eq s_env t1) (rel_type_sem cbor_t vmatch env t1 freeable) (rel_type_sem cbor_t vmatch env t2 freeable) freeable

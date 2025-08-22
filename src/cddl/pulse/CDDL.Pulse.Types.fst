module CDDL.Pulse.Types
#lang-pulse
include CDDL.Pulse.Types.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.SeqMatch
module S = Pulse.Lib.Slice.Util
module V = Pulse.Lib.Vec
module Spec = CDDL.Spec.All

module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

let map_of_list_cons
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m: Map.t key (list value))
: Tot (Map.t key (list value))
= 
    begin match Map.get m k with
    | None -> Map.set m k (key_eq k) [v]
    | Some l -> Map.set m k (key_eq k) (v :: l)
    end

let rec map_of_list_pair
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
: Tot (Map.t key (list value))
= match l with
  | [] -> Map.empty _ _
  | (k, v) :: q ->
    let m = map_of_list_pair key_eq q in
    map_of_list_cons key_eq k v m

let map_of_list_pair_cons
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (q: list (key & value))
: Lemma
  (map_of_list_pair key_eq ((k, v) :: q) == (
    let m = map_of_list_pair key_eq q in
    map_of_list_cons key_eq k v m
  ))
= ()

let rel_slice_of_table
  (#low_key #high_key: Type)
  (#low_value #high_value: Type)
  (key_eq: EqTest.eq_test high_key)
  (rkey: rel low_key high_key)
  (rvalue: rel low_value high_value)
: rel (slice (low_key & low_value)) (Map.t high_key (list high_value))
= mk_rel (fun x y -> exists* l . rel_slice_of_list (rel_pair rkey rvalue) false x l **
    pure (y == map_of_list_pair key_eq l)
  )

let rec map_of_list_pair_mem
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
  (kv: (key & value))
: Lemma
  (ensures (List.Tot.memP kv l <==> begin match Map.get (map_of_list_pair key_eq l) (fst kv) with
  | None -> False
  | Some lv -> List.Tot.memP (snd kv) lv
  end))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> map_of_list_pair_mem key_eq q kv

let rec map_of_list_pair_mem_fst
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
  (k: key)
: Lemma
  (ensures (List.Tot.memP k (List.Tot.map fst l) <==> Some? (Map.get (map_of_list_pair key_eq l) k)))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> map_of_list_pair_mem_fst key_eq q k

let map_of_list_maps_to_nonempty_at
  (#key #value: Type0)
  (m: Map.t key (list value))
  (k: key)
: Tot prop
= match Map.get m k with
  | None -> True
  | Some lv -> List.Tot.length lv >= 1

let rec map_of_list_pair_length
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
  (k: key)
: Lemma
  (ensures (map_of_list_maps_to_nonempty_at (map_of_list_pair key_eq l) k))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> map_of_list_pair_length key_eq q k

let rec map_of_list_pair_no_repeats_key_elim
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
  (k: key)
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (match Map.get (map_of_list_pair key_eq l) k with
  | None -> True
  | Some l -> List.Tot.length l == 1
  ))
= match l with
  | [] -> ()
  | (k1, v1) :: q ->
    map_of_list_pair_no_repeats_key_elim key_eq q k;
    CBOR.Spec.Util.list_memP_map_forall fst q;
    map_of_list_pair_mem_fst key_eq q k1;
    Classical.forall_intro (map_of_list_pair_mem key_eq q);
    map_of_list_pair_length key_eq q k;
    map_of_list_pair_length key_eq q k1

let rec map_of_list_pair_no_repeats_key_intro
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
: Lemma
  (requires forall k . (match Map.get (map_of_list_pair key_eq l) k with
  | None -> True
  | Some l -> List.Tot.length l == 1
  ))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l)))
= match l with
  | [] -> ()
  | (k, v) :: q ->
    map_of_list_pair_mem_fst key_eq q k;
    map_of_list_pair_length key_eq q k;
    map_of_list_pair_no_repeats_key_intro key_eq q

let map_of_list_singletons
  (#key #value: Type0)
  (m: Map.t key (list value))
: Tot prop
= forall k . begin match Map.get m k with
  | None -> True
  | Some l -> List.Tot.length l == 1
  end

let map_of_list_pair_no_repeats_key
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
: Lemma
  (List.Tot.no_repeats_p (List.Tot.map fst l) <==> map_of_list_singletons (map_of_list_pair key_eq l))
= Classical.forall_intro (Classical.move_requires (map_of_list_pair_no_repeats_key_elim key_eq l));
  Classical.move_requires (map_of_list_pair_no_repeats_key_intro key_eq) l

let map_of_list_snoc
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (m: Map.t key (list value))
  (k: key)
  (v: value)
: Tot (Map.t key (list value))
= 
    begin match Map.get m k with
    | None -> Map.set m k (key_eq k) [v]
    | Some l -> Map.set m k (key_eq k) (l `List.Tot.append` [v])
    end

let map_of_list_is_append
  (#key #value: Type)
  (m1 m2 m: Map.t key (list value))
: Tot prop
= forall (x: key) . {:pattern (Map.get m x)} Map.get m x == begin match Map.get m1 x, Map.get m2 x with
    | None, None -> None
    | Some y1, None
    | None, Some y1 -> Some y1
    | Some y1, Some y2 -> Some (List.Tot.append y1 y2)
    end

let map_of_list_is_append_nil_l_intro
  (#key #value: Type)
  (m: Map.t key (list value))
: Lemma
  (map_of_list_is_append (Map.empty _ _) m m)
= ()

let map_of_list_is_append_nil_r_elim
  (#key #value: Type)
  (m1 m2: Map.t key (list value))
: Lemma
  (requires (map_of_list_is_append m1 (Map.empty _ _) m2))
  (ensures (m1 == m2))
= assert (Map.equal m1 m2)

let map_of_list_is_append_cons_snoc_equiv
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (map_of_list_is_append m1 (map_of_list_cons key_eq k v m2) m <==> map_of_list_is_append (map_of_list_snoc key_eq m1 k v) m2 m)
= match Map.get m1 k, Map.get m2 k with
  | Some l1, Some l2 -> List.Tot.append_assoc l1 [v] l2
  | _ -> ()

let map_of_list_maps_to_nonempty
  (#key #value: Type0)
  (m: Map.t key (list value))
: Tot prop
= forall (k: key) . {:pattern (Map.get m k)} map_of_list_maps_to_nonempty_at m k

let map_of_list_pair_length_forall
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
: Lemma
  (ensures (map_of_list_maps_to_nonempty (map_of_list_pair key_eq l)))
  [SMTPat (map_of_list_pair key_eq l)]
= Classical.forall_intro (map_of_list_pair_length key_eq l)

(* FIXME: This DOES NOT work, because a CBOR object is not always
   guaranteed to be serialized into a slice: what if its size exceeds
   SIZE_MAX?

   Ideally, we should be able to copy a CBOR object, but then we need
   to model a `free` function in C.

module U8 = FStar.UInt8

noeq
type cbor_copy_t (cbor_t: Type0) = {
  base: option (V.vec U8.t); // this is the destination buffer to which to copy the CBOR object, that can be freed. Ideally, this field should not be visible from the user. This is in contrast to vec_or_slice, where the user can provide a full Vec.vec containing the elements to serialize
  cbor: cbor_t;
}

module Cbor = CBOR.Spec.API.Format
module Trade = Pulse.Lib.Trade

let rel_cbor_copy_vec_some
  (cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (base: V.vec U8.t)
  (cbor: cbor_t)
  (y: Cbor.cbor)
: Tot slprop
= exists* s .
    Trade.trade
      (vmatch 1.0R cbor y)
      (pts_to base s) **
    pure (V.is_full_vec base)

let rel_cbor_copy_vec
  (cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (freeable: bool)
  (x: cbor_copy_t cbor_t)
  (y: Cbor.cbor)
: Tot slprop
= match x.base with
  | None -> pure (freeable == false)
  | Some base -> rel_cbor_copy_vec_some cbor_t vmatch base x.cbor y

let rel_cbor_copy
  (cbor_t: Type0)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (freeable: bool)
: rel (cbor_copy_t cbor_t) (Cbor.cbor)
= mk_rel (fun x y ->
  vmatch 1.0R x.cbor y **
  rel_cbor_copy_vec cbor_t vmatch freeable x y
)

*)

noeq type cbor_with_perm
  (cbor_t: Type0)
= {
    c: cbor_t;
    p: perm;
  }

module Cbor = CBOR.Spec.API.Format

let rel_cbor_not_freeable
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> Cbor.cbor -> slprop)
  (freeable: bool)
: Tot (rel (cbor_with_perm cbor_t) Cbor.cbor)
= mk_rel (fun x1 x2 -> vmatch x1.p x1.c x2 ** pure (freeable == false))

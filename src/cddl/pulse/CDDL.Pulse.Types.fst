module CDDL.Pulse.Types
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.SeqMatch
module S = Pulse.Lib.Slice.Util
module V = Pulse.Lib.Vec
module Spec = CDDL.Spec.All

module FE = FStar.FunctionalExtensionality

let fe_restricted_arrow (t t': Type) = FE.restricted_t t (fun _ -> t')

let fe_restricted_arrow_eq (#t #t': Type) (f1 f2: fe_restricted_arrow t t') : Lemma
  (requires (FE.feq f1 f2))
  (ensures f1 == f2)
= ()

let fe_restricted_arrow_eq' (#t #t': Type) (f1 f2: fe_restricted_arrow t t')
  (prf: (x: t) -> Lemma
    (f1 x == f2 x)
  )
: Lemma
  (f1 == f2)
= Classical.forall_intro prf;
  fe_restricted_arrow_eq f1 f2

let feq2 (#t1 #t2 #t: Type) (f g: (t1 -> t2 -> t)) : Tot prop =
  forall x1 x2 . f x1 x2 == g x1 x2

let rel (t1 t2: Type) = fe_restricted_arrow t1 (fe_restricted_arrow t2 slprop)

let coerce_rel (#t1 #t': Type) (r: rel t1 t') (t2: Type) (sq: squash (t1 == t2)) : Tot (rel t2 t') = r

let rel_eq (#t #t': Type) (r1 r2: rel t t') : Lemma
  (requires (feq2 r1 r2))
  (ensures r1 == r2)
= fe_restricted_arrow_eq' r1 r2 (fun x ->
    fe_restricted_arrow_eq' (r1 x) (r2 x) (fun x' -> ())
  )

[@@pulse_unfold]
let mk_rel (#t: Type) (#t': Type) (f: (x: t) -> (x': t') -> slprop) : Tot (rel t t') =
  FE.on_dom t (fun x -> FE.on_dom t' (f x))

let rel_always_false (t1 t2: Type0) : rel t1 t2 = mk_rel (fun _ _ -> pure False)

let rel_pure
    (t: Type)
: rel t t
= mk_rel (fun x y -> pure (x == y))

let rel_unit : rel unit unit = mk_rel (fun _ _ -> emp)

noeq
type slice (t: Type) = {
  s: S.slice t;
  p: perm;
}

let rel_slice_of_list
  (#low #high: Type)
  (r: rel low high)
  (freeable: bool)
: rel (slice low) (list high)
= mk_rel (fun x y ->
    exists* s . pts_to x.s #x.p s ** seq_list_match s y r ** pure (freeable == false)
  )

module U64 = FStar.UInt64

noeq
type vec (t: Type) = {
  len: U64.t;
  v: V.vec t;
}


let rel_vec_of_list
  (#low #high: Type)
  (r: rel low high)
: rel (vec low) (list high)
= mk_rel (fun x y ->
    exists* s . pts_to x.v s ** seq_list_match s y r ** pure (V.is_full_vec x.v /\ V.length x.v == U64.v x.len)
  )

noeq
type vec_or_slice (t: Type) =
| Vec of vec t
| Slice of slice t

let rel_vec_or_slice_of_list
  (#low #high: Type)
  (r: rel low high)
  (freeable: bool)
: rel (vec_or_slice low) (list high)
= mk_rel (fun x y ->
  match x with
  | Vec v -> rel_vec_of_list r v y
  | Slice s -> rel_slice_of_list r freeable s y
)

ghost
fn rec seq_list_match_pure_elim
  (#t: Type0)
  (s: Seq.seq t)
  (l: list t)
requires
  seq_list_match s l (rel_pure _)
ensures
  pure (s `Seq.equal` Seq.seq_of_list l)
decreases l
{
  seq_list_match_length  (rel_pure t) s l;
  if (Nil? l) {
    seq_list_match_nil_elim s l (rel_pure _)
  } else {
    let _ = seq_list_match_cons_elim s l (rel_pure _);
    unfold (rel_pure _ (Seq.head s) (List.Tot.hd l));
    seq_list_match_pure_elim (Seq.tail s) (List.Tot.tl l)
  }
}

ghost
fn rec seq_list_match_pure_intro
  (#t: Type0)
  (s: Seq.seq t)
  (l: list t)
requires
  pure (s `Seq.equal` Seq.seq_of_list l)  
ensures
  seq_list_match s l (rel_pure _)
decreases l
{
  if (Nil? l) {
    seq_list_match_nil_intro s l (rel_pure _)
  } else {
    fold (rel_pure _ (Seq.head s) (List.Tot.hd l));
    seq_list_match_pure_intro (Seq.tail s) (List.Tot.tl l);
    seq_list_match_cons_intro (Seq.head s) (List.Tot.hd l) (Seq.tail s) (List.Tot.tl l) (rel_pure _);
    rewrite (seq_list_match 
      (Seq.head s `Seq.cons` Seq.tail s) (List.Tot.hd l :: List.Tot.tl l) (rel_pure _)
    ) as (seq_list_match s l (rel_pure _))
  }
}

let rel_pair
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
: rel (low1 & low2) (high1 & high2)
= mk_rel (fun xlow xhigh -> r1 (fst xlow) (fst xhigh) ** r2 (snd xlow) (snd xhigh))

let rel_pair_eq
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w1: low1)
  (w2: low2)
  (z1: high1)
  (z2: high2)
: Lemma
  (rel_pair r1 r2 (w1, w2) (z1, z2) == r1 w1 z1 ** r2 w2 z2)
= ()

let rel_either
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
: rel (either low1 low2) (either high1 high2)
= mk_rel (fun xlow xhigh -> match xlow, xhigh with
  | Inl xl, Inl xh -> r1 xl xh
  | Inr xl, Inr xh -> r2 xl xh
  | _ -> pure False
)

let rel_either_eq_left
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w1: low1)
  (z1: high1)
: Lemma
  (rel_either r1 r2 (Inl w1) (Inl z1) == r1 w1 z1)
= ()

let rel_either_eq_right
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w2: low2)
  (z2: high2)
: Lemma
  (rel_either r1 r2 (Inr w2) (Inr z2) == r2 w2 z2)
= ()

let rel_either_left
  (#low1 #high: Type)
  (r1: rel low1 high)
  (#low2: Type)
  (r2: rel low2 high)
: rel (either low1 low2) high
= mk_rel (fun xlow xh -> match xlow with
  | Inl xl -> r1 xl xh
  | Inr xl -> r2 xl xh
)

let rel_option
  (#low #high: Type)
  (r: rel low high)
: rel (option low) (option high)
= mk_rel (fun x y -> match x, y with
  | Some x', Some y' -> r x' y'
  | None, None -> emp
  | _ -> pure False
)

let rel_option_eq_some
  (#low #high: Type)
  (r: rel low high)
  (w: low)
  (z: high)
: Lemma
  (rel_option r (Some w) (Some z) == r w z)
= ()

let rel_option_eq_none
  (#low #high: Type)
  (r: rel low high)
: Lemma
  (rel_option r None None == emp)
= ()

let rel_option_right
  (#impl #spec: Type0)
  (r: rel impl spec)
: Tot (rel impl (option spec))
= mk_rel (fun i s -> match s with
  | None -> pure False
  | Some s -> r i s
  )

let rel_bij_l
  (#left #right: Type)
  (r: rel left right)
  (#left': Type)
  (bij: Spec.bijection left left')
: rel left' right
= mk_rel (fun
  (x: left')
  (y: right) ->
   r (bij.bij_to_from x) y
)

let rel_bij_r
  (#left #right: Type)
  (r: rel left right)
  (#right': Type)
  (bij: Spec.bijection right right')
: rel left right'
= mk_rel (fun
  (x: left)
  (y: right')
->
 r x (bij.bij_to_from y)
)

let rel_slice_of_seq
  (#t: Type)
  (freeable: bool)
: rel (slice t) (Seq.seq t)
= mk_rel (fun x y -> pts_to x.s #x.p y ** pure (freeable == false))

let rel_vec_of_seq
  (#t: Type)
: rel (vec t) (Seq.seq t)
= mk_rel (fun x y -> pts_to x.v y ** pure (V.is_full_vec x.v /\ V.length x.v == U64.v x.len))

let rel_vec_or_slice_of_seq
  (#t: Type)
  (freeable: bool)
: rel (vec_or_slice t) (Seq.seq t)
= mk_rel (fun x y -> match x with
  | Vec v -> rel_vec_of_seq v y
  | Slice s -> rel_slice_of_seq freeable s y
)

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

let rel_vec_or_slice_of_table
  (#low_key #high_key: Type)
  (#low_value #high_value: Type)
  (key_eq: EqTest.eq_test high_key)
  (rkey: rel low_key high_key)
  (rvalue: rel low_value high_value)
  (freeable: bool)
: rel (vec_or_slice (low_key & low_value)) (Map.t high_key (list high_value))
= mk_rel (fun x y -> exists* l . rel_vec_or_slice_of_list (rel_pair rkey rvalue) freeable x l **
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

let rec map_of_list_pair_length
  (#key #value: Type0)
  (key_eq: EqTest.eq_test key)
  (l: list (key & value))
  (k: key)
: Lemma
  (ensures (match Map.get (map_of_list_pair key_eq l) k with
  | None -> True
  | Some lv -> List.Tot.length lv >= 1
  ))
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

// A parser implementation that skips some data instead of reading
// it. This parser implementation has no equivalent serializer

let rel_skip (t: Type) : rel (Ghost.erased t) t =
  mk_rel (fun x y -> pure (Ghost.reveal x == y))

let rel_either_skip
  (#t: Type0)
  (#implt: Type0)
  (r: rel implt t)
  (skippable: bool)
: rel (either implt (Ghost.erased t)) t
= mk_rel (fun x y ->
  match x with
  | Inl x -> r x y
  | Inr x -> pure (Ghost.reveal x == y /\ skippable == true)
)

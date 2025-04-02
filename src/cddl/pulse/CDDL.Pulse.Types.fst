module CDDL.Pulse.Types
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.SeqMatch
module S = Pulse.Lib.Slice.Util
module V = Pulse.Lib.Vec
module Spec = CDDL.Spec.All

let rel (t1 t2: Type) = t1 -> t2 -> slprop

let coerce_rel (#t1 #t': Type) (r: rel t1 t') (t2: Type) (sq: squash (t1 == t2)) : Tot (rel t2 t') = r

[@@pulse_unfold]
let mk_rel (#t: Type) (#t': Type) (f: (x: t) -> (x': t') -> slprop) : Tot (rel t t') = f

let rel_always_false (t1 t2: Type0) : rel t1 t2 = mk_rel (fun _ _ -> pure False)

let rel_pure
    (t: Type)
: rel t t
= mk_rel (fun x y -> pure (x == y))

let rel_pure_eq
  (#t: Type)
  (x1 x2: t)
: Lemma
  (rel_pure t x1 x2 == pure (x1 == x2))
= ()

ghost fn rel_pure_intro
  (#t: Type0)
  (x: t)
requires emp
ensures rel_pure t x x
{
  rel_pure_eq x x;
  fold (rel_pure _ x x)
}

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

ghost fn rel_pair_intro
  (#tl1 #th1 #tl2 #th2: Type0)
  (r1: rel tl1 th1)
  (x1: tl1)
  (y1: th1)
  (r2: rel tl2 th2)
  (x2: tl2)
  (y2: th2)
requires r1 x1 y1 ** r2 x2 y2
ensures rel_pair r1 r2 (x1, x2) (y1, y2)
{
  rel_pair_eq r1 r2 x1 x2 y1 y2;
  rewrite (r1 x1 y1 ** r2 x2 y2) as (rel_pair r1 r2 (x1, x2) (y1, y2))
}

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

ghost fn rel_either_cases
  (#t1 #t2 #it1 #it2: Type0)
  (r1: rel it1 t1)
  (r2: rel it2 t2)
  (x: either it1 it2)
  (y: either t1 t2)
requires
  rel_either r1 r2 x y
ensures
  rel_either r1 r2 x y **
  pure (Inl? x <==> Inl? y)
{
  match x {
    Inl x1 -> {
      match y {
        Inl y1 -> {
          rewrite (rel_either r1 r2 (Inl x1) (Inl y1))
            as (rel_either r1 r2 x y)
        }
        Inr y2 -> {
          unfold (rel_either r1 r2 (Inl x1) (Inr y2));
          assert (pure False);
          rewrite emp as (rel_either r1 r2 x y)
        }
      }
    }
    Inr x2 -> {
      match y {
        Inl y1 -> {
          unfold (rel_either r1 r2 (Inr x2) (Inl y1));
          assert (pure False);
          rewrite emp as (rel_either r1 r2 x y)
        }
        Inr y2 -> {
          rewrite (rel_either r1 r2 (Inr x2) (Inr y2))
            as (rel_either r1 r2 x y)
        }
      }
    }
  }
}

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

ghost fn rel_option_cases
  (#t1 #it1: Type0)
  (r1: rel it1 t1)
  (x: option it1)
  (y: option t1)
requires
  rel_option r1 x y
ensures
  rel_option r1 x y **
  pure (Some? x <==> Some? y)
{
  match x {
    Some x1 -> {
      match y {
        Some y1 -> {
          rewrite (rel_option r1 (Some x1) (Some y1))
            as (rel_option r1 x y)
        }
        None -> {
          unfold (rel_option r1 (Some x1) None);
          assert (pure False);
          rewrite emp as (rel_option r1 x y)
        }
      }
    }
    None -> {
      match y {
        Some y1 -> {
          unfold (rel_option r1 None (Some y1));
          assert (pure False);
          rewrite emp as (rel_option r1 x y)
        }
        None -> {
          rewrite (rel_option r1 None None)
            as (rel_option r1 x y)
        }
      }
    }
  }
}

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

ghost fn rel_option_some_intro
  (#t1 #t2: Type0)
  (r: rel t1 t2)
  (x: t1)
  (y: t2)
requires r x y
ensures rel_option r (Some x) (Some y)
{
  rel_option_eq_some r x y;
  rewrite (r x y) as (rel_option r (Some x) (Some y))
}

let rel_option_right
  (#impl #spec: Type0)
  (r: rel impl spec)
: Tot (rel impl (option spec))
= mk_rel (fun i s -> match s with
  | None -> pure False
  | Some s -> r i s
  )

let rel_fun
  (#impl #spec: Type0)
  (r: rel impl spec)
  (#impl' #spec' : Type0)
  (f_impl : impl' -> impl)
  (f_spec : spec' -> spec)
: Tot (rel impl' spec')
= mk_rel (fun i s -> r (f_impl i) (f_spec s))

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

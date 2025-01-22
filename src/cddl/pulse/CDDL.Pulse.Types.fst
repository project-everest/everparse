module CDDL.Pulse.Types
open Pulse.Lib.Pervasives
open Pulse.Lib.SeqMatch
module S = Pulse.Lib.Slice.Util
module V = Pulse.Lib.Vec
module Spec = CDDL.Spec.All

let rel (t1 t2: Type) = t1 -> t2 -> slprop

let rel_always_false (t1 t2: Type0) (x1: t1) (x2: t2) : Tot slprop =
  pure False

let rel_pure
    (t: Type)
    (x y: t)
: Tot slprop
= pure (x == y)

let rel_unit : rel unit unit = fun _ _ -> emp

let rel_slice_of_list
  (#low #high: Type)
  (r: rel low high)
  (freeable: bool)
  (x: S.slice low)
  (y: list high)
: slprop
= exists* s . pts_to x s ** seq_list_match s y r ** pure (freeable == false)

module U64 = FStar.UInt64

noeq
type vec (t: Type) = {
  len: U64.t;
  v: V.vec t;
}

let rel_vec_of_list
  (#low #high: Type)
  (r: rel low high)
  (x: vec low)
  (y: list high)
: slprop
= exists* s . pts_to x.v s ** seq_list_match s y r ** pure (V.is_full_vec x.v /\ V.length x.v == U64.v x.len)

noeq
type vec_or_slice (t: Type) =
| Vec of vec t
| Slice of S.slice t

let rel_vec_or_slice_of_list
  (#low #high: Type)
  (r: rel low high)
  (freeable: bool)
  (x: vec_or_slice low)
  (y: list high)
: Tot slprop
= match x with
  | Vec v -> rel_vec_of_list r v y
  | Slice s -> rel_slice_of_list r freeable s y

```pulse
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
```

```pulse
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
```

let rel_pair
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (xlow: (low1 & low2)) (xhigh: (high1 & high2))
: slprop
= r1 (fst xlow) (fst xhigh) ** r2 (snd xlow) (snd xhigh)

let rel_either
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (xlow: (low1 `either` low2)) (xhigh: (high1 `either` high2))
: slprop
= match xlow, xhigh with
| Inl xl, Inl xh -> r1 xl xh
| Inr xl, Inr xh -> r2 xl xh
| _ -> pure False

let rel_option
  (#low #high: Type)
  (r: rel low high)
  (x: option low)
  (y: option high)
: slprop
= match x, y with
  | Some x', Some y' -> r x' y'
  | None, None -> emp
  | _ -> pure False

let rel_bij_l
  (#left #right: Type)
  (r: rel left right)
  (#left': Type)
  (bij: Spec.bijection left left')
: rel left' right
= fun
  (x: left')
  (y: right) ->
   r (bij.bij_to_from x) y

let rel_bij_r
  (#left #right: Type)
  (r: rel left right)
  (#right': Type)
  (bij: Spec.bijection right right')
: rel left right'
= fun
  (x: left)
  (y: right')
->
 r x (bij.bij_to_from y)
  
let rel_slice_of_seq
  (#t: Type)
  (freeable: bool)
  (x: S.slice t)
  (y: Seq.seq t)
: Tot slprop
= pts_to x y ** pure (freeable == false)

let rel_vec_of_seq
  (#t: Type)
  (x: vec t)
  (y: Seq.seq t)
: Tot slprop
= pts_to x.v y ** pure (V.is_full_vec x.v /\ V.length x.v == U64.v x.len)

let rel_vec_or_slice_of_seq
  (#t: Type)
  (freeable: bool)
  (x: vec_or_slice t)
  (y: Seq.seq t)
: Tot slprop
= match x with
  | Vec v -> rel_vec_of_seq v y
  | Slice s -> rel_slice_of_seq freeable s y

module Map = CDDL.Spec.Map

let rec map_of_list_pair
  (#key #value: Type0)
  (key_eq: (k1: key) -> (k2: key) -> Pure bool True (fun b -> b == true <==> k1 == k2))
  (l: list (key & value))
: Tot (Map.t key (list value))
= match l with
  | [] -> Map.empty _ _
  | (k, v) :: q ->
    let m = map_of_list_pair key_eq q in
    begin match Map.get m k with
    | None -> Map.set m k (key_eq k) [v]
    | Some l -> Map.set m k (key_eq k) (v :: l)
    end

let rel_vec_or_slice_of_table
  (#low_key #high_key: Type)
  (#low_value #high_value: Type)
  (key_eq: (k1: high_key) -> (k2: high_key) -> Pure bool True (fun b -> b == true <==> k1 == k2))
  (rkey: rel low_key high_key)
  (rvalue: rel low_value high_value)
  (freeable: bool)
  (x: vec_or_slice (low_key & low_value))
  (y: Map.t high_key (list high_value))
: Tot slprop
= exists* l . rel_vec_or_slice_of_list (rel_pair rkey rvalue) freeable x l **
    pure (y == map_of_list_pair key_eq l)

let rec map_of_list_pair_mem
  (#key #value: Type0)
  (key_eq: (k1: key) -> (k2: key) -> Pure bool True (fun b -> b == true <==> k1 == k2))
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
  (key_eq: (k1: key) -> (k2: key) -> Pure bool True (fun b -> b == true <==> k1 == k2))
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
  (key_eq: (k1: key) -> (k2: key) -> Pure bool True (fun b -> b == true <==> k1 == k2))
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
  (key_eq: (k1: key) -> (k2: key) -> Pure bool True (fun b -> b == true <==> k1 == k2))
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
  (key_eq: (k1: key) -> (k2: key) -> Pure bool True (fun b -> b == true <==> k1 == k2))
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

let map_of_list_pair_no_repeats_key
  (#key #value: Type0)
  (key_eq: (k1: key) -> (k2: key) -> Pure bool True (fun b -> b == true <==> k1 == k2))
  (l: list (key & value))
: Lemma
  (List.Tot.no_repeats_p (List.Tot.map fst l) <==> forall k . (match Map.get (map_of_list_pair key_eq l) k with
  | None -> True
  | Some l -> List.Tot.length l == 1
  ))
= Classical.forall_intro (Classical.move_requires (map_of_list_pair_no_repeats_key_elim key_eq l));
  Classical.move_requires (map_of_list_pair_no_repeats_key_intro key_eq) l

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
  (x: cbor_copy_t cbor_t)
  (y: Cbor.cbor)
: Tot slprop
= vmatch 1.0R x.cbor y **
  rel_cbor_copy_vec cbor_t vmatch freeable x y

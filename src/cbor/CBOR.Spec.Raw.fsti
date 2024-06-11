module CBOR.Spec.Raw
include CBOR.Spec.Constants

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* Raw data items, disregarding ordering of map entries *)

let nlist ([@@@strictly_positive] t: eqtype) (n: nat) : Tot eqtype = (l: list t { List.Tot.length l == n })

type integer_size = (n: nat { n < 4 })

open FStar.Mul

type raw_uint64 = {
  size: integer_size;
  value: (x: U64.t { U64.v x < pow2 (8 * pow2 size) })
}

let _ = assert_norm (8 * pow2 3 == 64)

type raw_data_item : eqtype
= | Simple: (v: simple_value) -> raw_data_item
  | Int64: (typ: major_type_uint64_or_neg_int64) -> (v: raw_uint64) -> raw_data_item
  | String: (typ: major_type_byte_string_or_text_string) -> (len: raw_uint64) -> (v: Seq.lseq U8.t (U64.v len.value)) -> raw_data_item // Section 3.1: "a string containing an invalid UTF-8 sequence is well-formed but invalid", so we don't care about UTF-8 specifics here.
  | Array: (len: raw_uint64) -> (v: nlist raw_data_item (U64.v len.value)) -> raw_data_item
  | Map: (len: raw_uint64) -> (v: nlist (raw_data_item & raw_data_item) (U64.v len.value)) -> raw_data_item
  | Tagged: (tag: raw_uint64) -> (v: raw_data_item) -> raw_data_item
//  | Float: (v: Float.float) -> raw_data_item // TODO

let dummy_raw_data_item : Ghost.erased raw_data_item =
  Int64 cbor_major_type_uint64 { size = 0; value = 0uL }

let raw_uint64_equiv (x1 x2: raw_uint64) : Tot bool =
  x1.value = x2.value

let rec list_forall2 (#t1 #t2: Type) (l1: list t1) (l2: list t2) (p: (x1: t1) -> (x2: t2 { x1 << l1 /\ x2 << l2 }) -> bool) : Tot bool (decreases l1) =
  match l1, l2 with
  | [], [] -> true
  | a1 :: q1, a2 :: q2 -> p a1 a2 && list_forall2 q1 q2 p
  | _ -> false

(*
let rec list_forall (#t: Type) (l: list t) (p: (x: t { x << l }) -> bool) : bool =
  match l with
  | [] -> true
  | a :: q -> p a && list_forall q p

let rec list_exists (#t: Type) (l: list t) (p: (x: t { x << l }) -> bool) : bool =
  match l with
  | [] -> false
  | a :: q -> p a || list_exists q p

let list_exists2 (#t': Type) (l0: list t') (#t: Type) (l: list t) (p: (x': t') -> (x: t { x' << l0 /\ x << l }) -> bool) (x: t' { x << l0 }) : bool =
  list_exists l (p x)

let list_exists1_swap (#t': Type) (#t: Type) (l: list t) (p: (x: t) -> (x': t' { x << l }) -> bool) (x: t') : bool =
  list_exists l (fun x' -> p x' x)

let rec raw_equiv (l1 l2: raw_data_item) : Tot bool (decreases l1) =
  match l1, l2 with
  | Simple v1, Simple v2 -> v1 = v2
  | Int64 ty1 v1, Int64 ty2 v2 -> ty1 = ty2 && raw_uint64_equiv v1 v2
  | String ty1 len1 v1, String ty2 len2 v2 -> ty1 = ty2 && raw_uint64_equiv len1 len2 && v1 = v2
  | Array len1 v1, Array len2 v2 -> raw_uint64_equiv len1 len2 && list_forall2 v1 v2 raw_equiv
  | Map len1 v1, Map len2 v2 ->
    raw_uint64_equiv len1 len2 &&
    list_forall v1 (list_exists2 v1 v2 raw_pair_equiv) &&
    list_forall v2 (list_exists1_swap v1 raw_pair_equiv)
  | Tagged tag1 v1, Tagged tag2 v2 ->
    raw_uint64_equiv tag1 tag2 &&
    raw_equiv v1 v2
  | _ -> false

and raw_pair_equiv (l1 l2: (raw_data_item & raw_data_item)) : Tot bool (decreases l1) =
  raw_equiv (fst l1) (fst l2) && raw_equiv (snd l1) (snd l2)
*)

val raw_equiv (l1 l2: raw_data_item) : Tot bool

noextract
let holds_on_pair2
  (#t: Type)
  (pred: (t -> t -> bool))
  (x: (t & t))
  (y: (t & t))
: Tot bool
= let (x1, x2) = x in
  let (y1, y2) = y in
  pred x1 y1 && pred x2 y2

let list_for_all_exists (#t1 #t2: Type) (p: t1 -> t2 -> bool) (l1: list t1) (l2: list t2) : bool =
  List.Tot.for_all (fun x -> List.Tot.existsb (p x) l2) l1

let rec list_for_all_exists_eq (#t1 #t2: Type) (p: t1 -> t2 -> bool) (l1: list t1) (l2: list t2) : Lemma
  (ensures (list_for_all_exists p l1 l2 == begin match l1 with
  | [] -> true
  | a :: q -> List.Tot.existsb (p a) l2 && list_for_all_exists p q l2
  end))
= match l1 with
  | [] -> ()
  | _ :: q -> list_for_all_exists_eq p q l2

val raw_equiv_eq (l1 l2: raw_data_item) : Lemma
  (raw_equiv l1 l2 == begin match l1, l2 with
  | Simple v1, Simple v2 -> v1 = v2
  | Int64 ty1 v1, Int64 ty2 v2 -> ty1 = ty2 && raw_uint64_equiv v1 v2
  | String ty1 len1 v1, String ty2 len2 v2 -> ty1 = ty2 && raw_uint64_equiv len1 len2 && v1 = v2
  | Array len1 v1, Array len2 v2 -> raw_uint64_equiv len1 len2 && list_forall2 v1 v2 raw_equiv
  | Map len1 v1, Map len2 v2 ->
    raw_uint64_equiv len1 len2 &&
    list_for_all_exists (holds_on_pair2 raw_equiv) v1 v2 &&
    list_for_all_exists (holds_on_pair2 raw_equiv) v2 v1
  | Tagged tag1 v1, Tagged tag2 v2 ->
    raw_uint64_equiv tag1 tag2 &&
    raw_equiv v1 v2
  | _ -> false
  end)

val raw_equiv_sym (l1 l2: raw_data_item) : Lemma
  (raw_equiv l1 l2 == raw_equiv l2 l1)

noextract
let get_major_type
  (d: raw_data_item)
: Tot major_type_t
= match d with
  | Simple _ -> cbor_major_type_simple_value
  | Int64 m _ -> m
  | String m _ _ -> m
  | Array _ _ -> cbor_major_type_array
  | Map _ _ -> cbor_major_type_map
  | Tagged _ _ -> cbor_major_type_tagged

noextract
let holds_on_pair
  (#t: Type)
  (pred: (t -> bool))
  (x: (t & t))
: Tot bool
= let (x1, x2) = x in
  pred x1 && pred x2

let andp (#t: Type) (p1 p2: t -> bool) (x: t) : bool =
  p1 x && p2 x

let holds_on_pair_andp
  (#t: Type)
  (p1 p2: (t -> bool))
  (x: (t & t))
: Lemma
  (holds_on_pair (andp p1 p2) x == (holds_on_pair p1 x && holds_on_pair p2 x))
= ()

let rec list_for_all_implies
  (#t: Type)
  (p1 p2: t -> bool)
  (l: list t)
  (prf: (x: t { x << l }) -> Lemma
    (p1 x == true ==> p2 x == true)
  )
: Lemma
  (ensures (List.Tot.for_all p1 l == true ==> List.Tot.for_all p2 l == true))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> prf a; list_for_all_implies p1 p2 q prf

let list_for_all_ext
  (#t: Type)
  (p1 p2: t -> bool)
  (l: list t)
  (prf: (x: t { x << l }) -> Lemma
    (p1 x == p2 x)
  )
: Lemma
  (ensures (List.Tot.for_all p1 l == List.Tot.for_all p2 l))
= list_for_all_implies p1 p2 l (fun x -> prf x);
  list_for_all_implies p2 p1 l (fun x -> prf x)

let rec list_for_all_andp
  (#t: Type)
  (p1 p2: t -> bool)
  (l: list t)
: Lemma
  (ensures (
    List.Tot.for_all (andp p1 p2) l == (List.Tot.for_all p1 l && List.Tot.for_all p2 l)
  ))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_andp p1 p2 q

noextract
val holds_on_raw_data_item
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool

noextract
let holds_on_raw_data_item'
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= p x &&
  begin match x with
  | Array _ l -> List.Tot.for_all (holds_on_raw_data_item p) l
  | Map _ l ->
    List.Tot.for_all (holds_on_pair (holds_on_raw_data_item p)) l
  | Tagged _ v -> holds_on_raw_data_item p v
  | _ -> true
  end

val holds_on_raw_data_item_eq
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (holds_on_raw_data_item p x == holds_on_raw_data_item' p x)

let rec holds_on_raw_data_item_andp
  (p1 p2: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (ensures (
    holds_on_raw_data_item (andp p1 p2) x == (holds_on_raw_data_item p1 x && holds_on_raw_data_item p2 x)
  ))
  (decreases x)
= holds_on_raw_data_item_eq (andp p1 p2) x;
  holds_on_raw_data_item_eq p1 x;
  holds_on_raw_data_item_eq p2 x;
  match x with
  | Array _ l ->
    list_for_all_ext (holds_on_raw_data_item (andp p1 p2)) (andp (holds_on_raw_data_item p1) (holds_on_raw_data_item p2)) l (fun x -> holds_on_raw_data_item_andp p1 p2 x);
    list_for_all_andp (holds_on_raw_data_item p1) (holds_on_raw_data_item p2) l
  | Map _ l ->
    list_for_all_ext (holds_on_pair (holds_on_raw_data_item (andp p1 p2))) (andp (holds_on_pair (holds_on_raw_data_item p1)) (holds_on_pair (holds_on_raw_data_item p2))) l (fun x ->
      holds_on_raw_data_item_andp p1 p2 (fst x);
      holds_on_raw_data_item_andp p1 p2 (snd x)
    );
    list_for_all_andp (holds_on_pair (holds_on_raw_data_item p1)) (holds_on_pair (holds_on_raw_data_item p2)) l
  | Tagged _ x' -> holds_on_raw_data_item_andp p1 p2 x'
  | _ -> ()

let holds_on_raw_data_item_eq_simple
  (p: (raw_data_item -> bool))
  (v: simple_value)
: Lemma
  (holds_on_raw_data_item p (Simple v) == p (Simple v))
  [SMTPat (holds_on_raw_data_item p (Simple v))]
= holds_on_raw_data_item_eq p (Simple v)

let holds_on_raw_data_item_eq_int64
  (p: (raw_data_item -> bool))
  (typ: major_type_uint64_or_neg_int64)
  (v: raw_uint64)
: Lemma
  (holds_on_raw_data_item p (Int64 typ v) == p (Int64 typ v))
  [SMTPat (holds_on_raw_data_item p (Int64 typ v))]
= holds_on_raw_data_item_eq p (Int64 typ v)

let holds_on_raw_data_item_eq_string
  (p: (raw_data_item -> bool))
  (typ: major_type_byte_string_or_text_string)
  (len: raw_uint64)
  (v: Seq.lseq U8.t (U64.v len.value))
: Lemma
  (holds_on_raw_data_item p (String typ len v) == p (String typ len v))
  [SMTPat (holds_on_raw_data_item p (String typ len v))]
= holds_on_raw_data_item_eq p (String typ len v)

let holds_on_raw_data_item_eq_array
  (p: (raw_data_item -> bool))
  (len: raw_uint64)
  (v: nlist raw_data_item (U64.v len.value))
: Lemma
  (holds_on_raw_data_item p (Array len v) == (p (Array len v) && List.Tot.for_all (holds_on_raw_data_item p) v))
  [SMTPat (holds_on_raw_data_item p (Array len v))]
= holds_on_raw_data_item_eq p (Array len v)

let holds_on_raw_data_item_eq_map
  (p: (raw_data_item -> bool))
  (len: raw_uint64)
  (v: nlist (raw_data_item & raw_data_item) (U64.v len.value))
: Lemma
  (holds_on_raw_data_item p (Map len v) == (p (Map len v) && List.Tot.for_all (holds_on_pair (holds_on_raw_data_item p)) v))
  [SMTPat (holds_on_raw_data_item p (Map len v))]
= holds_on_raw_data_item_eq p (Map len v)

let holds_on_raw_data_item_eq_tagged
  (p: (raw_data_item -> bool))
  (tag: raw_uint64)
  (v: raw_data_item)
: Lemma
  (holds_on_raw_data_item p (Tagged tag v) <==> (p (Tagged tag v) && holds_on_raw_data_item p v))
  [SMTPat (holds_on_raw_data_item p (Tagged tag v))]
= holds_on_raw_data_item_eq p (Tagged tag v)

noextract
let map_entry_order
  (#key: Type)
  (key_order: (key -> key -> bool))
  (value: Type)
  (m1: (key & value))
  (m2: (key & value))
: Tot bool
= key_order (fst m1) (fst m2)

noextract
let raw_data_item_sorted_elem (order: (raw_data_item -> raw_data_item -> bool)) (x: raw_data_item) : Tot bool
= match x with
  | Map _ l ->
      FStar.List.Tot.sorted (map_entry_order order _) l
  | _ -> true

noextract
let raw_data_item_sorted (order: (raw_data_item -> raw_data_item -> bool)) : Tot (raw_data_item -> bool)
= holds_on_raw_data_item (raw_data_item_sorted_elem order)

let raw_uint64_optimal (x: raw_uint64) : Tot bool =
  if x.size = 0
  then true
  else pow2 (8 * pow2 (x.size - 1)) <= U64.v x.value

let raw_uint64_optimal_unique (x1 x2: raw_uint64) : Lemma
  (requires (raw_uint64_optimal x1 /\ raw_uint64_optimal x2 /\ raw_uint64_equiv x1 x2))
  (ensures (x1 == x2))
= ()

let rec raw_uint64_optimize (x: raw_uint64) : Pure raw_uint64
  (requires True)
  (ensures (fun x' -> raw_uint64_equiv x x' /\ raw_uint64_optimal x'))
  (decreases x.size)
= if x.size = 0
  then x
  else if pow2 (8 * pow2 (x.size - 1)) <= U64.v x.value
  then x
  else raw_uint64_optimize { x with size = x.size - 1 }

let raw_data_item_ints_optimal_elem (x: raw_data_item) : Tot bool =
  match x with
  | Int64 _ v
  | String _ v _
  | Array v _
  | Map v _
  | Tagged v _
    -> raw_uint64_optimal v
  | Simple _ -> true

let raw_data_item_ints_optimal (x: raw_data_item) : Tot bool =
  holds_on_raw_data_item raw_data_item_ints_optimal_elem x

let rec list_no_setoid_repeats
  (#t: Type)
  (equiv: t -> t -> bool)
  (l: list t)
: Tot bool
  (decreases l)
= match l with
  | [] -> true
  | [_] -> true
  | a :: q ->
    list_no_setoid_repeats equiv q &&
    not (List.Tot.existsb (equiv a) q)

let valid_raw_data_item_elem
  (l: raw_data_item)
: Tot bool
= match l with
  | Map _ v -> list_no_setoid_repeats (holds_on_pair2 raw_equiv) v
  | _ -> true

let valid_raw_data_item
  (l: raw_data_item)
: Tot bool
= holds_on_raw_data_item valid_raw_data_item_elem l

let order_irrefl
  (#t: Type)
  (order: t -> t -> bool)
: Tot prop
= forall x . ~ (order x x)

let order_trans
  (#t: Type)
  (order: t -> t -> bool)
: Tot prop
= forall x y z . (order x y /\ order y z) ==> order x z

let rec raw_equiv_sorted_optimal
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x1 x2: raw_data_item)
: Lemma
  (requires (
    raw_equiv x1 x2 /\
    raw_data_item_sorted order x1 /\
    raw_data_item_sorted order x2 /\
    raw_data_item_ints_optimal x1 /\
    raw_data_item_ints_optimal x2
  ))
  (ensures (x1 == x2))
  (decreases x1)
= raw_equiv_eq x1 x2;
  match x1, x2 with
  | Simple _, Simple _ -> ()
  | Int64 _ v1, Int64 _ v2 ->
    raw_uint64_optimal_unique v1 v2
  | _ -> admit ()

let rec raw_data_item_sorted_optimal_valid
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x1: raw_data_item)
: Lemma
  (requires (
    raw_data_item_sorted order x1 /\
    raw_data_item_ints_optimal x1
  ))
  (ensures (valid_raw_data_item x1))
= holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x1;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x1;
  match x1 with
  | Simple _
  | Int64 _ _
  | String _ _ _
    -> ()
  | Tagged tag v -> raw_data_item_sorted_optimal_valid order v
  | _ -> assume False

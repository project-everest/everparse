module CBOR.Spec.Raw.Base
include CBOR.Spec.Constants
open CBOR.Spec.Util

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* Raw data items, disregarding ordering of map entries *)

let nlist ([@@@strictly_positive] t: eqtype) (n: nat) : Tot eqtype = (l: list t { List.Tot.length l == n })

type integer_size = (n: U8.t { U8.v n <= 4 })

open FStar.Mul

let raw_uint64_size_prop (size: integer_size) (value: U64.t) : Tot prop =
  if U8.v size = 0
  then U64.v value <= U8.v max_simple_value_additional_info
  else U64.v value < pow2 (8 * pow2 (U8.v size - 1))

type raw_uint64 = {
  size: integer_size;
  value: (value: U64.t { raw_uint64_size_prop size value })
}

let _ = assert_norm (8 * pow2 3 == 64)

type raw_data_item : eqtype
= | Simple: (v: simple_value) -> raw_data_item
  | Int64: (typ: major_type_uint64_or_neg_int64) -> (v: raw_uint64) -> raw_data_item
  | String: (typ: major_type_byte_string_or_text_string) -> (len: raw_uint64) -> (v: Seq.lseq U8.t (U64.v len.value) { typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v}) -> raw_data_item // Section 3.1: "a string containing an invalid UTF-8 sequence is well-formed but invalid", so we don't care about UTF-8 specifics here.
  | Array: (len: raw_uint64) -> (v: nlist raw_data_item (U64.v len.value)) -> raw_data_item
  | Map: (len: raw_uint64) -> (v: nlist (raw_data_item & raw_data_item) (U64.v len.value)) -> raw_data_item
  | Tagged: (tag: raw_uint64) -> (v: raw_data_item) -> raw_data_item
//  | Float: (v: Float.float) -> raw_data_item // TODO

let dummy_raw_data_item : Ghost.erased raw_data_item =
  Int64 cbor_major_type_uint64 { size = 0uy; value = 0uL }

let raw_uint64_equiv (x1 x2: raw_uint64) : Tot bool =
  x1.value = x2.value

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
val holds_on_raw_data_item
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool

noextract
let pre_holds_on_raw_data_item
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= begin match x with
  | Array _ l -> List.Tot.for_all (holds_on_raw_data_item p) l
  | Map _ l ->
    List.Tot.for_all (holds_on_pair (holds_on_raw_data_item p)) l
  | Tagged _ v -> holds_on_raw_data_item p v
  | _ -> true
  end

noextract
let holds_on_raw_data_item'
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= p x &&
  pre_holds_on_raw_data_item p x

val holds_on_raw_data_item_eq
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (holds_on_raw_data_item p x == holds_on_raw_data_item' p x)

(*
let holds_on_raw_data_item_weaken
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (requires (holds_on_raw_data_item p x == true))
  (ensures (p x == true))
  [SMTPat (holds_on_raw_data_item p x)]
= holds_on_raw_data_item_eq p x
*)

let rec holds_on_raw_data_item_truep
  (x: raw_data_item)
: Lemma
  (ensures (
    holds_on_raw_data_item truep x == true
  ))
  (decreases x)
= holds_on_raw_data_item_eq truep x;
  match x with
  | Array _ l ->
    list_for_all_intro (holds_on_raw_data_item truep) l (fun x -> holds_on_raw_data_item_truep x)
  | Map _ l ->
    list_for_all_intro (holds_on_pair (holds_on_raw_data_item truep)) l (fun x ->
      holds_on_raw_data_item_truep (fst x);
      holds_on_raw_data_item_truep (snd x)
    )
  | Tagged _ x' -> holds_on_raw_data_item_truep x'
  | _ -> ()

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

let rec holds_on_raw_data_item_implies
  (p1 p2: (raw_data_item -> bool))
  (prf: ((x': raw_data_item) -> Lemma
    (requires (holds_on_raw_data_item p1 x' == true))
    (ensures (p2 x' == true))
  ))
  (x: raw_data_item)
: Lemma
  (requires (holds_on_raw_data_item p1 x))
  (ensures (holds_on_raw_data_item p2 x == true))
  (decreases x)
= holds_on_raw_data_item_eq p1 x;
  holds_on_raw_data_item_eq p2 x;
  prf x;
  match x with
  | Array _ v ->
    list_for_all_implies (holds_on_raw_data_item p1) (holds_on_raw_data_item p2) v (fun x -> holds_on_raw_data_item_implies p1 p2 prf x)
  | Tagged _ v -> holds_on_raw_data_item_implies p1 p2 prf v
  | Map _ v ->
    list_for_all_implies (holds_on_pair (holds_on_raw_data_item p1)) (holds_on_pair (holds_on_raw_data_item p2)) v (fun x ->
      holds_on_raw_data_item_implies p1 p2 prf (fst x);
      holds_on_raw_data_item_implies p1 p2 prf (snd x)
    )
  | _ -> ()

// FIXME: avoid this code duplication
let pre_holds_on_raw_data_item_implies
  (p1 p2: (raw_data_item -> bool))
  (prf: ((x': raw_data_item) -> Lemma
    (requires (holds_on_raw_data_item p1 x' == true))
    (ensures (p2 x' == true))
  ))
  (x: raw_data_item)
: Lemma
  (requires (pre_holds_on_raw_data_item p1 x))
  (ensures (pre_holds_on_raw_data_item p2 x == true))
  (decreases x)
= match x with
  | Array _ v ->
    list_for_all_implies (holds_on_raw_data_item p1) (holds_on_raw_data_item p2) v (fun x -> holds_on_raw_data_item_implies p1 p2 prf x)
  | Tagged _ v -> holds_on_raw_data_item_implies p1 p2 prf v
  | Map _ v ->
    list_for_all_implies (holds_on_pair (holds_on_raw_data_item p1)) (holds_on_pair (holds_on_raw_data_item p2)) v (fun x ->
      holds_on_raw_data_item_implies p1 p2 prf (fst x);
      holds_on_raw_data_item_implies p1 p2 prf (snd x)
    )
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
  (v: Seq.lseq U8.t (U64.v len.value) { typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v})
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

val raw_data_item_size
  (x: raw_data_item)
: Tot nat

val raw_data_item_size_eq
  (x: raw_data_item)
: Lemma
  (raw_data_item_size x == begin match x with
  | Array _ v -> 2 + list_sum raw_data_item_size v
  | Map _ v -> 2 + list_sum (pair_sum raw_data_item_size raw_data_item_size) v
  | Tagged _ v -> 2 + raw_data_item_size v
  | _ -> 1
  end)

val raw_data_item_fmap
  (f: raw_data_item -> raw_data_item)
  (x: raw_data_item)
: Tot raw_data_item

let pre_raw_data_item_fmap
  (f: raw_data_item -> raw_data_item)
  (x: raw_data_item)
: Tot raw_data_item
= match x with
  | Map len v -> Map len (List.Tot.map (apply_on_pair (raw_data_item_fmap f)) v)
  | Array len v -> Array len (List.Tot.map (raw_data_item_fmap f) v)
  | Tagged tag v -> Tagged tag (raw_data_item_fmap f v)
  | _ -> x

val raw_data_item_fmap_eq
  (f: raw_data_item -> raw_data_item)
  (x: raw_data_item)
: Lemma
  (raw_data_item_fmap f x == f (pre_raw_data_item_fmap f x))

val holds_on_raw_data_item_fmap_gen
  (f: raw_data_item -> raw_data_item)
  (p q: raw_data_item -> bool)
  (prf1: (x: raw_data_item) -> Lemma
    (requires (
      holds_on_raw_data_item p x == true /\
      pre_holds_on_raw_data_item (p `andp` q) (pre_raw_data_item_fmap f x) == true
    ))
    (ensures (
      p (pre_raw_data_item_fmap f x) == true
    ))
  )
  (prf: (x: raw_data_item) -> Lemma
    (requires (holds_on_raw_data_item p x == true /\
    pre_holds_on_raw_data_item q x == true))
    (ensures (holds_on_raw_data_item (p `andp` q) (f x) == true))
  )
  (x: raw_data_item)
: Lemma
  (requires (holds_on_raw_data_item p x == true))
  (ensures (holds_on_raw_data_item (p `andp` q) (raw_data_item_fmap f x) == true))

let holds_on_raw_data_item_fmap_inv
  (f: raw_data_item -> raw_data_item)
  (p: raw_data_item -> bool)
  (prf1: (x: raw_data_item) -> Lemma
    (requires (
      holds_on_raw_data_item p x == true /\
      pre_holds_on_raw_data_item p (pre_raw_data_item_fmap f x) == true
    ))
    (ensures (
      p (pre_raw_data_item_fmap f x) == true
    ))
  )
  (prf: (x: raw_data_item) -> Lemma
    (requires (holds_on_raw_data_item p x == true))
    (ensures (holds_on_raw_data_item p (f x) == true))
  )
  (x: raw_data_item)
: Lemma
  (requires (holds_on_raw_data_item p x == true))
  (ensures (holds_on_raw_data_item p (raw_data_item_fmap f x) == true))
= holds_on_raw_data_item_fmap_gen f p truep
    (fun x ->
      pre_holds_on_raw_data_item_implies (p `andp` truep) p (fun x -> holds_on_raw_data_item_eq (p `andp` truep) x) (pre_raw_data_item_fmap f x);
      prf1 x
    )
    (fun x ->
      holds_on_raw_data_item_truep x;
      holds_on_raw_data_item_eq truep x;
      prf x;
      holds_on_raw_data_item_implies p (p `andp` truep) (fun x -> holds_on_raw_data_item_eq p x) (f x)
    )
    x;
  holds_on_raw_data_item_implies (p `andp` truep) p (fun x -> holds_on_raw_data_item_eq p x) (raw_data_item_fmap f x)

let holds_on_raw_data_item_fmap
  (f: raw_data_item -> raw_data_item)
  (p: raw_data_item -> bool)
  (prf: (x: raw_data_item) -> Lemma
    (requires (pre_holds_on_raw_data_item p x == true))
    (ensures (holds_on_raw_data_item p (f x) == true))
  )
  (x: raw_data_item)
: Lemma
  (ensures (holds_on_raw_data_item p (raw_data_item_fmap f x) == true))
=
  holds_on_raw_data_item_truep x;
  holds_on_raw_data_item_fmap_gen
    f
    truep
    p
    (fun _ -> ())
    (fun x ->
      prf x;
      holds_on_raw_data_item_implies
        p
        (truep `andp` p)
        (fun _ -> ())
        (f x)
    )
    x;
  holds_on_raw_data_item_implies (truep `andp` p) p (fun _ -> ()) (raw_data_item_fmap f x)

module CBOR.Spec.Raw.Canonical
include CBOR.Spec.Raw.Format
include CBOR.Spec.Raw.Sort
open CBOR.Spec.Util

(* A total order on raw CBOR data items, compatible with the basic
   data model equivalence on valid items: compare the deterministic
   encodings (shortest integers, sorted map keys). Used to check map
   key duplicates by sorting. *)

module U8 = FStar.UInt8
module U64 = FStar.UInt64

let canon_order = deterministically_encoded_cbor_map_key_order

let canon_compare
: (compare: (raw_data_item -> raw_data_item -> int) { compare_prop canon_order compare })
= lemma_compare_prop;
  cbor_compare

let canon (x: raw_data_item) : Tot raw_data_item =
  cbor_raw_sort canon_order canon_compare (raw_data_item_uint64_optimize x)

let cc (x y: raw_data_item) : Tot int =
  cbor_compare (canon x) (canon y)

let cbor_compare_props : squash (
  (forall x y z . (cbor_compare x y < 0 /\ cbor_compare y z < 0) ==> cbor_compare x z < 0) /\
  (forall x y . cbor_compare x y < 0 <==> cbor_compare y x > 0) /\
  (forall x y . cbor_compare x y == 0 <==> x == y)
)
= lemma_compare_prop;
  Classical.forall_intro_2 deterministically_encoded_cbor_map_key_order_spec;
  Classical.forall_intro_2 cbor_compare_correct

let cc_props : squash (
  (forall x y z . (cc x y < 0 /\ cc y z < 0) ==> cc x z < 0) /\
  (forall x y . cc x y < 0 <==> cc y x > 0)
)
= cbor_compare_props

let raw_equiv_props : squash (
  (forall x . raw_equiv x x) /\
  (forall x y . raw_equiv x y == raw_equiv y x) /\
  (forall x y z . (raw_equiv x y /\ raw_equiv y z) ==> raw_equiv x z)
)
= equiv_refl_forall basic_data_model;
  equiv_sym_forall basic_data_model;
  equiv_trans_forall basic_data_model

let canon_correct (x: raw_data_item) : Lemma
  (requires valid_raw_data_item x)
  (ensures (
    let x' = canon x in
    raw_data_item_ints_optimal x' == true /\
    raw_data_item_sorted canon_order x' == true /\
    valid_raw_data_item x' == true /\
    raw_equiv x x'
  ))
= raw_equiv_props;
  raw_data_item_uint64_optimize_correct x;
  raw_data_item_uint64_optimize_valid x ();
  cbor_raw_sort_correct canon_order canon_compare (raw_data_item_uint64_optimize x)

let cc_equiv (x y: raw_data_item) : Lemma
  (requires valid_raw_data_item x /\ valid_raw_data_item y)
  (ensures (cc x y == 0 <==> raw_equiv x y))
= raw_equiv_props;
  canon_correct x;
  canon_correct y;
  cbor_compare_props;
  if raw_equiv x y
  then begin
    lemma_compare_prop;
    raw_equiv_sorted_optimal canon_order (canon x) (canon y)
  end
  else ()

(* Structural unfolding of canon *)

let rec list_map_map (#a #b #c: Type) (f: b -> c) (g: a -> b) (l: list a) : Lemma
  (List.Tot.map f (List.Tot.map g l) == List.Tot.map (fun x -> f (g x)) l)
= match l with
  | [] -> ()
  | _ :: q -> list_map_map f g q

let canon_map_entries (v: list (raw_data_item & raw_data_item)) : Tot (l: list (raw_data_item & raw_data_item) { List.Tot.length l == List.Tot.length v }) =
  cbor_map_sort_failsafe_correct canon_order canon_compare (List.Tot.map (apply_on_pair canon) v);
  cbor_map_sort_failsafe canon_order (List.Tot.map (apply_on_pair canon) v)

let rec list_map_ext' (#a #b: Type) (f g: a -> b) (l: list a) (prf: (x: a) -> Lemma (f x == g x)) : Lemma
  (List.Tot.map f l == List.Tot.map g l)
= match l with
  | [] -> ()
  | x :: q -> prf x; list_map_ext' f g q prf

#push-options "--z3rlimit 32"

let canon_eq (x: raw_data_item) : Lemma
  (canon x == (match x with
    | Int64 ty v -> Int64 ty (raw_uint64_optimize v)
    | String ty len v -> String ty (raw_uint64_optimize len) v
    | Tagged tag v -> Tagged (raw_uint64_optimize tag) (canon v)
    | Array len v -> Array (raw_uint64_optimize len) (List.Tot.map canon v)
    | Map len v -> Map (raw_uint64_optimize len) (canon_map_entries v)
    | Simple _ -> x
  ))
= let o = raw_data_item_uint64_optimize_elem in
  let s = cbor_raw_sort_elem canon_order canon_compare in
  raw_data_item_fmap_eq o x;
  let x1 = raw_data_item_uint64_optimize x in
  raw_data_item_fmap_eq s x1;
  match x with
  | Array len v ->
    list_map_map (raw_data_item_fmap s) (raw_data_item_fmap o) v;
    list_map_ext' (fun x -> raw_data_item_fmap s (raw_data_item_fmap o x)) canon v (fun _ -> ())
  | Map len v ->
    list_map_map (apply_on_pair (raw_data_item_fmap s)) (apply_on_pair (raw_data_item_fmap o)) v;
    list_map_ext' (fun x -> apply_on_pair (raw_data_item_fmap s) (apply_on_pair (raw_data_item_fmap o) x)) (apply_on_pair canon) v (fun _ -> ())
  | _ -> ()

#pop-options

let canon_major_type (x: raw_data_item) : Lemma
  (get_major_type (canon x) == get_major_type x)
= canon_eq x

(* On shortest-size integers, raw_uint64_compare compares values *)

let raw_uint64_compare_optimize (x1 x2: raw_uint64) : Lemma
  (raw_uint64_compare (raw_uint64_optimize x1) (raw_uint64_optimize x2) == int_compare (U64.v x1.value) (U64.v x2.value))
= ()

(* Lexicographic comparisons of lists of items and of map entries *)

let rec cc_list (l1 l2: list raw_data_item) : Pure int
  (requires List.Tot.length l1 == List.Tot.length l2)
  (ensures fun _ -> True)
  (decreases l1)
= match l1, l2 with
  | [], [] -> 0
  | a1 :: q1, a2 :: q2 ->
    let c = cc a1 a2 in
    if c <> 0 then c else cc_list q1 q2

let rec cc_entries (l1 l2: list (raw_data_item & raw_data_item)) : Pure int
  (requires List.Tot.length l1 == List.Tot.length l2)
  (ensures fun _ -> True)
  (decreases l1)
= match l1, l2 with
  | [], [] -> 0
  | a1 :: q1, a2 :: q2 ->
    let c = cc (fst a1) (fst a2) in
    if c <> 0 then c else
    let c = cc (snd a1) (snd a2) in
    if c <> 0 then c else cc_entries q1 q2

let rec cc_list_eq (l1 l2: list raw_data_item) : Lemma
  (requires List.Tot.length l1 == List.Tot.length l2)
  (ensures cbor_compare_array (List.Tot.map canon l1) (List.Tot.map canon l2) == cc_list l1 l2)
  (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | _ :: q1, _ :: q2 -> cc_list_eq q1 q2

let rec cc_entries_eq (l1 l2: list (raw_data_item & raw_data_item)) : Lemma
  (requires List.Tot.length l1 == List.Tot.length l2)
  (ensures cbor_compare_map (List.Tot.map (apply_on_pair canon) l1) (List.Tot.map (apply_on_pair canon) l2) == cc_entries l1 l2)
  (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | _ :: q1, _ :: q2 -> cc_entries_eq q1 q2

let rec cc_list_append (a1 q1 a2 q2: list raw_data_item) : Lemma
  (requires List.Tot.length a1 == List.Tot.length a2 /\ List.Tot.length q1 == List.Tot.length q2)
  (ensures (
    List.Tot.length (List.Tot.append a1 q1) == List.Tot.length (List.Tot.append a2 q2) /\
    cc_list (List.Tot.append a1 q1) (List.Tot.append a2 q2) == (
      let c = cc_list a1 a2 in
      if c <> 0 then c else cc_list q1 q2
  )))
  (decreases a1)
= List.Tot.append_length a1 q1;
  List.Tot.append_length a2 q2;
  match a1, a2 with
  | [], [] -> ()
  | _ :: a1', _ :: a2' -> cc_list_append a1' q1 a2' q2

(* The canonical comparison of two items, one level at a time *)

let cc_map_entries (l1 l2: list (raw_data_item & raw_data_item)) : Pure int
  (requires List.Tot.length l1 == List.Tot.length l2)
  (ensures fun _ -> True)
= cbor_compare_map (canon_map_entries l1) (canon_map_entries l2)

#push-options "--z3rlimit 64"

let cc_eq (x1 x2: raw_data_item) : Lemma
  (cc x1 x2 == (
    let c = int_compare (U8.v (get_major_type x1)) (U8.v (get_major_type x2)) in
    if c <> 0 then c else
    match x1, x2 with
    | Int64 _ v1, Int64 _ v2 -> int_compare (U64.v v1.value) (U64.v v2.value)
    | Simple v1, Simple v2 -> int_compare (U8.v v1) (U8.v v2)
    | String _ len1 v1, String _ len2 v2 ->
      let c = int_compare (U64.v len1.value) (U64.v len2.value) in
      if c <> 0 then c else bytes_lex_compare v1 v2
    | Tagged tag1 v1, Tagged tag2 v2 ->
      let c = int_compare (U64.v tag1.value) (U64.v tag2.value) in
      if c <> 0 then c else cc v1 v2
    | Array len1 v1, Array len2 v2 ->
      let c = int_compare (U64.v len1.value) (U64.v len2.value) in
      if c <> 0 then c else cc_list v1 v2
    | Map len1 v1, Map len2 v2 ->
      let c = int_compare (U64.v len1.value) (U64.v len2.value) in
      if c <> 0 then c else cc_map_entries v1 v2
    | _ -> 0
  ))
= canon_eq x1;
  canon_eq x2;
  match x1, x2 with
  | Array len1 v1, Array len2 v2 ->
    if len1.value = len2.value then cc_list_eq v1 v2
  | _ -> ()

#pop-options

(* Sorting map entries by canonical key order *)

let cc_key_lt (a b: (raw_data_item & raw_data_item)) : Tot bool =
  cc (fst a) (fst b) < 0

let list_memP_map_elim_gen (#a #b: Type) (f: a -> b) (y: b) (l: list a) : Lemma
  (requires List.Tot.memP y (List.Tot.map f l))
  (ensures exists x . List.Tot.memP x l /\ y == f x)
= List.Tot.memP_map_elim f y l

let rec list_existsb_false (#t: Type) (p: t -> bool) (l: list t) : Lemma
  (requires List.Tot.existsb p l == false)
  (ensures forall x . List.Tot.memP x l ==> p x == false)
= match l with
  | [] -> ()
  | _ :: q -> list_existsb_false p q

let list_existsb_intro (#t: Type) (p: t -> bool) (l: list t) (x: t) : Lemma
  (requires List.Tot.memP x l /\ p x)
  (ensures List.Tot.existsb p l)
= Classical.move_requires (list_existsb_false p) l

let rec list_no_setoid_repeats_map' 
  (#t #t': Type)
  (eq: t -> t -> bool)
  (f: t -> t')
  (l: list t)
  (prf: (a: t) -> (b: t) -> Lemma
    (requires List.Tot.memP a l /\ List.Tot.memP b l /\ f a == f b)
    (ensures eq a b)
  )
: Lemma
  (requires list_no_setoid_repeats eq l)
  (ensures List.Tot.no_repeats_p (List.Tot.map f l))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    list_no_setoid_repeats_map' eq f q (fun a b -> prf a b);
    let aux () : Lemma
      (requires List.Tot.memP (f a) (List.Tot.map f q))
      (ensures False)
    = list_memP_map_elim_gen f (f a) q;
      let g (b: t) : Lemma
        (requires List.Tot.memP b q /\ f a == f b)
        (ensures False)
      = prf a b;
        list_existsb_intro (eq a) q b
      in
      Classical.forall_intro (Classical.move_requires g)
    in
    Classical.move_requires aux ()

let rec list_sorted_map
  (#t #t': Type)
  (r1: t -> t -> bool)
  (r2: t' -> t' -> bool)
  (f: t -> t')
  (l: list t)
  (prf: (a: t) -> (b: t) -> Lemma
    (requires r1 a b)
    (ensures r2 (f a) (f b))
  )
: Lemma
  (requires List.Tot.sorted r1 l)
  (ensures List.Tot.sorted r2 (List.Tot.map f l))
= match l with
  | [] -> ()
  | [_] -> ()
  | a :: b :: q -> prf a b; list_sorted_map r1 r2 f (b :: q) prf

let list_memP_map_iff
  (#t #t': Type)
  (f: t -> t')
  (l1 l2: list t)
: Lemma
  (requires forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2)
  (ensures forall y . List.Tot.memP y (List.Tot.map f l1) <==> List.Tot.memP y (List.Tot.map f l2))
= let prf (y: t') (l1 l2: list t) : Lemma
    (requires (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2) /\ List.Tot.memP y (List.Tot.map f l1))
    (ensures List.Tot.memP y (List.Tot.map f l2))
  = list_memP_map_elim_gen f y l1;
    Classical.forall_intro (fun x -> Classical.move_requires (List.Tot.memP_map_intro f x) l2)
  in
  Classical.forall_intro (fun y -> Classical.move_requires (prf y l1) l2);
  Classical.forall_intro (fun y -> Classical.move_requires (prf y l2) l1)

let canon_order_cc (x y: raw_data_item) : Lemma
  (canon_order (canon x) (canon y) == (cc x y < 0))
= lemma_compare_prop

let map_entry_order_canon_props : squash (
  order_irrefl (map_entry_order canon_order raw_data_item) /\
  order_trans (map_entry_order canon_order raw_data_item)
) = lemma_compare_prop

#push-options "--z3rlimit 64"

let canon_map_entries_sorted
  (v l: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    List.Tot.for_all valid_raw_data_item (List.Tot.map fst v) /\
    list_no_setoid_repeats raw_equiv (List.Tot.map fst v) /\
    (forall x . List.Tot.memP x l <==> List.Tot.memP x v) /\
    List.Tot.sorted cc_key_lt l
  )
  (ensures
    canon_map_entries v == List.Tot.map (apply_on_pair canon) l
  )
= let cv = List.Tot.map (apply_on_pair canon) v in
  let cl = List.Tot.map (apply_on_pair canon) l in
  list_map_fst_apply_on_pair canon v;
  list_no_setoid_repeats_map' raw_equiv canon (List.Tot.map fst v) (fun a b ->
    List.Tot.for_all_mem valid_raw_data_item (List.Tot.map fst v);
    cc_equiv a b;
    cbor_compare_props
  );
  cbor_map_sort_failsafe_correct canon_order canon_compare cv;
  list_sorted_map cc_key_lt (map_entry_order canon_order raw_data_item) (apply_on_pair canon) l (fun a b ->
    canon_order_cc (fst a) (fst b)
  );
  list_memP_map_iff (apply_on_pair canon) l v;
  map_entry_order_canon_props;
  list_sorted_ext_eq (map_entry_order canon_order raw_data_item) (canon_map_entries v) cl

#pop-options

let cc_map_entries_sorted
  (v1 l1 v2 l2: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    List.Tot.for_all valid_raw_data_item (List.Tot.map fst v1) /\
    list_no_setoid_repeats raw_equiv (List.Tot.map fst v1) /\
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x v1) /\
    List.Tot.sorted cc_key_lt l1 /\
    List.Tot.for_all valid_raw_data_item (List.Tot.map fst v2) /\
    list_no_setoid_repeats raw_equiv (List.Tot.map fst v2) /\
    (forall x . List.Tot.memP x l2 <==> List.Tot.memP x v2) /\
    List.Tot.sorted cc_key_lt l2 /\
    List.Tot.length v1 == List.Tot.length v2 /\
    List.Tot.length l1 == List.Tot.length l2
  )
  (ensures
    cc_map_entries v1 v2 == cc_entries l1 l2
  )
= canon_map_entries_sorted v1 l1;
  canon_map_entries_sorted v2 l2;
  cc_entries_eq l1 l2

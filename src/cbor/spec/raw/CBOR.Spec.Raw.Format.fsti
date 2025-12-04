(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module CBOR.Spec.Raw.Format
include CBOR.Spec.Raw.Valid

module U8 = FStar.UInt8

(* Data format specification *)

val serialize_cbor
  (c: raw_data_item)
: Tot (Seq.seq U8.t)

val serialize_cbor_inj
  (c1 c2: raw_data_item)
  (s1 s2: Seq.seq U8.t)
: Lemma
  (requires (serialize_cbor c1 `Seq.append` s1 == serialize_cbor c2 `Seq.append` s2))
  (ensures (c1 == c2 /\ s1 == s2))

let serialize_cbor_inj'
  (c1: raw_data_item)
  (s1: Seq.seq U8.t)
: Lemma
  (forall c2 s2 . serialize_cbor c1 `Seq.append` s1 == serialize_cbor c2 `Seq.append` s2 ==> (c1 == c2 /\ s1 == s2))
= Classical.forall_intro_2 (fun c2 s2 ->
    Classical.move_requires (serialize_cbor_inj c1 c2 s1) s2
  )

val parse_cbor (x: Seq.seq U8.t) : Pure (option (raw_data_item & nat))
  (requires True)
  (ensures (fun res -> match res with
  | None -> True
  | Some (y, n) -> 0 < n /\ n <= Seq.length x /\ serialize_cbor y == Seq.slice x 0 n // unique binary representation
  ))

val parse_cbor_prefix
  (x y: Seq.seq U8.t)
: Lemma
  (requires (match parse_cbor x with
  | Some (_, n) -> Seq.length y >= n /\ Seq.slice x 0 n `Seq.equal` Seq.slice y 0 n
  | _ -> False
  ))
  (ensures (
    parse_cbor x == parse_cbor y
  ))

val serialize_parse_cbor (x: raw_data_item) : Lemma
  (let s = serialize_cbor x in
    parse_cbor s == Some (x, Seq.length s)
  )

let serialize_cbor_with_test_correct
  (c: raw_data_item)
  (suff: Seq.seq U8.t)
  (p: (raw_data_item -> Seq.seq U8.t -> prop))
: Lemma
  (requires (
    ~ (p c suff)
  ))
  (ensures (
    forall (c': raw_data_item) (suff': Seq.seq U8.t) .
    serialize_cbor c `Seq.append` suff == serialize_cbor c' `Seq.append` suff' ==> ~ (p c' suff'))
  )
= Classical.forall_intro_2 (fun c' suff' ->
    Classical.move_requires (serialize_cbor_inj c c' suff) suff'
  )

val serialize_cbor_nonempty
  (c: raw_data_item)
: Lemma
  (Seq.length (serialize_cbor c) > 0)

(* 4.2.1 Deterministically encoded CBOR: The keys in every map MUST be sorted in the bytewise lexicographic order of their deterministic encodings. *)

val deterministically_encoded_cbor_map_key_order : (raw_data_item -> raw_data_item -> bool)

val deterministically_encoded_cbor_map_key_order_irrefl
  (x: raw_data_item)
: Lemma
  (Ghost.reveal deterministically_encoded_cbor_map_key_order x x == false)
  [SMTPat (deterministically_encoded_cbor_map_key_order x x)]

val deterministically_encoded_cbor_map_key_order_trans
  (x y z: raw_data_item)
: Lemma
  (requires (deterministically_encoded_cbor_map_key_order x y == true /\ deterministically_encoded_cbor_map_key_order y z == true))
  (ensures (deterministically_encoded_cbor_map_key_order x z == true))
  [SMTPat (deterministically_encoded_cbor_map_key_order x y); SMTPat (deterministically_encoded_cbor_map_key_order y z)]

val deterministically_encoded_cbor_map_key_order_assoc_ext :
  (m1: list (raw_data_item & raw_data_item)) ->
  (m2: list (raw_data_item & raw_data_item)) ->
  (ext: (
    (k: raw_data_item) ->
    Lemma
    (List.Tot.assoc k m1 == List.Tot.assoc k m2)
  )) ->
  Lemma
  (requires (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m1 /\ List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m2))
  (ensures (m1 == m2))

val list_sorted_map_entry_order_deterministically_encoded_cbor_map_key_order_no_repeats
  (#t: Type)
  (l: list (raw_data_item & t))
: Lemma
  (requires (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l)))

(* Comparisons with unserialized values *)

module U64 = FStar.UInt64

noextract [@@noextract_to "krml"]
let int_compare (x1 x2: int) : Tot int =
  if x1 < x2
  then -1
  else if x1 = x2
  then 0
  else 1

let raw_uint64_compare
  (x1 x2: raw_uint64)
: Tot int
=
      let c = int_compare (U8.v x1.size) (U8.v x2.size) in
      if c = 0
      then int_compare (U64.v x1.value) (U64.v x2.value)
      else c

noextract [@@noextract_to "krml"]
let rec bytes_lex_compare
  (s1 s2: Seq.seq U8.t)
: Tot int
  (decreases (Seq.length s1))
= if Seq.length s1 = 0 || Seq.length s2 = 0
  then int_compare (Seq.length s1) (Seq.length s2)
  else
    let c = int_compare (U8.v (Seq.index s1 0)) (U8.v (Seq.index s2 0)) in
    if c = 0
    then bytes_lex_compare (Seq.tail s1) (Seq.tail s2)
    else c

let rec bytes_lex_compare_opp
  (s1 s2: Seq.seq U8.t)
: Lemma
  (ensures (bytes_lex_compare s1 s2 == - bytes_lex_compare s2 s1))
  (decreases (Seq.length s1 + Seq.length s2))
= if Seq.length s1 = 0 || Seq.length s2 = 0
  then ()
  else bytes_lex_compare_opp (Seq.tail s1) (Seq.tail s2)

let rec bytes_lex_compare_values
  (s1 s2: Seq.seq U8.t)
: Lemma
  (ensures (let c = bytes_lex_compare s1 s2 in
    c == -1 \/ c == 0 \/ c == 1))
  (decreases (Seq.length s1))
  [SMTPat (bytes_lex_compare s1 s2)]
= if Seq.length s1 = 0 || Seq.length s2 = 0
  then ()
  else bytes_lex_compare_values (Seq.tail s1) (Seq.tail s2)

val bytes_lex_compare_equal
  (s1 s2: Seq.seq U8.t)
: Lemma
  (bytes_lex_compare s1 s2 == 0 <==> s1 == s2)

val deterministically_encoded_cbor_map_key_order_spec
  (x1 x2: raw_data_item)
: Lemma
  (deterministically_encoded_cbor_map_key_order x1 x2 == (bytes_lex_compare (serialize_cbor x1) (serialize_cbor x2) < 0))

noextract [@@noextract_to "krml"]
let rec cbor_compare
  (x1 x2: raw_data_item)
: Tot int
  (decreases x1)
= let ty1 = get_major_type x1 in
  let ty2 = get_major_type x2 in
  let c = int_compare (U8.v ty1) (U8.v ty2) in
  if c <> 0
  then c
  else if ty1 = cbor_major_type_uint64 || ty1 = cbor_major_type_neg_int64
  then raw_uint64_compare (Int64?.v x1) (Int64?.v x2)
  else if ty1 = cbor_major_type_simple_value
  then int_compare (U8.v (Simple?.v x1)) (U8.v (Simple?.v x2))
  else if ty1 = cbor_major_type_byte_string || ty1 = cbor_major_type_text_string
  then
    let c = raw_uint64_compare (String?.len x1) (String?.len x2) in
    if c <> 0
    then c
    else bytes_lex_compare (String?.v x1) (String?.v x2)
  else if ty1 = cbor_major_type_tagged
  then
    let c = raw_uint64_compare (Tagged?.tag x1) (Tagged?.tag x2) in
    if c <> 0
    then c
    else cbor_compare (Tagged?.v x1) (Tagged?.v x2)
  else if ty1 = cbor_major_type_array
  then
    let c = raw_uint64_compare (Array?.len x1) (Array?.len x2) in
    if c <> 0
    then c
    else cbor_compare_array (Array?.v x1) (Array?.v x2)
  else if ty1 = cbor_major_type_map
  then
    let c = raw_uint64_compare (Map?.len x1) (Map?.len x2) in
    if c <> 0
    then c
    else cbor_compare_map (Map?.v x1) (Map?.v x2)
  else false_elim ()

and cbor_compare_array
  (x1 x2: list raw_data_item)
: Pure int
    (requires (List.Tot.length x1 == List.Tot.length x2))
    (ensures (fun _ -> True))
    (decreases x1)
= match x1, x2 with
  | [], [] -> 0
  | a1 :: q1, a2 :: q2 ->
    let c = cbor_compare a1 a2 in
    if c <> 0
    then c
    else cbor_compare_array q1 q2

and cbor_compare_map
  (x1 x2: list (raw_data_item & raw_data_item))
: Pure int
    (requires (List.Tot.length x1 == List.Tot.length x2))
    (ensures (fun _ -> True))
    (decreases x1)
= match x1, x2 with
  | [], [] -> 0
  | a1 :: q1, a2 :: q2 ->
    let c = cbor_compare (fst a1) (fst a2) in
    if c <> 0
    then c
    else
      let c = cbor_compare (snd a1) (snd a2) in
      if c <> 0
      then c
      else cbor_compare_map q1 q2

val cbor_compare_correct
  (x1 x2: raw_data_item)
: Lemma
  (ensures (cbor_compare x1 x2 == bytes_lex_compare (serialize_cbor x1) (serialize_cbor x2)))

let cbor_map_entry_raw_compare = CBOR.Spec.Raw.Map.map_entry_compare cbor_compare

let cbor_map_entry_raw_compare_correct : squash (
  let order = (map_entry_order deterministically_encoded_cbor_map_key_order _) in
  let compare = cbor_map_entry_raw_compare in
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0))
  )
= Classical.forall_intro_2 deterministically_encoded_cbor_map_key_order_spec;
  Classical.forall_intro_2 cbor_compare_correct;
  Classical.forall_intro_2 bytes_lex_compare_opp

let cbor_compare_equal
  (x1 x2: raw_data_item)
: Lemma
  (cbor_compare x1 x2 == 0 <==> x1 == x2)
= cbor_compare_correct x1 x2;
  bytes_lex_compare_equal (serialize_cbor x1) (serialize_cbor x2);
  Seq.append_empty_r (serialize_cbor x1);
  Seq.append_empty_r (serialize_cbor x2);
  Classical.move_requires (serialize_cbor_inj x1 x2 Seq.empty) Seq.empty

let lemma_compare_prop : squash (CBOR.Spec.Raw.Sort.compare_prop deterministically_encoded_cbor_map_key_order cbor_compare) =
  Classical.forall_intro_2 deterministically_encoded_cbor_map_key_order_spec;
  Classical.forall_intro_2 cbor_compare_correct;
  Classical.forall_intro_2 cbor_compare_equal;
  Classical.forall_intro_2 bytes_lex_compare_opp

let cbor_map_entry_raw_compare_succeeds
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (~ (
    exists l1 l2 x1 x2 . l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ cbor_map_entry_raw_compare x1 x2 == 0
  )))
= let prf1
      (l1 l2: list (raw_data_item & raw_data_item))
      (x1 x2: (raw_data_item & raw_data_item))
  : Lemma
    (requires 
      l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ cbor_map_entry_raw_compare x1 x2 == 0
    )
    (ensures False)
  = List.Tot.map_append fst l1 l2;
    List.Tot.memP_map_intro fst x1 l1;
    List.Tot.memP_map_intro fst x2 l2;
    cbor_compare_equal (fst x1) (fst x2);
    List.Tot.no_repeats_p_append_elim (List.Tot.map fst l1) (List.Tot.map fst l2)
  in
  let prf2
    (l1 l2: list (raw_data_item & raw_data_item))
    (x1 x2: (raw_data_item & raw_data_item))
  : Lemma
    (ensures ~ (
      l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ cbor_map_entry_raw_compare x1 x2 == 0
    ))
  = Classical.move_requires (prf1 l1 l2 x1) x2
  in
  Classical.forall_intro_4 prf2

let deterministically_encoded_cbor_map_key_order_major_type_intro
  (v1 v2: raw_data_item)
: Lemma
  (requires (
    U8.v (get_major_type v1) < U8.v (get_major_type v2)
  ))
  (ensures (
    deterministically_encoded_cbor_map_key_order v1 v2 == true
  ))
= deterministically_encoded_cbor_map_key_order_spec v1 v2;
  cbor_compare_correct v1 v2

let raw_uint64_lt
  (x1 x2: raw_uint64)
: Tot bool
= x1.size `U8.lt` x2.size || (x1.size = x2.size && x1.value `U64.lt` x2.value)

let deterministically_encoded_cbor_map_key_order_int64
  (ty: major_type_uint64_or_neg_int64)
  (v1 v2: raw_uint64)
: Lemma
  (Ghost.reveal deterministically_encoded_cbor_map_key_order (Int64 ty v1) (Int64 ty v2) == raw_uint64_lt v1 v2)
  [SMTPat (Ghost.reveal deterministically_encoded_cbor_map_key_order (Int64 ty v1) (Int64 ty v2))]
= deterministically_encoded_cbor_map_key_order_spec (Int64 ty v1) (Int64 ty v2);
  cbor_compare_correct (Int64 ty v1) (Int64 ty v2)

val serialize_cbor_tag
  (tag: raw_uint64)
: Tot (Seq.seq U8.t)

val serialize_cbor_tag_length
  (tag: raw_uint64)
: Lemma
  (Seq.length (serialize_cbor_tag tag) > 0)

val serialize_cbor_tag_correct
  (tag: raw_uint64)
  (payload: raw_data_item)
: Lemma
  (serialize_cbor (Tagged tag payload) == serialize_cbor_tag tag `Seq.append` serialize_cbor payload)

val serialize_cbor_list : list raw_data_item -> Seq.seq U8.t

val serialize_cbor_list_nil (_: unit) : Lemma
  (serialize_cbor_list [] == Seq.empty)

val serialize_cbor_list_cons (a: raw_data_item) (q: list raw_data_item) : Lemma
  (serialize_cbor_list (a :: q) == serialize_cbor a `Seq.append` serialize_cbor_list q)

val serialize_cbor_array_length_gt_list
  (len: raw_uint64)
  (l: list raw_data_item)
: Lemma
  (requires (List.Tot.length l == U64.v len.value))
  (ensures (
    List.Tot.length l == U64.v len.value /\
    Seq.length (serialize_cbor (Array len l)) > Seq.length (serialize_cbor_list l)
  ))

val serialize_cbor_string_length_gt
  (ty: major_type_byte_string_or_text_string)
  (len: raw_uint64)
  (l: Seq.seq U8.t)
: Lemma
  (requires (Seq.length l == U64.v len.value /\
    (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct l)
  ))
  (ensures (
    Seq.length l == U64.v len.value /\
    (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct l) /\
    Seq.length (serialize_cbor (String ty len l)) > Seq.length l
  ))

val serialize_cbor_map : list (raw_data_item & raw_data_item) -> Seq.seq U8.t

val serialize_cbor_map_nil (_: unit) : Lemma
  (serialize_cbor_map [] == Seq.empty)

val serialize_cbor_map_cons (key: raw_data_item) (value: raw_data_item) (q: list (raw_data_item & raw_data_item)) : Lemma
  (serialize_cbor_map ((key, value) :: q) == (serialize_cbor key `Seq.append` serialize_cbor value) `Seq.append` serialize_cbor_map q)

let serialize_cbor_map_singleton (key: raw_data_item) (value: raw_data_item) : Lemma
  (serialize_cbor_map [key, value] == serialize_cbor key `Seq.append` serialize_cbor value)
= serialize_cbor_map_nil ();
  serialize_cbor_map_cons key value [];
  Seq.append_empty_r (serialize_cbor key `Seq.append` serialize_cbor value)

let rec serialize_cbor_map_append (l1 l2: list (raw_data_item & raw_data_item)) : Lemma
  (ensures (serialize_cbor_map (l1 `List.Tot.append` l2) == serialize_cbor_map l1 `Seq.append` serialize_cbor_map l2))
  (decreases l1)
= match l1 with
  | [] ->
    serialize_cbor_map_nil ();
    Seq.append_empty_l (serialize_cbor_map l2)
  | (k, v) :: l1' ->
    serialize_cbor_map_append l1' l2;
    serialize_cbor_map_cons k v l1';
    serialize_cbor_map_cons k v (l1' `List.Tot.append` l2);
    Seq.append_assoc (serialize_cbor k `Seq.append` serialize_cbor v) (serialize_cbor_map l1') (serialize_cbor_map l2)

let cbor_map_insert = CBOR.Spec.Raw.Map.map_insert cbor_compare

let cbor_map_insert_mem = CBOR.Spec.Raw.Map.map_insert_mem cbor_compare

let cbor_map_insert_sorted m kv
: Lemma
  (requires (
    List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m
  ))
  (ensures (
    let ol' = cbor_map_insert m kv in
    (None? ol' <==> List.Tot.memP (fst kv) (List.Tot.map fst m)) /\
    begin match ol' with
    | None -> True
    | Some l' -> List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l'
    end
  ))
=
  Classical.forall_intro_2 deterministically_encoded_cbor_map_key_order_spec;
  Classical.forall_intro_2 cbor_compare_correct;
  Classical.forall_intro_2 cbor_compare_equal;
  Classical.forall_intro_2 bytes_lex_compare_opp;
  CBOR.Spec.Raw.Map.map_insert_sorted deterministically_encoded_cbor_map_key_order cbor_compare m kv;
  ()

val serialize_cbor_map_insert_length
  (m: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
: Lemma
  (ensures (match cbor_map_insert m kv with
  | None -> True
  | Some m' ->
    Seq.length (serialize_cbor_map m') == Seq.length (serialize_cbor_map m) + Seq.length (serialize_cbor (fst kv)) + Seq.length (serialize_cbor (snd kv))
  ))

val cbor_serialize_map_length_gt_list
  (len: raw_uint64)
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (U64.v len.value == List.Tot.length l))
  (ensures (
    U64.v len.value == List.Tot.length l /\
    Seq.length (serialize_cbor (Map len l)) > Seq.length (serialize_cbor_map l)
  ))

val parse_cbor_map
  (n: nat)
  (s: Seq.seq U8.t)
: Pure (option (list (raw_data_item & raw_data_item) & nat))
    (requires True)
    (ensures fun res -> match res with
    | None -> True
    | Some (_, len) -> len <= Seq.length s
    )

val parse_cbor_map_prefix
  (n: nat)
  (s1 s2: Seq.seq U8.t)
: Lemma
  (match parse_cbor_map n s1 with
  | None -> True
  | Some (l, len1) ->
    (len1 <= Seq.length s2 /\ Seq.slice s1 0 len1 == Seq.slice s2 0 len1) ==>
    parse_cbor_map n s2 == Some (l, len1)
  )

val parse_cbor_map_equiv
  (n: nat)
  (s: Seq.seq U8.t)
  (l: list (raw_data_item & raw_data_item))
  (len: nat)
: Lemma
  (parse_cbor_map n s == Some (l, len) <==> (
    n == List.Tot.length l /\
    len <= Seq.length s /\
    Seq.slice s 0 len == serialize_cbor_map l
  ))

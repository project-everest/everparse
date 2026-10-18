module LowParse.Spec.Sorted

(* Lexicographic order *)

let rec lex_compare
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
: Tot int
  (decreases l1)
= match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | a1 :: q1, [] -> 1
  | a1 :: q1, a2 :: q2 ->
    let c = compare a1 a2 in
    if c = 0
    then lex_compare compare q1 q2
    else c

let rec lex_compare_equal
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (l1: list t)
  (l2: list t)
: Lemma
  (ensures (lex_compare compare l1 l2 == 0 <==> l1 == l2))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a1 :: q1 ->
    match l2 with
    | [] -> ()
    | a2 :: q2 ->
      compare_equal a1 a2;
      lex_compare_equal compare compare_equal q1 q2

let rec lex_compare_trans
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (compare_trans: (
    (x: t) ->
    (y: t) ->
    (z: t) ->
    Lemma
    (requires (compare x y < 0 /\ compare y z < 0))
    (ensures (compare x z < 0))
  ))
  (l1: list t)
  (l2: list t)
  (l3: list t)
: Lemma
  (requires (lex_compare compare l1 l2 < 0 /\ lex_compare compare l2 l3 < 0))
  (ensures (lex_compare compare l1 l3 < 0))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a1 :: q1 ->
    let a2 :: q2 = l2 in
    let a3 :: q3 = l3 in
    compare_equal a1 a2;
    compare_equal a2 a3;
    compare_equal a1 a3;
    if compare a1 a2 = 0 && compare a2 a3 = 0
    then lex_compare_trans compare compare_equal compare_trans q1 q2 q3
    else if compare a1 a2 < 0 && compare a2 a3 < 0
    then compare_trans a1 a2 a3
    else ()

let lex_order
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
: Tot bool
= lex_compare compare l1 l2 < 0

let lex_order_irrefl
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (x y: list t)
: Lemma
  (requires (lex_order compare x y))
  (ensures (~ (x == y)))
= lex_compare_equal compare compare_equal x y

let lex_order_trans
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (compare_trans: (
    (x: t) ->
    (y: t) ->
    (z: t) ->
    Lemma
    (requires (compare x y < 0 /\ compare y z < 0))
    (ensures (compare x z < 0))
  ))
  (x y z: list t)
: Lemma
  (requires (lex_order compare x y /\ lex_order compare y z))
  (ensures (lex_order compare x z))
= lex_compare_trans compare compare_equal compare_trans x y z

let rec lex_compare_antisym
  (#t: Type)
  (compare: t -> t -> int)
  (compare_antisym: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y < 0 <==> compare y x > 0)
  ))
  (x y: list t)
: Lemma
  (ensures (lex_compare compare x y < 0 <==> lex_compare compare y x > 0))
  (decreases x)
= match x with
    | [] -> ()
    | a :: x' ->
      begin match y with
      | [] -> ()
      | b :: y' ->
        compare_antisym a b;
        compare_antisym b a;
        if compare a b = 0
        then lex_compare_antisym compare compare_antisym x' y'
        else ()
      end

let rec lex_order_total
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (compare_antisym: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y < 0 <==> compare y x > 0)
  ))
  (x y: list t)
: Lemma
  (ensures (x == y \/ lex_order compare x y \/ lex_order compare y x))
=   match x with
    | [] -> ()
    | a :: x' ->
      begin match y with
      | [] -> ()
      | b :: y' ->
        compare_equal a b;
        compare_equal b a;
        compare_antisym a b;
        compare_antisym b a;
        if compare a b = 0
        then lex_order_total compare compare_equal compare_antisym x' y'
        else ()
      end

let rec lex_compare_append
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
  (l1' l2': list t)
: Lemma
  (requires (lex_compare compare l1 l2 < 0 /\ List.Tot.length l1 == List.Tot.length l2))
  (ensures (lex_compare compare (List.Tot.append l1 l1') (List.Tot.append l2 l2') < 0))
  (decreases l1)
= match l1, l2 with
  | a1 :: q1, a2 :: q2 ->
    let c = compare a1 a2 in
    if c = 0
    then lex_compare_append compare q1 q2 l1' l2'
    else ()

let rec lex_compare_append_recip
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
  (l1' l2': list t)
: Lemma
  (requires (
    lex_compare compare (List.Tot.append l1 l1') (List.Tot.append l2 l2') < 0 /\
    List.Tot.length l1 == List.Tot.length l2
  ))
  (ensures (
    lex_compare compare l1 l2 <= 0
  ))
  (decreases l1)
= match l1, l2 with
  | [], _ -> ()
  | a1 :: q1, a2 :: q2 ->
    if compare a1 a2 = 0
    then lex_compare_append_recip compare q1 q2 l1' l2'
    else ()

let rec lex_compare_prefix
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (l: list t)
  (l1 l2: list t)
: Lemma
  (ensures (lex_compare compare (List.Tot.append l l1) (List.Tot.append l l2) == lex_compare compare l1 l2))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    compare_equal a a;
    lex_compare_prefix compare compare_equal q l1 l2

let length_first_lex_order
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
: Tot bool
= if List.Tot.length l1 = List.Tot.length l2
  then lex_order compare l1 l2
  else List.Tot.length l1 < List.Tot.length l2

let length_first_lex_order_irrefl
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (x y: list t)
: Lemma
  (requires (length_first_lex_order compare x y))
  (ensures (~ (x == y)))
= if List.Tot.length x = List.Tot.length y
  then lex_order_irrefl compare compare_equal x y
  else ()

let length_first_lex_order_trans
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (compare_trans: (
    (x: t) ->
    (y: t) ->
    (z: t) ->
    Lemma
    (requires (compare x y < 0 /\ compare y z < 0))
    (ensures (compare x z < 0))
  ))
  (x y z: list t)
: Lemma
  (requires (length_first_lex_order compare x y /\ length_first_lex_order compare y z))
  (ensures (length_first_lex_order compare x z))
= if List.Tot.length x = List.Tot.length y && List.Tot.length y = List.Tot.length z
  then lex_order_trans compare compare_equal compare_trans x y z
  else ()

let length_first_lex_order_total
  (#t: Type)
  (compare: t -> t -> int)
  (compare_equal: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (compare_antisym: (
    (x: t) ->
    (y: t) ->
    Lemma
    (compare x y < 0 <==> compare y x > 0)
  ))
  (x y: list t)
: Lemma
  (ensures (x == y \/ length_first_lex_order compare x y \/ length_first_lex_order compare y x))
= if List.Tot.length x = List.Tot.length y
  then lex_order_total compare compare_equal compare_antisym x y
  else ()

let same_sign
  (x1 x2: int)
: GTot prop
= (x1 == 0 <==> x2 == 0) /\
  (x1 < 0 <==> x2 < 0)

let weak_compare_for
  (#t: Type)
  (order: t -> t -> bool)
: Tot Type
= (x: t) ->
  (y: t) ->
  Pure int
    (requires True)
    (ensures (fun z ->
      (z < 0 <==> order x y) /\
      (z > 0 <==> order y x)
    ))

let weak_compare_for_antisym
  (#t: Type)
  (#order: t -> t -> bool)
  (w: weak_compare_for order)
  (x: t)
  (y: t)
: Lemma
  (~ (order x y /\ order y x))
= let z = w x y in
  ()

let weak_compare_for_irrefl
  (#t: Type)
  (#order: t -> t -> bool)
  (w: weak_compare_for order)
  (x: t)
: Lemma
  (~ (order x x))
= let z = w x x in
  ()

let weak_compare_for_sign
  (#t: Type)
  (#order: t -> t -> bool)
  (w: weak_compare_for order)
  (x: t)
  (y: t)
: Lemma
  (same_sign (w x y) (- w y x))
= ()

let rec insert
  (#t: Type)
  (#order: t -> t -> bool)
  (w: weak_compare_for order)
  (x: t)
  (l: list t)
: Tot (option (list t))
  (decreases l)
= match l with
  | [] -> Some [x]
  | a :: q ->
    let c = w x a in
    if c = 0
    then None
    else if c < 0
    then Some (x :: a :: q)
    else match insert w x q with
    | None -> None
    | Some l' -> Some (a :: l')

let rec insert_sorted
  (#t: Type)
  (#order: t -> t -> bool)
  (w: weak_compare_for order)
  (x: t)
  (l: list t)
: Lemma
  (requires (List.Tot.sorted order l))
  (ensures (match insert w x l with
  | None -> True
  | Some l' -> List.Tot.sorted order l'
  ))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    if w x a > 0
    then insert_sorted w x q
    else ()

let compare_for
  (#t: Type)
  (order: t -> t -> bool)
: Tot Type
= (x: t) ->
  (y: t) ->
  Pure int
    (requires True)
    (ensures (fun z ->
      (z < 0 <==> order x y) /\
      (z > 0 <==> order x y) /\
      (z == 0 <==> x == y)
    ))

let compare_for_is_subtype_of_weak_compare_for
  (#t: Type)
  (#order: t -> t -> bool)
  (c: compare_for order)
: Tot unit
= let wc : weak_compare_for order = c in
  ()

module Seq = FStar.Seq

let rec seq_to_list_append
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures (Seq.seq_to_list (s1 `Seq.append` s2) == Seq.seq_to_list s1 `List.Tot.append` Seq.seq_to_list s2))
  (decreases (Seq.length s1))
= if Seq.length s1 = 0
  then begin
    assert ((s1 `Seq.append` s2) `Seq.equal` s2)
  end else begin
    let h = Seq.head s1 in
    let t = Seq.tail s1 in
    assert (s1 == Seq.cons h t);
    assert (s1 `Seq.append` s2 `Seq.equal` Seq.cons h (t `Seq.append` s2));
    Seq.lemma_seq_to_list_cons h t;
    Seq.lemma_seq_to_list_cons h (t `Seq.append` s2);
    seq_to_list_append t s2
  end

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

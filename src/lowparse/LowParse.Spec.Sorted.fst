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

let length_first_lex_order
  (#t: Type)
  (compare: t -> t -> int)
  (l1 l2: list t)
: Tot bool
= if List.Tot.length l1 = List.Tot.length l2
  then lex_order compare l1 l2
  else List.Tot.length l1 < List.Tot.length l2

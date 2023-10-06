module LowParse.SteelST.SeqMatch
include LowParse.SteelST.VCList
open Steel.ST.OnRange
open Steel.ST.GenElim

module Seq = FStar.Seq
module R = Steel.ST.Reference
module A = Steel.ST.Array
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

(* `seq_list_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a list of high-level
values. `seq_list_match` is carefully designed to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values.  *)

[@@__reduce__]
let seq_list_match_nil0
  (#t: Type0) // FIXME: universe polymorphism may be a problem with Steel
  (c: Seq.seq t)
: Tot vprop
= pure (c `Seq.equal` Seq.empty)

[@@__reduce__]
let seq_list_match_cons0
  (#t #t': Type0) // FIXME: universe polymorphism may be a problem with Steel
  (c: Seq.seq t)
  (l: list t' { Cons? l })
  (item_match: (t -> (v': t' { v' << l }) -> vprop))
  (seq_list_match: (Seq.seq t -> (v': list t') -> (raw_data_item_match: (t -> (v'': t' { v'' << v' }) -> vprop) { v' << l }) ->
vprop))
: Tot vprop
= exists_ (fun (c1: t) -> exists_ (fun (c2: Seq.seq t) ->
    item_match c1 (List.Tot.hd l) `star`
    seq_list_match c2 (List.Tot.tl l) item_match `star`
    pure (c `Seq.equal` Seq.cons c1 c2)
  ))

let rec seq_list_match
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> vprop))
: Tot vprop
  (decreases v)
= if Nil? v
  then seq_list_match_nil0 c
  else seq_list_match_cons0 c v item_match seq_list_match

let seq_list_match_cons_eq
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> vprop))
: Lemma
  (requires (Cons? v))
  (ensures (
    seq_list_match c v item_match ==
    seq_list_match_cons0 c v item_match seq_list_match
  ))
= let a :: q = v in
  assert_norm (seq_list_match c (a :: q) item_match ==
    seq_list_match_cons0 c (a :: q) item_match seq_list_match
  )

(* `seq_seq_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a sequence of high-level
values. Contrary to `seq_list_match`, `seq_seq_match` is not meant to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values, because no lemma ensures that `Seq.index s i << s`  *)

let seq_seq_match_item
  (#t1 #t2: Type0) // FIXME: universe polymorphism may be a problem with Steel
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (i: nat)
: Tot vprop
= if i < Seq.length c && i < Seq.length l
  then
    p (Seq.index c i) (Seq.index l i)
  else
    pure (squash False)

let seq_seq_match_item_tail
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (delta: nat)
  (i: nat)
: Lemma
  (requires (
    i + delta <= Seq.length c /\
    i + delta <= Seq.length l
  ))
  (ensures (
    seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) i ==
      seq_seq_match_item p c l (i + delta)
  ))
= ()

[@@__reduce__]
let seq_seq_match
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (i j: nat)
: Tot vprop
= on_range (seq_seq_match_item p c l) i j

let seq_seq_match_length
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: STGhost unit opened
    (seq_seq_match p s1 s2 i j)
    (fun _ -> seq_seq_match p s1 s2 i j)
    True
    (fun _ -> i <= j /\ (i == j \/ (j <= Seq.length s1 /\ j <= Seq.length s2)))
= on_range_le (seq_seq_match_item p s1 s2) i j;
  if i = j
  then noop ()
  else begin
    let j' = j - 1 in
    if j' < Seq.length s1 && j' < Seq.length s2
    then noop ()
    else begin
      on_range_unsnoc
        (seq_seq_match_item p s1 s2)
        i j' j;
      rewrite
        (seq_seq_match_item p _ _ _)
        (pure (squash False));
      let _ = gen_elim () in
      rewrite
        (seq_seq_match p s1 s2 i j')
        (seq_seq_match p s1 s2 i j) // by contradiction
    end
  end

let seq_seq_match_weaken
  (#opened: _)
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> vprop)
  (w: ((x1: t1) -> (x2: t2) -> STGhostT unit opened
    (p x1 x2) (fun _ -> p' x1 x2)
  ))
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: STGhost unit opened
    (seq_seq_match p c1 c2 i j)
    (fun _ -> seq_seq_match p' c1' c2' i j)
    (i <= j /\ (i == j \/ (
      j <= Seq.length c1 /\ j <= Seq.length c2 /\
      j <= Seq.length c1' /\ j <= Seq.length c2' /\
      Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
      Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
    )))
    (fun _ -> True)
=
  on_range_weaken
    (seq_seq_match_item p c1 c2)
    (seq_seq_match_item p' c1' c2')
    i j
    (fun k ->
       rewrite (seq_seq_match_item p c1 c2 k) (p (Seq.index (Seq.slice c1 i j) (k - i)) (Seq.index (Seq.slice c2 i j) (k - i)));
       w _ _;
       rewrite (p' _ _) (seq_seq_match_item p' c1' c2' k)
    )

let seq_seq_match_weaken_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: STGhost unit opened
    (seq_seq_match p c1 c2 i j)
    (fun _ -> seq_seq_match p c1' c2' i j `star`
      (seq_seq_match p c1' c2' i j `implies_` seq_seq_match p c1 c2 i j)
    )
    (i <= j /\ (i == j \/ (
      j <= Seq.length c1 /\ j <= Seq.length c2 /\
      j <= Seq.length c1' /\ j <= Seq.length c2' /\
      Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
      Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
    )))
    (fun _ -> True)
= seq_seq_match_weaken
    p p (fun _ _ -> noop ())
    c1 c1'
    c2 c2'
    i j;
  intro_implies
    (seq_seq_match p c1' c2' i j)
    (seq_seq_match p c1 c2 i j)
    emp
    (fun _ ->
      seq_seq_match_weaken
        p p (fun _ _ -> noop ())
        c1' c1
        c2' c2
        i j
    )

(* Going between `seq_list_match` and `seq_seq_match` *)

let rec list_index_append_cons
  (#t: Type)
  (l1: list t)
  (a: t)
  (l2: list t)
: Lemma
  (ensures (let l = l1 `List.Tot.append` (a :: l2) in
    let n1 = List.Tot.length l1 in
    n1 < List.Tot.length l /\
    List.Tot.index l n1 == a
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a1 :: l1' -> list_index_append_cons l1' a l2

let rec list_index_map
  (#t1 #t2: Type)
  (f: (t1 -> t2))
  (l1: list t1)
  (i: nat {i < List.Tot.length l1})
: Lemma
  (ensures (let l2 = List.Tot.map f l1 in
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.index l2 i == f (List.Tot.index l1 i)
  ))
  [SMTPat (List.Tot.index (List.Tot.map f l1) i)]
= let a :: l1' = l1 in
  if i = 0
  then ()
  else list_index_map f l1' (i - 1)

let seq_of_list_eq_init_index
  (#t: Type)
  (l: list t)
: Lemma
  (Seq.seq_of_list l `Seq.equal` Seq.init (List.Tot.length l) (List.Tot.index l))
= () // thanks to Seq.lemma_seq_of_list_index

let seq_of_list_tail
  (#t: Type)
  (a: t)
  (q: list t)
: Lemma
  (Seq.tail (Seq.seq_of_list (a :: q)) == Seq.seq_of_list q)
= Seq.lemma_seq_of_list_induction (a :: q)


let seq_seq_match_tail_elim
  (#t1 #t2: Type)
  (#opened: _)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq (t2))
  (delta: nat {
    delta <= Seq.length c /\
    delta <= Seq.length l
  })
  (i j: nat)
: STGhostT unit opened
    (seq_seq_match p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) i j)
    (fun _ -> seq_seq_match p c l (i + delta) (j + delta))
= on_range_le (seq_seq_match_item p _ _) _ _;
  on_range_weaken_and_shift
    (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)))
    (seq_seq_match_item p c l)
    delta
    i j
    (fun k ->
       if k < Seq.length c - delta && k < Seq.length l - delta
       then begin
         seq_seq_match_item_tail p c l delta k;
         rewrite
           (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) k)
           (seq_seq_match_item p c l (k + delta))
       end else begin
         rewrite
           (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) k)
           (pure (squash False));
         let _ = gen_elim () in
         rewrite
           emp
           (seq_seq_match_item p c l (k + delta)) // by contradiction
       end
    )
    (i + delta) (j + delta)

let seq_seq_match_tail_intro
  (#t1 #t2: Type)
  (#opened: _)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (delta: nat {
    delta <= Seq.length c /\
    delta <= Seq.length l
  })
  (i: nat {
    delta <= i
  })
  (j: nat)
: STGhostT (squash (i <= j)) opened
    (seq_seq_match p c l i j)
    (fun _ -> seq_seq_match p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (i - delta) (j - delta))
= on_range_le (seq_seq_match_item p _ _) _ _;
  on_range_weaken_and_shift
    (seq_seq_match_item p c l)
    (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)))
    (0 - delta)
    i j
    (fun k ->
      if k < Seq.length c && k < Seq.length l
      then begin
        seq_seq_match_item_tail p c l delta (k - delta);
        rewrite
          (seq_seq_match_item p c l k)
          (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (k + (0 - delta)))
      end else begin
        rewrite
          (seq_seq_match_item p c l k)
          (pure (squash False));
        let _ = gen_elim () in
        rewrite
          emp
          (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (k + (0 - delta))) // by contradiction
      end
    )
    (i - delta) (j - delta)

let rec seq_seq_match_seq_list_match
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    (fun _ -> seq_list_match c l p)
    (Seq.length c == List.Tot.length l)
    (fun _ -> True)
    (decreases l)
= match l with
  | [] ->
    drop (seq_seq_match p _ _ _ _);
    rewrite
      (seq_list_match_nil0 c)
      (seq_list_match c l p)
  | a :: q ->
    Seq.lemma_seq_of_list_induction (a :: q);
    seq_list_match_cons_eq c l p;
    on_range_uncons
      (seq_seq_match_item p _ _)
      _ 1 _;
    rewrite
      (seq_seq_match_item p _ _ _)
      (p (Seq.head c) (List.Tot.hd l));
    let _ = seq_seq_match_tail_intro
      p _ _ 1 _ _
    in
    rewrite
      (seq_seq_match p _ _ _ _)
      (seq_seq_match p (Seq.tail c) (Seq.seq_of_list (List.Tot.tl l)) 0 (List.Tot.length (List.Tot.tl l)));
    seq_seq_match_seq_list_match p _ (List.Tot.tl l);
    rewrite
      (seq_list_match_cons0 c l p seq_list_match)
      (seq_list_match c l p)

let rec seq_list_match_seq_seq_match
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_list_match c l p)
    (fun _ -> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    True
    (fun _ -> Seq.length c == List.Tot.length l)
    (decreases l)
= match l with
  | [] ->
    rewrite
      (seq_list_match c l p)
      (seq_list_match_nil0 c);
    let _ = gen_elim () in
    on_range_empty
      (seq_seq_match_item p c (Seq.seq_of_list l))
      0
      (List.Tot.length l)
  | a :: q ->
    let _l_nonempty : squash (Cons? l) = () in
    Seq.lemma_seq_of_list_induction (a :: q);
    seq_list_match_cons_eq c l p;
    noop ();
    rewrite
      (seq_list_match c l p)
      (seq_list_match_cons0 c l p seq_list_match);
    let _ = gen_elim () in
    let a' = vpattern (fun a' -> p a' _) in
    let c' = vpattern (fun c' -> seq_list_match c' _ _) in
    Seq.lemma_cons_inj (Seq.head c) a' (Seq.tail c) c';
    assert (a' == Seq.head c);
    assert (c' == Seq.tail c);
    noop ();
    seq_list_match_seq_seq_match p _ _;
    rewrite
      (seq_seq_match p _ _ _ _)
      (seq_seq_match p (Seq.slice c 1 (Seq.length c)) (Seq.slice (Seq.seq_of_list l) 1 (Seq.length (Seq.seq_of_list l))) 0 (List.Tot.length (List.Tot.tl l)));
    let _ = seq_seq_match_tail_elim
      p c (Seq.seq_of_list l) 1 0 (List.Tot.length (List.Tot.tl l))
    in
    rewrite
      (seq_seq_match p _ _ _ _)
      (seq_seq_match p c (Seq.seq_of_list l) 1 (List.Tot.length l));
    rewrite
      (p _ _)
      (seq_seq_match_item p c (Seq.seq_of_list l) 0);
    on_range_cons
      (seq_seq_match_item p _ _)
      0 1 (List.Tot.length l)

let seq_seq_match_seq_list_match_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    (fun _ -> seq_list_match c l p `star` (seq_list_match c l p `implies_` seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l)))
    (Seq.length c == List.Tot.length l)
    (fun _ -> True)
= seq_seq_match_seq_list_match p c l;
  intro_implies
    (seq_list_match c l p)
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    emp
    (fun _ -> seq_list_match_seq_seq_match p c l)

let seq_list_match_seq_seq_match_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_list_match c l p)
    (fun _ -> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) `star` (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) `implies_` seq_list_match c l p))
    True
    (fun _ -> Seq.length c == List.Tot.length l)
= seq_list_match_seq_seq_match p c l;
  intro_implies
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    (seq_list_match c l p)
    emp
    (fun _ -> seq_seq_match_seq_list_match p c l)

(* Random array access

Since `seq_list_match` is defined recursively on the list of
high-level values, it is used naturally left-to-right. By contrast,
in practice, an application may populate an array in a different
order, or even out-of-order. `seq_seq_match` supports that scenario
better, as we show below.

*)

let seq_map (#t1 #t2: Type) (f: t1 -> t2) (s: Seq.seq t1) : Tot (Seq.seq t2) =
  Seq.init (Seq.length s) (fun i -> f (Seq.index s i))

let rec seq_map_seq_of_list (#t1 #t2: Type) (f: t1 -> t2) (l: list t1) : Lemma
  (seq_map f (Seq.seq_of_list l) `Seq.equal` Seq.seq_of_list (List.Tot.map f l))
= match l with
  | [] -> ()
  | a :: q -> seq_map_seq_of_list f q

let item_match_option
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (x1: t1)
  (x2: option t2)
: Tot vprop
= match x2 with
  | None -> emp
  | Some x2' -> p x1 x2'

let seq_seq_match_item_match_option_elim
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: STGhostT unit opened
    (seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
    (fun _ -> seq_seq_match p s1 s2 i j)
= on_range_weaken
    (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2))
    (seq_seq_match_item p s1 s2)
    i j
    (fun k ->
      rewrite
        (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2) k)
        (seq_seq_match_item p s1 s2 k)
    )

let seq_seq_match_item_match_option_intro
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: STGhostT unit opened
    (seq_seq_match p s1 s2 i j)
    (fun _ -> seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
= on_range_weaken
    (seq_seq_match_item p s1 s2)
    (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2))
    i j
    (fun k ->
      rewrite
        (seq_seq_match_item p s1 s2 k)
        (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2) k)
    )

let rec seq_seq_match_item_match_option_init
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s: Seq.seq t1)
: STGhostT unit opened
    emp
    (fun _ -> seq_seq_match (item_match_option p) s (Seq.create (Seq.length s) None) 0 (Seq.length s))
    (decreases (Seq.length s))
= if Seq.length s = 0
  then
    on_range_empty (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None)) 0 (Seq.length s)
  else begin
    seq_seq_match_item_match_option_init p (Seq.tail s);
    on_range_weaken_and_shift
      (seq_seq_match_item (item_match_option p) (Seq.tail s) (Seq.create (Seq.length (Seq.tail s)) None))
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None))
      1
      0
      (Seq.length (Seq.tail s))
      (fun k ->
        rewrite
          (seq_seq_match_item (item_match_option p) (Seq.tail s) (Seq.create (Seq.length (Seq.tail s)) None) k)
          (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None) (k + 1))
      )
      1
      (Seq.length s);
    rewrite
      emp
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None) 0);
    on_range_cons
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None))
      0
      1
      (Seq.length s)
  end

let seq_seq_match_upd
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
  (k: nat {
    i <= j /\ j < k
  })
  (x1: t1)
  (x2: t2)
: STGhostT (squash (j < Seq.length s1 /\ j < Seq.length s2)) opened
    (seq_seq_match p s1 s2 i k `star` p x1 x2)
    (fun _ -> 
      seq_seq_match p (Seq.upd s1 j x1) (Seq.upd s2 j x2) i k
    )
= seq_seq_match_length p s1 s2 i k;
  on_range_get
    (seq_seq_match_item p s1 s2)
    i j (j + 1) k;
  let res : squash (j < Seq.length s1 /\ j < Seq.length s2) = () in
  drop (seq_seq_match_item p s1 s2 j);
  rewrite
    (p x1 x2)
    (seq_seq_match_item p (Seq.upd s1 j x1) (Seq.upd s2 j x2) j);
  seq_seq_match_weaken
    p p (fun _ _ -> noop ())
    s1 (Seq.upd s1 j x1)
    s2 (Seq.upd s2 j x2)
    i j;
  seq_seq_match_weaken
    p p (fun _ _ -> noop ())
    s1 (Seq.upd s1 j x1)
    s2 (Seq.upd s2 j x2)
    (j + 1) k;
  on_range_put
    (seq_seq_match_item p (Seq.upd s1 j x1) (Seq.upd s2 j x2))
    i j j (j + 1) k;
  res
    
let seq_seq_match_item_match_option_upd
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq (option t2))
  (i j: nat)
  (k: nat {
    i <= j /\ j < k
  })
  (x1: t1)
  (x2: t2)
: STGhostT (squash (j < Seq.length s1 /\ j < Seq.length s2)) opened
    (seq_seq_match (item_match_option p) s1 s2 i k `star` p x1 x2)
    (fun _ -> 
      seq_seq_match (item_match_option p) (Seq.upd s1 j x1) (Seq.upd s2 j (Some x2)) i k
    )
= rewrite
    (p x1 x2)
    (item_match_option p x1 (Some x2));
  seq_seq_match_upd (item_match_option p) s1 s2 i j k x1 (Some x2)

let seq_seq_match_item_match_option_index
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq (option t2))
  (i j: nat)
  (k: nat {
    i <= j /\ j < k /\
    (j < Seq.length s2 ==> Some? (Seq.index s2 j))
  })
: STGhostT (squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j))) opened
    (seq_seq_match (item_match_option p) s1 s2 i k)
    (fun _ -> 
      seq_seq_match (item_match_option p) s1 (Seq.upd s2 j None) i k `star`
      p (Seq.index s1 j) (Some?.v (Seq.index s2 j))
    )
= seq_seq_match_length (item_match_option p) s1 s2 i k;
  on_range_get
    (seq_seq_match_item (item_match_option p) s1 s2)
    i j (j + 1) k;
  let res : squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j)) = () in
  rewrite
    (seq_seq_match_item (item_match_option p) s1 s2 j)
    (p (Seq.index s1 j) (Some?.v (Seq.index s2 j)));
  rewrite
    emp
    (seq_seq_match_item (item_match_option p) s1 (Seq.upd s2 j None) j);
  seq_seq_match_weaken
    (item_match_option p) (item_match_option p) (fun _ _ -> noop ())
    s1 s1
    s2 (Seq.upd s2 j None)
    i j;
  seq_seq_match_weaken
    (item_match_option p) (item_match_option p) (fun _ _ -> noop ())
    s1 s1
    s2 (Seq.upd s2 j None)
    (j + 1) k;
  on_range_put
    (seq_seq_match_item (item_match_option p) s1 (Seq.upd s2 j None))
    i j j (j + 1) k;
  res

(* Parsing into an array

While this implementation also works if the low-level value type is a pointer type, the resulting C code may not be idiomatic. Also, it assumes that the parsing function for elements always succeeds (e.g. in the case of an array of pointers, `alloc` never returns NULL.)

*)

noextract
unfold
let read_array_payload_invariant_prop0
  (#t: Type)
  (#t': Type)
  (k: parser_kind)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (cont: bool)
  (s: Seq.seq t)
  (l1: list t')
  (vr: v parse_list_kind (list t'))
  (n: SZ.t)
  (n': nat)
: Tot prop
=
      k.parser_kind_subkind == Some ParserStrong /\
      SZ.v n0 == List.Tot.length vl0.contents /\
      SZ.v n == List.Tot.length l1 /\
      Seq.length s == SZ.v n0 /\
      List.Tot.append l1 vr.contents == vl0.contents /\
      n' == SZ.v n /\
      (cont == true <==> (SZ.v n < SZ.v n0))

noextract
let read_array_payload_invariant_prop
  (#t #t': Type)
  (k: parser_kind)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (cont: bool)
  (s: Seq.seq t)
  (l1: list t')
  (vr: v parse_list_kind (list t'))
  (n: SZ.t)
  (n': nat)
: Tot prop
= read_array_payload_invariant_prop0 k n0 vl0 cont s l1 vr n n'

[@@__reduce__]
let read_array_payload_invariant_body0
  (#t #t': Type)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (s: Seq.seq t)
  (l1: list t')
  (r: byte_array)
  (vr: v parse_list_kind (list t'))
  (n: SZ.t)
  (n': nat)
: Tot vprop
=
    A.pts_to a0 full_perm s `star`
    R.pts_to pn full_perm n `star`
    R.pts_to pr full_perm r `star`
    seq_seq_match item_match s (Seq.seq_of_list vl0.contents) 0 n' `star`
    aparse (parse_list p) r vr `star`
    ((seq_seq_match item_match s (Seq.seq_of_list vl0.contents) 0 n' `star` aparse (parse_list p) r vr) `implies_`
      aparse (parse_list p) l0 vl0)

[@@erasable]
noeq
type read_array_payload_invariant_t (t t': Type) = {
  s: Seq.seq t;
  l1: list t';
  r: byte_array;
  vr: v parse_list_kind (list t');
  n: SZ.t;
  n': nat;
}

[@@__reduce__]
let read_array_payload_invariant0
  (#t #t': Type)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (cont: bool)
: Tot vprop
= exists_ (fun w ->
    read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr w.s w.l1 w.r w.vr w.n w.n' `star`
    pure (read_array_payload_invariant_prop k n0 vl0 cont w.s w.l1 w.vr w.n w.n')
  )

let read_array_payload_invariant
  (#t #t': Type)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (cont: bool)
: Tot vprop
= read_array_payload_invariant0 p item_match n0 vl0 l0 a0 pn pr cont

let intro_read_array_payload_invariant
  (#t #t': Type)
  (#opened: _)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (l1: list t')
  (cont: bool)
  (s: Seq.seq t)
  (r: byte_array)
  (vr: v parse_list_kind (list t'))
  (n: SZ.t)
  (n': nat)
: STGhost unit opened
    (read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr s l1 r vr n n')
    (fun _ -> read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr cont)
    (read_array_payload_invariant_prop0 k n0 vl0 cont s l1 vr n n')
    (fun _ -> True)
= let w : read_array_payload_invariant_t t t' = {
    s = s;
    l1 = l1;
    r = r;
    vr = vr;
    n = n;
    n' = n';
  }
  in
  rewrite
    (read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr s l1 r vr n n')
    (read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr w.s w.l1 w.r w.vr w.n w.n');
  rewrite
    (read_array_payload_invariant0 p item_match n0 vl0 l0 a0 pn pr cont)  
    (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr cont)  

let elim_read_array_payload_invariant
  (#t #t': Type)
  (#opened: _)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (cont: bool)
: STGhost (read_array_payload_invariant_t t t') opened
    (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr cont)
    (fun w -> read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr w.s w.l1 w.r w.vr w.n w.n')
    True
    (fun w -> read_array_payload_invariant_prop k n0 vl0 cont w.s w.l1 w.vr w.n w.n')
= rewrite
    (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr cont)
    (read_array_payload_invariant0 p item_match n0 vl0 l0 a0 pn pr cont);
  let _ = gen_elim () in
  vpattern_replace (fun w -> read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr w.s w.l1 w.r w.vr w.n w.n')

let list_append_length_lt
  (#t: Type)
  (l0: list t)
  (n0: SZ.t)
  (sq0': squash (SZ.v n0 == List.Tot.length l0))
  (l1: list t)
  (n: SZ.t)
  (sq1': squash (SZ.v n == List.Tot.length l1))
  (l2: list t)
  (sq0: squash (l1 `List.Tot.append` l2 == l0))
  (sq1: squash (SZ.v n < SZ.v n0))
: Tot (squash (Cons? l2))
= List.Tot.append_length l1 l2

let implies_trans_l1
  (#opened: _)
  (p q1 q2 r: vprop)
: STGhostT unit opened
    ((p @==> q1) `star` ((q1 `star` q2) @==> r))
    (fun _ -> (p `star` q2) @==> r)
= implies_reg_r p q1 q2;
  implies_trans (p `star` q2) (q1 `star` q2) r

let implies_trans_r1
  (#opened: _)
  (q1 p q2 r: vprop)
: STGhostT unit opened
    ((p @==> q2) `star` ((q1 `star` q2) @==> r))
    (fun _ -> (q1 `star` p) @==> r)
= implies_reg_l q1 p q2;
  implies_trans (q1 `star` p) (q1 `star` q2) r

let implies_trans_cut
  (#opened: _)
  (p q1 q2 r2 r3: vprop)
: STGhostT unit opened
    ((p @==> (q1 `star` q2)) `star` ((q2 `star` r2) @==> r3))
    (fun _ -> (p `star` r2) @==> (q1 `star` r3))
= implies_reg_l q1 (q2 `star` r2) r3;
  implies_with_tactic ((q1 `star` q2) `star` r2) (q1 `star` (q2 `star` r2));
  implies_trans ((q1 `star` q2) `star` r2) (q1 `star` (q2 `star` r2)) (q1 `star` r3);
  implies_trans_l1 p (q1 `star` q2) r2 (q1 `star` r3)

#push-options "--split_queries always --z3cliopt smt.arith.nl=false --z3rlimit 64"
#restart-solver

inline_for_extraction noextract let
read_array_payload_body
  (#t: Type0)
  (#t': Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (j: jumper p)
  (item_match: t -> t' -> vprop)
  (read: (
    (#va: v k t') ->
    (a: byte_array) ->
    (alen: SZ.t) ->
    ST t
    (aparse p a va)
    (fun c' ->
      item_match c' va.contents `star`
      (item_match c' va.contents `implies_` aparse p a va)
    )
    (alen == AP.len (array_of va))
    (fun _ -> True)
  ))
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (_: unit)
: STT unit
    (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr true)
    (fun _ -> exists_ (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr))
= let w = elim_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr true in // +6
  A.pts_to_length a0 _;
  let vr_cons: squash (Cons? w.vr.contents) = list_append_length_lt vl0.contents n0 () w.l1 w.n () w.vr.contents () () in
  let r = R.read pr in
  vpattern_rewrite_with_implies (fun r -> aparse (parse_list p) r _) r; // +5
  let gr' = ghost_elim_cons_with_implies p r in // +4.2
  let _ = gen_elim () in
  let sz = get_parsed_size j r in
  let r' = hop_aparse_aparse_with_size_with_implies p (parse_list p) r sz gr' in // +4.1
  implies_trans_r1 // +4 -4.1 -4.2
    (aparse p r _) // q1
    (aparse (parse_list p) r' _) // p
    (aparse (parse_list p) gr' _) // q2
    (aparse (parse_list p) r _); // r
  let v1 = vpattern (aparse p r) in
  let vr' = vpattern (aparse (parse_list p) r') in
  List.Tot.append_assoc w.l1 [v1.contents] vr'.contents;
  List.Tot.append_length w.l1 [v1.contents];
  list_index_append_cons w.l1 v1.contents vr'.contents;
  let l1' : Ghost.erased (list t') = Ghost.hide (w.l1 `List.Tot.append` [v1.contents]) in
  R.write pr r';
  let n = R.read pn in
  let _ : squash (SZ.v n < Seq.length w.s) = () in
  let n' = n `SZ.add` 1sz in
  let n'_as_nat : Ghost.erased nat = SZ.v n' in
  R.write pn n';
  let c = read r sz in // +3
  A.upd a0 n c;
  let s' = vpattern_replace_erased (A.pts_to a0 full_perm) in
  seq_seq_match_weaken_with_implies // +2
    item_match w.s s' (Seq.seq_of_list vl0.contents) (Seq.seq_of_list vl0.contents) 0 w.n';
  rewrite_with_implies // +1
    (item_match c _)
    (seq_seq_match_item item_match s' (Seq.seq_of_list vl0.contents) (SZ.v n));
  on_range_snoc_with_implies // +0
    (seq_seq_match_item item_match s' (Seq.seq_of_list vl0.contents))
    _ _ (SZ.v n) n'_as_nat;
  (* BEGIN FIXME: this should be automated away *)
  implies_trans_r2 // -0 -1
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat)
    (seq_seq_match item_match _ _ _ _)
    (seq_seq_match_item item_match _ _ _)
    (item_match c _);
  implies_trans_l2 // -2
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat)
    (seq_seq_match item_match _ _ _ _)
    (item_match c _)
    (seq_seq_match item_match _ _ _ _);
  implies_trans_r2 // -3
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat)
    (seq_seq_match item_match _ _ _ _)
    (item_match c _)
    (aparse p _ _);
  implies_trans_cut // -4
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat) // p
    (seq_seq_match item_match _ _ _ _) // q1
    (aparse p _ _) // q2
    (aparse (parse_list p) _ _) // r2
    (aparse (parse_list p) _ _); // r3
  implies_trans_r2 // -5
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat `star` aparse (parse_list p) _ _)
    (seq_seq_match item_match _ _ _ _)
    (aparse (parse_list p) _ _)
    (aparse (parse_list p) _ _);
  implies_trans // -6
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat `star` aparse (parse_list p) _ _)
    (seq_seq_match item_match _ _ _ _ `star` aparse (parse_list p) _ _)
    (aparse (parse_list p) _ _);
  (* END FIXME *)
  intro_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr l1' (n' `SZ.lt` n0) _ _ _ _ _;
  return ()

#pop-options

inline_for_extraction
let read_array_payload_from_list
  (#t #t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (j: jumper p)
  (item_match: t -> t' -> vprop)
  (read: (
    (#va: v k t') ->
    (a: byte_array) ->
    (alen: SZ.t) ->
    ST t
    (aparse p a va)
    (fun c' ->
      item_match c' va.contents `star`
      (item_match c' va.contents `implies_` aparse p a va)
    )
    (alen == AP.len (array_of va))
    (fun _ -> True)
  ))
  (n0: SZ.t)
  (#vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (#va0: Ghost.erased (Seq.seq t))
  (a0: A.array t)
: ST (Ghost.erased (Seq.seq t))
    (A.pts_to a0 full_perm va0 `star`
      aparse (parse_list p) l0 vl0
    )
    (fun res ->
      A.pts_to a0 full_perm res `star`
      seq_list_match res vl0.contents item_match `star`
      (seq_list_match res vl0.contents item_match `implies_`
        aparse (parse_list p) l0 vl0
      )
    )
    (A.length a0 == SZ.v n0 /\
      List.Tot.length vl0.contents == SZ.v n0 /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
= A.pts_to_length a0 _;
  on_range_empty
    (seq_seq_match_item item_match va0 (Seq.seq_of_list vl0.contents))
    0 0;
  intro_implies
    (seq_seq_match item_match va0 (Seq.seq_of_list vl0.contents) 0 0 `star`
      aparse (parse_list p) l0 vl0)
    (aparse (parse_list p) l0 vl0)
    emp
    (fun _ -> drop (seq_seq_match item_match _ _ _ _));
  R.with_local 0sz (fun pn ->
  R.with_local l0 (fun pr ->
    intro_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr [] (0sz `SZ.lt` n0) _ _ _ _ _;
    Steel.ST.Loops.while_loop
      (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr)
      (fun _ ->
        let gcont = elim_exists () in
        let w = elim_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr gcont in
        let n = R.read pn in
        [@@inline_let]
        let cont = n `SZ.lt` n0 in
        intro_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr w.l1 cont _ _ _ _ _;
        return cont
      )
      (read_array_payload_body j item_match read n0 vl0 l0 a0 pn pr);
    let w = elim_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr false in
    List.Tot.append_length w.l1 w.vr.contents;
    assert (Nil? w.vr.contents);
    List.Tot.append_l_nil w.l1;
    A.pts_to_length a0 _;
    rewrite_with_implies
      (seq_seq_match item_match _ _ _ _)
      (seq_seq_match item_match w.s (Seq.seq_of_list vl0.contents) 0 (List.Tot.length vl0.contents));
    seq_seq_match_seq_list_match_with_implies item_match _ vl0.contents;
    implies_trans
      (seq_list_match w.s vl0.contents item_match)
      (seq_seq_match item_match _ _ _ _)
      (seq_seq_match item_match _ _ _ _);
    implies_concl_r
      (seq_list_match w.s vl0.contents item_match)
      (seq_seq_match item_match _ _ _ _)
      (aparse (parse_list p) _ _);
    implies_trans
      (seq_list_match w.s vl0.contents item_match)
      (seq_seq_match item_match _ _ _ _ `star` aparse (parse_list p) _ _)
      (aparse (parse_list p) _ _);
    return (Ghost.hide w.s)
  ))

inline_for_extraction
let read_array_payload_from_nlist
  (#t #t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (j: jumper p)
  (item_match: t -> t' -> vprop)
  (read: (
    (#va: v k t') ->
    (a: byte_array) ->
    (alen: SZ.t) ->
    ST t
    (aparse p a va)
    (fun c' ->
      item_match c' va.contents `star`
      (item_match c' va.contents `implies_` aparse p a va)
    )
    (alen == AP.len (array_of va))
    (fun _ -> True)
  ))
  (n0: SZ.t)
  (#vl0: v (parse_nlist_kind (SZ.v n0) k) (nlist (SZ.v n0) t'))
  (l0: byte_array)
  (#va0: Ghost.erased (Seq.seq t))
  (a0: A.array t)
: ST (Ghost.erased (Seq.seq t))
    (A.pts_to a0 full_perm va0 `star`
      aparse (parse_nlist (SZ.v n0) p) l0 vl0
    )
    (fun res ->
      A.pts_to a0 full_perm res `star`
      seq_list_match res vl0.contents item_match `star`
      (seq_list_match res vl0.contents item_match `implies_`
        aparse (parse_nlist (SZ.v n0) p) l0 vl0
      )
    )
    (A.length a0 == SZ.v n0 /\
      k.parser_kind_low > 0 /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
= A.pts_to_length a0 _;
  let vl = aparse_nlist_aparse_list_with_implies p (SZ.v n0) l0 in
  let res = read_array_payload_from_list j item_match read n0 l0 a0 in
  rewrite_with_implies
    (seq_list_match _ vl.contents item_match)
    (seq_list_match _ vl0.contents item_match);
  implies_trans
    (seq_list_match _ _ item_match)
    (seq_list_match _ _ item_match)
    (aparse (parse_list p) _ _);
  implies_trans
    (seq_list_match _ _ item_match)
    (aparse (parse_list p) _ _)
    (aparse (parse_nlist (SZ.v n0) p) _ _);
  return res

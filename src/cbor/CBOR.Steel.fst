module CBOR.Steel
open Steel.ST.OnRange
open Steel.ST.GenElim

module Cbor = CBOR.SteelST
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module LPA = LowParse.SteelST.ArrayPtr
module LPS = LowParse.SteelST.Access
module R = Steel.ST.Reference
module A = Steel.ST.Array

noeq
type cbor_int = {
  typ: Cbor.major_type_uint64_or_neg_int64;
  value: U64.t;
}

noeq
type cbor_string = {
  typ: Cbor.major_type_byte_string_or_text_string;
  byte_length: U64.t;
  payload: LPS.byte_array;
  footprint: LPA.array LPS.byte;
}

noeq
type cbor_serialized = {
  byte_size: SZ.t;
  payload: LPS.byte_array;
  footprint: LPA.array LPS.byte; // ghost
}

noeq
type cbor_tagged = {
  tag: U64.t;
  payload: R.ref cbor;
}

and cbor_array = {
  count: U64.t;
  payload: A.array cbor;
  footprint: Ghost.erased (Seq.seq cbor);
}

and cbor_map_entry = {
  key: cbor;
  value: cbor;
}

and cbor_map = {
  entry_count: U64.t;
  payload: A.array cbor_map_entry;
}

and cbor =
| CBOR_Case_Int64 of cbor_int
| CBOR_Case_String of cbor_string
| CBOR_Case_Tagged of cbor_tagged
| CBOR_Case_Array of cbor_array
| CBOR_Case_Map of cbor_map
| CBOR_Case_Simple_value of Cbor.simple_value
| CBOR_Case_Serialized of cbor_serialized

let dummy_cbor : cbor = CBOR_Case_Simple_value 0uy

let raw_data_item_match_serialized_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: LPS.byte_array)
  (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Serialized c ->
    c.byte_size == LPA.len (LPS.array_of w) /\
    c.payload == a /\
    c.footprint == LPS.array_of w /\
    w.LPS.contents == v
  | _ -> False

[@@__reduce__]
let raw_data_item_match_serialized0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun (a: LPS.byte_array) -> exists_ (fun (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) ->
    LPS.aparse Cbor.parse_raw_data_item a w `star`
    pure (
      raw_data_item_match_serialized_prop c v a w
    )
  ))

let raw_data_item_match_simple_value_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Simple_value c -> v == Cbor.Simple c
  | _ -> False

[@@__reduce__]
let raw_data_item_match_simple_value0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= pure (raw_data_item_match_simple_value_prop c v)

let raw_data_item_match_int_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
: GTot prop
= match c with
  | CBOR_Case_Int64 c -> v == Cbor.Int64 c.typ c.value
  | _ -> False

[@@__reduce__]
let raw_data_item_match_int0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= pure (raw_data_item_match_int_prop c v)

let raw_data_item_match_string_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: LPS.byte_array)
  (w: LPA.v LPS.byte)
: Tot prop
= match c with
  | CBOR_Case_String c ->
    U64.v c.byte_length == LPA.length (LPA.array_of w) /\
    v == Cbor.String c.typ (LPA.contents_of w) /\
    c.footprint == LPA.array_of w /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_string0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun a -> exists_ (fun w ->
    LPA.arrayptr a w `star`
    pure (raw_data_item_match_string_prop c v a w)
  ))

let raw_data_item_match_tagged_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: R.ref cbor)
: Tot prop
= match v, c with
  | Cbor.Tagged tag _, CBOR_Case_Tagged c ->
    c.tag == tag /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_tagged0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Tagged? v })
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun a -> exists_ (fun c' ->
    R.pts_to a full_perm c' `star`
    raw_data_item_match c' (Cbor.Tagged?.v v) `star`
    pure (raw_data_item_match_tagged_prop c v a)
  ))

let raw_data_item_match_array_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (s: Seq.seq cbor)
  (a: A.array cbor)
: GTot prop
= match c, v with
  | CBOR_Case_Array c, Cbor.Array l ->
    U64.v c.count == List.Tot.length l /\
    Ghost.reveal c.footprint == s /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_array0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Array? v })
  (raw_data_item_array_match: (Seq.seq cbor -> (v': list Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: A.array cbor) -> exists_ (fun (c': Seq.seq cbor) ->
    A.pts_to a full_perm c' `star`
    raw_data_item_array_match c' (Cbor.Array?.v v) `star`
    pure (
      raw_data_item_match_array_prop c v c' a
    )
  ))

let raw_data_item_match_map_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: A.array cbor_map_entry)
: GTot prop
= match c, v with
  | CBOR_Case_Map c, Cbor.Map l ->
    U64.v c.entry_count == List.Tot.length l /\
    c.payload == a
  | _ -> False

[@@__reduce__]
let raw_data_item_match_map0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Map? v })
  (raw_data_item_map_match: (Seq.seq cbor_map_entry -> (v': list (Cbor.raw_data_item & Cbor.raw_data_item) { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: A.array cbor_map_entry) -> exists_ (fun (c': Seq.seq cbor_map_entry) ->
    A.pts_to a full_perm c' `star`
    raw_data_item_map_match c' (Cbor.Map?.v v) `star`
    pure (
      raw_data_item_match_map_prop c v a
    )
  ))

noextract
let fstp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a1 = fst x

noextract
let sndp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a2 = snd x

[@@__reduce__]
let raw_data_item_map_entry_match1
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v1 }) -> vprop))
: Tot vprop
= raw_data_item_match c1.key (fstp v1) `star`
  raw_data_item_match c1.value (sndp v1)

let raw_data_item_map_entry_match0
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << l }) -> vprop))
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item) { v1 << l })
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 raw_data_item_match

[@@__reduce__]
let seq_list_match_nil0
  (#t: Type)
  (c: Seq.seq t)
: Tot vprop
= pure (c `Seq.equal` Seq.empty)

[@@__reduce__]
let seq_list_match_cons0
  (#t #t': Type)
  (c: Seq.seq t)
  (l: list t' { Cons? l })
  (raw_data_item_match: (t -> (v': t' { v' << l }) -> vprop))
  (raw_data_item_array_match: (Seq.seq t -> (v': list t') -> (raw_data_item_match: (t -> (v'': t' { v'' << v' }) -> vprop) { v' << l }) ->
vprop))
: Tot vprop
= exists_ (fun (c1: t) -> exists_ (fun (c2: Seq.seq t) ->
    raw_data_item_match c1 (List.Tot.hd l) `star`
    raw_data_item_array_match c2 (List.Tot.tl l) raw_data_item_match `star`
    pure (c `Seq.equal` Seq.cons c1 c2)
  ))

let rec seq_list_match
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (raw_data_item_match: (t -> (v': t' { v' << v }) -> vprop))
: Tot vprop
  (decreases v)
= if Nil? v
  then seq_list_match_nil0 c
  else seq_list_match_cons0 c v raw_data_item_match seq_list_match

let seq_list_match_cons_eq
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (raw_data_item_match: (t -> (v': t' { v' << v }) -> vprop))
: Lemma
  (requires (Cons? v))
  (ensures (
    seq_list_match c v raw_data_item_match ==
    seq_list_match_cons0 c v raw_data_item_match seq_list_match
  ))
= let a :: q = v in
  assert_norm (seq_list_match c (a :: q) raw_data_item_match ==
    seq_list_match_cons0 c (a :: q) raw_data_item_match seq_list_match
  )

let rec raw_data_item_match
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= match c, v with
  | CBOR_Case_Serialized _, _ -> raw_data_item_match_serialized0 c v
  | CBOR_Case_Simple_value _, Cbor.Simple _ -> raw_data_item_match_simple_value0 c v
  | CBOR_Case_Int64 _, Cbor.Int64 _ _ -> raw_data_item_match_int0 c v
  | CBOR_Case_String _, Cbor.String _ _ -> raw_data_item_match_string0 c v
  | CBOR_Case_Array _, Cbor.Array _ -> raw_data_item_match_array0 c v raw_data_item_array_match
  | CBOR_Case_Map _, Cbor.Map _ -> raw_data_item_match_map0 c v raw_data_item_map_match
  | CBOR_Case_Tagged _, Cbor.Tagged _ _ -> raw_data_item_match_tagged0 c v raw_data_item_match
  | _ -> pure False

and raw_data_item_array_match
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= seq_list_match c v raw_data_item_match

and raw_data_item_map_match
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= seq_list_match c v (raw_data_item_map_entry_match0 v raw_data_item_match)

#set-options "--ide_id_info_off"

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

let seq_seq_match_item
  (#t1 #t2: Type)
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

let raw_data_item_match_get_case
  (#opened: _)
  (#v: Cbor.raw_data_item)
  (c: cbor)
: STGhost unit opened
    (raw_data_item_match c v)
    (fun _ -> raw_data_item_match c v)
    True
    (fun _ -> match c, v with
    | CBOR_Case_Serialized _, _
    | CBOR_Case_Array _, Cbor.Array _
    | CBOR_Case_Int64 _, Cbor.Int64 _ _
    | CBOR_Case_Map _, Cbor.Map _
    | CBOR_Case_Simple_value _, Cbor.Simple _
    | CBOR_Case_String _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> True
    | _ -> False
    )
= match c, v with
    | CBOR_Case_Serialized _, _
    | CBOR_Case_Array _, Cbor.Array _
    | CBOR_Case_Int64 _, Cbor.Int64 _ _
    | CBOR_Case_Map _, Cbor.Map _
    | CBOR_Case_Simple_value _, Cbor.Simple _
    | CBOR_Case_String _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> noop ()
    | _ ->
      rewrite (raw_data_item_match c v) (pure False);
      let _ = gen_elim () in
      rewrite emp (raw_data_item_match c v)

let raw_data_item_match_array_intro
  (#opened: _)
  (#c': Seq.seq cbor)
  (#v': list Cbor.raw_data_item)
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: STGhostT unit opened
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v')
    (fun _ ->
      raw_data_item_match
        (CBOR_Case_Array ({
          count = len;
          payload = a;
          footprint = c';
        }))
        (Cbor.Array v')
    )
= noop ();
  rewrite_with_tactic
    (raw_data_item_match_array0
      (CBOR_Case_Array ({
        count = len;
        payload = a;
        footprint = c';
      }))
      (Cbor.Array v')
      raw_data_item_array_match
    )
    (raw_data_item_match _ _)

let raw_data_item_match_array_elim
  (#opened: _)
  (a: cbor_array)
  (v: Cbor.raw_data_item)
: STGhost (squash (Cbor.Array? v)) opened
    (raw_data_item_match (CBOR_Case_Array a) v)
    (fun _ ->
      A.pts_to a.payload full_perm a.footprint `star`
      raw_data_item_array_match a.footprint (Cbor.Array?.v v)
    )
    True
    (fun _ -> U64.v a.count == List.Tot.length (Cbor.Array?.v v))
= raw_data_item_match_get_case _;
  let sq : squash (Cbor.Array? v) = () in
  let Cbor.Array v' = v in
  vpattern_rewrite (raw_data_item_match _) (Cbor.Array v');
  rewrite_with_tactic
    (raw_data_item_match _ _)
    (raw_data_item_match_array0 (CBOR_Case_Array a) (Cbor.Array v') raw_data_item_array_match);
  let _ = gen_elim () in
  rewrite (A.pts_to _ _ _) (A.pts_to a.payload full_perm a.footprint);
  rewrite (raw_data_item_array_match _ _) (raw_data_item_array_match a.footprint (Cbor.Array?.v v));
  sq

let constr_cbor_array
  (#c': Ghost.erased (Seq.seq cbor))
  (#v': Ghost.erased (list Cbor.raw_data_item))
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: ST cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v')
    (fun res ->
      raw_data_item_match res (Cbor.Array v') `star`
      (raw_data_item_match res (Cbor.Array v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_array_match c' v')
      )
    )
    True
    (fun res ->
      res == CBOR_Case_Array ({
        payload = a;
        count = len;
        footprint = c';
      })
    )
= [@@inline_let]
  let ares : cbor_array = {
    count = len;
    payload = a;
    footprint = c';
  }
  in
  [@@inline_let]
  let res = CBOR_Case_Array ares in
  raw_data_item_match_array_intro a len;
  rewrite (raw_data_item_match _ _) (raw_data_item_match res (Cbor.Array v'));
  intro_implies
    (raw_data_item_match res (Cbor.Array v'))
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v'
    )
    emp
    (fun _ ->
      rewrite (raw_data_item_match _ _) (raw_data_item_match (CBOR_Case_Array ares) (Cbor.Array v'));
      let _ = raw_data_item_match_array_elim _ _ in
      rewrite (A.pts_to _ _ _) (A.pts_to a full_perm c');
      rewrite (raw_data_item_array_match _ _) (raw_data_item_array_match c' v')
    );
  return res

[@@__reduce__]
let maybe_cbor_array
  (v: Cbor.raw_data_item)
: GTot (list Cbor.raw_data_item)
= match v with
  | Cbor.Array l -> l
  | _ -> []

let destr_cbor_array
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_array
    (raw_data_item_match a v)
    (fun res ->
      A.pts_to res.payload full_perm res.footprint `star`
      raw_data_item_array_match res.footprint (maybe_cbor_array v) `star`
      ((A.pts_to res.payload full_perm res.footprint `star`
        raw_data_item_array_match res.footprint (maybe_cbor_array v)) `implies_`
        raw_data_item_match a v
      )
    )
    (CBOR_Case_Array? a)
    (fun res ->
      a == CBOR_Case_Array res /\
      Cbor.Array? v /\
      U64.v res.count == List.Tot.length (Cbor.Array?.v v)
    )
= raw_data_item_match_get_case _;
  let CBOR_Case_Array res = a in
  vpattern_rewrite
    (fun a -> raw_data_item_match a _)
    (CBOR_Case_Array res);
  let _ = raw_data_item_match_array_elim _ _ in
  vpattern_rewrite (raw_data_item_array_match _) (maybe_cbor_array v);
  intro_implies
    (A.pts_to res.payload full_perm res.footprint `star`
      raw_data_item_array_match res.footprint (maybe_cbor_array v))
    (raw_data_item_match a v)
    emp
    (fun _ ->
      raw_data_item_match_array_intro _ res.count;
      rewrite (raw_data_item_match _ _) (raw_data_item_match _ _)
    );
  return res

let read_valid_cbor_from_buffer_with_size_strong
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
  (alen: SZ.t)
: ST cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents `star`
      (raw_data_item_match c' va.contents `implies_` LPS.aparse Cbor.parse_raw_data_item a va)
    )
    (alen == LPA.len (LPS.array_of va))
    (fun c' -> CBOR_Case_Serialized? c')
= [@@inline_let]
  let c_pl : cbor_serialized = ({
    byte_size = alen;
    payload = a;
    footprint = LPS.array_of va;
  })
  in
  [@@inline_let]
  let c' = CBOR_Case_Serialized c_pl in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (raw_data_item_match c' va.contents);
  intro_implies
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (LPS.aparse Cbor.parse_raw_data_item a va)
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite (LPS.aparse Cbor.parse_raw_data_item _ _) (LPS.aparse Cbor.parse_raw_data_item a va) // works thanks to c_pl.footprint
    );
  implies_trans
    (raw_data_item_match c' va.contents)
    (raw_data_item_match_serialized0 (CBOR_Case_Serialized c_pl) va.contents)
    (LPS.aparse Cbor.parse_raw_data_item a va);
  return c'

let read_valid_cbor_from_buffer_with_size
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
  (alen: SZ.t)
: ST cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents
    )
    (alen == LPA.len (LPS.array_of va))
    (fun c' -> CBOR_Case_Serialized? c')
= let c' = read_valid_cbor_from_buffer_with_size_strong a alen in
  drop (_ `implies_` _);
  return c'

let read_valid_cbor_from_buffer
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (a: LPS.byte_array)
: STT cbor
    (LPS.aparse Cbor.parse_raw_data_item a va)
    (fun c' ->
      raw_data_item_match c' va.contents
    )
= let alen = LPS.get_parsed_size Cbor.jump_raw_data_item a in
  read_valid_cbor_from_buffer_with_size a alen

let read_cbor_int64
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> raw_data_item_match c (Ghost.reveal va))
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.typ c'.value
    )
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Int64 c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_int0 c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_int0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let typ = Cbor.read_major_type cs.payload in
    let value = Cbor.read_int64 cs.payload in
    let c' : cbor_int = {
      typ = typ;
      value = value;
    }
    in
    noop ();
    elim_implies
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_int64
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.typ c'.value
    )
= let c' = read_cbor_int64 c in
  rewrite
    (raw_data_item_match_int0 (CBOR_Case_Int64 c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va));
  intro_implies
    (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> drop (raw_data_item_match (CBOR_Case_Int64 c') (Ghost.reveal va)));
  return c'

let constr_cbor_int64
  (ty: Cbor.major_type_uint64_or_neg_int64)
  (value: U64.t)
: ST cbor
    emp
    (fun c -> raw_data_item_match c (Cbor.Int64 ty value))
    True
    (fun c -> c == CBOR_Case_Int64 ({ typ = ty; value = value }))
= [@@inline_let]
  let c = CBOR_Case_Int64 ({ typ = ty; value = value }) in
  noop ();
  rewrite
    (raw_data_item_match_int0 c (Cbor.Int64 ty value))
    (raw_data_item_match c (Cbor.Int64 ty value));
  return c

let read_cbor_simple_value
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match c (Ghost.reveal va)
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' -> Ghost.reveal va == Cbor.Simple c')
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_Simple_value c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_simple_value0 c (Ghost.reveal va));
    let _ = gen_elim () in
    elim_implies
      (raw_data_item_match_simple_value0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let c' = Cbor.read_simple_value cs.payload in
    elim_implies
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_simple_value
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' -> Ghost.reveal va == Cbor.Simple c')
= let c' = read_cbor_simple_value c in
  rewrite
    (raw_data_item_match_simple_value0 (CBOR_Case_Simple_value c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va));
  intro_implies
    (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> drop (raw_data_item_match (CBOR_Case_Simple_value c') (Ghost.reveal va)));
  return c'

let constr_cbor_simple_value
  (value: Cbor.simple_value)
: ST cbor
    emp
    (fun c -> raw_data_item_match c (Cbor.Simple value))
    True
    (fun c -> c == CBOR_Case_Simple_value value)
= [@@inline_let]
  let c = CBOR_Case_Simple_value value in
  noop ();
  rewrite
    (raw_data_item_match_simple_value0 c (Cbor.Simple value))
    (raw_data_item_match c (Cbor.Simple value));
  return c

let destr_cbor_string'
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_string
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va) `star`
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va) `implies_` raw_data_item_match c (Ghost.reveal va))
    )
    (Cbor.String? (Ghost.reveal va))
    (fun _ -> True)
= raw_data_item_match_get_case c;
  match c with
  | CBOR_Case_String c' ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
    return c'
  | CBOR_Case_Serialized cs ->
    rewrite_with_implies
      (raw_data_item_match c (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    let _ = gen_elim () in
    vpattern_rewrite (fun a -> LPS.aparse Cbor.parse_raw_data_item a _) cs.payload;
    let va' = vpattern_replace (LPS.aparse Cbor.parse_raw_data_item _) in
    let typ = Cbor.read_major_type cs.payload in
    let len = Cbor.read_argument_as_uint64 cs.payload in
    let payload = Cbor.focus_string cs.payload in
    let _ = gen_elim () in
    let vpl : LPA.v LPS.byte = vpattern_replace (fun vpl -> LPA.arrayptr payload vpl `star` (LPA.arrayptr payload vpl `implies_` LPS.aparse Cbor.parse_raw_data_item cs.payload va')) in
    let c' : cbor_string = {
      typ = typ;
      byte_length = len;
      payload = payload;
      footprint = LPA.array_of vpl;
    }
    in
    noop ();
    intro_implies
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (LPA.arrayptr payload vpl `implies_` LPS.aparse Cbor.parse_raw_data_item cs.payload va')
      (fun _ ->
        let _ = gen_elim () in
        rewrite (LPA.arrayptr _ _) (LPA.arrayptr payload vpl);
        elim_implies
          (LPA.arrayptr payload vpl)
          (LPS.aparse Cbor.parse_raw_data_item cs.payload va');
        noop ()
      );
    rewrite_with_implies
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
    implies_trans
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va));
    implies_trans
      (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
      (raw_data_item_match_serialized0 c (Ghost.reveal va))
      (raw_data_item_match c (Ghost.reveal va));
    return c'

let destr_cbor_string
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: STT cbor_string
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' -> exists_ (fun vc' ->
      LPA.arrayptr c'.payload vc' `star`
      (LPA.arrayptr c'.payload vc' `implies_` raw_data_item_match c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.byte_length == Seq.length (LPA.contents_of' vc') /\
        Ghost.reveal va == Cbor.String c'.typ (LPA.contents_of vc')
    )))
= let c' = destr_cbor_string' c in
  rewrite_with_implies
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va));
  let _ = gen_elim () in
  vpattern_rewrite (fun a -> LPA.arrayptr a _) c'.payload;
  let vc' = vpattern_replace (LPA.arrayptr _) in
  intro_implies
    (LPA.arrayptr c'.payload vc')
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
    (pure (raw_data_item_match_string_prop (CBOR_Case_String c') (Ghost.reveal va) c'.payload vc')) // FIXME: WHY WHY WHY?
    (fun _ ->
      noop ()
    );
  implies_trans
    (LPA.arrayptr c'.payload vc')
    (raw_data_item_match_string0 (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va));
  implies_trans
    (LPA.arrayptr c'.payload vc')
    (raw_data_item_match (CBOR_Case_String c') (Ghost.reveal va))
    (raw_data_item_match c (Ghost.reveal va));
  intro_exists vc' (fun vc' -> // FIXME: WHY WHY WHY?
    LPA.arrayptr c'.payload vc' `star`
      (LPA.arrayptr c'.payload vc' `implies_` raw_data_item_match c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.byte_length == Seq.length (LPA.contents_of' vc') /\
        Ghost.reveal va == Cbor.String c'.typ (LPA.contents_of vc')
    )  
  );
  return c'

let constr_cbor_string
  (#va: LPA.v LPS.byte)
  (typ: Cbor.major_type_byte_string_or_text_string)
  (a: LPS.byte_array)
  (len: U64.t {
    U64.v len == Seq.length (LPA.contents_of va)
  })
: STT cbor
    (LPA.arrayptr a va)
    (fun c' ->
      raw_data_item_match c' (Cbor.String typ (LPA.contents_of va)) `star`
      (raw_data_item_match c' (Cbor.String typ (LPA.contents_of va)) `implies_`
        LPA.arrayptr a va
      )
    )
= [@@inline_let]
  let c' = CBOR_Case_String ({
    typ = typ;
    payload = a;
    byte_length = len;
    footprint = LPA.array_of va;
  })
  in
  noop ();
  rewrite_with_implies
    (raw_data_item_match_string0 c' (Cbor.String typ (LPA.contents_of va)))
    (raw_data_item_match c' (Cbor.String typ (LPA.contents_of va)));
  intro_implies
    (raw_data_item_match_string0 c' (Cbor.String typ (LPA.contents_of va)))
    (LPA.arrayptr a va)
    emp
    (fun _ ->
      let _ = gen_elim () in
      rewrite (LPA.arrayptr _ _) (LPA.arrayptr a va)
    );
  implies_trans
    (raw_data_item_match c' (Cbor.String typ (LPA.contents_of va)))
    (raw_data_item_match_string0 c' (Cbor.String typ (LPA.contents_of va)))
    (LPA.arrayptr a va);
  return c'

module GR = Steel.ST.GhostReference

noextract
unfold
let read_cbor_array_payload_invariant_prop0
  (n0: U64.t)
  (vl0: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (cont: bool)
  (s: Seq.seq cbor)
  (l1: list Cbor.raw_data_item)
  (vr: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (n: U64.t)
  (n': nat)
: Tot prop
=
      SZ.fits_u64 /\
      U64.v n0 == List.Tot.length vl0.contents /\
      U64.v n == List.Tot.length l1 /\
      Seq.length s == U64.v n0 /\
      List.Tot.append l1 vr.LPS.contents == vl0.LPS.contents /\
      n' == U64.v n /\
      (cont == true <==> (U64.v n < U64.v n0))

noextract
let read_cbor_array_payload_invariant_prop
  (n0: U64.t)
  (vl0: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (cont: bool)
  (s: Seq.seq cbor)
  (l1: list Cbor.raw_data_item)
  (vr: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (n: U64.t)
  (n': nat)
: Tot prop
= read_cbor_array_payload_invariant_prop0 n0 vl0 cont s l1 vr n n'

[@@__reduce__]
let read_cbor_array_payload_invariant_body0
  (n0: U64.t)
  (vl0: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (a0: A.array cbor)
  (pn: R.ref U64.t)
  (pl1: GR.ref (list Cbor.raw_data_item))
  (pr: R.ref LPS.byte_array)
  (s: Seq.seq cbor)
  (l1: list Cbor.raw_data_item)
  (r: LPS.byte_array)
  (vr: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (n: U64.t)
  (n': nat)
: Tot vprop
=
    A.pts_to a0 full_perm s `star`
    GR.pts_to pl1 full_perm l1 `star`
    R.pts_to pn full_perm n `star`
    R.pts_to pr full_perm r `star`
    seq_seq_match raw_data_item_match s (Seq.seq_of_list vl0.contents) 0 n' `star`
    LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) r vr `star`
    ((seq_seq_match raw_data_item_match s (Seq.seq_of_list vl0.contents) 0 n' `star` LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) r vr) `implies_`
      LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) l0 vl0)

[@@erasable]
noeq
type read_cbor_array_payload_invariant_t = {
  s: Seq.seq cbor;
  l1: list Cbor.raw_data_item;
  r: LPS.byte_array;
  vr: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item);
  n: U64.t;
  n': nat;
}

[@@__reduce__]
let read_cbor_array_payload_invariant0
  (n0: U64.t)
  (vl0: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (a0: A.array cbor)
  (pn: R.ref U64.t)
  (pl1: GR.ref (list Cbor.raw_data_item))
  (pr: R.ref LPS.byte_array)
  (cont: bool)
: Tot vprop
= exists_ (fun w ->
    read_cbor_array_payload_invariant_body0 n0 vl0 l0 a0 pn pl1 pr w.s w.l1 w.r w.vr w.n w.n' `star`
    pure (read_cbor_array_payload_invariant_prop n0 vl0 cont w.s w.l1 w.vr w.n w.n')
  )

let read_cbor_array_payload_invariant
  (n0: U64.t)
  (vl0: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (a0: A.array cbor)
  (pn: R.ref U64.t)
  (pl1: GR.ref (list Cbor.raw_data_item))
  (pr: R.ref LPS.byte_array)
  (cont: bool)
: Tot vprop
= read_cbor_array_payload_invariant0 n0 vl0 l0 a0 pn pl1 pr cont

[@@__reduce__]
let intro_read_cbor_array_payload_invariant
  (#opened: _)
  (n0: U64.t)
  (vl0: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (a0: A.array cbor)
  (pn: R.ref U64.t)
  (pl1: GR.ref (list Cbor.raw_data_item))
  (pr: R.ref LPS.byte_array)
  (cont: bool)
  (s: Seq.seq cbor)
  (l1: list Cbor.raw_data_item)
  (r: LPS.byte_array)
  (vr: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (n: U64.t)
  (n': nat)
: STGhost unit opened
    (read_cbor_array_payload_invariant_body0 n0 vl0 l0 a0 pn pl1 pr s l1 r vr n n')
    (fun _ -> read_cbor_array_payload_invariant n0 vl0 l0 a0 pn pl1 pr cont)
    (read_cbor_array_payload_invariant_prop0 n0 vl0 cont s l1 vr n n')
    (fun _ -> True)
= let w : read_cbor_array_payload_invariant_t = {
    s = s;
    l1 = l1;
    r = r;
    vr = vr;
    n = n;
    n' = n';
  }
  in
  rewrite
    (read_cbor_array_payload_invariant_body0 n0 vl0 l0 a0 pn pl1 pr s l1 r vr n n')
    (read_cbor_array_payload_invariant_body0 n0 vl0 l0 a0 pn pl1 pr w.s w.l1 w.r w.vr w.n w.n');
  rewrite
    (read_cbor_array_payload_invariant0 n0 vl0 l0 a0 pn pl1 pr cont)  
    (read_cbor_array_payload_invariant n0 vl0 l0 a0 pn pl1 pr cont)  

let elim_read_cbor_array_payload_invariant
  (#opened: _)
  (n0: U64.t)
  (vl0: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (a0: A.array cbor)
  (pn: R.ref U64.t)
  (pl1: GR.ref (list Cbor.raw_data_item))
  (pr: R.ref LPS.byte_array)
  (cont: bool)
: STGhost read_cbor_array_payload_invariant_t opened
    (read_cbor_array_payload_invariant n0 vl0 l0 a0 pn pl1 pr cont)
    (fun w -> read_cbor_array_payload_invariant_body0 n0 vl0 l0 a0 pn pl1 pr w.s w.l1 w.r w.vr w.n w.n')
    True
    (fun w -> read_cbor_array_payload_invariant_prop n0 vl0 cont w.s w.l1 w.vr w.n w.n')
= rewrite
    (read_cbor_array_payload_invariant n0 vl0 l0 a0 pn pl1 pr cont)
    (read_cbor_array_payload_invariant0 n0 vl0 l0 a0 pn pl1 pr cont);
  let _ = gen_elim () in
  vpattern_replace (fun w -> read_cbor_array_payload_invariant_body0 n0 vl0 l0 a0 pn pl1 pr w.s w.l1 w.r w.vr w.n w.n')

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
let list_elim_cons_with_implies_and_size
  (#k: Ghost.erased LPS.parser_kind)
  (#t: Type0)
  (#p: LPS.parser k t)
  (j: LPS.jumper p)
  (#va: _)
  (a: LPS.byte_array)
  (#dummy_sz: Ghost.erased SZ.t)
  (psz: R.ref SZ.t)
  (sq: squash (Cons? va.LPS.contents))
: ST LPS.byte_array
    (LPS.aparse (LowParse.Spec.List.parse_list p) a va `star` R.pts_to psz full_perm dummy_sz)
    (fun a2 -> exists_ (fun va1 -> exists_ (fun va2 -> exists_ (fun sz ->
      LPS.aparse p a va1 `star`
      LPS.aparse (LowParse.Spec.List.parse_list p) a2 va2 `star`
      R.pts_to psz full_perm sz `star`
      ((LPS.aparse p a va1 `star` LPS.aparse (LowParse.Spec.List.parse_list p) a2 va2) `implies_`
        LPS.aparse (LowParse.Spec.List.parse_list p) a va) `star`
      pure (
        sz == LPA.len (LPS.array_of va1) /\
        va.contents == va1.LPS.contents :: va2.LPS.contents
    )))))
    (k.LPS.parser_kind_subkind == Some LPS.ParserStrong)
    (fun _ -> True)
= let ga2 = LowParse.SteelST.List.Base.ghost_elim_cons p a in
  let _ = gen_elim () in
  let sz = LPS.get_parsed_size j a in
  R.write psz sz;
  let a2 = LPS.hop_aparse_aparse_with_size _ _ a sz ga2 in
  intro_implies
    (LPS.aparse p a _ `star` LPS.aparse (LowParse.Spec.List.parse_list p) a2 _)
    (LPS.aparse (LowParse.Spec.List.parse_list p) a va)
    emp
    (fun _ ->
      let _ = LowParse.SteelST.List.Base.intro_cons p a a2 in
      vpattern_rewrite (LPS.aparse (LowParse.Spec.List.parse_list p) a) va
    );
  return a2

#pop-options

let list_append_length_lt
  (#t: Type)
  (l0: list t)
  (n0: U64.t)
  (sq0': squash (U64.v n0 == List.Tot.length l0))
  (l1: list t)
  (n: U64.t)
  (sq1': squash (U64.v n == List.Tot.length l1))
  (l2: list t)
  (sq0: squash (l1 `List.Tot.append` l2 == l0))
  (sq1: squash (U64.v n < U64.v n0))
: Tot (squash (Cons? l2))
= List.Tot.append_length l1 l2

let implies_trans_cut
  (#opened: _)
  (p q1 q2 r2 r3: vprop)
: STGhostT unit opened
    ((p @==> (q1 `star` q2)) `star` ((q2 `star` r2) @==> r3))
    (fun _ -> (p `star` r2) @==> (q1 `star` r3))
= implies_with_tactic ((q1 `star` q2) `star` r2) (q1 `star` (q2 `star` r2));
  implies_reg_r p (q1 `star` q2) r2;
  implies_trans (p `star` r2) ((q1 `star` q2) `star` r2) (q1 `star` (q2 `star` r2));
  implies_reg_l q1 (q2 `star` r2) r3;
  implies_trans (p `star` r2) (q1 `star` (q2 `star` r2)) (q1 `star` r3)

#push-options "--split_queries always --z3cliopt smt.arith.nl=false --z3rlimit 64"
#restart-solver

inline_for_extraction noextract let
read_cbor_array_payload_body
  (n0: U64.t)
  (vl0: LPS.v LowParse.Spec.List.parse_list_kind (list Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (a0: A.array cbor)
  (pn: R.ref U64.t)
  (pl1: GR.ref (list Cbor.raw_data_item))
  (pr: R.ref LPS.byte_array)
: STT unit
    (read_cbor_array_payload_invariant n0 vl0 l0 a0 pn pl1 pr true)
    (fun _ -> exists_ (read_cbor_array_payload_invariant n0 vl0 l0 a0 pn pl1 pr))
= let w = elim_read_cbor_array_payload_invariant n0 vl0 l0 a0 pn pl1 pr true in // +6
  A.pts_to_length a0 _;
  let vr_cons: squash (Cons? w.vr.LPS.contents) = list_append_length_lt vl0.LPS.contents n0 () w.l1 w.n () w.vr.LPS.contents () () in
  let r = R.read pr in
  vpattern_rewrite_with_implies (fun r -> LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) r _) r; // +5
  R.with_local 0sz (fun psz ->
    let r' = list_elim_cons_with_implies_and_size Cbor.jump_raw_data_item r psz vr_cons in // +4
    let _ = gen_elim () in
    let v1 = vpattern (LPS.aparse Cbor.parse_raw_data_item r) in
    let vr' = vpattern (LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) r') in
    List.Tot.append_assoc w.l1 [v1.LPS.contents] vr'.LPS.contents;
    List.Tot.append_length w.l1 [v1.LPS.contents];
    list_index_append_cons w.l1 v1.LPS.contents vr'.LPS.contents;
    let l1' = Ghost.hide (w.l1 `List.Tot.append` [v1.LPS.contents]) in
    noop ();
    GR.write pl1 l1';
    R.write pr r';
    let n = R.read pn in
    let n_as_sz = SZ.uint64_to_sizet n in
    let n' = n `U64.add` 1uL in
    let n'_as_nat : Ghost.erased nat = U64.v n' in
    R.write pn n';
    let sz = R.read psz in
    let c = read_valid_cbor_from_buffer_with_size_strong r sz in // +3
    A.upd a0 n_as_sz c;
    let s' = vpattern_replace_erased (A.pts_to a0 full_perm) in
    seq_seq_match_weaken_with_implies // +2
      raw_data_item_match _ s' _ (Seq.seq_of_list vl0.LPS.contents) _ _;
    rewrite_with_implies // +1
      (raw_data_item_match c _)
      (seq_seq_match_item raw_data_item_match s' (Seq.seq_of_list vl0.LPS.contents) (U64.v n));
    on_range_snoc_with_implies // +0
      (seq_seq_match_item raw_data_item_match s' (Seq.seq_of_list vl0.LPS.contents))
      _ _ (U64.v n) n'_as_nat;
    (* BEGIN FIXME: this should be automated away *)
    implies_trans_r2 // -0 -1
      (seq_seq_match raw_data_item_match s' (Seq.seq_of_list vl0.LPS.contents) 0 n'_as_nat)
      (seq_seq_match raw_data_item_match _ _ _ _)
      (seq_seq_match_item raw_data_item_match _ _ _)
      (raw_data_item_match c _);
    implies_trans_l2 // -2
      (seq_seq_match raw_data_item_match s' (Seq.seq_of_list vl0.LPS.contents) 0 n'_as_nat)
      (seq_seq_match raw_data_item_match _ _ _ _)
      (raw_data_item_match c _)
      (seq_seq_match raw_data_item_match _ _ _ _);
    implies_trans_r2 // -3
      (seq_seq_match raw_data_item_match s' (Seq.seq_of_list vl0.LPS.contents) 0 n'_as_nat)
      (seq_seq_match raw_data_item_match _ _ _ _)
      (raw_data_item_match c _)
      (LPS.aparse Cbor.parse_raw_data_item _ _);
    implies_trans_cut // -4
      (seq_seq_match raw_data_item_match s' (Seq.seq_of_list vl0.LPS.contents) 0 n'_as_nat) // p
      (seq_seq_match raw_data_item_match _ _ _ _) // q1
      (LPS.aparse Cbor.parse_raw_data_item _ _) // q2
      (LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) _ _) // r2
      (LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) _ _); // r3
    implies_trans_r2 // -5
      (seq_seq_match raw_data_item_match s' (Seq.seq_of_list vl0.LPS.contents) 0 n'_as_nat `star` LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) _ _)
      (seq_seq_match raw_data_item_match _ _ _ _)
      (LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) _ _)
      (LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) _ _);
    implies_trans // -6
      (seq_seq_match raw_data_item_match s' (Seq.seq_of_list vl0.LPS.contents) 0 n'_as_nat `star` LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) _ _)
      (seq_seq_match raw_data_item_match _ _ _ _ `star` LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) _ _)
      (LPS.aparse (LowParse.Spec.List.parse_list Cbor.parse_raw_data_item) _ _);
    (* END FIXME *)
    intro_read_cbor_array_payload_invariant n0 vl0 l0 a0 pn pl1 pr (n' `U64.lt` n0) _ _ _ _ _ _;
    return ()
  )

#pop-options

assume val read_cbor_array_payload
  (n0: U64.t)
  (vl0: LPS.v (LowParse.Spec.VCList.parse_nlist_kind (U64.v n0) Cbor.parse_raw_data_item_kind) (LowParse.Spec.VCList.nlist (U64.v n0) Cbor.raw_data_item))
  (l0: LPS.byte_array)
  (#va0: Ghost.erased (Seq.seq cbor))
  (a0: A.array cbor)
: STT (Ghost.erased (Seq.seq cbor))
    (A.pts_to a0 full_perm va0 `star`
      LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0
    )
    (fun res ->
      A.pts_to a0 full_perm res `star`
      raw_data_item_array_match res vl0.contents `star`
      (raw_data_item_array_match res vl0.contents `implies_`
        LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v n0) Cbor.parse_raw_data_item) l0 vl0
      )
    )

[@@__reduce__]
let read_cbor_array_post_success
  (c: cbor_array)
: Tot vprop
= exists_ (A.pts_to c.payload full_perm) `star`
  pure (
    A.is_full_array c.payload
  )

let read_cbor_array_post
  (input: cbor)
  (res: cbor)
: Tot vprop
= if CBOR_Case_Serialized? input && CBOR_Case_Array? res
  then read_cbor_array_post_success (CBOR_Case_Array?._0 res)
  else emp

inline_for_extraction
noextract
let read_cbor_array_noop
  (#obj: Ghost.erased Cbor.raw_data_item)
  (input: cbor)
: STT cbor
    (raw_data_item_match input obj)
    (fun res ->
      raw_data_item_match res obj `star`
      (raw_data_item_match res obj `implies_`
        (raw_data_item_match input obj `star` read_cbor_array_post input res)
      )
    )
= implies_with_tactic (raw_data_item_match input obj) (raw_data_item_match input obj);
  rewrite emp (read_cbor_array_post input input);
  implies_concl_r (raw_data_item_match input obj) (raw_data_item_match input obj) (read_cbor_array_post input input);
  return input

let array_pts_to_or_null
  (#t: Type)
  (a: A.array t)
  (v: Seq.seq t)
: Tot vprop
= if A.is_null a
  then emp
  else A.pts_to a full_perm v

inline_for_extraction
noextract
let array_alloc
  (#t: Type)
  (init: t)
  (n: SZ.t)
: ST (A.array t)
    emp
    (fun res -> array_pts_to_or_null res (Seq.create (SZ.v n) init))
    True
    (fun res ->
      if A.is_null res
      then True
      else A.length res == SZ.v n /\ A.is_full_array res
    )
= let res = A.alloc init n in
  A.pts_to_not_null res _;
  rewrite
    (A.pts_to res full_perm (Seq.create (SZ.v n) init))
    (array_pts_to_or_null res (Seq.create (SZ.v n) init));
  return res

let read_cbor_array
  (#obj: Ghost.erased Cbor.raw_data_item)
  (input: cbor)
: ST cbor
    (raw_data_item_match input obj)
    (fun res ->
      raw_data_item_match res obj `star`
      (raw_data_item_match res obj `implies_`
        (raw_data_item_match input obj `star` read_cbor_array_post input res)
      )
    )
    (Cbor.Array? obj)
    (fun _ -> True)
= raw_data_item_match_get_case input;
  match input with
  | CBOR_Case_Array _ -> read_cbor_array_noop input
  | CBOR_Case_Serialized s ->
      rewrite_with_implies
        (raw_data_item_match input obj)
        (raw_data_item_match_serialized0 input obj);
      let _ = gen_elim () in
      vpattern_rewrite_with_implies
        (fun a -> LPS.aparse Cbor.parse_raw_data_item a _)
        s.payload;
      intro_implies
        (LPS.aparse Cbor.parse_raw_data_item s.payload _)
        (raw_data_item_match_serialized0 input obj)
        (LPS.aparse Cbor.parse_raw_data_item s.payload _ `implies_`
          LPS.aparse Cbor.parse_raw_data_item _ _
        )
        (fun _ ->
          elim_implies
            (LPS.aparse Cbor.parse_raw_data_item s.payload _)
            (LPS.aparse Cbor.parse_raw_data_item _ _);
          noop ()
        );
      implies_trans
        (LPS.aparse Cbor.parse_raw_data_item s.payload _)
        (raw_data_item_match_serialized0 input obj)
        (raw_data_item_match input obj);
      R.with_local 0uL (fun plen ->
      R.with_local s.payload (fun pa ->
        let w = CBOR.SteelST.Array.focus_array plen pa s.payload in
        implies_trans
          (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.a _)
          (LPS.aparse Cbor.parse_raw_data_item s.payload _)
          (raw_data_item_match input obj);
        let len = R.read plen in
        let _ = A.intro_fits_u64 () in
        let a0 = array_alloc dummy_cbor (SZ.uint64_to_sizet len) in
        if (A.is_null a0)
        then begin
          noop ();
          rewrite
            (array_pts_to_or_null a0 _)
            emp;
          elim_implies
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.a _)
            (raw_data_item_match input obj);
          let res = read_cbor_array_noop input in
          return res
        end else begin
          noop ();
          rewrite
            (array_pts_to_or_null a0 _)
            (A.pts_to a0 full_perm (Seq.create (U64.v len) dummy_cbor));
          let vl = LPS.rewrite_aparse_with_implies
            w.a
            (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item)
          in
          let a = R.read pa in
          vpattern_rewrite_with_implies
            (fun a -> LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            a;
          implies_trans
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) _ _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) _ _);
          implies_trans
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) _ _)
            (raw_data_item_match input obj);
          let va = read_cbor_array_payload len vl a a0 in
          implies_trans
            (raw_data_item_array_match va vl.contents)
            (LPS.aparse (LowParse.Spec.VCList.parse_nlist (U64.v len) Cbor.parse_raw_data_item) a _)
            (raw_data_item_match input obj);
          let res = constr_cbor_array a0 len in
          vpattern_rewrite
            (fun ar -> raw_data_item_match _ ar `star` (raw_data_item_match _ ar `implies_` (A.pts_to _ _ _ `star` raw_data_item_array_match _ _)))
            obj;
          intro_implies
            (A.pts_to a0 full_perm va `star` raw_data_item_array_match va vl.contents)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res)
            emp
            (fun _ ->
              vpattern_rewrite (fun a0 -> A.pts_to a0 _ _) (CBOR_Case_Array?._0 res).payload;
              rewrite (read_cbor_array_post_success (CBOR_Case_Array?._0 res)) (read_cbor_array_post input res)
            );
          implies_reg_r
            (raw_data_item_array_match va vl.contents)
            (raw_data_item_match input obj)
            (read_cbor_array_post input res);
          implies_trans
            (raw_data_item_match res obj)
            (A.pts_to a0 full_perm va `star` raw_data_item_array_match va vl.contents)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res);
          implies_trans
            (raw_data_item_match res obj)
            (raw_data_item_array_match va vl.contents `star` read_cbor_array_post input res)
            (raw_data_item_match input obj `star` read_cbor_array_post input res);
          return res
        end
      ))

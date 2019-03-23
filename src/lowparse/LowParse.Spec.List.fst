module LowParse.Spec.List
include LowParse.Spec.Combinators // for seq_slice_append_l

module Seq = FStar.Seq
module L = FStar.List.Tot
module U32 = FStar.UInt32
module Classical = FStar.Classical

(* Parse a list, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size. *)

val parse_list_aux
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: GTot (option (list t * (consumed_length b)))
  (decreases (Seq.length b))

let rec parse_list_aux #k #t p b =
  if Seq.length b = 0
  then 
    Some ([], (0 <: consumed_length b))
  else
    match parse p b with
    | None -> None
    | Some (v, n) ->
      if n = 0
      then None (* elements cannot be empty *)
      else
        match parse_list_aux p (Seq.slice b n (Seq.length b)) with
	| Some (l, n') -> Some (v :: l, (n + n' <: consumed_length b))
	| _ -> None

val parse_list_bare
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (bare_parser (list t))

let parse_list_bare #k #t p = (fun b -> parse_list_aux #k #t p b) <: bare_parser (list t)

let rec parse_list_bare_consumed
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma
  (requires (Some? (parse_list_bare p b)))
  (ensures (
    let pb = parse_list_bare p b in (
    Some? pb /\ (
    let (Some (_, consumed)) = pb in
    consumed == Seq.length b
  ))))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then ()
  else
    let (Some (_, consumed1)) = p b in
    let b' = Seq.slice b consumed1 (Seq.length b) in
    parse_list_bare_consumed p b'

let parse_list_bare_consumes_all
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Lemma
  (consumes_all (parse_list_bare p))
= Classical.forall_intro (Classical.move_requires (parse_list_bare_consumed p))

#set-options "--z3rlimit 16"

let parse_list_bare_injective
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Lemma
  (ensures (injective (parse_list_bare p)))
= parser_kind_prop_equiv k p;
  let f () : Lemma
    (injective p)
  = ()
  in
  let rec aux
    (b1: bytes)
    (b2: bytes)
  : Lemma
    (requires (injective_precond (parse_list_bare p) b1 b2))
    (ensures (injective_postcond (parse_list_bare p) b1 b2))
    (decreases (Seq.length b1 + Seq.length b2))
  = if Seq.length b1 = 0
    then begin
      () // assert (Seq.equal b1 b2)
    end else begin
      assert (injective_precond p b1 b2);
      f ();
      assert (injective_postcond p b1 b2);
      let (Some (_, len1)) = parse p b1 in
      let (Some (_, len2)) = parse p b2 in
      assert ((len1 <: nat) == (len2 <: nat));
      let b1' : bytes = Seq.slice b1 len1 (Seq.length b1) in
      let b2' : bytes = Seq.slice b2 len2 (Seq.length b2) in
      aux b1' b2';
      let (Some (_, len1')) = parse (parse_list_bare p) b1' in
      let (Some (_, len2')) = parse (parse_list_bare p) b2' in
      Seq.lemma_split (Seq.slice b1 0 (len1 + len1')) len1;
      Seq.lemma_split (Seq.slice b2 0 (len2 + len2')) len2;
      assert (injective_postcond (parse_list_bare p) b1 b2)
    end
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (aux b))

#reset-options

inline_for_extraction
let parse_list_kind =
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_metadata = None;
    parser_kind_subkind = Some ParserConsumesAll;
  }

abstract
val parse_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser parse_list_kind (list t))

let parse_list #k #t p =
  parse_list_bare_injective p;
  parse_list_bare_consumes_all p;
  parser_kind_prop_equiv parse_list_kind (parse_list_bare p);
  parse_list_bare p

abstract
let parse_list_eq
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma
  (parse (parse_list p) b == (
    if Seq.length b = 0
    then 
      Some ([], (0 <: consumed_length b))
    else
      match parse p b with
      | None -> None
      | Some (v, n) ->
        if n = 0
        then None (* elements cannot be empty *)
        else
          match parse (parse_list p) (Seq.slice b n (Seq.length b)) with
	  | Some (l, n') -> Some (v :: l, (n + n' <: consumed_length b))
	  | _ -> None
  ))
= ()

abstract
let parse_list_eq'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma
  (requires (k.parser_kind_low > 0))
  (ensures (parse (parse_list p) b == (
    if Seq.length b = 0
    then 
      Some ([], (0 <: consumed_length b))
    else
      match parse p b with
      | None -> None
      | Some (v, n) ->
        begin match parse (parse_list p) (Seq.slice b n (Seq.length b)) with
	  | Some (l, n') -> Some (v :: l, (n + n' <: consumed_length b))
	  | _ -> None
        end
  )))
= ()

let rec bare_serialize_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
  (x: list t)
: GTot bytes
= match x with
  | [] -> Seq.empty
  | a :: q -> Seq.append (s a) (bare_serialize_list p s q)

unfold
let serialize_list_precond
  (k: parser_kind)
: GTot bool
= k.parser_kind_subkind = Some ParserStrong &&
  k.parser_kind_low > 0

let bare_serialize_list_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serializer_correct (parse_list p) (bare_serialize_list p s)))
= parser_kind_prop_equiv k p;
  let f () : Lemma (serialize_list_precond k) = () in
  let rec prf
    (l: list t)
  : Lemma
    (parse (parse_list p) (bare_serialize_list p s l) == Some (l, Seq.length (bare_serialize_list p s l)))
  = match l with
    | [] -> ()
    | a :: q ->
      let pa = parse p (bare_serialize_list p s l) in
      f ();
      parser_kind_prop_equiv k p;
      assert (no_lookahead_on p (serialize s a) (bare_serialize_list p s l));
      seq_slice_append_l (serialize s a) (bare_serialize_list p s q);
      assert (no_lookahead_on_precond p (serialize s a) (bare_serialize_list p s l));
      assert (no_lookahead_on_postcond p (serialize s a) (bare_serialize_list p s l));
      assert (Some? pa);
      assert (injective_precond p (serialize s a) (bare_serialize_list p s l));
      assert (injective_postcond p (serialize s a) (bare_serialize_list p s l));
      let (Some (a', lena)) = pa in
      assert (a == a');
      assert (lena == Seq.length (serialize s a));
      assert (lena > 0);
      prf q;
      seq_slice_append_r (serialize s a) (bare_serialize_list p s q)
  in
  Classical.forall_intro prf

abstract
let serialize_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
: Pure (serializer (parse_list p))
  (requires (
    serialize_list_precond k
  ))
  (ensures (fun _ -> True))
= bare_serialize_list_correct p s;
  bare_serialize_list p s

abstract
let serialize_list_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
: Lemma
  (requires (
    serialize_list_precond k
  ))
  (ensures (serialize (serialize_list p s) [] == Seq.empty))
= ()

abstract
let serialize_list_cons
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
  (a: t)
  (q: list t)
: Lemma
  (requires (
    serialize_list_precond k
  ))
  (ensures (
    serialize (serialize_list p s) (a :: q) == Seq.append (serialize s a) (serialize (serialize_list p s) q)
  ))
= ()

abstract
let serialize_list_singleton
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
  (a: t)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serialize (serialize_list p s) [a] == serialize s a))
= Seq.append_empty_r (serialize s a)

abstract
let rec serialize_list_append
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
  (l1 l2: list t)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serialize (serialize_list p s) (L.append l1 l2) == Seq.append (serialize (serialize_list p s) l1) (serialize (serialize_list p s) l2)))
= match l1 with
  | a :: q ->
    serialize_list_append p s q l2;
    Seq.append_assoc (serialize s a) (serialize (serialize_list p s) q) (serialize (serialize_list p s) l2)
  | [] ->
    Seq.append_empty_l (serialize (serialize_list p s) l2)

abstract
let serialize_list_cons_upd
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
  (l2: list t)
  (y: t)
: Lemma
  (requires (
    serialize_list_precond k /\
    Seq.length (serialize s y) == Seq.length (serialize s x)
  ))
  (ensures (
    let ln2 = Seq.length (serialize (serialize_list _ s) l2) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (x :: l2) in
    Seq.length sl == Seq.length sx + ln2 /\
    serialize (serialize_list _ s) (y :: l2) == seq_upd_seq sl 0 (serialize s y)
  ))
= serialize_list_cons _ s x l2;
  serialize_list_cons _ s y l2;
  let sl = serialize (serialize_list _ s) (x :: l2) in
  seq_upd_seq_left sl (serialize s y);
  let ln = Seq.length (serialize s x) in
  Seq.lemma_split sl ln;
  Seq.lemma_append_inj (Seq.slice sl 0 ln) (Seq.slice sl ln (Seq.length sl)) (serialize s x) (serialize (serialize_list _ s) l2)

#set-options "--z3rlimit 32"

abstract
let serialize_list_upd
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (l1: list t)
  (x: t)
  (l2: list t)
  (y: t)
: Lemma
  (requires (
    serialize_list_precond k /\
    Seq.length (serialize s y) == Seq.length (serialize s x)
  ))
  (ensures (
    let ln1 = Seq.length (serialize (serialize_list _ s) l1) in
    let ln2 = Seq.length (serialize (serialize_list _ s) l2) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (l1 `L.append` (x :: l2)) in
    Seq.length sl == ln1 + Seq.length sx + ln2 /\
    serialize (serialize_list _ s) (l1 `L.append` (y :: l2)) == seq_upd_seq sl ln1 (serialize s y)
  ))
  (decreases (L.length l1))
= serialize_list_append _ s l1 (y :: l2);
  assert (serialize (serialize_list _ s) (l1 `L.append` (y :: l2)) == serialize (serialize_list _ s) l1 `Seq.append` serialize (serialize_list _ s) (y :: l2));
  serialize_list_cons_upd s x l2 y;
  assert (serialize (serialize_list _ s) (l1 `L.append` (y :: l2)) == serialize (serialize_list _ s) l1 `Seq.append` seq_upd_seq (serialize (serialize_list _ s) (x :: l2)) 0 (serialize s y));
  seq_append_seq_upd_seq_l (serialize (serialize_list _ s) (x :: l2)) 0 (serialize s y) (serialize (serialize_list _ s) l1);
  assert (serialize (serialize_list _ s) (l1 `L.append` (y :: l2)) == seq_upd_seq (serialize (serialize_list _ s) l1 `Seq.append` serialize (serialize_list _ s) (x :: l2)) (Seq.length (serialize (serialize_list _ s) l1) + 0) (serialize s y));
  serialize_list_append _ s l1 (x :: l2)

abstract
let serialize_list_upd_bw
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (l1: list t)
  (x: t)
  (l2: list t)
  (y: t)
: Lemma
  (requires (
    serialize_list_precond k /\
    Seq.length (serialize s y) == Seq.length (serialize s x)
  ))
  (ensures (
    let ln1 = Seq.length (serialize (serialize_list _ s) l1) in
    let ln2 = Seq.length (serialize (serialize_list _ s) l2) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (l1 `L.append` (x :: l2)) in
    Seq.length sl == ln1 + Seq.length sx + ln2 /\
    serialize (serialize_list _ s) (l1 `L.append` (y :: l2)) == seq_upd_bw_seq sl ln2 (serialize s y)
  ))
  (decreases (L.length l1))
= serialize_list_upd s l1 x l2 y

#set-options "--z3rlimit 64"

abstract
let serialize_list_upd_chain
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (l1: list t)
  (x: t)
  (l2: list t)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    serialize_list_precond k /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_seq sx i' s'
  ))
  (ensures (
    let ln1 = Seq.length (serialize (serialize_list _ s) l1) in
    let ln2 = Seq.length (serialize (serialize_list _ s) l2) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (l1 `L.append` (x :: l2)) in
    Seq.length sl == ln1 + Seq.length sx + ln2 /\
    ln1 + i' + Seq.length s' <= Seq.length sl /\
    serialize (serialize_list _ s) (l1 `L.append` (y :: l2)) == seq_upd_seq sl (ln1 + i') s'
  ))
= serialize_list_upd s l1 x l2 y;
  serialize_list_append _ s l1 (x :: l2);
  let sl1 = serialize (serialize_list _ s) l1 in
  let ln1 = Seq.length sl1 in
  let sxl2 = serialize (serialize_list _ s) (x :: l2) in
  let sl = serialize (serialize_list _ s) (l1 `L.append` (x :: l2)) in
  Seq.lemma_split sl ln1;
  Seq.lemma_append_inj (Seq.slice sl 0 ln1) (Seq.slice sl ln1 (Seq.length sl)) sl1 sxl2;
  let sx = serialize s x in
  let sl2 = serialize (serialize_list _ s) l2 in
  let lx = Seq.length sx in
  serialize_list_cons _ s x l2;
  Seq.lemma_split sxl2 lx;
  Seq.lemma_append_inj (Seq.slice sxl2 0 lx) (Seq.slice sxl2 lx (Seq.length sxl2)) sx sl2;
  Seq.slice_slice sl ln1 (Seq.length sl) 0 lx;
  assert (sx == Seq.slice sl ln1 (ln1 + lx));
  seq_upd_seq_seq_upd_seq_slice sl ln1 (ln1 + lx) i' s';
  ()

abstract
let serialize_list_upd_bw_chain
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (l1: list t)
  (x: t)
  (l2: list t)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    serialize_list_precond k /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_bw_seq sx i' s'
  ))
  (ensures (
    let ln1 = Seq.length (serialize (serialize_list _ s) l1) in
    let ln2 = Seq.length (serialize (serialize_list _ s) l2) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (l1 `L.append` (x :: l2)) in
    Seq.length sl == ln1 + Seq.length sx + ln2 /\
    ln2 + i' + Seq.length s' <= Seq.length sl /\
    serialize (serialize_list _ s) (l1 `L.append` (y :: l2)) == seq_upd_bw_seq sl (ln2 + i') s'
  ))
= let sx = serialize s x in
  let j' = Seq.length sx - i' - Seq.length s' in
  serialize_list_upd_chain s l1 x l2 y j' s'

abstract
let serialize_list_cons_upd_chain
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
  (l2: list t)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    serialize_list_precond k /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_seq sx i' s'
  ))
  (ensures (
    let ln2 = Seq.length (serialize (serialize_list _ s) l2) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (x :: l2) in
    Seq.length sl == Seq.length sx + ln2 /\
    i' + Seq.length s' <= Seq.length sl /\
    serialize (serialize_list _ s) (y :: l2) == seq_upd_seq sl i' s'
  ))
= serialize_list_upd_chain s [] x l2 y i' s'

abstract
let serialize_list_cons_upd_bw_chain
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
  (l2: list t)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    serialize_list_precond k /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_bw_seq sx i' s'
  ))
  (ensures (
    let ln2 = Seq.length (serialize (serialize_list _ s) l2) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (x :: l2) in
    Seq.length sl == Seq.length sx + ln2 /\
    ln2 + i' + Seq.length s' <= Seq.length sl /\
    serialize (serialize_list _ s) (y :: l2) == seq_upd_bw_seq sl (ln2 + i') s'
  ))
= let j' = Seq.length (serialize s x) - i' - Seq.length s' in
  serialize_list_cons_upd_chain s x l2 y j' s'

abstract
let serialize_list_snoc_upd_chain
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (l1: list t)
  (x: t)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    serialize_list_precond k /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_seq sx i' s'
  ))
  (ensures (
    let ln1 = Seq.length (serialize (serialize_list _ s) l1) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (l1 `L.append` [x]) in
    Seq.length sl == ln1 + Seq.length sx /\
    ln1 + i' + Seq.length s' <= Seq.length sl /\
    serialize (serialize_list _ s) (l1 `L.append` [y]) == seq_upd_seq sl (ln1 + i') s'
  ))
= serialize_list_upd_chain s l1 x [] y i' s'

abstract
let serialize_list_snoc_upd_bw_chain
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (l1: list t)
  (x: t)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    serialize_list_precond k /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_bw_seq sx i' s'
  ))
  (ensures (
    let ln1 = Seq.length (serialize (serialize_list _ s) l1) in
    let sx = serialize s x in
    let sl = serialize (serialize_list _ s) (l1 `L.append` [x]) in
    Seq.length sl == ln1 + Seq.length sx /\
    i' + Seq.length s' <= Seq.length sl /\
    serialize (serialize_list _ s) (l1 `L.append` [y]) == seq_upd_bw_seq sl i' s'
  ))
= let j' = Seq.length (serialize s x) - i' - Seq.length s' in
  serialize_list_snoc_upd_chain s l1 x y j' s'

#reset-options

abstract
val list_length_constant_size_parser_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    Some? (parse (parse_list p) b)
  ))
  (ensures (
    let pb = parse (parse_list p) b in
    Some? pb /\ (
    let (Some (l, _)) = pb in
    FStar.Mul.op_Star (L.length l) k.parser_kind_low == Seq.length b
  )))
  (decreases (Seq.length b))

let rec list_length_constant_size_parser_correct #k #t p b =
  parser_kind_prop_equiv k p;
  let n = k.parser_kind_low in
  if Seq.length b = 0
  then ()
  else begin
    let (Some (_, consumed)) = parse p b in
    assert ((consumed <: nat) == n);
    assert (n > 0);
    let b' : bytes = Seq.slice b n (Seq.length b) in
    list_length_constant_size_parser_correct p b';
    let (Some (l', _)) = parse (parse_list p) b' in
    FStar.Math.Lemmas.distributivity_add_left 1 (L.length l') n
  end

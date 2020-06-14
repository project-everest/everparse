module LowParse.Spec.List
include LowParse.Spec.Combinators // for seq_slice_append_l

module Seq = FStar.Seq
module L = FStar.List.Tot
module U32 = FStar.UInt32
module Classical = FStar.Classical

(* Parse a list, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size. *)

let parse_list #k #t p =
  parse_list_bare_injective p;
  parse_list_bare_consumes_all p;
  parser_kind_prop_equiv parse_list_kind (parse_list_bare p);
  parse_list_bare p

let parse_list_eq
  (#k: parser_kind)
  (#t: Type)
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

let parse_list_eq'
  (#k: parser_kind)
  (#t: Type)
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

let bare_serialize_list_correct
  (#k: parser_kind)
  (#t: Type)
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

let serialize_list
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s: serializer p)
: Pure (serializer (parse_list p))
  (requires (
    serialize_list_precond k
  ))
  (ensures (fun _ -> True))
= bare_serialize_list_correct p s;
  bare_serialize_list p s

let serialize_list_nil
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s: serializer p)
: Lemma
  (requires (
    serialize_list_precond k
  ))
  (ensures (serialize (serialize_list p s) [] == Seq.empty))
= ()

let serialize_list_cons
  (#k: parser_kind)
  (#t: Type)
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

let serialize_list_singleton
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s: serializer p)
  (a: t)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serialize (serialize_list p s) [a] == serialize s a))
= Seq.append_empty_r (serialize s a)

let rec serialize_list_append
  (#k: parser_kind)
  (#t: Type)
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


#set-options "--z3rlimit 64"

let serialize_list_cons_upd_chain
  (#k: parser_kind)
  (#t: Type)
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

let serialize_list_snoc_upd_chain
  (#k: parser_kind)
  (#t: Type)
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


#reset-options

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

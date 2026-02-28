(* Variable-count lists *)

module LowParse.Spec.VCList
include LowParse.Spec.Combinators // for seq_slice_append_l
include LowParse.Spec.Array // for vlarray

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Classical = FStar.Classical
module L = FStar.List.Tot

inline_for_extraction
type nlist (n: nat) (t: Type) = (l: list t { L.length l == n } )

// abstract
inline_for_extraction
let nlist_nil (#t: Type) : Tot (nlist 0 t) = []

// abstract
let nlist_nil_unique (t: Type) (l: nlist 0 t) : Lemma (l == nlist_nil) = ()

// abstract
inline_for_extraction
let nlist_cons (#t: Type) (#n: nat) (a: t) (q: nlist n t) : Tot (nlist (n + 1) t) =
  a :: q

// abstract
inline_for_extraction
let nlist_destruct (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Tot (t * nlist n t) =
  match x with (a :: q) -> a, q

// abstract
let nlist_cons_unique (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Lemma
  (let (a, q) = nlist_destruct x in x == nlist_cons a q)
= ()

unfold let mul = Prims.op_Multiply

inline_for_extraction
let synth_nlist (#t: Type) (n: nat) (xy: t * nlist n t) : Tot (nlist (n + 1) t) =
  match xy with (x, y) ->
  nlist_cons x y

inline_for_extraction
let synth_nlist_recip (#t: Type) (n: nat) (xy: nlist (n + 1) t) : Tot (t * nlist n t) =
  nlist_destruct xy

// abstract
let synth_inverse_1 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist #t n) (synth_nlist_recip n))
= ()

// abstract
let synth_inverse_2 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist_recip #t n) (synth_nlist n))
= ()

let rec parse_nlist_kind'
  (n: nat)
  (k: parser_kind)
: GTot parser_kind
  (decreases n)
= if n = 0
  then parse_ret_kind
  else k `and_then_kind` parse_nlist_kind' (n - 1) k

let rec parse_nlist_kind_low
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_low == n `mul` k.parser_kind_low)
= if n = 0
  then ()
  else begin
    LowParse.Math.distributivity_add_left (n - 1) 1 k.parser_kind_low;
    parse_nlist_kind_low (n - 1) k
  end

let rec parse_nlist_kind_high
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_high == (match k.parser_kind_high with
    | None -> if n = 0 then Some 0 else None
    | Some b -> Some (n `mul` b)
  ))
= if n = 0
  then ()
  else begin
    begin match k.parser_kind_high with
    | None -> ()
    | Some b -> LowParse.Math.distributivity_add_left (n - 1) 1 b
    end;
    parse_nlist_kind_high (n - 1) k
  end

let rec parse_nlist_kind_metadata
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_metadata == (if n = 0 then Some ParserKindMetadataTotal else k.parser_kind_metadata))
= if n = 0
  then ()
  else parse_nlist_kind_metadata (n - 1) k

let rec parse_nlist_kind_subkind
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_subkind == (
    if n = 0 then Some ParserStrong else k.parser_kind_subkind
  ))
= if n = 0
  then ()
  else parse_nlist_kind_subkind (n - 1) k

let rec parse_nlist_kind_injective
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind' n k).parser_kind_injective == (
    if n = 0 then true else k.parser_kind_injective
  ))
= if n = 0
  then ()
  else parse_nlist_kind_injective (n - 1) k

inline_for_extraction
let parse_nlist_kind
  (n: nat)
  (k: parser_kind)
: Pure parser_kind
    (requires True)
    (ensures (fun k' -> k' == parse_nlist_kind' n k))
= [@inline_let] let _ =
    parse_nlist_kind_low n k;
    parse_nlist_kind_high n k;
    parse_nlist_kind_metadata n k;
    parse_nlist_kind_subkind n k;
    parse_nlist_kind_injective n k
  in
  {
    parser_kind_low = n `mul` k.parser_kind_low;
    parser_kind_high = (match k.parser_kind_high with
    | None -> if n = 0 then Some 0 else None
    | Some b -> Some (n `mul` b)
    );
    parser_kind_metadata = (if n = 0 then Some ParserKindMetadataTotal else k.parser_kind_metadata);
    parser_kind_subkind = (if n = 0 then Some ParserStrong else k.parser_kind_subkind);
    parser_kind_injective = (if n = 0 then true else k.parser_kind_injective);
  }


let rec tot_parse_nlist'
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
: Tot (tot_parser (parse_nlist_kind n k) (nlist n t))
= if n = 0
  then tot_parse_ret nlist_nil
  else begin
    [@inline_let] let _ = assert (parse_nlist_kind n k == parse_nlist_kind' n k) in
    tot_parse_synth
      (p `tot_nondep_then` tot_parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
  end

val tot_parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
: Pure (tot_parser (parse_nlist_kind n k) (nlist n t))
    (requires True)
    (ensures (fun y -> y == tot_parse_nlist' n p))

let tot_parse_nlist_eq
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
  (b: bytes)
: Lemma (
  parse (tot_parse_nlist n p) b == (
    if n = 0
    then Some ([], 0)
    else match parse p b with
    | Some (elem, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      begin match parse (tot_parse_nlist (n - 1) p) b' with
      | Some (q, consumed') -> Some (elem :: q, consumed + consumed')
      | _ -> None
      end
    | _ -> None
  ))
= if n = 0
  then ()
  else begin
    tot_parse_synth_eq
      (p `tot_nondep_then` tot_parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
      b;
    nondep_then_eq #k p #(parse_nlist_kind (n - 1) k) (tot_parse_nlist' (n - 1) p) b
  end

let rec parse_nlist'
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_nlist_kind n k) (nlist n t))
= if n = 0
  then parse_ret nlist_nil
  else begin
    [@inline_let] let _ = assert (parse_nlist_kind n k == parse_nlist_kind' n k) in
    parse_synth
      (p `nondep_then` parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
  end

val parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Pure (parser (parse_nlist_kind n k) (nlist n t))
    (requires True)
    (ensures (fun y -> y == parse_nlist' n p))

let parse_nlist_eq
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma (
  parse (parse_nlist n p) b == (
    if n = 0
    then Some ([], 0)
    else match parse p b with
    | Some (elem, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      begin match parse (parse_nlist (n - 1) p) b' with
      | Some (q, consumed') -> Some (elem :: q, consumed + consumed')
      | _ -> None
      end
    | _ -> None
  ))
= if n = 0
  then ()
  else begin
    parse_synth_eq
      (p `nondep_then` parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
      b;
    nondep_then_eq p (parse_nlist' (n - 1) p) b
  end

let rec tot_parse_nlist_parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
  (b: bytes)
: Lemma
  (ensures (tot_parse_nlist n p b == parse_nlist n #k p b))
  (decreases n)
= tot_parse_nlist_eq n p b;
  parse_nlist_eq n #k p b;
  if n = 0
  then ()
  else Classical.forall_intro (tot_parse_nlist_parse_nlist (n - 1) p)

let rec parse_nlist_ext
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: (parser k t))
  (#k': parser_kind)
  (p' : parser k' t)
  (b: bytes)
  (prf: (
    (b': bytes { Seq.length b' <= Seq.length b }) ->
    Lemma
    (parse p b' == parse p' b')
  ))
: Lemma
  (ensures (parse (parse_nlist n p) b == parse (parse_nlist n p') b))
  (decreases n)
= parse_nlist_eq n p b;
  parse_nlist_eq n p' b;
  if n = 0
  then ()
  else begin
    prf b;
    match parse p b with
    | None -> ()
    | Some (_, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      parse_nlist_ext (n - 1) p p' b' prf
  end

val parse_nlist_ext_forall
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: (parser k t))
  (#k': parser_kind)
  (p' : parser k' t)
: Lemma
  (requires
    forall b . parse p b == parse p' b
  )
  (ensures
    forall b . parse (parse_nlist n p) b == parse (parse_nlist n p') b
  )

let parse_nlist_fuel_ext
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: (nat -> parser k t))
  (fuel: nat)
  (fuel': nat { fuel <= fuel' })
  (prf: (
    (b: bytes { Seq.length b < fuel }) ->
    Lemma
    (parse (p fuel) b == parse (p fuel') b)
  ))
  (b: bytes { Seq.length b < fuel })
: Lemma
  (ensures (parse (parse_nlist n (p fuel)) b == parse (parse_nlist n (p fuel')) b))
= parse_nlist_ext n (p fuel) (p fuel') b prf

let parse_nlist_zero
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma (
  parse (parse_nlist 0 p) b == Some ([], 0)
)
= parse_nlist_eq 0 p b

let parse_nlist_one
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma (
  parse (parse_nlist 1 p) b == (match parse p b with
  | None -> None
  | Some (x, consumed) -> Some ([x], consumed)
  )
)
= parse_nlist_eq 1 p b

val parse_nlist_sum
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n1 n2: nat)
  (b: bytes)
: Lemma
  (ensures (parse (parse_nlist (n1 + n2) p) b ==
    begin match parse (parse_nlist n1 p) b with
    | None -> None
    | Some (l1, consumed1) ->
      let b2 = Seq.slice b consumed1 (Seq.length b) in
      match parse (parse_nlist n2 p) b2 with
      | None -> None
      | Some (l2, consumed2) ->
        List.Tot.append_length l1 l2;
        Some (l1 `List.Tot.append` l2, consumed1 + consumed2)
    end
  ))

val parse_nlist_parse_list
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: nat)
  (b: bytes)
: Lemma
  (requires (
    Some? (parse (parse_nlist n p) b) /\
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0
  ))
  (ensures (
    match parse (parse_nlist n p) b with
    | Some (l, consumed) ->
      let b' = Seq.slice b 0 consumed in
      parse (parse_list p) b' == Some (l, consumed)
    | _ -> False
  ))

val parse_nlist_parse_list_full
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: nat)
  (b: bytes)
: Lemma
  (requires (
    Some? (parse (parse_nlist n p) b) /\
    (let Some (_, consumed) = parse (parse_nlist n p) b in consumed == Seq.length b) /\
    k.parser_kind_low > 0
  ))
  (ensures (
    match parse (parse_nlist n p) b with
    | Some (l, consumed) ->
      parse (parse_list p) b == Some (l, consumed)
    | _ -> False
  ))

val parse_list_parse_nlist
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_list p) b)))
  (ensures (
    match parse (parse_list p) b with
    | Some (l, consumed) ->
      parse (parse_nlist (List.Tot.length l) p) b == Some (l, consumed)
    | _ -> False
  ))

let empty_to_nlist
  (t: Type)
  (_: unit)
: Tot (nlist 0 t)
= []

let empty_to_nlist_recip
  (t: Type)
  (_: nlist 0 t)
: Tot unit
= ()

let parse_nlist_nil_as_synth_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (forall b . parse (parse_nlist 0 p) b == parse (parse_synth parse_empty (empty_to_nlist t)) b)
= let prf
    (b: bytes)
  : Lemma
    (parse (parse_nlist 0 p) b == parse (parse_synth parse_empty (empty_to_nlist t)) b)
  = parse_nlist_eq 0 p b;
    parse_synth_eq parse_empty (empty_to_nlist t) b
  in
  Classical.forall_intro prf

let parse_nlist_cons_as_synth_eq
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (forall b . parse (parse_nlist (n + 1) p) b == parse (parse_synth (nondep_then p (parse_nlist n p)) (synth_nlist n)) b)
= ()

let singleton_to_nlist
  (#t: Type)
  (x: t)
: Tot (nlist 1 t)
= [x]

let singleton_to_nlist_recip
  (#t: Type)
  (l: nlist 1 t)
: Tot t
= List.Tot.hd l

let parse_nlist_singleton_as_synth_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (forall b . parse (parse_nlist 1 p) b == parse (parse_synth p singleton_to_nlist) b)
= let prf
    (b: bytes)
  : Lemma
    (parse (parse_nlist 1 p) b == parse (parse_synth p singleton_to_nlist) b)
  = parse_nlist_eq 1 p b;
    parse_synth_eq p singleton_to_nlist b
  in
  Classical.forall_intro prf

let pair_to_nlist
  (t: Type)
  (x: (t & t))
: Tot (nlist 2 t)
= [fst x; snd x]

let pair_to_nlist_recip
  (t: Type)
  (x: nlist 2 t)
: Tot (t & t)
= let [y; z] = x in (y, z)

let parse_nlist_pair_as_synth_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (forall b . parse (parse_nlist 2 p) b == parse (parse_synth (nondep_then p p) (pair_to_nlist t)) b)
= let prf
    (b: bytes)
  : Lemma
    (parse (parse_nlist 2 p) b == parse (parse_synth (nondep_then p p) (pair_to_nlist t)) b)
  = parse_nlist_eq 2 p b;
    Classical.forall_intro (parse_nlist_eq 1 p);
    parse_synth_eq (nondep_then p p) (pair_to_nlist _) b;
    nondep_then_eq p p b
  in
  Classical.forall_intro prf

let rec serialize_nlist'
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (serializer (parse_nlist n p))
= if n = 0
  then begin
    Classical.forall_intro (nlist_nil_unique t);
    (fun _ -> Seq.empty)
  end
  else begin
    synth_inverse_1 t (n - 1);
    synth_inverse_2 t (n - 1);
    serialize_synth _ (synth_nlist (n - 1)) (serialize_nondep_then s (serialize_nlist' (n - 1) s)) (synth_nlist_recip (n - 1)) ()
  end

val serialize_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (y: serializer (parse_nlist n p) { y == serialize_nlist' n s })

let serialize_nlist_nil
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Lemma
  (ensures (serialize (serialize_nlist 0 s) [] == Seq.empty))
= ()

let serialize_nlist_cons
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (a: t)
  (q: nlist n t)
: Lemma
  (ensures (
    serialize (serialize_nlist (n + 1) s) (a :: q) == Seq.append (serialize s a) (serialize (serialize_nlist n s) q)
  ))
= serialize_synth_eq _ (synth_nlist n) (serialize_nondep_then s (serialize_nlist' n s)) (synth_nlist_recip n) () (a :: q);
  serialize_nondep_then_eq s (serialize_nlist' n s) (a, q)

let rec serialize_nlist_serialize_list
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (#p: parser k t)
  (s: serializer p { serialize_list_precond k } )
  (l: nlist n t)
: Lemma
  (serialize (serialize_nlist n s) l == serialize (serialize_list _ s) l)
= if n = 0
  then begin
    serialize_nlist_nil p s;
    serialize_list_nil p s
  end else begin
    let a :: q = l in
    serialize_nlist_serialize_list (n - 1) s q;
    serialize_nlist_cons (n - 1) s a q;
    serialize_list_cons p s a q
  end

let rec tot_serialize_nlist'
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer #k p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (tot_serializer #(parse_nlist_kind n k) (tot_parse_nlist n p))
= if n = 0
  then begin
    Classical.forall_intro (nlist_nil_unique t);
    (fun _ -> Seq.empty)
  end
  else begin
    synth_inverse_1 t (n - 1);
    synth_inverse_2 t (n - 1);
    tot_serialize_synth _ (synth_nlist (n - 1)) (tot_serialize_nondep_then s (tot_serialize_nlist' (n - 1) s)) (synth_nlist_recip (n - 1)) ()
  end

val tot_serialize_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: tot_parser k t)
  (s: tot_serializer #k p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (y: tot_serializer #(parse_nlist_kind n k) (tot_parse_nlist n p) { y == tot_serialize_nlist' n s })

let tot_serialize_nlist_nil
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t)
  (s: tot_serializer #k p { k.parser_kind_subkind == Some ParserStrong } )
: Lemma
  (ensures (bare_serialize (tot_serialize_nlist 0 s) [] == Seq.empty))
= ()

let tot_serialize_nlist_cons
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (#p: tot_parser k t)
  (s: tot_serializer #k p { k.parser_kind_subkind == Some ParserStrong } )
  (a: t)
  (q: nlist n t)
: Lemma
  (ensures (
    bare_serialize (tot_serialize_nlist (n + 1) s) (a :: q) == Seq.append (bare_serialize s a) (bare_serialize (tot_serialize_nlist n s) q)
  ))
= tot_serialize_synth_eq #(parse_nlist_kind (n + 1) k) _ (synth_nlist n) (tot_serialize_nondep_then s (tot_serialize_nlist' n s)) (synth_nlist_recip n) () (a :: q);
  tot_serialize_nondep_then_eq s (tot_serialize_nlist' n s) (a, q)

let rec tot_serialize_nlist_serialize_nlist
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (#p: tot_parser k t)
  (s: tot_serializer #k p { k.parser_kind_subkind == Some ParserStrong } )
  (l: nlist n t)
: Lemma
  (ensures (
    bare_serialize (tot_serialize_nlist n s) l == serialize (serialize_nlist n #k #_ #p s) l
  ))
  (decreases n)
= if n = 0
  then ()
  else begin
    let a :: q = l in
    serialize_nlist_cons #k (n - 1) #p s a q;
    tot_serialize_nlist_cons (n - 1) s a q;
    tot_serialize_nlist_serialize_nlist (n - 1) s q
  end

let rec refine_nlist_of_nlist_refine
  (#t: Type)
  (f: t -> bool)
  (fl: list t -> bool { forall l . fl l == List.Tot.for_all f l })
  (n: nat)
  (l: nlist n (parse_filter_refine f))
: Tot (parse_filter_refine #(nlist n t) fl)
= match l with
  | [] -> []
  | a :: q -> a :: refine_nlist_of_nlist_refine f fl (n - 1) q

let rec refine_nlist_of_nlist_refine_injective
  (#t: Type)
  (f: t -> bool)
  (fl: list t -> bool)
  (n: nat)
: Lemma
  (requires (
    forall l . fl l == List.Tot.for_all f l
  ))
  (ensures (synth_injective (refine_nlist_of_nlist_refine f fl n)))
  (decreases n)
  [SMTPat (synth_injective (refine_nlist_of_nlist_refine f fl n))] // FIXME: WHY WHY WHY does this pattern not trigger?
= if n = 0
  then ()
  else begin
    refine_nlist_of_nlist_refine_injective f fl (n - 1);
    synth_injective_intro'
      #(nlist n (parse_filter_refine f))
      #(parse_filter_refine #(nlist n t) fl)
      (refine_nlist_of_nlist_refine f fl n)
      (fun l1 l2 ->
        let _ :: q1, _ :: q2 = l1, l2 in
        assert (refine_nlist_of_nlist_refine f fl (n - 1) q1 == refine_nlist_of_nlist_refine f fl (n - 1) q2)
      )
  end

let rec tot_parse_nlist_refine_eq
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t { k.parser_kind_subkind == Some ParserStrong })
  (f: t -> bool)
  (fl: list t -> bool {    forall l . fl l == List.Tot.for_all f l })
  (n: nat)
  (b: bytes)
: Lemma
  (ensures (synth_injective (refine_nlist_of_nlist_refine f fl n) /\
    parse (tot_parse_nlist n p `tot_parse_filter` fl) b == parse (tot_parse_nlist n (p `tot_parse_filter` f) `tot_parse_synth` refine_nlist_of_nlist_refine f fl n) b
  ))
  (decreases n)
= refine_nlist_of_nlist_refine_injective f fl n;
  tot_parse_synth_eq
    (tot_parse_nlist n (p `tot_parse_filter` f))
    (refine_nlist_of_nlist_refine f fl n)
    b;
  tot_parse_filter_eq
    (tot_parse_nlist n p)
    fl
    b;
  tot_parse_nlist_eq n p b;
  tot_parse_nlist_eq n (p `tot_parse_filter` f) b;
  tot_parse_filter_eq p f b;
  if n = 0
  then ()
  else begin
    match parse p b with
    | None -> ()
    | Some (e, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      tot_parse_nlist_refine_eq p f fl (n - 1) b';
      tot_parse_synth_eq
        (tot_parse_nlist (n - 1) (p `tot_parse_filter` f))
        (refine_nlist_of_nlist_refine f fl (n - 1))
        b';
      tot_parse_filter_eq
        (tot_parse_nlist (n - 1) p)
        fl
        b'
  end

let rec nlist_refine_of_refine_nlist
  (#t: Type)
  (f: t -> bool)
  (fl: list t -> bool { forall l . fl l == List.Tot.for_all f l })
  (n: nat)
  (l: parse_filter_refine #(nlist n t) fl)
: Tot (nlist n (parse_filter_refine f))
= match l with
  | [] -> []
  | a :: q -> a :: nlist_refine_of_refine_nlist f fl (n - 1) q

let rec refine_nlist_of_nlist_refine_inverse
  (#t: Type)
  (f: t -> bool)
  (fl: list t -> bool)
  (n: nat)
: Lemma
  (requires (forall l . fl l == List.Tot.for_all f l))
  (ensures (synth_inverse (refine_nlist_of_nlist_refine f fl n) (nlist_refine_of_refine_nlist f fl n)))
  (decreases n)
= if n = 0
  then ()
  else begin
    refine_nlist_of_nlist_refine_inverse f fl (n - 1);
    synth_inverse_intro'
      (refine_nlist_of_nlist_refine f fl n)
      (nlist_refine_of_refine_nlist f fl n)
      (fun (l: parse_filter_refine #(nlist n t) fl)  ->
        let a :: q = l in
        assert (refine_nlist_of_nlist_refine f fl (n - 1) (nlist_refine_of_refine_nlist f fl (n - 1) q) == q)
      )
  end

let rec tot_serialize_nlist_refine'
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t { k.parser_kind_subkind == Some ParserStrong })
  (f: t -> bool)
  (fl: list t -> bool { forall l . fl l == List.Tot.for_all f l })
  (s: tot_serializer (tot_parse_filter p f))
  (n: nat)
  (l: parse_filter_refine #(nlist n t) fl)
: Tot bytes
  (decreases n)
= if n = 0
  then Seq.empty
  else
    let a :: q = l in
    s a `Seq.append` tot_serialize_nlist_refine' p f fl s (n - 1) q

let tot_serialize_nlist_refine
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t { k.parser_kind_subkind == Some ParserStrong })
  (f: t -> bool)
  (fl: list t -> bool { forall l . fl l == List.Tot.for_all f l })
  (s: tot_serializer (tot_parse_filter p f))
  (n: nat)
: Tot (
    let _ = refine_nlist_of_nlist_refine_injective f fl n in
    tot_serializer (tot_parse_nlist n (tot_parse_filter p f) `tot_parse_synth` refine_nlist_of_nlist_refine f fl n)
  )
  (decreases n)
= 
  refine_nlist_of_nlist_refine_injective f fl n;
  refine_nlist_of_nlist_refine_inverse f fl n;
  tot_serialize_synth
    (tot_parse_nlist n (tot_parse_filter p f))
    (refine_nlist_of_nlist_refine f fl n)
    (tot_serialize_nlist n s)
    (nlist_refine_of_refine_nlist f fl n)
    ()

val tot_serialize_nlist_refine_eq
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t { k.parser_kind_subkind == Some ParserStrong })
  (f: t -> bool)
  (fl: list t -> bool { forall l . fl l == List.Tot.for_all f l })
  (s: tot_serializer (tot_parse_filter p f))
  (n: nat)
  (l: parse_filter_refine #(nlist n t) fl)
: Lemma
  (ensures (tot_serialize_nlist_refine p f fl s n l == tot_serialize_nlist_refine' p f fl s n l))

let tot_serialize_refine_nlist
  (#k: parser_kind)
  (#t: Type)
  (p: tot_parser k t { k.parser_kind_subkind == Some ParserStrong })
  (f: t -> bool)
  (fl: list t -> bool { forall l . fl l == List.Tot.for_all f l })
  (s: tot_serializer (tot_parse_filter p f))
  (n: nat)
: Tot (
    tot_serializer (tot_parse_nlist n p `tot_parse_filter` fl)
  )
= Classical.forall_intro (tot_parse_nlist_refine_eq p f fl n);
  refine_nlist_of_nlist_refine_injective f fl n;
  tot_serialize_ext
    _
    (tot_serialize_nlist_refine p f fl s n)
    _

(* variable-count lists proper *)

let bounded_count_prop
  (min max: nat)
  (x: U32.t)
: GTot bool
= min <= U32.v x && U32.v x <= max

inline_for_extraction
let bounded_count (min max: nat) : Tot Type = (x: U32.t { bounded_count_prop min max x == true } )

inline_for_extraction
let parse_vclist_payload_kind
  (min: nat)
  (max: nat { min <= max } )
  (k: parser_kind)
: Tot parser_kind
= {
    parser_kind_low = min `mul` k.parser_kind_low;
    parser_kind_high = (match k.parser_kind_high with
    | None -> if max = 0 then Some 0 else None
    | Some b -> Some (max `mul` b)
    );
    parser_kind_metadata = (if max = 0 then Some ParserKindMetadataTotal else if min = 0 && k.parser_kind_metadata <> Some ParserKindMetadataTotal then None else k.parser_kind_metadata);
    parser_kind_subkind = (if max = 0 then Some ParserStrong else if min = 0 && k.parser_kind_subkind <> Some ParserStrong then None else k.parser_kind_subkind);
    parser_kind_injective = (if max = 0 then true else k.parser_kind_injective);
  }

let parse_vclist_payload_kind_is_weaker_than
  (min: nat)
  (max: nat)
  (n: nat { min <= n /\ n <= max })
  (k: parser_kind)
: Lemma
  (parse_vclist_payload_kind min max k `is_weaker_than` parse_nlist_kind n k)
  [SMTPat (parse_vclist_payload_kind min max k `is_weaker_than` parse_nlist_kind n k)]
= FStar.Math.Lemmas.lemma_mult_le_right k.parser_kind_low min n;
  match k.parser_kind_high with
  | None -> ()
  | Some high -> FStar.Math.Lemmas.lemma_mult_le_right high n max

inline_for_extraction
let synth_vclist_payload
  (min: nat)
  (max: nat)
  (n: bounded_count min max)
  (#t: Type)
  (x: nlist (U32.v n) t)
: Tot (vlarray t min max)
= x

let parse_vclist_payload
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: bounded_count min max)
: Tot (parser (parse_vclist_payload_kind min max k) (vlarray t min max))
= weaken (parse_vclist_payload_kind min max k) (parse_synth (parse_nlist (U32.v n) p) (synth_vclist_payload min max n))

inline_for_extraction
let parse_vclist_kind
  (min: nat)
  (max: nat { min <= max } )
  (lk: parser_kind)
  (k: parser_kind)
: Tot parser_kind
= parse_filter_kind lk `and_then_kind` parse_vclist_payload_kind min max k

inline_for_extraction
let synth_bounded_count
  (min: nat)
  (max: nat { min <= max } )
  (x: U32.t { bounded_count_prop min max x == true } )
: Tot (bounded_count min max)
= x

let parse_vclist_and_then_cases_injective
  (min: nat)
  (max: nat { min <= max } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (and_then_cases_injective (parse_vclist_payload min max p))
  [SMTPat   (and_then_cases_injective (parse_vclist_payload min max p))]
=
    and_then_cases_injective_intro #(bounded_count min max) (parse_vclist_payload min max p) (fun x1 x2 b1 b2 ->
    parse_synth_eq (parse_nlist (U32.v x1) p) (synth_vclist_payload min max x1) b1;
    parse_synth_eq (parse_nlist (U32.v x2) p) (synth_vclist_payload min max x2) b2
  )

let parse_vclist
  (min: nat)
  (max: nat { min <= max } )
  (#lk: parser_kind)
  (lp: parser lk U32.t)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_vclist_kind min max lk k) (vlarray t min max))
= ((lp `parse_filter` bounded_count_prop min max) `parse_synth` synth_bounded_count min max) `and_then` parse_vclist_payload min max p 

let parse_vclist_eq
  (min: nat)
  (max: nat { min <= max } )
  (#lk: parser_kind)
  (lp: parser lk U32.t)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma
  (parse (parse_vclist min max lp p) b == (match parse lp b with
  | None -> None
  | Some (n, consumed_n) ->
    if min <= U32.v n && U32.v n <= max
    then
      let b_payload = Seq.slice b consumed_n (Seq.length b) in
      match parse (parse_nlist (U32.v n) p) b_payload with
      | None -> None
      | Some (l, consumed_l) ->
        Some (l, consumed_n + consumed_l)
    else None
  ))
= and_then_eq ((lp `parse_filter` bounded_count_prop min max) `parse_synth` synth_bounded_count min max) (parse_vclist_payload min max p) b;
  parse_synth_eq (lp `parse_filter` bounded_count_prop min max) (synth_bounded_count min max) b;
  parse_filter_eq lp (bounded_count_prop min max) b;
  match parse lp b with
  | None -> ()
  | Some (n, consumed_n) ->
    if min <= U32.v n && U32.v n <= max
    then
      let b_payload = Seq.slice b consumed_n (Seq.length b) in
      let n : bounded_count min max = n in
      parse_synth_eq #_ #(nlist (U32.v n) t) #(vlarray t min max) (parse_nlist (U32.v n) p) (synth_vclist_payload min max n) b_payload
    else ()

let bare_serialize_vclist
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (l: vlarray t min max)
: GTot bytes
= let n = L.length l in
  let un = U32.uint_to_t n in
  serialize ls un `Seq.append` serialize (serialize_nlist n s) l

val bare_serialize_vclist_correct
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp  { lk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Lemma
  (serializer_correct (parse_vclist min max lp p) (bare_serialize_vclist min max ls s))

let serialize_vclist
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (ls: serializer lp  { lk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (serializer (parse_vclist min max lp p))
= [@inline_let] let _ = bare_serialize_vclist_correct min max ls s in
  bare_serialize_vclist min max ls s

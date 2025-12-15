(* Variable-count lists *)

module LowParse.Spec.VCList
include LowParse.Spec.Combinators // for seq_slice_append_l
include LowParse.Spec.Array // for vlarray

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Classical = FStar.Classical
module L = FStar.List.Tot

let tot_parse_nlist n p = tot_parse_nlist' n p

let parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (y: parser (parse_nlist_kind n k) (nlist n t) { y == parse_nlist' n p } )
= parse_nlist' n p

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
#restart-solver

let rec parse_nlist_sum
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
  (decreases n1)
= parse_nlist_eq n1 p b;
  parse_nlist_eq (n1 + n2) p b;
  if n1 = 0
  then ()
  else
    match parse p b with
    | None -> ()
    | Some (x, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      parse_nlist_sum p (n1 - 1) n2 b'

#pop-options

let rec parse_nlist_parse_list
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
  (decreases n)
= let Some (_, consumed) = parse (parse_nlist n p) b in
  let bl = Seq.slice b 0 consumed in
  parse_nlist_eq n p b;
  parse_list_eq p bl;
  if n = 0
  then ()
  else begin
    parser_kind_prop_equiv k p;
    let Some (_, consumed) = parse p b in
    parse_strong_prefix p b bl;
    let b' = Seq.slice b consumed (Seq.length b) in
    let Some (_, consumed') = parse (parse_nlist (n - 1) p) b' in
    let bl' = Seq.slice b' 0 consumed' in
    assert (bl' `Seq.equal` Seq.slice bl consumed (Seq.length bl));
    parse_nlist_parse_list p (n - 1) b'
  end

let rec parse_nlist_parse_list_full
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
  (decreases n)
= let Some (_, consumed) = parse (parse_nlist n p) b in
  parse_nlist_eq n p b;
  parse_list_eq p b;
  if n = 0
  then ()
  else begin
    parser_kind_prop_equiv k p;
    let Some (_, consumed) = parse p b in
    let b' = Seq.slice b consumed (Seq.length b) in
    let Some (_, consumed') = parse (parse_nlist (n - 1) p) b' in
    parse_nlist_parse_list_full p (n - 1) b'
  end

let rec parse_list_parse_nlist
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
  (decreases (Seq.length b))
= parse_list_eq p b;
  let Some (l, _) = parse (parse_list p) b in
  parse_nlist_eq (List.Tot.length l) p b;
  if Seq.length b = 0
  then ()
  else begin
    let Some (_, consumed) = parse p b in
    let b' = Seq.slice b consumed (Seq.length b) in
    parse_list_parse_nlist p b'
  end    

let serialize_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (y: serializer (parse_nlist n p) { y == serialize_nlist' n s })
= serialize_nlist' n s

let tot_serialize_nlist n s = tot_serialize_nlist' n s

#push-options "--z3rlimit 32"

#restart-solver
let rec tot_serialize_nlist_refine_eq
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
  (decreases n)
= refine_nlist_of_nlist_refine_injective f fl n;
  refine_nlist_of_nlist_refine_inverse f fl n;
  tot_serialize_synth_eq
    (tot_parse_nlist n (tot_parse_filter p f))
    (refine_nlist_of_nlist_refine f fl n)
    (tot_serialize_nlist n s)
    (nlist_refine_of_refine_nlist f fl n)
    ()
    l;
  if n = 0
  then ()
  else begin
    let a :: q = l in
    let q : parse_filter_refine #(nlist (n - 1) t) fl = q in
    tot_serialize_nlist_refine_eq p f fl s (n - 1) q;
    refine_nlist_of_nlist_refine_injective f fl (n - 1);
    refine_nlist_of_nlist_refine_inverse f fl (n - 1);
    assert (refine_nlist_of_nlist_refine f fl (n - 1) (nlist_refine_of_refine_nlist f fl (n - 1) q) == q);
    tot_serialize_nlist_cons (n - 1) s a (nlist_refine_of_refine_nlist f fl (n - 1) q);
    assert (bare_serialize (tot_serialize_nlist (n - 1 + 1) s) (a :: nlist_refine_of_refine_nlist f fl (n - 1) q) == tot_serialize_nlist n s (nlist_refine_of_refine_nlist f fl n l));
    assert (tot_serialize_nlist n s (nlist_refine_of_refine_nlist f fl n l) == s a `Seq.append` tot_serialize_nlist (n - 1) s (nlist_refine_of_refine_nlist f fl (n - 1) q));
    assert (
      tot_serialize_nlist_refine p f fl s (n - 1) q == tot_serialize_nlist_refine' p f fl s (n - 1) q
    );
    let _ : squash (
      tot_serialize_nlist_refine p f fl s (n - 1) q == tot_serialize_nlist (n - 1) s (nlist_refine_of_refine_nlist f fl (n - 1) q)
    ) =
      assert_norm (
        tot_serialize_nlist_refine p f fl s (n - 1) ==
        tot_serialize_synth
          (tot_parse_nlist (n - 1) (tot_parse_filter p f))
          (refine_nlist_of_nlist_refine f fl (n - 1))
          (tot_serialize_nlist (n - 1) s)
          (nlist_refine_of_refine_nlist f fl (n - 1))
          ()
      );
      tot_serialize_synth_eq
        (tot_parse_nlist (n - 1) (tot_parse_filter p f))
        (refine_nlist_of_nlist_refine f fl (n - 1))
        (tot_serialize_nlist (n - 1) s)
        (nlist_refine_of_refine_nlist f fl (n - 1))
        ()
        q
    in
    assert (
      tot_serialize_nlist_refine p f fl s n l == tot_serialize_nlist_refine' p f fl s n l
    )
  end

let bare_serialize_vclist_correct
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
= let prf (x: vlarray t min max)
  : Lemma
    (let fx = bare_serialize_vclist min max ls s x in
      parse (parse_vclist min max lp p) fx == Some (x, Seq.length fx))
  = let fx = bare_serialize_vclist min max ls s x in
    parse_vclist_eq min max lp p fx;
    let n = L.length x in
    let un = U32.uint_to_t n in
    let fn = serialize ls un in
    parse_strong_prefix lp fn fx;
    let fl = serialize (serialize_nlist n s) x in
    assert (fl `Seq.equal` Seq.slice fx (Seq.length fn) (Seq.length fx))
  in
  Classical.forall_intro prf

#pop-options

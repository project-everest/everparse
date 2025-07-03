module LowParse.Spec.RtoLDepPair
include LowParse.Spec.Base

module Seq = FStar.Seq

let dtuple2_rtol_kind 
  (k1: parser_kind { k1.parser_kind_subkind == Some ParserConsumesAll })
  (n: nat)
  : parser_kind
  = {
      parser_kind_low = k1.parser_kind_low + n;
      parser_kind_high = None;
      parser_kind_subkind = Some (ParserConsumesAll);
      parser_kind_metadata = None;
    }

let dtuple2_rtol_bare
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2 { k2.parser_kind_high == Some (k2.parser_kind_low) } )
  (#k1: parser_kind { k1.parser_kind_subkind == Some ParserConsumesAll })
  (#t1: t2 -> Type)
  (p1: ((x:t2) -> parser k1 (t1 x)))
: Tot (bare_parser (dtuple2 t2 t1))
  =
  fun b ->
    if Seq.length b < k2.parser_kind_low then
      None
    else
      let (bl, br) = Seq.split b (Seq.length b - k2.parser_kind_low) in
      match parse p2 br with
      | Some (x2, consumed2) ->
        let p1_x2 = p1 x2 in
        begin match parse p1_x2 bl with
        | Some (x1, consumed1) ->
          Some ((|x2, x1|), consumed1 + consumed2)
        | _ -> None
        end
      | _ -> None

let dtuple2_rtol_bare_correct
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2 { k2.parser_kind_high == Some (k2.parser_kind_low) } )
  (#k1: parser_kind { k1.parser_kind_subkind == Some ParserConsumesAll })
  (#t1: t2 -> Type)
  (p1: ((x:t2) -> parser k1 (t1 x)))
  : Lemma (ensures parser_kind_prop (dtuple2_rtol_kind k1 k2.parser_kind_low) (dtuple2_rtol_bare
    p2 p1))
  = 
    Classical.forall_intro_2 (Seq.lemma_split # byte) ;
    parser_kind_prop_equiv k2 p2;
    Classical.forall_intro (fun x -> parser_kind_prop_equiv k1 (p1 x));
    parser_kind_prop_equiv (dtuple2_rtol_kind k1 k2.parser_kind_low) (dtuple2_rtol_bare
    p2 p1);

    let ps = dtuple2_rtol_bare p2 p1 in
    let f
      (b1 b2: bytes)
    : Lemma
      (requires (injective_precond ps b1 b2))
      (ensures (injective_postcond ps b1 b2))
    = 
      let (bl1, br1) = Seq.split b1 (Seq.length b1 - k2.parser_kind_low) in
      let (bl2, br2) = Seq.split b2 (Seq.length b2 - k2.parser_kind_low) in
      assert (injective_precond p2 br1 br2);
      let (Some (x2, len2)) = parse p2 br1 in
      assert (injective_precond (p1 x2) bl1 bl2);
      assert (injective_postcond ps b1 b2)
    in
    Classical.forall_intro_2 (fun x -> Classical.move_requires (f x)) ; // add f to the SMT context
    assert (injective (dtuple2_rtol_bare p2 p1));
    assert (consumes_all (dtuple2_rtol_bare p2 p1));
    assert (parses_at_least (k1.parser_kind_low + k2.parser_kind_low) (dtuple2_rtol_bare p2 p1))


val parse_dtuple2_rtol
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2 { k2.parser_kind_high == Some (k2.parser_kind_low) } )
  (#k1: parser_kind { k1.parser_kind_subkind == Some ParserConsumesAll })
  (#t1: t2 -> Type)
  (p1: ((x:t2) -> parser k1 (t1 x)))
: Tot (parser (dtuple2_rtol_kind k1 k2.parser_kind_low) (dtuple2 t2 t1))

let parse_dtuple2_rtol
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2 { k2.parser_kind_high == Some (k2.parser_kind_low) } )
  (#k1: parser_kind { k1.parser_kind_subkind == Some ParserConsumesAll })
  (#t1: t2 -> Type)
  (p1: ((x:t2) -> parser k1 (t1 x)))
: Tot (parser (dtuple2_rtol_kind k1 k2.parser_kind_low) (dtuple2 t2 t1))
=
  dtuple2_rtol_bare_correct p2 p1;
  dtuple2_rtol_bare p2 p1


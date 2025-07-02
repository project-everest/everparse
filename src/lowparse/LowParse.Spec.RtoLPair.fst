module LowParse.Spec.RtoLPair
include LowParse.Spec.Base

module Seq = FStar.Seq

let nondep_then_rtol_kind 
  (k1: parser_kind { k1.parser_kind_subkind == Some ParserConsumesAll })
  (n: nat)
  : parser_kind
  = {
      parser_kind_low = k1.parser_kind_low + n;
      parser_kind_high = None;
      parser_kind_subkind = Some (ParserConsumesAll);
      parser_kind_metadata = None;
    }

let nondep_then_rtol_bare
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1 { k1.parser_kind_subkind == Some ParserConsumesAll })
  (#n: nat)
  (#t2: Type)
  (p2: parser (total_constant_size_parser_kind n) t2)
: Tot (bare_parser (t2 & t1))
  =
  fun b ->
    if Seq.length b < n then
      None
    else
      let (bl, br) = Seq.split b (Seq.length b - n) in
      match parse p2 br with
      | Some (x2, consumed2) ->
        begin match parse p1 bl with
        | Some (x1, consumed1) ->
          Some ((x2, x1), consumed1 + consumed2)
        | _ -> None
        end
      | _ -> None

let nondep_then_rtol_bare_correct
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1 { k1.parser_kind_subkind == Some ParserConsumesAll })
  (#n: nat)
  (#t2: Type)
  (p2: parser (total_constant_size_parser_kind n) t2)
  : Lemma (ensures parser_kind_prop (nondep_then_rtol_kind k1 n) (nondep_then_rtol_bare
    p1 p2))
  = 
    Classical.forall_intro_2 (Seq.lemma_split # byte) ;
    parser_kind_prop_equiv k1 p1;
    parser_kind_prop_equiv (total_constant_size_parser_kind n) p2;
    parser_kind_prop_equiv (nondep_then_rtol_kind k1 n) (nondep_then_rtol_bare
    p1 p2);

    let ps = nondep_then_rtol_bare p1 p2 in
    let f
      (b1 b2: bytes)
    : Lemma
      (requires (injective_precond ps b1 b2))
      (ensures (injective_postcond ps b1 b2))
    = 
      let (bl1, br1) = Seq.split b1 (Seq.length b1 - n) in
      let (bl2, br2) = Seq.split b2 (Seq.length b2 - n) in
      assert (injective_precond p2 br1 br2);
      assert (injective_precond p1 bl1 bl2);
      assert (injective_postcond ps b1 b2)
    in
    Classical.forall_intro_2 (fun x -> Classical.move_requires (f x)) ; // add f to the SMT context
    assert (injective (nondep_then_rtol_bare p1 p2));
    assert (consumes_all (nondep_then_rtol_bare p1 p2));
    assert (parses_at_least (k1.parser_kind_low + n) (nondep_then_rtol_bare p1 p2))


val parse_nondep_then_rtol
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1 { k1.parser_kind_subkind == Some ParserConsumesAll })
  (#n: nat)
  (#t2: Type)
  (p2: parser (total_constant_size_parser_kind n) t2)
: Tot (parser (nondep_then_rtol_kind k1 n) (t2 & t1))

let parse_nondep_then_rtol
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1 { k1.parser_kind_subkind == Some ParserConsumesAll })
  (#n: nat)
  (#t2: Type)
  (p2: parser (total_constant_size_parser_kind n) t2)
  : Tot (parser (nondep_then_rtol_kind k1 n) (t2 & t1)) =
  nondep_then_rtol_bare_correct p1 p2;
  nondep_then_rtol_bare p1 p2


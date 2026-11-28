module LowParse.Spec.RecursiveGen
include LowParse.Spec.Combinators

(* A generic recursive parser combinator.

   A recursive value is a header followed by a payload whose parser may
   call the recursive parser itself (`ih`). The only requirement is that
   the payload only ever calls `ih` on inputs no longer than its own input
   (`payload_ext`). Since the header consumes at least one byte, this
   guarantees well-foundedness; the fixpoint is built by fuel
   (LowParse.Spec.Fuel).

   LowParse.Spec.Recursive (count-based payload: `nlist (count h) t`) and
   LowParse.Spec.RecursiveVLGen (length-delimited payload) are instances. *)

module Seq = FStar.Seq

let parse_rec_gen_kind
  (k: parser_kind { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 })
: Tot parser_kind
= {
    parser_kind_low = k.parser_kind_low;
    parser_kind_high = None;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = None;
    parser_kind_injective = k.parser_kind_injective;
  }

let parse_rec_gen_header_kind = (k: parser_kind { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 })

let parse_rec_gen_payload_kind (hk: parse_rec_gen_header_kind) =
  (k: parser_kind { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_injective == hk.parser_kind_injective })

let parse_rec_gen_ih_agree
  (#k: parser_kind)
  (#t: Type)
  (ih1 ih2: tot_parser k t)
  (b: bytes)
: Tot prop
= forall (b': bytes { Seq.length b' <= Seq.length b }) . parse ih1 b' == parse ih2 b'

[@@(noextract_to "krml")]
inline_for_extraction
noeq
type parse_rec_gen_param = {
  t: Type;
  header: Type;
  header_kind: parse_rec_gen_header_kind;
  parse_header: tot_parser header_kind header;
  payload_t: (header -> Type);
  payload_kind: parse_rec_gen_payload_kind header_kind;
  payload: ((ih: tot_parser (parse_rec_gen_kind header_kind) t) -> (h: header) -> tot_parser payload_kind (payload_t h));
  payload_ext: (
    (ih1: tot_parser (parse_rec_gen_kind header_kind) t) ->
    (ih2: tot_parser (parse_rec_gen_kind header_kind) t) ->
    (h: header) ->
    (b: bytes) ->
    Lemma
    (requires (parse_rec_gen_ih_agree ih1 ih2 b))
    (ensures (parse (payload ih1 h) b == parse (payload ih2 h) b))
  );
  synth_: (dtuple2 header payload_t -> t);
  synth_inj: squash (synth_injective synth_);
}

let parse_rec_gen_alt
  (p: parse_rec_gen_param)
  (ih: tot_parser (parse_rec_gen_kind p.header_kind) p.t)
: Tot (tot_parser (and_then_kind p.header_kind p.payload_kind) (dtuple2 p.header p.payload_t))
= p.parse_header `tot_parse_dtuple2` p.payload ih

let parse_rec_gen_aux
  (p: parse_rec_gen_param)
  (ih: tot_parser (parse_rec_gen_kind p.header_kind) p.t)
: Tot (tot_parser (parse_rec_gen_kind p.header_kind) p.t)
= p.synth_inj;
  tot_weaken _ (parse_rec_gen_alt p ih `tot_parse_synth` p.synth_)

val parse_rec_gen
  (p: parse_rec_gen_param)
: Tot (tot_parser (parse_rec_gen_kind p.header_kind) p.t)

val parse_rec_gen_eq
  (p: parse_rec_gen_param)
  (b: bytes)
: Lemma
  (parse (parse_rec_gen p) b == parse (parse_rec_gen_aux p (parse_rec_gen p)) b)

let parse_rec_gen_eq'
  (p: parse_rec_gen_param)
  (b: bytes)
: Lemma
  (parse (parse_rec_gen p) b == begin match parse p.parse_header b with
  | None -> None
  | Some (h, consumed1) ->
    let b2 = Seq.slice b consumed1 (Seq.length b) in
    match parse (p.payload (parse_rec_gen p) h) b2 with
    | None -> None
    | Some (pl, consumed2) ->
      Some (p.synth_ (| h, pl |), consumed1 + consumed2)
  end
  )
= parse_rec_gen_eq p b;
  p.synth_inj;
  tot_parse_synth_eq (parse_rec_gen_alt p (parse_rec_gen p)) p.synth_ b

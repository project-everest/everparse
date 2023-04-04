module LowParse.Spec.Recursive

open LowParse.Spec.Combinators
open LowParse.Spec.VCList
open LowParse.WellFounded

let parse_recursive_payload_t
  (t: Type)
  (header: Type)
  (count: (header -> nat))
  (h: header)
: Tot Type
= nlist (count h) t

let parse_recursive_alt_t
  (t: Type)
  (header: Type)
  (count: (header -> nat))
: Tot Type
= dtuple2 header (parse_recursive_payload_t t header count)

[@@(noextract_to "krml")]
inline_for_extraction
noeq
type parse_recursive_param = {
  t: Type;
  header: Type;
  parse_header_kind: (k: parser_kind { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 });
  parse_header: parser parse_header_kind header;
  count: (header -> nat);
  synth_: (parse_recursive_alt_t t header count -> t);
  synth_inj: squash (synth_injective synth_);
}

let parse_recursive_kind
  (k: parser_kind { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 })
: Tot parser_kind
= {
    parser_kind_low = k.parser_kind_low;
    parser_kind_high = None;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = None;
  }

let parse_recursive_payload_kind
: parser_kind
= {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = None;
  }

let parse_recursive_payload
  (p: parse_recursive_param)
  (ih: parser (parse_recursive_kind p.parse_header_kind) p.t)
  (h: p.header)
: Tot (parser parse_recursive_payload_kind (parse_recursive_payload_t p.t p.header p.count h))
= weaken parse_recursive_payload_kind (parse_nlist (p.count h) ih)

let parse_recursive_alt
  (p: parse_recursive_param)
  (ih: parser (parse_recursive_kind p.parse_header_kind) p.t)
: Tot (parser _ (parse_recursive_alt_t p.t p.header p.count))
= p.parse_header `parse_dtuple2` parse_recursive_payload p ih

let parse_recursive_aux
  (p: parse_recursive_param)
  (ih: parser (parse_recursive_kind p.parse_header_kind) p.t)
: Tot (parser (parse_recursive_kind p.parse_header_kind) p.t)
= weaken _ (parse_recursive_alt p ih `parse_synth` p.synth_)

val parse_recursive
  (p: parse_recursive_param)
: Tot (parser (parse_recursive_kind p.parse_header_kind) p.t)

val parse_recursive_eq
  (p: parse_recursive_param)
  (b: bytes)
: Lemma
  (parse (parse_recursive p) b == parse (parse_recursive_aux p (parse_recursive p)) b)

let has_level
  (#t: Type)
  (level: (t -> nat))
  (n: nat)
  (d: t)
: Tot bool
= level d <= n

let list_has_pred_level
  (#t: Type)
  (level: (t -> nat))
  (n: nat)
  (l: list t)
: Tot bool
= if n = 0 then Nil? l else forall_list l (has_level level (n - 1))

[@@(noextract_to "krml")]
inline_for_extraction
noeq
type serialize_recursive_param (p: parse_recursive_param) = {
  serialize_header: serializer p.parse_header;
  synth_recip: (p.t -> (parse_recursive_alt_t p.t p.header p.count));
  synth_inv: squash (synth_inverse p.synth_ synth_recip);
  level: (p.t -> nat);
  level_correct: (x: p.t) -> (n: nat) -> Lemma (requires (has_level level n x)) (ensures ( (list_has_pred_level level n (dsnd (synth_recip x)))));
}

val serialize_recursive
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
: Tot (serializer (parse_recursive pp))

let serialize_recursive_payload
  (#p: parse_recursive_param)
  (sp: serialize_recursive_param p)
  (h: p.header)
: Tot (serializer (parse_recursive_payload p (parse_recursive p) h))
= serialize_weaken _
    (serialize_nlist
      (p.count h)
      (serialize_recursive sp)
    )

let serialize_recursive_aux
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
: Tot (serializer (parse_recursive_aux pp (parse_recursive pp)))
=
  serialize_weaken _
    (serialize_synth _
      pp.synth_
      (serialize_dtuple2
        sp.serialize_header
        (serialize_recursive_payload sp)
      )
      sp.synth_recip
      ()
    )

val serialize_recursive_eq
  (#pp: parse_recursive_param)
  (sp: serialize_recursive_param pp)
  (x: pp.t)
: Lemma
  (serialize (serialize_recursive sp) x == serialize (serialize_recursive_aux sp) x)

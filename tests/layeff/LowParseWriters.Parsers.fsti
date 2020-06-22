module LowParseWriters.Parsers
include LowParseWriters

module LP = LowParse.Low
module Seq = FStar.Seq

inline_for_extraction
noextract
val get_parser_kind
  (p: parser)
: Tot (kind: LP.parser_kind { kind.LP.parser_kind_subkind == Some LP.ParserStrong })

inline_for_extraction
val get_parser
  (p: parser)
: Tot (LP.parser (get_parser_kind p) (dfst p))

inline_for_extraction
noextract
val make_parser'
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Tot (parser' t)

inline_for_extraction
noextract
let make_parser
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Tot parser
= (| t, make_parser' p s j |)

val make_parser_correct
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Lemma
  (let p' = make_parser p s j in
   get_parser_kind p' == k /\
   get_parser p' == p
  )
  [SMTPat (make_parser p s j)]

val size_correct
  (p: parser)
  (s: LP.serializer (get_parser p))
  (x: dfst p)
: Lemma
  (size p x == Seq.length (LP.serialize s x))

val valid_synth_parser_eq
  (p1: parser)
  (p2: parser {
    dfst p1 == dfst p2 /\
    get_parser_kind p1 == get_parser_kind p2 /\
    get_parser p1 == LP.coerce (LP.parser (get_parser_kind p1) (dfst p1)) (get_parser p2)
  })
: Tot (valid_synth_t p1 p2 (fun _ -> True) (fun x -> x))

inline_for_extraction
val parse_synth
  (p1: parser)
  (#t2: Type)
  (f2: dfst p1 -> GTot t2)
  (f1: t2 -> GTot (dfst p1))
: Pure parser
  (requires (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
  (ensures (fun r ->
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1 /\
    dfst r == t2 /\
    get_parser_kind r == get_parser_kind p1 /\
    get_parser r == LP.coerce (LP.parser (get_parser_kind r) (dfst r)) (get_parser p1 `LP.parse_synth` f2)
  ))

val valid_synth_parse_synth
  (p1: parser)
  (#t2: Type)
  (f2: dfst p1 -> GTot t2)
  (f1: t2 -> GTot (dfst p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (valid_synth_t p1 (parse_synth p1 f2 f1) (fun _ -> True) f2)

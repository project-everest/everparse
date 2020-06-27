module LowParseWriters.Compat
include LowParseWriters.Parsers

module LP = LowParse.Low

val star_correct
  (p1 p2: parser)
: Lemma
  (get_parser_kind (p1 `star` p2) == get_parser_kind p1 `LP.and_then_kind` get_parser_kind p2 /\
  get_parser (p1 `star` p2) == get_parser p1 `LP.nondep_then` get_parser p2 /\
  get_serializer (p1 `star` p2) == get_serializer p1 `LP.serialize_nondep_then` get_serializer p2)
  [SMTPat (p1 `star` p2)]

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
    get_parser r == LP.coerce (LP.parser (get_parser_kind r) (dfst r)) (get_parser p1 `LP.parse_synth` f2) /\
    get_serializer r == LP.coerce (LP.serializer (get_parser r)) (LP.serialize_synth (get_parser p1) f2 (get_serializer p1) f1 ())
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

val valid_synth_parse_synth_recip
  (p1: parser)
  (#t2: Type)
  (f2: dfst p1 -> GTot t2)
  (f1: t2 -> GTot (dfst p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (valid_synth_t (parse_synth p1 f2 f1) p1 (fun _ -> True) f1)

module U32 = FStar.UInt32

val parse_vldata_correct
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Lemma
  (
    let p' = parse_vldata p min max in
    dfst p' == LP.parse_bounded_vldata_strong_t (U32.v min) (U32.v max) (get_serializer p) /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) (get_parser_kind p) /\
    get_parser p' == LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p) /\
    get_serializer p' == LP.serialize_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p)
  )
  [SMTPatOr [
    [SMTPat (dfst (parse_vldata p min max))];
    [SMTPat (get_parser_kind (parse_vldata p min max))];
    [SMTPat (get_parser (parse_vldata p min max))];
    [SMTPat (get_serializer (parse_vldata p min max))];
  ]]

val list_size_correct
  (p: parser1)
  (x: list (dfst p))
: Lemma
  (list_size p x == Seq.length (LP.serialize (LP.serialize_list _ (get_serializer p)) x))
  [SMTPat (list_size p x)]

inline_for_extraction
val parse_vllist_correct
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Lemma
  (let p' = parse_vllist p min max in
    dfst p' == LP.parse_bounded_vldata_strong_t (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) LP.parse_list_kind /\
    get_parser p' == LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) /\
    get_serializer p' == LP.serialize_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p))
  )
  [SMTPatOr [
    [SMTPat (dfst (parse_vllist p min max))];
    [SMTPat (get_parser_kind (parse_vllist p min max))];
    [SMTPat (get_parser (parse_vllist p min max))];
    [SMTPat (get_serializer (parse_vllist p min max))];
  ]]

val parse_vlbytes_correct
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Lemma (
    let p' = parse_vlbytes min max in
    dfst p' == LP.parse_bounded_vlbytes_t (U32.v min) (U32.v max) /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) LP.parse_all_bytes_kind /\
    get_parser p' == LP.parse_bounded_vlbytes (U32.v min) (U32.v max) /\
    get_serializer p' == LP.serialize_bounded_vlbytes (U32.v min) (U32.v max)
  )
  [SMTPatOr [
    [SMTPat (dfst (parse_vlbytes min max))];
    [SMTPat (get_parser_kind (parse_vlbytes min max))];
    [SMTPat (get_parser (parse_vlbytes min max))];
    [SMTPat (get_serializer (parse_vlbytes min max))];
  ]]

inline_for_extraction
noextract
noeq
type parse_sum_t = {
  sum_kt: LP.parser_kind;
  sum_t: (sum_t: LP.sum {
    Cons? (LP.sum_enum sum_t)
  });
  sum_p: LP.parser sum_kt (LP.sum_repr_type sum_t);
  sum_r: LP.leaf_reader sum_p;
  sum_s: LP.serializer sum_p;
  sum_pc: ((x: LP.sum_key sum_t) -> Tot (k: LP.parser_kind & LP.parser k (LP.sum_type_of_tag sum_t x)));
  sum_sc: ((x: LP.sum_key sum_t) -> Tot (LP.serializer (dsnd (sum_pc x))));
  sum_destr: LP.dep_maybe_enum_destr_t (LP.sum_enum sum_t) (LP.jump_sum_aux_payload_t sum_t sum_pc);
  sum_p' : (p' : parser {
    dfst p' == LP.sum_repr_type sum_t /\
    get_parser_kind p' == sum_kt /\
    get_parser p' == sum_p /\
    get_serializer p' == sum_s
  });
  sum_pc' : ((x: LP.sum_key sum_t) -> Tot (p': parser {
    dfst p' == LP.sum_type_of_tag sum_t x /\
    get_parser_kind p' == dfst (sum_pc x) /\
    get_parser p' == LP.coerce (LP.parser (get_parser_kind p') (dfst p')) (dsnd (sum_pc x)) /\
    get_serializer p' == LP.coerce (LP.serializer (get_parser p')) (sum_sc x)
  }));
}

inline_for_extraction
noextract
val parse_enum
  (#key: eqtype)
  (p: parser { hasEq (dfst p) })
  (e: LP.enum key (dfst p))
: Tot (p': parser {
    dfst p' == LP.enum_key e /\
    get_parser_kind p' == LP.parse_filter_kind (get_parser_kind p) /\
    get_parser p' == LP.parse_enum_key (get_parser p) e /\
    get_serializer p' == LP.serialize_enum_key _ (get_serializer p) e
  })

inline_for_extraction
noextract
val parse_sum
  (ps: parse_sum_t)
: Tot (q: parser {
    dfst q == LP.sum_type ps.sum_t /\
    get_parser_kind q == LP.parse_sum_kind ps.sum_kt ps.sum_t ps.sum_pc /\
    get_parser q == LP.parse_sum ps.sum_t ps.sum_p ps.sum_pc /\
    get_serializer q == LP.serialize_sum #ps.sum_kt ps.sum_t #ps.sum_p ps.sum_s #ps.sum_pc ps.sum_sc
  })

val valid_synth_parse_sum
  (ps: parse_sum_t)
  (k: LP.sum_key ps.sum_t)
: Tot (valid_synth_t (parse_enum ps.sum_p' (LP.sum_enum ps.sum_t) `star` ps.sum_pc' k) (parse_sum ps) (fun (k', _) -> k' == k) (fun (_, pl) -> LP.Sum?.synth_case ps.sum_t k pl))

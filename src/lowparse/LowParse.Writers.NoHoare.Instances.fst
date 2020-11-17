module LowParse.Writers.NoHoare.Instances
include LowParse.Writers.Instances
include LowParse.Writers.NoHoare.Combinators

module LP = LowParse.Low

let valid_rewrite_parse_synth_gen'
  (p1: parser)
  (p2: parser)
  (f2: Parser?.t p1 -> GTot (Parser?.t p2))
  (f1: Parser?.t p2 -> GTot (Parser?.t p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1 /\
    get_parser_kind p2 == get_parser_kind p1 /\
    get_parser p2 == LP.coerce (LP.parser (get_parser_kind p2) (Parser?.t p2)) (get_parser p1 `LP.parse_synth` f2) /\
    get_serializer p2 == LP.coerce (LP.serializer (get_parser p2)) (LP.serialize_synth (get_parser p1) f2 (get_serializer p1) f1 ())
  ))
: Tot (squash (valid_rewrite_prop p1 p2))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_synth_gen p1 p2 f2 f1 sq)

let valid_rewrite_parse_synth'
  (p1: parser)
  (#t2: Type)
  (f2: Parser?.t p1 -> GTot t2)
  (f1: t2 -> GTot (Parser?.t p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (squash (valid_rewrite_prop p1 (parse_synth p1 f2 f1)))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_synth p1 f2 f1 sq)

let valid_rewrite_parse_synth_recip'
  (p1: parser)
  (#t2: Type)
  (f2: Parser?.t p1 -> GTot t2)
  (f1: t2 -> GTot (Parser?.t p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (squash (valid_rewrite_prop (parse_synth p1 f2 f1) p1))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_synth_recip p1 f2 f1 sq)

module U32 = FStar.UInt32

let valid_rewrite_parse_vlarray_intro'
  (pa: parser)
  (p: parser1)
  (array_byte_size_min: U32.t)
  (array_byte_size_max: U32.t { U32.v array_byte_size_min <= U32.v array_byte_size_max /\ U32.v array_byte_size_max > 0 } )
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: squash (
    LP.vldata_vlarray_precond (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_parser p) elem_count_min elem_count_max == true /\
    get_parser_kind pa == LP.parse_vlarray_kind (U32.v array_byte_size_min) (U32.v array_byte_size_max) /\
    Parser?.t pa == LP.vlarray (Parser?.t p) elem_count_min elem_count_max /\
    get_parser pa == LP.parse_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max ()
  ))
: Tot (squash (valid_rewrite_prop
    (parse_vllist p array_byte_size_min array_byte_size_max)
    pa
  ))
=
  tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_vlarray_intro pa p array_byte_size_min array_byte_size_max elem_count_min elem_count_max u)

let valid_rewrite_parse_vlarray_elim'
  (pa: parser)
  (p: parser1)
  (array_byte_size_min: U32.t)
  (array_byte_size_max: U32.t { U32.v array_byte_size_min <= U32.v array_byte_size_max /\ U32.v array_byte_size_max > 0 } )
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: squash (
    LP.vldata_vlarray_precond (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_parser p) elem_count_min elem_count_max == true /\
    get_parser_kind pa == LP.parse_vlarray_kind (U32.v array_byte_size_min) (U32.v array_byte_size_max) /\
    Parser?.t pa == LP.vlarray (Parser?.t p) elem_count_min elem_count_max /\
    get_parser pa == LP.parse_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max ()
  ))
: Tot (squash (valid_rewrite_prop
    pa
    (parse_vllist p array_byte_size_min array_byte_size_max)
  ))
=
  tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_vlarray_elim pa p array_byte_size_min array_byte_size_max elem_count_min elem_count_max u)

let valid_rewrite_parse_bounded_vldata_intro'
  (pa: parser)
  (p: parser)
  (min: U32.t)
  (max: U32.t {
    U32.v min <= U32.v max /\
    U32.v max > 0 /\
    LP.serialize_bounded_vldata_precond (U32.v min) (U32.v max) (get_parser_kind p) /\
    Parser?.t pa == Parser?.t p /\
    get_parser_kind pa == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) (get_parser_kind p) /\
    get_parser pa == LP.parse_bounded_vldata (U32.v min) (U32.v max) (get_parser p)
  })
: Tot (squash (valid_rewrite_prop
    (parse_vldata p min max)
    pa
  ))
=
  tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_bounded_vldata_intro pa p min max)

inline_for_extraction
noextract
let parse_bounded_vldata_intro_ho'
  (#inv: memory_invariant)
  (pa: parser)
  (p: parser)
  (min: U32.t)
  (max: U32.t {
    U32.v min <= U32.v max /\
    U32.v max > 0 /\
    LP.serialize_bounded_vldata_precond (U32.v min) (U32.v max) (get_parser_kind p) /\
    Parser?.t pa == Parser?.t p /\
    get_parser_kind pa == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) (get_parser_kind p) /\
    get_parser pa == LP.parse_bounded_vldata (U32.v min) (U32.v max) (get_parser p)
  })
  (f: (unit -> TWrite unit parse_empty p inv))
: TWrite unit parse_empty pa
    inv
=
  twrite_of_ewrite (fun _ -> parse_bounded_vldata_intro_ho' pa p min max (fun _ -> ewrite_of_twrite f))
   
inline_for_extraction
noextract
let write_sum
  (ps: parse_sum_t)
  (pe: pparser _ _ _ (LP.serialize_enum_key ps.sum_p ps.sum_s (LP.sum_enum ps.sum_t)))
  (p: pparser _ _ _ (LP.serialize_sum ps.sum_t ps.sum_s #ps.sum_pc ps.sum_sc))
  (w: LP.leaf_writer_strong (LP.serialize_enum_key ps.sum_p ps.sum_s (LP.sum_enum ps.sum_t)) {
    ps.sum_kt.LP.parser_kind_high == Some ps.sum_kt.LP.parser_kind_low
  })
  (k: LP.sum_key ps.sum_t)
  (pk: pparser _ _ (dsnd (ps.sum_pc k)) (ps.sum_sc k))
  (inv: memory_invariant)
  (f: (unit -> TWrite unit parse_empty pk inv))
: TWrite unit parse_empty p inv
=
  twrite_of_ewrite (fun _ -> write_sum ps pe p w k pk _ _ _ inv (fun _ -> ewrite_of_twrite f))

inline_for_extraction
noextract
let write_dsum_known
  (ps: parse_dsum_t)
  (pe: pparser _ _ _ (LP.serialize_maybe_enum_key ps.dsum_p ps.dsum_s (LP.dsum_enum ps.dsum_t)))
  (p: pparser _ _ _ (LP.serialize_dsum ps.dsum_t ps.dsum_s ps.dsum_pc ps.dsum_sc ps.dsum_pu ps.dsum_su))
  (w: LP.leaf_writer_strong (LP.serialize_maybe_enum_key ps.dsum_p ps.dsum_s (LP.dsum_enum ps.dsum_t)) {
    ps.dsum_kt.LP.parser_kind_high == Some ps.dsum_kt.LP.parser_kind_low
  })
  (k: LP.dsum_known_key ps.dsum_t)
  (pk: pparser _ _ (dsnd (ps.dsum_pc k)) (ps.dsum_sc k))
  (inv: memory_invariant)
  (f: (unit -> TWrite unit parse_empty pk inv))
: TWrite unit parse_empty p
    inv
=
  twrite_of_ewrite (fun _ -> write_dsum_known ps pe p w k pk _ _ _ inv (fun _ -> ewrite_of_twrite f))

inline_for_extraction
noextract
let write_dsum_unknown
  (ps: parse_dsum_t)
  (pe: pparser _ _ _ (LP.serialize_maybe_enum_key ps.dsum_p ps.dsum_s (LP.dsum_enum ps.dsum_t)))
  (p: pparser _ _ _ (LP.serialize_dsum ps.dsum_t ps.dsum_s ps.dsum_pc ps.dsum_sc ps.dsum_pu ps.dsum_su))
  (w: LP.leaf_writer_strong (LP.serialize_maybe_enum_key ps.dsum_p ps.dsum_s (LP.dsum_enum ps.dsum_t)) {
    ps.dsum_kt.LP.parser_kind_high == Some ps.dsum_kt.LP.parser_kind_low
  })
  (k: LP.dsum_unknown_key ps.dsum_t)
  (pk: pparser _ _ _ ps.dsum_su)
  (inv: memory_invariant)
  ($f: (unit -> TWrite unit parse_empty pk inv))
: TWrite unit parse_empty p
    inv
=
  twrite_of_ewrite (fun _ -> write_dsum_unknown ps pe p w k pk _ _ _ inv (fun _ -> ewrite_of_twrite f))

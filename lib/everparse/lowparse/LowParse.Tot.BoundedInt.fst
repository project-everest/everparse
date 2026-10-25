module LowParse.Tot.BoundedInt
include LowParse.Spec.BoundedInt
include LowParse.Tot.Int

module E = FStar.Endianness
module U32 = FStar.UInt32

let parse_bounded_integer_bare
  (i: integer_size)
: Tot (bare_parser (bounded_integer i))
= fun input ->
  parse_bounded_integer_spec i input;
  if Seq.length input < i
  then None
  else
    let input' = Seq.slice input 0 i in
    let _ = E.lemma_be_to_n_is_bounded input' in
    let y = U32.uint_to_t (E.be_to_n input') in
    Some (y, i)

val parse_bounded_integer
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))

let parse_bounded_integer
  i
=
  Classical.forall_intro (parse_bounded_integer_spec i);
  parser_kind_prop_ext
    (parse_bounded_integer_kind i)
    (parse_bounded_integer i)
    (parse_bounded_integer_bare i);
  parse_bounded_integer_bare i

module LowParse.Spec.Int
open LowParse.Spec.Combinators

let decode_u8
  (b: bytes { Seq.length b == 1 } )
: GTot U8.t
= Seq.index b 0

let decode_u8_injective () : Lemma
  (make_total_constant_size_parser_precond 1 U8.t decode_u8)
= ()

let parse_u8 =
  decode_u8_injective ();
  make_total_constant_size_parser 1 U8.t decode_u8

let parse_u8_spec
  b
=
  Seq.lemma_index_slice b 0 1 0;
  E.reveal_be_to_n (Seq.slice b 0 1);
  E.reveal_be_to_n (Seq.slice (Seq.slice b 0 1) 0 0)

let parse_u8_spec' b = ()

let serialize_u8 =
  Seq.create 1

let serialize_u8_spec x = ()

let decode_u16
  (b: bytes { Seq.length b == 2 } )
: GTot U16.t
= E.lemma_be_to_n_is_bounded b;
  U16.uint_to_t (E.be_to_n b)

let decode_u16_injective'
  (b1: bytes { Seq.length b1 == 2 } )
  (b2: bytes { Seq.length b2 == 2 } )
: Lemma
  (decode_u16 b1 == decode_u16 b2 ==> Seq.equal b1 b2)
= if decode_u16 b1 = decode_u16 b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    E.be_to_n_inj b1 b2
  end else ()

let decode_u16_injective
  ()
: Lemma
  (make_total_constant_size_parser_precond 2 U16.t decode_u16)
= Classical.forall_intro_2 decode_u16_injective'

let parse_u16 =
  decode_u16_injective ();
  make_total_constant_size_parser 2 U16.t decode_u16

let parse_u16_spec
  b
=
  E.lemma_be_to_n_is_bounded (Seq.slice b 0 2)

let serialize_u16 =
  (fun (x: U16.t) -> E.n_to_be 2 (U16.v x))

let decode_u32
  (b: bytes { Seq.length b == 4 } )
: GTot U32.t
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

let decode_u32_injective'
  (b1: bytes { Seq.length b1 == 4 } )
  (b2: bytes { Seq.length b2 == 4 } )
: Lemma
  (decode_u32 b1 == decode_u32 b2 ==> Seq.equal b1 b2)
= if decode_u32 b1 = decode_u32 b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    E.be_to_n_inj b1 b2
  end else ()

let decode_u32_injective () : Lemma
  (make_total_constant_size_parser_precond 4 U32.t decode_u32)
= Classical.forall_intro_2 decode_u32_injective'

let parse_u32 =
  decode_u32_injective ();
  make_total_constant_size_parser 4 U32.t decode_u32

let parse_u32_spec
  b
=
  E.lemma_be_to_n_is_bounded (Seq.slice b 0 4)

let serialize_u32 =
  (fun (x: U32.t) -> E.n_to_be 4 (U32.v x))

let decode_u64
  (b: bytes { Seq.length b == 8 } )
: GTot U64.t
= E.lemma_be_to_n_is_bounded b;
  U64.uint_to_t (E.be_to_n b)

let decode_u64_injective'
  (b1: bytes { Seq.length b1 == 8 } )
  (b2: bytes { Seq.length b2 == 8 } )
: Lemma
  (decode_u64 b1 == decode_u64 b2 ==> Seq.equal b1 b2)
= if decode_u64 b1 = decode_u64 b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U64.v (U64.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U64.v (U64.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    E.be_to_n_inj b1 b2
  end else ()

let decode_u64_injective () : Lemma
  (make_total_constant_size_parser_precond 8 U64.t decode_u64)
= Classical.forall_intro_2 decode_u64_injective'

let parse_u64 =
  decode_u64_injective ();
  make_total_constant_size_parser 8 U64.t decode_u64

let parse_u64_spec
  b
= E.lemma_be_to_n_is_bounded (Seq.slice b 0 8)

let serialize_u64 =
  (fun (x: U64.t) -> E.n_to_be 8 (U64.v x))

let decode_u64_le
  (b: bytes { Seq.length b == 8 } )
: GTot U64.t
= E.lemma_le_to_n_is_bounded b;
  U64.uint_to_t (E.le_to_n b)

let decode_u64_le_injective'
  (b1: bytes { Seq.length b1 == 8 } )
  (b2: bytes { Seq.length b2 == 8 } )
: Lemma
  (decode_u64_le b1 == decode_u64_le b2 ==> Seq.equal b1 b2)
= if decode_u64_le b1 = decode_u64_le b2
  then begin
    E.lemma_le_to_n_is_bounded b1;
    E.lemma_le_to_n_is_bounded b2;
    assert (U64.v (U64.uint_to_t (E.le_to_n b1)) == E.le_to_n b1);
    assert (U64.v (U64.uint_to_t (E.le_to_n b2)) == E.le_to_n b2);
    assert (E.le_to_n b1 == E.le_to_n b2);
    E.le_to_n_inj b1 b2
  end else ()

let decode_u64_le_injective () : Lemma
  (make_total_constant_size_parser_precond 8 U64.t decode_u64_le)
= Classical.forall_intro_2 decode_u64_le_injective'

let parse_u64_le =
  decode_u64_le_injective ();
  make_total_constant_size_parser 8 U64.t decode_u64_le

let parse_u64_le_spec
  b
= E.lemma_le_to_n_is_bounded (Seq.slice b 0 8)

let serialize_u64_le =
  (fun (x: U64.t) -> E.n_to_le 8 (U64.v x))

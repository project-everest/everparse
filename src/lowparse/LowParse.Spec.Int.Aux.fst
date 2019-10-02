module LowParse.Spec.Int.Aux
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

let parse_u8_kind : parser_kind = total_constant_size_parser_kind 1

let decode_u8
  (b: bytes { Seq.length b == 1 } )
: GTot U8.t
= Seq.index b 0

let decode_u8_injective () : Lemma
  (make_total_constant_size_parser_precond 1 U8.t decode_u8)
= ()

let parse_u8: parser parse_u8_kind U8.t =
  decode_u8_injective ();
  make_total_constant_size_parser 1 U8.t decode_u8

let parse_u8_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 1))
  (ensures (
    let pp = parse parse_u8 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U8.v v == E.be_to_n (Seq.slice b 0 1)
  )))
= ()

let serialize_u8 : serializer parse_u8 =
  Seq.create 1

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

inline_for_extraction
let parse_u16_kind : parser_kind =
  total_constant_size_parser_kind 2

#set-options "--z3rlimit 16"

let parse_u16: parser parse_u16_kind U16.t =
  decode_u16_injective ();
  let p =
    make_total_constant_size_parser 2 U16.t decode_u16
  in
  p

let parse_u16_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 2))
  (ensures (
    let pp = parse parse_u16 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U16.v v == E.be_to_n (Seq.slice b 0 2)
  )))
= let pp = parse parse_u16 b in
  assert (Some? pp);
  let (Some (v, _)) = pp in
  let s = Seq.slice b 0 2 in
  assert (v == decode_u16 s);
  E.lemma_be_to_n_is_bounded s;
  ()

#set-options "--z3rlimit 64"

let serialize_u16 : serializer parse_u16 =
  (fun (x: U16.t) -> E.n_to_be 2ul (U16.v x))

#reset-options

let serialize_u16_eq (x: U16.t) : Lemma
  (serialize #_ #_ #parse_u16 serialize_u16 x `Seq.equal` (
    let b1 = U8.uint_to_t (U16.v x % 256) in
    let d0 = U16.v x / 256 in
    let b0 = U8.uint_to_t (d0 % 256) in
    Seq.append (Seq.create 1 b0) (Seq.create 1 b1)
  ))
= ()

let decode_u32
  (b: bytes { Seq.length b == 4 } )
: GTot U32.t
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

#set-options "--z3rlimit 16"

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

#reset-options

let decode_u32_injective () : Lemma
  (make_total_constant_size_parser_precond 4 U32.t decode_u32)
= Classical.forall_intro_2 decode_u32_injective'

let parse_u32_kind : parser_kind =
  total_constant_size_parser_kind 4

let parse_u32: parser parse_u32_kind U32.t =
  decode_u32_injective ();
  make_total_constant_size_parser 4 U32.t decode_u32

#set-options "--z3rlimit 16"

let parse_u32_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 4))
  (ensures (
    let pp = parse parse_u32 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U32.v v == E.be_to_n (Seq.slice b 0 4)
  )))
= let pp = parse parse_u32 b in
  assert (Some? pp);
  let (Some (v, _)) = pp in
  let s = Seq.slice b 0 4 in
  assert (v == decode_u32 s);
  E.lemma_be_to_n_is_bounded s;
  ()

#set-options "--z3rlimit 128"

let serialize_u32 : serializer parse_u32 =
  (fun (x: U32.t) -> E.n_to_be 4ul (U32.v x))

#reset-options

let decode_u64
  (b: bytes { Seq.length b == 8 } )
: GTot U64.t
= E.lemma_be_to_n_is_bounded b;
  U64.uint_to_t (E.be_to_n b)

#push-options "--max_fuel 9 --initial_fuel 9 --z3rlimit 32"

let decode_u64_eq
  (b: bytes { Seq.length b == 8 } )
: Lemma
  (U64.v (decode_u64 b) ==
    U8.v (Seq.index b 7) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 6) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 5) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 4) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 3) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 2) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 1) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 0)
  ))))))))
= assert_norm (pow2 8 == 256);
  E.lemma_be_to_n_is_bounded b;
  FStar.Math.Lemmas.pow2_le_compat 64 (8 `FStar.Mul.op_Star` 8)

#pop-options

#set-options "--z3rlimit 16"

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

#reset-options

let decode_u64_injective () : Lemma
  (make_total_constant_size_parser_precond 8 U64.t decode_u64)
= Classical.forall_intro_2 decode_u64_injective'

let parse_u64_kind : parser_kind =
  total_constant_size_parser_kind 8

let parse_u64: parser parse_u64_kind U64.t =
  decode_u64_injective ();
  make_total_constant_size_parser 8 U64.t decode_u64

#set-options "--z3rlimit 16"

let parse_u64_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 8))
  (ensures (
    let pp = parse parse_u64 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U64.v v == E.be_to_n (Seq.slice b 0 8)
  )))
= let pp = parse parse_u64 b in
  assert (Some? pp);
  let (Some (v, _)) = pp in
  let s = Seq.slice b 0 8 in
  assert (v == decode_u64 s);
  E.lemma_be_to_n_is_bounded s;
  ()

#set-options "--z3rlimit 128"

let serialize_u64 : serializer parse_u64 =
  (fun (x: U64.t) ->
    E.n_to_be 8ul (U64.v x)
  )

#reset-options

#push-options "--max_fuel 9 --initial_fuel 9 --z3rlimit 1024"

let serialize_u64_eq
  (x: U64.t)
  (i: nat {i < 8 })
: Lemma
  (U8.v (Seq.index (serialize serialize_u64 x) i) == (
    let rem7 = U64.v x % 256 in
    let div7 = U64.v x / 256 in
    let rem6 = div7 % 256 in
    let div6 = div7 / 256 in
    let rem5 = div6 % 256 in
    let div5 = div6 / 256 in
    let rem4 = div5 % 256 in
    let div4 = div5 / 256 in
    let rem3 = div4 % 256 in
    let div3 = div4 / 256 in
    let rem2 = div3 % 256 in
    let div2 = div3 / 256 in
    let rem1 = div2 % 256 in
    let div1 = div2 / 256 in
    let rem0 = div1 % 256 in
    if i = 0
    then rem0
    else if i = 1
    then rem1
    else if i = 2
    then rem2
    else if i = 3
    then rem3
    else if i = 4
    then rem4
    else if i = 5
    then rem5
    else if i = 6
    then rem6
    else rem7
  ))
= assert_norm (pow2 8 == 256)

#pop-options

let decode_u64_le
  (b: bytes { Seq.length b == 8 } )
: GTot U64.t
= E.lemma_le_to_n_is_bounded b;
  U64.uint_to_t (E.le_to_n b)

#push-options "--max_fuel 9 --initial_fuel 9 --z3rlimit 32"

let decode_u64_le_eq
  (b: bytes { Seq.length b == 8 } )
: Lemma
  (U64.v (decode_u64_le b) ==
    U8.v (Seq.index b 0) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 1) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 2) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 3) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 4) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 5) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 6) + 256 `FStar.Mul.op_Star` (
    U8.v (Seq.index b 7)
  ))))))))
= assert_norm (pow2 8 == 256);
  E.lemma_le_to_n_is_bounded b;
  FStar.Math.Lemmas.pow2_le_compat 64 (8 `FStar.Mul.op_Star` 8)

#pop-options

#set-options "--z3rlimit 16"

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

#reset-options

let decode_u64_le_injective () : Lemma
  (make_total_constant_size_parser_precond 8 U64.t decode_u64_le)
= Classical.forall_intro_2 decode_u64_le_injective'

let parse_u64_le: parser parse_u64_kind U64.t =
  decode_u64_le_injective ();
  make_total_constant_size_parser 8 U64.t decode_u64_le

#set-options "--z3rlimit 16"

let parse_u64_le_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 8))
  (ensures (
    let pp = parse parse_u64_le b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U64.v v == E.le_to_n (Seq.slice b 0 8)
  )))
= let pp = parse parse_u64_le b in
  assert (Some? pp);
  let (Some (v, _)) = pp in
  let s = Seq.slice b 0 8 in
  assert (v == decode_u64_le s);
  E.lemma_le_to_n_is_bounded s;
  ()

#set-options "--z3rlimit 128"

let serialize_u64_le : serializer parse_u64_le =
  (fun (x: U64.t) ->
    E.n_to_le 8ul (U64.v x)
  )

#reset-options

#push-options "--max_fuel 9 --initial_fuel 9 --z3rlimit 512"

let serialize_u64_le_eq
  (x: U64.t)
  (i: nat {i < 8 })
: Lemma
  (U8.v (Seq.index (serialize serialize_u64_le x) i) == (
    let rem0 = U64.v x % 256 in
    let div0 = U64.v x / 256 in
    let rem1 = div0 % 256 in
    let div1 = div0 / 256 in
    let rem2 = div1 % 256 in
    let div2 = div1 / 256 in
    let rem3 = div2 % 256 in
    let div3 = div2 / 256 in
    let rem4 = div3 % 256 in
    let div4 = div3 / 256 in
    let rem5 = div4 % 256 in
    let div5 = div4 / 256 in
    let rem6 = div5 % 256 in
    let div6 = div5 / 256 in
    let rem7 = div6 % 256 in
    if i = 0
    then rem0
    else if i = 1
    then rem1
    else if i = 2
    then rem2
    else if i = 3
    then rem3
    else if i = 4
    then rem4
    else if i = 5
    then rem5
    else if i = 6
    then rem6
    else rem7
  ))
= assert_norm (pow2 8 == 256)

#pop-options

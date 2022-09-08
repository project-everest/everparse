module LowParse.Spec.BoundedInt

open LowParse.Spec.Combinators // for make_total_constant_size_parser_precond

module Seq = FStar.Seq
module E = FStar.Endianness
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module M = LowParse.Math
module Cast = FStar.Int.Cast

(* bounded integers *)

let integer_size_values i = ()

let bounded_integer_prop_equiv
  (i: integer_size)
  (u: U32.t)
: Lemma
  (bounded_integer_prop i u <==> U32.v u < pow2 (8 * i))
= 
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296)

#push-options "--z3rlimit 16"

let decode_bounded_integer
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: GTot (bounded_integer i)
= E.lemma_be_to_n_is_bounded b;
  M.pow2_le_compat 32 (8 `FStar.Mul.op_Star` i);
  U32.uint_to_t (E.be_to_n b)

let decode_bounded_integer_injective'
  (i: integer_size)
  (b1: bytes { Seq.length b1 == i } )
  (b2: bytes { Seq.length b2 == i } )
: Lemma
  (decode_bounded_integer i b1 == decode_bounded_integer i b2 ==> Seq.equal b1 b2)
= if decode_bounded_integer i b1 = decode_bounded_integer i b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    E.be_to_n_inj b1 b2
  end else ()

let decode_bounded_integer_injective
  (i: integer_size)
: Lemma
  (make_total_constant_size_parser_precond i (bounded_integer i) (decode_bounded_integer i))
= Classical.forall_intro_2 (decode_bounded_integer_injective' i)

let parse_bounded_integer
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))
= decode_bounded_integer_injective i;
  make_total_constant_size_parser i (bounded_integer i) (decode_bounded_integer i)

let parse_bounded_integer_spec i input =
  parser_kind_prop_equiv (parse_bounded_integer_kind i) (parse_bounded_integer i);
  M.pow2_le_compat 32 (8 `FStar.Mul.op_Star` i);
  match parse (parse_bounded_integer i) input with
  | None -> ()
  | Some (y, consumed) ->
    let input' = Seq.slice input 0 i in
    E.lemma_be_to_n_is_bounded input';
    parse_strong_prefix (parse_bounded_integer i) input input'

let serialize_bounded_integer'
  (sz: integer_size)
: Tot (bare_serializer (bounded_integer sz))
= (fun (x: bounded_integer sz) ->
    let res = E.n_to_be sz (U32.v x) in
    res
  )

let serialize_bounded_integer_correct
  (sz: integer_size)
: Lemma
  (serializer_correct (parse_bounded_integer sz) (serialize_bounded_integer' sz))
= let prf
    (x: bounded_integer sz)
  : Lemma
    (
      let res = serialize_bounded_integer' sz x in
      Seq.length res == (sz <: nat) /\
      parse (parse_bounded_integer sz) res == Some (x, (sz <: nat))
    )
  = ()
  in
  Classical.forall_intro prf

let serialize_bounded_integer
sz
: Tot (serializer (parse_bounded_integer sz))
= serialize_bounded_integer_correct sz;
  serialize_bounded_integer' sz

let serialize_bounded_integer_spec sz x = ()

let bounded_integer_of_le
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: GTot (bounded_integer i)
= E.lemma_le_to_n_is_bounded b;
  M.pow2_le_compat 32 (8 `FStar.Mul.op_Star` i);
  U32.uint_to_t (E.le_to_n b)

let bounded_integer_of_le_injective'
  (i: integer_size)
  (b1: bytes { Seq.length b1 == i } )
  (b2: bytes { Seq.length b2 == i } )
: Lemma
  (bounded_integer_of_le i b1 == bounded_integer_of_le i b2 ==> Seq.equal b1 b2)
= if bounded_integer_of_le i b1 = bounded_integer_of_le i b2
  then begin
    E.lemma_le_to_n_is_bounded b1;
    E.lemma_le_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.le_to_n b1)) == E.le_to_n b1);
    assert (U32.v (U32.uint_to_t (E.le_to_n b2)) == E.le_to_n b2);
    assert (E.le_to_n b1 == E.le_to_n b2);
    E.le_to_n_inj b1 b2
  end else ()

#pop-options

let bounded_integer_of_le_injective
  (i: integer_size)
: Lemma
  (make_total_constant_size_parser_precond i (bounded_integer i) (bounded_integer_of_le i))
= Classical.forall_intro_2 (bounded_integer_of_le_injective' i)

let parse_bounded_integer_le
i
= bounded_integer_of_le_injective i;
  make_total_constant_size_parser i (bounded_integer i) (bounded_integer_of_le i)

inline_for_extraction
let synth_u16_le
  (x: bounded_integer 2)
: Tot U16.t
= Cast.uint32_to_uint16 x

let synth_u16_le_injective : squash (synth_injective synth_u16_le) = ()

let parse_u16_le = parse_bounded_integer_le 2 `parse_synth` synth_u16_le

inline_for_extraction
let synth_u32_le
  (x: bounded_integer 4)
: Tot U32.t
= x

let parse_u32_le = parse_bounded_integer_le 4 `parse_synth` synth_u32_le

let serialize_bounded_integer_le'
  (sz: integer_size)
: Tot (bare_serializer (bounded_integer sz))
= (fun (x: bounded_integer sz) ->
    E.n_to_le sz (U32.v x)
  )

#push-options "--z3rlimit 16"

let serialize_bounded_integer_le_correct
  (sz: integer_size)
: Lemma
  (serializer_correct (parse_bounded_integer_le sz) (serialize_bounded_integer_le' sz))
= let prf
    (x: bounded_integer sz)
  : Lemma
    (
      let res = serialize_bounded_integer_le' sz x in
      Seq.length res == (sz <: nat) /\
      parse (parse_bounded_integer_le sz) res == Some (x, (sz <: nat))
    )
  = ()
  in
  Classical.forall_intro prf

#pop-options

let serialize_bounded_integer_le
sz
= serialize_bounded_integer_le_correct sz;
  serialize_bounded_integer_le' sz

inline_for_extraction
let synth_u16_le_recip
  (x: U16.t)
: Tot (bounded_integer 2)
= Cast.uint16_to_uint32 x

let synth_u16_le_inverse : squash (synth_inverse synth_u16_le synth_u16_le_recip) = ()

let serialize_u16_le : serializer parse_u16_le =
  serialize_synth
    _
    synth_u16_le
    (serialize_bounded_integer_le 2)
    synth_u16_le_recip
    ()

inline_for_extraction
let synth_u32_le_recip
  (x: U32.t)
: Tot (bounded_integer 4)
= x

let serialize_u32_le =
  serialize_synth
    _
    synth_u32_le
    (serialize_bounded_integer_le 4)
    synth_u32_le_recip
    ()

let parse_bounded_int32
  min max
= let sz = log256' max in
  (parse_bounded_integer sz `parse_filter` in_bounds min max) `parse_synth` (fun x -> (x <: bounded_int32 min max))

let serialize_bounded_int32
  min max
= let sz = log256' max in
  serialize_synth
    (parse_bounded_integer sz `parse_filter` in_bounds min max)
    (fun x -> (x <: bounded_int32 min max))
    (serialize_filter (serialize_bounded_integer sz) (in_bounds min max))
    (fun x -> x)
    ()

let parse_bounded_int32_le
  min max
= let sz = log256' max in
  (parse_bounded_integer_le sz `parse_filter` in_bounds min max) `parse_synth` (fun x -> (x <: bounded_int32 min max))

let serialize_bounded_int32_le
  min max
= let sz = log256' max in
  serialize_synth
    (parse_bounded_integer_le sz `parse_filter` in_bounds min max)
    (fun x -> (x <: bounded_int32 min max))
    (serialize_filter (serialize_bounded_integer_le sz) (in_bounds min max))
    (fun x -> x)
    ()

let parse_bounded_int32_le_fixed_size
  min max
= parse_filter parse_u32_le (in_bounds min max)

let serialize_bounded_int32_le_fixed_size
  min max
= serialize_filter serialize_u32_le (in_bounds min max)

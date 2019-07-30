module LowParse.Spec.Int32le

(* LowParse specification module for parsing unconstrainted 32 bits = 4 bytes unsigned little endian integers

   Examples:

   uint32le foo

*)

include FStar.Endianness

include LowParse.Spec.Base
include LowParse.Spec.Combinators

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq
module M = LowParse.Math

let decode_int32le
  (b: bytes { Seq.length b == 4 } )
: Tot (v: U32.t { 0 <= U32.v v /\ U32.v v < 4294967296 } )
= lemma_le_to_n_is_bounded b;
  M.pow2_le_compat 32 32;
  let res = le_to_n b in
  assert (0 <= res /\ res < 4294967296);
  U32.uint_to_t res

let decode_int32le_injective
  (b1 : bytes { Seq.length b1 == 4 } )
  (b2 : bytes { Seq.length b2 == 4 } )
: Lemma (decode_int32le b1 == decode_int32le b2
        ==>
        b1 == b2)
= if (decode_int32le b1) = (decode_int32le b2) then
  begin
    lemma_le_to_n_is_bounded b1;
    lemma_le_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (le_to_n b1)) == le_to_n b1);
    assert (U32.v (U32.uint_to_t (le_to_n b2)) == le_to_n b2);
    assert (le_to_n b1 == le_to_n b2);
    le_to_n_inj b1 b2
  end
  else
    ()

let decode_int32le_total_constant () : Lemma (make_total_constant_size_parser_precond 4 U32.t decode_int32le)
= Classical.forall_intro_2 decode_int32le_injective
  
let parse_int32le : parser (total_constant_size_parser_kind 4) U32.t
= decode_int32le_total_constant () ;
  make_total_constant_size_parser 4 U32.t decode_int32le

let serialize_int32le : serializer parse_int32le
= fun (x : U32.t) -> n_to_le 4 (U32.v x)

(* lemmas for inplace comparison in validators *)

let le_to_n_0_eq
  (b : bytes { Seq.length b == 0 } )
: Lemma (le_to_n b == 0)
= reveal_le_to_n b

let le_to_n_1_eq
  (b : bytes { Seq.length b == 1 } )
: Lemma (le_to_n b == 
    U8.v (Seq.index b 0))
= assert_norm (pow2 8 == 256);
  reveal_le_to_n b;
  le_to_n_0_eq (Seq.tail b)

let le_to_n_2_eq
  (b : bytes { Seq.length b == 2 } )
: Lemma (le_to_n b == 
    U8.v (Seq.index b 0) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 1)))
= assert_norm (pow2 8 == 256);
  reveal_le_to_n b;
  le_to_n_1_eq (Seq.tail b)

let le_to_n_3_eq
  (b : bytes { Seq.length b == 3 } )
: Lemma (le_to_n b == 
    U8.v (Seq.index b 0) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 1) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 2))))
= assert_norm (pow2 8 == 256);
  reveal_le_to_n b;
  le_to_n_2_eq (Seq.tail b)

let le_to_n_4_eq
  (b : bytes { Seq.length b == 4 } )
: Lemma (le_to_n b == 
    U8.v (Seq.index b 0) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 1) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 2) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 3)))))
= assert_norm (pow2 8 == 256);
  reveal_le_to_n b;
  le_to_n_3_eq (Seq.tail b)

let decode_int32le_eq
  (b : bytes { Seq.length b == 4 } )
: Lemma
  (U32.v (decode_int32le b) ==
    U8.v (Seq.index b 0) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 1) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 2) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 3)))))
= lemma_le_to_n_is_bounded b;
  assert (U32.v (decode_int32le b) == le_to_n b);
  le_to_n_4_eq b


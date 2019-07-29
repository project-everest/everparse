module LowParse.Spec.ConstInt32

(* LowParse specification module for parsing 32 bits = 4 bytes constants

   Examples:

   uint32 foo = 5
   uint32_le foo = 7

*)

include FStar.Endianness

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.BoundedInt

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq
module M = LowParse.Math

let constint32
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot Type0
= (u: U32.t { U32.v u == v } )

inline_for_extraction
let parse_constint32le_kind
: parser_kind
= strong_parser_kind 4 4 None

let decode_int32_le
  (b: bytes { Seq.length b == 4 } )
: Tot (v: U32.t { 0 <= U32.v v /\ U32.v v < 4294967296 } )
= lemma_le_to_n_is_bounded b;
  M.pow2_le_compat 32 32;
  let res = le_to_n b in
  assert (0 <= res /\ res < 4294967296);
  U32.uint_to_t res

let decode_int32_le_injective
  (b1 : bytes { Seq.length b1 == 4 } )
  (b2 : bytes { Seq.length b2 == 4 } )
: Lemma (decode_int32_le b1 == decode_int32_le b2
        ==>
        b1 == b2)
= if (decode_int32_le b1) = (decode_int32_le b2) then
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

let decode_int32_le_total_constant () : Lemma (make_total_constant_size_parser_precond 4 U32.t decode_int32_le)
= Classical.forall_intro_2 decode_int32_le_injective

let parse_int32_le () : Tot (parser (total_constant_size_parser_kind 4) U32.t)
= decode_int32_le_total_constant () ;
  make_total_constant_size_parser 4 U32.t decode_int32_le

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

let decode_int32_le_eq
  (b : bytes { Seq.length b == 4 } )
: Lemma
  (U32.v (decode_int32_le b) ==
    U8.v (Seq.index b 0) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 1) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 2) + 
    256 `FStar.Mul.op_Star` (U8.v (Seq.index b 3)))))
= lemma_le_to_n_is_bounded b;
  assert (U32.v (decode_int32_le b) == le_to_n b);
  le_to_n_4_eq b

let decode_constint32_le
  (v: nat {0 <= v /\ v < 4294967296 } )
  (b: bytes { Seq.length b == 4 } )
: Tot (option (constint32 v))
= let v' = decode_int32_le b in
    if U32.v v' = v then
      Some v'
    else
      None

let decode_constint32_le_injective'
  (v: nat { 0 <= v /\ v < 4294967296 } )
  (b1: bytes { Seq.length b1 == 4 } )
  (b2: bytes { Seq.length b2 == 4 } )
: Lemma
  ((Some? (decode_constint32_le v b1) \/ Some? (decode_constint32_le v b2))
   /\ (decode_constint32_le v b1 == decode_constint32_le v b2) 
   ==> Seq.equal b1 b2)
= let res1 = decode_constint32_le v b1 in
  let res2 = decode_constint32_le v b2 in
  match res1 with
  | Some v1 ->
    assert ( U32.v v1 == v );
    (match res2 with
    | Some v2 ->
      assert ( U32.v v2 == v );
      assert ( v1 == v2 );
      decode_int32_le_injective b1 b2
    | None -> ())
  | None -> ()

let decode_constint32_le_injective
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Lemma
  (make_constant_size_parser_precond 4 (constint32 v) (decode_constint32_le v))
= Classical.forall_intro_2 (decode_constint32_le_injective' v)

let parse_constint32le
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (parser parse_constint32le_kind (constint32 v))
= decode_constint32_le_injective v;
  make_constant_size_parser 4 (constint32 v) (decode_constint32_le v)

let parse_constint32le_unfold
  (v: nat { 0 <= v /\ v < 4294967296 } )
  (input: bytes)
: Lemma 
  (parse (parse_constint32le v) input ==
  (let res = parse (parse_int32_le ()) input in
     match res with
     | Some (x, consumed) ->
       if U32.v x = v && consumed = 4 then
         Some (x, consumed)
       else
         None
     | None -> None))
= let res = parse (parse_int32_le ()) input in
    match res with
    | Some (x, consumed) ->
      if U32.v x = v && consumed = 4 then
        ()
      else
        ()
    | None -> ()

let serialize_constint32le'
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (bare_serializer (constint32 v))
= fun (x: constint32 v) -> 
  let res = n_to_le 4 v in
  res

let serialize_constint32le_correct
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Lemma
  (serializer_correct (parse_constint32le v) (serialize_constint32le' v))
= let prf
    (x: constint32 v)
  : Lemma 
    (let res = n_to_le 4 v in
     U32.v x == v /\ Seq.length res == 4 /\ (parse (parse_constint32le v) res == Some (x, 4)))
  = ()
  in
  Classical.forall_intro prf

let serialize_constint32le
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (serializer (parse_constint32le v))
= serialize_constint32le_correct v;
  serialize_constint32le' v


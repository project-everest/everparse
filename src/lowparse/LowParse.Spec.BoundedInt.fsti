module LowParse.Spec.BoundedInt
include LowParse.Spec.Base
include LowParse.Spec.Int // for parse_u16_kind

module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian

(* bounded integers *)

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

val integer_size_values (i: integer_size) : Lemma
  (i == 1 \/ i == 2 \/ i == 3 \/ i == 4)

let bounded_integer_prop
  (i: integer_size)
  (u: U32.t)
: GTot Type0
= U32.v u < (match i with 1 -> 256 | 2 -> 65536 | 3 -> 16777216 | 4 -> 4294967296)

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: U32.t { bounded_integer_prop i u } )

inline_for_extraction
let parse_bounded_integer_kind
  (i: integer_size)
: Tot parser_kind
= total_constant_size_parser_kind i

val parse_bounded_integer
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))

val parse_bounded_integer_spec
  (i: integer_size)
  (input: bytes)
: Lemma
  (let res = parse (parse_bounded_integer i) input in
   if Seq.length input < i
   then res == None
   else
     match res with
     | None -> False
     | Some (y, consumed) ->
       U32.v y == E.be_to_n (Seq.slice input 0 i) /\ consumed == i
  )

val serialize_bounded_integer
  (sz: integer_size)
: Tot (serializer (parse_bounded_integer sz))

val serialize_bounded_integer_spec
  (sz: integer_size)
  (x: bounded_integer sz)
: Lemma
  (serialize (serialize_bounded_integer sz) x == E.n_to_be'' sz (U32.v x))

val parse_bounded_integer_le
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))

val parse_u16_le : parser parse_u16_kind U16.t

val parse_u32_le : parser parse_u32_kind U32.t

val serialize_bounded_integer_le
  (sz: integer_size)
: Tot (serializer (parse_bounded_integer_le sz))

val serialize_u16_le : serializer parse_u16_le

val serialize_u32_le : serializer parse_u32_le

inline_for_extraction
let log256'
  (n: nat)
: Pure integer_size
  (requires (n > 0 /\ n < 4294967296))
  (ensures (fun l ->
    pow2 (FStar.Mul.op_Star 8 (l - 1)) <= n /\
    n < pow2 (FStar.Mul.op_Star 8 l)
  ))
= [@inline_let]
  let _ = assert_norm (pow2 32 == 4294967296) in
  [@inline_let]
  let _ = assert (n < pow2 32) in
  [@inline_let]
  let z0 = 1 in
  [@inline_let]
  let z1 = 256 in
  [@inline_let]
  let _ = assert_norm (z1 == Prims.op_Multiply 256 z0) in
  [@inline_let]
  let l = 1 in
  [@inline_let]
  let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z1) in
  [@inline_let]
  let _ = assert_norm (pow2 (Prims.op_Multiply 8 (l - 1)) == z0) in
  if n < z1
  then begin
    [@inline_let]
    let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
    [@inline_let]
    let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
    l
  end else begin
    [@inline_let]
    let z2 = 65536 in
    [@inline_let]
    let _ = assert_norm (z2 == Prims.op_Multiply 256 z1) in
    [@inline_let]
    let l = 2 in
    [@inline_let]
    let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z2) in
    if n < z2
    then begin
      [@inline_let]
      let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
      [@inline_let]
      let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
      l
    end else begin
      [@inline_let]
      let z3 = 16777216 in
      [@inline_let]
      let _ = assert_norm (z3 == Prims.op_Multiply 256 z2) in
      [@inline_let]
      let l = 3 in
      [@inline_let]
      let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z3) in
      if n < z3
      then begin
        [@inline_let]
	let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
        [@inline_let]
	let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
        l    
      end else begin
        [@inline_let]
        let l = 4 in
        [@inline_let]
        let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == Prims.op_Multiply 256 z3) in
        [@inline_let]
	let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
        [@inline_let]
	let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
        l
      end
    end
  end

let in_bounds
  (min: nat)
  (max: nat)
  (x: U32.t)
: GTot bool
= not (U32.v x < min || max < U32.v x)

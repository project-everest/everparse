module LowParse.Low.ConstInt32

(* LowParse implementation module for 32 bits contants *)

include FStar.Endianness

include LowParse.Spec.ConstInt32
include LowParse.Low.Combinators

include LowParse.Low.BoundedInt

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

let valid_constint32le
  (v: nat { 0 <= v /\ v < 4294967296 } )
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma (valid (parse_constint32le v) h input pos 
    <==> 
    (valid (parse_int32_le ()) h input pos /\
    U32.v (contents (parse_int32_le ()) h input pos) == v))
= valid_facts (parse_constint32le v) h input pos;
  valid_facts (parse_int32_le ()) h input pos;
  parse_constint32le_unfold v (bytes_of_slice_from h input pos)

let read_int32_le : (leaf_reader (parse_int32_le ()))
= make_total_constant_size_reader 4 4ul decode_int32_le (decode_int32_le_total_constant ()) (fun #rrel #rel b pos ->
    let h = HST.get () in
    [@inline_let] let _ = decode_int32_le_eq (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 4)) in
    let r0 = B.index b pos in
    let r1 = B.index b (pos `U32.add` 1ul) in
    let r2 = B.index b (pos `U32.add` 2ul) in
    let r3 = B.index b (pos `U32.add` 3ul) in
    Cast.uint8_to_uint32 r0 `U32.add` (256ul `U32.mul` (Cast.uint8_to_uint32 r1 `U32.add` (256ul `U32.mul` (Cast.uint8_to_uint32 r2 `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 r3)))))
  )


let validate_constint32le_slow
  (v: U32.t { 0 <= U32.v v /\ U32.v v < 4294967296 } )
: Tot (validator (parse_constint32le (U32.v v)))
= fun #rrel #rel (input: slice rrel rel) (pos: U32.t) ->
  let h = HST.get() in
    let _ =
      valid_constint32le (U32.v v) h input pos;    
      valid_equiv (parse_int32_le ()) h input pos
    in
  if U32.lt (input.len `U32.sub` pos) 4ul
  then
    validator_error_not_enough_data
  else
    let v' = read_int32_le input pos in
    if U32.eq v v' then
      pos `U32.add` 4ul
    else
      validator_error_generic


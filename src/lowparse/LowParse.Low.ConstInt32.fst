module LowParse.Low.ConstInt32

(* LowParse implementation module for 32 bits contants *)

include FStar.Endianness

include LowParse.Spec.ConstInt32

include LowParse.Low.BoundedInt

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

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

let read_int32_le : unit -> Tot (leaf_reader (parse_int32_le ()))
= read_bounded_integer_le_4

(*
let validate_constint32le_slow
  (v: U32.t { 0 <= U32.v v /\ U32.v v < 4294967296 } )
: Tot (validator (parse_constint32le (U32.v v)))
= fun #rrel #rel (input: slice rrel rel) (pos: U32.t) ->
  let h = HST.get() in
    let _ =
      valid_equiv (parse_constint32le (U32.v v)) h input pos;
      valid_constint32le (U32.v v) h input pos    
    in
  if U32.lt (input.len `U32.sub` pos) 4ul
  then
    validator_error_not_enough_data
  else
    let v' = read_bounded_integer_le_4 input pos in
    if U32.eq v v' then
      pos `U32.add` 4ul
    else
      validator_error_generic
*)

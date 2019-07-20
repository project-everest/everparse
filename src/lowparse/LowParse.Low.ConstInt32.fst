module LowParse.Low.ConstInt32

(* LowParse implementation module for 32 bits contants *)

include FStar.Endianness

include LowParse.Spec.ConstInt32

include LowParse.Low.BoundedInt

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*
let valid_constint32le
  (v: nat { 0 <= v /\ v < 4294967276 } )
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma (valid (parse_constint32le v) h input pos 
    <==> 
    (live_slice h input /\ 
    U32.v input.len - U32.v pos >= 4 /\
    U32.v (contents (parse_constint32le v) h input pos) == v))
= valid_facts (parse_constint32le v) h input pos
*)

#push-options "--z3rlimit 40"

let validate_constint32le
  (v: U32.t)
: Tot (validator (parse_constint32le (U32.v v)))
= fun #rrel #rel (input: slice rrel rel) (pos: U32.t) ->
  let h = HST.get() in
    let _ = valid_equiv (parse_constint32le (U32.v v)) h input pos in
  if U32.lt (input.len `U32.sub` pos) 4ul
  then
    validator_error_not_enough_data
  else
    let v' = read_bounded_integer_le_4 input pos in
    if U32.eq v v' then
      pos `U32.add` 4ul
    else
      validator_error_generic
   
#pop-options

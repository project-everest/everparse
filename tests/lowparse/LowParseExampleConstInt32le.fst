module LowParseExampleConstInt32le

(* Unit test for LowParse.Spec.ConstInt32 LowParse.Low.ConstInt32

   Example:

   uint32 a(5)
   uint32 b(2147483647)

   Contents:

   extractable validator
*)

include LowParse.Spec.ConstInt32
include LowParse.Low.ConstInt32

include LowParse.Spec.Bytes
include LowParse.Low.Bytes

module B32 = FStar.Bytes
module U32 = FStar.UInt32

(* Validator *)

inline_for_extraction
let unit_test_constint32le_a_validator_slow : validator (parse_constint32le 5)
= fun #rrel #rel input pos ->
    validate_constint32le_slow 5ul input pos

inline_for_extraction
let unit_test_constint32le_a_validator : validator (parse_constint32le 5)
= fun #rrel #rel input pos ->
    validate_constint32le 5ul input pos

inline_for_extraction
let unit_test_constint32le_a_reader : leaf_reader (parse_constint32le 5)
= fun #rrel #rel input pos ->
    read_constint32le 5ul input pos

inline_for_extraction
let unit_test_constint32le_b_validator_slow : validator (parse_constint32le 2147483647)
= fun #rrel #rel input pos ->
    validate_constint32le_slow 2147483647ul input pos

inline_for_extraction
let unit_test_constint32le_b_validator : validator (parse_constint32le 2147483647)
= fun #rrel #rel input pos ->
    validate_constint32le 2147483647ul input pos

inline_for_extraction
let unit_test_constint32le_b_reader : leaf_reader (parse_constint32le 2147483647)
= fun #rrel #rel input pos ->
    read_constint32le 2147483647ul input pos

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)

let main _ _ = C.EXIT_SUCCESS


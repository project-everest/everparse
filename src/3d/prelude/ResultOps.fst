module ResultOps
module U64 = FStar.UInt64
module LPL = LowParse.Low.Base
module BF = LowParse.BitFields
let result = U64.t
let field_id = x:U64.t{ 0 < U64.v x /\ U64.v x < pow2 16}
let field_id_of_result (result:result) : U64.t =
  LowParse.Low.Base.get_validator_error_code result
let result_is_error(result:result) : bool =
  let open U64 in
  result >^ LPL.validator_max_length
let error_kind_of_result (result:result) : U64.t =
  LowParse.Low.Base.get_validator_error_kind result

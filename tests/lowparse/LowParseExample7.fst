module LowParseExample7

module Aux = LowParseExample7.Aux

val main: FStar.Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  C.EXIT_SUCCESS

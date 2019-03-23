module LowParseExample3
include LowParseExample3.Aux

open FStar.HyperStack.ST
open LowParse.TestLib.Low

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module Cast = FStar.Int.Cast

// #reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --using_facts_from '* -LowParse.Low.VLData'"

inline_for_extraction
let slice = LowParse.Low.slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _))

#set-options "--z3rlimit 32"

let dummy
  (input: slice)
  (which: U32.t)
: HST.Stack U32.t
  (requires (fun h -> live_slice h input /\ U32.v input.len <= U32.v validator_max_length))
  (ensures (fun _ _ _ -> True))
= HST.push_frame ();
  let res =
    if validate_t input 0ul `U32.lte` validator_max_length
    then
      if which = 42ul
      then
        let x : U16.t = read_u16 input (access_a input 0ul) in
        Cast.uint16_to_uint32 x
      else if which = 1729ul
      then
        read_u32 input (access_b input 0ul)
      else
        let x : U16.t = read_u16 input (access_c input 0ul) in
        Cast.uint16_to_uint32 x
    else 0ul
  in
  HST.pop_frame ();
  res

#reset-options "--using_facts_from '* -LowParse'"

(** Test parser 'f' and formatter 'm' *)
let test_f_m : testbuffer_t = fun #rrel #rel input ->
(* BUGBUG:  Complete this when low-level formatting is ready
  let result = f input in
  match result with
  | Some (v, offset) -> (
    let formattedresult = m v in
    Some (formattedresult, offset)
  )
  | _ -> None
*)
  None

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 16"

(** Run all unit tests, by calling test_buffer and test_file_buffer
    multiple times, with different parser+formatter pairs and 
    input data *)
let test (_:unit): ST unit (requires (fun _ -> true)) (ensures (fun _ _ _ -> true)) =
  push_frame();
  let testbuffer: B.buffer byte = B.alloca_of_list [ 0x01uy; 0x02uy; 0x55uy; 0xaauy; 0x34uy; 0x45uy; 0xbauy; 0xabuy ] in
  test_buffer test_f_m "Example3 expect fail" (make_slice testbuffer 8ul);
(*  
  test_file_buffer test_f_m "Example3_pass.bin";
  test_file_buffer test_f_m "Example3_fail.bin";  
*)
  pop_frame()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  HST.ST C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  test ();
  pop_frame ();
  C.EXIT_SUCCESS

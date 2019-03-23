module LowParse.TestLib.Low

open FStar.HyperStack.ST
open FStar.HyperStack.IO
open FStar.Printf
open LowParse.Low.Base

module B = LowStar.Buffer
module U32 = FStar.UInt32
module M = LowStar.Modifies

#reset-options "--using_facts_from '* -LowParse'"
#reset-options "--z3cliopt smt.arith.nl=false"

(** The type of a unit test.  It takes an input buffer8, parses it,
    and returns a newly formatted buffer8.  Or it returns None if
    there is a fail to parse. *)
type testbuffer_t = (input: slice) -> ST (option slice) 
  (requires(fun h -> live_slice h input))
  (ensures(fun h0 y h1 ->
    M.modifies M.loc_none h0 h1 /\ (
    match y with
    | None -> true
    | Some out ->
      B.unused_in out.base h0 /\
      live_slice h1 out
  )))

assume val load_file_buffer: (filename:string) -> ST slice
  (requires (fun h -> True))
  (ensures (fun h out h' ->
    M.modifies M.loc_none h h' /\ B.unused_in out.base h /\ live_slice h' out
  ))

(* TODO: implement in LowStar.Buffer *)

module U32 = FStar.UInt32

(** Corresponds to memcmp for `eqtype` *)
assume
val beqb: b1:buffer8 -> b2:buffer8
  -> len:U32.t{U32.v len <= B.length b1 /\ U32.v len <= B.length b2}
  -> Stack bool
    (requires (fun h ->
      B.live h b1 /\
      B.live h b2
    ))
    (ensures  (fun h0 z h1 -> h1 == h0 /\
      (z <==> Seq.equal (B.as_seq h0 (B.gsub b1 0ul len)) (B.as_seq h0 (B.gsub b2 0ul len)))))

(** Test one parser+formatter pair against an in-memory buffer of UInt8.t *)
let test_buffer (t:testbuffer_t) (testname:string) (input:slice)
: ST unit 
(requires (fun h -> live_slice h input))
(ensures (fun _ _ _ -> true)) =
  push_frame();
  print_string (sprintf "==== Testing buffer %s ====\n" testname);
  let result = t input in
  (match result with
  | Some output -> (
    if U32.lte output.len input.len then (
      if beqb input.base output.base output.len then
        print_string "Formatted data matches original input data\n"
      else (
        print_string "FAIL:  formatted data does not match original input data\n"
      )
    ) else (  
      print_string "Invalid length return - it is longer than the input buffer!"
    ))
  | _ -> print_string "Failed to parse\n"
  ); 
  print_string (sprintf "==== Finished %s ====\n" testname);
  pop_frame()

(** Test one parser+formatter pair against a disk file, using buffer *)
let test_file_buffer (t:testbuffer_t) (filename:string): ST unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let input = load_file_buffer filename in
  (*test_buffer t filename input inputlen;*)
  pop_frame()

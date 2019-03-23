module LowParse.TestLib.SLow

open FStar.HyperStack.ST
open FStar.Bytes
open FStar.HyperStack.IO
open FStar.Printf

module U32 = FStar.UInt32

#reset-options "--using_facts_from '* -LowParse'"
#reset-options "--z3cliopt smt.arith.nl=false"

(** The type of a unit test.  It takes an input Bytes, parses it,
    and returns a newly formatted Bytes.  Or it returns None if
    there is a fail to parse. *)
type test_t = (input:FStar.Bytes.bytes) -> Stack (option (FStar.Bytes.bytes * U32.t)) (fun _ -> true) (fun _ _ _ -> true)

assume val load_file: (filename:string) -> Tot FStar.Bytes.bytes

(** Test one parser+formatter pair against an in-memory buffer of Bytes *)
let test_bytes (t:test_t) (testname:string) (input:FStar.Bytes.bytes): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  print_string (sprintf "==== Testing Bytes %s ====\n" testname);
  let result = t input in
  (match result with
  | Some (formattedresult, offset) -> (
    if U32.gt offset (len input) then (
      print_string "Invalid length return - it is longer than the input buffer!"
    ) else (  
      let inputslice = FStar.Bytes.slice input 0ul offset in
      if formattedresult = inputslice then
        print_string "Formatted data matches original input data\n"
      else (
        print_string "FAIL:  formatted data does not match original input data\n"
      )
    )
    )
  | _ -> print_string "Failed to parse\n"
  ); 
  print_string (sprintf "==== Finished %s ====\n" testname);
  pop_frame()

(** Test one parser+formatter pair against a string of hex bytes, as Bytes *)
let test_string (t:test_t) (testname:string) (inputstring:string): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let input = bytes_of_hex inputstring in
  test_bytes t testname input;
  pop_frame()
  
(** Test one parser+formatter pair against a disk file, as Bytes *)
let test_file (t:test_t) (filename:string): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let input = load_file filename in
  test_bytes t filename input;
  pop_frame()

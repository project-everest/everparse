module Runtest

open FStar.HyperStack.ST
open FStar.HyperStack.IO
open C
open C.String
open FStar.Bytes
module LB = LowStar.Buffer
module LPL = LowParse.Low.Base

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let bprint s = discard (FStar.IO.debug_print_string (s^"\n"))

let from_bytes (b:bytes{length b <> 0}) : StackInline (LB.buffer LPL.byte)
  (requires (fun h0 -> True))
  (ensures  (fun h0 buf h1 ->
    LB.(modifies loc_none h0 h1) /\
    LB.live h1 buf /\ LB.unused_in buf h0 /\
    LB.length buf = length b /\
    reveal b `Seq.equal` LB.as_seq h1 buf))
  =
  let h0 = FStar.HyperStack.ST.get () in
  let lb = LB.alloca 0uy (len b) in
  store_bytes b lb;
  let h1 = FStar.HyperStack.ST.get () in
  LB.(modifies_only_not_unused_in loc_none h0 h1);
  lb

let test_student () : St bool =
  push_frame();
  let raw = bytes_of_hex "123456789a0000000000000000000000000000000000000000" in
  let open FStar.UInt32 in
  let open FStar.Bytes in
  assume (length raw > 0 /\ length raw < v LowParse.Low.Base.validator_max_length);
  let lb = from_bytes raw in
  let slice = LPL.make_slice lb (len raw) in
  let res =
  if Student.student_validator slice 0ul >^ LPL.validator_max_length then
    (print !$"Validator failed on student raw data!\n"; false)
  else
    let pos_random = Student.accessor_student_name slice 0ul in
    let p_random = LB.sub lb pos_random 20ul in
    bprint (" The student name is: " ^(hex_of_bytes (of_buffer 20ul p_random))); true
  in
  pop_frame();
  res


let test_zeroarg () : St C.exit_code =
  let b = test_student() in
  if b then C.EXIT_SUCCESS else C.EXIT_FAILURE

let main
  (argc: Int32.t)
  (argv: LowStar.Buffer.buffer C.String.t)
: ST C.exit_code
    (requires (fun h ->
      LowStar.Buffer.live h argv /\
      Int32.v argc == LowStar.Buffer.length argv
    ))
    (ensures (fun _ _ _ -> True))
= test_zeroarg ()

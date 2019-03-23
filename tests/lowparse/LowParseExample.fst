module LowParseExample

open FStar.HyperStack.ST
open FStar.Bytes
open FStar.HyperStack.IO
open FStar.Printf
open LowParse.TestLib.SLow

#reset-options "--using_facts_from '* -LowParse +LowParse.Spec.Base +LowParse.SLow.Base'"

module Aux = LowParseExample.Aux

(*
let f (input: FStar.Bytes.bytes) : Pure (option (LowParseExample.Aux.t * FStar.UInt32.t))
  (requires True)
  (ensures (fun res ->
    match res with
    | None -> True
    | Some (_, consumed) -> FStar.UInt32.v consumed <= FStar.Bytes.length input
  ))
= [@inline_let]
  let res = LowParseExample.Aux.parse32_t input in
  [@inline_let]
  let _ = LowParse.SLow.Base.parser32_consumes LowParseExample.Aux.parse32_t input in
  res

let g (input: FStar.Bytes.bytes) : Tot (option (LowParse.SLow.array LowParseExample.Aux.t 18 * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t_array input

let j (input: FStar.Bytes.bytes) : Tot (option (LowParse.SLow.vlarray LowParseExample.Aux.t 5 7 * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t_vlarray input
*)

let m (x: LowParseExample.Aux.t) : Tot FStar.Bytes.bytes =
  LowParseExample.Aux.serialize32_t x

inline_for_extraction
let slice = LowParse.Low.slice (LowParse.Low.srel_of_buffer_srel (LowStar.Buffer.trivial_preorder _)) (LowParse.Low.srel_of_buffer_srel (LowStar.Buffer.trivial_preorder _))

// For now, extract the validator for compilation purposes only
let v (x: slice) : FStar.HyperStack.ST.Stack FStar.UInt32.t
  (requires (fun _ -> False))
  (ensures (fun _ _ _ -> True))
= LowParseExample.Aux.validate_t x 0ul

(*
let msz ( x: LowParseExample.Aux.t) : Tot FStar.UInt32.t =
  LowParseExample.Aux.size32_t x

let s (x: LowParse.SLow.array LowParseExample.Aux.t 18) : Tot FStar.Bytes.bytes =
  LowParseExample.Aux.serialize32_t_array x

#reset-options "--using_facts_from '* -LowParse'"

(** Test parser 'f' and formatter 'm' *)
let test_f_m (input:FStar.Bytes.bytes): Stack (option (FStar.Bytes.bytes * FStar.UInt32.t)) (fun _ -> true) (fun _ _ _ -> true) =
  let result = f input in
  match result with
  | Some (v, offset) -> (
    let formattedresult = m v in
    Some (formattedresult, offset)
  )
  | _ -> None
*)

(** Run all unit tests, by calling test_bytes and test_file 
    multiple times, with different parser+formatter pairs and 
    input data *)
let test (_:unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();

(*
  let test1 = "11010299" in
  let testbytes = bytes_of_hex test1 in
  test_bytes test_f_m "test_expect_fail" testbytes;

  test_string test_f_m "test_expect_pass" "12020300";
  
  test_file test_f_m "test_f_m_pass.bin";
  test_file test_f_m "test_f_m_fail.bin";
*)

  pop_frame()

// BUGBUG: HACK for Kremlin kremlib issue
// Dummy function, to call some FStar.Bytes functions.  This
// causes Kremlin to emit type declarations that are needed bytes
// krembytes.h.
let dummy (_:unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  assume false;
  push_frame();
  let p = twobytes (0uy, 1uy) in
  let p = split p 1ul in
  let p = iutf8_opt (utf8_encode "Napoléon") in
  pop_frame()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  test ();
  pop_frame ();
  C.EXIT_SUCCESS

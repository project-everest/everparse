module ASN1Test

include ASN1.Low.Content.BOOLEAN

open FStar.HyperStack.ST
open FStar.HyperStack.IO
open C
open C.String
open FStar.Bytes
module LB = LowStar.Buffer
module LPL = LowParse.Low.Base

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

let test_asn1_boolean () : St bool =
  assume false;
  print (!$"Testing ASN1 Boolean.\n");
  let buf = bytes_of_hex "ff" in
  let open FStar.UInt32 in
  let open FStar.Bytes in
  let input = from_bytes buf in
  if not (LPL.validate (validate_asn1_boolean ()) input (len buf)) then
    (print !$"Validator failed!"; false)
  else
    (print !$"Validator succeeded!"; true)

let test_zeroarg () : St C.exit_code =
  let b = true in
  let b = test_asn1_boolean () in
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

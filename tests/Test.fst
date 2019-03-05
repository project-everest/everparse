module Test

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

let from_bytes (b:bytes{length b <> 0}) : StackInline LPL.buffer8
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

(*
let test_open_enum () : St bool =
  print (!$"Testing open enum parser.\n");
  let x = T7.Body_y [
    twobytes (0z,1z);
    twobytes (3z,5z);
    twobytes (2z,6z);
    twobytes (255z,0z)
  ] in
  let tmp : list T1.t1 = [create 10ul 7z; create 12ul 9z] in
  assume(T2.t2_list_bytesize tmp == 22);
  let y = T7.Body_Unknown_tag2 33z tmp in
  let xb = T7.t7_serializer32 x in
  let yb = T7.t7_serializer32 y in
  bprint ("Serialized (case Y): "^hex_of_bytes xb);
  bprint ("Serialized (default case): "^hex_of_bytes yb);
  match T7.t7_parser32 xb, T7.t7_parser32 yb with
  | Some (x',r), Some (y', r') ->
    if x = x' && r = len xb && y = y' && r' = len yb  then (
      print (!$"Roundtrip OK.\n\n");
      true
    ) else (
      print (!$"Roundtrip failed.\n\n");
      false
    )
  | _ -> print (!$"failed.\n"); false

let test_closed_enum () : St bool =
  print (!$"Testing closed enum parser.\n");
  let x = T6.Body_a (twobytes (127z, 63z)) in
  let xb = T6.t6_serializer32 x in
  bprint ("Serialized: "^hex_of_bytes xb);
  match T6.t6_parser32 xb with
  | None -> print (!$"failed.\n"); false
  | Some (x',r) ->
    if x = x' && r = len xb then (
      print (!$"Roundtrip OK.\n\n");
      true
    ) else (
      print (!$"Roundtrip failed.\n\n");
      false
    )
*)

let test_bitcoin () : St bool =
  assume false;
  let block = bytes_of_hex   "030000009185dbc5e60723af6b4cdcdb5ceea505bc1cf7fe85097d02000000000000000001fef45c2701088577dffd37927b20da129acce6303f2ba3116ce032b4f8a5018de2dd55c4431418cb638acc0201000000010000000000000000000000000000000000000000000000000000000000000000ffffffff5703a7ab052f4249503130302f048fe2dd550850030f240c3900003c5b4254434368696e612e636f6d5d20e5b9b8e7a68fe4b88de59ca8e5be97e588b0e5a49a20e8808ce59ca8e8aea1e8be83e5b0912d2de4b99de6809d000000000100f90295000000001976a9142c30a6aaac6d96687291475d7d52f4b469f665a688ac000000000100000001f71c1cd429d1800080147ef63b2aa7440273d1ecdb2b0a1da01aded965e2ca8e000000006b483045022100de5bdb5a365fb16cc4057f1b1c1d9aabf130e85a9da6c184f186d0d0fbe7afd7022024321c4a53c4f5017153a666e10c65e4d790eb100fb4d66eaac8f9417699351c012102163e80de410646145142636833d8a92de4bb5c99e49bd52be5346fb1030628d4ffffffff02f05e3102000000001976a9145ca26d65ee83f441ef98b624763a305d50eb36cf88aca0860100000000001976a914838eb1034b719f9c47ab853aee63d505e4176a8388ac00000000" in
  let open FStar.UInt32 in
  let open FStar.Bytes in
  let lb = from_bytes block in
  let slice = { LPL.base = lb; LPL.len = len block } in
  if Block.block_validator slice 0ul >^ LPL.validator_max_length then
    (print !$"Validator failed on Bitcoin block!\n"; false)
  else
    let pos_random = Block.accessor_block_prev_block slice 0ul in
    let p_random = LB.sub lb pos_random 32ul in
    bprint (" The previous block hash is: " ^(hex_of_bytes (of_buffer 32ul p_random))); true

let main () : St C.exit_code =
  let b = true in
//  let b = test_closed_enum () in
//  let b = if b then test_open_enum () else false in
  let b = if b then test_bitcoin () else false in
  if b then C.EXIT_SUCCESS else C.EXIT_FAILURE

(*
Old test for TLS parsers. This has been moved to mitls-fstar

//module CH = QD.Parse_clientHello
//module SH = QD.Parse_serverHello
//module NST = QD.Parse_newSessionTicket13

  let client_hello = bytes_of_hex "0303636fad80506049a41bf5d2bc6282def8541c064f7c5dfc1a22d15d1fdb63a7312053bada022607152b1f61edc26aa42ae04e47a557188d8d5618aa43fed2bfe358003e130213031301c02cc030009fcca9cca8ccaac02bc02f009ec024c028006bc023c0270067c00ac0140039c009c0130033009d009c003d003c0035002f00ff010000b2000000190017000014746c7331332e636c6f7564666c6172652e636f6d000b000403000102000a000c000a001d0017001e00190018002300000016000000170000000d0030002e040305030603080708080809080a080b080408050806040105010601030302030301020103020202040205020602002b0009087f1c030303020301002d00020101003300260024001d002028f6c297892591276bf0dd77a6c1ade6b586ed955e80dc79c3bb98609f538101" in
  let server_hello = bytes_of_hex (* record header "02000076" *) "0303f71ed30cc04779b506a9f8af668da1b5fd8f26357c12cd4ba7c214f680e14e0f20c01886bb135f6d36102340ca06c5f9b9b777438dc3dda56e747003216dcbf136130200002e00330024001d0020b4871c8695fc4be0eae36067356ee16ff5e92e756f89b2cbfe48525acd3e0c27002b00027f1c" in
  let new_session_ticket = bytes_of_hex "0002a3002af9a838010000d08225ecc6fec0ee18c3dfef6d54a87f1d742ee5a43abbe59a3c86441dbd5ad39e69320a025e89481d3c7ee6b199bf944a8f4834b4d39da4706445ee8b0ea43b910bde77faffde5f856c906932dbe75bd60aa5f9c7b5ec47735e9f2deadf28828801ba2484b9a8cb5e7861d63840723fb9182d4db9cc1e91057949df74161360ae06b4ebf38f7611c36406808d4060d43c82888794b6c8d2a6d32aa16eafd9fd01b5fbaf7a8924d6b502f8f1898f6413845855a03e5ff7273402f85e1269d26298bd8a00512c0d8e45c005f06c200a52200008002a000400003800" in
  print (!$"Parsing client hello... ");
  match CH.clientHello_parser32 client_hello with
  | None ->
    print (!$"failed.\n");
    C.EXIT_FAILURE
  | Some (ch, r) ->
    print_string ("OK, parsed "^(FStar.UInt32.to_string r)^" bytes\n");
    print (!$"Parsing server hello... ");
    match SH.serverHello_parser32 server_hello with
    | None ->
      print (!$"failed.\n");
      C.EXIT_FAILURE
    | Some (sh, r) ->
      print_string ("OK, parsed "^(FStar.UInt32.to_string r)^" bytes\n");
      print (!$"Parsing new session ticket... ");
      match NST.newSessionTicket13_parser32 new_session_ticket with
      | None ->
        print (!$"failed.\n");
	C.EXIT_FAILURE
      | Some (nst, r) ->
        print_string ("OK, parsed "^(FStar.UInt32.to_string r)^" bytes\n");
        C.EXIT_SUCCESS
*)

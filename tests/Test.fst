module Test

open FStar.HyperStack.ST
open FStar.HyperStack.IO
open C
open C.String
open FStar.Bytes

module CH = QD.Parse_clientHello
module SH = QD.Parse_serverHello
module NST = QD.Parse_newSessionTicket

let main () : St C.exit_code =
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
      match NST.newSessionTicket_parser32 new_session_ticket with
      | None ->
        print (!$"failed.\n");
	C.EXIT_FAILURE
      | Some (nst, r) ->
        print_string ("OK, parsed "^(FStar.UInt32.to_string r)^" bytes\n");
        C.EXIT_SUCCESS


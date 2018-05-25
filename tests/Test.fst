module Test

open FStar.HyperStack.ST
open FStar.HyperStack.IO
open C
open C.String
open FStar.Bytes

module SH = QD.Parse_serverHello

let main () : St C.exit_code =
  let server_hello = bytes_of_hex (* record header "02000076" *) "0303f71ed30cc04779b506a9f8af668da1b5fd8f26357c12cd4ba7c214f680e14e0f20c01886bb135f6d36102340ca06c5f9b9b777438dc3dda56e747003216dcbf136130200002e00330024001d0020b4871c8695fc4be0eae36067356ee16ff5e92e756f89b2cbfe48525acd3e0c27002b00027f1c" in
  match SH.serverHello_parser32 server_hello with
  | None ->
    print (!$"Parsing failed.");
    C.EXIT_FAILURE
  | Some (sh, r) ->
    print (!$"Parsed bytes: ");
    print_string (print_bytes (bytes_of_int32 r));
    print (!$"\.QD Parsing OK\n");
    C.EXIT_SUCCESS


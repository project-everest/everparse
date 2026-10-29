(* Custard represents [LowParse.Bytes.bytes = Seq.seq byte] as an OCaml
   [int list], so a byte string is converted directly. *)
let lp_bytes_of_string (s:string) : int list
  = List.map int_of_char (List.init (String.length s) (String.get s))

let check_omitted_default (s:string)
  : bool
  = let pattern = Str.regexp_string "\x30\x0F\x06\x03\x55\x1D\x13\x01\x01\xFF\x04\x05\x30\x03\x01\x01\x00" in
    try (let _ = Str.search_forward pattern s 0 in 
         print_string "Found default field not omitted in BasicConstraints\n";
         true) with
      Not_found -> false

let check_certificate_version (s : string) : bool
  = let pattern = Str.regexp_string "\xA0\x03\x02\x01\x02" in
    try (let _ = Str.search_forward pattern s 0 in false) with
      Not_found ->
         print_string "Incorrect certificate version\n";
         true

let check_directorytype (s : string) : bool
  = let pattern = Str.regexp "\x06\x03\x55\x04\\(.\\|\x0A\\)\x16" in
    try (let _ = Str.search_forward pattern s 0 in 
         print_string "Found invalid directory string type\n";
         true) with
      Not_found -> false

let check_directorytype2 (s : string) : bool
  = let pattern = Str.regexp_string "\x06\x09\x2A\x86\x48\x86\xF7\x0D\x01\x09\x01\x13" in
    try (let _ = Str.search_forward pattern s 0 in 
         print_string "Found invalid directory string type\n";
         true) with
      Not_found -> false

let check_omitted_default2 (s:string)
  : bool
  = let pattern = Str.regexp "\x06\x03\x55\x1D.\x01\x01\x00" in
    try (let _ = Str.search_forward pattern s 0 in 
         print_string "Found default field not omitted in extension\n";
         true) with
      Not_found -> false

let check_wrong_timeformat (s:string)
  :bool
  = let pattern = Str.regexp "\x17\x11[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]\\(+\\|-\\)0000" in
    try (let _ = Str.search_forward pattern s 0 in 
         print_string "Found invalid time format\n";
         true) with
      Not_found -> false

let check_empty_sequence (s:string)
  : bool
  = let pattern = Str.regexp_string "\x30\x09\x06\x03\x55\x1D\x11\x04\x02\x30\x00" in
    try (let _ = Str.search_forward pattern s 0 in 
         print_string "Found empty sequence in SubjectAlternativeName extension\n";
         true) with
      Not_found -> false

let check_bad_boolean (s:string)
  : bool
  = let pattern = Str.regexp_string "\x06\x03\x55\x1D\x13\x01\x01\x01" in
    try (let _ = Str.search_forward pattern s 0 in 
         print_string "Found bad boolean in BasicConstraints\n";
         true) with
      Not_found -> false

let check_overly_large (s:string)
  : bool
  = let pattern = Str.regexp_string "\xA0\x03\x02\x01\x02" in
    try (let x = Str.search_forward pattern s 0 in 
         let lch = String.get s (x + 6) in
         if int_of_char lch > 20 then
           (print_string "Found overly large serial number\n";
           true)
         else
           false) with
      Not_found -> false

let get_failure_reason (s:string)
  : int
  = if check_certificate_version s then
      3
    else if check_omitted_default s then 
      4
    else if check_omitted_default2 s then
      4
    else if check_directorytype s then
      5
    else if check_directorytype2 s then
      5
    else if check_wrong_timeformat s then
      6
    else if check_overly_large s then
      6
    else if check_bad_boolean s then
      6
    else if check_empty_sequence s then
      7
    else
      2

(* Differential testing (../difftest): [DIFFTEST manifest.json results.jsonl]
   runs every vector of the manifest through ASN1.DiffTest.parse and writes
   one JSON object per line: {id, impl, verdict, consumed}. The verdict is
   "accept" iff the whole input is consumed. *)
let bytes_of_hex (h:string) : string =
  let h = String.concat "" (String.split_on_char ' ' h) in
  String.init (String.length h / 2)
    (fun i -> Char.chr (int_of_string ("0x" ^ String.sub h (2 * i) 2)))

let difftest (manifest:string) (results:string) : unit =
  let open Yojson.Safe.Util in
  let vectors = Yojson.Safe.from_file manifest |> member "vectors" |> to_list in
  let oc = open_out_bin results in
  List.iter (fun v ->
      let id = v |> member "id" |> to_string in
      let ty = v |> member "type" |> to_string in
      let data = bytes_of_hex (v |> member "hex" |> to_string) in
      let len = String.length data in
      let verdict, consumed =
        match ASN1_DiffTest.parse ty (lp_bytes_of_string data) with
        | None -> "unsupported", `Null
        | Some None -> "reject", `Null
        | Some (Some n) ->
          let n = Z.to_int n in
          (if n = len then "accept" else "reject"), `Int n
      in
      let line = `Assoc [ ("id", `String id); ("impl", `String "ours");
                          ("verdict", `String verdict); ("consumed", consumed) ] in
      output_string oc (Yojson.Safe.to_string line);
      output_char oc '\n')
    vectors;
  close_out oc

let main = 
  if Array.length Sys.argv = 4 && String.equal Sys.argv.(1) "DIFFTEST" then
    (difftest Sys.argv.(2) Sys.argv.(3); exit 0);
  let argc = Array.length Sys.argv in
  if argc <> 3 && argc <> 4
  then (
     print_string "Usage: ASN1_Parser format filename [-debug]\n";
     print_string "       ASN1_Parser DIFFTEST manifest.json results.jsonl\n";
     print_string "Supported format: X509 CRL SETTEST\n";
     exit 1
  )
  else (
    let formatname = Sys.argv.(1) in
    let debugflag = argc = 4 in
    let p = if String.equal formatname "X509" then
              (if debugflag then ASN1_X509.dparse_cert else ASN1_X509.parse_cert)
            else if String.equal formatname "CRL" then
              (if debugflag then ASN1_CRL.dparse_crl else ASN1_CRL.parse_crl)
            else if String.equal formatname "SETTEST" then
              (if debugflag then ASN1_SetTest.dparse_settest else ASN1_SetTest.parse_settest)
            else 
              fun _ -> None
    in
    let filename = Sys.argv.(2) in
    try
      let file = open_in_bin filename in
      let filelen = in_channel_length file in
      let str = really_input_string file filelen in
      close_in file;
      let b = lp_bytes_of_string str in
      print_string ("About to parse " ^ string_of_int (String.length str) ^ " bytes from " ^ filename ^ " ... \n");
      match p b with
      | None -> print_string "parsing failed\n"; 
                if formatname = "X509" then
                  exit (get_failure_reason str)
                else
                  exit 2
      | Some (x, n) ->
        print_string ("parsing succeeded consuming " ^ Z.to_string n ^ " bytes\n");
        (* Round trip through the spec serializer (ASN1.Spec.Serializer) *)
        let enc =
          if debugflag then None
          else if String.equal formatname "X509" then Some (ASN1_RoundTrip.enc_cert (Obj.magic x))
          else if String.equal formatname "CRL" then Some (ASN1_RoundTrip.enc_crl (Obj.magic x))
          else None
        in
        match enc with
        | None -> ()
        | Some e ->
          let consumed = lp_bytes_of_string (String.sub str 0 (Z.to_int n)) in
          if e = consumed
          then print_string "round trip succeeded\n"
          else (print_string "round trip FAILED\n"; exit 8)
    with
     e -> print_string (filename ^ " could not be read: " ^ Printexc.to_string e ^ "\n"); exit 3
  )

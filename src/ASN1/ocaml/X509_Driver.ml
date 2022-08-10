let lp_bytes_of_bytes (b:FStar_Bytes.bytes)
  : LowParse_Bytes.bytes
  = let rec aux (i:int) (out:LowParse_Bytes.bytes)
     : LowParse_Bytes.bytes
     = if Z.of_int i = FStar_Bytes.length b
       then out
       else aux (i + 1) (FStar_Seq_Properties.snoc out (FStar_Bytes.get b (Stdint.Uint32.of_int i)))
    in
    aux 0 (FStar_Seq_Base.empty())
      
  
let main = 
  let argc = Array.length Sys.argv in
  if argc <> 2
  then (
     print_string "Usage: X509_Driver filename\n";
     exit 1
  )
  else (
    let filename = Sys.argv.(1) in
    try
      let file = Core.In_channel.create ~binary:true filename in
      let str = Core.In_channel.input_all file in
      Core.In_channel.close file;
      let b = FStar_Bytes.bytes_of_string str in
      let b = lp_bytes_of_bytes b in
      print_string ("About to parse " ^ string_of_int (Z.to_int (FStar_Bytes.length str)) ^ " bytes from " ^ filename ^ " ... \n");
      match ASN1_X509.parse_cert b with
      | None -> print_string "parsing failed\n"; exit 2
      | Some (_, n) -> 
        print_string ("parsing succeeded consuming " ^ Z.to_string n ^ " bytes\n")
    with
     _ -> print_string (filename ^ " could not be read\n"); exit 3
  )

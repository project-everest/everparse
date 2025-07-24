(* let () = print_endline "Hello, World!" *)
open Thrift
module TCTrans = TChannelTransport
module TCompactProt = TCompactProtocol

open Parquet_types
open Parquet_shim

let test_file_path = "/home/caiyi/repos/arrow-rs/parquet-testing/data/nested_maps.snappy.parquet"

let () =
  (* open the test file to be parsed *)
  let file_path = Sys.getenv_opt "PARQUET_TEST_FILE" |> Option.value ~default:test_file_path in
  let ic = open_in_bin file_path in         (* input channel *)
  let oc = open_out_bin "/dev/null" in      (* dummy output, protocol wants both *)
  (* read the *last* 4 bytes for ic *)
  let file_size = in_channel_length ic in
  let magic = Bytes.create 4 in
  seek_in ic (file_size - 4);
  really_input ic magic 0 4;
  (* check the magic number *)
  if magic <> Bytes.of_string "PAR1" then
    failwith "Not a valid Parquet file: magic number mismatch";
  (* read another 4 bytes from the back as little endian int *)
  let footer_len = Bytes.create 4 in
  seek_in ic (file_size - 8);
  really_input ic footer_len 0 4;
  let footer_len = Bytes.get_int32_le footer_len 0 |> Int32.to_int in
  Printf.printf "Footer length: %d\n" footer_len;
  (* read the footer from the start *)
  seek_in ic (file_size - footer_len - 8);
  (* let footer = Bytes.create footer_len in *)
  (* really_input ic footer 0 footer_len; *)
  let transport  = new TCTrans.t (ic, oc) in
  let proto      = new TCompactProt.t transport in    (* Compact protocol instance *)
  let fmd     = read_fileMetaData proto in     (* ← deserialise! *)
  close_in ic; close_out oc;
  Printf.printf "File metadata version: %s\n" (Int32.to_string fmd#grab_version) ;
  Printf.printf "File metadata num rows: %d\n" (Int64.to_int fmd#grab_num_rows) ;
  let fmd = convert_file_meta_data fmd in
  Printf.printf "Converted file metadata: %s\n" (show_file_meta_data fmd) ;




 

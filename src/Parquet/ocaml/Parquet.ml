(* let () = print_endline "Hello, World!" *)
open Thrift
module TCTrans = TChannelTransport
module TCompactProt = TCompactProtocol

open Parquet_types
open Parquet_shim
open Printf

let test_file_path = "/home/caiyi/repos/arrow-rs/parquet-testing/data/nested_maps.snappy.parquet"

let () =
  (* open the test file to be parsed *)
  if Array.length Sys.argv < 2 then begin
    eprintf "Usage: %s <file.parquet>\n%!" Sys.argv.(0);
    exit 64                      (* EX_USAGE *)
  end;
  let file_path = Sys.argv.(1) in
  (* let file_path = Sys.getenv_opt "PARQUET_TEST_FILE" |> Option.value ~default:test_file_path in *)
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
  printf "Footer length: %d\n" footer_len;
  (* read the footer from the start *)
  let footer_start = file_size - footer_len - 8 in
  seek_in ic footer_start;
  (* let footer = Bytes.create footer_len in *)
  (* really_input ic footer 0 footer_len; *)
  let transport  = new TCTrans.t (ic, oc) in
  let proto      = new TCompactProt.t transport in    (* Compact protocol instance *)
  let fmd     = read_fileMetaData proto in     (* ← deserialise! *)
  printf "File metadata created by: %s\n%!" fmd#grab_created_by;
  let fmd = convert_file_meta_data fmd in
  let ok  = validate_file_meta_data fmd (Int64.of_int footer_start) in

  (* printf "Converted file metadata: %s\n" (show_file_meta_data fmd) ; *)

  (* validate the file metadata *)

  if ok then begin
    printf "%s ✔︎ valid\n%!" file_path;
    (* traverse each of the column chunks in each of the row group *)
    List.iter (fun rg ->
      List.iter (fun cc ->
        match cc.offset_index_offset, cc.offset_index_length with 
        Some offset, Some length ->
          seek_in ic Int64.(to_int offset);
          let offset_index = read_offsetIndex proto in
          let offset_index = convert_offset_index offset_index in
          if validate_offset_index offset_index cc then begin
            printf "OffsetIndex ✔︎ valid\n%!";
            (* printf "Column chunk %s offset index: %s\n" (show pp_column_chunk cc) (show pp_offset_index offset_index); *)
          end else begin
            printf "OffsetIndex ✘ invalid\n%!";
            close_in ic; close_out oc;
            exit 1;
            (* printf "Column chunk %s offset index: %s\n" (show pp_column_chunk cc) (show pp_offset_index offset_index); *)
          end
          (* printf "Column chunk %s offset index: %s\n" (show pp_column_chunk cc) (show pp_offset_index offset_index) *)
        | _ -> printf "No offset index\n"
      ) rg.columns
    ) fmd.row_groups ;
  end else begin
    printf "%s ✘ invalid\n%!" file_path;
    close_in ic; close_out oc;
    exit 1
  end 
  close_in ic; close_out oc;

module Hashing.Hash
open Hashing.Op

type c_files = {
    wrapper_h: option string;
    wrapper_c: option string;
    h: string;
    c: string;
    assertions: option string;
  }

let hash f opt_c =
  let h = hash_init () in
  hash_string h Version.everparse_version;
  hash_string h Version.fstar_commit;
  hash_string h Version.karamel_commit;
  hash_file h f;
  begin match opt_c with
  | None -> hash_bool h false
  | Some c ->
     hash_bool h true;
     hash_file_option h c.wrapper_h;
     hash_file_option h c.wrapper_c;
     hash_file h c.h;
     hash_file h c.c;
     begin match c.assertions with
     | None ->
        hash_bool h false
     | Some assertions ->
        hash_bool h true;
        hash_file h assertions
     end
  end;
  hash_finish h

let c_comment_intro = "EverParse checksum hash"

let hash_as_comment file =
  let h = hash file None in
  c_comment_intro ^ ":" ^ h

type check_inplace_hashes_t =
  | AllHashes of c_files
  | OneHash of string

let check_inplace_hashes_on f file_3d files_c =
  let h = hash file_3d None in
  match files_c with
  | OneHash c_file -> f h c_file
  | AllHashes files_c ->
    List.for_all (f h) (
      files_c.c ::
      files_c.h ::
      begin match files_c.wrapper_c with
      | None -> []
      | Some w -> [w]
      end @
      begin match files_c.wrapper_h with
      | None -> []
      | Some w -> [w]
      end @
      begin match files_c.assertions with
      | None -> []
      | Some assertions -> [assertions]
      end
    )

let check_inplace_hash
     f file_3d_file_c
  =
  let eqstr' () : FStar.All.ML (s: string { String.length s == 1 }) =
    assert_norm (String.length "=" == 1);
    "="
  in
  let eqstr = eqstr' () in
  match String.split [String.index eqstr 0] file_3d_file_c with
  | [file_3d; file_c] ->
     if check_inplace_hashes_on f file_3d (OneHash file_c)
     then begin
         FStar.IO.print_string (Printf.sprintf "EverParse check_inplace_hash succeeded on %s\n" file_3d)
       end else begin
         FStar.IO.print_string (Printf.sprintf "EverParse check_inplace_hash failed on %s\n" file_3d);
         FStar.All.exit 255
       end
  | _ -> FStar.All.failwith "check_inplace_hash: expected file.3d=file.h"

let check_inplace_hashes f = List.iter (check_inplace_hash f)

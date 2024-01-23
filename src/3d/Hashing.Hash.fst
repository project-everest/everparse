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

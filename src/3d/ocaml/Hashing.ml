(* Hash a boolean *)

let char_of_int4 x =
  assert (0 <= x && x < 16);
  if x < 10
  then char_of_int (int_of_char '0' + x)
  else char_of_int (int_of_char 'a' + x - 10)

let hex_of_char c =
  let i = int_of_char c in
  assert (0 <= i && i < 256);
  char_of_int4 (i / 16), char_of_int4 (i mod 16)

let hex_of_bytes buf =
  let hex = Bytes.create (Bytes.length buf * 2) in
  Bytes.iteri (fun idx c ->
      let hi, lo = hex_of_char c in
      Bytes.set hex (2 * idx) hi;
      Bytes.set hex (2 * idx + 1) lo
    ) buf;
  Bytes.to_string hex

let hash_debug = false

let hash_debug_print s =
  if hash_debug
  then print_endline s

let hash_debug_print_current_digest h =
  if hash_debug
  then hash_debug_print (Printf.sprintf ("Current hash: %s") (hex_of_bytes (HashingBase.get_current_digest h)))

let hash_update h buf =
  HashingBase.update h buf;
  hash_debug_print_current_digest h

let hash_bool h b =
  hash_debug_print (Printf.sprintf "hash_bool %s" (if b then "true" else "false"));
  let buf = Bytes.make 1 (char_of_int (if b then 1 else 0)) in
  hash_update h buf

(* Hash an integer *)

let hash_int h i =
  let i32 = Int32.of_int i in
  hash_debug_print (Printf.sprintf "hash_int %d" (Int32.to_int i32));
  let buf = Bytes.create 4 in
  Bytes.set_int32_be buf 0 i32;
  hash_update h buf

(* Hash a file *)

let hash_file h f =
  let ch = open_in_bin f in
  let len = in_channel_length ch in
  hash_int h len;
  hash_debug_print (Printf.sprintf "hash_file %s" f);
  let buf = Bytes.create len in
  let _ = really_input ch buf 0 len in
  close_in ch;
  hash_update h buf

let hash_file_option h = function
  | None -> hash_bool h false
  | Some f -> hash_bool h true; hash_file h f

(* Hash a string *)

let hash_string h s =
  hash_int h (String.length s);
  hash_debug_print (Printf.sprintf "hash_string \"%s\"" s);
  hash_update h (Bytes.of_string s)


type c_files = {
    wrapper_h: string option;
    wrapper_c: string option;
    h: string;
    c: string;
    assertions: string option;
  }

let hash f opt_c =
  hash_debug_print "hash_init";
  let h = HashingBase.init () in
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
  hash_debug_print "hash_finish";
  hex_of_bytes (HashingBase.finish h)

(* load, check and save weak hashes from a C file *)

let c_comment_intro = "EverParse checksum hash"

let hash_as_comment file =
  let h = hash file None in
  Printf.sprintf "%s:%s" c_comment_intro h

type check_inplace_hashes_t =
  | AllHashes of c_files
  | OneHash of string

let check_inplace_hashes file_3d files_c =
  let h = hash file_3d None in
  let f file_c =
    let ch = open_in file_c in
    (* Check fails if a bad hash or no hash is found. A
       good hash alone does not make the check succeed *)
    let rec aux accu =
      try
        let l = input_line ch in
        begin match String.split_on_char ':' (String.trim l) with
        | [hd; tl] when hd = c_comment_intro ->
           if tl = h
           then aux true
           else begin
               Printf.printf "Weak hash check failed in %s, expected %s, found %s\n" file_c h tl;
               false
           end 
        | _ -> aux accu
        end
      with End_of_file -> 
        begin
          if not accu
          then Printf.printf "No hash found in %s\n" file_c;
          accu
        end
    in
    let res = aux false in
    close_in ch;
    res
  in
  match files_c with
  | OneHash c_file -> f c_file
  | AllHashes files_c ->
    List.for_all f (
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
  

(* load, check and save hashes from/to JSON file *)

let load_hash file is_weak =
  try
    begin match Yojson.Basic.from_file file with
    | `Assoc l ->
       let name = Printf.sprintf "%s-hash" (if is_weak then "weak" else "strong") in
       begin match List.assoc_opt name l with
       | Some (`String s) -> Some s
       | _ -> None
       end
    | _ -> None
    end
  with _ -> None

let check_hash f opt_c f_json =
  match load_hash f_json (opt_c = None) with
  | None ->
     Printf.printf "No hashes found in %s for %s\n" f_json f;
     false
  | Some h0 ->
     let h = hash f opt_c in
     let res = (h0 = h) in
     if not res
     then Printf.printf "%s hash check failed for %s from %s\nOriginal: %s\nComputed: %s\n" (if opt_c = None then "weak" else "strong") f f_json h0 h;
     res

let save_hashes f opt_c f_json =
  let weak_hash = hash f None in
  let l : (string * Yojson.Basic.t) list = [("weak-hash", `String weak_hash)] in
  let l : (string * Yojson.Basic.t) list = match opt_c with
    | None -> l
    | _ ->
       let strong_hash = hash f opt_c in
       ("strong-hash", `String strong_hash) :: l
  in
  Yojson.Basic.to_file f_json (`Assoc l)

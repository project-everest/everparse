(* Hash a boolean *)

let hash_bool h b =
  let buf = Bytes.make 1 (char_of_int (if b then 1 else 0)) in
  Hacl_star__EverCrypt.Hash.update h buf

(* Hash an integer *)

let hash_int h i =
  let i32 = Int32.of_int i in
  let buf = Bytes.create 4 in
  Bytes.set_int32_be buf 0 i32;
  Hacl_star__EverCrypt.Hash.update h buf

(* Hash a file *)

let hash_file h f =
  let ch = open_in_bin f in
  let len = in_channel_length ch in
  hash_int h len;
  let buf = Bytes.create len in
  let _ = input ch buf 0 len in
  close_in ch;
  Hacl_star__EverCrypt.Hash.update h buf

(* Hash a string *)

let hash_string h s =
  hash_int h (String.length s);
  Hacl_star__EverCrypt.Hash.update h (Bytes.of_string s)

type t = Hacl_star__EverCrypt.Hash.t
let alg = Hacl_star__SharedDefs.HashDefs.SHA2_256
let hlen = Hacl_star__SharedDefs.HashDefs.digest_len alg

let init () = Hacl_star__EverCrypt.Hash.init alg

let finish h =
  let buf = Bytes.create hlen in
  Hacl_star__EverCrypt.Hash.finish h buf;
  buf

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

let hash f opt_c =
  let h = init () in
  hash_string h Version.everparse_version;
  hash_string h Version.fstar_commit;
  hash_string h Version.kremlin_commit;
  hash_file h f;
  begin match opt_c with
  | None -> hash_bool h false
  | Some c -> hash_bool h true; hash_file h c
  end;
  hex_of_bytes (finish h)

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
  | None -> false
  | Some h' -> h' = hash f opt_c

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

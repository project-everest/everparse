type t = HashingBase.t

let debug_hash = false

(* Hash a boolean *)

let hash_bool h b =
  let buf = Bytes.make 1 (char_of_int (if b then 1 else 0)) in
  HashingBase.update h buf

(* Hash an integer *)

let hash_int h i =
  let i32 = Int32.of_int i in
  let buf = Bytes.create 4 in
  Bytes.set_int32_be buf 0 i32;
  HashingBase.update h buf

(* Hash a file *)

let hash_file h f =
  let ch = open_in_bin f in
  let len = in_channel_length ch in
  hash_int h len;
  let buf = Bytes.create len in
  let _ = input ch buf 0 len in
  close_in ch;
  HashingBase.update h buf

let hash_file_option h = function
  | None -> hash_bool h false
  | Some f -> hash_bool h true; hash_file h f

(* Hash a string *)

let hash_string h s =
  if debug_hash then begin
      print_endline ("hash_string: \"" ^ s ^ "\"")
  end;
  hash_int h (String.length s);
  HashingBase.update h (Bytes.of_string s)

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

let hash_init () =
  HashingBase.init ()

let hash_finish h =
  hex_of_bytes (HashingBase.finish h)

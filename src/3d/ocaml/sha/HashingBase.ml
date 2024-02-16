type t = Sha256.ctx

let debug_hash = false

let init () = Sha256.init ()

let finish h = Bytes.of_string (Sha256.to_bin (Sha256.finalize h))

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

let update h b =
  if debug_hash then begin
      print_endline ("Trying to update with: " ^ hex_of_bytes b);
  end;
  Sha256.update_string h (Bytes.to_string b);
  if debug_hash then begin
      let h' = Sha256.copy h in
      let s = finish h' in
      print_endline ("Update: " ^ hex_of_bytes s)
  end

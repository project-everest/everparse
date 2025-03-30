type t = Sha256.ctx

let init () = Sha256.init ()

let update h b = Sha256.update_string h (Bytes.to_string b)

let finish h = Bytes.of_string (Sha256.to_bin (Sha256.finalize h))

let get_current_digest h =
  let h' = Sha256.copy h in
  finish h'

type t = Hacl_star__EverCrypt.Hash.t
let alg = Hacl_star__SharedDefs.HashDefs.SHA2_256
let hlen = Hacl_star__SharedDefs.HashDefs.digest_len alg

let init () = Hacl_star__EverCrypt.Hash.init alg
let update = Hacl_star__EverCrypt.Hash.update

let finish h =
  let buf = Bytes.create hlen in
  Hacl_star__EverCrypt.Hash.finish h buf;
  buf

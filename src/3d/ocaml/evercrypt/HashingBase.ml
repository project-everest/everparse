type t = Hacl_star__EverCrypt.Hash.t
let alg = Hacl_star__SharedDefs.HashDefs.SHA2_256

let init () = Hacl_star__EverCrypt.Hash.init ~alg:alg
let update st data = Hacl_star__EverCrypt.Hash.update ~st:st ~msg:data

let finish h =
  Hacl_star__EverCrypt.Hash.finish ~st:h

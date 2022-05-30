module LowParse.Steel.StdInt

let size_t = U32.t

let size_precond x = (exists (x': U32.t) . x == U32.v x')

let size_v x = U32.v x

let size_v_inj _ _ = ()

let mk_size_t x = x

let uint32_of_size_t x _ = x

let int_to_size_t x = U32.uint_to_t x

let size_precond_le x _ =
  let _ = U32.uint_to_t x in
  ()

let size_add x y = U32.add x y

let size_sub x y = U32.sub x y

let size_mul x y = U32.mul x y

let size_div x y = U32.div x y

let size_mod x y = U32.rem x y

let size_le x y = U32.lte x y

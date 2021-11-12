module LowParse.Steel.ArrayPtr.Make
friend LowParse.Steel.ArrayPtr

module R = Steel.Reference

let array_of x = x

let enter #_ #base #t0 ar =
    let tmp : R.ghost_ref (array' (fst0 ar)) = R.ghost_alloc ar in
    array_null_to_unique ar;
    let res : t base t0 = (fst0 ar, Ghost.hide (Some ({ from = fst0 ar; to = tmp; }))) in
    change_equal_slprop
      (R.ghost_vptr tmp)
      (R.ghost_vptr (Some?.v (snd0 res)).to);
    intro_varrayptr res ar ();
    return res

let exit #_ #base #a r =
  let tmp = elim_varrayptr r in
  let ar : A.array base a = (fst0 r, snd0 (snd0 tmp)) in
  change_equal_slprop
    (A.varray (snd0 tmp))
    (A.varray ar);
  R.ghost_free (fst0 tmp);
  return ar

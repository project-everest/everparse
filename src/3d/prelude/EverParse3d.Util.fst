module EverParse3d.Util

open FStar.Tactics.V2

let solve_from_ctx () : Tac unit =
  ignore (intros ());
  let bs = vars_of_env (cur_env ()) in
  first (map (fun (b:binding) () -> exact b) bs)

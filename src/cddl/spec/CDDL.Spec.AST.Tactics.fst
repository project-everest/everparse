module CDDL.Spec.AST.Tactics
include CDDL.Spec.AST.Elab

let solve_by_norm () : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta; iota; zeta; primops; nbe];
  FStar.Tactics.smt ()

let solve_sem () : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta_attr [`%sem_attr]; iota; zeta; primops; nbe];
  FStar.Tactics.smt ()

exception ExceptionOutOfFuel

let solve_mk_wf_typ_fuel_for () : FStar.Tactics.Tac unit =
  let rec aux (n: nat) : FStar.Tactics.Tac unit =
    FStar.Tactics.try_with
    (fun _ ->
      FStar.Tactics.print ("solve_mk_wf_typ_fuel_for with fuel " ^ string_of_int n ^ "\n");
      FStar.Tactics.apply (FStar.Tactics.mk_app (`mk_wf_typ_fuel_for_intro) [quote n, FStar.Tactics.Q_Explicit]);
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.try_with
        (fun _ ->
          FStar.Tactics.trefl ()
        )
        (fun e -> 
          let g = FStar.Tactics.cur_goal () in
          FStar.Tactics.print ("solve_mk_wf_typ_fuel_for Failure: " ^ FStar.Tactics.term_to_string g ^ "\n");
          let g0 = quote (squash (ROutOfFuel == RSuccess ())) in
          FStar.Tactics.print ("Comparing with " ^ FStar.Tactics.term_to_string g0 ^ "\n");
          let e' =
            if g `FStar.Tactics.term_eq` g0
            then ExceptionOutOfFuel
            else e
          in
          FStar.Tactics.raise e'
        )
      )
      (fun e ->
        match e with
        | ExceptionOutOfFuel -> aux (n + 1)
        | _ -> FStar.Tactics.raise e
      )
  in
  aux 0

module LowParse.Low.Tac.Sum
include LowParse.Low.Sum

open LowParse.TacLib

(* Tactic for accessor extensionality *)

noextract
let sum_accessor_ext (ty: term) : Tac unit =
      let thm = mk_app (`clens_eq_intro') [(ty, Q_Implicit)] in
      apply thm;
      iseq [
        (fun _ ->
          norm [delta; zeta; iota; primops];
          let x = intro () in
          destruct (binder_to_term x);
          to_all_goals (fun _ ->
            let eqn = intros_until_eq_hyp () in
            rewrite eqn;
            norm [delta; zeta; iota; primops];
            trivial ()
          )
        );
        (fun _ ->
          norm [delta; zeta; iota; primops];
          let x = intro () in
          destruct (binder_to_term x);
          to_all_goals (fun _ ->
            let eqn = intros_until_eq_hyp () in
            rewrite eqn;
            norm [delta; zeta; iota; primops];
            let u = intro () in
            smt ()
          )
        )
      ]

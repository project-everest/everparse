module LowParse.TacLib
include FStar.Tactics
include LowParse.Norm

module L = FStar.List.Tot

[@@ noextract_to "krml"]
let conclude ()
: Tac unit
= // dump "conclude before";
  norm [delta; iota; primops];
  begin if lax_on ()
    then smt ()
    else
    first [
      trefl;
      trivial;
    ]
  end;
//  dump "conclude after";
  qed ()

[@@ noextract_to "krml"]
let solve_vc ()
: Tac unit
= exact_guard (quote ()); conclude ()

[@@ noextract_to "krml"]
let app_head_tail (t: term) :
    Tac (term * list argv)
= collect_app t

[@@ noextract_to "krml"]
let tassert (b: bool) : Tac (squash b) =
  if b
  then ()
  else
    let s = term_to_string (quote b) in
    fail ("Tactic assertion failed: " ^ s)

[@@ noextract_to "krml"]
let rec to_all_goals (t: (unit -> Tac unit)) : Tac unit =
  if ngoals () = 0
  then ()
  else
    let _ = divide 1 t (fun () -> to_all_goals t) in ()

[@@ noextract_to "krml"]
let rec intros_until_squash
  ()
: Tac binder
= let i = intro () in
  let (tm, _) = app_head_tail (cur_goal ()) in
  if tm `is_fvar` (`%squash)
  then i
  else intros_until_squash ()

[@@ noextract_to "krml"]
let rec intros_until_eq_hyp
  ()
: Tac binder
= let i = intro () in
  let (sq, ar) = app_head_tail (type_of_binding i) in
  let cond =
    if sq `is_fvar` (`%squash) then
      match ar with
      | (ar1, _) :: _ ->
        let (eq, _) = app_head_tail ar1 in
        eq `is_fvar` (`%eq2)
      | _ -> false
    else false
  in
  if cond
  then i
  else intros_until_eq_hyp ()

[@@ noextract_to "krml"]
let pp_norm_tac () : Tac unit =
  norm norm_steps;
  trefl ();
  to_all_goals (fun _ ->
    norm [delta; iota; zeta; primops];
    smt ()
  );
  qed ()

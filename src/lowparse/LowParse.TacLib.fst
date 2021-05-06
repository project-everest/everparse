module LowParse.TacLib
include FStar.Tactics
include LowParse.Norm

module L = FStar.List.Tot

[@@ noextract_to "Kremlin"]
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

[@@ noextract_to "Kremlin"]
let solve_vc ()
: Tac unit
= exact_guard (quote ()); conclude ()

[@@ noextract_to "Kremlin"]
let rec app_head_rev_tail (t: term) :
  Tac (term * list argv)
=
  let ins = inspect t in
  if Tv_App? ins
  then
    let (Tv_App u v) = ins in
    let (x, l) = app_head_rev_tail u in
    (x, v :: l)
  else
    (t, [])

[@@ noextract_to "Kremlin"]
let app_head_tail (t: term) :
    Tac (term * list argv)
= let (x, l) = app_head_rev_tail t in
  (x, L.rev l)

[@@ noextract_to "Kremlin"]
let tassert (b: bool) : Tac (squash b) =
  if b
  then ()
  else
    let s = term_to_string (quote b) in
    fail ("Tactic assertion failed: " ^ s)

[@@ noextract_to "Kremlin"]
let rec to_all_goals (t: (unit -> Tac unit)) : Tac unit =
  if ngoals () = 0
  then ()
  else
    let _ = divide 1 t (fun () -> to_all_goals t) in ()

[@@ noextract_to "Kremlin"]
let rec intros_until_squash
  ()
: Tac binder
= let i = intro () in
  let (tm, _) = app_head_tail (cur_goal ()) in
  if tm `term_eq` (`squash)
  then i
  else intros_until_squash ()

[@@ noextract_to "Kremlin"]
let rec intros_until_eq_hyp
  ()
: Tac binder
= let i = intro () in
  let (sq, ar) = app_head_tail (type_of_binder i) in
  let cond =
    if sq `term_eq` (`squash) then
      match ar with
      | (ar1, _) :: _ ->
        let (eq, _) = app_head_tail ar1 in
        eq `term_eq` (`eq2)
      | _ -> false
    else false
  in
  if cond
  then i
  else intros_until_eq_hyp ()

[@@ noextract_to "Kremlin"]
let pp_norm_tac () : Tac unit =
  norm norm_steps;
  trefl ();
  to_all_goals (fun _ ->
    norm [delta; iota; zeta; primops];
    smt ()
  );
  qed ()

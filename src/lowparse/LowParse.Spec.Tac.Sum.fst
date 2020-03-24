module LowParse.Spec.Tac.Sum
include LowParse.Spec.Tac.Enum
include LowParse.Spec.Sum

module T = LowParse.TacLib
module U32 = FStar.UInt32


(* Universal destructor *)

noextract
let enum_destr_tac
  (#key #repr: Type)
  (e: list (key * repr))
: T.Tac unit
= enum_tac_gen (quote enum_destr_cons_nil') (quote enum_destr_cons') e

noextract
let make_sum_synth_case_recip_synth_case_tac
  ()
: T.Tac unit
= 
    let x = T.binder_to_term (T.intro ()) in
    T.destruct x;
    T.to_all_goals (fun () ->
      let xeq = T.intros_until_squash () in
      T.norm [delta; iota; zeta; primops];
      T.rewrite xeq;
      T.norm [delta; iota; zeta; primops];
      T.trivial ()
    )

noextract
let make_dsum_synth_case_recip_synth_case_known_tac
  ()
: T.Tac unit
= make_sum_synth_case_recip_synth_case_tac ()

noextract
let make_dsum_synth_case_recip_synth_case_unknown_tac
  ()
: T.Tac unit
= let x = T.binder_to_term (T.intro ()) in
  T.norm [delta; iota; zeta; primops];
  T.trivial ()

noextract
let synth_case_synth_case_recip_tac
  ()
: T.Tac unit
= make_sum_synth_case_recip_synth_case_tac ()

noextract
let synth_case_recip_pre_tac
  ()
: T.Tac unit
= let x = T.intro () in
  T.destruct (T.binder_to_term x);
  T.to_all_goals (fun () ->
    let re = T.intros_until_squash () in
    T.rewrite re;
    T.norm [delta; iota];
    let im = T.implies_intro () in
    T.rewrite im;
    T.trefl ()
  )

noextract
let rec dep_enum_destr_tac () : T.Tac unit =
  let (goal_fun, goal_arg) = T.app_head_tail (T.cur_goal ()) in
  let _ = T.tassert (goal_fun `T.term_eq` (`dep_enum_destr)) in
  match goal_arg with
  | [_; _; (te, _); _] ->
    let (te_fun, te_arg) = T.app_head_tail (T.norm_term [delta; iota; zeta] te) in
    let _ = T.tassert (te_fun `T.term_eq` (`Cons)) in
    begin match te_arg with
    | [_; _; (tl, _)] ->
      let (tl_fun, _) = T.app_head_tail tl in
      if tl_fun `T.term_eq` (`Cons)
      then begin
        T.apply (`dep_enum_destr_cons);
        T.iseq [
          (fun () -> T.trivial (); T.qed ());
          dep_enum_destr_tac
        ];
        T.qed ()
      end
      else if tl_fun `T.term_eq` (`Nil)
      then begin
        T.apply (`dep_enum_destr_cons_nil);
        T.trivial ();
        T.qed ()
      end
      else T.fail "Unknown enum shape: not a cons/nil"
    | _ -> T.fail "Not the right arguments to cons"
    end
  | _ -> T.fail ("Not the right argument to dep_enum_destr")

noextract
let rec maybe_enum_destr_t'_tac () : T.Tac unit =
  let (goal_fun, goal_arg) = T.app_head_tail (T.cur_goal ()) in
  let _ = T.tassert (goal_fun `T.term_eq` (`maybe_enum_destr_t')) in
  match goal_arg with
  | [_; _; _; _; (tl1, _); (tl2, _); _] ->
    let (tl2_fun, _) = T.app_head_tail (T.norm_term [delta; iota; zeta] tl2) in
    if tl2_fun `T.term_eq` (`Cons)
    then begin
      T.apply (`maybe_enum_destr_cons);
      maybe_enum_destr_t'_tac ()
    end else
    if tl2_fun `T.term_eq` (`Nil)
    then begin
      T.apply (`maybe_enum_destr_nil);
      T.qed ()
    end
    else T.fail "Unknown shape for l2"
  | _ -> T.fail "Not the rigt arguments to maybe_enum_destr_t'"

noextract
let maybe_enum_destr_t_tac () : T.Tac unit =
  let (goal_fun, _) = T.app_head_tail (T.cur_goal ()) in
  let _ = T.tassert (goal_fun `T.term_eq` (`maybe_enum_destr_t)) in
  T.apply (`maybe_enum_destr_t_intro);
  maybe_enum_destr_t'_tac ()

noextract
let rec dep_maybe_enum_destr_t'_tac () : T.Tac unit =
  let (goal_fun, goal_arg) = T.app_head_tail (T.cur_goal ()) in
  let _ = T.tassert (goal_fun `T.term_eq` (`dep_maybe_enum_destr_t')) in
  match goal_arg with
  | [_; _; _; _; (tl1, _); (tl2, _); _] ->
    let (tl2_fun, _) = T.app_head_tail (T.norm_term [delta; iota; zeta] tl2) in
    if tl2_fun `T.term_eq` (`Cons)
    then begin
      T.apply (`dep_maybe_enum_destr_cons);
      dep_maybe_enum_destr_t'_tac ()
    end else
    if tl2_fun `T.term_eq` (`Nil)
    then begin
      T.apply (`dep_maybe_enum_destr_nil);
      T.qed ()
    end
    else T.fail "Unknown shape for l2"
  | _ -> T.fail "Not the rigt arguments to maybe_enum_destr_t'"

noextract
let dep_maybe_enum_destr_t_tac () : T.Tac unit =
  let (goal_fun, _) = T.app_head_tail (T.cur_goal ()) in
  let _ = T.tassert (goal_fun `T.term_eq` (`dep_maybe_enum_destr_t)) in
  T.apply (`dep_maybe_enum_destr_t_intro);
  dep_maybe_enum_destr_t'_tac ()


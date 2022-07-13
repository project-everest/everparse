module LowParse.Spec.Tac.Enum
include LowParse.Spec.Enum

module T = LowParse.TacLib

//
// The enum tactic solves goals of type ?u:eqtype with enum types that are
//   in the environment at type Type0
// So typechecking such uvars fails since F* 2635 bug fix
//   (since uvar solutions are checked with smt off)
//
// To circumvent that, we use t_apply with tc_resolve_uvars flag on,
//   so that ?u will be typechecked as soon as it is resolved,
//   resulting in an smt guard that will be added to the proofstate
//

let apply (t:T.term) : T.Tac unit =
  T.t_apply true false true t

noextract
let rec enum_tac_gen
  (t_cons_nil: T.term)
  (t_cons: T.term)
  (#key #repr: Type)
  (e: list (key * repr))
: T.Tac unit
= match e with
  | [] -> T.fail "enum_tac_gen: e must be cons"
  | [_] ->
    apply t_cons_nil;
    T.iseq [
      T.solve_vc;
      T.solve_vc;
    ];
    T.qed ()
  | _ :: e_ ->
    apply t_cons;
    T.iseq [
      T.solve_vc;
      (fun () -> enum_tac_gen t_cons_nil t_cons e_);
    ];
    T.qed ()

noextract
let maybe_enum_key_of_repr_tac
  (#key #repr: Type)
  (e: list (key * repr))
: T.Tac unit
= enum_tac_gen (quote maybe_enum_key_of_repr'_t_cons_nil') (quote maybe_enum_key_of_repr'_t_cons') e

noextract
let enum_repr_of_key_tac
  (#key #repr: Type)
  (e: list (key * repr))
: T.Tac unit
= enum_tac_gen (quote enum_repr_of_key_cons_nil') (quote enum_repr_of_key_cons') e

noextract
let synth_maybe_enum_key_inv_unknown_tac (#key: Type) (x: key) : T.Tac unit =
  let open T in
    destruct (quote x);
    to_all_goals (fun () ->
      let breq = intros_until_squash () in
      rewrite breq;
      norm [delta; iota; zeta; primops];
      trivial ();
      qed ()
    );
    qed ()

noextract
let forall_maybe_enum_key_known_tac () : T.Tac unit =
      let open T in
      norm [delta; iota; zeta; primops];
      trivial ();
      qed ()

noextract
let forall_maybe_enum_key_unknown_tac () : T.Tac unit =
      let open T in
      let x = intro () in
      norm [delta; iota; zeta; primops];
      trivial ();
      qed ()

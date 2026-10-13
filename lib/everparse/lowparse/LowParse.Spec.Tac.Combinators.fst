module LowParse.Spec.Tac.Combinators
include LowParse.Spec.Combinators

open LowParse.TacLib

(* for structs *)

let rec destruct_lhs_pairs (t: FStar.Tactics.term) (n: nat) : FStar.Tactics.Tac unit =
  if n = 0
  then trefl ()
  else begin
    destruct t;
    let a = intro () in
    let b = intro () in
    let abeq = intro () in
    rewrite abeq;
    destruct_lhs_pairs (binder_to_term a) (n - 1)
  end

let synth_pairs_to_struct_to_pairs_tac' (n: nat) : Tac unit =
  norm [delta]; // _only [(`%synth_inverse); (`%t8')]];
  let x = forall_intro () in
  destruct_lhs_pairs (binder_to_term x) n

let synth_pairs_to_struct_to_pairs_tac (#struct_t: Type) (#pairs_t: Type) (recip: struct_t -> GTot pairs_t) (n: nat) : Tac unit =
  apply (quote (synth_inverse_synth_injective' recip));
  synth_pairs_to_struct_to_pairs_tac' n

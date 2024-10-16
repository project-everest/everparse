module CBOR.Pulse.Raw.Util
open Pulse.Lib.Pervasives

// FIXME: this file is VERY brittle

let perm_div (p1 p2: perm) : Tot perm = p1 /. p2

let perm_mul (p1 p2: perm) : Tot perm = p1 *. p2

#reset-options "--z3cliopt smt.arith.nl=true --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native --z3rlimit 16"

#restart-solver

let perm_mul_assoc
  (p1 p2 p3: perm)
: Lemma
  (ensures (p1 `perm_mul` (p2 `perm_mul` p3) == (p1 `perm_mul` p2) `perm_mul` p3))
  [SMTPatOr [
    [SMTPat (p1 `perm_mul` (p2 `perm_mul` p3))];
    [SMTPat ((p1 `perm_mul` p2) `perm_mul` p3)];
  ]]
= ()

let perm_1_l
  (p: perm)
: Lemma
  (1.0R `perm_mul` p == p)
= ()

let half_mul (a b: real) : Lemma
  ((a *. b) /. 2.0R == a *. (b /. 2.0R))
= ()

let perm_mul_div (a b: perm) : Lemma
  (a `perm_mul` (b `perm_div` a) == b)
= ()
# Fix EverParse proof failures after F* hash advance

## Context

`opt/hashes.Makefile` was advanced across the last two commits on this branch:

```
7174af7bbb53fda0271a57bc0a714858a3acab1e  (F* hash before both bumps)
  -> dfd3d2b65900b68d559b7ca8cb9e363c806cfd3c  ("advance F*", commit b24b45f4c)
  -> fbaf80c83d61c667d2e12f21fa77c5816a9bdde2  ("Advance F*/Karamel hashes", commit 04818c475)
```

Building EverParse against the new F* commit range broke 3 previously-verified
proofs (recorded in `test.log`). All three failures are consequences of F*
commits in that range that changed how the typechecker determines/propagates
expected types and postconditions, in particular:

- `39160cb4f5` "Choose a match's result type from its branches, not from the context"
- `5b368bac67` "Give a match the result type its branches established"
- `238d8d6165` / `e4e983c9fa` / `ea3d7b68a7` (the "push postcondition" series):
  the expected postcondition is now pushed into the body's expected type (and
  through type ascriptions) more aggressively than before.

The net effect is that several proofs which used to be discharged by SMT via
an "ambient"/accumulated set of hypotheses at the *end* of a function body
now have parts of their postcondition checked earlier / against a more
precise (and sometimes harder) goal at each branch of a `match`/`if`. Where
the old encoding let Z3 combine facts opportunistically, the new encoding
requires the intermediate facts to be established more explicitly. All fixes
below add the missing explicit reasoning steps (or, in one case, more z3
budget for a step whose cost genuinely grew); none of them change the
semantics/spec of any function.

## Fixes

### 1. `src/lowparse/LowParse.Spec.BitFields.fst` — `synth_bitfield_injective`

Failure: `Subtyping check failed ... Failed to prove: x == y` at the closing
assert of the injectivity proof.

The lemma proves `x == y` from `get_bitfield (cl.v x) 0 tot == get_bitfield (cl.v y) 0 tot`
via `get_bitfield_full`, ending in
`assert (cl.uint_to_t (cl.v x) == cl.uint_to_t (cl.v y))`. That final
assertion is no longer accepted as a proof of `x == y` directly: previously
Z3 could chain it together with the (patterned) lemmas
`uint_t_uint_to_t_v : cl.uint_to_t (cl.v x) == x` after the fact, but the
match's expected-type change means the final expression in the closure is now
checked directly against `unit{x == y}`.

Fix: make the intermediate step `cl.v x == cl.v y` explicit, then explicitly
invoke `cl.uint_to_t_v x` / `cl.uint_to_t_v y` (the two projector lemmas that
say `cl.uint_to_t (cl.v x) == x`), and assert `x == y` as the literal final
expression, matching the exact shape of the required postcondition.

### 2. `src/cddl/spec/CDDL.Spec.MapGroup.Base.fst` — `map_group_match_item_for_eq_gen`

Failure: 5 cascading `Subtyping check failed` errors, all rooted in the
`cut = true` branch of this lemma, which previously ended each case with a
bare `()`.

This lemma proves an equational unfolding of
`map_group_match_item_for cut k ty l` for all four combinations of
(`cbor_map_get l k` is `None`/`Some v`) x (`ty v` true/false when `Some`).
Only the "`ty v` false" sub-case had explicit reasoning (needed to derive
`MapGroupCutFailure` via an *existential* witness for `map_group_match_item_cut`'s
cut-failure predicate). The "`cbor_map_get l k == None`" and "`ty v` true"
sub-cases both need to derive that **no** entry in the relevant map satisfies
the cut-failure witness predicate — i.e. a *negative*/universally-quantified
fact — which the old encoding discharged automatically but the new one does
not.

Fix: add explicit reasoning to both previously-implicit branches:
- `None` case: derive `~ (cbor_map_defined k l)` from `cbor_map_get l k == None`,
  lift it to `forall v' . ~ (cbor_map_mem (k, v') l)` (using
  `bring_cbor_map_defined_alt ()`), and use it to show the cut-exists
  predicate is false on the pre-processed singleton set, hence
  `map_group_match_item_for true k ty l == MapGroupResult MPS.empty`.
- `Some v`, `ty v = true` case: derive `cbor_map_disjoint l1 l2` (already
  implied by the `cbor_map_sub` postcondition used to build `l2`), combine it
  with `cbor_map_defined k l1` (trivial from `l1 = cbor_map_singleton k v`) to
  get `~ (cbor_map_defined k l2)`, then as above show the cut-exists predicate
  is false, giving `map_group_match_item_for true k ty l == MapGroupResult (MPS.singleton (l1, l2))`.

No lemma signatures, specs, or preconditions changed — only added proof steps.

### 3. `src/cddl/pulse/CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma13.fst` — `invariant_insert_dup`

Failure: `The SMT query timed out, you might want to increase the rlimit` on
the closing `()` of `invariant_insert_dup`.

Unlike the other two failures, this is a genuine solver-effort regression:
the final proof obligation combines a large invariant-preservation goal built
out of several lemma applications, and the additional bookkeeping introduced
by the F* postcondition-push changes increased the amount of case-splitting
Z3 has to perform to close it out. No missing lemma or logical gap was found
after inspection; increasing the rlimit resolves it.

Fix: bumped the local `--z3rlimit` for this file from 128 to 512
(`#push-options "--z3rlimit 512 --fuel 1 --ifuel 1 --z3seed 42"`).

## Verification

- Reproduced all 3 original failures against the same F* head
  (`fbaf80c83d61c667d2e12f21fa77c5816a9bdde2`) referenced in
  `opt/hashes.Makefile`.
- After the above fixes, rebuilt each of the 3 affected files individually
  and confirmed each is now `Verified module: ...` / `All verification
  conditions discharged successfully`.
- Ran the full suite: `make -j$(nproc) -k test` completes with **exit code 0**
  (no remaining `Error` lines, other than the pre-existing benign
  `Error while extracting (["FStar", "List"], ...)` KaRaMeL diagnostic lines
  that were already present in the original `test.log` before this fix and do
  not fail the build).

## Files changed

- `src/lowparse/LowParse.Spec.BitFields.fst`
- `src/cddl/spec/CDDL.Spec.MapGroup.Base.fst`
- `src/cddl/pulse/CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma13.fst`

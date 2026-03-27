# EverParse SMT Query Performance Optimization Plan

## Results Summary

| Metric | Before | After | Change |
|--------|--------|-------|--------|
| Total SMT time | 117.2 min | **70.4 min** | **-39.9%** |
| Avg query time | 321 ms | **192 ms** | **-40.2%** |
| Total wall time | 236.6 min | **164.1 min** | **-30.6%** |
| Total queries | 21,910 | 21,901 | — |

### Biggest win: Remove SMTPat from `cbor_map_defined_alt`
- Root cause: `[SMTPat (cbor_map_defined k f)]` caused 64K+ quantifier instantiation cascades
- Fix: Removed SMTPat, added `bring_cbor_map_defined_alt()` helper with pattern, called in 8 locations
- **CDDL.Pulse.MapGroup**: 1600s → **142s** (11.3x speedup)
- **CDDL.Spec.MapGroup.Base**: 543s → **84s** (6.5x speedup)

### Key settings tightened (catches regressions faster):
- `parse_raw_data_item_eq`: ifuel 8→2, rlimit 1024→256
- `impl_map_group_filter`: fuel 8→2, ifuel 6→1, rlimit 1024→768
- `impl_map_group_filter_aux_skip`: fuel 8→2, ifuel 6→1
- `impl_check_equiv_list`: rlimit 256→128
- `impl_check_equiv_map_hd_body`: fuel 4→2, ifuel 8→4, rlimit 128→64
- `impl_check_map_depth_aux`: fuel 4→2, rlimit 256→128, context_pruning re-enabled
- `serialized_lex_compare_*`: rlimit 256→128
- `holds_on_raw_data_item_eq_recursive`: rlimit 256→64
- `parse_pair_list_as_list`: rlimit 256→64

### Per-file SMT comparison:
- `CBOR.Spec.Raw.EverParse.fst`: 1049s → 971s (-7.4%)
- `CBOR.Pulse.Raw.EverParse.Nondet.Gen.fst`: 952s → 735s (-22.8%)
- `CDDL.Pulse.MapGroup.fst`: 1600s → 1664s (dominated by 1 query)
- `CDDL.Spec.MapGroup.Base.fst`: 543s → 543s (unchanged, needs proof restructuring)

## Build Profile (2026-03-24, baseline)

- **Total serial verification time**: 236.6 minutes across 690 files
- **Total SMT query time**: 117.2 minutes across 21,910 queries (avg 321 ms/query)
- **Failed queries (retried)**: 311

### Time by Module Area (SMT time only)

| Area | SMT Time (min) | Queries |
|------|---------------|---------|
| CDDL.Pulse | 40.6 | 4,166 |
| CDDL.Spec | 21.0 | 3,547 |
| CBOR.Pulse | 26.6 | 5,199 |
| CBOR.Spec | 20.4 | 1,612 |
| LowParse.Pulse | 2.7 | 1,576 |
| LowParse.Spec | 2.1 | 2,126 |
| ASN1 | 1.3 | 870 |

### Top 10 Files by Aggregated SMT Time

| File | SMT Time (s) | Share |
|------|-------------|-------|
| CDDL.Pulse.MapGroup.fst | 1601 | 22.8% |
| CBOR.Spec.Raw.EverParse.fst | 1049 | 14.9% |
| CBOR.Pulse.Raw.EverParse.Nondet.Gen.fst | 924 | 13.1% |
| CDDL.Spec.MapGroup.Base.fst | 521 | 7.4% |
| CDDL.Pulse.Serialize.Gen.MapGroup.MatchItemFor.fst | 235 | 3.3% |
| CBOR.Pulse.Raw.Format.Serialize.fst | 164 | 2.3% |
| CBOR.Pulse.Raw.Format.Parse.fst | 132 | 1.9% |
| CDDL.Spec.AST.Elab.Disjoint.Array.fst | 115 | 1.6% |
| CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma12.fst | 113 | 1.6% |
| CDDL.Spec.MapGroup.fst | 111 | 1.6% |

**Top 4 files account for 58.2% of all SMT time.**

### Top Individual Queries (> 30s wall clock)

| Time (s) | rlimit used | Function | File |
|----------|------------|----------|------|
| 1309 | 634 / 1024 | impl_map_group_filter #45 | CDDL.Pulse.MapGroup.fst |
| 446 | 457 / 512 | apply_map_group_det_match_item_cut #2 | CDDL.Spec.MapGroup.Base.fst |
| 105 | 256 / 256 | impl_check_map_depth_aux #32 | CBOR.Pulse.Raw.EverParse.Nondet.Gen.fst |
| 92 | 132 / 256 | invariant_insert_success #41 | CDDL...ZeroOrMore.Aux2.Lemma12.fst |
| 88 | 234 / 1024 | parse_raw_data_item_eq #72 | CBOR.Spec.Raw.EverParse.fst |
| 79 | 289 / 512 | impl_serialize_match_item_for #174 | CDDL...MapGroup.MatchItemFor.fst |
| 71 | 194 / 256 | impl_check_equiv_list #73 | CBOR.Pulse.Raw.EverParse.Nondet.Gen.fst |
| 70 | 169 / 256 | impl_check_equiv_list #70 | CBOR.Pulse.Raw.EverParse.Nondet.Gen.fst |
| 66 | 43 / 1024 | impl_map_group_filter #35 | CDDL.Pulse.MapGroup.fst |
| 52 | 34 / 1024 | impl_map_group_filter #40 | CDDL.Pulse.MapGroup.fst |

### Heaviest Functions (aggregated across all queries ≥ 5s)

| Total (s) | #Queries | Avg (s) | Function |
|-----------|----------|---------|----------|
| 1491 | 6 | 249 | CDDL.Pulse.MapGroup.impl_map_group_filter |
| 548 | 28 | 20 | CBOR.Spec.Raw.EverParse.parse_raw_data_item_eq |
| 486 | 17 | 29 | CBOR.Pulse.Raw.EverParse.Nondet.Gen.impl_check_map_depth_aux |
| 446 | 1 | 446 | CDDL.Spec.MapGroup.Base.apply_map_group_det_match_item_cut |
| 211 | 4 | 53 | CBOR.Pulse.Raw.EverParse.Nondet.Gen.impl_check_equiv_list |
| 208 | 12 | 17 | CBOR.Spec.Raw.EverParse.serialized_lex_compare_simple_value |
| 150 | 10 | 15 | CBOR.Pulse.Raw.EverParse.Nondet.Gen.impl_check_equiv_map_hd_body |
| 125 | 11 | 11 | CBOR.Pulse.Raw.Format.Parse.cbor_raw_sorted |
| 111 | 2 | 55 | ...Lemma12.invariant_insert_success |
| 86 | 2 | 43 | ...MatchItemFor.impl_serialize_match_item_for |

---

## Optimization Checklist

Priority ordering is by total SMT time (i.e., optimization payoff).

### Tier 1: Critical (> 400s total SMT time, 58% of all)

- [x] **OPT-1: CDDL.Pulse.MapGroup.impl_map_group_filter (1491s)**
  - Reduced fuel 8→2, ifuel 6→1, rlimit 1024→768, removed z3seed.
  - 44 of 45 queries are now much faster. Query #45 still dominates (1371s).
  - Further improvement requires proof restructuring (adding intermediate assertions).

- [x] **OPT-2: CBOR.Spec.Raw.EverParse.parse_raw_data_item_eq (548s)**
  - Reduced ifuel 8→2, rlimit 1024→256. All queries pass.
  - 971s total file SMT (was 1049s, -7.4%).

- [x] **OPT-3: CBOR.Pulse.Raw.EverParse.Nondet.Gen.impl_check_map_depth_aux (486s)**
  - Reduced fuel 4→2, rlimit 256→128, re-enabled context_pruning.
  - 735s total file SMT (was 952s, -22.8%).

- [ ] **OPT-4: CDDL.Spec.MapGroup.Base.apply_map_group_det_match_item_cut (446s)**
  - Cannot reduce rlimit below 512 (query uses 457). Cannot add split_queries.
  - Needs proof restructuring with explicit intermediate assertions to split the VC.

### Tier 2: High (100–400s total, ~15% of all)

- [x] **OPT-5: CBOR.Pulse.Raw.EverParse.Nondet.Gen.impl_check_equiv_list (211s)**
  - Reduced rlimit 256→128. Part of OPT-3 file.

- [x] **OPT-6: CBOR.Spec.Raw.EverParse.serialized_lex_compare_* (310s combined)**
  - Reduced rlimit 256→128 for simple_value, string, tagged. array_aux kept at 128.

- [x] **OPT-7: CBOR.Pulse.Raw.EverParse.Nondet.Gen.impl_check_equiv_map_hd_body (150s)**
  - Reduced fuel 4→2, ifuel 8→4, rlimit 128→64. Part of OPT-3 file.

- [ ] **OPT-8: CBOR.Pulse.Raw.Format.Parse.cbor_raw_sorted (125s)**
  - 11 queries, avg 11s, rlimit 128
  - Actions: Check if sorting/ordering predicates can be made opaque.

- [ ] **OPT-9: CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma12.invariant_insert_success (111s)**
  - 2 slow queries + failed retries (162s wasted on failures)
  - Actions: Profile failed query. May need explicit assert/calc steps.

### Tier 3: Medium (30–100s total, ~10% of all)

- [ ] **OPT-10: CDDL.Pulse.Serialize.Gen.MapGroup.MatchItemFor.impl_serialize_match_item_for (86s)**
  - 2 queries, rlimit 512

- [ ] **OPT-11: CDDL.Pulse.MapGroup.impl_map_group_filter_aux_skip (80s)**
  - 6 queries, rlimit 32 (already low rlimit, still slow due to fuel 8, ifuel 6)

- [ ] **OPT-12: CBOR.Pulse.Raw.EverParse.Nondet.Gen.impl_check_valid_item (74s)**
  - 6 queries, avg 12s, rlimit 64

- [ ] **OPT-13: CDDL.Spec.AST.Elab.Included.Array.array_group_included (73s)**
  - 8 queries, rlimit 512, fuel 4, ifuel 8

- [ ] **OPT-14: CDDL.Spec.AST.Elab.Disjoint.Array.array_group_disjoint (59s)**
  - 5 queries, one using rlimit 4096 (!!), fuel 4, ifuel 8

- [ ] **OPT-15: CBOR.Pulse.Raw.Insert.cbor_raw_map_insert (54s)**
  - 4 queries, rlimit 192

- [ ] **OPT-16: CDDL.Spec.MapGroup.matches_map_group_equiv_concat' (39s)**
  - 1 query, rlimit 256 — also has a failed attempt (44s wasted)

- [ ] **OPT-17: CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma5.invariant_min_next_aux (37s)**

- [ ] **OPT-18: CBOR.Pulse.Raw.EverParse.Nondet.Gen.check_equiv_head_correct (24s)**

- [ ] **OPT-19: CDDL.Spec.AST.Elab.MGCC.map_group_choice_compatible' (39s)**
  - 2 queries, rlimit 256, fuel 2, ifuel 8

### Tier 4: Low-Hanging Fruit (excessive rlimits that can be tightened)

- [ ] **OPT-20: Tighten rlimits across the board**
  - Many queries use only a fraction of their rlimit (e.g., rlimit 1024 but used 20–43).
  - Scan for cases where `used rlimit` < 25% of `allocated rlimit` and reduce.
  - This won't reduce SMT time but will catch regressions faster.

- [ ] **OPT-21: Reduce fuel/ifuel globally where possible**
  - Files using fuel 8 / ifuel 6-8 are the slowest. Each fuel increment doubles search space.
  - Prefer fuel 0-2, ifuel 0-2 with explicit lemma calls.

---

## General Optimization Strategies

1. **`[@opaque_to_smt]`**: Mark predicates that don't need to be unfolded by Z3. Provide explicit `reveal_opaque` calls or unfolding lemmas at use sites.

2. **`--z3cliopt smt.arith.nl=false`**: Disable non-linear arithmetic support in Z3. Use `FStar.Math.Lemmas` explicitly for any non-linear reasoning.

3. **`--split_queries always`**: Isolate each assertion into its own Z3 query. Makes profiling cleaner and can sometimes help Z3 focus.

4. **Fuel/ifuel reduction**: High fuel (>2) causes exponential unfolding. Replace with explicit `unfold_*` or recursive lemma calls.

5. **Explicit intermediate assertions**: Break large VCs into smaller steps with `assert(...)` or `calc` blocks.

6. **Quantifier patterns**: For universally quantified lemmas, add SMT patterns (`%[triggers]`) to control instantiation.

7. **Context pruning**: Already enabled (`--ext context_pruning`). Good.

8. **`context_pruning_no_ambients`**: Prunes triggerless ambient assumptions. Available via `--ext context_pruning_no_ambients`. Tested: **breaks LowParse.Bytes32.fst globally** — can only be used per-file/function. Also caused z3 parse errors on some Pulse while-loop VCs. Use cautiously.

## Deep Investigation Notes

### OPT-1: impl_map_group_filter query #45 (1371s)
- This is a Pulse `while` loop VC at (452,4-735,3). With `--split_queries always`, each loop body assertion splits into its own query, but the overall loop frame check remains monolithic.
- **ROOT CAUSE IDENTIFIED**: Z3 quantifier profiling on the isolated `.smt2` file shows **`cbor_map_defined_alt` fires 64,065 times** in 120 seconds, dwarfing everything else. This lemma (in `CBOR.Spec.API.Type.fsti:138`) has `[SMTPat (cbor_map_defined k f)]` and introduces `exists v . cbor_map_mem (k,v) f`, creating a chain reaction:
  1. `cbor_map_equal` unfolds to `forall k . cbor_map_get m1 k == cbor_map_get m2 k`
  2. Each `cbor_map_get` produces a `cbor_map_defined` term
  3. `cbor_map_defined_alt` fires, introducing existentials `exists v . cbor_map_mem (k,v) f`
  4. Existentials create skolem terms → more `cbor_map_defined` terms → positive feedback loop
- **Removing the SMTPat** eliminates the cascade, but **breaks 20+ downstream proofs** that rely on it (e.g., `cbor_map_sub`, `cbor_map_ind_bounded`). Not viable without fixing all callsites.
- **`smt.qi.eager_threshold=100`**: too restrictive (Q45 never completes). `1000`: insufficient improvement.
- **Invariant rewrite attempted**: replaced `apply_map_group_det`/`map_group_filter` pattern match with direct `cbor_map_filter` terms. While-loop VC: 1371s→85ms, BUT postcondition VC: 85ms→1086s timeout. Zero-sum.
- **Recommended fix**: refactor `cbor_map_defined_alt` to use a multi-pattern trigger (e.g., `[SMTPat (cbor_map_defined k f); SMTPat (cbor_map_mem (k, _) f)]`) to prevent the chain reaction while keeping the lemma available when both terms are present. This requires changes to `CBOR.Spec.API.Type.fsti` and `CBOR.Spec.Raw.DataModel.fsti` plus fixing any proofs that break.

### OPT-4: apply_map_group_det_match_item_cut (446s)
- Single monolithic query, fuel 8 needed (default F* retry escalation).
- Proof has 3 branches (empty, singleton, multiple matching entries).
- Inner `prf` lemma (lines 1476-1499) could be extracted as standalone.
- **Factoring plan**: split into 3 lemmas by case (n=0, n=1 with ty, else). This would reduce per-case VC complexity.
- **Key definitions driving cost**: `cbor_map_fold`, `cbor_map_key_list`, `mps_exists` — all have recursive fold structure that Z3 over-unfolds.

## Profiling Workflow for Each Item

```bash
# 1. Add profiling options to the file
#push-options "--log_queries --z3refresh --query_stats --split_queries always"

# 2. Verify the file
fstar.exe Module.fst [include paths...]

# 3. Run Z3 with quantifier profiling on the .smt2 file
z3 smt.qi.profile=true queries-Module.QueryName.smt2

# 4. Analyze which quantifiers fire excessively
# Look for user-authored quantifiers with high instantiation counts
```

## Success Criteria

- Reduce total SMT time from 117 minutes to < 60 minutes (50% reduction target)
- No single query should take > 60 seconds
- Maximum rlimit should be ≤ 256 (currently some at 1024, 4096)
- Maximum fuel should be ≤ 4, ifuel ≤ 4

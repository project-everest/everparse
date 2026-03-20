# Error 308: Friend Dependencies Fail in fly_deps Mode

## Problem

`ADMIT=1 make src/cbor/spec/raw/CBOR.Spec.Raw.fst.checked` fails with:
```
* Error 308:
  - Friend dependences must be declared as the first dependence on a module.
  - A non-friend dependence was already found on module CBOR.Spec.Raw.DataModel.
```

## Root Cause

The bug is in F*'s `fly_deps` mode (now enabled by default in
`FStarC.Options.Ext.fst:30`), specifically in `FStarC.Universal.fst` around
line 695-703.

### The Pattern That Triggers the Bug

When a module C friends both modules A and B, and B depends on A through a
regular (non-friend) dependency:

1. `fly_deps` processes C.fst declarations one at a time
2. `friend B` is processed first — B and its transitive dependency A are loaded.
   A is loaded **via interface only** (PreferInterface edge), since B's dep on A
   is non-friend.
3. `friend A` is processed next — needs to load A's **implementation** (.fst).
   A.fst is NOT in `deps.all_files` (only A.fsti was), so `collect_deps_of_decl`
   includes A.fst in the files to load.
4. The check at Universal.fst:697 sees that module A is already in `env.modules`
   (loaded via interface) and raises Error 308.

### Why It Worked Before

- `fly_deps` was not the default; the old `widen_deps` mechanism handled
  retroactive friend upgrades.
- `fly_deps` was made default in commit `41913c70f2`.
- The Error 308 check was added in commit `8e0002d432`.

### Additional Bug in FStarC.Parser.Dep.fst

Line 1199 has a variable name bug:
```fstar
| PreferInterface mname' -> mname' = mname   (* should be: mname' = module_name *)
```
This compares against the wrong variable (`mname` = current module, instead of
`module_name` = the module being friended). This check happens to be ineffective
due to the wrong comparison, and the actual error comes from Universal.fst.

## Minimal Reproduction

Files in `opt/FStar/tests/friends/5/`:
- A.fsti, A.fst: Module A (abstract value)
- B.fsti, B.fst: Module B (depends on A via `open`, not `friend`)
- C.fsti, C.fst: Module C (friends both B and A)

```bash
# Fails with fly_deps (default):
fstar.exe --ext fly_deps tests/friends/5/C.fst --include tests/friends/5

# Works without fly_deps:
fstar.exe --ext fly_deps=false tests/friends/5/C.fst --include tests/friends/5
```

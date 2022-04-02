module LowParse.SteelST.ArrayPtr
include LowParse.Steel.ArrayPtr

open Steel.Memory
open Steel.FractionalPermission
module SEA = Steel.Effect.Atomic
module SZ = LowParse.Steel.StdInt
module SC = Steel.ST.Coercions
module C = Steel.ST.Combinators
open Steel.ST.Util

let arrayptr
  (#base #a: Type0)
  (r: t base a)
  ([@@@smt_fallback] value: v base a)
= varrayptr r `C.vselect` value

let arrayptr_not_null'
  (#opened: _)
  (#base #a: Type)
  (#value: v base a)
  (x: t base a)
: SEA.SteelGhostT (squash (g_is_null x == false)) opened
    (x `arrayptr` value)
    (fun _ -> x `arrayptr` value)
=
  C.vselect_elim0 (varrayptr x) _;
  varrayptr_not_null x;
  let _ = C.vselect_intro0 (varrayptr x) in
  ()

let arrayptr_not_null
  (#opened: _)
  (#base #a: Type)
  (#value: v base a)
  (x: t base a)
: STGhostT (squash (g_is_null x == false)) opened
    (x `arrayptr` value)
    (fun _ -> x `arrayptr` value)
=
  SC.coerce_ghost (fun _ -> arrayptr_not_null' x)

let arrayptr_or_null
  (#base #a: Type0)
  (r: t base a)
  ([@@@smt_fallback] value: Ghost.erased (option (v base a)))
= varrayptr_or_null r `C.vselect` value

let intro_arrayptr_or_null_none'
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
  (sq: squash (g_is_null x == true))
  ()
: SEA.SteelGhostT unit opened
    emp
    (fun _ -> arrayptr_or_null x None)
=
  intro_varrayptr_or_null_none x;
  let _ = C.vselect_intro0 (varrayptr_or_null x) in
  ()

let intro_arrayptr_or_null_none
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
  (sq: squash (g_is_null x == true))
: STGhostT unit opened
    emp
    (fun _ -> arrayptr_or_null x None)
=
  SC.coerce_ghost (intro_arrayptr_or_null_none' x sq)

let intro_arrayptr_or_null_some'
  (#opened: _)
  (#base #a: Type)
  (#value: v base a)
  (x: t base a)
  ()
: SEA.SteelGhostT unit opened
    (arrayptr x value)
    (fun _ -> arrayptr_or_null x (Some value))
=
  C.vselect_elim0 (varrayptr x) _;
  intro_varrayptr_or_null_some x;
  let _ = C.vselect_intro0 (varrayptr_or_null x) in
  ()

let intro_arrayptr_or_null_some
  (#opened: _)
  (#base #a: Type)
  (#value: v base a)
  (x: t base a)
: STGhostT unit opened
    (arrayptr x value)
    (fun _ -> arrayptr_or_null x (Some value))
=
  SC.coerce_ghost (intro_arrayptr_or_null_some' x)

let extract_some
  (#a: Type)
  (v: option a)
  (sq: squash (Some? v))
: Tot a
= Some?.v v

[@@solve_can_be_split_lookup; (solve_can_be_split_for exists_)]
let _intro_can_be_split_exists = intro_can_be_split_exists

[@@solve_can_be_split_forall_dep_lookup; (solve_can_be_split_forall_dep_for exists_)]
let _intro_can_be_split_forall_dep_exists = intro_can_be_split_forall_dep_exists

[@@solve_can_be_split_lookup; (solve_can_be_split_for pure)]
let _intro_can_be_split_pure = intro_can_be_split_pure

[@@solve_can_be_split_forall_dep_lookup; (solve_can_be_split_forall_dep_for pure)]
let _intro_can_be_split_forall_dep_pure = intro_can_be_split_forall_dep_pure

let elim_arrayptr_or_null_some'
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
  (sq: squash (g_is_null x == false \/ Some? value))
  ()
: SEA.SteelGhostT (v base a) opened
    (arrayptr_or_null x value)
    (fun value' -> arrayptr x value' `star` pure (Ghost.reveal value == Some value'))
= C.vselect_elim0 (varrayptr_or_null x) _;
  elim_varrayptr_or_null_some x;
  let res0 = C.vselect_intro0 (varrayptr x) in
  let res : v base a = Ghost.reveal res0 in
  SEA.change_equal_slprop
    (varrayptr x `C.vselect` res0)
    (arrayptr x res);
  res

let elim_arrayptr_or_null_some
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
  (sq: squash (g_is_null x == false \/ Some? value))
: STGhostT (v base a) opened
    (arrayptr_or_null x value)
    (fun value' -> arrayptr x value' `star` pure (Ghost.reveal value == Some value'))
= SC.coerce_ghost (elim_arrayptr_or_null_some' x sq)

let elim_arrayptr_or_null_none'
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
  (sq: squash (g_is_null x == true \/ None? value))
  ()
: SEA.SteelGhostT unit opened
    (arrayptr_or_null x value)
    (fun _ -> pure (g_is_null x == true /\ Ghost.reveal value == None))
=
  C.vselect_elim0 (varrayptr_or_null x) _;
  elim_varrayptr_or_null_none x;
  noop ()

let elim_arrayptr_or_null_none
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
  (sq: squash (g_is_null x == true \/ None? value))
: STGhostT unit opened
    (arrayptr_or_null x value)
    (fun _ -> pure (g_is_null x == true /\ Ghost.reveal value == None))
= SC.coerce_ghost (elim_arrayptr_or_null_none' x sq)

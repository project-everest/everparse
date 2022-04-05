module LowParse.SteelST.ArrayPtr
module S = LowParse.Steel.ArrayPtr

open Steel.Memory
open Steel.FractionalPermission
module SEA = Steel.Effect.Atomic
module SZ = LowParse.Steel.StdInt
module SC = Steel.ST.Coercions
module C = Steel.ST.Combinators
open Steel.ST.Util

let t = S.t
let v = S.v
let g_is_null = S.g_is_null
let array = S.array
let length = S.length
let len = S.len
let array_of #base #a (v: v base a) : Tot (array base a) =
  v.S.array
let contents_of #base #a (v: v base a) : GTot (Seq.lseq a (length (array_of v))) =
  v.S.contents
let contents_of' #base #a (v: v base a) : GTot (Seq.seq a) =
  contents_of v

let arrayptr
  (#base #a: Type0)
  (r: t base a)
  ([@@@smt_fallback] value: v base a)
= S.varrayptr r `C.vselect` value

let intro_arrayptr'
  (#opened: _)
  (#base #a: Type0)
  (r: t base a)
: SEA.SteelGhost (v base a) opened
    (S.varrayptr r)
    (fun res -> arrayptr r res)
    (fun _ -> True)
    (fun h res _ -> res == h (S.varrayptr r))
= let res0 = C.vselect_intro0 (S.varrayptr r) in
  let res : v base a = Ghost.reveal res0 in
  SEA.change_equal_slprop
    (S.varrayptr r `C.vselect` res0)
    (arrayptr r res);
  res

let elim_arrayptr'
  (#opened: _)
  (#base #a: Type0)
  (#value: v base a)
  (r: t base a)
: SEA.SteelGhost unit opened
    (arrayptr r value)
    (fun _ -> S.varrayptr r)
    (fun _ -> True)
    (fun _ _ h' -> h' (S.varrayptr r) == value)
= C.vselect_elim0 (S.varrayptr r) _

let arrayptr_not_null'
  (#opened: _)
  (#base #a: Type)
  (#value: v base a)
  (x: t base a)
: SEA.SteelGhostT (squash (g_is_null x == false)) opened
    (x `arrayptr` value)
    (fun _ -> x `arrayptr` value)
=
  elim_arrayptr' x;
  S.varrayptr_not_null x;
  let _ = intro_arrayptr' x in
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
= S.varrayptr_or_null r `C.vselect` value

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
  S.intro_varrayptr_or_null_none x;
  let _ = C.vselect_intro0 (S.varrayptr_or_null x) in
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
  C.vselect_elim0 (S.varrayptr x) _;
  S.intro_varrayptr_or_null_some x;
  let _ = C.vselect_intro0 (S.varrayptr_or_null x) in
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
  ()
: SEA.SteelGhost (v base a) opened
    (arrayptr_or_null x value)
    (fun value' -> arrayptr x value')
    (fun _ -> g_is_null x == false \/ Some? value)
    (fun _ value' _ -> Ghost.reveal value == Some value')
= C.vselect_elim0 (S.varrayptr_or_null x) _;
  S.elim_varrayptr_or_null_some x;
  let res0 = C.vselect_intro0 (S.varrayptr x) in
  let res : v base a = Ghost.reveal res0 in
  SEA.change_equal_slprop
    (S.varrayptr x `C.vselect` res0)
    (arrayptr x res);
  res

let elim_arrayptr_or_null_some
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
: STGhost (v base a) opened
    (arrayptr_or_null x value)
    (fun value' -> arrayptr x value')
    (g_is_null x == false \/ Some? value)
    (fun value' -> Ghost.reveal value == Some value')
= SC.coerce_ghost (elim_arrayptr_or_null_some' x)

let elim_arrayptr_or_null_none'
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
  ()
: SEA.SteelGhost unit opened
    (arrayptr_or_null x value)
    (fun _ -> emp)
    (fun _ -> g_is_null x == true \/ None? value)
    (fun _ _ _ -> g_is_null x == true /\ Ghost.reveal value == None)
=
  C.vselect_elim0 (S.varrayptr_or_null x) _;
  S.elim_varrayptr_or_null_none x;
  noop ()

let elim_arrayptr_or_null_none
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
: STGhost unit opened
    (arrayptr_or_null x value)
    (fun _ -> emp)
    (g_is_null x == true \/ None? value)
    (fun _ -> g_is_null x == true /\ Ghost.reveal value == None)
= SC.coerce_ghost (elim_arrayptr_or_null_none' x)

let is_null'
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
  ()
: SEA.SteelAtomicBase bool false opened Unobservable
    (arrayptr_or_null x value)
    (fun res -> arrayptr_or_null x value)
    (fun _ -> True)
    (fun _ res _ -> res == None? value /\ res == g_is_null x)
=
  C.vselect_elim0 (S.varrayptr_or_null x) _;
  let res = S.is_null x in
  let _ = C.vselect_intro0 (S.varrayptr_or_null x) in
  SEA.return res

let is_null
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
: STAtomicBase bool false opened Unobservable
    (arrayptr_or_null x value)
    (fun res -> arrayptr_or_null x value)
    (True)
    (fun res -> res == None? value /\ res == g_is_null x)
= SC.coerce_atomic (is_null' x)

let adjacent = S.adjacent
let merge = S.merge
let merge_into = S.merge_into

let arrayptr0
  (#base #a: Type0)
  (r: t base a)
  (value: v base a)
= S.varrayptr r `C.vselect` value

let join' (#opened: _) (#base #a:Type) (#vl #vr: v base a) (al ar:t base a)
  (_: unit)
  : SEA.SteelGhost (v base a) opened
          (arrayptr0 al vl `star` arrayptr ar vr)
          (fun res -> arrayptr al res)
          (fun _ ->
             adjacent (array_of vl) (array_of vr)
          )
          (fun _ res _ ->
             merge_into (array_of vl) (array_of vr) (array_of res) /\
             contents_of' res == contents_of vl `Seq.append` contents_of vr
          )
=
  elim_arrayptr' al;
  elim_arrayptr' ar;
  S.join al ar;
  let res = intro_arrayptr' al in
  noop ();
  res

let join (#opened: _) (#base #a:Type) (#vl #vr: v base a) (al ar:t base a)
  : STGhost (v base a) opened
          (arrayptr al vl `star` arrayptr ar vr)
          (fun res -> arrayptr al res)
          (adjacent (array_of vl) (array_of vr))
          (fun res ->
            merge_into (array_of vl) (array_of vr) (array_of res) /\
            contents_of res == contents_of vl `Seq.append` contents_of vr
          )
= SC.coerce_ghost (join' al ar)

let seq_slice
  (#a:Type) (s:Seq.seq a) (i: nat) (j: nat) : Pure (Seq.seq a)
  (requires (i <= j /\ j <= Seq.length s))
  (ensures (fun _ -> True))
= Seq.slice s i j

let split' (#opened: _) (#base #a:Type) (#value: v base a) (x: t base a) (i:SZ.size_t)
  (_: unit)
  : SEA.SteelAtomicBase (t base a) false opened Unobservable
          (arrayptr x value)
          (fun res -> exists_ (fun vl -> exists_ (fun vr ->
            arrayptr x vl `star` arrayptr res vr `star` pure (
            SZ.size_v i <= length (array_of value) /\
            merge_into (array_of vl) (array_of vr) (array_of value) /\
            contents_of' vl == seq_slice (contents_of' value) 0 (SZ.size_v i) /\
            length (array_of vl) == SZ.size_v i /\
            length (array_of vr) == length (array_of value) - SZ.size_v i /\
            contents_of' vr == seq_slice (contents_of' value) (SZ.size_v i) (length (array_of value)) /\
            contents_of' value == contents_of' vl `Seq.append` contents_of' vr
          ))))
          (fun _ -> SZ.size_v i <= length (array_of value))
          (fun _ _ _ -> True)
=
  elim_arrayptr' x;
  let res = S.split x i in
  let _ = intro_arrayptr' x in
  let _ = intro_arrayptr' res in
  noop ();
  SEA.return res

let split (#opened: _) (#base #a:Type) (#value: v base a) (x: t base a) (i:SZ.size_t)
  : STAtomicBase (t base a) false opened Unobservable
          (arrayptr x value)
          (fun res -> exists_ (fun vl -> exists_ (fun vr ->
            arrayptr x vl `star` arrayptr res vr `star` pure (
            SZ.size_v i <= length (array_of value) /\
            merge_into (array_of vl) (array_of vr) (array_of value) /\
            contents_of' vl == seq_slice (contents_of' value) 0 (SZ.size_v i) /\
            length (array_of vl) == SZ.size_v i /\
            length (array_of vr) == length (array_of value) - SZ.size_v i /\
            contents_of' vr == seq_slice (contents_of' value) (SZ.size_v i) (length (array_of value)) /\
            contents_of' value == contents_of' vl `Seq.append` contents_of' vr
          ))))
          (SZ.size_v i <= length (array_of value))
          (fun _ -> True)
= SC.coerce_atomic (split' x i)

let index' (#base: Type) (#a:Type) (#value: v base a) (r: t base a) (i: SZ.size_t)
  (_: unit)
  : Steel.Effect.Steel a
             (arrayptr r value)
             (fun y -> arrayptr r value)
             (fun _ -> SZ.size_v i < length (array_of value))
             (fun _ y _ ->
               SZ.size_v i < length (array_of value) /\
               y == Seq.index (contents_of' value) (SZ.size_v i)
             )
= elim_arrayptr' r;
  let res = S.index r i in
  let _ = intro_arrayptr' r in
  noop ();
  SEA.return res

let index (#base: Type) (#a:Type) (#value: v base a) (r: t base a) (i: SZ.size_t)
  : ST a
             (arrayptr r value)
             (fun y -> arrayptr r value)
             (SZ.size_v i < length (array_of value))
             (fun y ->
               SZ.size_v i < length (array_of value) /\
               y == Seq.index (contents_of' value) (SZ.size_v i)
             )
= SC.coerce_steel (index' r i)

let upd' (#base: Type) (#a:Type) (#value: v base a) (r: t base a) (i:SZ.size_t) (x:a)
  (_: unit)
  : Steel.Effect.Steel (v base a)
             (arrayptr r value)
             (fun value' -> arrayptr r value')
             (fun _ -> SZ.size_v i < length (array_of value))
             (fun _ value' _ ->
               SZ.size_v i < length (array_of value) /\
               array_of value' == array_of value /\
               contents_of' value' == Seq.upd (contents_of' value) (SZ.size_v i) x
             )
= elim_arrayptr' r;
  S.upd r i x;
  let res = intro_arrayptr' r in
  noop ();
  res

let upd (#base: Type) (#a:Type) (#value: v base a) (r: t base a) (i:SZ.size_t) (x:a)
  : ST (v base a)
             (arrayptr r value)
             (fun value' -> arrayptr r value')
             (SZ.size_v i < length (array_of value))
             (fun value'->
               SZ.size_v i < length (array_of value) /\
               array_of value' == array_of value /\
               contents_of' value' == Seq.upd (contents_of' value) (SZ.size_v i) x
             )
= SC.coerce_steel (upd' r i x)

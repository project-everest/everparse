module LowParse.SteelST.ArrayPtr

open Steel.Memory
open Steel.FractionalPermission
module SZ = LowParse.Steel.StdInt
open Steel.ST.Util

val t (base: Type0) (t:Type u#0) : Type u#0
val null (base: Type) (a: Type) : Tot (t base a)
val g_is_null (#base #a: Type) (x: t base a) : Ghost bool
  (requires True)
  (ensures (fun y -> y == true <==> x == null base a))

[@@erasable]
val array
  (base: Type0)
  (t: Type0)
: Tot Type0

val len
  (#base #t: Type0)
  (x: array base t)
: GTot SZ.size_t

let length
  (#base #t: Type0)
  (x: array base t)
: GTot nat
= SZ.size_v (len x)

[@@erasable]
val v (base: Type0) (t: Type u#0) : Tot Type0

val array_of (#base: _) (#a: _) (v: v base a) : Tot (array base a)
val contents_of (#base: _) (#a: _) (v: v base a) : GTot (Seq.lseq a (length (array_of v)))
let contents_of' #base #a (v: v base a) : GTot (Seq.seq a) =
  contents_of v

val array_contents_inj
  (#base: _) (#a: _)
  (v1 v2: v base a)
: Lemma
  (requires (
    array_of v1 == array_of v2 /\
    contents_of v1 == contents_of v2
  ))
  (ensures (v1 == v2))
  [SMTPatOr [
    [SMTPat (array_of v1); SMTPat (array_of v2)];
    [SMTPat (contents_of v1); SMTPat (contents_of v2)];
  ]]

val arrayptr
  (#base #a: Type0)
  (r: t base a)
  ([@@@smt_fallback] value: v base a)
: Tot vprop

val arrayptr_not_null
  (#opened: _)
  (#base #a: Type)
  (#value: v base a)
  (x: t base a)
: STGhostT (squash (g_is_null x == false)) opened
    (x `arrayptr` value)
    (fun _ -> x `arrayptr` value)

val arrayptr_or_null
  (#base #a: Type0)
  (r: t base a)
  ([@@@smt_fallback] value: Ghost.erased (option (v base a)))
: Tot vprop

val intro_arrayptr_or_null_none
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
  (sq: squash (g_is_null x == true))
: STGhostT unit opened
    emp
    (fun _ -> arrayptr_or_null x None)

val intro_arrayptr_or_null_some
  (#opened: _)
  (#base #a: Type)
  (#value: v base a)
  (x: t base a)
: STGhostT unit opened
    (arrayptr x value)
    (fun _ -> arrayptr_or_null x (Some value))

let extract_some
  (#a: Type)
  (v: option a)
  (sq: squash (Some? v))
: Tot a
= Some?.v v

val elim_arrayptr_or_null_some
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
: STGhost (v base a) opened
    (arrayptr_or_null x value)
    (fun value' -> arrayptr x value')
    (g_is_null x == false \/ Some? value)
    (fun value' -> Ghost.reveal value == Some value')

val elim_arrayptr_or_null_none
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
: STGhost unit opened
    (arrayptr_or_null x value)
    (fun _ -> emp)
    (g_is_null x == true \/ None? value)
    (fun _ -> g_is_null x == true /\ Ghost.reveal value == None)

val is_null
  (#opened: _)
  (#base #a: Type)
  (#value: Ghost.erased (option (v base a)))
  (x: t base a)
: STAtomicBase bool false opened Unobservable
    (arrayptr_or_null x value)
    (fun res -> arrayptr_or_null x value)
    (True)
    (fun res -> res == None? value /\ res == g_is_null x)

val adjacent
  (#base #t: Type0)
  (x1 x2: array base t)
: Tot prop

val merge
  (#base #t: Type0)
  (x1 x2: array base t)
: Ghost (array base t)
  (requires (adjacent x1 x2))
  (ensures (fun y -> length y == length x1 + length x2))

let merge_into
  (#base #t: Type0)
  (x1 x2 y: array base t)
: Tot prop
= adjacent x1 x2 /\
  merge x1 x2 == y

val join (#opened: _) (#base #a:Type) (#vl #vr: v base a) (al ar:t base a)
  : STGhost (v base a) opened
          (arrayptr al vl `star` arrayptr ar vr)
          (fun res -> arrayptr al res)
          (adjacent (array_of vl) (array_of vr))
          (fun res ->
            merge_into (array_of vl) (array_of vr) (array_of res) /\
            contents_of res == contents_of vl `Seq.append` contents_of vr
          )

let seq_slice
  (#a:Type) (s:Seq.seq a) (i: nat) (j: nat) : Pure (Seq.seq a)
  (requires (i <= j /\ j <= Seq.length s))
  (ensures (fun _ -> True))
= Seq.slice s i j

val gsplit (#opened: _) (#base #a:Type) (#value: v base a) (x: t base a) (i:SZ.size_t)
  : STGhost (Ghost.erased (t base a)) opened
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

val split' (#opened: _) (#base #a:Type) (#vl #vr: v base a) (x: t base a) (i: SZ.size_t) (x': Ghost.erased (t base a))
  : STAtomicBase (t base a) false opened Unobservable
          (arrayptr x vl `star` arrayptr x' vr)
          (fun res -> arrayptr x vl `star` arrayptr res vr)
          (adjacent (array_of vl) (array_of vr) /\ SZ.size_v i == length (array_of vl))
          (fun res -> res == Ghost.reveal x')

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
= let gres = gsplit x i in
  let _ = gen_elim () in
  let res = split' x i gres in
  res

val index (#base: Type) (#a:Type) (#value: v base a) (r: t base a) (i: SZ.size_t)
  : ST a
             (arrayptr r value)
             (fun y -> arrayptr r value)
             (SZ.size_v i < length (array_of value))
             (fun y ->
               SZ.size_v i < length (array_of value) /\
               y == Seq.index (contents_of' value) (SZ.size_v i)
             )

val upd (#base: Type) (#a:Type) (#value: v base a) (r: t base a) (i:SZ.size_t) (x:a)
  : ST (v base a)
             (arrayptr r value)
             (fun value' -> arrayptr r value')
             (SZ.size_v i < length (array_of value))
             (fun value'->
               SZ.size_v i < length (array_of value) /\
               array_of value' == array_of value /\
               contents_of' value' == Seq.upd (contents_of' value) (SZ.size_v i) x
             )

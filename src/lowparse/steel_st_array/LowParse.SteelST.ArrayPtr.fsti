module LowParse.SteelST.ArrayPtr

open Steel.Memory
open Steel.FractionalPermission
module SZ = LowParse.Steel.StdInt
open Steel.ST.Util

val t (t:Type u#0) : Type u#0

[@@erasable]
val array
  (t: Type0)
: Tot Type0

val len
  (#t: Type0)
  (x: array t)
: GTot SZ.size_t

let length
  (#t: Type0)
  (x: array t)
: GTot nat
= SZ.size_v (len x)

[@@erasable]
val v (t: Type u#0) : Tot Type0

val array_of (#a: _) (v: v a) : Tot (array a)
val contents_of (#a: _) (v: v a) : GTot (Seq.lseq a (length (array_of v)))
let contents_of' #a (v: v a) : GTot (Seq.seq a) =
  contents_of v

val array_contents_inj
  (#a: _)
  (v1 v2: v a)
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
  (#a: Type0)
  (r: t a)
  ([@@@smt_fallback] value: v a)
: Tot vprop

val adjacent
  (#t: Type0)
  (x1 x2: array t)
: Tot prop

val merge
  (#t: Type0)
  (x1 x2: array t)
: Ghost (array t)
  (requires (adjacent x1 x2))
  (ensures (fun y -> length y == length x1 + length x2))

let merge_into
  (#t: Type0)
  (x1 x2 y: array t)
: Tot prop
= adjacent x1 x2 /\
  merge x1 x2 == y

val join (#opened: _) (#a:Type) (#vl #vr: v a) (al ar:t a)
  : STGhost (v a) opened
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

val gsplit (#opened: _) (#a:Type) (#value: v a) (x: t a) (i:SZ.size_t)
  : STGhost (Ghost.erased (t a)) opened
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

val split' (#opened: _) (#a:Type) (#vl #vr: v a) (x: t a) (i: SZ.size_t) (x': Ghost.erased (t a))
  : STAtomicBase (t a) false opened Unobservable
          (arrayptr x vl `star` arrayptr x' vr)
          (fun res -> arrayptr x vl `star` arrayptr res vr)
          (adjacent (array_of vl) (array_of vr) /\ SZ.size_v i == length (array_of vl))
          (fun res -> res == Ghost.reveal x')

let split (#opened: _) (#a:Type) (#value: v a) (x: t a) (i:SZ.size_t)
  : STAtomicBase (t a) false opened Unobservable
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

val index (#a:Type) (#value: v a) (r: t a) (i: SZ.size_t)
  : ST a
             (arrayptr r value)
             (fun y -> arrayptr r value)
             (SZ.size_v i < length (array_of value))
             (fun y ->
               SZ.size_v i < length (array_of value) /\
               y == Seq.index (contents_of' value) (SZ.size_v i)
             )

val upd (#a:Type) (#value: v a) (r: t a) (i:SZ.size_t) (x:a)
  : ST (v a)
             (arrayptr r value)
             (fun value' -> arrayptr r value')
             (SZ.size_v i < length (array_of value))
             (fun value'->
               SZ.size_v i < length (array_of value) /\
               array_of value' == array_of value /\
               contents_of' value' == Seq.upd (contents_of' value) (SZ.size_v i) x
             )

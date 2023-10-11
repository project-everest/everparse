module LowParse.SteelST.ArrayPtr

open Steel.Memory
open Steel.FractionalPermission
module SZ = FStar.SizeT
open Steel.ST.GenElim

inline_for_extraction
val t (t:Type u#0) : Type u#0

[@@erasable]
val array
  (t: Type0)
: Tot Type0

val len
  (#t: Type0)
  (x: array t)
: GTot SZ.t

let length
  (#t: Type0)
  (x: array t)
: GTot nat
= SZ.v (len x)

val array_perm
  (#t: Type)
  (x: array t)
: GTot perm

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
  (ensures (fun y -> length y == length x1 + length x2 /\ array_perm y == array_perm x1 /\ array_perm y == array_perm x2))

let adjacent_sizes_fit
  (#t: Type0)
  (x1 x2: array t)
: Lemma
  (requires (adjacent x1 x2))
  (ensures (SZ.fits (length x1 + length x2)))
  [SMTPat (adjacent x1 x2)]
= let _ = merge x1 x2 in
  ()

let merge_into
  (#t: Type0)
  (x1 x2 y: array t)
: Tot prop
= adjacent x1 x2 /\
  merge x1 x2 == y

val merge_assoc
  (#t: Type0)
  (x1 x2 x3: array t)
: Lemma
  (requires (
    (adjacent x1 x2 /\ adjacent x2 x3) \/
    (adjacent x1 x2 /\ adjacent (merge x1 x2) x3) \/
    (adjacent x2 x3 /\ adjacent x1 (merge x2 x3))
  ))
  (ensures (
    adjacent x1 x2 /\ adjacent (merge x1 x2) x3 /\
    adjacent x2 x3 /\ adjacent x1 (merge x2 x3) /\
    merge (merge x1 x2) x3 == merge x1 (merge x2 x3)
  ))
  [SMTPatOr [
    [SMTPat (adjacent x1 x2); SMTPat (adjacent x2 x3)];
    [SMTPat (adjacent (merge x1 x2) x3)];
    [SMTPat (adjacent x1 (merge x2 x3))];
  ]]

val join (#opened: _) (#a:Type) (#vl #vr: v a) (al ar:t a)
  : STGhost (v a) opened
          (arrayptr al vl `star` arrayptr ar vr)
          (fun res -> arrayptr al res)
          (adjacent (array_of vl) (array_of vr))
          (fun res ->
            merge_into (array_of vl) (array_of vr) (array_of res) /\
            contents_of res == contents_of vl `Seq.append` contents_of vr
          )

[@@noextract_to "krml"]
let seq_slice
  (#a:Type) (s:Seq.seq a) (i: nat) (j: nat) : Pure (Seq.seq a)
  (requires (i <= j /\ j <= Seq.length s))
  (ensures (fun _ -> True))
= Seq.slice s i j

val gsplit (#opened: _) (#a:Type) (#value: v a) (x: t a) (i:SZ.t)
  : STGhost (Ghost.erased (t a)) opened
          (arrayptr x value)
          (fun res -> exists_ (fun vl -> exists_ (fun vr ->
            arrayptr x vl `star` arrayptr res vr `star` pure (
            SZ.v i <= length (array_of value) /\
            merge_into (array_of vl) (array_of vr) (array_of value) /\
            contents_of' vl == seq_slice (contents_of' value) 0 (SZ.v i) /\
            length (array_of vl) == SZ.v i /\
            length (array_of vr) == length (array_of value) - SZ.v i /\
            contents_of' vr == seq_slice (contents_of' value) (SZ.v i) (length (array_of value)) /\
            contents_of' value == contents_of' vl `Seq.append` contents_of' vr /\
            (SZ.v i == 0 ==> Ghost.reveal res == x)
          ))))
          (SZ.v i <= length (array_of value))
          (fun _ -> True)

inline_for_extraction
val split' (#a:Type) (#vl #vr: v a) (x: t a) (i: SZ.t) (x': Ghost.erased (t a))
  : ST (t a)
          (arrayptr x vl `star` arrayptr x' vr)
          (fun res -> arrayptr x vl `star` arrayptr res vr)
          (adjacent (array_of vl) (array_of vr) /\ SZ.v i == length (array_of vl))
          (fun res -> res == Ghost.reveal x')

inline_for_extraction
let split (#a:Type) (#value: v a) (x: t a) (i:SZ.t)
  : ST (t a)
          (arrayptr x value)
          (fun res -> exists_ (fun vl -> exists_ (fun vr ->
            arrayptr x vl `star` arrayptr res vr `star` pure (
            SZ.v i <= length (array_of value) /\
            merge_into (array_of vl) (array_of vr) (array_of value) /\
            contents_of' vl == seq_slice (contents_of' value) 0 (SZ.v i) /\
            length (array_of vl) == SZ.v i /\
            length (array_of vr) == length (array_of value) - SZ.v i /\
            contents_of' vr == seq_slice (contents_of' value) (SZ.v i) (length (array_of value)) /\
            contents_of' value == contents_of' vl `Seq.append` contents_of' vr /\
            (SZ.v i == 0 ==> res == x)
          ))))
          (SZ.v i <= length (array_of value))
          (fun _ -> True)
= let gres = gsplit x i in
  let _ = gen_elim () in
  let res = split' x i gres in
  res

inline_for_extraction
val index (#a:Type) (#value: v a) (r: t a) (i: SZ.t)
  : ST a
             (arrayptr r value)
             (fun y -> arrayptr r value)
             (SZ.v i < length (array_of value))
             (fun y ->
               SZ.v i < length (array_of value) /\
               y == Seq.index (contents_of' value) (SZ.v i)
             )

inline_for_extraction
val upd (#a:Type) (#value: v a) (r: t a) (i:SZ.t) (x:a)
  : ST (v a)
             (arrayptr r value)
             (fun value' -> arrayptr r value')
             (SZ.v i < length (array_of value) /\ array_perm (array_of value) == full_perm)
             (fun value'->
               SZ.v i < length (array_of value) /\
               array_of value' == array_of value /\
               contents_of' value' == Seq.upd (contents_of' value) (SZ.v i) x
             )

val set_array_perm
  (#t: Type)
  (a: array t)
  (p: perm)
: Ghost (array t)
    (requires True)
    (ensures (fun y -> len y == len a /\ array_perm y == p))

val set_array_perm_idem
  (#t: Type)
  (a: array t)
  (p1 p2: perm)
: Lemma
  (set_array_perm (set_array_perm a p1) p2 == set_array_perm a p2)
  [SMTPat (set_array_perm (set_array_perm a p1) p2)]

val set_array_perm_eq
  (#t: Type)
  (a: array t)
: Lemma
  (set_array_perm a (array_perm a) == a)
  [SMTPat (set_array_perm a (array_perm a))]

val set_array_perm_adjacent
  (#t: Type)
  (a1 a2: array t)
  (p: perm)
: Lemma
  (requires (adjacent a1 a2))
  (ensures (
    merge_into (set_array_perm a1 p) (set_array_perm a2 p) (set_array_perm (merge a1 a2) p)
  ))
  [SMTPat (adjacent (set_array_perm a1 p) (set_array_perm a2 p))]

inline_for_extraction
val copy
  (#elt: Type)
  (#vin #vout: v elt)
  (ain aout: t elt)
  (len: SZ.t)
: ST (v elt)
    (arrayptr ain vin `star` arrayptr aout vout)
    (fun vout' -> arrayptr ain vin `star` arrayptr aout vout')
    (SZ.v len == length (array_of vin) /\
      SZ.v len == length (array_of vout) /\
      array_perm (array_of vout) == full_perm
    )
    (fun vout' ->
      array_of vout' == array_of vout /\
      contents_of' vout' == contents_of' vin
    )

val share
  (#opened: _)
  (#elt: Type)
  (#x: v elt)
  (a: t elt)
  (p1 p2: perm)
: STGhost (Ghost.erased (v elt & v elt)) opened
    (arrayptr a x)
    (fun res -> arrayptr a (fst res) `star` arrayptr a (snd res))
    (array_perm (array_of x) == p1 `Steel.FractionalPermission.sum_perm` p2)
    (fun res ->
      contents_of' (fst res) == contents_of x /\
      contents_of' (snd res) == contents_of x /\
      array_of (fst res) == set_array_perm (array_of x) p1 /\
      array_of (snd res) == set_array_perm (array_of x) p2
    )

val gather
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: v elt)
  (a: t elt)
: STGhost (v elt) opened
    (arrayptr a x1 `star` arrayptr a x2)
    (fun res -> arrayptr a res)
    (array_of x1 == set_array_perm (array_of x2) (array_perm (array_of x1)))
    (fun res ->
      contents_of' res == contents_of x1 /\
      contents_of' res == contents_of x2 /\
      array_of res == set_array_perm (array_of x1) (array_perm (array_of x1) `Steel.FractionalPermission.sum_perm` array_perm (array_of x2))
    )

(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(* A partial model for C array pointers. Given a type t, we model type
   t* with the following operations:

   * null

   * alloc, free

   * read at some offset p[i]
   
   * additive pointer arithmetic: if p is an array pointer, then the
     user has permission to access n cells to its right-hand-side (no
     subtractions.) So if i <= n, then operation q = p+i splits the
     permission into two parts, p for cells from 0 to i-1, and q for
     cells from i to n-1. User needs to explicitly return the
     permission by "merging" back q into p.
*)

module LowParse.Steel.ArrayPtr
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Effect.Atomic
module SZ = Steel.C.StdInt.Base

inline_for_extraction
val t (base: Type0) (t:Type u#0) : Type u#0

inline_for_extraction
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
noeq type v (base: Type0) (t: Type u#0) = {
  array: array base t; (* spatial permission range *)
  contents: Seq.lseq t (length array); (* actual contents *)
//  perm: perm;                            (* temporal permission *)
}

val is_arrayptr (#base #a:Type0) (r:t base a) : slprop u#1
val arrayptr_sel (#base #a:Type0) (r:t base a) : selector (v base a) (is_arrayptr r)

[@@ __steel_reduce__]
let varrayptr' #base #a r : vprop' =
  {hp = is_arrayptr r;
   t = v base a;
   sel = arrayptr_sel r}

[@@ __steel_reduce__]
let varrayptr r = VUnit (varrayptr' r)

[@@ __steel_reduce__]
let sel (#base #a:Type) (#p:vprop) (r:t base a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (varrayptr r) /\ True)})
: GTot (v base a)
  = h (varrayptr r)

val varrayptr_not_null
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelGhost unit opened
    (varrayptr x)
    (fun _ -> varrayptr x)
    (fun _ -> True)
    (fun h _ h' ->
      h' (varrayptr x) == h (varrayptr x) /\
      g_is_null x == false
    )


val is_arrayptr_or_null (#base #a:Type0) (r:t base a) : slprop u#1
val arrayptr_or_null_sel (#base #a:Type0) (r:t base a) : GTot (selector (option (v base a)) (is_arrayptr_or_null r))

[@@ __steel_reduce__]
let varrayptr_or_null' #base #a r : GTot vprop' =
  {hp = is_arrayptr_or_null r;
   t = option (v base a);
   sel = arrayptr_or_null_sel r}

[@@ __steel_reduce__]
let varrayptr_or_null r = VUnit (varrayptr_or_null' r)

val intro_varrayptr_or_null_none
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelGhost unit opened
    emp
    (fun _ -> varrayptr_or_null x)
    (fun _ -> g_is_null x == true)
    (fun _ _ h' -> h' (varrayptr_or_null x) == None)

val intro_varrayptr_or_null_some
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelGhost unit opened
    (varrayptr x)
    (fun _ -> varrayptr_or_null x)
    (fun _ -> True)
    (fun h _ h' ->
      g_is_null x == false /\
      h' (varrayptr_or_null x) == Some (h (varrayptr x)
    ))

val elim_varrayptr_or_null_some
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelGhost unit opened
    (varrayptr_or_null x)
    (fun _ -> varrayptr x)
    (fun h -> g_is_null x == false \/ Some? (h (varrayptr_or_null x)))
    (fun h _ h' ->
      g_is_null x == false /\
      h (varrayptr_or_null x) == Some (h' (varrayptr x))
    )

val elim_varrayptr_or_null_none
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelGhost unit opened
    (varrayptr_or_null x)
    (fun _ -> emp)
    (fun h -> g_is_null x == true \/ None? (h (varrayptr_or_null x)))
    (fun h _ _ ->
      g_is_null x == true /\
      h (varrayptr_or_null x) == None
    )

inline_for_extraction
val is_null
  (#opened: _)
  (#base #a: Type)
  (x: t base a)
: SteelAtomicBase bool false opened Unobservable
    (varrayptr_or_null x)
    (fun _ -> varrayptr_or_null x)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (varrayptr_or_null x) in
      h' (varrayptr_or_null x) == s /\
      res == None? s /\
      res == g_is_null x
    )

(* Splitting an array (inspired from Steel.Array) *)

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

val join (#opened: _) (#base #a:Type) (al ar:t base a)
  : SteelGhost unit opened
          (varrayptr al `star` varrayptr ar)
          (fun _ -> varrayptr al)
          (fun h ->
            adjacent (h (varrayptr al)).array (h (varrayptr ar)).array /\
True //            (h (varrayptr al)).perm == (h (varrayptr ar)).perm
          )
          (fun h _ h' ->
            let cl = h (varrayptr al) in
            let cr = h (varrayptr ar) in
            let c' = h' (varrayptr al) in
            merge_into cl.array cr.array c'.array /\
//            c'.perm == cl.perm /\
            c'.contents == cl.contents `Seq.append` cr.contents
          )

inline_for_extraction
val split (#opened: _) (#base #a:Type) (x: t base a) (i:SZ.size_t)
  : SteelAtomicBase (t base a) false opened Unobservable
          (varrayptr x)
          (fun res -> varrayptr x `star` varrayptr res)
          (fun h -> SZ.size_v i <= length (h (varrayptr x)).array)
          (fun h res h' ->
            let s = h (varrayptr x) in
            let sl = h' (varrayptr x) in
            let sr = h' (varrayptr res) in
            SZ.size_v i <= length s.array /\
            merge_into sl.array sr.array s.array /\
//            sl.perm == s.perm /\
//            sr.perm == s.perm /\
            sl.contents == Seq.slice s.contents 0 (SZ.size_v i) /\
            length sl.array == SZ.size_v i /\
            length sr.array == length s.array - SZ.size_v i /\
            sr.contents == Seq.slice s.contents (SZ.size_v i) (length s.array) /\
            s.contents == sl.contents `Seq.append` sr.contents
          )

inline_for_extraction
val base_t (a: Type0) (n: SZ.size_t) : Tot Type0

val freeable
  (#base #t: Type0)
  (x: array base t)
: Tot prop

inline_for_extraction
val alloc (#a:Type) (x:a) (n:SZ.size_t)
  : Steel (t (base_t a n) a)
             emp
             (fun r -> varrayptr_or_null r)
             (requires fun _ -> SZ.size_v n > 0)
             (ensures fun _ r h1 ->
               match g_is_null r, h1 (varrayptr_or_null r) with
               | true, None -> True
               | false, Some s ->
                 length s.array == SZ.size_v n /\
                 s.contents == Seq.create (SZ.size_v n) x /\
//                 s.perm == full_perm /\
                 freeable s.array
               | _ -> False
             )

inline_for_extraction
val index (#base: Type) (#a:Type) (r: t base a) (i: SZ.size_t)
  : Steel a
             (varrayptr r)
             (fun _ -> varrayptr r)
             (requires fun h -> SZ.size_v i < length (h (varrayptr r)).array)
             (ensures fun h0 y h1 ->
               let s = h0 (varrayptr r) in
               h1 (varrayptr r) == s /\
               SZ.size_v i < length s.array /\
               y == Seq.index s.contents (SZ.size_v i))

inline_for_extraction
val upd (#base: Type) (#a:Type) (r: t base a) (i:SZ.size_t) (x:a)
  : Steel unit
             (varrayptr r)
             (fun _ -> varrayptr r)
             (requires fun h ->
//               (h (varrayptr r)).perm == full_perm /\
               SZ.size_v i < length (h (varrayptr r)).array
             )
             (ensures fun h0 _ h1 ->
               let s = h0 (varrayptr r) in
               let s' = h1 (varrayptr r) in
               s'.array == s.array /\
//               s'.perm == full_perm /\
               SZ.size_v i < length s.array /\
               s'.contents == Seq.upd s.contents (SZ.size_v i) x)

inline_for_extraction
val free (#base: Type) (#a:Type) (r:t base a)
  : Steel unit
             (varrayptr r)
             (fun _ -> emp)
             (requires fun h ->
//               (h (varrayptr r)).perm == full_perm /\
               freeable (h (varrayptr r)).array
             )
             (ensures fun _ _ _ -> True)

(*
val share (#opened: _) (#base: Type) (#a: Type) (r: t base a)
  : SteelAtomicBase (t base a) false opened Unobservable
    (varrayptr r)
    (fun res -> varrayptr r `star` varrayptr res)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (varrayptr r) in
      let d = h' (varrayptr res) in
      let s' = h' (varrayptr r) in
      s'.perm == half_perm s.perm /\
      s'.array == s.array /\
      s'.contents == s.contents /\
      d.array == s.array /\
      d.perm == half_perm s.perm /\
      d.contents == s.contents
    )

val gather
  (#opened: _)
  (#a: Type)
  (r1 r2: t a)
: SteelGhost unit opened
    (varrayptr r1 `star` varrayptr r2)
    (fun _ -> varrayptr r1)
    (fun h ->
      (h (varrayptr r1)).array == (h (varrayptr r2)).array
    )
    (fun h res h' ->
      let s1 = h (varrayptr r1) in
      let s2 = h (varrayptr r2) in
      let s' = h' (varrayptr r1) in
      s'.array == s1.array /\
      s'.array == s2.array /\
      s'.contents == s1.contents /\
      s'.contents == s2.contents /\
      s'.perm == s1.perm `sum_perm` s2.perm
    )
*)

(* Entering and exiting the abstraction *)
module A = Steel.C.Array

val array_of
  (#base #t: Type0)
  (x: array base t)
: Ghost (A.array base t)
  (requires True)
  (ensures (fun y -> A.length y == length x))

inline_for_extraction
val enter
  (#opened: _)
  (#base: Type)
  (#a: Type)
  (x: A.array base a)
//  (p: perm)
: SteelAtomicBase (t base a) false opened Unobservable
    (A.varray x) // (A.varrayp x p)
    (fun res -> varrayptr res)
    (fun _ ->
      True
//      let p = A.g_get_pointer x in
//      (P.g_is_null p == false ==> P.size_v (P.base_array_len (P.base p)) < 4294967296) // TODO: remove and use size_t instead
    )
    (fun h res h' ->
      let s = h' (varrayptr res) in
      array_of s.array == x /\
//      s.perm == p /\
      s.contents == h (A.varray x) // (A.varrayp x p)
    )

inline_for_extraction
val exit
  (#opened: _)
  (#base: Type)
  (#a: Type)
  (x: t base a)
: SteelAtomicBase (A.array base a) (* & perm *) false opened Unobservable
    (varrayptr x)
    (fun res -> A.varray res) // A.varrayp (fst res) (snd res))
    (fun _ -> True)
    (fun h res h' ->
      let s = h (varrayptr x) in
      res == array_of s.array /\
      h' (A.varray res) == s.contents
//      fst res == s.array /\
//      snd res == s.perm /\
//      h' (A.varrayp (fst res) (snd res)) == s.contents
    )

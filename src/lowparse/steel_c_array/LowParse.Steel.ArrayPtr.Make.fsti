module LowParse.Steel.ArrayPtr.Make
include LowParse.Steel.ArrayPtr

open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Effect.Atomic
module SZ = LowParse.Steel.StdInt

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

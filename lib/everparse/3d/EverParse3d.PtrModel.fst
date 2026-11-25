module EverParse3d.PtrModel

(* A ghost model of the byte pointers returned by the `field_ptr` action.

   `Pulse.Lib.ArrayPtr.ptr` is abstract: its only observations are `base` and
   `offset`, and nothing says that they determine the pointer. The pointer
   returned by `field_ptr` is obtained by `AP.split`, whose post-condition
   only gives its `base` and `offset`. So to give `field_ptr` a deterministic
   spec, we assume pointer extensionality (`ptr_ext`), which holds of C
   pointers. This is the only trusted assumption of this module. *)

module AP = Pulse.Lib.ArrayPtr
module U8 = FStar.UInt8

let ptr : Type0 = AP.ptr U8.t

(* Trusted: a pointer is determined by its base and offset. *)
assume val ptr_ext (p q: ptr) : Lemma
  (requires (AP.base p == AP.base q /\ AP.offset p == AP.offset q))
  (ensures (p == q))

let ptr_at_prop (o: ptr) (n: nat) (p: ptr) : prop =
  AP.adjacent o n p

(* The pointer `n` bytes after `o`, if any. *)
let ptr_at (o: ptr) (n: nat) : GTot ptr =
  if FStar.IndefiniteDescription.strong_excluded_middle (exists (p: ptr) . ptr_at_prop o n p)
  then FStar.IndefiniteDescription.indefinite_description_ghost ptr (fun p -> ptr_at_prop o n p)
  else o

let ptr_at_adjacent (o: ptr) (n: nat) (p: ptr) : Lemma
  (requires (AP.adjacent o n p))
  (ensures (ptr_at o n == p))
= assert (ptr_at_prop o n p);
  ptr_ext (ptr_at o n) p

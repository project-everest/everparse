module CBOR.Pulse.API.Nondet.C.Alloc
open Pulse.Lib.Pervasives
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module U64 = FStar.UInt64

(* TRUSTED: fallible heap allocation of scratch spaces for the C
   extraction, assumed here and implemented by hand in
   include/everparse/CBORNondetAlloc.h (with malloc and free.)

   cbor_nondet_malloc_X n either returns NULL, or a pointer to n
   (uninitialized) elements, which must be freed exactly once with
   cbor_nondet_free_X. The element count is a U64.t rather than a
   SZ.t, so that callers can compute it without overflow before
   knowing whether it fits size_t; success implies that it does. *)

let cbor_nondet_malloc_post
  (#t: Type0)
  (freeable: AP.ptr t -> slprop)
  (n: U64.t)
  (p: AP.ptr t)
: Tot slprop
= exists* (v: Seq.seq t) .
    AP.pts_to_or_null p v **
    freeable p **
    pure (not (AP.g_is_null p) ==> (SZ.fits (U64.v n) /\ Seq.length v == U64.v n))

val cbor_nondet_freeable_size_t ([@@@mkey] p: AP.ptr SZ.t) : slprop

val cbor_nondet_malloc_size_t (n: U64.t) : stt (AP.ptr SZ.t)
  emp
  (fun p -> cbor_nondet_malloc_post cbor_nondet_freeable_size_t n p)

val cbor_nondet_free_size_t (p: AP.ptr SZ.t) (#v: Ghost.erased (Seq.seq SZ.t)) : stt unit
  (AP.pts_to p v ** cbor_nondet_freeable_size_t p)
  (fun _ -> emp)

val cbor_nondet_freeable_uint64_t ([@@@mkey] p: AP.ptr U64.t) : slprop

val cbor_nondet_malloc_uint64_t (n: U64.t) : stt (AP.ptr U64.t)
  emp
  (fun p -> cbor_nondet_malloc_post cbor_nondet_freeable_uint64_t n p)

val cbor_nondet_free_uint64_t (p: AP.ptr U64.t) (#v: Ghost.erased (Seq.seq U64.t)) : stt unit
  (AP.pts_to p v ** cbor_nondet_freeable_uint64_t p)
  (fun _ -> emp)

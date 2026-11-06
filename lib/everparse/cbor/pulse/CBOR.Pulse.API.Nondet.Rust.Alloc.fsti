module CBOR.Pulse.API.Nondet.Rust.Alloc
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U64 = FStar.UInt64

(* TRUSTED: fallible heap allocation of scratch spaces for the Rust
   extraction, assumed here and implemented by hand in
   src/cbor/pulse/nondet/rust/src/cbornondetallocimpl.rs (with
   Vec::try_reserve_exact, Box::leak and Box::from_raw.)

   cbor_nondet_alloc_X n either returns None, or a slice of exactly n
   elements, which must be freed exactly once, as is, with
   cbor_nondet_free_X. The element count is a U64.t rather than a
   SZ.t, so that callers can compute it without overflow before
   knowing whether it fits usize. *)

let cbor_nondet_alloc_post
  (#t: Type0)
  (freeable: S.slice t -> slprop)
  (n: U64.t)
  (r: option (S.slice t))
: Tot slprop
= match r with
  | None -> emp
  | Some s -> exists* (v: Seq.seq t) .
    pts_to s v **
    freeable s **
    pure (SZ.v (S.len s) == U64.v n)

val cbor_nondet_freeable_usize ([@@@mkey] s: S.slice SZ.t) : slprop

val cbor_nondet_alloc_usize (n: U64.t) : stt (option (S.slice SZ.t))
  emp
  (fun r -> cbor_nondet_alloc_post cbor_nondet_freeable_usize n r)

val cbor_nondet_free_usize (s: S.slice SZ.t) (#v: Ghost.erased (Seq.seq SZ.t)) : stt unit
  (pts_to s v ** cbor_nondet_freeable_usize s)
  (fun _ -> emp)

val cbor_nondet_freeable_u64 ([@@@mkey] s: S.slice U64.t) : slprop

val cbor_nondet_alloc_u64 (n: U64.t) : stt (option (S.slice U64.t))
  emp
  (fun r -> cbor_nondet_alloc_post cbor_nondet_freeable_u64 n r)

val cbor_nondet_free_u64 (s: S.slice U64.t) (#v: Ghost.erased (Seq.seq U64.t)) : stt unit
  (pts_to s v ** cbor_nondet_freeable_u64 s)
  (fun _ -> emp)

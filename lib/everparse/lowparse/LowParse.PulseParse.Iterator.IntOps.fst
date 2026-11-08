module LowParse.PulseParse.Iterator.IntOps

(* Integer-type dictionary to parameterize the lowparse mixed_list over its
   count/offset integer type: other libraries keep [SZ.t] (via [sizet_ops]);
   CBOR instantiates at [U64.t] (via [u64_ops]) to shed [FStar.SizeT.fits_u64].

   Pure F* (no Pulse); safe to [open] from a [#lang-pulse] module.

   NB (design, validated by spike): this dictionary is passed to
   [inline_for_extraction] FUNCTIONS applied to a CONCRETE instance; it must
   NOT index a mixed_list TYPE (KaRaMeL cannot parameterize a type by a value). *)

module SZ = FStar.SizeT
module U64 = FStar.UInt64

noeq
inline_for_extraction
type int_ops (i: Type0) = {
  // --- spec / ghost (erased) ---
  fits : (nat -> prop);
  v    : (x: i) -> GTot (n: nat { fits n });
  // --- constants ---
  zero : (z: i { v z == 0 });
  one  : (o: i { v o == 1 });
  // --- arithmetic (total, refined) ---
  add  : (x: i) -> (y: i { fits (v x + v y) }) -> (z: i { v z == v x + v y });
  sub  : (x: i) -> (y: i { v y <= v x })       -> (z: i { v z == v x - v y });
  // --- comparison (runtime, spec-reflecting) ---
  eq   : (x: i) -> (y: i) -> (b: bool { b <==> v x == v y });
  lt   : (x: i) -> (y: i) -> (b: bool { b <==> v x <  v y });
  lte  : (x: i) -> (y: i) -> (b: bool { b <==> v x <= v y });
  gt   : (x: i) -> (y: i) -> (b: bool { b <==> v x >  v y });
  gte  : (x: i) -> (y: i) -> (b: bool { b <==> v x >= v y });
  // --- size_t boundary (BOTH directions are axiom-free) ---
  //   to_sizet: i -> size_t, needs only the LOCAL [SZ.fits (v x)] (the real
  //     stage2 [uint64_to_sizet] requires [fits_u64 \/ fits (U64.v x)], so the
  //     local disjunct suffices; NO global [fits_u64]).  Discharged at slice
  //     indexing from the slice length.
  //   of_sizet: size_t -> i, needs only [fits (SZ.v s)] (for u64: < 2^64).
  to_sizet : (x: i { SZ.fits (v x) }) -> (s: SZ.t { SZ.v s == v x });
  of_sizet : (s: SZ.t { fits (SZ.v s) }) -> (x: i { v x == SZ.v s });
}

(* ---------------- instance: size_t (the default, identity) ---------------- *)

inline_for_extraction
let sizet_ops : int_ops SZ.t = {
  fits = (fun (n: nat) -> (SZ.fits n <: prop));
  v    = (fun x -> SZ.v x);
  zero = 0sz;
  one  = 1sz;
  add  = (fun x y -> SZ.add x y);
  sub  = (fun x y -> SZ.sub x y);
  eq   = (fun x y -> SZ.eq x y);
  lt   = (fun x y -> SZ.lt x y);
  lte  = (fun x y -> SZ.lte x y);
  gt   = (fun x y -> SZ.gt x y);
  gte  = (fun x y -> SZ.gte x y);
  to_sizet = (fun x -> x);
  of_sizet = (fun s -> s);
}

(* ---------------- instance: U64.t (the CBOR count type) ---------------- *)

inline_for_extraction
let u64_ops : int_ops U64.t = {
  fits = (fun (n: nat) -> (n < pow2 64 <: prop));
  v    = (fun x -> U64.v x);
  zero = 0uL;
  one  = 1uL;
  add  = (fun x y -> U64.add x y);
  sub  = (fun x y -> U64.sub x y);
  eq   = (fun x y -> x = y);
  lt   = (fun x y -> U64.lt x y);
  lte  = (fun x y -> U64.lte x y);
  gt   = (fun x y -> U64.gt x y);
  gte  = (fun x y -> U64.gte x y);
  to_sizet = (fun x -> SZ.uint64_to_sizet x);   // pre SZ.fits (U64.v x) => fits disjunct
  of_sizet = (fun s -> SZ.sizet_to_uint64 s);    // pre SZ.v s < 2^64
}

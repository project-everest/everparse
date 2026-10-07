open Fstarcompiler
open Prims
type u8 = FStar_UInt8.t
type u32 = FStar_UInt32.t
let le_to_n (s : u8 FStar_Seq_Base.seq) : Prims.nat=
  FStar_Endianness.le_to_n s
let frozen_until (s : u8 FStar_Seq_Base.seq) : Prims.nat=
  le_to_n (FStar_Seq_Base.slice s Prims.int_zero (Prims.of_int (4)))
type ('s1, 's2) pre = unit
type ('uuuuu, 'uuuuu1) prefix_freezable_preorder = unit
type ('n, 's) frozen_until_at_least = unit
type ('i, 'j, 'snap, 's) slice_is = unit
type buffer = (u8, unit, unit) LowStar_Monotonic_Buffer.mbuffer
type 'len lbuffer = buffer
type ('r, 'len) malloc_pre = unit
type ('h0, 'b, 'h1) alloc_post_mem_common = unit
let update_frozen_until_alloc
  (b :
    (u8, (unit, unit) prefix_freezable_preorder,
      (unit, unit) prefix_freezable_preorder)
      LowStar_Monotonic_Buffer.mbuffer)
  : unit=
  LowStar_Endianness.store32_le_i b Stdint.Uint32.zero
    (Stdint.Uint32.of_int (4));
  LowStar_Monotonic_Buffer.witness_p b ()
let gcmalloc (r : unit) (len : u32) : buffer=
  let h0 = FStar_HyperStack_ST.get () in
  let b =
    LowStar_Monotonic_Buffer.mgcmalloc () 0
      (FStar_UInt32.add len (Stdint.Uint32.of_int (4))) in
  let h = FStar_HyperStack_ST.get () in update_frozen_until_alloc b; b
let malloc (r : unit) (len : u32) : buffer=
  let h0 = FStar_HyperStack_ST.get () in
  let b =
    LowStar_Monotonic_Buffer.mmalloc () 0
      (FStar_UInt32.add len (Stdint.Uint32.of_int (4))) in
  let h = FStar_HyperStack_ST.get () in update_frozen_until_alloc b; b
type 'len alloca_pre = unit
let alloca (len : u32) : buffer=
  let h0 = FStar_HyperStack_ST.get () in
  let b =
    LowStar_Monotonic_Buffer.malloca 0
      (FStar_UInt32.add len (Stdint.Uint32.of_int (4))) in
  let h = FStar_HyperStack_ST.get () in update_frozen_until_alloc b; b
let upd (b : buffer) (i : u32) (v : u8) : unit=
  LowStar_Monotonic_Buffer.recall_p b ();
  (let h = FStar_HyperStack_ST.get () in LowStar_Monotonic_Buffer.upd' b i v)
let freeze (b : buffer) (i : u32) : unit=
  LowStar_Monotonic_Buffer.recall_p b ();
  LowStar_Endianness.store32_le_i b Stdint.Uint32.zero i;
  LowStar_Monotonic_Buffer.witness_p b ()
let frozen_until_st (b : buffer) : u32=
  LowStar_Endianness.load32_le_i b Stdint.Uint32.zero
let witness_slice (b : buffer) (i : u32) (j : u32) (snap : unit) : unit=
  LowStar_Monotonic_Buffer.witness_p b ()
let recall_slice (b : buffer) (i : u32) (j : u32) (snap : unit) : unit=
  LowStar_Monotonic_Buffer.recall_p b ()
let witness_frozen_until (b : buffer) (n : Prims.nat) : unit=
  LowStar_Monotonic_Buffer.witness_p b ()
let recall_frozen_until (b : buffer) (n : Prims.nat) : unit=
  LowStar_Monotonic_Buffer.recall_p b ()
let recall_frozen_until_default (b : buffer) : unit=
  LowStar_Monotonic_Buffer.recall_p b ()

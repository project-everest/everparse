module EverParse3d.InputStream.LowstarExtern.Raw
open Pulse.Lib.Pervasives
open EverParse3d.InputStream.LowstarExtern.Types
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module AP = Pulse.Lib.ArrayPtr
module Util = EverParse3d.Util

// Trusted client boundary: the five old C primitives. All position arguments
// and sequences are erased; only extra, raw base, U64 count and dst reach C.
val has (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: input_stream_base) (n: U64.t) (#pos: Ghost.erased nat)
  : stt bool
    (storage b pos ** pure (pos <= Seq.length (get_all b)))
    (fun r -> storage b pos **
      pure (r == true <==> U64.v n <= Seq.length (get_all b) - pos))

val skip (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: input_stream_base) (n: U64.t) (#pos: Ghost.erased nat)
  : stt unit
    (storage b pos ** pure (pos + U64.v n <= Seq.length (get_all b)))
    (fun _ -> storage b (pos + U64.v n))

val empty (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: input_stream_base) (#pos: Ghost.erased nat)
  : stt U64.t
    (storage b pos ** pure (pos <= Seq.length (get_all b)))
    (fun r -> storage b (Seq.length (get_all b)) **
      pure (U64.v r == Seq.length (get_all b) - pos))

// A read lends a fractional view and withholds BOTH stream and scratch
// ownership. This allows the result to alias dst OR client storage.
// The token is returned only by read. Restoring it is ghost, not a C release.
val read_loan (b: input_stream_base) (pos: nat)
  (n: U64.t) (dst result: AP.ptr U8.t) : slprop

val read (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: input_stream_base) (n: U64.t) (dst: AP.ptr U8.t)
  (#pos: Ghost.erased (p: nat { p + U64.v n <= Seq.length (get_all b) }))
  (#scratch: Ghost.erased (Seq.seq U8.t))
  : stt (AP.ptr U8.t)
    (storage b pos ** AP.pts_to dst scratch **
      pure (pos + U64.v n <= Seq.length (get_all b) /\
            Seq.length scratch == U64.v n))
    (fun result ->
      AP.pts_to result #0.5R (Seq.slice (get_all b) pos (pos + U64.v n)) **
      read_loan b pos n dst result)

val restore_read (b: input_stream_base) (n: U64.t)
  (pos: nat { pos + U64.v n <= Seq.length (get_all b) })
  (dst result: AP.ptr U8.t)
  : stt_ghost unit emp_inames
    (AP.pts_to result #0.5R (Seq.slice (get_all b) pos (pos + U64.v n)) **
      read_loan b pos n dst result)
    (fun _ -> exists* scratch.
      storage b (pos + U64.v n) ** AP.pts_to dst scratch **
      pure (Seq.length scratch == U64.v n))

// Peep is nullable and non-consuming. Its loan similarly avoids overlapping
// full ownership of client storage and the returned readable prefix.
val peep_loan (b: input_stream_base) (pos: nat)
  (n: U64.t) (result: AP.ptr U8.t) : slprop

val peep (#[Util.solve_from_ctx ()] extra: extra_t)
  (b: input_stream_base) (n: U64.t)
  (#pos: Ghost.erased (p: nat { p + U64.v n <= Seq.length (get_all b) }))
  : stt (AP.ptr U8.t)
    (storage b pos ** pure (pos + U64.v n <= Seq.length (get_all b)))
    (fun result ->
      AP.pts_to_or_null result #0.5R
        (Seq.slice (get_all b) pos (pos + U64.v n)) **
      peep_loan b pos n result)

val restore_peep (b: input_stream_base) (n: U64.t)
  (pos: nat { pos + U64.v n <= Seq.length (get_all b) })
  (result: AP.ptr U8.t)
  : stt_ghost unit emp_inames
    (AP.pts_to_or_null result #0.5R
        (Seq.slice (get_all b) pos (pos + U64.v n)) **
      peep_loan b pos n result)
    (fun _ -> storage b pos)

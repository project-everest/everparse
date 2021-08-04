module EverParse3d.InputStream.Buffer
open EverParse3d.InputStream.Buffer.Aux

(* Implementation for single buffers *)

let t = t

let _get_read
  (x: t)
  (h: HS.mem)
: Ghost (Seq.seq U8.t)
  (requires (_live x h))
  (ensures (fun y -> Ghost.reveal x.g_all == y `Seq.append` _get_remaining x h))
=
  let i = U32.v (B.deref h x.pos) in
  Seq.lemma_split x.g_all i;
  Seq.slice x.g_all 0 i

let _is_prefix_of
  (x y: t)
: Tot prop
= x.buf == y.buf /\
  U32.v x.len <= U32.v y.len /\
  x.pos == y.pos /\
  x.g_all_buf == y.g_all_buf /\
  Ghost.reveal x.g_all == Seq.slice (Ghost.reveal y.g_all) 0 (U32.v x.len)

let _get_suffix
  (x y: t)
: Ghost (Seq.seq U8.t)
  (requires (x `_is_prefix_of` y))
  (ensures (fun _ -> True))
= Seq.slice (Ghost.reveal y.g_all) (U32.v x.len) (U32.v y.len)

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false"
#restart-solver

let _is_prefix_of_prop
  (x: t)
  (y: t)
  (h: HS.mem)
: Lemma
  (requires (
    _live x h /\
    x `_is_prefix_of` y
  ))
  (ensures (
      _live y h /\
      _get_read y h `Seq.equal` _get_read x h /\
      _get_remaining y h `Seq.equal` (_get_remaining x h `Seq.append` _get_suffix x y)
  ))
= ()

open LowStar.BufferOps

#restart-solver

module U64 = FStar.UInt64

inline_for_extraction
noextract
let uint32_to_uint64
  (x: U32.t)
: Pure U64.t
  (requires True)
  (ensures (fun y -> U64.v y == U32.v x))
= FStar.Int.Cast.uint32_to_uint64 x

inline_for_extraction
noextract
let uint64_to_uint32
  (x: U64.t)
: Pure U32.t
  (requires (U64.v x < 4294967296))
  (ensures (fun y -> U32.v y == U64.v x))
= FStar.Math.Lemmas.modulo_lemma (U64.v x) 4294967296;
  FStar.Int.Cast.uint64_to_uint32 x

let inst = {

  live = _live;

  footprint = _footprint;

  live_not_unused_in = begin fun x h ->
    ()
  end;

  len_all = begin fun x ->
    uint32_to_uint64 x.len
  end;

  get_all = begin fun x ->
    Ghost.reveal x.g_all
  end;

  get_remaining = begin fun x h ->
    _get_remaining x h
  end;

  get_read = begin fun x h ->
    _get_read x h
  end;

  preserved = begin fun x l h h' ->
    ()
  end;
  
  has = begin fun x currentPosition n ->
    n `U64.lte` (uint32_to_uint64 x.len `U64.sub` currentPosition)
  end;

  read = begin fun x currentPosition n dst ->
    let h0 = HST.get () in
    let res = B.sub x.buf (uint64_to_uint32 currentPosition) (uint64_to_uint32 n) in
    x.pos *= uint64_to_uint32 (currentPosition `U64.add` n);
    let h' = HST.get () in
    res
  end;

  skip = begin fun x currentPosition n ->
    let h0 = HST.get () in
    x.pos *= uint64_to_uint32 (currentPosition `U64.add` n);
    let h' = HST.get () in
    ()
  end;

  empty = begin fun x _ ->
    let h0 = HST.get () in
    x.pos *= x.len;
    uint32_to_uint64 x.len
  end;

  is_prefix_of = _is_prefix_of;

  get_suffix = _get_suffix;

  is_prefix_of_prop = _is_prefix_of_prop;

  truncate = begin fun x currentPosition n ->
    {
      buf = x.buf;
      len = uint64_to_uint32 (currentPosition `U64.add` n);
      pos = x.pos;
      g_all = Ghost.hide (Seq.slice (Ghost.reveal x.g_all) 0 (U64.v currentPosition + U64.v n));
      g_all_buf = x.g_all_buf;
      prf = ();
    }
  end;
}

#pop-options

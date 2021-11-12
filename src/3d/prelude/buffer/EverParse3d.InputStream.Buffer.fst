module EverParse3d.InputStream.Buffer
open EverParse3d.InputStream.Buffer.Aux

(* Implementation for single buffers *)

module U64 = FStar.UInt64

let t = t

inline_for_extraction
noextract
let _tlen
  (x: t)
: Tot Type0
= (len: U64.t { U64.v len == U32.v x.len })

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
= x.len0 == y.len0 /\
  x.buf == y.buf /\
  x.perm_of == y.perm_of /\
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

module LP = LowParse.Low.Base
module IB = EverParse3d.InputBuffer
module IR = EverParse3d.Readable

let inst = {

  live = _live;

  footprint = _footprint;

  perm_footprint = _perm_footprint;

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

  tlen = _tlen;
  
  has = begin fun x xlen currentPosition n ->
    n `U64.lte` (xlen `U64.sub` currentPosition)
  end;

  read = begin fun _ k p r x currentPosition n ->
    let h = HST.get () in
    LP.parser_kind_prop_equiv k p;
    x.pos *= uint64_to_uint32 (currentPosition `U64.add` n);
    let h1 = HST.get () in
    LP.parse_strong_prefix p (_get_remaining x h) (LP.bytes_of_slice_from_to h (IB.slice_of x.buf) (uint64_to_uint32 currentPosition) x.len0);
    LP.parse_strong_prefix p (_get_remaining x h) (LP.bytes_of_slice_from_to h (IB.slice_of x.buf) (uint64_to_uint32 currentPosition) (uint64_to_uint32 (currentPosition `U64.add` n)));
    LP.valid_facts p h (IB.slice_of x.buf) (uint64_to_uint32 currentPosition);
    IR.readable_split' h x.perm_of (uint64_to_uint32 currentPosition) (uint64_to_uint32 (currentPosition `U64.add` n)) x.len0;
    let prf (h': HS.mem) : Lemma
      (requires (
        let pos = uint64_to_uint32 currentPosition in
        let pos' = uint64_to_uint32 (currentPosition `U64.add` n) in
        B.modifies (IR.loc_perm x.perm_of) h1 h' /\
        IR.preserved x.perm_of 0ul pos h1 h' /\
        IR.preserved x.perm_of pos' (B.len (IB.slice_of x.buf).LP.base) h1 h' /\
        IR.unreadable h' x.perm_of pos pos' /\
        IB.live_input_buffer h' x.buf x.perm_of
      ))
      (ensures (
        IR.unreadable h' x.perm_of 0ul (B.deref h' x.pos) /\
        IR.readable h' x.perm_of (B.deref h' x.pos) x.len0
      ))
      [SMTPat (B.modifies (IR.loc_perm x.perm_of) h1 h')] // this lemma *with SMT pattern* allows tail call to the reader, thus removing spurious temporary assignments in the generated C code
    =
      IR.unreadable_frame0 h1 x.perm_of 0ul (uint64_to_uint32 currentPosition) h' ;
      IR.unreadable_merge' h' x.perm_of 0ul (uint64_to_uint32 currentPosition) (uint64_to_uint32 (currentPosition `U64.add` n));
      IR.readable_frame0 h1 x.perm_of (uint64_to_uint32 (currentPosition `U64.add` n)) x.len0 h'
    in
    IB.read_with_perm r x.buf (uint64_to_uint32 currentPosition) (uint64_to_uint32 n) x.perm_of
  end;

  skip = begin fun x currentPosition n ->
    let h0 = HST.get () in
    IR.readable_split' h0 x.perm_of (uint64_to_uint32 currentPosition) (uint64_to_uint32 (currentPosition `U64.add` n)) x.len0;
    x.pos *= uint64_to_uint32 (currentPosition `U64.add` n);
    let h1 = HST.get () in
    IB.drop x.buf (uint64_to_uint32 currentPosition) (uint64_to_uint32 (currentPosition `U64.add` n)) x.perm_of;
    let h' = HST.get () in
    IR.unreadable_frame0 h1 x.perm_of 0ul (uint64_to_uint32 currentPosition) h';
    IR.unreadable_merge' h' x.perm_of 0ul (uint64_to_uint32 currentPosition) (uint64_to_uint32 (currentPosition `U64.add` n));
    IR.readable_frame0 h1 x.perm_of (uint64_to_uint32 (currentPosition `U64.add` n)) x.len0 h' ;
    ()
  end;

  skip_if_success = begin fun x currentPosition res ->
    let h0 = HST.get () in
    let pos0 = !* x.pos in
    let pos1 = Ghost.hide (if EverParse3d.ErrorCode.is_success res then uint64_to_uint32 res else Ghost.reveal pos0) in
    x.pos *= pos1;
    let h1 = HST.get () in
    IR.readable_split' h1 x.perm_of pos0 pos1 x.len0;
    IB.drop x.buf pos0 pos1 x.perm_of;
    let h2 = HST.get () in
    IR.unreadable_frame0 h1 x.perm_of 0ul pos0 h2;
    IR.unreadable_merge' h2 x.perm_of 0ul pos0 pos1;
    IR.readable_frame0 h1 x.perm_of pos1 x.len0 h2
  end;

  empty = begin fun x xlen _ ->
    let h0 = HST.get () in
    let pos0 = !* x.pos in
    x.pos *= x.len;
    let h1 = HST.get () in
    IR.readable_split' h1 x.perm_of pos0 x.len x.len0;
    IB.drop x.buf pos0 x.len x.perm_of;
    let h2 = HST.get () in
    IR.unreadable_frame0 h1 x.perm_of 0ul pos0 h2;
    IR.unreadable_merge' h2 x.perm_of 0ul pos0 x.len;
    IR.readable_frame0 h1 x.perm_of x.len x.len0 h2;
    xlen
  end;

  is_prefix_of = _is_prefix_of;

  get_suffix = _get_suffix;

  is_prefix_of_prop = _is_prefix_of_prop;

  truncate = begin fun x currentPosition n ->
    {
      len0 = x.len0;
      buf = x.buf;
      perm_of = x.perm_of;
      len = uint64_to_uint32 (currentPosition `U64.add` n);
      pos = x.pos;
      g_all = Ghost.hide (Seq.slice (Ghost.reveal x.g_all) 0 (U64.v currentPosition + U64.v n));
      g_all_buf = x.g_all_buf;
      prf = ();
    }
  end;

  truncate_len = begin fun x currentPosition n truncated ->
    currentPosition `U64.add` n
  end;
}

#pop-options

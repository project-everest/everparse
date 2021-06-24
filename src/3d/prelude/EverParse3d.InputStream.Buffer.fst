module EverParse3d.InputStream.Buffer

(* Implementation for single buffers *)

noeq
type t = {
  buf: B.buffer U8.t;
  len: U32.t;
  pos: B.pointer U32.t;
  g_all: Ghost.erased (Seq.seq U8.t);
  prf: squash (
    len == B.len buf /\
    Seq.length (Ghost.reveal g_all) == U32.v len /\
    B.loc_disjoint (B.loc_buffer buf) (B.loc_buffer pos)
  );
}

let _live
  (x: t)
  (h: HS.mem)
: Tot prop
=
  B.live h x.buf /\
  B.live h x.pos /\
  U32.v (B.deref h x.pos) <= B.length x.buf /\
  B.as_seq h x.buf == Ghost.reveal x.g_all

let _get_remaining
  (x: t)
  (h: HS.mem)
: Ghost (Seq.seq U8.t)
  (requires (_live x h))
  (ensures (fun y -> Seq.length y <= U32.v x.len))
= 
  let i = U32.v (B.deref h x.pos) in
  Seq.slice x.g_all i (Seq.length x.g_all)

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

let phi
  (a b c: int)
: Lemma
  (requires (a == b - c))
  (ensures (c + a == b))
= ()

open LowStar.BufferOps

#push-options "--z3rlimit 16 --z3cliopt smt.arith.nl=false"
#restart-solver

let inst = {

  live = _live;

  footprint = begin fun x ->
    B.loc_buffer x.buf `B.loc_union` B.loc_buffer x.pos
  end;

  len_all = begin fun x ->
    x.len
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
  
  has = begin fun x n ->
    let pos = !* x.pos in
    n `U32.lte` (x.len `U32.sub` pos)
  end;

  read = begin fun x n dst ->
    let h0 = HST.get () in
    let pos = !* x.pos in
    B.blit x.buf pos dst 0ul n;
    x.pos *= pos `U32.add` n;
    let h' = HST.get () in
    assert (B.deref h' x.pos == pos `U32.add` n);
    Seq.slice_length (B.as_seq h' dst);
    Seq.slice_slice (B.as_seq h0 x.buf) (U32.v pos) (U32.v x.len) 0 (U32.v n);
    Seq.slice_slice (B.as_seq h0 x.buf) (U32.v pos) (B.length x.buf) (U32.v n) (Seq.length (_get_remaining x h0));
    phi (Seq.length (_get_remaining x h0)) (B.length x.buf) (U32.v pos);
    ()
  end;

  skip = begin fun x n ->
    let h0 = HST.get () in
    let pos = !* x.pos in
    x.pos *= pos `U32.add` n;
    let h' = HST.get () in
    assert (B.deref h' x.pos == pos `U32.add` n);
    Seq.slice_slice (B.as_seq h0 x.buf) (U32.v pos) (B.length x.buf) (U32.v n) (Seq.length (_get_remaining x h0));
    phi (Seq.length (_get_remaining x h0)) (B.length x.buf) (U32.v pos);
    ()
  end;

  get_read_count = begin fun x ->
    !* x.pos
  end;

}

let make from n =
  let h = HST.get () in
  let g = Ghost.hide (B.as_seq h from) in
  let pos = B.malloc HS.root 0ul 1ul in
  {
    buf = from;
    len = n;
    pos = pos;
    g_all = g;
    prf = ();
  }

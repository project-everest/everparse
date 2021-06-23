module EverParse3d.InputStream

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

let live x h =
  B.live h x.buf /\
  B.live h x.pos /\
  U32.v (B.deref h x.pos) <= B.length x.buf /\
  B.as_seq h x.buf == Ghost.reveal x.g_all

let footprint x =
  B.loc_buffer x.buf `B.loc_union` B.loc_buffer x.pos

let len_all x =
  x.len

let get_all x =
  Ghost.reveal x.g_all

let get_remaining x h =
  let i = U32.v (B.deref h x.pos) in
  Seq.slice x.g_all i (Seq.length x.g_all)

let get_remaining_is_suffix x h =
  let i = U32.v (B.deref h x.pos) in
  Seq.lemma_split x.g_all i

let preserved x l h h' = ()

open LowStar.BufferOps

let has x n =
  let pos = !* x.pos in
  n `U32.lte` (x.len `U32.sub` pos)

let phi
  (a b c: int)
: Lemma
  (requires (a == b - c))
  (ensures (c + a == b))
= ()

#push-options "--z3rlimit 16 --z3cliopt smt.arith.nl=false"
#restart-solver

let read x n dst =
  let h0 = HST.get () in
  let pos = !* x.pos in
  B.blit x.buf pos dst 0ul n;
  x.pos *= pos `U32.add` n;
  let h' = HST.get () in
  assert (B.deref h' x.pos == pos `U32.add` n);
  Seq.slice_length (B.as_seq h' dst);
  Seq.slice_slice (B.as_seq h0 x.buf) (U32.v pos) (U32.v x.len) 0 (U32.v n);
  Seq.slice_slice (B.as_seq h0 x.buf) (U32.v pos) (B.length x.buf) (U32.v n) (Seq.length (get_remaining x h0));
  phi (Seq.length (get_remaining x h0)) (B.length x.buf) (U32.v pos);
  ()

let skip x n =
  let h0 = HST.get () in
  let pos = !* x.pos in
  x.pos *= pos `U32.add` n;
  let h' = HST.get () in
  assert (B.deref h' x.pos == pos `U32.add` n);
  Seq.slice_slice (B.as_seq h0 x.buf) (U32.v pos) (B.length x.buf) (U32.v n) (Seq.length (get_remaining x h0));
  phi (Seq.length (get_remaining x h0)) (B.length x.buf) (U32.v pos);
  ()

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

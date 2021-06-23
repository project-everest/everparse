module EverParse3d.InputStream

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

val t : Type0

val live (x: t) (h: HS.mem) : Tot prop

val footprint (x: t) : Ghost B.loc
  (requires True)
  (ensures (fun y -> B.address_liveness_insensitive_locs `B.loc_includes` y))

val len_all (x: t) : GTot U32.t

let length_all (x: t) : GTot nat = U32.v (len_all x)

val get_all (x: t) : Ghost (Seq.seq U8.t)
  (requires True)
  (ensures (fun y -> Seq.length y == length_all x))

val get_remaining (x: t) (h: HS.mem) : Ghost (Seq.seq U8.t)
  (requires (live x h))
  (ensures (fun y -> Seq.length y <= length_all x))

val get_remaining_is_suffix (x: t) (h: HS.mem) : Lemma
  (requires (live x h))
  (ensures (exists z . get_all x == z `Seq.append` get_remaining x h))

val preserved
  (x: t)
  (l: B.loc)
  (h h' : HS.mem)
: Lemma
  (requires (live x h /\ B.modifies l h h' /\ B.loc_disjoint (footprint x) l))
  (ensures (
    live x h' /\
    get_remaining x h' == get_remaining x h
  ))

let get_read (x: t) (h: HS.mem) : Ghost (Seq.seq U8.t)
  (requires (live x h))
  (ensures (fun y -> get_all x `Seq.equal` (y `Seq.append` get_remaining x h)))
=
  let s = get_all x in
  get_remaining_is_suffix x h;
  Seq.slice s 0 (Seq.length s - Seq.length (get_remaining x h))

let preserved'
  (x: t)
  (l: B.loc)
  (h h' : HS.mem)
: Lemma
  (requires (live x h /\ B.modifies l h h' /\ B.loc_disjoint (footprint x) l))
  (ensures (
    live x h' /\
    get_remaining x h' == get_remaining x h /\
    get_read x h' == get_read x h
  ))
  [SMTPatOr [
    [SMTPat (live x h); SMTPat (B.modifies l h h')];
    [SMTPat (live x h'); SMTPat (B.modifies l h h')];
    [SMTPat (get_remaining x h); SMTPat (B.modifies l h h')];
    [SMTPat (get_remaining x h'); SMTPat (B.modifies l h h')];
    [SMTPat (get_read x h); SMTPat (B.modifies l h h')];
    [SMTPat (get_read x h'); SMTPat (B.modifies l h h')];
  ]]
= preserved x l h h'

val has
  (x: t)
  (n: U32.t)
: HST.Stack bool
  (requires (fun h -> live x h))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    (res == true <==> Seq.length (get_remaining x h) >= U32.v n)
  ))

val read
  (x: t)
  (n: U32.t)
  (dst: B.buffer U8.t)
: HST.Stack unit
    (requires (fun h -> live x h /\ B.live h dst /\ B.loc_disjoint (footprint x) (B.loc_buffer dst) /\ B.length dst == U32.v n /\ Seq.length (get_remaining x h) >= U32.v n))
    (ensures (fun h _ h' ->
      let s = get_remaining x h in
      B.modifies (B.loc_buffer dst `B.loc_union` footprint x) h h' /\
      B.as_seq h' dst == Seq.slice s 0 (U32.v n) /\
      live x h' /\
      get_remaining x h' == Seq.slice s (U32.v n) (Seq.length s)
    ))

val skip
  (x: t)
  (n: U32.t)
: HST.Stack unit
    (requires (fun h -> live x h /\ Seq.length (get_remaining x h) >= U32.v n))
    (ensures (fun h _ h' ->
      let s = get_remaining x h in
      B.modifies (footprint x) h h' /\
      live x h' /\
      get_remaining x h' == Seq.slice s (U32.v n) (Seq.length s)
    ))

val make
  (from: B.buffer U8.t)
  (n: U32.t)
: HST.ST t
  (requires (fun h -> B.live h from /\ U32.v n == B.length from))
  (ensures (fun h res h' ->
    B.modifies (B.loc_buffer from) h h' /\
    footprint res `B.loc_includes` B.loc_buffer from /\
    (B.loc_unused_in h `B.loc_union` B.loc_buffer from) `B.loc_includes` footprint res /\
    live res h' /\
    get_remaining res h' == B.as_seq h from
  ))

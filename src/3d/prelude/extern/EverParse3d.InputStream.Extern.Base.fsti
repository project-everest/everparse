module EverParse3d.InputStream.Extern.Base

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module LPE = EverParse3d.ErrorCode
module U64 = FStar.UInt64

val input_stream_base : Type0

inline_for_extraction
noextract
let t = input_stream_base

val live: t -> HS.mem -> Tot prop

val footprint
  (x: t)
: Ghost B.loc
  (requires True)
  (ensures (fun y -> B.address_liveness_insensitive_locs `B.loc_includes` y))

val live_not_unused_in :
    (x: t) ->
    (h: HS.mem) ->
    Lemma
    (requires (live x h))
    (ensures (B.loc_not_unused_in h `B.loc_includes` footprint x))

val len_all: (x: t) -> GTot LPE.pos_t

/// WARNING: the following assumes that no computations shall overflow
val get_all: (x: t) -> Ghost (Seq.seq U8.t)
    (requires True)
    (ensures (fun y -> Seq.length y == U64.v (len_all x)))

val get_remaining: (x: t) -> (h: HS.mem) -> Ghost (Seq.seq U8.t)
    (requires (live x h))
    (ensures (fun y -> Seq.length y <= U64.v (len_all x)))

val get_read: (x: t) -> (h: HS.mem) -> Ghost (Seq.seq U8.t)
    (requires (live x h))
    (ensures (fun y -> get_all x `Seq.equal` (y `Seq.append` get_remaining x h)))

val preserved:
    (x: t) ->
    (l: B.loc) ->
    (h: HS.mem) ->
    (h' : HS.mem) ->
    Lemma
    (requires (live x h /\ B.modifies l h h' /\ B.loc_disjoint (footprint x) l))
    (ensures (
      live x h' /\
      get_remaining x h' == get_remaining x h /\
      get_read x h' == get_read x h
    ))

val has:
    (x: t) ->
    (n: U64.t) ->
    HST.Stack bool
    (requires (fun h -> live x h))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      (res == true <==> Seq.length (get_remaining x h) >= U64.v n)
    ))

val read:
    (x: t) ->
    (n: U64.t) ->
    (dst: B.buffer U8.t) ->
    HST.Stack (B.buffer U8.t)
    (requires (fun h ->
      live x h /\
      B.live h dst /\
      B.loc_disjoint (footprint x) (B.loc_buffer dst) /\
      B.length dst == U64.v n /\
      Seq.length (get_remaining x h) >= U64.v n
    ))
    (ensures (fun h dst' h' ->
      let s = get_remaining x h in
      B.modifies (B.loc_buffer dst `B.loc_union` footprint x) h h' /\
      B.as_seq h' dst' `Seq.equal` Seq.slice s 0 (U64.v n) /\
      live x h' /\
      B.live h' dst /\
      B.live h' dst' /\
      (B.loc_buffer dst `B.loc_union` footprint x) `B.loc_includes` B.loc_buffer dst' /\
      get_remaining x h' `Seq.equal` Seq.slice s (U64.v n) (Seq.length s)
    ))

val skip:
    (x: t) ->
    (n: U64.t) ->
    HST.Stack unit
    (requires (fun h -> live x h /\ Seq.length (get_remaining x h) >= U64.v n))
    (ensures (fun h _ h' ->
      let s = get_remaining x h in
      B.modifies (footprint x) h h' /\
      live x h' /\
      get_remaining x h' `Seq.equal` Seq.slice s (U64.v n) (Seq.length s)
    ))

val empty:
    (x: t) ->
    HST.Stack U64.t
    (requires (fun h -> live x h))
    (ensures (fun h res h' ->
      B.modifies (footprint x) h h' /\
      live x h' /\
      get_remaining x h' `Seq.equal` Seq.empty /\
      U64.v res == Seq.length (get_remaining x h)
    ))

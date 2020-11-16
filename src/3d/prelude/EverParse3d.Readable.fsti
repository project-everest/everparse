module EverParse3d.Readable

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LPL = LowParse.Low.Base

inline_for_extraction noextract
val perm (#t: Type) (b: B.buffer t) : Tot Type0

val loc_perm (#t: _) (#b: B.buffer t) (p: perm b) : GTot B.loc

val loc_perm_prop (#t: _) (#b: B.buffer t) (p: perm b) : Lemma
  (B.address_liveness_insensitive_locs `B.loc_includes` loc_perm p)
  [SMTPat (loc_perm p)]

val valid_perm (h: HS.mem) (#t: _) (#b: B.buffer t) (p: perm b) : GTot Type0

val valid_perm_prop (h: HS.mem) (#t: _) (#b: B.buffer t) (p: perm b)
: Lemma
  (requires (valid_perm h p))
  (ensures (
    B.live h b /\
    B.loc_buffer b `B.loc_disjoint` loc_perm p /\
    loc_perm p `B.loc_in` h
  ))
  [SMTPat (valid_perm h p)]

val valid_perm_frame
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    valid_perm h p /\
    B.modifies (B.address_liveness_insensitive_locs `B.loc_union` l) h h' /\
    B.loc_disjoint (loc_perm p) l /\
    B.live h' b // because nothing prevents b from being deallocated
  ))
  (ensures (
    valid_perm h' p
  ))

let valid_perm_frame_pat
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    valid_perm h p /\
    B.modifies l h h' /\
    B.loc_disjoint (loc_perm p) l /\
    B.live h' b // because nothing prevents b from being deallocated
  ))
  (ensures (
    valid_perm h' p
  ))
  [SMTPatOr [
    [ SMTPat (B.modifies l h h'); SMTPat (valid_perm h p) ] ;
    [ SMTPat (B.modifies l h h'); SMTPat (valid_perm h' p) ] ;
  ]]
= valid_perm_frame h p l h'

val perm_gsub
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
: GTot (perm (B.gsub b offset length))

inline_for_extraction
noextract
val perm_sub
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
: HST.Stack (perm (B.gsub b offset length))
  (requires (fun h -> valid_perm h p))
  (ensures (fun h p' h' ->
    h' == h /\
    p' == perm_gsub p offset length
  ))

inline_for_extraction
noextract
val perm_offset
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset: U32.t { U32.v offset <= B.length b })
: HST.Stack (perm (B.gsub b offset (B.len b `U32.sub` offset)))
  (requires (fun h -> valid_perm h p))
  (ensures (fun h p' h' ->
    h' == h /\
    p' == perm_gsub p offset (B.len b `U32.sub` offset)
  ))

val perm_gsub_gsub
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset1: U32.t)
  (length1: U32.t { U32.v offset1 + U32.v length1 <= B.length b })
  (offset2: U32.t)
  (length2: U32.t { U32.v offset2 + U32.v length2 <= U32.v length1 })
: Lemma
  ( 
    perm_gsub (perm_gsub p offset1 length1) offset2 length2 == LPL.coerce (perm (B.gsub (B.gsub b offset1 length1) offset2 length2)) (perm_gsub p (offset1 `U32.add` offset2) length2)
  )
  [SMTPat (perm_gsub (perm_gsub p offset1 length1) offset2 length2)]

val perm_gsub_zero_length
  (#t: _) (#b: B.buffer t) (p: perm b)
: Lemma
  (
    B.gsub b 0ul (B.len b) == b /\
    perm_gsub p 0ul (B.len b) == LPL.coerce (perm (B.gsub b 0ul (B.len b))) p
  )

val loc_perm_gsub
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
: Lemma
  (loc_perm p `B.loc_includes` loc_perm (perm_gsub p offset length))
  [SMTPat (loc_perm (perm_gsub p offset length))]

let loc_perm_gsub_includes
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset1: U32.t)
  (length1: U32.t)
  (offset2: U32.t)
  (length2: U32.t)
: Lemma
  (requires (
    U32.v offset1 <= U32.v offset2 /\
    U32.v offset2 + U32.v length2 <= U32.v offset1 + U32.v length1 /\
    U32.v offset1 + U32.v length1 <= B.length b
  ))
  (ensures (
    loc_perm (perm_gsub p offset1 length1) `B.loc_includes` loc_perm (perm_gsub p offset2 length2)
  ))
//  [SMTPat [loc_perm (perm_gsub p offset1 length1) `B.loc_includes` loc_perm (perm_gsub p offset2 length2)]]
= perm_gsub_gsub p offset1 length1 (offset2 `U32.sub` offset1) length2

val valid_perm_gsub
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
: Lemma
  (requires (valid_perm h p))
  (ensures (valid_perm h (perm_gsub p offset length)))
  [SMTPat (valid_perm h (perm_gsub p offset length))]

let loc_perm_from_to
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: GTot B.loc
= loc_perm (perm_gsub p from (to `U32.sub` from))

val loc_perm_from_to_disjoint
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from1: U32.t)
  (to1: U32.t { U32.v from1 <= U32.v to1 /\ U32.v to1 <= B.length b })
  (from2: U32.t)
  (to2: U32.t { U32.v from2 <= U32.v to2 /\ U32.v to2 <= B.length b })
: Lemma
  (requires (U32.v to1 <= U32.v from2 \/ U32.v to2 <= U32.v from1))
  (ensures (loc_perm_from_to p from1 to1 `B.loc_disjoint` loc_perm_from_to p from2 to2))
  [SMTPat (loc_perm_from_to p from1 to1 `B.loc_disjoint` loc_perm_from_to p from2 to2)]

let loc_perm_from_to_includes
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from1: U32.t)
  (to1: U32.t { U32.v from1 <= U32.v to1 /\ U32.v to1 <= B.length b })
  (from2: U32.t)
  (to2: U32.t { U32.v from1 <= U32.v from2 /\ U32.v from2 <= U32.v to2 /\ U32.v to2 <= U32.v to1 })
: Lemma
  (requires True)
  (ensures (loc_perm_from_to p from1 to1 `B.loc_includes` loc_perm_from_to p from2 to2))
  [SMTPat (loc_perm_from_to p from1 to1 `B.loc_includes` loc_perm_from_to p from2 to2)]
= loc_perm_gsub_includes p from1 (to1 `U32.sub` from1) from2 (to2 `U32.sub` from2)

val readable
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: GTot Type0

val readable_prop
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (readable h p from to))
  (ensures (valid_perm h p))
  [SMTPat (readable h p from to)]

val readable_gsub
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= U32.v length })
: Lemma
  (requires (valid_perm h p))
  (ensures (readable h (perm_gsub p offset length) from to <==> readable h p (offset `U32.add` from) (offset `U32.add` to)))
  [SMTPat (readable h (perm_gsub p offset length) from to)]

val readable_split
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (readable h p from to <==> (readable h p from mid /\ readable h p mid to))

val readable_frame
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    readable h p from to /\
    B.modifies l h h' /\
    B.loc_disjoint (loc_perm_from_to p from to) l /\
    B.live h' b // because nothing prevents b from being deallocated
  ))
  (ensures (
    readable h' p from to
  ))
  [SMTPatOr [
    [ SMTPat (B.modifies l h h'); SMTPat (readable h p from to) ] ;
    [ SMTPat (B.modifies l h h'); SMTPat (readable h' p from to) ] ;
  ]]

val unreadable
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: GTot Type0

val unreadable_prop
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (~ (valid_perm h p)))
  (ensures (unreadable h p from to))
  [SMTPat (readable h p from to)]

val model : FStar.Ghost.erased bool

val readable_not_unreadable
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from < (* important: not equal *) U32.v to /\ U32.v to <= B.length b })
: Lemma
  (FStar.Ghost.reveal model ==> (~ (readable h p from to /\ unreadable h p from to)))

val unreadable_gsub
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (offset: U32.t)
  (length: U32.t { U32.v offset + U32.v length <= B.length b })
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= U32.v length })
: Lemma
  (requires (valid_perm h p))
  (ensures (unreadable h (perm_gsub p offset length) from to <==> unreadable h p (offset `U32.add` from) (offset `U32.add` to)))
  [SMTPat (unreadable h (perm_gsub p offset length) from to)]

val unreadable_split
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (unreadable h p from to <==> (unreadable h p from mid /\ unreadable h p mid to))

val unreadable_empty
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (i: U32.t { U32.v i <= B.length b })
: Lemma
  (unreadable h p i i)

val unreadable_frame
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    B.modifies l h h' /\
    (valid_perm h' p ==> (
      valid_perm h p /\
      unreadable h p from to /\
      B.loc_disjoint (loc_perm_from_to p from to) l /\
      B.live h' b // because nothing prevents b from being deallocated
  ))))
  (ensures (
    unreadable h' p from to
  ))
  [SMTPatOr [
    [ SMTPat (B.modifies l h h'); SMTPat (unreadable h p from to) ] ;
    [ SMTPat (B.modifies l h h'); SMTPat (unreadable h' p from to) ] ;
  ]]

inline_for_extraction
noextract
val drop
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: HST.Stack unit
  (requires (fun h ->
    valid_perm h p
  ))
  (ensures (fun h _ h' ->
    B.modifies (loc_perm_from_to p from to) h h' /\
    valid_perm h' p /\
    unreadable h' p from to
  ))

inline_for_extraction
noextract
val drop_if
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
  (cond: Ghost.erased bool)
: HST.Stack unit
  (requires (fun h ->
    valid_perm h p /\
    readable h p from to
  ))
  (ensures (fun h _ h' ->
    B.modifies (loc_perm_from_to p from (if cond then mid else to)) h h' /\
    valid_perm h' p /\
    unreadable h' p from (if cond then mid else to)
  ))

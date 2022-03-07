module EverParse3d.Readable

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LPL = LowParse.Low.Base

// not erasable because Low* buffers of erased elements are not erasable
inline_for_extraction noextract
val perm0 (t: Type) : Tot Type0

val perm_prop (#t: Type) (x: perm0 t) (b: B.buffer t) : Tot prop

inline_for_extraction noextract
let perm (#t: Type) (b: B.buffer t) = (x: perm0 t { perm_prop x b })

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

val preserved
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (h h' : HS.mem)
: Tot prop

val valid_perm_frame
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
    valid_perm h' p /\
    preserved p 0ul (B.len b) h h'
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
    valid_perm h' p /\
    preserved p 0ul (B.len b) h h'
  ))
  [SMTPatOr [
    [ SMTPat (B.modifies l h h'); SMTPat (valid_perm h p) ] ;
    [ SMTPat (B.modifies l h h'); SMTPat (valid_perm h' p) ] ;
  ]]
= valid_perm_frame h p l h'

val preserved_refl
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (h: HS.mem)
: Lemma
  (preserved p from to h h)

val preserved_trans
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (h1 h2 h3: HS.mem)
: Lemma
  (requires (
    preserved p from to h1 h2 /\
    preserved p from to h2 h3
  ))
  (ensures (
    preserved p from to h1 h3
  ))

val preserved_split
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
  (h h' : HS.mem)
: Lemma
  (preserved p from to h h' <==> (preserved p from mid h h' /\ preserved p mid to h h'))

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

val readable_split
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (readable h p from to <==> (readable h p from mid /\ readable h p mid to))

let readable_split'
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (readable h p from to))
  (ensures (readable h p from mid /\ readable h p mid to))
= readable_split h p from mid to

let readable_merge'
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (
    readable h p from mid /\
    readable h p mid to
  ))
  (ensures (readable h p from to))
= readable_split h p from mid to

val readable_frame0
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (h' : HS.mem)
: Lemma
  (requires (
    readable h p from to /\
    preserved p from to h h'
  ))
  (ensures (
    readable h' p from to
  ))

let readable_frame
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
    B.loc_disjoint (loc_perm p) l /\
    B.live h' b // because nothing prevents b from being deallocated
  ))
  (ensures (
    readable h' p from to
  ))
  [SMTPatOr [
    [ SMTPat (B.modifies l h h'); SMTPat (readable h p from to) ] ;
    [ SMTPat (B.modifies l h h'); SMTPat (readable h' p from to) ] ;
  ]]
=
  valid_perm_frame h p l h' ;
  preserved_split p 0ul from (B.len b) h h' ;
  preserved_split p from to (B.len b) h h' ;
  readable_frame0 h p from to h'

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

val readable_not_unreadable
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from < (* important: not equal *) U32.v to /\ U32.v to <= B.length b })
: Lemma
  (~ (readable h p from to /\ unreadable h p from to))

val unreadable_split
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (unreadable h p from to <==> (unreadable h p from mid /\ unreadable h p mid to))

let unreadable_split'
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (unreadable h p from to))
  (ensures (unreadable h p from mid /\ unreadable h p mid to))
= unreadable_split h p from mid to

let unreadable_merge'
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (
    unreadable h p from mid /\
    unreadable h p mid to
  ))
  (ensures (unreadable h p from to))
= unreadable_split h p from mid to

val unreadable_empty
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (i: U32.t { U32.v i <= B.length b })
: Lemma
  (unreadable h p i i)

val unreadable_frame0
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (h' : HS.mem)
: Lemma
  (requires (
    (valid_perm h' p ==> (
      valid_perm h p /\
      unreadable h p from to /\
      preserved p from to h h'
  ))))
  (ensures (
    unreadable h' p from to
  ))

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
      B.loc_disjoint (loc_perm p) l /\
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
  (from: Ghost.erased U32.t)
  (to: Ghost.erased U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
: HST.Stack unit
  (requires (fun h ->
    readable h p from to
  ))
  (ensures (fun h _ h' ->
    B.modifies (loc_perm p) h h' /\
    valid_perm h' p /\
    preserved p 0ul from h h' /\
    preserved p to (B.len b) h h' /\
    unreadable h' p from to
  ))

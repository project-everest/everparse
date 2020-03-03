module EverParse3d.Readable

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = FStar.Seq

module F = EverParse3d.Flags

inline_for_extraction
noextract
let perm' (#t: Type0) (b: B.buffer t)
: Tot Type0
= B.lbuffer (G.erased bool) (B.length b)

let perm #t b = if F.model then perm' b else unit
  
let loc_perm #t #b p = if F.model then B.loc_buffer (p <: perm' b) else B.loc_none

let loc_perm_prop #t #b p = ()

let valid_perm h #t #b p =
  B.live h b /\
  B.loc_buffer b `B.loc_disjoint` loc_perm p /\
  (F.model ==> B.live h (p <: perm' b))

let valid_perm_prop h #t #b p = ()

let valid_perm_frame h #t #b p l h' = ()

let perm_gsub #t #b p offset length = if F.model then B.gsub (p <: perm' b) offset length else ()

let perm_sub #t #b p offset length = if F.model then B.sub (p <: perm' b) offset length else ()

let perm_offset #t #b p offset = if F.model then B.offset (p <: perm' b) offset else ()

let perm_gsub_gsub #t #b p offset1 length1 offset2 length2 = ()

let perm_gsub_zero_length #t #b p =
  B.gsub_zero_length b;
  if F.model then B.gsub_zero_length (p <: perm' b)

let loc_perm_gsub #t #b p offset length = ()

let valid_perm_gsub h #t #b p offset length = ()

let loc_perm_from_to_disjoint #t #b p from1 to1 from2 to2 = ()

let readable h #t #b p from to =
  valid_perm h p /\
  (F.model ==> B.as_seq h (B.gsub p from (to `U32.sub` from)) `Seq.equal` Seq.create (U32.v to - U32.v from) (G.hide true))

let readable_prop h #t #b p from to = ()

let readable_gsub h #t #b p offset length from to = ()

let readable_split h #t #b p from mid to =
  Seq.lemma_split (B.as_seq h (B.gsub b from (to `U32.sub` from))) (U32.v mid - U32.v from);
  if F.model then Seq.lemma_split (B.as_seq h (B.gsub (p <: perm' b) from (to `U32.sub` from))) (U32.v mid - U32.v from)

let readable_frame h #t #b p from to l h' = ()

let unreadable h #t #b p from to =
  (valid_perm h p /\ F.model) ==>
  B.as_seq h (B.gsub p from (to `U32.sub` from)) `Seq.equal` Seq.create (U32.v to - U32.v from) (G.hide false)

let unreadable_prop h #t #b p from to = ()

let model = FStar.Ghost.hide F.model

let readable_not_unreadable h #t #b p from to =
  let f () : Lemma
    (requires (F.model /\ readable h p from to /\ unreadable h p from to))
    (ensures False)
  = assert (valid_perm h p);
    let s = B.as_seq h (B.gsub p from (to `U32.sub` from)) in
    assert (s == Seq.create (U32.v to - U32.v from) (G.hide true));
    assert (Seq.index s 0 == G.hide true);
    assert (s == Seq.create (U32.v to - U32.v from) (G.hide false));
    assert (Seq.index s 0 == G.hide false);
    assert False
  in
  Classical.move_requires f ()

let unreadable_gsub h #t #b p offset length from to = ()

let unreadable_split h #t #b p from mid to =
  Seq.lemma_split (B.as_seq h (B.gsub b from (to `U32.sub` from))) (U32.v mid - U32.v from);
  if F.model then Seq.lemma_split (B.as_seq h (B.gsub (p <: perm' b) from (to `U32.sub` from))) (U32.v mid - U32.v from)

let unreadable_empty h #t #b p i = ()

let unreadable_frame h #t #b p from to l h' = ()

let drop #t #b p from to =
  if F.model then B.fill (B.sub (p <: perm' b) from (to `U32.sub` from)) (G.hide false) (to `U32.sub` from) else ()

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

let readable_split_1
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (readable h p from to))
  (ensures (readable h p from mid /\ readable h p mid to))
= if F.model then begin
    let s_from_to = B.as_seq h (B.gsub (p <: perm' b) from (to `U32.sub` from)) in
    let s_from_mid = B.as_seq h (B.gsub (p <: perm' b) from (mid `U32.sub` from)) in
    let s_mid_to = B.as_seq h (B.gsub (p <: perm' b) mid (to `U32.sub` mid)) in

    assert (forall (i:nat). i < Seq.length s_from_to ==> Seq.index s_from_to i == G.hide true);

    assert (forall (i:nat). i < Seq.length s_from_mid ==> Seq.index s_from_mid i == G.hide true);
    assert (readable h p from mid);

    assert (forall (i:nat). i < Seq.length s_mid_to ==> Seq.index s_mid_to i == Seq.index s_from_to (i+ U32.v mid-U32.v from));
    assert (forall (i:nat). i < Seq.length s_mid_to ==> Seq.index s_mid_to i == G.hide true);
    assert (readable h p mid to)
  end

#push-options "--fuel 17" // "--using_facts_from '*,-LowParse.Low.Base.serializer32_of_leaf_writer_strong_constant_size'"
#restart-solver

let readable_split_2
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (readable h p from mid /\ readable h p mid to))
  (ensures (readable h p from to))
=
  Seq.lemma_split (B.as_seq h (B.gsub b from (to `U32.sub` from))) (U32.v mid - U32.v from);
  if F.model then Seq.lemma_split (B.as_seq h (B.gsub (p <: perm' b) from (to `U32.sub` from))) (U32.v mid - U32.v from)

#pop-options
#restart-solver

let readable_split h #t #b p from mid to =
  Classical.move_requires (readable_split_1 h p from mid) to;
  Classical.move_requires (readable_split_2 h p from mid) to

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

#push-options "--warn_error -271"
let unreadable_split_1
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (unreadable h p from to))
  (ensures (unreadable h p from mid /\ unreadable h p mid to))
=
  let aux (#a:Type) (s:Seq.seq a) (from to mid:nat) (x:a)
    : Lemma
        (requires
          from <= mid /\ mid <= to /\ to <= Seq.length s /\
          Seq.equal (Seq.slice s from to) (Seq.create (to - from) x))
        (ensures Seq.equal (Seq.slice s from mid)
                           (Seq.create (mid - from) x) /\
                 Seq.equal (Seq.slice s mid to)
                           (Seq.create (to - mid) x))
        [SMTPat ()]
    = 
    let aux0 (#a:Type) (s:Seq.seq a) (from:nat) (to:nat{from <= to /\ to <= Seq.length s})
        (i:nat{from <= i /\ i < to})
        : Lemma (Seq.index (Seq.slice s from to) (i - from) == Seq.index s i)
                [SMTPat ()]
        = Seq.lemma_index_slice s from to (i - from) in
      assert (forall (i:nat). (from <= i /\ i < to) ==> Seq.index (Seq.slice s from to) (i - from) == x);
      assert (forall (i:nat). (from <= i /\ i < to) ==> Seq.index s i == x) in
  ()
#pop-options

let unreadable_split_2
  (h: HS.mem)
  (#t: _) (#b: B.buffer t) (p: perm b)
  (from: U32.t)
  (mid: U32.t)
  (to: U32.t { U32.v from <= U32.v mid /\ U32.v mid <= U32.v to /\ U32.v to <= B.length b })
: Lemma
  (requires (unreadable h p from mid /\ unreadable h p mid to))
  (ensures (unreadable h p from to))
= Seq.lemma_split (B.as_seq h (B.gsub b from (to `U32.sub` from))) (U32.v mid - U32.v from);
  if F.model then Seq.lemma_split (B.as_seq h (B.gsub (p <: perm' b) from (to `U32.sub` from))) (U32.v mid - U32.v from)

let unreadable_split h #t #b p from mid to =
  Classical.move_requires (unreadable_split_1 h p from mid) to;
  Classical.move_requires (unreadable_split_2 h p from mid) to

let unreadable_empty h #t #b p i = ()

let unreadable_frame h #t #b p from to l h' = ()

let drop #t #b p from to =
  if F.model then B.fill (B.sub (p <: perm' b) from (to `U32.sub` from)) (G.hide false) (to `U32.sub` from) else ()

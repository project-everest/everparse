module EverParse3d.Readable

let perm0 t = B.pointer (Ghost.erased (Seq.seq bool))

let perm_prop p b = B.loc_disjoint (B.loc_buffer b) (B.loc_buffer p) /\ True

let loc_perm p = B.loc_buffer p

let loc_perm_prop p = ()

let valid_perm h #_ #b p =
  B.live h b /\
  B.live h p /\
  Seq.length (B.deref h p) == B.length b

let valid_perm_prop h p = ()

let preserved #_ #b p from to h h' =
  (valid_perm h p /\ U32.v from <= U32.v to /\ U32.v to <= B.length b) ==>
  (valid_perm h' p /\ Seq.slice (B.deref h' p) (U32.v from) (U32.v to) `Seq.equal` Seq.slice (B.deref h p) (U32.v from) (U32.v to))

let valid_perm_frame h p l h' = ()

let preserved_refl p from to h = ()

let preserved_trans p from to h1 h2 h3 = ()

let preserved_split p from mid to h h' =
  let s = B.deref h p in
  let s' = B.deref h' p in
  let prf () : Lemma
    (requires (valid_perm h p /\ valid_perm h' p))
    (ensures (preserved p from to h h' <==> (preserved p from mid h h' /\ preserved p mid to h h')))
  =
  assert (Seq.slice s' (U32.v from) (U32.v to) `Seq.equal` (Seq.slice s' (U32.v from) (U32.v mid) `Seq.append` Seq.slice s' (U32.v mid) (U32.v to)));
  assert (Seq.slice s (U32.v from) (U32.v to) `Seq.equal` (Seq.slice s (U32.v from) (U32.v mid) `Seq.append` Seq.slice s (U32.v mid) (U32.v to)));
  assert (Seq.slice s' (U32.v from) (U32.v mid) `Seq.equal` Seq.slice (Seq.slice s' (U32.v from) (U32.v to)) 0 (U32.v mid - U32.v from));
  assert (Seq.slice s' (U32.v mid) (U32.v to) `Seq.equal` Seq.slice (Seq.slice s' (U32.v from) (U32.v to)) (U32.v mid - U32.v from) (U32.v to - U32.v from))
  in
  Classical.move_requires prf ()

let readable h p from to =
  valid_perm h p /\
  Seq.slice (B.deref h p) (U32.v from) (U32.v to) `Seq.equal` Seq.create (U32.v to - U32.v from) true

let readable_prop h p from to = ()

let readable_split h p from mid to =
  let s = B.deref h p in
  let prf () : Lemma
    (requires (valid_perm h p))
    (ensures (readable h p from to <==> (readable h p from mid /\ readable h p mid to)))
  =
  assert (Seq.slice s (U32.v from) (U32.v to) `Seq.equal` (Seq.slice s (U32.v from) (U32.v mid) `Seq.append` Seq.slice s (U32.v mid) (U32.v to)));
  assert (Seq.slice s (U32.v from) (U32.v mid) `Seq.equal` Seq.slice (Seq.slice s (U32.v from) (U32.v to)) 0 (U32.v mid - U32.v from));
  assert (Seq.slice s (U32.v mid) (U32.v to) `Seq.equal` Seq.slice (Seq.slice s (U32.v from) (U32.v to)) (U32.v mid - U32.v from) (U32.v to - U32.v from));
  assert (Seq.create (U32.v to - U32.v from) true `Seq.equal` (Seq.create (U32.v mid - U32.v from) true `Seq.append` Seq.create (U32.v to - U32.v mid) true))
  in
  Classical.move_requires prf ()

let readable_frame0 h p from to h' = ()

let unreadable h p from to =
  valid_perm h p ==>
  (Seq.slice (B.deref h p) (U32.v from) (U32.v to) `Seq.equal` Seq.create (U32.v to - U32.v from) false)

let unreadable_prop h p from to = ()

let readable_not_unreadable h p from to =
  assert (~ (Seq.index (Seq.create (U32.v to - U32.v from) true) 0 == Seq.index (Seq.create (U32.v to - U32.v from) false) 0))

let unreadable_split h p from mid to =
  let s = B.deref h p in
  let prf () : Lemma
    (requires (valid_perm h p))
    (ensures (unreadable h p from to <==> (unreadable h p from mid /\ unreadable h p mid to)))
  =
  assert (Seq.slice s (U32.v from) (U32.v to) `Seq.equal` (Seq.slice s (U32.v from) (U32.v mid) `Seq.append` Seq.slice s (U32.v mid) (U32.v to)));
  assert (Seq.slice s (U32.v from) (U32.v mid) `Seq.equal` Seq.slice (Seq.slice s (U32.v from) (U32.v to)) 0 (U32.v mid - U32.v from));
  assert (Seq.slice s (U32.v mid) (U32.v to) `Seq.equal` Seq.slice (Seq.slice s (U32.v from) (U32.v to)) (U32.v mid - U32.v from) (U32.v to - U32.v from));
  assert (Seq.create (U32.v to - U32.v from) false `Seq.equal` (Seq.create (U32.v mid - U32.v from) false `Seq.append` Seq.create (U32.v to - U32.v mid) false))
  in
  Classical.move_requires prf ()

let unreadable_empty h p i = ()

let unreadable_frame0 h p from to h' = ()

let unreadable_frame h p from to l h' = ()

let drop p from to =
  let open LowStar.BufferOps in
  let r = !* p in
  p *= Ghost.hide (
    Seq.slice r 0 (U32.v from) `Seq.append`
    Seq.create (U32.v to - U32.v from) false `Seq.append`
    Seq.slice r (U32.v to) (Seq.length r)
  )

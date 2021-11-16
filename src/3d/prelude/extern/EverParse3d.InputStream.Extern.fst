module EverParse3d.InputStream.Extern

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module LPE = EverParse3d.ErrorCode

module Aux = EverParse3d.InputStream.Extern.Type

inline_for_extraction
noextract
let t = Aux.input_buffer

let len_all
  (x: t)
: GTot LPE.pos_t
= if x.Aux.has_length
  then x.Aux.length
  else Aux.len_all x.Aux.base

unfold
let live
  (x: t)
  (m: HS.mem)
: Tot prop
= let read = U64.v (B.deref m x.Aux.position) in
  Aux.live x.Aux.base m /\
  B.live m x.Aux.position /\
  read <= U64.v (len_all x) /\
  read == Seq.length (Aux.get_read x.Aux.base m)

let footprint
  (x: t)
: Ghost B.loc
  (requires True)
  (ensures (fun y -> B.address_liveness_insensitive_locs `B.loc_includes` y))
= Aux.footprint x.Aux.base `B.loc_union` B.loc_buffer x.Aux.position

let perm_footprint
  (x: t)
: Ghost B.loc
  (requires True)
  (ensures (fun y -> footprint x `B.loc_includes` y))
= footprint x

let live_not_unused_in
    (x: t)
    (h: HS.mem)
:   Lemma
    (requires (live x h))
    (ensures (B.loc_not_unused_in h `B.loc_includes` footprint x))
= Aux.live_not_unused_in x.Aux.base h

let get_all (x: t) : Ghost (Seq.seq U8.t)
    (requires True)
    (ensures (fun y -> Seq.length y == U64.v (len_all x)))
= Seq.slice (Aux.get_all x.Aux.base) 0 (U64.v (len_all x))

let get_remaining (x: t) (h: HS.mem) : Ghost (Seq.seq U8.t)
    (requires (live x h))
    (ensures (fun y -> Seq.length y <= U64.v (len_all x)))
= let r = U64.v (B.deref h x.Aux.position) in
  Seq.slice (get_all x) r (U64.v (len_all x))

let get_read (x: t) (h: HS.mem) : Ghost (Seq.seq U8.t)
    (requires (live x h))
    (ensures (fun y -> get_all x `Seq.equal` (y `Seq.append` get_remaining x h)))
= Aux.get_read x.Aux.base h

let preserved
    (x: t)
    (l: B.loc)
    (h: HS.mem)
    (h' : HS.mem)
:   Lemma
    (requires (live x h /\ B.modifies l h h' /\ B.loc_disjoint (footprint x) l))
    (ensures (
      live x h' /\
      get_remaining x h' == get_remaining x h /\
      get_read x h' == get_read x h
    ))
=
  Aux.preserved x.Aux.base l h h'

open LowStar.BufferOps

inline_for_extraction
noextract
let has
    (x: t)
    (_: unit)
    (position: LPE.pos_t)
    (n: U64.t)
:   HST.Stack bool
    (requires (fun h ->
      live x h /\
      U64.v position == Seq.length (get_read x h)
    ))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      (res == true <==> Seq.length (get_remaining x h) >= U64.v n)
    ))
=
  if x.Aux.has_length
  then
    n `U64.lte` (x.Aux.length `U64.sub` position)
  else
    Aux.has x.Aux.base n

#push-options "--z3rlimit 64"
#restart-solver
inline_for_extraction
noextract
let read0
    (x: t)
    (position: LPE.pos_t)
    (n: U64.t)
    (dst: B.buffer U8.t)
:   HST.Stack (B.buffer U8.t)
    (requires (fun h ->
      live x h /\
      B.live h dst /\
      B.loc_disjoint (footprint x) (B.loc_buffer dst) /\
      U64.v position == Seq.length (get_read x h) /\
      B.length dst == U64.v n /\
      Seq.length (get_remaining x h) >= U64.v n
    ))
    (ensures (fun h dst' h' ->
      let s = get_remaining x h in
      B.modifies (B.loc_buffer dst `B.loc_union` perm_footprint x) h h' /\
      B.as_seq h' dst' `Seq.equal` Seq.slice s 0 (U64.v n) /\
      live x h' /\
      B.live h' dst /\
      B.live h' dst' /\
      (B.loc_buffer dst `B.loc_union` footprint x) `B.loc_includes` B.loc_buffer dst' /\
      get_remaining x h' `Seq.equal` Seq.slice s (U64.v n) (Seq.length s)
    ))
= let dst = Aux.read x.Aux.base n dst in
  let h1 = HST.get () in
  x.Aux.position *= Ghost.hide (position `U64.add` n);
  let h2 = HST.get () in
  Aux.preserved x.Aux.base (B.loc_buffer x.Aux.position) h1 h2;
  dst

module LP = LowParse.Low.Base

#restart-solver
inline_for_extraction
noextract
let read
    (t': Type0)
    (k: LP.parser_kind)
    (p: LP.parser k t')
    (r: LP.leaf_reader p)
    (x: t)
    (pos: LPE.pos_t)
    (n: U64.t)
:   HST.Stack t'
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h) /\
      k.LP.parser_kind_subkind == Some LP.ParserStrong /\
      k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
      k.LP.parser_kind_low == U64.v n /\
      U64.v n > 0 /\
      U64.v n < 4294967296 /\
      Some? (LP.parse p (get_remaining x h))
    ))
    (ensures (fun h dst' h' ->
      let s = get_remaining x h in
      B.modifies (perm_footprint x) h h' /\
      Seq.length s >= U64.v n /\
      LP.parse p (Seq.slice s 0 (U64.v n)) == Some (dst', U64.v n) /\
      LP.parse p s == Some (dst', U64.v n) /\
      live x h' /\
      get_remaining x h' `Seq.equal` Seq.slice s (U64.v n) (Seq.length s)
    ))
=
  let h0 = HST.get () in
  HST.push_frame ();
  [@inline_let]
  let n32 = LP.uint64_to_uint32 n in
  let dst = B.alloca 0uy n32 in
  let h1 = HST.get () in
  preserved x B.loc_none h0 h1;
  live_not_unused_in x h0;
  LP.parser_kind_prop_equiv k p;
  let dst' = read0 x pos n dst in
  let h2 = HST.get () in
  assert (Seq.length (B.as_seq h2 dst') == U64.v n);
  [@inline_let]
  let sl = LP.make_slice dst' n32 in
  LP.parse_strong_prefix p (get_remaining x h1) (B.as_seq h2 dst');
  LP.valid_facts p h2 sl 0ul;
  let res = r sl 0ul in
  let h3 = HST.get () in
  preserved x B.loc_none h2 h3;
  HST.pop_frame ();
  let h4 = HST.get () in
  preserved x (B.loc_region_only false (HS.get_tip h1)) h3 h4;
  res

#pop-options

inline_for_extraction
noextract
let skip
    (x: t)
    (position: LPE.pos_t)
    (n: U64.t)
:   HST.Stack unit
    (requires (fun h ->
      live x h /\
      U64.v position == Seq.length (get_read x h) /\
      Seq.length (get_remaining x h) >= U64.v n
    ))
    (ensures (fun h _ h' ->
      let s = get_remaining x h in
      B.modifies (perm_footprint x) h h' /\
      live x h' /\
      get_remaining x h' `Seq.equal` Seq.slice s (U64.v n) (Seq.length s)
    ))
= Aux.skip x.Aux.base n;
  let h1 = HST.get () in
  x.Aux.position *= Ghost.hide (position `U64.add` n);
  let h2 = HST.get () in
  Aux.preserved x.Aux.base (B.loc_buffer x.Aux.position) h1 h2

inline_for_extraction
noextract
let skip_if_success
    (x: t)
    (pos: LPE.pos_t)
    (res: U64.t)
:   HST.Stack unit
    (requires (fun h ->
      live x h /\
      (LPE.is_success res ==> (
        U64.v pos == Seq.length (get_read x h)) /\
        U64.v res >= U64.v pos /\
        U64.v pos + Seq.length (get_remaining x h) >= U64.v res
    )))
    (ensures (fun h _ h' ->
      let s = get_remaining x h in
      B.modifies (perm_footprint x) h h' /\
      live x h' /\
      get_remaining x h' == (if LPE.is_success res then Seq.slice s (U64.v res - U64.v pos) (Seq.length s) else get_remaining x h)
    ))
= if LPE.is_success res
  then skip x pos (res `U64.sub` pos)

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let empty
    (x: t)
    (_: unit)
    (position: LPE.pos_t)
:   HST.Stack LPE.pos_t
    (requires (fun h ->
      live x h /\
      U64.v position == Seq.length (get_read x h)
    ))
    (ensures (fun h res h' ->
      B.modifies (perm_footprint x) h h' /\
      live x h' /\
      U64.v res == Seq.length (get_read x h') /\
      get_remaining x h' `Seq.equal` Seq.empty
    ))
=
  if x.Aux.has_length
  then begin
    let h0 = HST.get () in
    let h1 = HST.get () in
    Aux.preserved x.Aux.base (B.loc_buffer x.Aux.position) h0 h1;
    Aux.skip x.Aux.base (x.Aux.length `U64.sub` position);
    let h2 = HST.get () in
    x.Aux.position *= x.Aux.length;
    let h3 = HST.get () in
    Aux.preserved x.Aux.base (B.loc_buffer x.Aux.position) h2 h3;
    x.Aux.length
  end else begin
    let skipped = Aux.empty x.Aux.base in
    let h2 = HST.get () in
    x.Aux.position *= position `U64.add` skipped;
    let h3 = HST.get () in
    Aux.preserved x.Aux.base (B.loc_buffer x.Aux.position) h2 h3;
    position `U64.add` skipped
  end

#pop-options

let is_prefix_of
    (x: t)
    (y: t)
:   Tot prop
= x.Aux.base == y.Aux.base /\
  x.Aux.position == y.Aux.position /\
  (y.Aux.has_length == true ==>
    (x.Aux.has_length == true /\
    U64.v x.Aux.length <= U64.v y.Aux.length))

let get_suffix
    (x: t)
    (y: t)
:   Ghost (Seq.seq U8.t)
    (requires (x `is_prefix_of` y))
    (ensures (fun _ -> True))
= Seq.slice (get_all y) (U64.v (len_all x)) (U64.v (len_all y))

#push-options "--z3rlimit 32"
#restart-solver
let is_prefix_of_prop
    (x: t)
    (y: t)
    (h: HS.mem)
:   Lemma
    (requires (
      live x h /\
      x `is_prefix_of` y
    ))
    (ensures (
      live y h /\
      get_read y h `Seq.equal` get_read x h /\
      get_remaining y h `Seq.equal` (get_remaining x h `Seq.append` get_suffix x y)
    ))
= ()
#pop-options

inline_for_extraction
noextract
let truncate
    (x: t)
    (pos: LPE.pos_t)
    (n: U64.t)
:   HST.Stack t
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h) /\
      U64.v n <= Seq.length (get_remaining x h)
    ))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      res `is_prefix_of` x /\
      footprint res == footprint x /\
      live res h' /\
      Seq.length (get_remaining res h') == U64.v n
    ))
= {
    Aux.base = x.Aux.base;
    Aux.has_length = true;
    Aux.position = x.Aux.position;
    Aux.length = pos `U64.add` n;
    Aux.prf = ();
  }

inline_for_extraction
noextract
let truncate_len
    (x: t)
    (pos: LPE.pos_t)
    (n: U64.t)
    (res: t)
:   HST.Stack unit
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h) /\
      U64.v n <= Seq.length (get_remaining x h) /\
      res `is_prefix_of` x /\
      footprint res == footprint x /\
      live res h /\
      Seq.length (get_remaining res h) == U64.v n
    ))
    (ensures (fun h res_len h' ->
      B.modifies B.loc_none h h'
    ))
= ()

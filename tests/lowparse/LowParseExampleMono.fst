module LowParseExampleMono
include LowParse.MLow.Base
open LowStar.PrefixFreezableBuffer

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Monotonic.Buffer

let compl
  (t: Type)
  (pos: U32.t)
  (v: t)
  (pos' : U32.t)
  (x: Seq.seq byte)
: GTot Type0
= U32.v pos >= 4 /\
  Seq.length x >= 4 /\ (
  let len = frozen_until x in
  len >= 4 /\ len <= Seq.length x /\
  U32.v pos' <= len
  )

inline_for_extraction
type slice = (s: slice prefix_freezable_preorder prefix_freezable_preorder {
  B.length s.base >= 4 /\
  B.witnessed s.base (frozen_until_at_least 4)
})

inline_for_extraction
let make_slice
  (b: buffer)
  (len: U32.t { U32.v len == B.length b } )
: Tot slice
= ({ base = b; len = len; })

let wvalid_stable
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s: slice)
  (pos: U32.t)
  (gpos' : Ghost.erased U32.t)
  (v' : Ghost.erased t)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    stable_on (wvalid p s (compl t) pos gpos' v') prefix_freezable_preorder
  ))
= let pf (s1 s2: Seq.seq byte) : Lemma
    (requires (wvalid p s (compl t) pos gpos' v' s1 /\ prefix_freezable_preorder s1 s2))
    (ensures (wvalid p s (compl t) pos gpos' v' s1 /\ prefix_freezable_preorder s1 s2 /\ wvalid p s (compl t) pos gpos' v' s2))
  = prefix_freezable_preorder_elim s1 s2;
    parse_strong_prefix p (Seq.slice s1 (U32.v pos) (U32.v s.len)) (Seq.slice s2 (U32.v pos) (U32.v s.len))
  in
  let pf' (s1 s2: Seq.seq byte) : Lemma
    ((wvalid p s (compl t) pos gpos' v' s1 /\ prefix_freezable_preorder s1 s2) ==> wvalid p s (compl t) pos gpos' v' s2)
  = Classical.move_requires (pf s1) s2
  in
  Classical.forall_intro_2 pf'

inline_for_extraction
let irepr
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (s: slice)
= irepr p s (compl t)

let buffer_frozen_until (buf: buffer) (h:HS.mem) : GTot nat =
  frozen_until (B.as_seq h buf)

inline_for_extraction
noextract
let witness_valid
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (s: slice)
  (pos: U32.t)
: HST.Stack (irepr p s)
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid p h s pos /\
    (* conditions on global size header *)
    U32.v pos >= 4 /\ (
    let len = buffer_frozen_until s.base h in
    U32.v (get_valid_pos p h s pos) <= len
  )))
  (ensures (fun h res h' ->
    h' == h /\
    irepr_pos res == pos /\
    valid_content_pos p h s pos (irepr_v res) (irepr_pos' res)
  ))
= let h = HST.get () in
  recall_frozen_until_default s.base;
  wvalid_stable p s pos (Ghost.hide (get_valid_pos p h s pos)) (Ghost.hide (contents p h s pos));
  witness_valid_gen s (compl t) pos

inline_for_extraction
noextract
let recall_valid
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: slice)
  (i: irepr p s)
: HST.Stack unit
  (requires (fun h -> B.recallable s.base \/ live_slice h s))
  (ensures (fun h _ h' ->
    h' == h /\
    live_slice h s /\
    valid_content_pos p h s (irepr_pos i) (irepr_v i) (irepr_pos' i) /\
    U32.v s.len >= 4 /\
    U32.v (irepr_pos i) >= 4 /\
    U32.v (irepr_pos' i) <= buffer_frozen_until s.base h
  ))
= recall_valid_gen i

inline_for_extraction
noextract
let iaccess
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (#g: gaccessor p1 p2 cl)
  ($a: accessor g)
  (#s: slice)
  (i1: irepr p1 s)
: HST.Stack (irepr p2 s)
  (requires (fun h ->
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    cl.clens_cond (irepr_v i1) /\
    (B.recallable s.base \/ live_slice h s)
  ))
  (ensures (fun h i2 h' ->
    B.modifies B.loc_none h h' /\
    valid_content_pos p1 h s (irepr_pos i1) (irepr_v i1) (irepr_pos' i1) /\
    valid_content_pos p2 h s (irepr_pos i2) (irepr_v i2) (irepr_pos' i2) /\
    irepr_pos i2 == slice_access h g s (irepr_pos i1) /\
    irepr_v i2 == cl.clens_get (irepr_v i1)
  ))
= recall_valid i1;
  let x = a s (irepr_pos i1) in
  recall_frozen_until_default s.base;
  witness_valid s x

inline_for_extraction
noextract
let iread
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (r: leaf_reader p)
  (#s: slice)
  (i: irepr p s)
: HST.Stack t
  (requires (fun h -> (B.recallable s.base \/ live_slice h s)))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    valid_content_pos p h s (irepr_pos i) (irepr_v i) (irepr_pos' i) /\
    res == irepr_v i
  ))
= recall_valid i;
  r s (irepr_pos i)

inline_for_extraction
let ijump
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#s: slice)
  (i: irepr p s)
: HST.Stack U32.t
  (requires (fun h -> (B.recallable s.base \/ live_slice h s)))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    valid_content_pos p h s (irepr_pos i) (irepr_v i) (irepr_pos' i) /\
    res == irepr_pos' i
  ))
= recall_valid i;
  j s (irepr_pos i)

let freezable_buffer_writable_intro
  (b: buffer)
  (pos pos' : nat)
  (h: HS.mem)
: Lemma
  (requires (
    let len = buffer_frozen_until b h in
    B.live h b /\
    4 <= len /\
    len <= pos
  ))
  (ensures (writable b pos pos' h))
  [SMTPat (writable b pos pos' h)]
= if pos <= pos' && pos' <= B.length b
  then
    let s = B.as_seq h b in
    let slen = Seq.slice s 0 4 in
    Classical.forall_intro_2 prefix_freezable_preorder_elim;
    writable_intro b pos pos' h () (fun s1 s2 ->
      assert (Seq.slice (Seq.replace_subseq s pos pos' s1) 0 4 `Seq.equal` slen);
      assert (Seq.slice (Seq.replace_subseq s pos pos' s2) 0 4 `Seq.equal` slen)
    )

inline_for_extraction
noextract
let freeze_valid
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sl: slice)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack (irepr p sl)
  (requires (fun h ->
    (B.recallable sl.base \/ live_slice h sl) /\
    buffer_frozen_until sl.base h <= U32.v pos /\
    valid_pos p h sl pos pos' /\
    k.parser_kind_subkind == Some ParserStrong // for valid_exact_ext_intro
  ))
  (ensures (fun h res h' ->
    B.modifies (B.loc_buffer sl.base) h h' /\
    buffer_frozen_until sl.base h' == U32.v pos' /\
    irepr_pos res == pos /\
    irepr_pos' res == pos' /\
    irepr_v res == contents p h sl pos
  ))
=    B.recall_p sl.base (frozen_until_at_least 4); // to recover liveness
     let h1 = HST.get () in
     freeze sl.base pos' ;
     let h2 = HST.get () in
     valid_pos_valid_exact p h1 sl pos pos' ;
     valid_exact_ext_intro p h1 sl pos pos' h2 sl pos pos' ;
     witness_valid sl pos

let frozen_until_frame
  (sl: slice)
  (l: B.loc)
  (h h' : HS.mem)
: Lemma
  (requires (live_slice h sl /\ B.modifies l h h' /\ B.loc_disjoint l (loc_slice_from_to sl 0ul 4ul)))
  (ensures (buffer_frozen_until sl.base h' == buffer_frozen_until sl.base h))
  [SMTPatOr [
    [SMTPat (B.modifies l h h'); SMTPat (buffer_frozen_until sl.base h);];
    [SMTPat (B.modifies l h h'); SMTPat (buffer_frozen_until sl.base h');];
  ]]
= B.modifies_buffer_from_to_elim sl.base 0ul 4ul l h h'

inline_for_extraction
noextract
let iwrite
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_writer_strong s)
  (v: t)
  (sl: slice)
  (pos: U32.t)
: HST.Stack (irepr p sl)
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\ // for valid_exact_ext_intro
    buffer_frozen_until sl.base h <= U32.v pos /\
    U32.v pos + serialized_length s v <= U32.v sl.len /\
    (recallable sl.base \/ live_slice h sl)
  ))
  (ensures (fun h i h' ->
    irepr_v i == v /\
    irepr_pos i == pos /\
    irepr_pos' i == pos `U32.add` U32.uint_to_t (serialized_length s v) /\
    buffer_frozen_until sl.base h' == U32.v (irepr_pos' i) /\
    B.modifies (B.loc_buffer sl.base) h h'
  ))
=    B.recall_p sl.base (frozen_until_at_least 4); // to recover liveness
     let pos' = w v sl pos in
     freeze_valid p sl pos pos'

inline_for_extraction
noextract
let icopy
  (#rrel #rel: B.srel byte)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: LowParse.MLow.Base.slice rrel rel)
  (spos spos' : U32.t)
  (dst: slice)
  (dpos: U32.t)
: HST.Stack (irepr p dst)
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h src spos spos' /\
    U32.v dpos + U32.v spos' - U32.v spos <= U32.v dst.len /\
    B.loc_disjoint (loc_slice_from_to src spos spos') (loc_slice_from_to dst dpos (dpos `U32.add` (spos' `U32.sub` spos))) /\ (
    let len = buffer_frozen_until dst.base h in
    (recallable dst.base \/ live_slice h dst) /\
    len <= U32.v dpos
  )))
  (ensures (fun h i h' ->
    B.modifies (B.loc_buffer dst.base) h h' /\
    irepr_pos i == dpos /\
    irepr_v i == contents p h src spos /\
    buffer_frozen_until dst.base h' == U32.v (irepr_pos' i)
  ))
= B.recall_p dst.base (frozen_until_at_least 4); // to recover liveness
  let dpos' = copy_strong p src spos spos' dst dpos in
  let i = freeze_valid p dst dpos dpos' in
  i

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main _ _ = C.EXIT_SUCCESS

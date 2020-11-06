module LowParse.Low.Base
include LowParse.Low.Base.Spec
include LowParse.Low.ErrorCode

module M = LowParse.Math
module B = LowStar.Monotonic.Buffer
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module Cast = FStar.Int.Cast
module L = FStar.List.Tot

[@unifier_hint_injective]
inline_for_extraction
let accessor
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
: Tot Type
= (#rrel: _) ->
  (#rel: _) ->
  (sl: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos)
  ))
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    pos' == slice_access h g sl pos
  ))

#push-options "--z3rlimit 16"

inline_for_extraction
let make_accessor_from_pure
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  ($g: gaccessor p1 p2 cl)
  (f: (
    (input: Ghost.erased bytes) ->
    Pure U32.t
    (requires (Seq.length (Ghost.reveal input) < 4294967296 /\ gaccessor_pre p1 p2 cl (Ghost.reveal input)))
    (ensures (fun y -> U32.v y == (g (Ghost.reveal input))))
  ))
: Tot (accessor g)
= fun #rrel #rel sl (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ =
    slice_access_eq h g sl pos
  in
  pos `U32.add` f (Ghost.hide (bytes_of_slice_from h sl pos))

#pop-options

inline_for_extraction
let accessor_id
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (accessor (gaccessor_id p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_id p) input pos in
  [@inline_let] let _ = gaccessor_id_eq p (bytes_of_slice_from h input pos) in
  pos

inline_for_extraction
let accessor_ext
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (#g: gaccessor p1 p2 cl)
  (a: accessor g)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
: Tot (accessor (gaccessor_ext g cl' sq))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq h (gaccessor_ext g cl' sq) input pos;
    slice_access_eq h g input pos;
    gaccessor_ext_eq g cl' sq (bytes_of_slice_from h input pos)
  in
  a input pos

#push-options "--z3rlimit 128" // necessary for the .fst
#restart-solver // necessary for the .fst

inline_for_extraction
let accessor_compose
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (#a12: gaccessor p1 p2 cl12)
  (a12' : accessor a12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (#a23: gaccessor p2 p3 cl23)
  (a23' : accessor a23)
  (sq: unit) // squash (k2.parser_kind_subkind == Some ParserStrong))
: Tot (accessor (gaccessor_compose a12 a23))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  let pos2 = a12' input pos in
  let pos3 = a23' input pos2 in
  slice_access_eq h a12 input pos;
  slice_access_eq h a23 input pos2;
  slice_access_eq h (gaccessor_compose a12 a23) input pos;
  gaccessor_compose_eq a12 a23 (bytes_of_slice_from h input pos);
  pos3

#pop-options

(*
inline_for_extraction
let accessor_compose_strong
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (#a12: gaccessor p1 p2 cl12)
  (a12' : accessor a12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (#a23: gaccessor p2 p3 cl23)
  (a23' : accessor a23 { clens_compose_strong_pre cl12 cl23 } )
  (sq: squash (k2.parser_kind_subkind == Some ParserStrong))
: Tot (accessor (gaccessor_compose_strong a12 a23))
= fun #rrel #rel input pos -> 
  let h = HST.get () in
  slice_access_eq h (gaccessor_compose_strong a12 a23) input pos;
  slice_access_eq h (gaccessor_compose a12 a23) input pos;
  accessor_compose a12' a23' () input pos
*)

(* Validators *)

[@unifier_hint_injective]
inline_for_extraction
let validator (#k: parser_kind) (#t: Type) (p: parser k t) : Tot Type =
  (#rrel: _) -> (#rel: _) ->
  (sl: slice rrel rel) ->
  (pos: U64.t) ->
  HST.Stack U64.t
  (requires (fun h -> live_slice h sl /\ U64.v pos <= U32.v sl.len))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    if is_success res
    then
      valid_pos p h sl (uint64_to_uint32 pos) (uint64_to_uint32 res)
    else
      (~ (valid p h sl (uint64_to_uint32 pos)))
  )))

[@unifier_hint_injective]
inline_for_extraction
let validator_no_read (#k: parser_kind) (#t: Type) (p: parser k t) : Tot Type =
  (#rrel: _) -> (#rel: _) ->
  (sl: Ghost.erased (slice rrel rel)) ->
  (len: U32.t { len == (Ghost.reveal sl).len }) ->
  (pos: U64.t) ->
  HST.Stack U64.t
  (requires (fun h -> live_slice h sl /\ U64.v pos <= U32.v sl.len))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    if is_success res
    then
      valid_pos p h sl (uint64_to_uint32 pos) (uint64_to_uint32 res)
    else
      (~ (valid p h sl (uint64_to_uint32 pos)))
  )))

inline_for_extraction
let validate_no_read
  (#k: parser_kind) (#t: Type) (#p: parser k t)
  (v: validator_no_read p)
: Tot (validator p)
= fun #rrel #rel sl pos -> v (Ghost.hide sl) sl.len pos

noextract
inline_for_extraction
let comment (s: string) : HST.Stack unit
  (requires (fun _ -> True))
  (ensures (fun h _ h' -> h == h'))
= LowStar.Comment.comment s

noextract
inline_for_extraction
let validate_with_comment
  (s: string)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
: Tot (validator p)
= fun #rrel #rel sl pos ->
  comment s;
  v sl pos

inline_for_extraction
let validate_with_error_code
  (#k: parser_kind) (#t: Type) (#p: parser k t) (v: validator p) (c: error_code)
: Tot (validator p)
= fun #rrel #rel sl pos ->
  let res = v sl pos in
  maybe_set_error_code res pos c

inline_for_extraction
let validate
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (#rrel: _)
  (#rel: _)
  (b: B.mbuffer byte rrel rel)
  (len: U32.t)
: HST.Stack bool
  (requires (fun h ->
    B.live h b /\
    U32.v len <= B.length b
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    let sl = make_slice b len in
    (res == true <==> (is_success (Cast.uint32_to_uint64 len) /\ valid p h sl 0ul))
  )))
= if is_error (Cast.uint32_to_uint64 len)
  then false
  else
    [@inline_let]
    let sl = make_slice b len in
    is_success (v sl 0uL)

let valid_total_constant_size
  (h: HS.mem)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
    (valid p h input pos <==> (live_slice h input /\ U32.v input.len - U32.v pos >= k.parser_kind_low)) /\
    (valid p h input pos ==> content_length p h input pos == k.parser_kind_low)
  ))
= parser_kind_prop_equiv k p;
  valid_facts p h input pos

inline_for_extraction
let validate_total_constant_size_no_read
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: U64.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U64.v sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  })
: Tot (validator_no_read p)
= fun #rrel #rel (input: Ghost.erased (slice rrel rel)) len pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_total_constant_size h p (U64.v sz) input (uint64_to_uint32 pos) in
  if U64.lt (Cast.uint32_to_uint64 len `U64.sub` pos) sz
  then validator_error_not_enough_data
  else
    (pos `U64.add` sz)

inline_for_extraction
let validate_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: U64.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U64.v sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  })
: Tot (validator p)
= validate_no_read (validate_total_constant_size_no_read p sz u)

inline_for_extraction
let validate_total_constant_size_with_error_code
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: U64.t)
  (c: error_code {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U64.v sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  })
: Tot (validator p)
= fun #rrel #rel (input: slice rrel rel) pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_total_constant_size h p (U64.v sz) input (uint64_to_uint32 pos) in
  if U64.lt (Cast.uint32_to_uint64 input.len `U64.sub` pos) sz
  then set_validator_error_pos_and_code validator_error_not_enough_data pos c
  else
    (pos `U64.add` sz)

let valid_weaken
  (k1: parser_kind)
  (#k2: parser_kind)
  (#t: Type)
  (p2: parser k2 t)
  (h: HS.mem)
  #rrel #rel
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (k1 `is_weaker_than` k2))
  (ensures (
    (valid (weaken k1 p2) h sl pos \/ valid p2 h sl pos) ==> (
    valid p2 h sl pos /\
    valid_content_pos (weaken k1 p2) h sl pos (contents p2 h sl pos) (get_valid_pos p2 h sl pos)
  )))
= valid_facts (weaken k1 p2) h sl pos;
  valid_facts p2 h sl pos

inline_for_extraction
let validate_weaken
  (k1: parser_kind)
  (#k2: parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (v2: validator p2 { k1 `is_weaker_than` k2 } )
: Tot (validator (weaken k1 p2))
= fun #rrel #rel sl pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_weaken k1 p2 h sl (uint64_to_uint32 pos)
  in
  v2 sl pos

[@unifier_hint_injective]
inline_for_extraction
let jumper
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (#rrel: _) -> (#rel: _) ->
  (sl: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> valid p h sl pos))
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + content_length p h sl pos == U32.v pos'
  ))

inline_for_extraction
let jump_constant_size'
  (#k: parser_kind)
  (#t: Type)
  (p: (unit -> GTot (parser k t)))
  (sz: U32.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz
  })
: Tot (jumper (p ()))
= fun #rrel #rel (input: slice rrel rel) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (p ()) h input pos in
  pos `U32.add` sz

inline_for_extraction
let jump_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz
  })
: Tot (jumper p)
= jump_constant_size' (fun _ -> p) sz u

inline_for_extraction
let jump_weaken
  (k1: parser_kind)
  (#k2: parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (v2: jumper p2 { k1 `is_weaker_than` k2 } )
: Tot (jumper (weaken k1 p2))
= fun #rrel #rel sl pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_weaken k1 p2 h sl pos
  in
  v2 sl pos

let seq_starts_with (#t: Type) (slong sshort: Seq.seq t) : GTot Type0 =
  Seq.length sshort <= Seq.length slong /\
  Seq.slice slong 0 (Seq.length sshort) `Seq.equal` sshort

let seq_starts_with_trans (#t: Type) (s1 s2 s3: Seq.seq t) : Lemma
  (requires (s1 `seq_starts_with` s2 /\ s2 `seq_starts_with` s3))
  (ensures (s1 `seq_starts_with` s3))
= ()

let seq_starts_with_append_l_intro (#t: Type) (s1 s2: Seq.seq t) : Lemma
  ((s1 `Seq.append` s2) `seq_starts_with` s1)
= ()

let seq_starts_with_append_r_elim (#t: Type) (s s1 s2: Seq.seq t) : Lemma
  (requires (s `seq_starts_with` (s1 `Seq.append` s2)))
  (ensures (
    s `seq_starts_with` s1 /\
    Seq.slice s (Seq.length s1) (Seq.length s) `seq_starts_with` s2
  ))
  [SMTPat (s `seq_starts_with` (s1 `Seq.append` s2))]
= let s3 = Seq.slice s (Seq.length s1 + Seq.length s2) (Seq.length s) in
  assert (s `Seq.equal` (s1 `Seq.append` s2 `Seq.append` s3))

inline_for_extraction
noextract
let jump_serializer
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: jumper p)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
  (x: Ghost.erased t)
: HST.Stack U32.t
  (requires (fun h ->
    let sq = serialize s (Ghost.reveal x) in
    live_slice h sl /\
    U32.v pos <= U32.v sl.len /\
    bytes_of_slice_from h sl pos `seq_starts_with` sq
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + Seq.length (serialize s (Ghost.reveal x)) == U32.v res
  ))
= let h = HST.get () in
  let gsq = Ghost.hide (serialize s (Ghost.reveal x)) in
  let glen = Ghost.hide (Seq.length (Ghost.reveal gsq)) in
  let gpos' = Ghost.hide (pos `U32.add` U32.uint_to_t (Ghost.reveal glen)) in
  assert (bytes_of_slice_from_to h sl pos (Ghost.reveal gpos') == Seq.slice (bytes_of_slice_from h sl pos) 0 (Seq.length (serialize s (Ghost.reveal x))));
  serialize_valid_exact s h sl (Ghost.reveal x) pos (Ghost.reveal gpos');
  valid_exact_valid p h sl pos (Ghost.reveal gpos');
  j sl pos

[@unifier_hint_injective]
inline_for_extraction
let leaf_reader
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (#rrel: _) -> (#rel: _) ->
  (sl: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack t
  (requires (fun h -> valid p h sl pos))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == contents p h sl pos
  ))

noextract
inline_for_extraction
let read_with_comment
  (s: string)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (r: leaf_reader p)
: Tot (leaf_reader p)
= fun #rrel #rel sl pos ->
    comment s;
    r sl pos

[@unifier_hint_injective]
inline_for_extraction
let leaf_reader_ext
  (#k1: parser_kind)
  (#t: Type)
  (#p1: parser k1 t)
  (p32: leaf_reader p1)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (lem: (
    (x: bytes) ->
    Lemma
    (parse p2 x == parse p1 x)
  ))
: Tot (leaf_reader p2)
= fun #rrel #rel sl pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts p1 h sl pos;
    valid_facts p2 h sl pos;
    lem (bytes_of_slice_from h sl pos)
  in
  p32 sl pos

let writable
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (h: HS.mem)
: GTot Type0
= let s = B.as_seq h b in
  B.live h b /\
  ((pos <= pos' /\ pos' <= B.length b) ==> (
    (forall (s1:Seq.lseq t (pos' - pos)) . {:pattern (Seq.replace_subseq s pos pos' s1)}
      forall (s2:Seq.lseq t (pos' - pos)) . {:pattern (Seq.replace_subseq s pos pos' s2)}
      Seq.replace_subseq s pos pos' s1 `rel` Seq.replace_subseq s pos pos' s2
  )))

let writable_intro
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (h: HS.mem)
  (_: squash (B.live h b /\ pos <= pos' /\ pos' <= B.length b))
  (f: (
    (s1: Seq.lseq t (pos' - pos)) ->
    (s2: Seq.lseq t (pos' - pos)) ->
    Lemma
    (let s = B.as_seq h b in
      Seq.replace_subseq s pos pos' s1 `rel` Seq.replace_subseq s pos pos' s2)
  ))
: Lemma
  (writable b pos pos' h)
= Classical.forall_intro_2 f

#push-options "--z3rlimit 32"

let writable_weaken
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (h: HS.mem)
  (lpos lpos' : nat)
: Lemma
  (requires (writable b pos pos' h /\ pos <= lpos /\ lpos <= lpos' /\ lpos' <= pos' /\ pos' <= B.length b))
  (ensures (writable b lpos lpos' h))
= writable_intro b lpos lpos' h () (fun s1 s2 ->
    let s = B.as_seq h b in
    let sl = Seq.slice s pos pos'  in
    let j1 = Seq.replace_subseq s pos pos' (Seq.replace_subseq sl (lpos - pos) (lpos' - pos) s1) in
    let j2 = Seq.replace_subseq s pos pos' (Seq.replace_subseq sl (lpos - pos) (lpos' - pos) s2) in
    assert (Seq.replace_subseq s lpos lpos' s1 `Seq.equal` j1);
    assert (Seq.replace_subseq s lpos lpos' s2 `Seq.equal` j2);
    assert (j1 `rel` j2)
  )

#pop-options

let writable_replace_subseq_elim
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (h: HS.mem)
  (sl' : Seq.seq t)
: Lemma
  (requires (
    writable b pos pos' h /\
    pos <= pos' /\
    pos' <= B.length b /\
    Seq.length sl' == pos' - pos
  ))
  (ensures (
    let s = B.as_seq h b in
    let s' = Seq.replace_subseq s pos pos' sl' in
    s `rel` s'
  ))
= let s = B.as_seq h b in
  let sl = Seq.slice s pos pos' in
  assert (s `Seq.equal` Seq.replace_subseq s pos pos' sl)

let writable_replace_subseq
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (h: HS.mem)
  (sl' : Seq.seq t)
  (h' : HS.mem)
: Lemma
  (requires (
    writable b pos pos' h /\
    pos <= pos' /\
    pos' <= B.length b /\
    Seq.length sl' == pos' - pos /\
    B.as_seq h' b `Seq.equal` Seq.replace_subseq (B.as_seq h b) pos pos' sl' /\
    B.live h' b
  ))
  (ensures (
    let s = B.as_seq h b in
    let s' = Seq.replace_subseq s pos pos' sl' in
    s `rel` s' /\
    writable b pos pos' h'
  ))
= let s = B.as_seq h b in
  let s' = Seq.replace_subseq s pos pos' sl' in
  let sl = Seq.slice s pos pos' in
  assert (s `Seq.equal` Seq.replace_subseq s pos pos' sl);
  assert (s' `Seq.equal` Seq.replace_subseq s pos pos' sl');
  writable_intro b pos pos' h' () (fun s1 s2 ->
    assert (Seq.replace_subseq s' pos pos' s1 `Seq.equal` Seq.replace_subseq s pos pos' s1);
    assert (Seq.replace_subseq s' pos pos' s2 `Seq.equal` Seq.replace_subseq s pos pos' s2)
  ) 

let writable_ext
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (h: HS.mem)
  (h' : HS.mem)
: Lemma
  (requires (
    writable b pos pos' h /\
    pos <= pos' /\
    pos' <= B.length b /\
    B.as_seq h' b `Seq.equal` B.as_seq h b /\
    B.live h' b
  ))
  (ensures (
    writable b pos pos' h'
  ))
= writable_replace_subseq b pos pos' h (Seq.slice (B.as_seq h b) pos pos') h'

let writable_upd_seq
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (sl' : Seq.seq t)
  (h: HS.mem)
: Lemma
  (requires (writable b pos pos' h /\ pos <= pos' /\ pos' <= B.length b /\ Seq.length sl' == pos' - pos))
  (ensures (
    let s = B.as_seq h b in
    let s' = Seq.replace_subseq s pos pos' sl' in
    s `rel` s' /\
    writable b pos pos' (B.g_upd_seq b s' h)
  ))
= let s = B.as_seq h b in
  let s' = Seq.replace_subseq s pos pos' sl' in
  let h' = B.g_upd_seq b s' h in
  B.g_upd_seq_as_seq b s' h; // for live
  writable_replace_subseq b pos pos' h sl' h'

let writable_upd
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (h: HS.mem)
  (i: nat)
  (v: t)
: Lemma
  (requires (writable b pos pos' h /\ pos <= i /\ i < pos' /\ pos' <= B.length b))
  (ensures (
    let s = B.as_seq h b in
    s `rel` Seq.upd s i v /\
    writable b pos pos' (B.g_upd b i v h)
  ))
= let s = B.as_seq h b in
  let sl' = Seq.upd (Seq.slice s pos pos') (i - pos) v in
  writable_upd_seq b pos pos' sl' h;
  assert (Seq.upd s i v `Seq.equal` Seq.replace_subseq s pos pos' sl')

let writable_modifies
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : nat)
  (h: HS.mem)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    writable b pos pos' h /\
    pos <= pos' /\ pos' <= B.length b /\
    B.modifies (l `B.loc_union` B.loc_buffer_from_to b (U32.uint_to_t pos) (U32.uint_to_t pos')) h h' /\
    B.loc_disjoint l (B.loc_buffer b)
  ))
  (ensures (
    writable b pos pos' h'
  ))
= B.modifies_buffer_from_to_elim b 0ul (U32.uint_to_t pos) (l `B.loc_union` B.loc_buffer_from_to b (U32.uint_to_t pos) (U32.uint_to_t pos')) h h';
  B.modifies_buffer_from_to_elim b (U32.uint_to_t pos') (B.len b) (l `B.loc_union` B.loc_buffer_from_to b (U32.uint_to_t pos) (U32.uint_to_t pos')) h h';
  writable_replace_subseq b pos pos' h (Seq.slice (B.as_seq h' b) pos pos') h'

inline_for_extraction
noextract
let mbuffer_upd
  (#t: Type)
  (#rrel #rel: _)
  (b: B.mbuffer t rrel rel)
  (pos pos' : Ghost.erased nat)
  (i: U32.t)
  (v: t)
: HST.Stack unit
  (requires (fun h ->
    writable b (Ghost.reveal pos) (Ghost.reveal pos') h /\
    Ghost.reveal pos <= U32.v i /\
    U32.v i + 1 <= Ghost.reveal pos' /\
    Ghost.reveal pos' <= B.length b
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer_from_to b i (i `U32.add` 1ul)) h h' /\
    writable b (Ghost.reveal pos) (Ghost.reveal pos') h' /\
    B.as_seq h' b == Seq.upd (B.as_seq h b) (U32.v i) v
  ))
= let h = HST.get () in
  writable_upd b (Ghost.reveal pos) (Ghost.reveal pos') h (U32.v i) v;
  B.g_upd_modifies_strong b (U32.v i) v h;
  B.g_upd_seq_as_seq b (Seq.upd (B.as_seq h b) (U32.v i) v) h;
  B.upd' b i v

[@unifier_hint_injective]
inline_for_extraction
let leaf_writer_weak
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (#rrel: _) -> (#rel: _) ->
  (sl: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    live_slice h sl /\
    U32.v pos <= U32.v sl.len /\
    U32.v sl.len < U32.v max_uint32 /\
    writable sl.base (U32.v pos) (U32.v sl.len) h
  ))
  (ensures (fun h pos' h' ->
    B.modifies (loc_slice_from sl pos) h h' /\ (
    if pos' = max_uint32
    then U32.v pos + serialized_length s x > U32.v sl.len
    else valid_content_pos p h' sl pos x pos'
  )))

[@unifier_hint_injective]
inline_for_extraction
let leaf_writer_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (#rrel: _) -> (#rel: _) ->
  (sl: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    let sq = B.as_seq h sl.base in
    let len = serialized_length s x in
    live_slice h sl /\
    U32.v pos + len <= U32.v sl.len /\
    writable sl.base (U32.v pos) (U32.v pos + len) h
  ))
  (ensures (fun h pos' h' ->
    B.modifies (loc_slice_from_to sl pos pos') h h' /\
    valid_content_pos p h' sl pos x pos'
  ))

[@unifier_hint_injective]
inline_for_extraction
let serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (#rrel: _) -> (#rel: _) ->
  (b: B.mbuffer byte rrel rel) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    let len = Seq.length (serialize s x) in
    let sq = B.as_seq h b in
    B.live h b /\
    U32.v pos + len <= B.length b /\
    writable b (U32.v pos) (U32.v pos + len) h
  ))
  (ensures (fun h len h' ->
    Seq.length (serialize s x) == U32.v len /\ (
    B.modifies (B.loc_buffer_from_to b pos (pos `U32.add` len)) h h' /\
    B.live h b /\
    Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + U32.v len) `Seq.equal` serialize s x
  )))

inline_for_extraction
let serialize32_ext
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (s1': serializer32 s1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (u: squash (t1 == t2 /\ (forall (input: bytes) . parse p1 input == parse p2 input)))
: Tot (serializer32 (serialize_ext p1 s1 p2))
= fun x #rrel #rel b pos -> s1' x b pos

inline_for_extraction
let frame_serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (x: t)
  (#rrel: _)
  (#rel: _)
  (b: B.mbuffer byte rrel rel)
  (posl: Ghost.erased U32.t)
  (posr: Ghost.erased U32.t)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    let len = Seq.length (serialize s x) in
    let sq = B.as_seq h b in
    B.live h b /\
    U32.v (Ghost.reveal posl) <= U32.v pos /\
    U32.v pos + len <= U32.v (Ghost.reveal posr) /\
    U32.v (Ghost.reveal posr) <= B.length b /\
    writable b (U32.v (Ghost.reveal posl)) (U32.v (Ghost.reveal posr)) h
  ))
  (ensures (fun h len h' ->
    Seq.length (serialize s x) == U32.v len /\ (
    B.modifies (B.loc_buffer_from_to b (Ghost.reveal posl) (Ghost.reveal posr)) h h' /\
    B.live h b /\
    Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + U32.v len) `Seq.equal` serialize s x /\
    writable b (U32.v (Ghost.reveal posl)) (U32.v (Ghost.reveal posr)) h' /\
    Seq.slice (B.as_seq h' b) (U32.v (Ghost.reveal posl)) (U32.v pos) `Seq.equal` Seq.slice (B.as_seq h b) (U32.v (Ghost.reveal posl)) (U32.v pos) /\
    Seq.slice (B.as_seq h' b) (U32.v pos + U32.v len) (U32.v (Ghost.reveal posr)) `Seq.equal` Seq.slice (B.as_seq h b) (U32.v pos + U32.v len) (U32.v (Ghost.reveal posr))
  )))
=
  let h0 = HST.get () in
  writable_weaken b (U32.v (Ghost.reveal posl)) (U32.v (Ghost.reveal posr)) h0 (U32.v pos) (U32.v pos + Seq.length (serialize s x));
  let res = s32 x b pos in
  let h1 = HST.get () in
  let pos' = pos `U32.add` res in
  B.loc_includes_loc_buffer_from_to b (Ghost.reveal posl) (Ghost.reveal posr) pos pos';
  writable_modifies b (U32.v (Ghost.reveal posl)) (U32.v (Ghost.reveal posr)) h0 B.loc_none h1;
  B.loc_includes_loc_buffer_from_to b (Ghost.reveal posl) (Ghost.reveal posr) (Ghost.reveal posl) pos;
  B.loc_disjoint_loc_buffer_from_to b (Ghost.reveal posl) pos pos pos';
  B.modifies_buffer_from_to_elim b (Ghost.reveal posl) pos (B.loc_buffer_from_to b pos pos') h0 h1;
  B.loc_includes_loc_buffer_from_to b (Ghost.reveal posl) (Ghost.reveal posr) pos' (Ghost.reveal posr);
  B.loc_disjoint_loc_buffer_from_to b pos pos' pos' (Ghost.reveal posr);
  B.modifies_buffer_from_to_elim b pos' (Ghost.reveal posr) (B.loc_buffer_from_to b pos pos') h0 h1;
  res

inline_for_extraction
let leaf_writer_strong_of_serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (u: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (leaf_writer_strong s)
= fun x #rrel #rel input pos ->
  serialized_length_eq s x;
  let h0 = HST.get () in
  let len = s32 x input.base pos in
  [@inline_let]
  let pos' = pos `U32.add` len in
  let h = HST.get () in
  [@inline_let] let _ =
    let large = bytes_of_slice_from h input pos in
    let small = bytes_of_slice_from_to h input pos pos' in
    parse_strong_prefix p small large;
    valid_facts p h input pos
  in
  pos'

inline_for_extraction
let leaf_writer_weak_of_strong_constant_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: leaf_writer_strong s)
  (sz: U32.t)
  (u: squash (
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz /\
    k.parser_kind_low < U32.v max_uint32
  ))
: Tot (leaf_writer_weak s)
= fun x #rrel #rel input pos ->
  if (input.len `U32.sub` pos) `U32.lt` sz
  then max_uint32
  else begin
    let h = HST.get () in
    writable_weaken input.base (U32.v pos) (U32.v input.len) h (U32.v pos) (U32.v pos + U32.v sz);
    s32 x input pos
  end

inline_for_extraction
let serializer32_of_leaf_writer_strong_constant_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: leaf_writer_strong s)
  (sz: U32.t)
  (u: squash (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz
  ))
: Tot (serializer32 s)
= fun x #rrel #rel b pos ->
  serialized_length_eq s x;
  let h0 = HST.get () in
  let pos' = s32 x (make_slice b (pos `U32.add` sz)) pos in
  [@inline_let]
  let len = pos' `U32.sub` pos in
  let h = HST.get () in
  [@inline_let] let _ =
    valid_valid_exact p h (make_slice b (pos `U32.add` sz)) pos;
    valid_exact_serialize s h (make_slice b (pos `U32.add` sz)) pos pos'
  in
  len

inline_for_extraction
let blit_strong
  (#a:Type) (#rrel1 #rrel2 #rel1 #rel2: _)
  (src: B.mbuffer a rrel1 rel1)
  (idx_src:U32.t)
  (dst: B.mbuffer a rrel2 rel2)
  (idx_dst:U32.t)
  (len:U32.t)
: HST.Stack unit
  (requires (fun h ->
    B.live h src /\ B.live h dst /\
    U32.v idx_src + U32.v len <= B.length src /\
    U32.v idx_dst + U32.v len <= B.length dst /\
    B.loc_disjoint (B.loc_buffer_from_to src idx_src (idx_src `U32.add` len)) (B.loc_buffer_from_to dst idx_dst (idx_dst `U32.add` len)) /\
    rel2 (B.as_seq h dst)
         (Seq.replace_subseq (B.as_seq h dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len)
	   (Seq.slice (B.as_seq h src) (U32.v idx_src) (U32.v idx_src + U32.v len)))))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer_from_to dst idx_dst (idx_dst `U32.add` len)) h h' /\
    B.live h' dst /\
    Seq.slice (B.as_seq h' dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len) ==
    Seq.slice (B.as_seq h src) (U32.v idx_src) (U32.v idx_src + U32.v len)
  ))
= let h = HST.get () in
  B.blit src idx_src dst idx_dst len;
  let h' = HST.get () in
  B.modifies_loc_buffer_from_to_intro dst idx_dst (idx_dst `U32.add` len) B.loc_none h h'

#push-options "--z3rlimit 16"

inline_for_extraction
let copy_strong
  (#rrel1 #rrel2 #rel1 #rel2: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: slice rrel1 rel1) // FIXME: length is useless here
  (spos spos' : U32.t)
  (dst: slice rrel2 rel2)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h src spos spos' /\
    U32.v dpos + U32.v spos' - U32.v spos <= U32.v dst.len /\
    live_slice h dst /\
    writable dst.base (U32.v dpos) (U32.v dpos + (U32.v spos' - U32.v spos)) h /\
    B.loc_disjoint (loc_slice_from_to src spos spos') (loc_slice_from_to dst dpos (dpos `U32.add` (spos' `U32.sub` spos)))
  ))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from_to dst dpos dpos') h h' /\
    valid_content_pos p h' dst dpos (contents p h src spos) dpos' /\
    dpos' `U32.sub` dpos == spos' `U32.sub` spos
  ))
= let h0 = HST.get () in
  let len = spos' `U32.sub` spos in
  valid_facts p h0 src spos;
  writable_replace_subseq_elim dst.base (U32.v dpos) (U32.v dpos + (U32.v spos' - U32.v spos)) h0 (Seq.slice (B.as_seq h0 src.base) (U32.v spos) (U32.v spos'));
  blit_strong src.base spos dst.base dpos len;
  let h = HST.get () in
  [@inline_let] let dpos' = dpos `U32.add` len in
  parse_strong_prefix p (bytes_of_slice_from h0 src spos) (bytes_of_slice_from h dst dpos);
  valid_facts p h dst dpos;
  dpos'

#pop-options

inline_for_extraction
let copy_strong'
  (#rrel1 #rrel2 #rel1 #rel2: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (src: slice rrel1 rel1) // FIXME: length is useless here
  (spos : U32.t)
  (dst: slice rrel2 rel2)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid p h src spos /\ (
    let clen = content_length p h src spos in
    U32.v dpos + clen <= U32.v dst.len /\
    live_slice h dst /\
    writable dst.base (U32.v dpos) (U32.v dpos + clen) h /\
    B.loc_disjoint (loc_slice_from src spos) (loc_slice_from_to dst dpos (dpos `U32.add` (U32.uint_to_t clen)))
  )))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from_to dst dpos dpos') h h' /\
    valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  ))
= let spos' = j src spos in
  copy_strong p src spos spos' dst dpos

inline_for_extraction
let copy_weak_with_length
  (#rrel1 #rrel2 #rel1 #rel2: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: slice rrel1 rel1) // FIXME: length is useless here
  (spos spos' : U32.t)
  (dst: slice rrel2 rel2)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h src spos spos' /\
    live_slice h dst /\
    U32.v dpos <= U32.v dst.len /\
    U32.v dst.len < U32.v max_uint32 /\
    writable dst.base (U32.v dpos) (U32.v dpos + (U32.v spos' - U32.v spos)) h /\
    B.loc_disjoint (loc_slice_from_to src spos spos') (loc_slice_from dst dpos)
  ))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from dst dpos) h h' /\ (
    if dpos' = max_uint32
    then
      U32.v dpos + content_length p h src spos > U32.v dst.len
    else
      valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  )))
= if (dst.len `U32.sub` dpos) `U32.lt` (spos' `U32.sub` spos)
  then max_uint32
  else copy_strong p src spos spos' dst dpos

inline_for_extraction
let copy_weak
  (#rrel1 #rrel2 #rel1 #rel2: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (jmp: jumper p)
  (src: slice rrel1 rel1)
  (spos : U32.t)
  (dst: slice rrel2 rel2)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid p h src spos /\
    live_slice h dst /\
    U32.v dpos <= U32.v dst.len /\
    U32.v dst.len < U32.v max_uint32 /\
    writable dst.base (U32.v dpos) (U32.v dpos + (content_length p h src spos)) h /\
    B.loc_disjoint (loc_slice_from_to src spos (get_valid_pos p h src spos)) (loc_slice_from dst dpos)
  ))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from dst dpos) h h' /\ (
    if dpos' = max_uint32
    then
      U32.v dpos + content_length p h src spos > U32.v dst.len
    else
      valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  )))
= let spos' = jmp src spos in
  copy_weak_with_length p src spos spos' dst dpos


(* fold_left on lists *)

module BF = LowStar.Buffer

#push-options "--z3rlimit 256 --fuel 1 --ifuel 1"
#restart-solver
inline_for_extraction
let list_fold_left_gen
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (j: jumper p)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
  (h0: HS.mem)
  (l: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal l) (loc_slice_from_to sl pos pos') } )
  (inv: (HS.mem -> list t -> list t -> U32.t -> GTot Type0))
  (inv_frame: (h: HS.mem) -> (l1: list t) -> (l2: list t) -> (pos1: U32.t) -> (h' : HS.mem) -> Lemma (requires (
    B.modifies (B.loc_unused_in h0) h h' /\
    inv h l1 l2 pos1
  )) (ensures (inv h' l1 l2 pos1)))
  (post_interrupt: ((h: HS.mem) -> GTot Type0))
  (post_interrupt_frame: (h: HS.mem) -> (h' : HS.mem) -> Lemma (requires (
    B.modifies (B.loc_unused_in h0) h h' /\
    post_interrupt h
  )) (ensures (post_interrupt h')))
  (body: (
    (pos1: U32.t) ->
    (pos2: U32.t) ->
    HST.Stack bool
    (requires (fun h ->
      B.modifies (Ghost.reveal l) h0 h /\
      valid_list p h0 sl pos pos1 /\
      valid_pos p h0 sl pos1 pos2 /\
      valid_list p h0 sl pos2 pos' /\
      inv h (contents_list p h0 sl pos pos1) (contents p h0 sl pos1 :: contents_list p h0 sl pos2 pos') pos1
    ))
    (ensures (fun h ctinue h' ->
      B.modifies (Ghost.reveal l) h h' /\
      (if ctinue then inv h' (contents_list p h0 sl pos pos1 `L.append` [contents p h0 sl pos1]) (contents_list p h0 sl pos2 pos') pos2 else post_interrupt h')
    ))
  ))
: HST.Stack bool
  (requires (fun h ->
    h == h0 /\
    valid_list p h sl pos pos' /\
    inv h [] (contents_list p h sl pos pos') pos
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal l) h h' /\
    (if res then inv h' (contents_list p h sl pos pos') [] pos' else post_interrupt h')
  ))
= HST.push_frame ();
  let h1 = HST.get () in
//  B.fresh_frame_modifies h0 h1;
  let bpos : BF.pointer U32.t = BF.alloca pos 1ul in
  let bctinue : BF.pointer bool = BF.alloca true 1ul in
  let btest: BF.pointer bool = BF.alloca (pos `U32.lt` pos') 1ul in
  let h2 = HST.get () in
  assert (B.modifies B.loc_none h0 h2);
  let test_pre (h: HS.mem) : GTot Type0 =
    B.live h bpos /\ B.live h bctinue /\ B.live h btest /\ (
    let pos1 = Seq.index (B.as_seq h bpos) 0 in
    let ctinue = Seq.index (B.as_seq h bctinue) 0 in
    valid_list p h0 sl pos pos1 /\
    valid_list p h0 sl pos1 pos' /\
    B.modifies (Ghost.reveal l `B.loc_union` B.loc_region_only true (HS.get_tip h1)) h2 h /\
    Seq.index (B.as_seq h btest) 0 == ((U32.v (Seq.index (B.as_seq h bpos) 0) < U32.v pos') && Seq.index (B.as_seq h bctinue) 0) /\
    (if ctinue then inv h (contents_list p h0 sl pos pos1) (contents_list p h0 sl pos1 pos') pos1 else post_interrupt h)
  )
  in
  let test_post (cond: bool) (h: HS.mem) : GTot Type0 =
    test_pre h /\
    cond == Seq.index (B.as_seq h btest) 0
  in
  valid_list_nil p h0 sl pos;
  inv_frame h0 [] (contents_list p h0 sl pos pos') pos h1;
  inv_frame h1 [] (contents_list p h0 sl pos pos') pos h2;
  [@inline_let]
  let while_body () : HST.Stack unit
    (requires (fun h -> test_post true h))
    (ensures (fun _ _ h1 -> test_pre h1))
  =
      let h51 = HST.get () in
      let pos1 = B.index bpos 0ul in
      valid_list_cons_recip p h0 sl pos1 pos';
      //assert (B.modifies (Ghost.reveal l `B.loc_union` B.loc_buffer bpos) h0 h51);
      //assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos'));
      //assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos pos1));
      valid_list_cons_recip p h51 sl pos1 pos';
      let pos2 = j sl pos1 in
      let h52 = HST.get () in
      inv_frame h51 (contents_list p h0 sl pos pos1) (contents_list p h0 sl pos1 pos') pos1 h52;
      B.modifies_only_not_unused_in (Ghost.reveal l) h0 h52;
      let ctinue = body pos1 pos2 in
      let h53 = HST.get () in
      //assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos2));
      //assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos2 pos'));
      B.loc_regions_unused_in h0 (Set.singleton (HS.get_tip h1));
      valid_pos_frame_strong p h0 sl pos1 pos2 (Ghost.reveal l) h53;
      valid_list_snoc p h0 sl pos pos1;
      B.upd bpos 0ul pos2;
      B.upd bctinue 0ul ctinue;
      B.upd btest 0ul ((pos2 `U32.lt` pos') && ctinue);
      let h54 = HST.get () in
      [@inline_let]
      let _ =
        if ctinue
        then inv_frame h53 (contents_list p h0 sl pos pos2) (contents_list p h0 sl pos2 pos') pos2 h54
        else post_interrupt_frame h53 h54
      in
      ()
  in
  C.Loops.while
    #test_pre
    #test_post
    (fun (_: unit) -> (
      B.index btest 0ul) <: HST.Stack bool (requires (fun h -> test_pre h)) (ensures (fun h x h1 -> test_post x h1)))
    while_body
    ;
  valid_list_nil p h0 sl pos';
  let res = B.index bctinue 0ul in
  let h3 = HST.get () in
  HST.pop_frame ();
  let h4 = HST.get () in
  //B.popped_modifies h3 h4;
  B.loc_regions_unused_in h0 (Set.singleton (HS.get_tip h3));
  [@inline_let]
  let _ =
    if res
    then inv_frame h3 (contents_list p h0 sl pos pos') [] pos' h4
    else post_interrupt_frame h3 h4
  in
  res
#pop-options

  //B.loc_includes_union_l (B.loc_all_regions_from false (HS.get_tip h1)) (Ghost.reveal l) (Ghost.reveal l)
  //B.modifies_fresh_frame_popped h0 h1 (Ghost.reveal l) h3 h4

module G = FStar.Ghost

inline_for_extraction
let list_fold_left
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (j: jumper p)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
  (h0: HS.mem)
  (l: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal l) (loc_slice_from_to sl pos pos') } )
  (inv: (HS.mem -> list t -> list t -> U32.t -> GTot Type0))
  (inv_frame: (h: HS.mem) -> (l1: list t) -> (l2: list t) -> (pos1: U32.t) -> (h' : HS.mem) -> Lemma (requires (
    B.modifies (B.loc_unused_in h0) h h' /\
    inv h l1 l2 pos1
  )) (ensures (inv h' l1 l2 pos1)))
  (body: (
    (pos1: U32.t) ->
    (pos2: U32.t) ->
    (l1: Ghost.erased (list t)) ->
    (x: Ghost.erased t) ->
    (l2: Ghost.erased (list t)) ->
    HST.Stack unit
    (requires (fun h ->
      B.modifies (Ghost.reveal l) h0 h /\
      valid_list p h0 sl pos pos' /\
      valid_content_pos p h0 sl pos1 (G.reveal x) pos2 /\
      U32.v pos <= U32.v pos1 /\ U32.v pos2 <= U32.v pos' /\
      B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos2) /\
      inv h (Ghost.reveal l1) (Ghost.reveal x :: Ghost.reveal l2) pos1 /\
      contents_list p h0 sl pos pos' == Ghost.reveal l1 `L.append` (Ghost.reveal x :: Ghost.reveal l2)
    ))
    (ensures (fun h _ h' ->
      B.modifies (Ghost.reveal l) h h' /\
      inv h' (Ghost.reveal l1 `L.append` [contents p h0 sl pos1]) (Ghost.reveal l2) pos2
    ))
  ))
: HST.Stack unit
  (requires (fun h ->
    h == h0 /\
    valid_list p h sl pos pos' /\
    inv h [] (contents_list p h sl pos pos') pos
  ))
  (ensures (fun h _ h' ->
    B.modifies (Ghost.reveal l) h h' /\
    inv h' (contents_list p h sl pos pos') [] pos'
  ))
= let _ = list_fold_left_gen
    p
    j
    sl
    pos pos'
    h0
    l
    inv
    inv_frame
    (fun _ -> False)
    (fun _ _ -> ())
    (fun pos1 pos2 ->
      let h = HST.get () in
      valid_list_cons p h sl pos1 pos';
      valid_list_append p h sl pos pos1 pos';
      body
        pos1
        pos2
        (Ghost.hide (contents_list p h sl pos pos1))
        (Ghost.hide (contents p h sl pos1))
        (Ghost.hide (contents_list p h sl pos2 pos'))
        ;
      true
    )
  in
  ()

inline_for_extraction
let list_length
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (j: jumper p)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid_list p h sl pos pos'
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v res == L.length (contents_list p h sl pos pos')
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  B.fresh_frame_modifies h0 h1;
  let blen : BF.pointer U32.t = BF.alloca 0ul 1ul in
  let h2 = HST.get () in
  list_fold_left
    p
    j
    sl
    pos
    pos'
    h2
    (Ghost.hide (B.loc_buffer blen))
    (fun h l1 l2 pos1 ->
      B.modifies (B.loc_buffer blen) h2 h /\
      B.live h blen /\ (
      let len = U32.v (Seq.index (B.as_seq h blen) 0) in
      len <= U32.v pos1 /\ // necessary to prove that length computations do not overflow
      len == L.length l1
    ))
    (fun h l1 l2 pos1 h' ->
      B.modifies_only_not_unused_in (B.loc_buffer blen) h2 h';
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun pos1 pos2 l1 x l2 ->
      B.upd blen 0ul (B.index blen 0ul `U32.add` 1ul);
      Classical.forall_intro_2 (list_length_append #t)
    )
    ;
  let len = B.index blen 0ul in
  HST.pop_frame ();
  len

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1"

inline_for_extraction
let list_filter
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (j: jumper p)
  (f: (t -> Tot bool))
  (f' : (
    (#rrel: _) ->
    (#rel: _) ->
    (sl: slice rrel rel) ->
    (pos: U32.t) ->
    (x: Ghost.erased t) ->
    HST.Stack bool
    (requires (fun h -> valid_content p h sl pos (G.reveal x)))
    (ensures (fun h res h' -> B.modifies B.loc_none h h' /\ res == f (G.reveal x)))
  ))
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
  (#rrel_out #rel_out: _)
  (sl_out : slice rrel_out rel_out)
  (pos_out : U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v pos_out + U32.v pos' - U32.v pos <= U32.v sl_out.len /\
    valid_list p h sl pos pos' /\
    B.loc_disjoint (loc_slice_from_to sl pos pos') (loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))) /\
    writable sl_out.base (U32.v pos_out) (U32.v pos_out + (U32.v pos' - U32.v pos)) h /\
    live_slice h sl_out
  ))
  (ensures (fun h pos_out' h' ->
    B.modifies (loc_slice_from_to sl_out pos_out pos_out') h h' /\
    U32.v pos_out' - U32.v pos_out <= U32.v pos' - U32.v pos /\
    valid_list p h' sl_out pos_out pos_out' /\
    contents_list p h' sl_out pos_out pos_out' == L.filter f (contents_list p h sl pos pos')
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  //B.fresh_frame_modifies h0 h1;
  let bpos_out' : BF.pointer U32.t = BF.alloca pos_out 1ul in
  let h2 = HST.get () in
  let inv (h: HS.mem) (l1 l2: list t) (pos1: U32.t) : GTot Type0 =
    B.live h bpos_out' /\ (
      let pos_out' = Seq.index (B.as_seq h bpos_out') 0 in
      B.modifies (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out pos_out') h2 h /\
      writable sl_out.base (U32.v pos_out) (U32.v pos_out + (U32.v pos' - U32.v pos)) h /\
      valid_list p h sl_out pos_out pos_out' /\
      contents_list p h sl_out pos_out pos_out' == L.filter f l1 /\
      U32.v pos_out' - U32.v pos1 <= U32.v pos_out - U32.v pos // necessary to prove that length computations do not overflow
    )
  in
  valid_list_nil p h2 sl_out pos_out;
  list_fold_left
    p
    j
    sl
    pos
    pos'
    h2
    (Ghost.hide (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))))
    inv
    (fun h l1 l2 pos1 h' ->
      let pos_out' = Seq.index (B.as_seq h bpos_out') 0 in
      B.modifies_only_not_unused_in (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out pos_out') h2 h';
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun pos1 pos2 l1 x l2 ->
      let pos_out1 = B.index bpos_out' 0ul in
      list_filter_append f (G.reveal l1) [G.reveal x];
      if f' sl pos1 x
      then begin
        assert (B.loc_includes (loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))) (loc_slice_from_to sl_out pos_out1 (pos_out1 `U32.add` (pos2 `U32.sub` pos1))));
        let h = HST.get () in
        writable_weaken sl_out.base (U32.v pos_out) (U32.v pos_out + (U32.v pos' - U32.v pos)) h (U32.v pos_out1) (U32.v pos_out1 + (U32.v pos2 - U32.v pos1));
        let pos_out2 = copy_strong p sl pos1 pos2 sl_out pos_out1 in
        B.upd bpos_out' 0ul pos_out2;
        let h' = HST.get () in
        writable_modifies sl_out.base (U32.v pos_out) (U32.v pos_out + (U32.v pos' - U32.v pos)) h (B.loc_region_only true (HS.get_tip h1)) h';
        valid_list_nil p h' sl_out pos_out2;
        valid_list_cons p h' sl_out pos_out1 pos_out2;
        valid_list_append p h' sl_out pos_out pos_out1 pos_out2
      end else
        L.append_l_nil (L.filter f (G.reveal l1))
    )
    ;
  let pos_out' = B.index bpos_out' 0ul in
  HST.pop_frame ();
  pos_out'

#pop-options


#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
inline_for_extraction
let list_nth
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (j: jumper p)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
  (i: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid_list p h sl pos pos' /\
    U32.v i < L.length (contents_list p h sl pos pos')
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    valid_list p h sl pos res /\
    valid p h sl res /\
    valid_list p h sl (get_valid_pos p h sl res) pos' /\
    L.length (contents_list p h sl pos res) == U32.v i /\
    contents p h sl res == L.index (contents_list p h sl pos pos') (U32.v i)
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let bpos1 = BF.alloca pos 1ul in
  let bk = BF.alloca 0ul 1ul in
  let h2 = HST.get () in
  valid_list_nil p h0 sl pos;
  let _ : bool = list_fold_left_gen
    p
    j
    sl
    pos pos'
    h2
    (Ghost.hide (B.loc_region_only true (HS.get_tip h1)))
    (fun h l1 l2 pos1 ->
      let k = Seq.index (B.as_seq h bk) 0 in
      B.modifies (B.loc_region_only true (HS.get_tip h1)) h2 h /\
      B.live h bpos1 /\
      B.live h bk /\
      valid_list p h0 sl pos pos1 /\
      valid_list p h0 sl pos1 pos' /\
      L.length (contents_list p h0 sl pos pos1) == U32.v k /\
      U32.v k <= U32.v i
    )
    (fun h _ _ _ h' ->
//      assert (B.loc_not_unused_in h2 `B.loc_includes` B.loc_buffer bpos1);
//      assert (B.loc_not_unused_in h2 `B.loc_includes` B.loc_buffer bk);
      B.loc_unused_in_not_unused_in_disjoint h2;
      B.modifies_only_not_unused_in (B.loc_region_only true (HS.get_tip h1)) h2 h'
    )
    (fun h ->
      let pos1 = Seq.index (B.as_seq h bpos1) 0 in
      B.live h bpos1 /\
      valid p h0 sl pos1 /\
      valid_list p h0 sl pos pos1 /\
      valid_list p h0 sl (get_valid_pos p h0 sl pos1) pos' /\
      L.length (contents_list p h0 sl pos pos1) == U32.v i /\
      contents p h0 sl pos1 == L.index (contents_list p h0 sl pos pos') (U32.v i)
    )
    (fun _ _ -> 
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun pos1 pos2 ->
      let k = B.index bk 0ul in
      if k = i
      then begin
        B.upd bpos1 0ul pos1;
        valid_list_cons_recip p h0 sl pos1 pos';
        list_index_append (contents_list p h0 sl pos pos1) (contents_list p h0 sl pos1 pos') (U32.v i);
        valid_list_append p h0 sl pos pos1 pos' ;
        assert (contents p h0 sl pos1 == L.index (contents_list p h0 sl pos pos') (U32.v i));
        false
      end else begin
        B.upd bk 0ul (k `U32.add` 1ul);
        let h = HST.get () in
        B.modifies_only_not_unused_in B.loc_none h0 h;
        valid_list_snoc p h0 sl pos pos1;
        assert (valid p h0 sl pos1);
        assert (pos2 == get_valid_pos p h0 sl pos1);
        assert (valid_list p h0 sl pos pos2);
        list_length_append (contents_list p h0 sl pos pos1) [contents p h0 sl pos1];
        true
      end
    )
  in
  let res = B.index bpos1 0ul in
  HST.pop_frame ();
  res

inline_for_extraction
let list_find
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (f: (t -> Tot bool)) // should be GTot, but List.find requires Tot
  (f' : (
    (#rrel: _) ->
    (#rel: _) ->
    (sl: slice rrel rel) ->
    (pos: U32.t) ->
    HST.Stack bool
    (requires (fun h ->
      valid p h sl pos
    ))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      res == f (contents p h sl pos)
    ))
  ))
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
: HST.Stack U32.t
  (requires (fun h -> valid_list p h sl pos pos'))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    let l = contents_list p h sl pos pos' in
    if res = pos'
    then L.find f l == None
    else
      U32.v pos <= U32.v res /\
      valid p h sl res /\ (
        let x = contents p h sl res in
        U32.v res + content_length p h sl res <= U32.v pos' /\
        f x == true /\
        L.find f l == Some x
      )
  )))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let bres = BF.alloca 0ul 1ul in
  let h2 = HST.get () in
  let not_found = list_fold_left_gen
    p
    j
    sl
    pos pos'
    h2
    (Ghost.hide (B.loc_region_only true (HS.get_tip h1)))
    (fun h l1 l2 pos1 ->
      B.modifies (B.loc_region_only true (HS.get_tip h1)) h2 h /\
      B.live h bres /\
      valid_list p h0 sl pos1 pos' /\
      l2 == contents_list p h0 sl pos1 pos' /\
      L.find f (contents_list p h0 sl pos pos') == L.find f l2
    )
    (fun h _ _ _ h' ->
      B.loc_unused_in_not_unused_in_disjoint h2;
      B.modifies_only_not_unused_in (B.loc_region_only true (HS.get_tip h1)) h2 h'
    )
    (fun h ->
      B.modifies (B.loc_region_only true (HS.get_tip h1)) h2 h /\
      B.live h bres /\ (
      let res = Seq.index (B.as_seq h bres) 0 in
      U32.v pos <= U32.v res /\
      valid p h0 sl res /\ (
        let x = contents p h0 sl res in
        U32.v res + content_length p h0 sl res <= U32.v pos' /\
        f x == true /\
        L.find f (contents_list p h0 sl pos pos') == Some x
    )))
    (fun h h' ->
      B.loc_unused_in_not_unused_in_disjoint h2;
      B.modifies_only_not_unused_in (B.loc_region_only true (HS.get_tip h1)) h2 h'
    )
    (fun pos1 pos2 ->
      if f' sl pos1
      then begin
        B.upd bres 0ul pos1;
        false
      end
      else true
    )
  in
  let res =
    if not_found
    then pos'
    else B.index bres 0ul
  in
  HST.pop_frame ();
  res
#pop-options

let rec list_existsb_find
  (#a: Type)
  (f: (a -> Tot bool))
  (l: list a)
: Lemma
  (L.existsb f l == Some? (L.find f l))
= match l with
  | [] -> ()
  | x :: q ->
    if f x
    then ()
    else list_existsb_find f q

inline_for_extraction
noextract
let list_existsb
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (f: (t -> Tot bool)) // should be GTot, but List.find requires Tot
  (f' : (
    (#rrel: _) ->
    (#rel: _) ->
    (sl: slice rrel rel) ->
    (pos: U32.t) ->
    HST.Stack bool
    (requires (fun h ->
      valid p h sl pos
    ))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      res == f (contents p h sl pos)
    ))
  ))
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
: HST.Stack bool
  (requires (fun h -> valid_list p h sl pos pos'))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == L.existsb f (contents_list p h sl pos pos')
  ))
= let h = HST.get () in
  list_existsb_find f (contents_list p h sl pos pos');
  let posn = list_find j f f' sl pos pos' in
  posn <> pos'

#push-options "--fuel 2 --ifuel 0 --z3rlimit 64"
inline_for_extraction
noextract
let list_flatten_map
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2 { k2.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_low > 0 } )
  (f: (t1 -> Tot (list t2))) // should be GTot, but List.Tot.map requires Tot
  (h0: HS.mem)
  (#rrel1 #rel1: _)
  (sl1: slice rrel1 rel1)
  (pos1 pos1' : U32.t)
  (#rrel2 #rel2: _)
  (sl2: slice rrel2 rel2)
  (pos2: U32.t {
    valid_list p1 h0 sl1 pos1 pos1' /\
    U32.v pos1 <= U32.v pos1' /\
    U32.v pos1' <= U32.v sl1.len /\
    U32.v pos2 <= U32.v sl2.len /\
    B.loc_disjoint (loc_slice_from_to sl1 pos1 pos1') (loc_slice_from sl2 pos2) /\
    U32.v sl2.len < U32.v max_uint32
  })
  (f' : (
    (pos1_: U32.t) ->
    (pos2_: U32.t) ->
    HST.Stack U32.t
    (requires (fun h ->
      B.modifies (loc_slice_from sl2 pos2) h0 h /\
      valid p1 h0 sl1 pos1_ /\
      U32.v pos1 <= U32.v pos1_ /\
      U32.v pos1_ + content_length p1 h0 sl1 pos1_ <= U32.v pos1' /\
      live_slice h sl2 /\
      U32.v pos2 <= U32.v pos2_ /\
      U32.v pos2_ <= U32.v sl2.len /\
      writable sl2.base (U32.v pos2) (U32.v sl2.len) h
    ))
    (ensures (fun h res h' ->
      B.modifies (loc_slice_from sl2 pos2_) h h' /\ (
      let y = f (contents p1 h0 sl1 pos1_) in
      if res = max_uint32
      then U32.v pos2_ + serialized_list_length s2 y > U32.v sl2.len
      else
        valid_list p2 h' sl2 pos2_ res /\
        contents_list p2 h' sl2 pos2_ res == y
    )))
  ))
: HST.Stack U32.t
  (requires (fun h ->
    B.modifies (loc_slice_from sl2 pos2) h0 h /\
    live_slice h sl2 /\
    writable sl2.base (U32.v pos2) (U32.v sl2.len) h
  ))
  (ensures (fun h res h' ->
    B.modifies (loc_slice_from sl2 pos2) h h' /\ (
    let y = List.Tot.flatten (List.Tot.map f (contents_list p1 h0 sl1 pos1 pos1')) in
    if res = max_uint32
    then U32.v pos2 + serialized_list_length s2 y > U32.v sl2.len
    else
      valid_list p2 h' sl2 pos2 res /\
      contents_list p2 h' sl2 pos2 res == y
  )))
= let hz = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let bpos2_ = BF.alloca pos2 1ul in
  let h2 = HST.get () in
  valid_list_nil p2 hz sl2 pos2;
  let fits = list_fold_left_gen
    p1
    j1
    sl1
    pos1 pos1'
    h2
    (Ghost.hide (B.loc_region_only true (HS.get_tip h1) `B.loc_union` loc_slice_from sl2 pos2))
    (fun h ll lr _ ->
      B.modifies (B.loc_region_only true (HS.get_tip h1) `B.loc_union` loc_slice_from sl2 pos2) h2 h /\
      B.live h bpos2_ /\ (
      let pos2_ = Seq.index (B.as_seq h bpos2_) 0 in
      contents_list p1 h0 sl1 pos1 pos1' == ll `List.Tot.append` lr /\
      valid_list p2 h sl2 pos2 pos2_ /\
      contents_list p2 h sl2 pos2 pos2_ == List.Tot.flatten (List.Tot.map f ll) /\
      writable sl2.base (U32.v pos2) (U32.v sl2.len) h
    ))
    (fun h _ _ _ h' ->
      B.modifies_only_not_unused_in (B.loc_region_only true (HS.get_tip h1) `B.loc_union` loc_slice_from sl2 pos2) h2 h';
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun h ->
      B.modifies (B.loc_region_only true (HS.get_tip h1) `B.loc_union` loc_slice_from sl2 pos2) h2 h /\
      U32.v pos2 + serialized_list_length s2 (List.Tot.flatten (List.Tot.map f (contents_list p1 h0 sl1 pos1 pos1'))) > U32.v sl2.len
    )
    (fun h h' -> 
      B.modifies_only_not_unused_in (B.loc_region_only true (HS.get_tip h1) `B.loc_union` loc_slice_from sl2 pos2) h2 h';
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun pos1l pos1r ->
      let pos2_ = B.index bpos2_ 0ul in
      let h = HST.get () in
      writable_weaken sl2.base (U32.v pos2) (U32.v sl2.len) h (U32.v pos2_) (U32.v sl2.len);
      valid_pos_frame_strong p1 h0 sl1 pos1l pos1r (loc_slice_from sl2 pos2) hz;
      let res = f' pos1l pos2_ in
      let fits = not (res = max_uint32) in
      if fits then begin
        B.upd bpos2_ 0ul res;
        let h' = HST.get () in
        writable_modifies sl2.base (U32.v pos2) (U32.v sl2.len) h (B.loc_region_only true (HS.get_tip h1)) h' ;
        List.Tot.append_assoc (contents_list p1 h0 sl1 pos1 pos1l) [contents p1 h0 sl1 pos1l] (contents_list p1 h0 sl1 pos1r pos1');
        list_flatten_map_append f (contents_list p1 h0 sl1 pos1 pos1l) [contents p1 h0 sl1 pos1l];
        valid_list_snoc p1 h0 sl1 pos1 pos1l;
        valid_list_append p2 h' sl2 pos2 pos2_ res;
        valid_list_nil p2 h' sl2 res;
        valid_list_append p2 h' sl2 pos2_ res res
      end else begin
        let h' = HST.get () in
        valid_list_cons p1 h0 sl1 pos1l pos1' ;
        valid_list_append p1 h0 sl1 pos1 pos1l pos1' ;
        list_flatten_map_append f (contents_list p1 h0 sl1 pos1 pos1l) (contents_list p1 h0 sl1 pos1l pos1');
        serialized_list_length_append s2 (L.flatten (L.map f (contents_list p1 h0 sl1 pos1 pos1l))) (L.flatten (L.map f (contents_list p1 h0 sl1 pos1l pos1')));
        serialized_list_length_append s2 (f (contents p1 h0 sl1 pos1l)) (L.flatten (L.map f (contents_list p1 h0 sl1 pos1r pos1')));
        valid_list_serialized_list_length s2 h' sl2 pos2 pos2_
      end;
      fits
    )
  in
  let res =
    if fits
    then B.index bpos2_ 0ul
    else max_uint32
  in
  HST.pop_frame ();
  res
#pop-options

inline_for_extraction
noextract
let list_map
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2 { k2.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_low > 0 } )
  (f: (t1 -> Tot t2)) // should be GTot, but List.Tot.map requires Tot
  (h0: HS.mem)
  (#rrel1 #rel1: _)
  (sl1: slice rrel1 rel1)
  (pos1 pos1' : U32.t)
  (#rrel2 #rel2: _)
  (sl2: slice rrel2 rel2)
  (pos2: U32.t {
    valid_list p1 h0 sl1 pos1 pos1' /\
    U32.v pos1 <= U32.v pos1' /\
    U32.v pos1' <= U32.v sl1.len /\
    U32.v pos2 <= U32.v sl2.len /\
    B.loc_disjoint (loc_slice_from_to sl1 pos1 pos1') (loc_slice_from sl2 pos2) /\
    U32.v sl2.len < U32.v max_uint32
  })
  (f' : (
    (pos1_: U32.t) ->
    (pos2_: U32.t) ->
    HST.Stack U32.t
    (requires (fun h ->
      B.modifies (loc_slice_from sl2 pos2) h0 h /\
      valid p1 h0 sl1 pos1_ /\
      U32.v pos1 <= U32.v pos1_ /\
      U32.v pos1_ + content_length p1 h0 sl1 pos1_ <= U32.v pos1' /\
      live_slice h sl2 /\
      U32.v pos2 <= U32.v pos2_ /\
      U32.v pos2_ <= U32.v sl2.len /\
      writable sl2.base (U32.v pos2) (U32.v sl2.len) h
    ))
    (ensures (fun h res h' ->
      B.modifies (loc_slice_from sl2 pos2_) h h' /\ (
      let y = f (contents p1 h0 sl1 pos1_) in
      if res = max_uint32
      then U32.v pos2_ + serialized_length s2 y > U32.v sl2.len
      else
        valid_content_pos p2 h' sl2 pos2_ y res
    )))
  ))
: HST.Stack U32.t
  (requires (fun h ->
    B.modifies (loc_slice_from sl2 pos2) h0 h /\
    live_slice h sl2 /\
    writable sl2.base (U32.v pos2) (U32.v sl2.len) h
  ))
  (ensures (fun h res h' ->
    B.modifies (loc_slice_from sl2 pos2) h h' /\ (
    let y = List.Tot.map f (contents_list p1 h0 sl1 pos1 pos1') in
    if res = max_uint32
    then U32.v pos2 + serialized_list_length s2 y > U32.v sl2.len
    else
      valid_list p2 h' sl2 pos2 res /\
      contents_list p2 h' sl2 pos2 res == y
  )))
= list_map_list_flatten_map f (contents_list p1 h0 sl1 pos1 pos1');
  list_flatten_map
    j1
    s2
    (fun x -> [f x])
    h0
    sl1 pos1 pos1'
    sl2 pos2
    (fun pos1 pos2 ->
      let res = f' pos1 pos2 in
      let h = HST.get () in
      if res = max_uint32
      then begin
        serialized_list_length_nil s2;
        serialized_list_length_cons s2 (f (contents p1 h0 sl1 pos1)) []
      end
      else begin
        valid_list_nil p2 h sl2 res;
        valid_list_cons p2 h sl2 pos2 res
      end;
      res
    )

(* Example: trivial printers *)

inline_for_extraction
let print_list
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (print: ((#rrel: _) -> (#rel: _) -> (sl: slice rrel rel) -> (pos: U32.t) -> HST.Stack unit (requires (fun h -> valid p h sl pos)) (ensures (fun h _ h' -> B.modifies B.loc_none h h'))))
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    valid_list p h sl pos pos'
  ))
  (ensures (fun h _ h' ->
    B.modifies B.loc_none h h'
  ))
= let h0 = HST.get () in
  list_fold_left
    p
    j
    sl
    pos pos'
    h0
    (Ghost.hide B.loc_none)
    (fun _ _ _ _ -> True)
    (fun _ _ _ _ _ -> ())
    (fun pos1 _ _ _ _ ->
      print sl pos1
    )


(* Monotonicity *)

inline_for_extraction
let compl_t (t: Type) = U32.t -> t -> U32.t -> Tot (B.spred byte)

let wvalid 
  (#t: Type) (#k: parser_kind) (p: parser k t) (#rrel #rel: _) (s: slice rrel rel)
  (compl: compl_t t)
  (pos: U32.t)
  (gpos' : Ghost.erased U32.t)
  (gv: Ghost.erased t)
  (x: Seq.seq byte)
: GTot Type0
= 
  U32.v pos <= U32.v (Ghost.reveal gpos') /\
  U32.v (Ghost.reveal gpos') <= U32.v s.len /\
  U32.v s.len <= Seq.length x /\
  parse p (Seq.slice x (U32.v pos) (U32.v s.len)) == Some (Ghost.reveal gv, U32.v (Ghost.reveal gpos') - U32.v pos) /\
  compl pos (Ghost.reveal gv) (Ghost.reveal gpos') x

inline_for_extraction
noeq
type irepr (#t: Type) (#k: parser_kind) (p: parser k t) (#rrel #rel: _) (s: slice rrel rel) (compl: compl_t t) =
  | IRepr:
      (pos: U32.t) ->
      (gpos' : Ghost.erased U32.t) ->
      (gv: Ghost.erased t) ->
      (irepr_correct: squash (
        U32.v pos <= U32.v (Ghost.reveal gpos') /\
        U32.v (Ghost.reveal gpos') <= U32.v s.len /\
        B.witnessed s.base (wvalid p s compl pos gpos' gv)
      )) ->
      irepr p s compl

inline_for_extraction
let irepr_pos
  (#t: Type) (#k: parser_kind) (#p: parser k t) (#rrel #rel: _) (#s: slice rrel rel) (#compl: compl_t t) (x: irepr p s compl) : Tot U32.t =
  IRepr?.pos x

let irepr_pos'
  (#t: Type) (#k: parser_kind) (#p: parser k t) (#rrel #rel: _) (#s: slice rrel rel) (#compl: compl_t t) (x: irepr p s compl) : Ghost U32.t
  (requires True)
  (ensures (fun y -> True))
= Ghost.reveal (IRepr?.gpos' x)

#set-options "--ifuel 1 --fuel 2"

let irepr_pos'_post
  (#t: Type) (#k: parser_kind) (#p: parser k t) (#rrel #rel: _) (#s: slice rrel rel) (#compl: compl_t t) (x: irepr p s compl) : Lemma
  (requires True)
  (ensures (
    let y = irepr_pos' x in
    U32.v (irepr_pos x) <= U32.v y /\ U32.v y <= U32.v s.len
  ))
  [SMTPat (irepr_pos' x)]
= ()

let irepr_v
  (#t: Type) (#k: parser_kind) (#p: parser k t) (#rrel #rel: _) (#s: slice rrel rel) (#compl: compl_t t) (x: irepr p s compl) : GTot t
= Ghost.reveal (IRepr?.gv x)

inline_for_extraction
let witness_valid_gen
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (#rrel #rel: _)
  (s: slice rrel rel)
  (compl: compl_t t)
  (pos: U32.t)
: HST.Stack (irepr p s compl)
  (requires (fun h ->
    valid p h s pos /\
    B.stable_on (wvalid p s compl pos (Ghost.hide (get_valid_pos p h s pos)) (Ghost.hide (contents p h s pos))) (buffer_srel_of_srel rel) /\
    compl pos (contents p h s pos) (get_valid_pos p h s pos) (B.as_seq h s.base)
  ))
  (ensures (fun h res h' ->
    h' == h /\
    irepr_pos res == pos /\
    valid_content_pos p h s pos (irepr_v res) (irepr_pos' res)
  ))
= let h = HST.get () in
  [@inline_let]
  let gpos' = Ghost.hide (get_valid_pos p h s pos) in
  [@inline_let]
  let gv = Ghost.hide (contents p h s pos) in
  [@inline_let]
  let _ = valid_facts p h s pos in
  B.witness_p s.base (wvalid p s compl pos gpos' gv);
  IRepr pos gpos' gv ()

#push-options "--z3rlimit 128"
#restart-solver
inline_for_extraction
let recall_valid_gen
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (#rrel #rel: _)
  (#s: slice rrel rel)
  (#compl: compl_t t)
  (i: irepr p s compl)
: HST.Stack unit
  (requires (fun h -> B.recallable s.base \/ live_slice h s))
  (ensures (fun h _ h' ->
    h' == h /\
    live_slice h s /\
    valid_content_pos p h s (irepr_pos i) (irepr_v i) (irepr_pos' i) /\
    compl (irepr_pos i) (irepr_v i) (irepr_pos' i) (B.as_seq h s.base)
  ))
= let h = HST.get () in
  [@inline_let]
  let _ = valid_facts p h s (irepr_pos i) in
  B.recall_p s.base (wvalid p s compl (irepr_pos i) (IRepr?.gpos' i) (IRepr?.gv i))
#pop-options

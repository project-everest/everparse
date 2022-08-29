module LowParse.Low.Combinators
include LowParse.Low.Base
include LowParse.Spec.Combinators

module B = LowStar.Monotonic.Buffer
module B0 = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--z3rlimit 16"

let valid_nondep_then
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (live_slice h s))
  (ensures ((
    valid (nondep_then p1 p2) h s pos \/
    (valid p1 h s pos /\ valid p2 h s (get_valid_pos p1 h s pos))
  ) ==> (
    valid p1 h s pos /\ (
    let pos1 = get_valid_pos p1 h s pos in
    valid p2 h s (get_valid_pos p1 h s pos) /\
    valid_content_pos (nondep_then p1 p2) h s pos (contents p1 h s pos, contents p2 h s pos1) (get_valid_pos p2 h s pos1)
  ))))
= valid_facts p1 h s pos;
  valid_facts (nondep_then p1 p2) h s pos;
  if U32.v pos <= U32.v s.len
  then begin
    nondep_then_eq p1 p2 (bytes_of_slice_from h s pos);
    if valid_dec p1 h s pos
    then begin
      let pos1 = get_valid_pos p1 h s pos in
      valid_facts p2 h s pos1
    end
  end

let valid_nondep_then_intro
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p1 h s pos /\ valid p2 h s (get_valid_pos p1 h s pos)))
  (ensures ((
    let pos1 = get_valid_pos p1 h s pos in
    valid_content_pos (nondep_then p1 p2) h s pos (contents p1 h s pos, contents p2 h s pos1) (get_valid_pos p2 h s pos1)
  )))
= valid_nondep_then h p1 p2 s pos

inline_for_extraction
let validate_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (p1' : validator p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (p2' : validator p2)
: Tot (validator (nondep_then p1 p2))
= fun   (#rrel #rel: _)
  (input: slice rrel rel) pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_nondep_then h p1 p2 input (uint64_to_uint32 pos) in
  let pos1 = p1' input pos in
  if is_error pos1
  then begin
    pos1
  end
  else
    [@inline_let] let _ = valid_facts p2 h input (uint64_to_uint32 pos1) in
    p2' input pos1

inline_for_extraction
let jump_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (p1' : jumper p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (p2' : jumper p2)
: Tot (jumper (nondep_then p1 p2))
= fun  (#rrel #rel: _)
  (input: slice rrel rel) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_nondep_then h p1 p2 input pos in
  p2' input (p1' input pos)

inline_for_extraction
let read_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (p1' : jumper p1)
  (r1: leaf_reader p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (r2: leaf_reader p2)
: Tot (leaf_reader (nondep_then p1 p2))
= fun #_ #_ sl pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_nondep_then h p1 p2 sl pos in
  let x1 = r1 sl pos in
  let pos2 = p1' sl pos in
  let x2 = r2 sl pos2 in
  (x1, x2)

inline_for_extraction
let serialize32_nondep_then_aux
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : serializer32 s1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#s2: serializer p2)
  (s2' : serializer32 s2)
  (x1: t1)
  (x2: t2)
  (#rrel: _) (#rel: _)
  (b: B.mbuffer byte rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    let len1 = Seq.length (serialize s1 x1) in
    let len2 = Seq.length (serialize s2 x2) in
    let len = len1 + len2 in
    let sq = B.as_seq h b in
    B.live h b /\
    U32.v pos + len <= B.length b /\
    writable b (U32.v pos) (U32.v pos + len) h
  ))
  (ensures (fun h len h' ->
    let len1 = Seq.length (serialize s1 x1) in
    let len2 = Seq.length (serialize s2 x2) in
    len1 + len2 == U32.v len /\ (
    B.modifies (B.loc_buffer_from_to b pos (pos `U32.add` len)) h h' /\
    B.live h b /\
    Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + U32.v len) `Seq.equal` (serialize s1 x1 `Seq.append` serialize s2 x2)
  )))
=
  let gpos' = Ghost.hide (pos `U32.add` U32.uint_to_t (Seq.length (serialize s1 x1) + Seq.length (serialize s2 x2))) in
  let len1 = frame_serializer32 s1' x1 b (Ghost.hide pos) gpos' pos in
  let pos1 = pos `U32.add` len1 in
  let len2 = frame_serializer32 s2' x2 b (Ghost.hide pos) gpos' pos1 in
  let h1 = HST.get () in
  len1 `U32.add` len2

inline_for_extraction
let serialize32_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : serializer32 s1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#s2: serializer p2)
  (s2' : serializer32 s2)
: Tot (serializer32 (s1 `serialize_nondep_then` s2))
= fun x #rrel #rel b pos ->
  [@inline_let]
  let (x1, x2) = x in
  serialize_nondep_then_eq s1 s2 x;
  serialize32_nondep_then_aux s1' s2' x1 x2 b pos

let valid_synth
  (#rrel #rel: _)
  (h: HS.mem)
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    live_slice h input /\ synth_injective f2
  ))
  (ensures (
    (valid (parse_synth p1 f2) h input pos \/ valid p1 h input pos) ==> (
      valid p1 h input pos /\
      valid_content_pos (parse_synth p1 f2) h input pos (f2 (contents p1 h input pos)) (get_valid_pos p1 h input pos)
  )))
= valid_facts p1 h input pos;
  valid_facts (parse_synth p1 f2) h input pos;
  if U32.v pos <= U32.v input.len
  then parse_synth_eq p1 f2 (bytes_of_slice_from h input pos)

let valid_synth_intro
  (#rrel #rel: _)
  (h: HS.mem)
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    synth_injective f2 /\
    valid p1 h input pos
  ))
  (ensures (
    valid_content_pos (parse_synth p1 f2) h input pos (f2 (contents p1 h input pos)) (get_valid_pos p1 h input pos)
  ))
= valid_synth h p1 f2 input pos

inline_for_extraction
let validate_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (#p1: parser k t1)
  (p1' : validator p1)
  (f2: t1 -> GTot t2)
  (u: unit {
    synth_injective f2
  })
: Tot (validator (parse_synth p1 f2))
= fun   (#rrel #rel: _)
  (input: slice rrel rel) pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input (uint64_to_uint32 pos) in
  p1' input pos

inline_for_extraction
let jump_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (#p1: parser k t1)
  (p1' : jumper p1)
  (f2: t1 -> GTot t2)
  (u: unit {
    synth_injective f2
  })
: Tot (jumper (parse_synth p1 f2))
= fun   (#rrel #rel: _)
  (input: slice rrel rel) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input pos in
  p1' input pos

let valid_dtuple2
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (p2: (x: t1) -> parser k2 (t2 x))
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (live_slice h s))
  (ensures ((
    valid (parse_dtuple2 p1 p2) h s pos \/
    (valid p1 h s pos /\ valid (p2 (contents p1 h s pos)) h s (get_valid_pos p1 h s pos))
  ) ==> (
    valid p1 h s pos /\ (
    let pos1 = get_valid_pos p1 h s pos in
    let x = contents p1 h s pos in
    valid (p2 x) h s (get_valid_pos p1 h s pos) /\
    valid_content_pos (parse_dtuple2 p1 p2) h s pos (| x, contents (p2 x) h s pos1 |) (get_valid_pos (p2 x) h s pos1)
  ))))
= valid_facts p1 h s pos;
  valid_facts (parse_dtuple2 p1 p2) h s pos;
  if U32.v pos <= U32.v s.len
  then begin
    parse_dtuple2_eq p1 p2 (bytes_of_slice_from h s pos);
    if valid_dec p1 h s pos
    then begin
      let pos1 = get_valid_pos p1 h s pos in
      let x = contents p1 h s pos in
      valid_facts (p2 x) h s pos1
    end
  end

inline_for_extraction
let validate_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (r1: leaf_reader p1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (v2: (x: t1) -> Tot (validator (p2 x)))
: Tot (validator (parse_dtuple2 p1 p2))
= fun   (#rrel #rel: _)
  (input: slice rrel rel) pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_dtuple2 h p1 p2 input (uint64_to_uint32 pos) in
  let pos1 = v1 input pos in
  if is_error pos1
  then begin
    pos1
  end
  else
    let x = r1 input (uint64_to_uint32 pos) in
    [@inline_let] let _ = valid_facts (p2 x) h input (uint64_to_uint32 pos1) in
    v2 x input pos1

inline_for_extraction
let jump_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (r1: leaf_reader p1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (v2: (x: t1) -> Tot (jumper (p2 x)))
: Tot (jumper (parse_dtuple2 p1 p2))
= fun   (#rrel #rel: _)
  (input: slice rrel rel) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_dtuple2 h p1 p2 input pos in
  let pos1 = v1 input pos in
  let x = r1 input pos in
  [@inline_let] let _ = valid_facts (p2 x) h input pos1 in
  v2 x input pos1

inline_for_extraction
let jump_dtuple2_constant_size_dsnd
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (p2: (x: t1) -> parser k2 (t2 x))
  (sz: U32.t { U32.v sz == k2.parser_kind_low /\ k2.parser_kind_high == Some k2.parser_kind_low })
: Tot (jumper (parse_dtuple2 p1 p2))
= fun   (#rrel #rel: _)
  (input: slice rrel rel) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_dtuple2 h p1 p2 input pos in
  let pos1 = v1 input pos in
  [@inline_let] let p2x = Ghost.hide (p2 (contents p1 h input pos)) in
  [@inline_let] let _ = valid_facts (Ghost.reveal p2x) h input pos1 in
  jump_constant_size' (fun _ -> Ghost.reveal p2x) sz () input pos1

inline_for_extraction
let read_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (r1: leaf_reader p1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#p2: (x: t1) -> parser k2 (t2 x))
  (r2: (x: t1) -> Tot (leaf_reader (p2 x)))
: Tot (leaf_reader (parse_dtuple2 p1 p2))
= fun #_ #_ sl pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_dtuple2 h p1 p2 sl pos in
  let x1 = r1 sl pos in
  let pos2 = v1 sl pos in
  let x2 = r2 x1 sl pos2 in
  (| x1, x2 |)

inline_for_extraction
let serialize32_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : serializer32 s1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: t1 -> Tot Type)
  (#p2: (x: t1) -> Tot (parser k2 (t2 x)))
  (#s2: (x: t1) -> Tot (serializer (p2 x)))
  (s2' : (x: t1) -> serializer32 (s2 x))
: Tot (serializer32 (serialize_dtuple2 s1 s2))
= fun (x: dtuple2 t1 t2) #_ #_ b pos ->
  [@inline_let]
  let _ = serialize_dtuple2_eq s1 s2 x in
  match x with
  | (| x1, x2 |) ->
    serialize32_nondep_then_aux s1' (s2' x1) x1 x2 b pos

inline_for_extraction
let validate_ret
  (#t: Type)
  (v: t)
: Tot (validator (parse_ret v))
= validate_total_constant_size (parse_ret v) 0uL ()

inline_for_extraction
let validate_empty () : Tot (validator parse_empty)
= validate_ret ()

inline_for_extraction
let validate_false () : Tot (validator parse_false)
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = valid_facts parse_false h input (uint64_to_uint32 pos) in
  validator_error_generic

inline_for_extraction
let jump_empty : jumper parse_empty
= jump_constant_size parse_empty 0ul ()

inline_for_extraction
let jump_false : jumper parse_false
= jump_constant_size parse_false 0ul ()

inline_for_extraction
let read_ret
  (#t: Type)
  (v: t)
: Tot (leaf_reader (parse_ret v))
= fun #rrel #rel sl pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_ret v) h sl pos in
  v

inline_for_extraction
let read_empty : leaf_reader parse_empty = read_ret ()

inline_for_extraction
let read_false : leaf_reader parse_false = fun #rrel #rel sl pos ->
  LowStar.Failure.failwith "read_false: should not be called"

inline_for_extraction
let serialize32_ret
  (#t: Type)
  (v: t)
  (v_unique: (v' : t) -> Lemma (v == v'))
: Tot (serializer32 (serialize_ret v v_unique))
= fun _ #_ #_ _ _ -> 0ul

inline_for_extraction
let serialize32_empty : serializer32 #_ #_ #parse_empty serialize_empty
= serialize32_ret () (fun _ -> ())

inline_for_extraction
let serialize32_false : serializer32 #_ #_ #parse_false serialize_false
= fun _ #_ #_ _ _ -> 0ul // dummy

let valid_lift_parser
  (#k: parser_kind)
  (#t: Type)
  (p: unit -> Tot (parser k t))
  (h: HS.mem)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  ((valid (lift_parser p) h input pos \/ valid (p ()) h input pos) ==>
    valid (p ()) h input pos /\
    valid_content_pos (lift_parser p) h input pos (contents (p ()) h input pos) (get_valid_pos (p ()) h input pos))
= valid_facts (p ()) h input pos;
  valid_facts (lift_parser p) h input pos

inline_for_extraction
let validate_lift_parser
  (#k: parser_kind)
  (#t: Type)
  (p: unit -> Tot (parser k t))
  (v: validator #k #t (p ()))
: Tot (validator #k #t (lift_parser p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  valid_lift_parser p h input (uint64_to_uint32 pos);
  v input pos

inline_for_extraction
let jump_lift_parser
  (#k: parser_kind)
  (#t: Type)
  (p: unit -> Tot (parser k t))
  (v: jumper (p ()))
: Tot (jumper (lift_parser p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  valid_lift_parser p h input pos;
  v input pos

let clens_synth
  (#t1: Type)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
: Tot (clens t1 t2)
= {
  clens_cond = (fun (x: t1) -> True);
  clens_get = (fun (x: t1) -> f x);
(*  
  clens_put = (fun (x: t1) (y: t2) -> g y);
  clens_get_put = (fun (x: t1) (y: t2) -> ());
  clens_put_put = (fun (x: t1) (y y' : t2) -> ());
  clens_put_get = (fun (x: t1) -> ());
*)
}

let gaccessor_synth'
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
  (input: bytes)
: Ghost (nat)
  (requires (True))
  (ensures (fun pos' -> gaccessor_post' (parse_synth p1 f) p1 (clens_synth g f) input pos'))
= synth_injective_synth_inverse_synth_inverse_recip f g ();
  parse_synth_eq p1 f input;
  0

val gaccessor_synth
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: squash (synth_inverse f g /\ synth_injective f))
: Tot (gaccessor (parse_synth p1 f) p1 (clens_synth g f))

val gaccessor_synth_eq
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
  (input: bytes)
: Lemma
  (gaccessor_synth p1 f g u input == gaccessor_synth' p1 f g u input)

inline_for_extraction
let accessor_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
: Tot (accessor (gaccessor_synth p1 f g u))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    Classical.forall_intro (gaccessor_synth_eq p1 f g u);
    slice_access_eq h (gaccessor_synth p1 f g u) input pos
  in
  pos

let clens_synth_inv
  (#t1: Type)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
: Tot (clens t2 t1)
= {
  clens_cond = (fun (x: t2) -> True);
  clens_get = (fun (x: t2) -> g x);
(*  
  clens_put = (fun (x: t1) (y: t2) -> g y);
  clens_get_put = (fun (x: t1) (y: t2) -> ());
  clens_put_put = (fun (x: t1) (y y' : t2) -> ());
  clens_put_get = (fun (x: t1) -> ());
*)
}

let gaccessor_synth_inv'
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
  (input: bytes)
: Ghost (nat)
  (requires (True))
  (ensures (fun pos' -> gaccessor_post' p1 (parse_synth p1 f) (clens_synth_inv g f) input pos'))
= parse_synth_eq p1 f input;
  0

val gaccessor_synth_inv
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: squash (synth_inverse f g /\ synth_injective f))
: Tot (gaccessor p1 (parse_synth p1 f) (clens_synth_inv g f))

val gaccessor_synth_inv_eq
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
  (input: bytes)
: Lemma
  (gaccessor_synth_inv p1 f g u input == gaccessor_synth_inv' p1 f g u input)

inline_for_extraction
let accessor_synth_inv
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
: Tot (accessor (gaccessor_synth_inv p1 f g u))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    Classical.forall_intro (gaccessor_synth_inv_eq p1 f g u);
    slice_access_eq h (gaccessor_synth_inv p1 f g u) input pos
  in
  pos

let clens_fst
  (t1: Type)
  (t2: Type)
: Tot (clens (t1 & t2) t1)
= {
  clens_cond = (fun (x: (t1 & t2)) -> True);
  clens_get = fst;
(*  
  clens_put = (fun x y -> (y, snd x));
  clens_get_put = (fun x y -> ());
  clens_put_put = (fun x y y' -> ());
  clens_put_get = (fun x -> ());
*)
}

let clens_snd
  (t1: Type)
  (t2: Type)
: Tot (clens (t1 & t2) t2)
= {
  clens_cond = (fun (x: (t1 & t2)) -> True);
  clens_get = snd;
(*  
  clens_put = (fun x y -> (fst x, y));
  clens_get_put = (fun x y -> ());
  clens_put_put = (fun x y y' -> ());
  clens_put_get = (fun x -> ());
*)
}

let gaccessor_fst'
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (sq: squash unit)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (input: bytes)
: Ghost (nat)
  (requires True)
  (ensures (fun pos' -> gaccessor_post' (p1 `nondep_then` p2) p1 (clens_fst _ _) input pos'))
= nondep_then_eq p1 p2 input;
  0

[@"opaque_to_smt"]
let gaccessor_fst
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (sq: squash unit)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (gaccessor (p1 `nondep_then` p2) p1 (clens_fst _ _))
= gaccessor_prop_equiv (p1 `nondep_then` p2) p1 (clens_fst _ _) (gaccessor_fst' p1 sq p2);
  gaccessor_fst' p1 sq p2

let gaccessor_fst_eq
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (sq: squash unit)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (input: bytes)
: Lemma
  (gaccessor_fst p1 sq p2 input == gaccessor_fst' p1 sq p2 input)
= reveal_opaque (`%gaccessor_fst) (gaccessor_fst p1 sq p2 input)

let gaccessor_fst_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k' : parser_kind)
  (#t' : Type)
  (#p': parser k' t')
  (#cl: clens t1 t')
  (g: gaccessor p1 p' cl)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (u: squash unit)
: Tot (gaccessor (p1 `nondep_then` p2) p' (clens_fst _ _ `clens_compose` cl))
= gaccessor_fst p1 u p2 `gaccessor_compose` g

let gaccessor_then_fst
  (#k0: parser_kind)
  (#t0: Type)
  (#p0: parser k0 t0)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t0 (t1 & t2))
  (g: gaccessor p0 (p1 `nondep_then` p2) cl)
: Tot (gaccessor p0 p1 (cl `clens_compose` clens_fst _ _))
= g `gaccessor_compose` gaccessor_fst _ () _

let gaccessor_snd'
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (input: bytes)
: Ghost (nat)
  (requires (True))
  (ensures (fun pos' -> gaccessor_post' (p1 `nondep_then` p2) p2 (clens_snd _ _) input pos'))
= nondep_then_eq p1 p2 input;
  match parse p1 input with
  | None -> 0 // dummy
  | Some (_, consumed) -> consumed

let gaccessor_snd_injective
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (sl sl' : bytes)
: Lemma
  (requires (gaccessor_pre (p1 `nondep_then` p2) p2 (clens_snd _ _) sl /\ gaccessor_pre (p1 `nondep_then` p2) p2 (clens_snd _ _) sl /\ injective_precond (p1 `nondep_then` p2) sl sl'))
  (ensures (gaccessor_snd' p1 p2 sl == gaccessor_snd' p1 p2 sl'))
= nondep_then_eq p1 p2 sl;
  nondep_then_eq p1 p2 sl';
  parse_injective p1 sl sl'

let gaccessor_snd_no_lookahead
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (sl sl' : bytes)
: Lemma
  (requires ((and_then_kind k1 k2).parser_kind_subkind == Some ParserStrong /\ gaccessor_pre (p1 `nondep_then` p2) p2 (clens_snd _ _) sl /\ gaccessor_pre (p1 `nondep_then` p2) p2 (clens_snd _ _) sl /\ no_lookahead_on_precond (p1 `nondep_then` p2) sl sl'))
  (ensures (gaccessor_snd' p1 p2 sl == gaccessor_snd' p1 p2 sl'))
= nondep_then_eq p1 p2 sl;
  nondep_then_eq p1 p2 sl' ;
  parse_strong_prefix (p1 `nondep_then` p2) sl sl';
  parse_injective p1 sl sl' ;
  parse_strong_prefix p1 sl sl'

[@"opaque_to_smt"]
let gaccessor_snd
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (gaccessor (p1 `nondep_then` p2) p2 (clens_snd _ _))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_snd_injective p1 p2 x));
  Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_snd_no_lookahead p1 p2 x));
  gaccessor_prop_equiv (p1 `nondep_then` p2) p2 (clens_snd _ _) (gaccessor_snd' p1 p2);
  gaccessor_snd' p1 p2

let gaccessor_snd_eq
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (input: bytes)
: Lemma
  (gaccessor_snd p1 p2 input == gaccessor_snd' p1 p2 input)
= reveal_opaque (`%gaccessor_snd) (gaccessor_snd p1 p2 input )

let gaccessor_then_snd
  (#k0: parser_kind)
  (#t0: Type)
  (#p0: parser k0 t0)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t0 (t1 & t2))
  (g: gaccessor p0 (p1 `nondep_then` p2) cl)
: Tot (gaccessor p0 p2 (cl `clens_compose` clens_snd _ _))
= g `gaccessor_compose` gaccessor_snd _ _


(*
let clens_fst_snd_disjoint
  (t1 t2: Type)
: Lemma
  (clens_disjoint (clens_fst t1 t2) (clens_snd t1 t2))
= clens_disjoint_l_intro (clens_fst t1 t2) (clens_snd t1 t2) (fun x1 x2 -> ());
  clens_disjoint_l_intro (clens_snd t1 t2) (clens_fst t1 t2) (fun x1 x2 -> ())
*)

(*
abstract
let gaccessor_fst_snd_disjoint
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (sq: squash (k1.parser_kind_subkind == Some ParserStrong))
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Lemma
  (gaccessors_disjoint (gaccessor_fst p1 sq p2) (gaccessor_snd p1 p2))
= // clens_fst_snd_disjoint t1 t2;
  gaccessors_disjoint_intro (gaccessor_fst p1 sq p2) (gaccessor_snd p1 p2) (* *) (fun x -> ())
*)

inline_for_extraction
let accessor_fst
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (sq: squash unit)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (accessor (gaccessor_fst p1 sq p2))
= reveal_opaque (`%gaccessor_fst) (gaccessor_fst p1 sq p2);
  fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_fst p1 sq p2) input pos in
  pos

inline_for_extraction
let accessor_fst_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k' : parser_kind)
  (#t' : Type)
  (#p': parser k' t')
  (#cl: clens t1 t')
  (#g: gaccessor p1 p' cl)
  (a: accessor g)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (u: squash unit)
: Tot (accessor (gaccessor_fst_then g p2 u))
= accessor_compose (accessor_fst p1 u p2) a u

inline_for_extraction
let accessor_then_fst
  (#k0: parser_kind)
  (#t0: Type)
  (#p0: parser k0 t0)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t0 (t1 & t2))
  (#g: gaccessor p0 (p1 `nondep_then` p2) cl)
  (a: accessor g)
: Tot (accessor (gaccessor_then_fst g))
= accessor_compose a (accessor_fst p1 () p2) ()

inline_for_extraction
let accessor_snd
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (accessor (gaccessor_snd p1 p2))
= reveal_opaque (`%gaccessor_snd) (gaccessor_snd p1 p2);
  fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_nondep_then h p1 p2 input pos in
  let res = j1 input pos in
  [@inline_let] let _ =
    slice_access_eq h (gaccessor_snd p1 p2) input pos;
    valid_facts p1 h input pos
  in
  res

inline_for_extraction
let accessor_then_snd
  (#k0: parser_kind)
  (#t0: Type)
  (#p0: parser k0 t0)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t0 (t1 & t2))
  (#g: gaccessor p0 (p1 `nondep_then` p2) cl)
  (a: accessor g)
  (j1: jumper p1)
: Tot (accessor (gaccessor_then_snd g))
= accessor_compose a (accessor_snd j1 p2) ()

inline_for_extraction
let make_total_constant_size_reader
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (t)))
  (u: unit {
    make_total_constant_size_parser_precond sz t f
  })
  (f' : ((#rrel: _) -> (#rel: _) -> (s: B.mbuffer byte rrel rel) -> (pos: U32.t) -> HST.Stack t
    (requires (fun h -> B.live h s /\ U32.v pos + sz <= B.length s))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      res == f (Seq.slice (B.as_seq h s) (U32.v pos) (U32.v pos + sz))
  ))))
: Tot (leaf_reader (make_total_constant_size_parser sz t f))
= fun #rrel #rel sl pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (make_total_constant_size_parser sz t f) h sl pos in
  f' sl.base pos

let valid_filter
  (#rrel #rel: _)
  (h: HS.mem)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (
    (valid (parse_filter p f) h input pos \/ (valid p h input pos /\ f (contents p h input pos))) ==> (
    valid p h input pos /\
    f (contents p h input pos) == true /\
    valid_content_pos (parse_filter p f) h input pos (contents p h input pos) (get_valid_pos p h input pos)
  ))
= valid_facts (parse_filter p f) h input pos;
  valid_facts p h input pos;
  if U32.v pos <= U32.v input.len
  then parse_filter_eq p f (bytes_of_slice_from h input pos)

inline_for_extraction
let validate_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v32: validator p)
  (p32: leaf_reader p)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Tot (validator (parse_filter p f))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input (uint64_to_uint32 pos) in
  let res = v32 input pos in
  if is_error res
  then res
  else
    let va = p32 input (uint64_to_uint32 pos) in
    if not (f' va)
    then validator_error_generic
    else res

inline_for_extraction
let validate_filter_with_error_code
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v32: validator p)
  (p32: leaf_reader p)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
  (c: error_code)
: Tot (validator (parse_filter p f))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input (uint64_to_uint32 pos) in
  let res = v32 input pos in
  if is_error res
  then maybe_set_validator_error_pos_and_code res pos c
  else
    let va = p32 input (uint64_to_uint32 pos) in
    if not (f' va)
    then set_validator_error_pos_and_code validator_error_generic pos c
    else res

inline_for_extraction
let validate_filter_ret
  (#t: Type0)
  (r: t)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Tot (validator (parse_filter (parse_ret r) f))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h (parse_ret r) f input (uint64_to_uint32 pos) in
  [@inline_let] let _ = valid_facts (parse_ret r) h input (uint64_to_uint32 pos) in
  if not (f' r)
  then validator_error_generic
  else pos

inline_for_extraction
let validate_filter_ret_with_error_code
  (#t: Type0)
  (r: t)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
  (c: error_code)
: Tot (validator (parse_filter (parse_ret r) f))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h (parse_ret r) f input (uint64_to_uint32 pos) in
  [@inline_let] let _ = valid_facts (parse_ret r) h input (uint64_to_uint32 pos) in
  if not (f' r)
  then set_validator_error_pos_and_code validator_error_generic pos c
  else pos

inline_for_extraction
let jump_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (f: (t -> GTot bool))
: Tot (jumper (parse_filter p f))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input pos in
  j input pos

inline_for_extraction
let read_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: leaf_reader p)
  (f: (t -> GTot bool))
: Tot (leaf_reader (parse_filter p f))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input pos in
  (p32 input pos <: (res: t { f res == true } )) // FIXME: WHY WHY WHY do we need this coercion?

inline_for_extraction
let write_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: leaf_writer_strong s)
  (f: (t -> GTot bool))
: Tot (leaf_writer_strong (serialize_filter s f))
= fun x #rrel #rel input pos ->
  [@inline_let] let _ = serialized_length_eq s x in
  [@inline_let] let _ = serialized_length_eq (serialize_filter s f) x in 
  let res = s32 x input pos in
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input pos in
  res

inline_for_extraction
let write_filter_weak
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: leaf_writer_weak s)
  (f: (t -> GTot bool))
: Tot (leaf_writer_weak (serialize_filter s f))
= fun x #rrel #rel input pos ->
  [@inline_let] let _ = serialized_length_eq s x in
  [@inline_let] let _ = serialized_length_eq (serialize_filter s f) x in 
  let res = s32 x input pos in
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input pos in
  res

inline_for_extraction
let serialize32_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (f: (t -> GTot bool))
: Tot (serializer32 (serialize_filter s f))
= fun x #rrel #rel input pos ->
  s32 x input pos

inline_for_extraction
let read_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x } )) 
  (p1' : leaf_reader p1)
  (u: unit {
    synth_injective f2
  })
: Tot (leaf_reader (parse_synth p1 f2))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input pos in
  let res = p1' input pos in
  f2' res <: t2 // FIXME: WHY WHY WHY this coercion AND the separate let binding?

inline_for_extraction
let read_synth'
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (p1' : leaf_reader p1)
  (u: unit {
    synth_injective f2
  })
: Tot (leaf_reader (parse_synth p1 f2))
= read_synth p1 f2 (fun x -> f2 x) p1' u

inline_for_extraction
let read_inline_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x } )) 
  (p1' : leaf_reader p1)
  (u: unit {
    synth_injective f2
  })
: Tot (leaf_reader (parse_synth p1 f2))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input pos in
  [@inline_let] let f2'' (x: t1) : HST.Stack t2 (requires (fun _ -> True)) (ensures (fun h y h' -> h == h' /\ y == f2 x)) = f2' x in // FIXME: WHY WHY WHY do I need this stateful function here? why can't I directly use f2' ?
  f2'' (p1' input pos)

inline_for_extraction
let read_inline_synth'
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (p1' : leaf_reader p1)
  (u: unit {
    synth_injective f2
  })
: Tot (leaf_reader (parse_synth p1 f2))
= read_inline_synth p1 f2 (fun x -> f2 x) p1' ()

inline_for_extraction
let write_synth
  (#k: parser_kind)
  (#t1: Type)
  (#p1: parser k t1)
  (#s1: serializer p1)
  (s1' : leaf_writer_strong s1)
  (#t2: Type)
  (f2: t1 -> GTot t2)
  (g1: t2 -> GTot t1)
  (g1' : (x2: t2) -> Tot (x1: t1 { x1 == g1 x2 } ))
  (u: squash (synth_injective f2 /\ synth_inverse f2 g1))
: Tot (leaf_writer_strong (serialize_synth p1 f2 s1 g1 ()))
= fun x #rrel #rel input pos ->
  [@inline_let] let _ = serialize_synth_eq p1 f2 s1 g1 () x in
  [@inline_let] let _ = serialized_length_eq (serialize_synth p1 f2 s1 g1 ()) x in
  [@inline_let] let _ = serialized_length_eq s1 (g1 x) in
  let pos' = s1' (g1' x) input pos in
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input pos in
  pos'

inline_for_extraction
let write_synth_weak
  (#k: parser_kind)
  (#t1: Type)
  (#p1: parser k t1)
  (#s1: serializer p1)
  (s1' : leaf_writer_weak s1)
  (#t2: Type)
  (f2: t1 -> GTot t2)
  (g1: t2 -> GTot t1)
  (g1' : (x2: t2) -> Tot (x1: t1 { x1 == g1 x2 } ))
  (u: squash (synth_injective f2 /\ synth_inverse f2 g1))
: Tot (leaf_writer_weak (serialize_synth p1 f2 s1 g1 ()))
= fun x #rrel #rel input pos ->
  [@inline_let] let _ = serialize_synth_eq p1 f2 s1 g1 () x in
  [@inline_let] let _ = serialized_length_eq (serialize_synth p1 f2 s1 g1 ()) x in
  [@inline_let] let _ = serialized_length_eq s1 (g1 x) in
  let pos' = s1' (g1' x) input pos in
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input pos in
  pos'

inline_for_extraction
let serialize32_synth
  (#k: parser_kind)
  (#t1: Type)
  (#p1: parser k t1)
  (#s1: serializer p1)
  (s1' : serializer32 s1)
  (#t2: Type)
  (f2: t1 -> GTot t2)
  (g1: t2 -> GTot t1)
  (g1' : (x2: t2) -> Tot (x1: t1 { x1 == g1 x2 } ))
  (u: squash (synth_injective f2 /\ synth_inverse f2 g1))
: Tot (serializer32 (serialize_synth p1 f2 s1 g1 ()))
= fun x #rrel #rel input pos ->
  [@inline_let] let _ =
    serialize_synth_eq p1 f2 s1 g1 () x
  in
  s1' (g1' x) input pos

(* Special case for vldata and maybe also sum types *)

inline_for_extraction
let validate_filter_and_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (p1': leaf_reader p1)
  (f: (t1 -> GTot bool))
  (f' : ((x: t1) -> Tot (y: bool { y == f x } )))
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: ((x: t1 { f x == true} ) -> parser k2 t2))
  (v2: ((x1: t1 { f x1 == true } ) -> validator (p2 x1)))
  (u: unit {
    and_then_cases_injective p2
  })
: Tot (validator (parse_filter p1 f `and_then` p2))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    let sinput = bytes_of_slice_from h input (uint64_to_uint32 pos) in
    valid_facts (parse_filter p1 f `and_then` p2) h input (uint64_to_uint32 pos);
    and_then_eq (parse_filter p1 f) p2 sinput;
    parse_filter_eq p1 f sinput;
    valid_facts p1 h input (uint64_to_uint32 pos)
  in
  let res = v1 input pos in
  if is_error res
  then res
  else
    let va = p1' input (uint64_to_uint32 pos) in
    if f' va
    then
      [@inline_let]
      let _ = valid_facts (p2 va) h input (uint64_to_uint32 res) in
      v2 va input res
    else validator_error_generic

inline_for_extraction
let validate_weaken
  (k1: parser_kind)
  (#k2: parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (v2: validator p2)
  (sq: squash (k1 `is_weaker_than` k2))
: Tot (validator (weaken k1 p2))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = valid_facts (weaken k1 p2) h input (uint64_to_uint32 pos) in
  [@inline_let]
  let _ = valid_facts p2 h input (uint64_to_uint32 pos) in
  v2 input pos

inline_for_extraction
let jump_weaken
  (k1: parser_kind)
  (#k2: parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (v2: jumper p2)
  (sq: squash (k1 `is_weaker_than` k2))
: Tot (jumper (weaken k1 p2))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = valid_facts (weaken k1 p2) h input pos in
  [@inline_let]
  let _ = valid_facts p2 h input pos in
  v2 input pos

inline_for_extraction
let validate_strengthen
  (k2: parser_kind)
  (#k1: parser_kind)
  (#t: Type)
  (#p1: parser k1 t)
  (v1: validator p1)
  (sq: squash (parser_kind_prop k2 p1))
: Tot (validator (strengthen k2 p1))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = valid_facts (strengthen k2 p1) h input (uint64_to_uint32 pos) in
  [@inline_let]
  let _ = valid_facts p1 h input (uint64_to_uint32 pos) in
  v1 input pos

inline_for_extraction
let validate_compose_context
  (#pk: parser_kind)
  (#kt1 #kt2: Type)
  (f: (kt2 -> Tot kt1))
  (t: (kt1 -> Tot Type))
  (p: ((k: kt1) -> Tot (parser pk (t k))))
  (v: ((k: kt1) -> Tot (validator (p k))))
  (k: kt2)
: Tot (validator (p (f k)))
= fun #rrel #rel input pos -> v (f k) input pos

inline_for_extraction
let jump_compose_context
  (#pk: parser_kind)
  (#kt1 #kt2: Type)
  (f: (kt2 -> Tot kt1))
  (t: (kt1 -> Tot Type))
  (p: ((k: kt1) -> Tot (parser pk (t k))))
  (v: ((k: kt1) -> Tot (jumper (p k))))
  (k: kt2)
: Tot (jumper (p (f k)))
= fun #rrel #rel input pos -> v (f k) input pos

let clens_tagged_union_tag
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
: Tot (clens data_t tag_t)
= {
    clens_cond = (fun _ -> True);
    clens_get  = tag_of_data;
  }

let gaccessor_tagged_union_tag'
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
: Tot (gaccessor' (parse_tagged_union pt tag_of_data p) pt (clens_tagged_union_tag tag_of_data))
= fun input ->
    parse_tagged_union_eq pt tag_of_data p input;
    0

let gaccessor_tagged_union_tag
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
: Tot (gaccessor (parse_tagged_union pt tag_of_data p) pt (clens_tagged_union_tag tag_of_data))
= gaccessor_prop_equiv (parse_tagged_union pt tag_of_data p) pt (clens_tagged_union_tag tag_of_data) (gaccessor_tagged_union_tag' pt tag_of_data p);
  gaccessor_tagged_union_tag' pt tag_of_data p

inline_for_extraction
let accessor_tagged_union_tag
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
: Tot (accessor (gaccessor_tagged_union_tag pt tag_of_data p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_tagged_union_tag pt tag_of_data p) input pos in
  pos

let clens_tagged_union_payload
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (t: tag_t)
: Tot (clens data_t (refine_with_tag tag_of_data t))
= {
    clens_cond = (fun d -> tag_of_data d == t);
    clens_get  = (fun (d: data_t) -> (d <: refine_with_tag tag_of_data t));
  }

let gaccessor_tagged_union_payload'
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (t: tag_t)
: Tot (gaccessor' (parse_tagged_union pt tag_of_data p) (p t) (clens_tagged_union_payload tag_of_data t))
= fun input ->
    parse_tagged_union_eq pt tag_of_data p input;
    match parse pt input with
      | Some (t', consumed_t) ->
        consumed_t
      | _ -> 0 (* dummy *)

let gaccessor_tagged_union_payload_injective
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (t: tag_t)
  (sl sl' : bytes)
: Lemma
  (requires (
    gaccessor_pre (parse_tagged_union pt tag_of_data p) (p t) (clens_tagged_union_payload tag_of_data t) sl /\
    gaccessor_pre (parse_tagged_union pt tag_of_data p) (p t) (clens_tagged_union_payload tag_of_data t) sl' /\
    injective_precond (parse_tagged_union pt tag_of_data p) sl sl'
  ))
  (ensures (
    gaccessor_tagged_union_payload' pt tag_of_data p t sl == gaccessor_tagged_union_payload' pt tag_of_data p t sl'
  ))
= parse_injective (parse_tagged_union pt tag_of_data p) sl sl' ;
  parse_tagged_union_eq pt tag_of_data p sl ;
  parse_tagged_union_eq pt tag_of_data p sl' ;
  parse_injective pt sl sl'

let gaccessor_tagged_union_payload_no_lookahead
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (t: tag_t)
  (sl sl' : bytes)
: Lemma
  (requires (
    (and_then_kind kt k).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_tagged_union pt tag_of_data p) (p t) (clens_tagged_union_payload tag_of_data t) sl /\
    gaccessor_pre (parse_tagged_union pt tag_of_data p) (p t) (clens_tagged_union_payload tag_of_data t) sl' /\
    no_lookahead_on_precond (parse_tagged_union pt tag_of_data p) sl sl'
  ))
  (ensures (
    gaccessor_tagged_union_payload' pt tag_of_data p t sl == gaccessor_tagged_union_payload' pt tag_of_data p t sl'
  ))
= parse_strong_prefix (parse_tagged_union pt tag_of_data p) sl sl' ;
  parse_tagged_union_eq pt tag_of_data p sl ;
  parse_tagged_union_eq pt tag_of_data p sl' ;
  parse_injective pt sl sl'

let gaccessor_tagged_union_payload
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (t: tag_t)
: Tot (gaccessor (parse_tagged_union pt tag_of_data p) (p t) (clens_tagged_union_payload tag_of_data t))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_tagged_union_payload_injective pt tag_of_data p t x));
  Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_tagged_union_payload_no_lookahead pt tag_of_data p t x));
  gaccessor_prop_equiv (parse_tagged_union pt tag_of_data p) (p t) (clens_tagged_union_payload tag_of_data t) (gaccessor_tagged_union_payload' pt tag_of_data p t);
  gaccessor_tagged_union_payload' pt tag_of_data p t

inline_for_extraction
let accessor_tagged_union_payload
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (jt: jumper pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (t: tag_t)
: Tot (accessor (gaccessor_tagged_union_payload pt tag_of_data p t))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_tagged_union pt tag_of_data p) h input pos;
    parse_tagged_union_eq pt tag_of_data p (bytes_of_slice_from h input pos);
    valid_facts pt h input pos
  in
  let res = jt input pos in
  [@inline_let] let _ =
    slice_access_eq h (gaccessor_tagged_union_payload pt tag_of_data p t) input pos
  in
  res

module LowParse.Low.VCList
include LowParse.Spec.VCList
include LowParse.Low.List

module L = FStar.List.Tot
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

let valid_nlist_nil
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (live_slice h sl /\ U32.v pos <= U32.v sl.len))
  (ensures (valid_content_pos (parse_nlist 0 p) h sl pos [] pos))
= valid_facts (parse_nlist 0 p) h sl pos;
  parse_nlist_eq 0 p (bytes_of_slice_from h sl pos)

let valid_nlist_nil_recip
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid (parse_nlist 0 p) h sl pos))
  (ensures (valid_content_pos (parse_nlist 0 p) h sl pos [] pos))
= valid_facts (parse_nlist 0 p) h sl pos;
  parse_nlist_eq 0 p (bytes_of_slice_from h sl pos)

#push-options "--z3rlimit 16"

let valid_nlist_cons
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid p h sl pos /\
    valid (parse_nlist n p) h sl (get_valid_pos p h sl pos)
  ))
  (ensures (
    valid p h sl pos /\
    valid (parse_nlist n p) h sl (get_valid_pos p h sl pos) /\ (
    let pos1 = get_valid_pos p h sl pos in
    valid_content_pos
      (parse_nlist (n + 1) p)
      h
      sl
      pos
      (contents p h sl pos :: contents (parse_nlist n p) h sl pos1)
      (get_valid_pos (parse_nlist n p) h sl pos1)
  )))
= let pos1 = get_valid_pos p h sl pos in
  valid_facts p h sl pos;
  valid_facts (parse_nlist n p) h sl pos1;
  valid_facts (parse_nlist (n + 1) p) h sl pos;
  parse_nlist_eq (n + 1) p (bytes_of_slice_from h sl pos)

let valid_nlist_cons_recip
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    n > 0 /\
    valid (parse_nlist n p) h sl pos
  ))
  (ensures (
    valid p h sl pos /\ (
    let pos1 = get_valid_pos p h sl pos in
    valid (parse_nlist (n - 1) p) h sl (get_valid_pos p h sl pos) /\
    valid_content_pos
      (parse_nlist n p)
      h
      sl
      pos
      (contents p h sl pos :: contents (parse_nlist (n - 1) p) h sl pos1)
      (get_valid_pos (parse_nlist (n - 1) p) h sl pos1)
  )))
= valid_facts (parse_nlist n p) h sl pos;
  parse_nlist_eq n p (bytes_of_slice_from h sl pos);
  valid_facts p h sl pos;
  let pos1 = get_valid_pos p h sl pos in
  valid_facts (parse_nlist (n - 1) p) h sl pos1

#pop-options

let valid_nlist_cons'
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    n > 0 /\
    valid p h sl pos
  ))
  (ensures (
    let pos1 = get_valid_pos p h sl pos in
    (valid (parse_nlist n p) h sl pos <==> valid (parse_nlist (n - 1) p) h sl pos1) /\
    ((valid (parse_nlist n p) h sl pos /\ valid (parse_nlist (n - 1) p) h sl pos1) ==> get_valid_pos (parse_nlist n p) h sl pos == get_valid_pos (parse_nlist (n - 1) p) h sl pos1)
  ))
= Classical.move_requires (valid_nlist_cons (n - 1) p h sl) pos;
  Classical.move_requires (valid_nlist_cons_recip n p h sl) pos

let valid_nlist_cons_not
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    n > 0 /\
    (~ (valid p h sl pos))
  ))
  (ensures (
    ~ (valid (parse_nlist n p) h sl pos)
  ))
= Classical.move_requires (valid_nlist_cons (n - 1) p h sl) pos;
  Classical.move_requires (valid_nlist_cons_recip n p h sl) pos

#push-options "--z3rlimit 32"

inline_for_extraction
let validate_nlist
  (n: U32.t)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
: Tot (validator (parse_nlist (U32.v n) p))
= fun #rrel #rel input pos ->
  let h0 = HST.get () in
  HST.push_frame ();
  let bpos1 : B.buffer U64.t = B.alloca pos 1ul in
  let br = B.alloca n 1ul in
  let h1 = HST.get () in
  C.Loops.do_while
    (fun h stop ->
      B.modifies (B.loc_buffer bpos1 `B.loc_union` B.loc_buffer br) h1 h /\ (
      let pos1 = B.get h bpos1 0 in
      let r = B.get h br 0 in
      U32.v r <= U32.v n /\
      U64.v pos <= U64.v pos1 /\ (
      if is_success pos1
      then
        let pos1 = uint64_to_uint32 pos1 in
        U32.v pos1 <= U32.v input.len /\
        (valid (parse_nlist (U32.v n) p) h0 input (uint64_to_uint32 pos) <==> valid (parse_nlist (U32.v r) p) h0 input pos1) /\
        ((valid (parse_nlist (U32.v n) p) h0 input (uint64_to_uint32 pos) /\ valid (parse_nlist (U32.v r) p) h0 input pos1) ==> get_valid_pos (parse_nlist (U32.v n) p) h0 input (uint64_to_uint32 pos) == get_valid_pos (parse_nlist (U32.v r) p) h0 input pos1) /\
        (stop == true ==> r == 0ul)
      else
        (stop == true /\ (~ (valid (parse_nlist (U32.v n) p) h0 input (uint64_to_uint32 pos))))
    )))
    (fun _ ->
      let r = B.index br 0ul in
      if r = 0ul
      then true
      else
        let pos1 = B.index bpos1 0ul in
        let pos2 = v input pos1 in
        let _ = B.upd br 0ul (r `U32.sub` 1ul) in
        let _ = B.upd bpos1 0ul pos2 in
        [@inline_let]
        let stop = is_error pos2 in
        [@inline_let]
        let _ =
          if stop
          then valid_nlist_cons_not (U32.v r) p h0 input (uint64_to_uint32 pos1)
          else valid_nlist_cons' (U32.v r) p h0 input (uint64_to_uint32 pos1)
        in
        stop
    )
  ;
  let res = B.index bpos1 0ul in
  [@inline_let] let _ =
    if is_success res
    then valid_nlist_nil p h0 input (uint64_to_uint32 res)
  in
  HST.pop_frame ();
  res

inline_for_extraction
let jump_nlist
  (n: U32.t)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: jumper p)
: Tot (jumper (parse_nlist (U32.v n) p))
= fun #rrel #rel input pos ->
  let h0 = HST.get () in
  HST.push_frame ();
  let bpos1 = B.alloca pos 1ul in
  let br = B.alloca n 1ul in
  let h1 = HST.get () in
  C.Loops.do_while
    (fun h stop ->
      B.modifies (B.loc_buffer bpos1 `B.loc_union` B.loc_buffer br) h1 h /\ (
      let pos1 = B.get h bpos1 0 in
      let r = B.get h br 0 in
      U32.v r <= U32.v n /\
      U32.v pos <= U32.v pos1 /\
      U32.v pos1 <= U32.v input.len /\
      valid (parse_nlist (U32.v n) p) h0 input pos /\ valid (parse_nlist (U32.v r) p) h0 input pos1 /\
      get_valid_pos (parse_nlist (U32.v n) p) h0 input pos == get_valid_pos (parse_nlist (U32.v r) p) h0 input pos1 /\
      (stop == true ==> r == 0ul)
    ))
    (fun _ ->
      let r = B.index br 0ul in
      if r = 0ul
      then true
      else
        let pos1 = B.index bpos1 0ul in
        [@inline_let]
        let _ =
          valid_nlist_cons_recip (U32.v r) p h0 input pos1
        in
        let pos2 = v input pos1 in
        let _ = B.upd br 0ul (r `U32.sub` 1ul) in
        let _ = B.upd bpos1 0ul pos2 in
        false
    )
  ;
  let res = B.index bpos1 0ul in
  [@inline_let] let _ =
    valid_nlist_nil p h0 input res
  in
  HST.pop_frame ();
  res

#pop-options

let rec valid_nlist_valid_list
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    k.parser_kind_low > 0 /\
    k.parser_kind_subkind == Some ParserStrong /\
    valid (parse_nlist n p) h sl pos
  ))
  (ensures (
    let pos' = get_valid_pos (parse_nlist n p) h sl pos in
    valid_list p h sl pos pos' /\
    contents_list p h sl pos pos' == contents (parse_nlist n p) h sl pos
  ))
= if n = 0
  then begin
    valid_nlist_nil_recip p h sl pos;
    valid_list_nil p h sl pos
  end else begin
    valid_nlist_cons_recip n p h sl pos;
    let pos1 = get_valid_pos p h sl pos in
    let pos' = get_valid_pos (parse_nlist n p) h sl pos in
    valid_nlist_valid_list (n - 1) p h sl pos1;
    valid_list_cons p h sl pos pos'
  end

let rec valid_list_valid_nlist
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    valid_list p h sl pos pos'
  ))
  (ensures (
    let x = contents_list p h sl pos pos' in
    valid_content_pos (parse_nlist (L.length x) p) h sl pos x pos'
  ))
  (decreases (U32.v pos' - U32.v pos))
= if pos = pos'
  then begin
    valid_list_nil p h sl pos;
    valid_nlist_nil p h sl pos
  end else begin
    valid_list_cons_recip p h sl pos pos' ;
    let pos1 = get_valid_pos p h sl pos in
    valid_list_valid_nlist p h sl pos1 pos' ;
    valid_nlist_cons (L.length (contents_list p h sl pos1 pos')) p h sl pos
  end

(* vclist *)

#push-options "--z3rlimit 16"

inline_for_extraction
let validate_vclist
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (lv: validator lp)
  (lr: leaf_reader lp)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
: Tot (validator (parse_vclist (U32.v min) (U32.v max) lp p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_vclist (U32.v min) (U32.v max) lp p) h input (uint64_to_uint32 pos);
    parse_vclist_eq (U32.v min) (U32.v max) lp p (bytes_of_slice_from h input (uint64_to_uint32 pos));
    valid_facts lp h input (uint64_to_uint32 pos)
  in
  let pos1 = lv input pos in
  if is_error pos1
  then pos1 // error
  else
    let n = lr input (uint64_to_uint32 pos) in
    if n `U32.lt` min || max `U32.lt` n
    then validator_error_generic
    else
      [@inline_let]
      let _ = valid_facts (parse_nlist (U32.v n) p) h input (uint64_to_uint32 pos1) in
      validate_nlist n v input pos1

inline_for_extraction
let jump_vclist
  (min: nat)
  (max: nat { min <= max } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (lv: jumper lp)
  (lr: leaf_reader lp)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: jumper p)
: Tot (jumper (parse_vclist min max lp p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_vclist min max lp p) h input pos;
    parse_vclist_eq min max lp p (bytes_of_slice_from h input pos);
    valid_facts lp h input pos
  in
  let pos1 = lv input pos in
  let n = lr input pos in
  [@inline_let]
  let _ = valid_facts (parse_nlist (U32.v n) p) h input pos1 in
  jump_nlist n v input pos1

#pop-options

let valid_vclist_elim
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#lk: parser_kind)
  (lp: parser lk U32.t { lk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid (parse_vclist min max lp p) h input pos))
  (ensures (
    valid lp h input pos /\ (
    let len = contents lp h input pos in
    let pos1 = get_valid_pos lp h input pos in
    let x = contents (parse_vclist min max lp p) h input pos in
    L.length x == U32.v len /\
    valid_content_pos (parse_nlist (U32.v len) p) h input pos1 x (get_valid_pos (parse_vclist min max lp p) h input pos)
  )))
= valid_facts (parse_vclist min max lp p) h input pos;
  parse_vclist_eq min max lp p (bytes_of_slice_from h input pos);
  valid_facts lp h input pos;
  let len = contents lp h input pos in
  let pos1 = get_valid_pos lp h input pos in
  valid_facts (parse_nlist (U32.v len) p) h input pos1

#push-options "--z3rlimit 20"
let valid_vclist_intro
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#lk: parser_kind)
  (lp: parser lk U32.t { lk.parser_kind_subkind == Some ParserStrong })
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid lp h input pos /\ (
    let pos1 = get_valid_pos lp h input pos in
    let len = contents lp h input pos in
    min <= U32.v len /\ U32.v len <= max /\
    valid (parse_nlist (U32.v len) p) h input pos1
  )))
  (ensures (
    let pos1 = get_valid_pos lp h input pos in
    let len = contents lp h input pos in
    valid_content_pos (parse_vclist min max lp p) h input pos (contents (parse_nlist (U32.v len) p) h input pos1) (get_valid_pos (parse_nlist (U32.v len) p) h input pos1)
  ))
= valid_facts (parse_vclist min max lp p) h input pos;
  parse_vclist_eq min max lp p (bytes_of_slice_from h input pos);
  valid_facts lp h input pos;
  let len = contents lp h input pos in
  let pos1 = get_valid_pos lp h input pos in
  valid_facts (parse_nlist (U32.v len) p) h input pos1
#pop-options

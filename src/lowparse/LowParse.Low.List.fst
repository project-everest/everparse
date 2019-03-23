module LowParse.Low.List

include LowParse.Spec.List
include LowParse.Low.Base

module B = LowStar.Buffer
module U32 = FStar.UInt32
module CL = C.Loops
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module G = FStar.Ghost

let valid_exact_list_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
: Lemma
  (requires (U32.v pos <= U32.v sl.len /\ live_slice h sl))
  (ensures (
    valid_exact (parse_list p) h sl pos pos /\
    contents_exact (parse_list p) h sl pos pos == []
  ))
= parse_list_eq p (B.as_seq h (B.gsub sl.base pos 0ul));
  valid_exact_equiv (parse_list p) h sl pos pos;
  contents_exact_eq (parse_list p) h sl pos pos

let valid_exact_list_cons
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid p h sl pos /\
    valid_exact (parse_list p) h sl (get_valid_pos p h sl pos) pos'
  ))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid p h sl pos /\
    valid_exact (parse_list p) h sl (get_valid_pos p h sl pos) pos' /\
    valid_exact (parse_list p) h sl pos pos' /\
    contents_exact (parse_list p) h sl pos pos' == contents p h sl pos :: contents_exact (parse_list p) h sl (get_valid_pos p h sl pos) pos'
  ))
= let sq = B.as_seq h (B.gsub sl.base pos (pos' `U32.sub` pos)) in
  parse_list_eq' p sq;
  let pos1 = get_valid_pos p h sl pos in
  valid_exact_equiv (parse_list p) h sl pos pos';
  valid_facts p h sl pos;
  let sq0 = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
  parser_kind_prop_equiv k p;
  assert (no_lookahead_on p sq0 sq);
  assert (injective_postcond p sq0 sq);
  valid_exact_equiv (parse_list p) h sl pos1 pos';  
  contents_exact_eq (parse_list p) h sl pos pos';
  contents_exact_eq (parse_list p) h sl pos1 pos'

abstract
let rec valid_list_valid_exact_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    valid_list p h sl pos pos'
  ))
  (ensures (
    valid_exact (parse_list p) h sl pos pos' /\
    contents_exact (parse_list p) h sl pos pos' == contents_list p h sl pos pos'
  ))
  (decreases (U32.v pos' - U32.v pos))
= valid_list_equiv p h sl pos pos';
  contents_list_eq p h sl pos pos' ;
  if pos = pos'
  then valid_exact_list_nil p h sl pos
  else begin
    let pos1 = get_valid_pos p h sl pos in
    valid_list_valid_exact_list p h sl pos1 pos';
    valid_exact_list_cons p h sl pos pos'
  end

let valid_exact_list_cons_recip
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    pos <> pos' /\
    valid_exact (parse_list p) h sl pos pos'
  ))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    pos <> pos' /\
    valid_exact (parse_list p) h sl pos pos' /\
    valid p h sl pos /\ (
    let pos1 = get_valid_pos p h sl pos in
    valid_exact (parse_list p) h sl pos1 pos' /\
    contents_exact (parse_list p) h sl pos pos' == contents p h sl pos :: contents_exact (parse_list p) h sl pos1 pos'
  )))
= let sq = B.as_seq h (B.gsub sl.base pos (pos' `U32.sub` pos)) in
  parse_list_eq p sq;
  valid_exact_equiv (parse_list p) h sl pos pos';
  valid_facts p h sl pos;
  let sq0 = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
  parser_kind_prop_equiv k p;
  assert (no_lookahead_on p sq sq0);
  assert (injective_postcond p sq sq0);
  let pos1 = get_valid_pos p h sl pos in
  valid_exact_equiv (parse_list p) h sl pos1 pos';  
  contents_exact_eq (parse_list p) h sl pos pos';
  contents_exact_eq (parse_list p) h sl pos1 pos'

abstract
let rec valid_exact_list_valid_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid_exact (parse_list p) h sl pos pos'
  ))
  (ensures (
    valid_list p h sl pos pos' /\
    contents_exact (parse_list p) h sl pos pos' == contents_list p h sl pos pos'
  ))
  (decreases (U32.v pos' - U32.v pos))
= valid_list_equiv p h sl pos pos';
  if pos = pos'
  then
    valid_exact_list_nil p h sl pos
  else begin
    valid_exact_list_cons_recip p h sl pos pos';
    let pos1 = get_valid_pos p h sl pos in
    valid_exact_list_valid_list p h sl pos1 pos'
  end;
  contents_list_eq p h sl pos pos'

module L = FStar.List.Tot

abstract
let rec valid_exact_list_append
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos1 pos2 pos3 : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid_exact (parse_list p) h sl pos1 pos2 /\
    valid_exact (parse_list p) h sl pos2 pos3
  ))
  (ensures (
    valid_exact (parse_list p) h sl pos1 pos3 /\
    contents_exact (parse_list p) h sl pos1 pos3 == contents_exact (parse_list p) h sl pos1 pos2 `L.append` contents_exact (parse_list p) h sl pos2 pos3
  ))
  (decreases (U32.v pos2 - U32.v pos1))
= if pos1 = pos2
  then
    valid_exact_list_nil p h sl pos1
  else begin
    valid_exact_list_cons_recip p h sl pos1 pos2;
    let pos15 = get_valid_pos p h sl pos1 in
    valid_exact_list_append p h sl pos15 pos2 pos3;
    valid_exact_list_cons p h sl pos1 pos3
  end


let validate_list_inv
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (g0 g1: G.erased HS.mem)
  (sl: slice)
  (pos0: U32.t)
  (bpos: B.pointer U32.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let h0 = G.reveal g0 in
  let h1 = G.reveal g1 in
  B.disjoint sl.base bpos /\
  k.parser_kind_subkind == Some ParserStrong /\
  k.parser_kind_low > 0 /\
  U32.v pos0 <= U32.v sl.len /\
  U32.v sl.len <= U32.v validator_max_length /\
  live_slice h0 sl /\
  B.live h1 bpos /\
  B.modifies B.loc_none h0 h1 /\
  B.modifies (B.loc_buffer bpos) h1 h /\ (
  let pos1 = Seq.index (B.as_seq h bpos) 0 in
  if
    U32.v pos1 > U32.v validator_max_length
  then
    stop == true /\
    (~ (valid_exact (parse_list p) h0 sl pos0 sl.len))
  else
    U32.v pos0 <= U32.v pos1 /\
    U32.v pos1 <= U32.v sl.len /\
    (valid_exact (parse_list p) h0 sl pos0 sl.len <==> valid_exact (parse_list p) h0 sl pos1 sl.len) /\
    (stop == true ==> pos1 == sl.len)
  )

inline_for_extraction
let validate_list_body
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (g0 g1: G.erased HS.mem)
  (sl: slice)
  (pos0: U32.t)
  (bpos: B.pointer U32.t)
: HST.Stack bool
  (requires (fun h -> validate_list_inv p g0 g1 sl pos0 bpos h false))
  (ensures (fun h res h' ->
    validate_list_inv p g0 g1 sl pos0 bpos h false /\
    validate_list_inv p g0 g1 sl pos0 bpos h' res
  ))
= let pos1 = B.index bpos 0ul in
  assert (U32.v pos1 <= U32.v sl.len);
  if pos1 = sl.len
  then true
  else begin
    Classical.move_requires (valid_exact_list_cons p (G.reveal g0) sl pos1) sl.len;
    Classical.move_requires (valid_exact_list_cons_recip p (G.reveal g0) sl pos1) sl.len;
    let pos1 = v sl pos1 in
    B.upd bpos 0ul pos1;
    pos1 `U32.gt` validator_max_length
  end

inline_for_extraction
let validate_list'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (sl: slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    U32.v pos <= U32.v sl.len /\
    U32.v sl.len <= U32.v validator_max_length /\
    live_slice h sl
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    (* we could return a boolean, but we would like to return the last
       validation error code if it fails. (alas, we cannot capture
       that fact in the spec.) *)
    (U32.v res <= U32.v validator_max_length <==> valid_exact (parse_list p) h sl pos sl.len)
  ))
= let h0 = HST.get () in
  let g0 = G.hide h0 in
  HST.push_frame ();
  let h02 = HST.get () in
  B.fresh_frame_modifies h0 h02;
  let bpos = B.alloca pos 1ul in
  let h1 = HST.get () in
  let g1 = G.hide h1 in
  C.Loops.do_while (validate_list_inv p g0 g1 sl pos bpos) (fun _ -> validate_list_body v g0 g1 sl pos bpos);
  valid_exact_list_nil p h0 sl sl.len;
  let posf = B.index bpos 0ul in
  HST.pop_frame ();
  posf

inline_for_extraction
let validate_list
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (u: squash (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0
  ))
: Tot (validator (parse_list p))
= fun
  (sl: slice)
  (pos: U32.t) ->
  let h = HST.get () in
  valid_valid_exact_consumes_all (parse_list p) h sl pos;
  let error = validate_list' v sl pos in 
  if error `U32.lte` validator_max_length
  then sl.len
  else error

(*
#reset-options "--z3rlimit 128 --max_fuel 16 --max_ifuel 16 --z3cliopt smt.arith.nl=false"

inline_for_extraction
val list_is_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
  (len: I32.t)
: HST.Stack bool
  (requires (fun h ->
    is_slice h input len /\
    Some? (parse (parse_list p) (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    h == h' /\ (
    let Some (v, _) = parse (parse_list p) (B.as_seq h input) in
    res == true <==> v == []
  )))

let list_is_nil #k #t p input len =
  len = 0l

/// TODO: generalize accessors with conditions

inline_for_extraction
let list_head
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
: HST.Stack buffer8
  (requires (fun h ->
    B.live h input /\ (
    let ps = parse (parse_list p) (B.as_seq h input) in
    Some? ps /\ (
    let Some (v, _) = ps in
    Cons? v
  ))))
  (ensures (fun h res h' ->
    M.modifies (M.loc_none) h h' /\
    B.live h' input /\
    B.includes input res /\ (
    let Some ((v::_), _) = parse (parse_list p) (B.as_seq h input) in
    let ps = parse p (B.as_seq h res) in
    Some? ps /\ (
    let (Some (v', _)) = ps in
    v' == v
  ))))
= input

inline_for_extraction
let list_tail
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator_nochk32 p)
  (input: buffer8)
: HST.Stack buffer8
  (requires (fun h ->
    B.live h input /\ (
    let ps = parse (parse_list p) (B.as_seq h input) in
    Some? ps /\ (
    let Some (v, _) = ps in
    Cons? v
  ))))
  (ensures (fun h res h' ->
    M.modifies (M.loc_none) h h' /\
    B.live h' input /\ (
    let Some ((_::v), _) = parse (parse_list p) (B.as_seq h input) in
    let ps = parse (parse_list p) (B.as_seq h res) in
    Some? ps /\ (
    let (Some (v', _)) = ps in
    v == v'
  ))))
= B.offset input (v input)

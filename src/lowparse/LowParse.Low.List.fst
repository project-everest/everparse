module LowParse.Low.List

include LowParse.Spec.List
include LowParse.Low.Base

module B = LowStar.Buffer
module U32 = FStar.UInt32
module CL = C.Loops
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module G = FStar.Ghost
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

let valid_exact_list_nil
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos : U32.t)
: Lemma
  (requires (U32.v pos <= U32.v sl.len /\ live_slice h sl))
  (ensures (
    valid_exact (parse_list p) h sl pos pos /\
    contents_exact (parse_list p) h sl pos pos == []
  ))
= parse_list_eq p (bytes_of_slice_from_to h sl pos pos);
  valid_exact_equiv (parse_list p) h sl pos pos;
  contents_exact_eq (parse_list p) h sl pos pos

let valid_list_intro_nil
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos : U32.t)
: Lemma
  (requires (U32.v pos == U32.v sl.len /\ live_slice h sl))
  (ensures (
    valid (parse_list p) h sl pos /\
    contents (parse_list p) h sl pos == []
  ))
= parse_list_eq p (bytes_of_slice_from h sl pos);
  valid_equiv (parse_list p) h sl pos;
  contents_eq (parse_list p) h sl pos

let valid_exact_list_cons
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
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
= let sq = bytes_of_slice_from_to h sl pos pos' in
  parse_list_eq' p sq;
  let pos1 = get_valid_pos p h sl pos in
  valid_exact_equiv (parse_list p) h sl pos pos';
  valid_facts p h sl pos;
  let sq0 = bytes_of_slice_from h sl pos in
  parser_kind_prop_equiv k p;
  assert (no_lookahead_on p sq0 sq);
  assert (injective_postcond p sq0 sq);
  valid_exact_equiv (parse_list p) h sl pos1 pos';  
  contents_exact_eq (parse_list p) h sl pos pos';
  contents_exact_eq (parse_list p) h sl pos1 pos'

let valid_list_intro_cons
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos : U32.t)
: Lemma
  (requires (
    U32.v pos < U32.v sl.len /\
    valid p h sl pos /\
    valid (parse_list p) h sl (get_valid_pos p h sl pos)
  ))
  (ensures (
    valid p h sl pos /\
    valid (parse_list p) h sl (get_valid_pos p h sl pos) /\
    valid (parse_list p) h sl pos /\
    contents (parse_list p) h sl pos == contents p h sl pos :: contents (parse_list p) h sl (get_valid_pos p h sl pos)
  ))
= let sq = bytes_of_slice_from h sl pos in
  parse_list_eq p sq;
  let pos1 = get_valid_pos p h sl pos in
  valid_facts (parse_list p) h sl pos;
  valid_facts p h sl pos;
  valid_facts (parse_list p) h sl pos1

let valid_list_elim_cons
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos : U32.t)
: Lemma
  (requires (
    U32.v pos < U32.v sl.len /\
    valid (parse_list p) h sl pos
  ))
  (ensures (
    valid p h sl pos /\
    valid (parse_list p) h sl (get_valid_pos p h sl pos)
  ))
= let sq = bytes_of_slice_from h sl pos in
  parse_list_eq p sq;
  valid_facts (parse_list p) h sl pos;
  valid_facts p h sl pos;
  let pos1 = get_valid_pos p h sl pos in
  valid_facts (parse_list p) h sl pos1

let rec valid_list_valid_exact_list
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
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
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
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
= let sq = bytes_of_slice_from_to h sl pos pos' in
  parse_list_eq p sq;
  valid_exact_equiv (parse_list p) h sl pos pos';
  valid_facts p h sl pos;
  let sq0 = bytes_of_slice_from h sl pos in
  parser_kind_prop_equiv k p;
  assert (no_lookahead_on p sq sq0);
  assert (injective_postcond p sq sq0);
  let pos1 = get_valid_pos p h sl pos in
  valid_exact_equiv (parse_list p) h sl pos1 pos';  
  contents_exact_eq (parse_list p) h sl pos pos';
  contents_exact_eq (parse_list p) h sl pos1 pos'

let rec valid_exact_list_valid_list
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
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

let rec valid_exact_list_append
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
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
  (#t: Type)
  (p: parser k t)
  (g0 g1: G.erased HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos0: pos_t)
  (bpos: B.pointer U64.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let h0 = G.reveal g0 in
  let h1 = G.reveal g1 in
  B.disjoint sl.base bpos /\
  k.parser_kind_subkind == Some ParserStrong /\
  k.parser_kind_low > 0 /\
  U64.v pos0 <= U32.v sl.len /\
  live_slice h0 sl /\
  B.live h1 bpos /\
  B.modifies B.loc_none h0 h1 /\
  B.modifies (B.loc_buffer bpos) h1 h /\ (
  let pos1 = Seq.index (B.as_seq h bpos) 0 in
  if
    is_error pos1
  then
    stop == true /\
    (~ (valid_exact (parse_list p) h0 sl (uint64_to_uint32 pos0) sl.len))
  else
    U64.v pos0 <= U64.v pos1 /\
    U64.v pos1 <= U32.v sl.len /\
    (valid_exact (parse_list p) h0 sl (uint64_to_uint32 pos0) sl.len <==> valid_exact (parse_list p) h0 sl (uint64_to_uint32 pos1) sl.len) /\
    (stop == true ==> U64.v pos1 == U32.v sl.len)
  )

inline_for_extraction
let validate_list_body
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (g0 g1: G.erased HS.mem)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos0: pos_t)
  (bpos: B.pointer U64.t)
: HST.Stack bool
  (requires (fun h -> validate_list_inv p g0 g1 sl pos0 bpos h false))
  (ensures (fun h res h' ->
    validate_list_inv p g0 g1 sl pos0 bpos h false /\
    validate_list_inv p g0 g1 sl pos0 bpos h' res
  ))
= let pos1 = B.index bpos 0ul in
  assert (U64.v pos1 <= U32.v sl.len);
  if pos1 = Cast.uint32_to_uint64 sl.len
  then true
  else begin
    Classical.move_requires (valid_exact_list_cons p (G.reveal g0) sl (uint64_to_uint32 pos1)) sl.len;
    Classical.move_requires (valid_exact_list_cons_recip p (G.reveal g0) sl (uint64_to_uint32 pos1)) sl.len;
    let pos1 = v sl pos1 in
    B.upd bpos 0ul pos1;
    is_error pos1
  end

inline_for_extraction
let validate_list'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: pos_t)
: HST.Stack U64.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    U64.v pos <= U32.v sl.len /\
    live_slice h sl
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    (* we could return a boolean, but we would like to return the last
       validation error code if it fails. (alas, we cannot capture
       that fact in the spec.) *)
    (is_success res <==> valid_exact (parse_list p) h sl (uint64_to_uint32 pos) sl.len) /\
    (is_success res ==> U64.v res == U32.v sl.len)
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
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (u: squash (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0
  ))
: Tot (validator (parse_list p))
= fun
  (#rrel #rel: _)
  (sl: slice rrel rel)
  pos ->
  let h = HST.get () in
  valid_valid_exact_consumes_all (parse_list p) h sl (uint64_to_uint32 pos);
  validate_list' v sl pos

let rec serialized_list_length_eq_length_serialize_list
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (l: list t)
: Lemma
  (requires (
    serialize_list_precond k
  ))
  (ensures (serialized_list_length s l == Seq.length (serialize (serialize_list _ s) l)))
= match l with
  | [] ->
    serialize_list_nil _ s;
    serialized_list_length_nil s
  | a :: q ->
    serialize_list_cons _ s a q;
    serialized_list_length_cons s a q;
    serialized_list_length_eq_length_serialize_list s q;
    serialized_length_eq s a

#push-options "--z3rlimit 32"

inline_for_extraction
let rec list_last_pos
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (s: serializer p)
  (j: jumper p)
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
  (l: Ghost.erased (list t))
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    live_slice h sl /\
    U32.v pos <= U32.v pos' /\
    U32.v pos' <= U32.v sl.len /\
    bytes_of_slice_from_to h sl pos pos' `Seq.equal` serialize (serialize_list _ s) (Ghost.reveal l) /\
    Cons? (Ghost.reveal l)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + Seq.length (serialize (serialize_list _ s) (L.init (Ghost.reveal l))) == U32.v res
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let bgleft = B.alloca (Ghost.hide ([] <: list t)) 1ul in
  let bgright = B.alloca l 1ul in
  let bpos1 = B.alloca pos 1ul in
  serialize_list_nil _ s;
  let _ = C.Loops.do_while
    (fun h stop ->
      B.modifies (B.loc_region_only true (HS.get_tip h1)) h1 h /\
      B.live h bgleft /\
      B.live h bgright /\
      B.live h bpos1 /\ (
      let left = Ghost.reveal (Seq.index (B.as_seq h bgleft) 0) in
      let right = Ghost.reveal (Seq.index (B.as_seq h bgright) 0) in
      let pos1 = Seq.index (B.as_seq h bpos1) 0 in
      Ghost.reveal l == left `L.append` right /\
      U32.v pos + Seq.length (serialize (serialize_list _ s) left) == U32.v pos1 /\
      U32.v pos1 <= U32.v pos' /\
      bytes_of_slice_from_to h0 sl pos1 pos' `Seq.equal` serialize (serialize_list _ s) right /\
      Cons? right /\
      (stop == true ==> L.length right == 1)
    ))
    (fun _ ->
      let pos1 = B.index bpos1 0ul in
      let gright = B.index bgright 0ul in
      serialize_list_cons _ s (L.hd (Ghost.reveal gright)) (L.tl (Ghost.reveal gright));
      assert (bytes_of_slice_from h0 sl pos1 `seq_starts_with` bytes_of_slice_from_to h0 sl pos1 pos');
      let pos2 = jump_serializer s j sl pos1 (Ghost.hide (L.hd (Ghost.reveal gright))) in
      if pos2 = pos'
      then begin
        let f () : Lemma
          (Nil? (L.tl (Ghost.reveal gright)))
        = match L.tl (Ghost.reveal gright) with
          | [] -> ()
          | a :: q -> serialize_list_cons _ s a q   
        in
        f ();
        true
      end else begin
        let gleft = B.index bgleft 0ul in
        B.upd bgleft 0ul (Ghost.hide (Ghost.reveal gleft `L.append` [L.hd (Ghost.reveal gright)]));
        B.upd bgright 0ul (Ghost.hide (L.tl (Ghost.reveal gright)));
        B.upd bpos1 0ul pos2;
        L.append_assoc (Ghost.reveal gleft) [L.hd (Ghost.reveal gright)] (L.tl (Ghost.reveal gright));
        serialize_list_singleton _ s (L.hd (Ghost.reveal gright));
        serialize_list_append _ s (Ghost.reveal gleft) [L.hd (Ghost.reveal gright)];
        false
      end
    )
  in
  let res = B.index bpos1 0ul in
  let h = HST.get () in
  L.init_last_def (Ghost.reveal (Seq.index (B.as_seq h bgleft) 0)) (L.hd (Ghost.reveal (Seq.index (B.as_seq h bgright) 0)));
  HST.pop_frame ();
  res

#pop-options

(*
#reset-options "--z3rlimit 128 --max_fuel 16 --max_ifuel 16 --z3cliopt smt.arith.nl=false"

inline_for_extraction
val list_is_nil
  (#k: parser_kind)
  (#t: Type)
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
  (#t: Type)
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
  (#t: Type)
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



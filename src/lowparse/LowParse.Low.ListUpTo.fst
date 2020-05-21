module LowParse.Low.ListUpTo
include LowParse.Spec.ListUpTo
include LowParse.Low.Base

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

unfold
let validate_list_up_to_inv
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (cond: (t -> Tot bool))
  (prf: consumes_if_not_cond cond p { k.parser_kind_subkind <> Some ParserConsumesAll } )
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos0: U32.t)
  (h0: HS.mem)
  (bpos: B.pointer U64.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let pos = B.deref h bpos in
  let q = parse_list_up_to cond p prf in
  B.live h0 bpos /\
  live_slice h0 sl /\
  B.loc_disjoint (B.loc_buffer sl.base) (B.loc_buffer bpos) /\
  B.modifies (B.loc_buffer bpos) h0 h /\
  U32.v pos0 <= U64.v pos /\
  begin if is_success pos
  then
    let pos = uint64_to_uint32 pos in
    U32.v pos <= U32.v sl.len /\
    begin if stop
    then
      valid_pos q h0 sl pos0 pos
    else
      (valid q h0 sl pos0 <==> valid q h0 sl pos) /\
      ((valid q h0 sl pos0 /\ valid q h0 sl pos) ==>
        get_valid_pos q h0 sl pos0 == get_valid_pos q h0 sl pos
      )
    end
  else
    stop == true /\
    (~ (valid q h0 sl pos0))
  end

#push-options "--z3rlimit 16"

inline_for_extraction
let validate_list_up_to_body
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (cond: (t -> Tot bool))
  (prf: consumes_if_not_cond cond p { k.parser_kind_subkind <> Some ParserConsumesAll } )
  (v: validator p)
  (cond_impl: (
    (#rrel: _) ->
    (#rel: _) ->
    (sl: slice rrel rel) ->
    (pos: U32.t) ->
    HST.Stack bool
    (requires (fun h -> valid p h sl pos))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      valid p h sl pos /\
      res == cond (contents p h sl pos)
    ))
  ))
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos0: U32.t)
  (h0: HS.mem)
  (bpos: B.pointer U64.t)
: HST.Stack bool
  (requires (fun h ->
    validate_list_up_to_inv cond prf sl pos0 h0 bpos h false
  ))
  (ensures (fun h stop h' ->
    validate_list_up_to_inv cond prf sl pos0 h0 bpos h false /\
    validate_list_up_to_inv cond prf sl pos0 h0 bpos h' stop
  ))
=
  let h = HST.get () in
  let pos = B.index bpos 0ul in
  valid_facts (parse_list_up_to cond p prf) h sl (uint64_to_uint32 pos);
  parse_list_up_to_eq cond p prf (bytes_of_slice_from h sl (uint64_to_uint32 pos));
  valid_facts p h sl (uint64_to_uint32 pos);
  let pos1 = v sl pos in
  B.upd bpos 0ul pos1;
  if is_error pos1
  then 
    true
  else begin
    valid_facts (parse_list_up_to cond p prf) h sl (uint64_to_uint32 pos1);
    cond_impl sl (uint64_to_uint32 pos)
  end

#pop-options

inline_for_extraction
let validate_list_up_to
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (cond: (t -> Tot bool))
  (prf: consumes_if_not_cond cond p { k.parser_kind_subkind <> Some ParserConsumesAll } )
  (v: validator p)
  (cond_impl: (
    (#rrel: _) ->
    (#rel: _) ->
    (sl: slice rrel rel) ->
    (pos: U32.t) ->
    HST.Stack bool
    (requires (fun h -> valid p h sl pos))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      valid p h sl pos /\
      res == cond (contents p h sl pos)
    ))
  ))
: Tot (validator (parse_list_up_to cond p prf))
= fun #rrel #rel sl pos ->
  HST.push_frame ();
  let bpos = B.alloca pos 1ul in
  let h2 = HST.get () in
  C.Loops.do_while
    (validate_list_up_to_inv cond prf sl (uint64_to_uint32 pos) h2 bpos)
    (fun _ -> validate_list_up_to_body cond prf v cond_impl sl (uint64_to_uint32 pos) h2 bpos)
    ;
  let res = B.index bpos 0ul in
  HST.pop_frame ();
  res

unfold
let jump_list_up_to_inv
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (cond: (t -> Tot bool))
  (prf: consumes_if_not_cond cond p { k.parser_kind_subkind <> Some ParserConsumesAll } )
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos0: U32.t)
  (h0: HS.mem)
  (bpos: B.pointer U32.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let pos = B.deref h bpos in
  let q = parse_list_up_to cond p prf in
  B.live h0 bpos /\
  live_slice h0 sl /\
  B.loc_disjoint (B.loc_buffer sl.base) (B.loc_buffer bpos) /\
  B.modifies (B.loc_buffer bpos) h0 h /\
  U32.v pos0 <= U32.v pos /\
  valid q h0 sl pos0 /\
  begin if stop
  then 
    get_valid_pos q h0 sl pos0 == pos
  else
    valid q h0 sl pos /\
    get_valid_pos q h0 sl pos0 == get_valid_pos q h0 sl pos
  end

#push-options "--z3rlimit 16"

inline_for_extraction
let jump_list_up_to_body
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (cond: (t -> Tot bool))
  (prf: consumes_if_not_cond cond p { k.parser_kind_subkind <> Some ParserConsumesAll } )
  (j: jumper p)
  (cond_impl: (
    (#rrel: _) ->
    (#rel: _) ->
    (sl: slice rrel rel) ->
    (pos: U32.t) ->
    HST.Stack bool
    (requires (fun h -> valid p h sl pos))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      valid p h sl pos /\
      res == cond (contents p h sl pos)
    ))
  ))
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos0: U32.t)
  (h0: HS.mem)
  (bpos: B.pointer U32.t)
: HST.Stack bool
  (requires (fun h ->
    jump_list_up_to_inv cond prf sl pos0 h0 bpos h false
  ))
  (ensures (fun h stop h' ->
    jump_list_up_to_inv cond prf sl pos0 h0 bpos h false /\
    jump_list_up_to_inv cond prf sl pos0 h0 bpos h' stop
  ))
=
  let h = HST.get () in
  let pos = B.index bpos 0ul in
  valid_facts (parse_list_up_to cond p prf) h sl pos;
  parse_list_up_to_eq cond p prf (bytes_of_slice_from h sl pos);
  valid_facts p h sl pos;
  let pos1 = j sl pos in
  B.upd bpos 0ul pos1;
  valid_facts (parse_list_up_to cond p prf) h sl pos1;
  cond_impl sl pos

#pop-options

inline_for_extraction
let jump_list_up_to
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (cond: (t -> Tot bool))
  (prf: consumes_if_not_cond cond p { k.parser_kind_subkind <> Some ParserConsumesAll } )
  (j: jumper p)
  (cond_impl: (
    (#rrel: _) ->
    (#rel: _) ->
    (sl: slice rrel rel) ->
    (pos: U32.t) ->
    HST.Stack bool
    (requires (fun h -> valid p h sl pos))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      valid p h sl pos /\
      res == cond (contents p h sl pos)
    ))
  ))
: Tot (jumper (parse_list_up_to cond p prf))
= fun #rrel #rel sl pos ->
  HST.push_frame ();
  let bpos = B.alloca pos 1ul in
  let h2 = HST.get () in
  C.Loops.do_while
    (jump_list_up_to_inv cond prf sl pos h2 bpos)
    (fun _ -> jump_list_up_to_body cond prf j cond_impl sl pos h2 bpos)
    ;
  let res = B.index bpos 0ul in
  HST.pop_frame ();
  res

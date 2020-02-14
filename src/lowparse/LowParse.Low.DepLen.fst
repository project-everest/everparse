module LowParse.Low.DepLen
include LowParse.Spec.DepLen

include LowParse.Low.Base
include LowParse.Low.Combinators

module B = LowStar.Monotonic.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

let valid_exact_valid_pos_equiv
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  #rrel #rel
  (input: slice rrel rel)
  (pos_begin: U32.t)
  (pos_end: U32.t)
: Lemma
  (requires live_slice h input)
  (ensures
    ((valid_exact p h input pos_begin pos_end)
    <==>
    (U32.v pos_begin <= U32.v pos_end /\
    U32.v pos_end <= U32.v input.len /\
    (let input' = { base = input.base; len = pos_end; } in
    valid_pos p h input' pos_begin pos_end))))
= valid_exact_equiv p h input pos_begin pos_end;
  if U32.v pos_begin <= U32.v pos_end && U32.v pos_end <= U32.v input.len then
  begin
    let input' = { base = input.base; len = pos_end; } in
    valid_facts p h input' pos_begin
  end

(* the validity lemma says it is equivalent to have a valid header followed by a valid payload and
   have a valid piece of deplen data *)

let valid_deplen_decomp
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#hk: parser_kind)
  (#ht: Type)
  (hp: parser hk ht)
  (dlf: ht -> Tot (bounded_int32 min max) )
  (#pk: parser_kind)
  (#pt: Type)
  (pp: parser pk pt)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
= valid hp h input pos /\ 
    (let pos_payload = get_valid_pos hp h input pos in
    let len = dlf (contents hp h input pos) in
    U32.v pos_payload + U32.v len <= U32.v input.len /\ 
    valid_exact pp h input pos_payload (pos_payload `U32.add` len))

let valid_deplen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#hk: parser_kind)
  (#ht: Type)
  (hp: parser hk ht)
  (dlf: ht -> Tot (bounded_int32 min max) )
  (#pk: parser_kind)
  (#pt: Type)
  (#pp: parser pk pt)
  (ps: serializer pp)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires live_slice h input)
  (ensures 
    ((valid (parse_deplen min max hp dlf ps) h input pos)
    <==>
    (valid_deplen_decomp min max hp dlf pp input pos h)))
= valid_facts (parse_deplen min max hp dlf ps) h input pos;
  valid_facts hp h input pos;
  parse_deplen_unfold2 min max hp dlf ps (bytes_of_slice_from h input pos);
  if valid_dec hp h input pos then
  begin
    let pos_payload = get_valid_pos hp h input pos in
    let len = dlf (contents hp h input pos) in
    if U32.v pos_payload + U32.v len <= U32.v input.len then
    begin
      let pos_end = pos_payload `U32.add` len in
      valid_exact_equiv pp h input pos_payload pos_end;
      match parse pp (bytes_of_slice_from_to h input pos_payload pos_end) with
      | None -> ()
      | Some (_, consumed) -> if consumed = U32.v len then
        valid_exact_serialize ps h input pos_payload pos_end
    end
  end

let valid_deplen_len
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#hk: parser_kind)
  (#ht: Type)
  (hp: parser hk ht)
  (dlf: ht -> Tot (bounded_int32 min max) )
  (#pk: parser_kind)
  (#pt: Type)
  (#pp: parser pk pt)
  (ps: serializer pp)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (valid (parse_deplen min max hp dlf ps) h input pos) /\
            (valid_deplen_decomp min max hp dlf pp input pos h))
  (ensures (let pos_payload = get_valid_pos hp h input pos in
           let len_payload = dlf (contents hp h input pos) in
           let input' = { base = input.base; len = (pos_payload `U32.add` len_payload); } in
           valid pp h input' pos_payload /\
           (let pos_end' = get_valid_pos pp h input' pos_payload in
           let pos_end = get_valid_pos (parse_deplen min max hp dlf ps) h input pos in
           pos_end == pos_end')))
= valid_facts (parse_deplen min max hp dlf ps) h input pos;
  valid_facts hp h input pos;
  parse_deplen_unfold2 min max hp dlf ps (bytes_of_slice_from h input pos);
  if valid_dec hp h input pos then
  begin
    let pos_payload = get_valid_pos hp h input pos in
    let len = dlf (contents hp h input pos) in
    if U32.v pos_payload + U32.v len <= U32.v input.len then
    begin
      let pos_end = pos_payload `U32.add` len in
      valid_exact_equiv pp h input pos_payload pos_end;      
      valid_exact_valid_pos_equiv pp h input pos_payload pos_end;
      let input' = { base = input.base; len = pos_end; } in
      valid_pos_get_valid_pos pp h input' pos_payload pos_end
    end
  end

inline_for_extraction
let deplen_func
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (dlf: t -> Tot (bounded_int32 min max) )
: Tot Type
= (#rrel: _) -> (#rel: _) ->
  (input: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack (bounded_int32 min max)
  (requires (fun h -> valid p h input pos))
  (ensures (fun h res h' -> res == dlf (contents p h input pos) /\ B.modifies B.loc_none h h'))


(* the validator for deplen data first validates the header then the payload *)

inline_for_extraction
let validate_deplen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#hk: parser_kind)
  (#ht: Type)
  (#hp: parser hk ht)
  (hv: validator hp)
  (dlf: ht -> Tot (bounded_int32 min max))
  (dlfc: deplen_func min max hp dlf)
  (#pk: parser_kind)
  (#pt: Type)
  (#pp: parser pk pt)
  (ps: serializer pp)
  (pv: validator pp)
: Tot (validator (parse_deplen min max hp dlf ps))
= fun #rrel #rel (input: slice rrel rel) pos ->
  let h = HST.get () in
    let _ = 
      valid_deplen min max hp dlf ps input (uint64_to_uint32 pos) h
    in
  let pos_payload = hv input pos in
  if is_error pos_payload then
    pos_payload
  else
    let payload_len = dlfc input (uint64_to_uint32 pos) in
    if (Cast.uint32_to_uint64 input.len `U64.sub` pos_payload) `U64.lt` Cast.uint32_to_uint64 payload_len then
      validator_error_not_enough_data
    else
      let pos_end = uint64_to_uint32 pos_payload `U32.add` payload_len in
      let _ = valid_exact_valid_pos_equiv pp h input (uint64_to_uint32 pos_payload) pos_end in
      [@inline_let] let input' = { base = input.base; len = pos_end; } in
      let pos_end' = pv input' pos_payload in
      if is_error pos_end' then
        pos_end'
      else
        if uint64_to_uint32 pos_end' = pos_end then
          let _ = valid_deplen_len min max hp dlf ps input (uint64_to_uint32 pos) h in
          pos_end'
        else
          validator_error_generic 

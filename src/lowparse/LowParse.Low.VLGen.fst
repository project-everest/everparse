module LowParse.Low.VLGen
include LowParse.Spec.VLGen
include LowParse.Low.VLData

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

#reset-options "--z3cliopt smt.arith.nl=false"

let valid_bounded_vlgen'
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (vmin) (vmax)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid (parse_fldata_strong s (U32.v len)) h input pos1
  )))
  (ensures (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    valid (parse_fldata_strong s (U32.v len)) h input pos1 /\ (
    let x = contents (parse_fldata_strong s (U32.v len)) h input pos1 in
    Seq.length (serialize s x) == U32.v len /\
    valid_content_pos (parse_bounded_vlgen vmin vmax pk s) h input pos x (pos1 `U32.add` len)
  ))))
= valid_facts (parse_bounded_vlgen (vmin) (vmax) pk s) h input pos;
  parse_bounded_vlgen_unfold_aux (vmin) (vmax) pk s (bytes_of_slice_from h input pos);
  valid_facts pk h input pos;
  let pos1 = get_valid_pos pk h input pos in
  let len = contents pk h input pos in
  valid_facts (parse_fldata_strong s (U32.v len)) h input pos1

let valid_bounded_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (vmin) (vmax)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid_exact p h input pos1 (pos1 `U32.add` len)
  )))
  (ensures (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid_exact p h input pos1 (pos1 `U32.add` len) /\ (
    let x = contents_exact p h input pos1 (pos1 `U32.add` len) in
    Seq.length (serialize s x) == U32.v len /\
    valid_content_pos (parse_bounded_vlgen vmin vmax pk s) h input pos x (pos1 `U32.add` len)
  ))))
= valid_facts (parse_bounded_vlgen (vmin) (vmax) pk s) h input pos;
  parse_bounded_vlgen_unfold (vmin) (vmax) pk s (bytes_of_slice_from h input pos);
  valid_facts pk h input pos;
  let pos1 = get_valid_pos pk h input pos in
  let len = contents pk h input pos in
  let pos2 = pos1 `U32.add` len in
  let x = contents_exact p h input pos1 pos2 in
  valid_fldata_gen p (U32.v len) input pos1 h;
  serialized_length_eq s x;
  valid_exact_serialize s h input pos1 pos2

let valid_bounded_vlgen_elim'
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (vmin) (vmax)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    valid (parse_bounded_vlgen vmin vmax pk s) h input pos
  ))
  (ensures (
    valid (parse_bounded_vlgen vmin vmax pk s) h input pos /\
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid (parse_fldata_strong s (U32.v len)) h input pos1 /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    let x = contents (parse_fldata_strong s (U32.v len)) h input pos1 in
    Seq.length (serialize s x) == U32.v len /\
    valid_content_pos (parse_bounded_vlgen vmin vmax pk s) h input pos x (pos1 `U32.add` len)
  ))))
= valid_facts (parse_bounded_vlgen (vmin) (vmax) pk s) h input pos;
  parse_bounded_vlgen_unfold_aux (vmin) (vmax) pk s (bytes_of_slice_from h input pos);
  valid_facts pk h input pos;
  let pos1 = get_valid_pos pk h input pos in
  let len = contents pk h input pos in
  valid_facts (parse_fldata_strong s (U32.v len)) h input pos1

let valid_bounded_vlgen_elim
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (vmin) (vmax)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    valid (parse_bounded_vlgen vmin vmax pk s) h input pos
  ))
  (ensures (
    valid (parse_bounded_vlgen vmin vmax pk s) h input pos /\
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid_exact p h input pos1 (pos1 `U32.add` len) /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    let x = contents_exact p h input pos1 (pos1 `U32.add` len) in
    Seq.length (serialize s x) == U32.v len /\
    valid_content_pos (parse_bounded_vlgen vmin vmax pk s) h input pos x (pos1 `U32.add` len)
  ))))
= valid_facts (parse_bounded_vlgen (vmin) (vmax) pk s) h input pos;
  parse_bounded_vlgen_unfold (vmin) (vmax) pk s (bytes_of_slice_from h input pos);
  valid_facts pk h input pos;
  let pos1 = get_valid_pos pk h input pos in
  let len = contents pk h input pos in
  let pos2 = pos1 `U32.add` len in
  valid_facts (parse_fldata p (U32.v len)) h input pos1;
  valid_fldata_gen_elim p (U32.v len) input pos1 h;
  valid_exact_serialize s h input pos1 pos2

inline_for_extraction
let finalize_bounded_vlgen_exact
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (sz32: U32.t)
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (min) (max)))
  (#ssk: serializer pk)
  (wk: leaf_writer_strong ssk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    let sz = U32.v sz32 in
    sk.parser_kind_low == sz /\
    sk.parser_kind_high == Some sz /\
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` sz32 in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    let len_ser = Seq.length (serialize s (contents_exact p h input pos_payload pos')) in
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    ((min <= U32.v len_payload /\ U32.v len_payload <= max) \/ (min <= len_ser /\ len_ser <= max))
  ))))
  (ensures (fun h _ h' ->
    let sz = U32.v sz32 in
    let x = contents_exact p h input (pos `U32.add` sz32) pos' in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` sz32)) h h' /\
    Seq.length (serialize s x) == U32.v pos'  - (U32.v pos + sz) /\
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vlgen min max pk s) h' input pos x pos'
  ))
= [@inline_let]
  let len_payload = pos' `U32.sub` (pos `U32.add` sz32) in
  let h = HST.get () in
  [@inline_let]
  let _ =
    serialized_length_eq s (contents_exact p h input (pos `U32.add` sz32) pos');
    valid_exact_serialize s h input (pos `U32.add` sz32) pos'
  in
  let _ = wk len_payload input pos in
  let h = HST.get () in
  valid_bounded_vlgen min max pk s input pos h

inline_for_extraction
let finalize_bounded_vlgen
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (sz32: U32.t)
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (min) (max)))
  (#ssk: serializer pk)
  (wk: leaf_writer_strong ssk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    let sz = U32.v sz32 in
    sk.parser_kind_low == sz /\
    sk.parser_kind_high == Some sz /\
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos p h input pos_payload pos' /\
    k.parser_kind_subkind == Some ParserStrong /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    let len_ser = Seq.length (serialize s (contents p h input pos_payload)) in
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    ((min <= U32.v len_payload /\ U32.v len_payload <= max) \/ (min <= len_ser /\ len_ser <= max))
  ))))
  (ensures (fun h _ h' ->
    let x = contents p h input (pos `U32.add` sz32) in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` sz32)) h h' /\
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vlgen min max pk s) h' input pos x pos'
  ))
= let h = HST.get () in
  [@inline_let]
  let _ =
    let pos_payload = pos `U32.add` sz32 in
    valid_pos_valid_exact p h input pos_payload pos'
  in
  finalize_bounded_vlgen_exact min max sz32 wk s input pos pos'

inline_for_extraction
let validate_bounded_vlgen
  (vmin: der_length_t)
  (min: U32.t { U32.v min == vmin } )
  (vmax: der_length_t)
  (max: U32.t { U32.v max == vmax /\ U32.v min <= U32.v max } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (vmin) (vmax)))
  (vk: validator pk)
  (rk: leaf_reader pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
: Tot (validator (parse_bounded_vlgen (vmin) (vmax) pk s))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    Classical.move_requires (valid_bounded_vlgen' vmin vmax pk s input (uint64_to_uint32 pos)) h;
    Classical.move_requires (valid_bounded_vlgen_elim' vmin vmax pk s input (uint64_to_uint32 pos)) h
  in
  let n = vk input pos in
  if is_error n
  then n
  else begin
    let len = rk input (uint64_to_uint32 pos) in
    validate_fldata_strong s v (U32.v len) len input n
  end

let valid_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (vmin) (vmax)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (vmin) (vmax) k })
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid_exact p h input pos1 (pos1 `U32.add` len)
  )))
  (ensures (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    let x = contents_exact p h input pos1 (pos1 `U32.add` len) in
    Seq.length (serialize s x) == U32.v len /\
    valid_content_pos (parse_vlgen vmin vmax pk s) h input pos x (pos1 `U32.add` len)
  ))
= valid_bounded_vlgen vmin vmax pk s input pos h;
  valid_synth
    h
    (parse_bounded_vlgen vmin vmax pk s)
    (synth_vlgen (vmin) (vmax) s)
    input
    pos

inline_for_extraction
let finalize_vlgen_exact
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (sz32: U32.t)
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (min) (max)))
  (#ssk: serializer pk)
  (wk: leaf_writer_strong ssk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (min) (max) k })
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    let sz = U32.v sz32 in
    sk.parser_kind_low == sz /\
    sk.parser_kind_high == Some sz /\
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` sz32 in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    let len_ser = Seq.length (serialize s (contents_exact p h input pos_payload pos')) in
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    ((min <= U32.v len_payload /\ U32.v len_payload <= max) \/ (min <= len_ser /\ len_ser <= max))
  ))))
  (ensures (fun h _ h' ->
    let sz = U32.v sz32 in
    let x = contents_exact p h input (pos `U32.add` sz32) pos' in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` sz32)) h h' /\
    Seq.length (serialize s x) == U32.v pos'  - (U32.v pos + sz) /\
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_vlgen min max pk s) h' input pos x pos'
  ))
= [@inline_let]
  let len_payload = pos' `U32.sub` (pos `U32.add` sz32) in
  let h = HST.get () in
  [@inline_let]
  let _ =
    serialized_length_eq s (contents_exact p h input (pos `U32.add` sz32) pos');
    valid_exact_serialize s h input (pos `U32.add` sz32) pos'
  in
  let _ = wk len_payload input pos in
  let h = HST.get () in
  valid_vlgen min max pk s input pos h

inline_for_extraction
let finalize_vlgen
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (sz32: U32.t)
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (min) (max)))
  (#ssk: serializer pk)
  (wk: leaf_writer_strong ssk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (min) (max) k })
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    let sz = U32.v sz32 in
    sk.parser_kind_low == sz /\
    sk.parser_kind_high == Some sz /\
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos p h input pos_payload pos' /\
    k.parser_kind_subkind == Some ParserStrong /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    let len_ser = Seq.length (serialize s (contents p h input pos_payload)) in
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    ((min <= U32.v len_payload /\ U32.v len_payload <= max) \/ (min <= len_ser /\ len_ser <= max))
  ))))
  (ensures (fun h _ h' ->
    let x = contents p h input (pos `U32.add` sz32) in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` sz32)) h h' /\
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_vlgen min max pk s) h' input pos x pos'
  ))
= let h = HST.get () in
  [@inline_let]
  let _ =
    let pos_payload = pos `U32.add` sz32 in
    valid_pos_valid_exact p h input pos_payload pos'
  in
  finalize_vlgen_exact min max sz32 wk s input pos pos'

inline_for_extraction
let validate_vlgen
  (vmin: der_length_t)
  (min: U32.t { U32.v min == vmin } )
  (vmax: der_length_t)
  (max: U32.t { U32.v max == vmax /\ U32.v min <= U32.v max } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (vmin) (vmax)))
  (vk: validator pk)
  (rk: leaf_reader pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (U32.v min) (U32.v max) k })
  (v: validator p)
: Tot (validator (parse_vlgen (vmin) (vmax) pk s))
= validate_synth
    (validate_bounded_vlgen vmin min vmax max vk rk s v)
    (synth_vlgen (U32.v min) (U32.v max) s)
    ()

#push-options "--z3rlimit 16"

inline_for_extraction
let jump_bounded_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (vmin) (vmax)))
  (vk: jumper pk)
  (rk: leaf_reader pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (jumper (parse_bounded_vlgen (vmin) (vmax) pk s))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_bounded_vlgen (vmin) (vmax) pk s) h input pos;
    parse_bounded_vlgen_unfold (vmin) (vmax) pk s (bytes_of_slice_from h input pos);
    valid_facts pk h input pos
  in
  let n = vk input pos in
  let len = rk input pos in
  [@inline_let]
  let _ = valid_facts (parse_fldata_strong s (U32.v len)) h input n in
  jump_fldata_strong s (U32.v len) len input n

#pop-options

inline_for_extraction
let jump_vlgen
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 (vmin) (vmax)))
  (vk: jumper pk)
  (rk: leaf_reader pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (vmin) (vmax) k })
: Tot (jumper (parse_vlgen (vmin) (vmax) pk s))
= jump_synth
    (jump_bounded_vlgen vmin vmax vk rk s)
    (synth_vlgen (vmin) (vmax) s)
    ()

let gaccessor_bounded_vlgen_payload'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_subkind == Some ParserStrong})
: Tot (gaccessor' (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s))
= fun input ->
  parse_bounded_vlgen_unfold min max pk s input;
  let res =
    match parse pk input with
    | None -> (0) // dummy
    | Some (len, sz)  ->
      if sz + U32.v len <= Seq.length input
      then
        let input' = Seq.slice input sz (sz + U32.v len) in
        let _ = match parse p input' with
        | None -> ()
        | Some _ ->
          parse_strong_prefix p input' (Seq.slice input sz (Seq.length input))
        in
        sz
      else 0
  in
  res

let gaccessor_bounded_vlgen_payload_injective_1
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sl sl' : bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl' /\
    injective_precond (parse_bounded_vlgen min max pk s) sl sl'
  ))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl' /\
    injective_precond (parse_bounded_vlgen min max pk s) sl sl' /\
    gaccessor_bounded_vlgen_payload' min max pk s sl == gaccessor_bounded_vlgen_payload' min max pk s sl'
  ))
= parse_bounded_vlgen_unfold min max pk s sl;
  parse_bounded_vlgen_unfold min max pk s sl' ;
  parse_injective (parse_bounded_vlgen min max pk s) sl sl' ;
  parse_injective pk sl sl'

let gaccessor_bounded_vlgen_payload_injective_2
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sl sl' : bytes)
: Lemma
  (ensures ((
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl' /\
    injective_precond (parse_bounded_vlgen min max pk s) sl sl'
  ) ==> (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl' /\
    injective_precond (parse_bounded_vlgen min max pk s) sl sl' /\
    gaccessor_bounded_vlgen_payload' min max pk s sl == gaccessor_bounded_vlgen_payload' min max pk s sl'
  )))
= Classical.move_requires (gaccessor_bounded_vlgen_payload_injective_1 min max pk s sl) sl'

let gaccessor_bounded_vlgen_payload_no_lookahead_1
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sl sl' : bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    (and_then_kind sk k).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl' /\
    no_lookahead_on_precond (parse_bounded_vlgen min max pk s) sl sl'
  ))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_bounded_vlgen_payload' min max pk s sl == gaccessor_bounded_vlgen_payload' min max pk s sl'
  ))
= parse_bounded_vlgen_unfold min max pk s sl;
  parse_bounded_vlgen_unfold min max pk s sl' ;
  parse_strong_prefix (parse_bounded_vlgen min max pk s) sl sl' ;
  parse_injective pk sl sl'

let gaccessor_bounded_vlgen_payload_no_lookahead_2
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sl sl' : bytes)
: Lemma
  (ensures ((
    k.parser_kind_subkind == Some ParserStrong /\
    (and_then_kind sk k).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl /\
    gaccessor_pre (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) sl' /\
    no_lookahead_on_precond (parse_bounded_vlgen min max pk s) sl sl'
  ) ==> (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_bounded_vlgen_payload' min max pk s sl == gaccessor_bounded_vlgen_payload' min max pk s sl'
  )))
= Classical.move_requires (gaccessor_bounded_vlgen_payload_no_lookahead_1 min max pk s sl) sl'

let gaccessor_bounded_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_subkind == Some ParserStrong})
: Tot (gaccessor (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s))
= Classical.forall_intro_2 (gaccessor_bounded_vlgen_payload_no_lookahead_2 min max pk s);
  Classical.forall_intro_2 (gaccessor_bounded_vlgen_payload_injective_2 min max pk s);
  gaccessor_prop_equiv (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) (gaccessor_bounded_vlgen_payload' min max pk s);
  gaccessor_bounded_vlgen_payload' min max pk s

module B = LowStar.Buffer

inline_for_extraction
let accessor_bounded_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 ( min) ( max)))
  (jk: jumper pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_subkind == Some ParserStrong})
: Tot (accessor (gaccessor_bounded_vlgen_payload min max pk s))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq h (gaccessor_bounded_vlgen_payload min max pk s) input pos;
    valid_facts (parse_bounded_vlgen min max pk s) h input pos;
    parse_bounded_vlgen_unfold_aux min max pk s (bytes_of_slice_from h input pos);
    valid_facts pk h input pos
  in
  jk input pos

let gaccessor_vlgen_payload'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k /\ k.parser_kind_subkind == Some ParserStrong } )
: Tot (gaccessor' (parse_vlgen min max pk s) p (clens_id _))
= fun input ->
  parse_vlgen_unfold min max pk s input;
  let res =
    match parse pk input with
    | None -> (0) // dummy
    | Some (len, sz)  ->
      if sz + U32.v len <= Seq.length input
      then
        let input' = Seq.slice input sz (sz + U32.v len) in
        let _ = match parse p input' with
        | None -> ()
        | Some _ ->
          parse_strong_prefix p input' (Seq.slice input sz (Seq.length input))
        in
        sz
      else 0
  in
  res

let gaccessor_vlgen_payload_injective_1
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k })
  (sl sl' : bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl' /\
    injective_precond (parse_vlgen min max pk s) sl sl'
  ))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl' /\
    injective_precond (parse_vlgen min max pk s) sl sl' /\
    gaccessor_vlgen_payload' min max pk s sl == gaccessor_vlgen_payload' min max pk s sl'
  ))
= parse_vlgen_unfold min max pk s sl;
  parse_vlgen_unfold min max pk s sl' ;
  parse_injective (parse_vlgen min max pk s) sl sl' ;
  parse_injective pk sl sl'

let gaccessor_vlgen_payload_injective_2
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k })
  (sl sl' : bytes)
: Lemma
  (ensures ((
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl' /\
    injective_precond (parse_vlgen min max pk s) sl sl'
  ) ==> (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl' /\
    injective_precond (parse_vlgen min max pk s) sl sl' /\
    gaccessor_vlgen_payload' min max pk s sl == gaccessor_vlgen_payload' min max pk s sl'
  )))
= Classical.move_requires (gaccessor_vlgen_payload_injective_1 min max pk s sl) sl'

let gaccessor_vlgen_payload_no_lookahead_1
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k })
  (sl sl' : bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    (and_then_kind sk k).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl' /\
    no_lookahead_on_precond (parse_vlgen min max pk s) sl sl'
  ))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_vlgen_payload' min max pk s sl == gaccessor_vlgen_payload' min max pk s sl'
  ))
= parse_vlgen_unfold min max pk s sl;
  parse_vlgen_unfold min max pk s sl' ;
  parse_strong_prefix (parse_vlgen min max pk s) sl sl' ;
  parse_injective pk sl sl'

let gaccessor_vlgen_payload_no_lookahead_2
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k })
  (sl sl' : bytes)
: Lemma
  (ensures ((
    k.parser_kind_subkind == Some ParserStrong /\
    (and_then_kind sk k).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl /\
    gaccessor_pre (parse_vlgen min max pk s) p (clens_id _) sl' /\
    no_lookahead_on_precond (parse_vlgen min max pk s) sl sl'
  ) ==> (
    k.parser_kind_subkind == Some ParserStrong /\
    gaccessor_vlgen_payload' min max pk s sl == gaccessor_vlgen_payload' min max pk s sl'
  )))
= Classical.move_requires (gaccessor_vlgen_payload_no_lookahead_1 min max pk s sl) sl'

let gaccessor_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k /\ k.parser_kind_subkind == Some ParserStrong})
: Tot (gaccessor (parse_vlgen min max pk s) p (clens_id _))
= Classical.forall_intro_2 (gaccessor_vlgen_payload_no_lookahead_2 min max pk s);
  Classical.forall_intro_2 (gaccessor_vlgen_payload_injective_2 min max pk s);
  gaccessor_prop_equiv (parse_vlgen min max pk s) p (clens_id _) (gaccessor_vlgen_payload' min max pk s);
  gaccessor_vlgen_payload' min max pk s

inline_for_extraction
let accessor_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 ( min) ( max)))
  (jk: jumper pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k /\ k.parser_kind_subkind == Some ParserStrong } )
: Tot (accessor (gaccessor_vlgen_payload min max pk s))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq h (gaccessor_vlgen_payload min max pk s) input pos;
    valid_facts (parse_vlgen min max pk s) h input pos;
    parse_vlgen_unfold min max pk s (bytes_of_slice_from h input pos);
    valid_facts pk h input pos
  in
  jk input pos

module HS = FStar.HyperStack

#push-options "--z3rlimit 16"

let valid_bounded_vlgen_intro
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (min) (max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid_exact p h input pos1 (pos1 `U32.add` len)
  )))
  (ensures (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid_exact p h input pos1 (pos1 `U32.add` len) /\ (
    let x = contents_exact p h input pos1 (pos1 `U32.add` len) in
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vlgen min max pk s) h input pos x (pos1 `U32.add` len)
  ))))
= valid_facts pk h input pos;
  let pos1 = get_valid_pos pk h input pos in
  let len = contents pk h input pos in
  valid_exact_equiv p h input pos1 (pos1 `U32.add` len);
  contents_exact_eq p h input pos1 (pos1 `U32.add` len);
  parse_bounded_vlgen_unfold min max pk s (bytes_of_slice_from h input pos);
  valid_facts (parse_bounded_vlgen min max pk s) h input pos

#pop-options

let valid_bounded_vlgen_intro_strong_prefix
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (min) (max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h input pos1 (pos1 `U32.add` len)
  )))
  (ensures (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h input pos1 (pos1 `U32.add` len) /\ (
    let x = contents p h input pos1 in
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vlgen min max pk s) h input pos x (pos1 `U32.add` len)
  ))))
=   let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    valid_pos_valid_exact p h input pos1 (pos1 `U32.add` len);
    valid_bounded_vlgen_intro min max pk s h input pos

let valid_vlgen_intro
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (min) (max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid_exact p h input pos1 (pos1 `U32.add` len) /\
    parse_vlgen_precond min max k
  )))
  (ensures (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    valid_exact p h input pos1 (pos1 `U32.add` len) /\ (
    let x = contents_exact p h input pos1 (pos1 `U32.add` len) in
    valid_content_pos (parse_vlgen min max pk s) h input pos x (pos1 `U32.add` len)
  ))))
= valid_facts pk h input pos;
  let pos1 = get_valid_pos pk h input pos in
  let len = contents pk h input pos in
  valid_exact_equiv p h input pos1 (pos1 `U32.add` len);
  contents_exact_eq p h input pos1 (pos1 `U32.add` len);
  parse_vlgen_unfold min max pk s (bytes_of_slice_from h input pos);
  valid_facts (parse_vlgen min max pk s) h input pos

let valid_vlgen_intro_strong_prefix
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (min) (max)))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h input pos1 (pos1 `U32.add` len) /\
    parse_vlgen_precond min max k
  )))
  (ensures (
    valid pk h input pos /\ (
    let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    U32.v pos1 + U32.v len < 4294967296 /\
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h input pos1 (pos1 `U32.add` len) /\ (
    let x = contents p h input pos1 in
    valid_content_pos (parse_vlgen min max pk s) h input pos x (pos1 `U32.add` len)
  ))))
=   let pos1 = get_valid_pos pk h input pos in
    let len = contents pk h input pos in
    valid_pos_valid_exact p h input pos1 (pos1 `U32.add` len);
    valid_vlgen_intro min max pk s h input pos


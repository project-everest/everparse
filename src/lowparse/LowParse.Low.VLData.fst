module LowParse.Low.VLData
include LowParse.Spec.VLData
include LowParse.Low.BoundedInt // for bounded_integer
include LowParse.Low.FLData

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32

inline_for_extraction
let validate_vldata_payload
  (sz: integer_size)
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (i: bounded_integer sz { f i == true } )
: Tot (validator (parse_vldata_payload sz f p i))
= validate_weaken (parse_vldata_payload_kind sz k) (validate_fldata v (U32.v i) i) ()

inline_for_extraction
let validate_vldata_gen
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (f' : ((x: bounded_integer sz) -> Tot (y: bool { y == f x })))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
: Tot (validator (parse_vldata_gen sz f p))
= parse_vldata_gen_eq_def sz f p;
  validate_filter_and_then
    (validate_bounded_integer sz)
    (read_bounded_integer sz)
    f
    f'
    #_ #_ #(parse_vldata_payload sz f p)
    (validate_vldata_payload sz f v)
    ()

#push-options "--z3rlimit 32 --initial_ifuel 4 --max_ifuel 4"

module HS = FStar.HyperStack

let valid_vldata_gen_elim
  (h: HS.mem)
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_vldata_gen sz f p) h input pos
  ))
  (ensures (
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    f len_payload == true /\
    sz + U32.v len_payload == content_length (parse_vldata_gen sz f p) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos (parse_vldata_gen sz f p) h input pos (pos_payload `U32.add` len_payload) /\
    valid_exact p h input pos_payload (pos_payload `U32.add` len_payload) /\
    contents_exact p h input pos_payload (pos_payload `U32.add` len_payload) == contents (parse_vldata_gen sz f p) h input pos
  ))))
= valid_facts (parse_vldata_gen sz f p) h input pos;
  valid_facts (parse_bounded_integer sz) h input pos;
  parse_vldata_gen_eq sz f p (bytes_of_slice_from h input pos);
  let len_payload = contents (parse_bounded_integer sz) h input pos in
  let pos_payload = pos `U32.add` U32.uint_to_t sz in
  valid_exact_equiv p h input pos_payload (pos_payload `U32.add` len_payload);
  contents_exact_eq p h input pos_payload (pos_payload `U32.add` len_payload)

#pop-options

inline_for_extraction
let jump_vldata_gen
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (jumper (parse_vldata_gen sz f p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_vldata_gen_elim h sz f p input pos in
  pos `U32.add` (U32.uint_to_t sz `U32.add` read_bounded_integer sz input pos)

inline_for_extraction
let validate_bounded_vldata'
  (min: nat) // must be a constant
  (max: nat {
    min <= max /\
    max > 0 /\
    max < 4294967296
  }) // must be a constant
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
: Tot (validator (parse_bounded_vldata' min max l p))
= [@inline_let]
  let sz : integer_size = l in
  [@inline_let]
  let _ = parse_bounded_vldata_correct min max sz p in
  validate_strengthen
    (parse_bounded_vldata_strong_kind min max sz k)
    (validate_vldata_gen sz (in_bounds min max) (fun i -> if min = 0 then i `U32.lte` U32.uint_to_t max else (U32.uint_to_t min `U32.lte` i && i `U32.lte` U32.uint_to_t max)) v)
    ()

inline_for_extraction
let validate_bounded_vldata
  (min: nat) // must be a constant
  (max: nat) // must be a constant
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (u: unit {
    min <= max /\
    max > 0 /\
    max < 4294967296
  })
: Tot (validator (parse_bounded_vldata min max p))
= validate_bounded_vldata' min max (log256' max) v

inline_for_extraction
let jump_bounded_vldata'
  (min: nat) // must be a constant
  (max: nat {
    min <= max /\
    max > 0 /\
    max < 4294967296
  }) // must be a constant
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (jumper (parse_bounded_vldata' min max l p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let sz = l in
  [@inline_let] let _ = valid_facts (parse_bounded_vldata' min max l p) h input pos in
  [@inline_let] let _ = valid_facts (parse_vldata_gen sz (in_bounds min max) p) h input pos in
  jump_vldata_gen sz (in_bounds min max) p input pos

inline_for_extraction
let jump_bounded_vldata
  (min: nat) // must be a constant
  (max: nat) // must be a constant
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (u: unit {
    min <= max /\
    max > 0 /\
    max < 4294967296
  })
: Tot (jumper (parse_bounded_vldata min max p))
= jump_bounded_vldata' min max (log256' max) p

inline_for_extraction
let validate_bounded_vldata_strong'
  (min: nat) // must be a constant
  (max: nat {
    min <= max /\ max > 0 /\ max < 4294967296
  })
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
: Tot (validator (parse_bounded_vldata_strong' min max l s))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = valid_facts (parse_bounded_vldata_strong' min max l s) h input (uint64_to_uint32 pos) in
  [@inline_let]
  let _ = valid_facts (parse_bounded_vldata' min max l p) h input (uint64_to_uint32 pos) in
  validate_bounded_vldata' min max l v input pos

inline_for_extraction
let validate_bounded_vldata_strong
  (min: nat) // must be a constant
  (max: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (u: unit {
    min <= max /\ max > 0 /\ max < 4294967296
  })
: Tot (validator (parse_bounded_vldata_strong min max s))
= validate_bounded_vldata_strong' min max (log256' max) s v

inline_for_extraction
let jump_bounded_vldata_strong'
  (min: nat) // must be a constant
  (max: nat {
    min <= max /\ max > 0 /\ max < 4294967296
  })
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (jumper (parse_bounded_vldata_strong' min max l s))
= fun #rrel #rel (input: slice rrel rel) pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_bounded_vldata_strong' min max l s) h input pos in
  [@inline_let] let _ = valid_facts (parse_bounded_vldata' min max l p) h input pos in
  jump_bounded_vldata' min max l p input pos

inline_for_extraction
let jump_bounded_vldata_strong
  (min: nat) // must be a constant
  (max: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (u: unit {
    min <= max /\ max > 0 /\ max < 4294967296
  })
: Tot (jumper (parse_bounded_vldata_strong min max s))
= jump_bounded_vldata_strong' min max (log256' max) s

#push-options "--z3rlimit 32 --initial_ifuel 4 --max_ifuel 4"

let valid_vldata_gen_intro
  (h: HS.mem)
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    bounded_integer_prop sz len_payload /\
    f len_payload == true /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len_payload
  ))))
  (ensures (
    valid_content_pos (parse_vldata_gen sz f p) h input pos (contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos') pos'
  ))
= valid_facts (parse_vldata_gen sz f p) h input pos;
  valid_facts (parse_bounded_integer sz) h input pos;
  parse_vldata_gen_eq sz f p (bytes_of_slice_from h input pos);
  contents_exact_eq p h input (pos `U32.add` U32.uint_to_t sz) pos'

#pop-options

inline_for_extraction
let finalize_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    bounded_integer_prop sz len_payload /\
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    f len_payload == true
  ))))
  (ensures (fun h _ h' ->
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    valid_content_pos (parse_vldata_gen sz f p) h' input pos (contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos') pos'
  ))
= [@inline_let]
  let len_payload = pos' `U32.sub` (pos `U32.add` U32.uint_to_t sz) in
  let _ = write_bounded_integer sz len_payload input pos in
  let h = HST.get () in
  valid_vldata_gen_intro h sz f p input pos pos'

let valid_bounded_vldata'_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vldata' min max l p) h input pos
  ))
  (ensures (
    let sz = l in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vldata' min max l p) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos (parse_bounded_vldata' min max l p) h input pos (pos_payload `U32.add` len_payload) /\
    valid_exact p h input pos_payload (pos_payload `U32.add` len_payload) /\
    contents_exact p h input pos_payload (pos_payload `U32.add` len_payload) == contents (parse_bounded_vldata' min max l p) h input pos
  ))))
= valid_facts (parse_bounded_vldata' min max l p) h input pos;
  let sz = l in
  valid_facts (parse_vldata_gen sz (in_bounds min max) p) h input pos;
  valid_vldata_gen_elim h sz (in_bounds min max) p input pos

let valid_bounded_vldata_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vldata min max p) h input pos
  ))
  (ensures (
    let sz = log256' max in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vldata min max p) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos (parse_bounded_vldata min max p) h input pos (pos_payload `U32.add` len_payload) /\
    valid_exact p h input pos_payload (pos_payload `U32.add` len_payload) /\
    contents_exact p h input pos_payload (pos_payload `U32.add` len_payload) == contents (parse_bounded_vldata min max p) h input pos
  ))))
= valid_bounded_vldata'_elim h min max (log256' max) p input pos

let valid_bounded_vldata_intro
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len_payload
  ))))
  (ensures (
    let sz = log256' max in
    valid_content_pos (parse_bounded_vldata min max p) h input pos (contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos') pos'
  ))
= valid_facts (parse_bounded_vldata min max p) h input pos;
  valid_facts (parse_vldata_gen (log256' max) (in_bounds min max) p) h input pos;
  valid_vldata_gen_intro h (log256' max) (in_bounds min max) p input pos pos'

let valid_bounded_vldata_strong'_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vldata_strong' min max l s) h input pos
  ))
  (ensures (
    let sz = l in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vldata_strong' min max l s) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos (parse_bounded_vldata_strong' min max l s) h input pos (pos_payload `U32.add` len_payload) /\
    valid_exact p h input pos_payload (pos_payload `U32.add` len_payload) /\
    contents_exact p h input pos_payload (pos_payload `U32.add` len_payload) == contents (parse_bounded_vldata_strong' min max l s) h input pos
  ))))
= valid_facts (parse_bounded_vldata_strong' min max l s) h input pos;
  valid_facts (parse_bounded_vldata' min max l p) h input pos;
  valid_bounded_vldata'_elim h min max l p input pos

let valid_bounded_vldata_strong_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vldata_strong min max s) h input pos
  ))
  (ensures (
    let sz = log256' max in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vldata_strong min max s) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos (parse_bounded_vldata_strong min max s) h input pos (pos_payload `U32.add` len_payload) /\
    valid_exact p h input pos_payload (pos_payload `U32.add` len_payload) /\
    contents_exact p h input pos_payload (pos_payload `U32.add` len_payload) == contents (parse_bounded_vldata_strong min max s) h input pos
  ))))
= valid_bounded_vldata_strong'_elim h min max (log256' max) s input pos
  
let valid_bounded_vldata_strong_intro
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len_payload
  ))))
  (ensures (
    let sz = log256' max in
    let x = contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos' in
    Seq.length (serialize s x) == U32.v pos'  - (U32.v pos + sz) /\
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vldata_strong min max s) h input pos x pos'
  ))
= valid_facts (parse_bounded_vldata_strong min max s) h input pos;
  valid_facts (parse_bounded_vldata min max p) h input pos;
  valid_bounded_vldata_intro h min max p input pos pos';
  valid_exact_serialize s h input (pos `U32.add` U32.uint_to_t (log256' max)) pos'

inline_for_extraction
let finalize_bounded_vldata_strong_exact
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
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
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    let len_ser = Seq.length (serialize s (contents_exact p h input pos_payload pos')) in
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    ((min <= U32.v len_payload /\ U32.v len_payload <= max) \/ (min <= len_ser /\ len_ser <= max))
  ))))
  (ensures (fun h _ h' ->
    let sz = log256' max in
    let x = contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos' in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    Seq.length (serialize s x) == U32.v pos'  - (U32.v pos + sz) /\
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vldata_strong min max s) h' input pos x pos'
  ))
= [@inline_let]
  let sz = log256' max in
  [@inline_let]
  let len_payload = pos' `U32.sub` (pos `U32.add` U32.uint_to_t sz) in
  let h = HST.get () in
  [@inline_let]
  let _ =
    serialized_length_eq s (contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos');
    valid_exact_serialize s h input (pos `U32.add` U32.uint_to_t sz) pos'
  in
  let _ = write_bounded_integer sz len_payload input pos in
  let h = HST.get () in
  valid_bounded_vldata_strong_intro h min max s input pos pos'

inline_for_extraction
let finalize_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
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
    let sz = log256' max in
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
    let sz = log256' max in
    let x = contents p h input (pos `U32.add` U32.uint_to_t sz) in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vldata_strong min max s) h' input pos x pos'
  ))
= let h = HST.get () in
  [@inline_let]
  let _ =
    let sz = log256' max in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos_valid_exact p h input pos_payload pos'
  in
  finalize_bounded_vldata_strong_exact min max s input pos pos'

inline_for_extraction
let finalize_bounded_vldata_exact
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    min <= k.parser_kind_low /\
    Some? k.parser_kind_high /\
    Some?.v k.parser_kind_high <= max
  )))
  (ensures (fun h _ h' ->
    let sz = log256' max in
    let x = contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos' in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    valid_content_pos (parse_bounded_vldata min max p) h' input pos x pos'
  ))
= [@inline_let]
  let sz = log256' max in
  [@inline_let]
  let len_payload = pos' `U32.sub` (pos `U32.add` U32.uint_to_t sz) in
  let h = HST.get () in
  let _ = write_bounded_integer sz len_payload input pos in
  let h = HST.get () in
  valid_bounded_vldata_intro h min max p input pos pos'

inline_for_extraction
let finalize_bounded_vldata
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos p h input pos_payload pos' /\
    k.parser_kind_subkind == Some ParserStrong /\
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    min <= k.parser_kind_low /\
    Some? k.parser_kind_high /\
    Some?.v k.parser_kind_high <= max
  )))
  (ensures (fun h _ h' ->
    let sz = log256' max in
    let x = contents p h input (pos `U32.add` U32.uint_to_t sz) in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    valid_content_pos (parse_bounded_vldata min max p) h' input pos x pos'
  ))
= finalize_bounded_vldata_exact min max p input pos pos'

inline_for_extraction
let weak_finalize_bounded_vldata_strong_exact
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack bool
  (requires (fun h ->
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    valid_exact p h input pos_payload pos'
  )))
  (ensures (fun h res h' ->
    let sz = log256' max in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    let len_payload = pos' `U32.sub` pos_payload in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    (res == true <==> (min <= U32.v len_payload /\ U32.v len_payload <= max)) /\
    (if res
    then
      let x = contents_exact p h input pos_payload pos' in
      parse_bounded_vldata_strong_pred min max s x /\
      valid_content_pos (parse_bounded_vldata_strong min max s) h' input pos x pos'
    else True
  )))
= let len_payload = pos' `U32.sub`  (pos `U32.add` U32.uint_to_t (log256' max)) in
  if U32.uint_to_t max `U32.lt` len_payload || len_payload `U32.lt` U32.uint_to_t min
  then false
  else begin
    finalize_bounded_vldata_strong_exact min max s input pos pos';
    true
  end

inline_for_extraction
let weak_finalize_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack bool
  (requires (fun h ->
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\
    k.parser_kind_subkind == Some ParserStrong /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    writable input.base (U32.v pos) (U32.v pos + sz) h /\
    valid_pos p h input pos_payload pos'
  )))
  (ensures (fun h res h' ->
    let sz = log256' max in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    let len_payload = pos' `U32.sub` pos_payload in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    (res == true <==> (min <= U32.v len_payload /\ U32.v len_payload <= max)) /\
    (if res
    then
      let x = contents p h input pos_payload in
      parse_bounded_vldata_strong_pred min max s x /\
      valid_content_pos (parse_bounded_vldata_strong min max s) h' input pos x pos'
    else True
  )))
= let h = HST.get () in
  [@inline_let]
  let _ =
    let sz = log256' max in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos_valid_exact p h input pos_payload pos'
  in
  weak_finalize_bounded_vldata_strong_exact min max s input pos pos'


let gaccessor_bounded_vldata_payload'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong })
: Tot (gaccessor' (parse_bounded_vldata min max p) p (clens_id t))
= fun input ->
  let sz = log256' max in
  parse_vldata_gen_eq sz (in_bounds min max) p input;
  if Seq.length input < sz
  then 0 (* dummy *)
  else
    let _ = match parse (parse_bounded_vldata min max p) input with
    | None -> ()
    | Some _ ->
      assert (Some? (parse (parse_vldata_gen sz (in_bounds min max) p) input));
      parse_vldata_gen_eq sz (in_bounds min max) p input;
      let Some (len, consumed) = parse (parse_bounded_integer sz) input in
      assert (consumed == sz);
      parse_strong_prefix p (Seq.slice input sz (sz + U32.v len)) (Seq.slice input sz (Seq.length input))
    in
    sz

let gaccessor_bounded_vldata_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong })
: Tot (gaccessor (parse_bounded_vldata min max p) p (clens_id t))
= let sz = log256' max in
  Classical.forall_intro (parse_vldata_gen_eq sz (in_bounds min max) p);
  assert (forall x . gaccessor_pre (parse_bounded_vldata min max p) p (clens_id t) x ==> Seq.length x >= sz);
  gaccessor_prop_equiv (parse_bounded_vldata min max p) p (clens_id t) (gaccessor_bounded_vldata_payload' min max p);
  gaccessor_bounded_vldata_payload' min max p

inline_for_extraction
let accessor_bounded_vldata_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong })
: Tot (accessor (gaccessor_bounded_vldata_payload min max p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = slice_access_eq h (gaccessor_bounded_vldata_payload min max p) input pos in
  pos `U32.add` U32.uint_to_t (log256' max)


let clens_bounded_vldata_strong_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (clens (parse_bounded_vldata_strong_t min max s) t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (x: parse_bounded_vldata_strong_t min max s) -> (x <: t));
}

let gaccessor_bounded_vldata_strong_payload'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_subkind == Some ParserStrong})
: Tot (gaccessor' (parse_bounded_vldata_strong min max s) p (clens_bounded_vldata_strong_payload min max s))
= fun input ->
  (gaccessor_bounded_vldata_payload min max p input <: (res : _ { gaccessor_post' (parse_bounded_vldata_strong min max s) p (clens_bounded_vldata_strong_payload min max s) input res } ))

let gaccessor_bounded_vldata_strong_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_subkind == Some ParserStrong})
: Tot (gaccessor (parse_bounded_vldata_strong min max s) p (clens_bounded_vldata_strong_payload min max s))
= gaccessor_prop_equiv (parse_bounded_vldata min max p) p (clens_id t) (gaccessor_bounded_vldata_payload' min max p);
  gaccessor_prop_equiv (parse_bounded_vldata_strong min max s) p (clens_bounded_vldata_strong_payload min max s) (gaccessor_bounded_vldata_strong_payload' min max s);
  gaccessor_bounded_vldata_strong_payload' min max s

inline_for_extraction
let accessor_bounded_vldata_strong_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_subkind == Some ParserStrong})
: Tot (accessor (gaccessor_bounded_vldata_strong_payload min max s))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = slice_access_eq h (gaccessor_bounded_vldata_strong_payload min max s) input pos in
  pos `U32.add` U32.uint_to_t (log256' max)

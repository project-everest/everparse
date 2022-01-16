module LowParse.Low.Sum
include LowParse.Low.Enum
include LowParse.Spec.Sum

module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

inline_for_extraction
let validate_sum_cases_aux
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (vc: ((x: sum_key t) -> Tot (validator (dsnd (pc x)))))
  (k: sum_key t)
: Tot (validator (parse_sum_cases t pc k))
= [@inline_let]
  let _ = synth_sum_case_injective t k in
  validate_synth
    (validate_weaken
      (weaken_parse_cases_kind t pc)
      (vc k)
      ()
    )
    (synth_sum_case t k)
    ()

inline_for_extraction
let validate_sum_cases_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot Type
= validator (parse_sum_cases t pc k)

let validate_sum_cases_t_eq
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (x y : validate_sum_cases_t t pc k)
: GTot Type0
= True

inline_for_extraction
let validate_sum_cases_t_if
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (if_combinator _ (validate_sum_cases_t_eq t pc k))
= fun cond (sv_true: cond_true cond -> Tot (validate_sum_cases_t t pc k)) (sv_false: cond_false cond -> Tot (validate_sum_cases_t t pc k)) #rrel #rel input pos ->
  if cond
  then sv_true () input pos
  else sv_false () input pos

inline_for_extraction
let validate_sum_cases 
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (vc: ((x: sum_key t) -> Tot (validator (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (validate_sum_cases_t t pc))
  (k: sum_key t)
: Tot (validator (parse_sum_cases t pc k))
= destr
    _
    (validate_sum_cases_t_if t pc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (validate_sum_cases_aux t pc vc)
    k

inline_for_extraction
let validate_sum_aux_payload_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot Type
= (#rrel: _) -> (#rel: _) ->
  (input: slice rrel rel) ->
  (pos: U64.t) ->
  HST.Stack U64.t
  (requires (fun h -> live_slice h input /\ U64.v pos <= U32.v input.len))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    match k with
    | Unknown _ -> is_error res
    | Known k' ->
      if is_success res
      then
        valid_pos (dsnd (pc k')) h input (uint64_to_uint32 pos) (uint64_to_uint32 res)
      else
        (~ (valid (dsnd (pc k')) h input (uint64_to_uint32 pos)))
  )))

let validate_sum_aux_payload_eq
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot (validate_sum_aux_payload_t t pc k -> validate_sum_aux_payload_t t pc k -> GTot Type0)
= fun _ _ -> True

inline_for_extraction
let validate_sum_aux_payload_if'
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
  (cond: bool)
  (ift: ((cond_true cond) -> Tot (validate_sum_aux_payload_t t pc k)))
  (iff: ((cond_false cond) -> Tot (validate_sum_aux_payload_t t pc k)))
: Tot (validate_sum_aux_payload_t t pc k)
= fun #rrel #rel input pos ->
  if cond
  then begin
    (ift () <: validate_sum_aux_payload_t t pc k) input pos
  end else
    (iff () <: validate_sum_aux_payload_t t pc k) input pos

inline_for_extraction
let validate_sum_aux_payload_if
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot (if_combinator _ (validate_sum_aux_payload_eq t pc k))
= validate_sum_aux_payload_if' t pc k

#push-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --initial_ifuel 8 --max_ifuel 8 --initial_fuel 2 --max_fuel 2 --using_facts_from '* -FStar.Int.Cast -LowParse.BitFields'"
// --query_stats  --smtencoding.elim_box true --smtencoding.l_arith_repr native --z3refresh"

inline_for_extraction
let validate_sum_aux
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: validator p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (v_payload: ((k: sum_repr_type t)) -> Tot (validate_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k)))
: Tot (validator (parse_sum t p pc))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = parse_sum_eq'' t p pc (bytes_of_slice_from h input (uint64_to_uint32 pos)) in
  [@inline_let]
  let _ = valid_facts (parse_sum t p pc) h input (uint64_to_uint32 pos) in
  [@inline_let]
  let _ = valid_facts p h input (uint64_to_uint32 pos) in
  let len_after_tag = v input pos in
  if is_error len_after_tag
  then len_after_tag
  else begin
    let h1 = HST.get () in
    let k' = p32 input (uint64_to_uint32 pos) in
    [@inline_let]
    let _ =
      match maybe_enum_key_of_repr (sum_enum t) k' with
      | Known k -> valid_facts (dsnd (pc k)) h input (uint64_to_uint32 len_after_tag)
      | _ -> ()
    in
    v_payload k' input len_after_tag
  end

#pop-options

inline_for_extraction
let validate_sum_aux_payload'
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (validator (dsnd (pc x)))))
  (k: maybe_enum_key (sum_enum t))
: Tot (validate_sum_aux_payload_t t pc k)
= fun #rrel #rel input pos ->
    match k with
    | Known k ->
      [@inline_let]
      let _ = synth_sum_case_injective t k in
      pc32 k input pos
      // validate_synth (pc32 k) (synth_sum_case t k) () input pos
    | _ -> validator_error_generic

inline_for_extraction
let validate_sum_aux_payload
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (validator (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (validate_sum_aux_payload_t t pc))
  (k: sum_repr_type t)
: Tot (validate_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k))
= destr (validate_sum_aux_payload_eq t pc) (validate_sum_aux_payload_if t pc) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (validate_sum_aux_payload' t pc pc32) k

inline_for_extraction
let validate_sum
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: validator p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (validator (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (validate_sum_aux_payload_t t pc))
: Tot (validator (parse_sum t p pc))
= validate_sum_aux t v p32 pc (validate_sum_aux_payload t pc pc32 destr)

module HS = FStar.HyperStack

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --initial_ifuel 8 --max_ifuel 8 --initial_fuel 2 --max_fuel 2"

let valid_sum_intro
  (h: HS.mem)
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_enum_key p (sum_enum t)) h input pos /\ (
    let k = contents (parse_enum_key p (sum_enum t)) h input pos in
    valid (dsnd (pc k)) h input (get_valid_pos (parse_enum_key p (sum_enum t)) h input pos)
  )))
  (ensures (
    let k = contents (parse_enum_key p (sum_enum t)) h input pos in
    let pos_payload = get_valid_pos (parse_enum_key p (sum_enum t)) h input pos in
    valid_content_pos
      (parse_sum t p pc) h input pos
      (synth_sum_case t k (contents (dsnd (pc k)) h input pos_payload))
      (get_valid_pos (dsnd (pc k)) h input pos_payload)
  ))
= valid_facts (parse_enum_key p (sum_enum t)) h input pos;
  let k = contents (parse_enum_key p (sum_enum t)) h input pos in
  let pos_payload = get_valid_pos (parse_enum_key p (sum_enum t)) h input pos in
  valid_facts (dsnd (pc k)) h input pos_payload;
  valid_facts (parse_sum t p pc) h input pos;
  parse_sum_eq t p pc (bytes_of_slice_from h input pos)

#pop-options

inline_for_extraction
let finalize_sum_case
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (w: leaf_writer_strong s)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (destr: enum_repr_of_key'_t (sum_enum t))
  (k: sum_key t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack unit
  (requires (fun h ->
    let len_tag = serialized_length (serialize_enum_key _ s (sum_enum t)) k in
    U32.v pos + len_tag < 4294967296 /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t len_tag in
    valid (dsnd (pc k)) h input pos_payload /\
    writable input.base (U32.v pos) (U32.v pos_payload) h
  )))
  (ensures (fun h _ h' ->
    let len_tag = serialized_length (serialize_enum_key _ s (sum_enum t)) k in
    let pos_payload = pos `U32.add` U32.uint_to_t len_tag in
    B.modifies (loc_slice_from_to input pos pos_payload) h h' /\
    valid_content_pos (parse_sum t p pc) h' input pos (synth_sum_case t k (contents (dsnd (pc k)) h input pos_payload)) (get_valid_pos (dsnd (pc k)) h input pos_payload)
  ))
= let pos1 = write_enum_key w (sum_enum t) destr k input pos in
  let h = HST.get () in
  [@inline_let]
  let _ = valid_sum_intro h t p pc input pos in
  ()

inline_for_extraction
let jump_sum_cases_aux
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (vc: ((x: sum_key t) -> Tot (jumper (dsnd (pc x)))))
  (k: sum_key t)
: Tot (jumper (parse_sum_cases t pc k))
= [@inline_let]
  let _ = synth_sum_case_injective t k in
  jump_synth
    (jump_weaken
      (weaken_parse_cases_kind t pc)
      (vc k)
      ()
    )
    (synth_sum_case t k)
    ()

inline_for_extraction
let jump_sum_cases_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot Type
= jumper (parse_sum_cases t pc k)

let jump_sum_cases_t_eq
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (x y : jump_sum_cases_t t pc k)
: GTot Type0
= True

inline_for_extraction
let jump_sum_cases_t_if
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (if_combinator _ (jump_sum_cases_t_eq t pc k))
= fun cond (sv_true: cond_true cond -> Tot (jump_sum_cases_t t pc k)) (sv_false: cond_false cond -> Tot (jump_sum_cases_t t pc k)) #rrel #rel input pos ->
  if cond
  then sv_true () input pos
  else sv_false () input pos

inline_for_extraction
let jump_sum_cases 
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (vc: ((x: sum_key t) -> Tot (jumper (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (jump_sum_cases_t t pc))
  (k: sum_key t)
: Tot (jumper (parse_sum_cases t pc k))
= destr
    _
    (jump_sum_cases_t_if t pc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (jump_sum_cases_aux t pc vc)
    k

inline_for_extraction
let jump_sum_aux_payload_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot Type
= (#rrel: _) -> (#rel: _) ->
  (input: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> live_slice h input /\ U32.v pos <= U32.v input.len /\ (
    match k with
    | Unknown _ -> False
    | Known k' -> valid (dsnd (pc k')) h input pos
  )))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    match k with
    | Unknown _ -> False
    | Known k' ->
      valid_pos (dsnd (pc k')) h input pos res
  )))

let jump_sum_aux_payload_eq
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot (jump_sum_aux_payload_t t pc k -> jump_sum_aux_payload_t t pc k -> GTot Type0)
= fun _ _ -> True

inline_for_extraction
let jump_sum_aux_payload_if'
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
  (cond: bool)
  (ift: ((cond_true cond) -> Tot (jump_sum_aux_payload_t t pc k)))
  (iff: ((cond_false cond) -> Tot (jump_sum_aux_payload_t t pc k)))
: Tot (jump_sum_aux_payload_t t pc k)
= fun #rrel #rel input pos ->
  if cond
  then begin
    (ift () <: jump_sum_aux_payload_t t pc k) input pos
  end else
    (iff () <: jump_sum_aux_payload_t t pc k) input pos

inline_for_extraction
let jump_sum_aux_payload_if
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot (if_combinator _ (jump_sum_aux_payload_eq t pc k))
= jump_sum_aux_payload_if' t pc k

let parse_sum_eq3
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (input: bytes)
  (k' : sum_repr_type t)
  (consumed_k: consumed_length input)
: Lemma
  (requires (Some? (parse (parse_sum t p pc) input) /\ parse p input == Some (k', consumed_k)))
  (ensures (
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    let k = maybe_enum_key_of_repr (sum_enum t) k' in
    begin match k with
    | Known k ->
      Some? (parse (dsnd (pc k)) input_k)
    | _ -> False
    end
  ))
= parse_sum_eq'' t p pc input

let parse_sum_eq4
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (input: bytes)
  (k' : sum_repr_type t)
  (consumed_k: consumed_length input)
  (consumed_payload: nat)
: Lemma
  (requires (Some? (parse (parse_sum t p pc) input) /\ parse p input == Some (k', consumed_k) /\ (
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    let k = maybe_enum_key_of_repr (sum_enum t) k' in
    begin match k with
    | Known k ->
      Some? (parse (dsnd (pc k)) input_k) /\ (
      let Some (_, consumed_payload') = parse (dsnd (pc k)) input_k in
      consumed_payload' == consumed_payload
      )
    | _ -> False
    end
  )))
  (ensures (
      let Some (_, consumed) = parse (parse_sum t p pc) input in
      consumed == consumed_k + consumed_payload
  ))
= parse_sum_eq'' t p pc input

#push-options "--z3rlimit 16"

let valid_sum_elim
  (h: HS.mem)
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (#rrel: _) (#rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_sum t p pc) h input pos
  ))
  (ensures (
    valid p h input pos /\ (
    let pos_payload = get_valid_pos p h input pos in
    let k' = maybe_enum_key_of_repr (sum_enum t) (contents p h input pos) in
    match k' with
    | Known k ->
      k == sum_tag_of_data t (contents (parse_sum t p pc) h input pos) /\
      valid (dsnd (pc k)) h input pos_payload /\
      valid_pos
        (parse_sum t p pc) h input pos
        (get_valid_pos (dsnd (pc k)) h input pos_payload)
    | _ -> False
  )))
= let sinput = bytes_of_slice_from h input pos in
  let _ = parse_sum_eq'' t p pc sinput in
  [@inline_let]
  let _ = valid_facts (parse_sum t p pc) h input pos in
  let Some (k', consumed_k) = parse p sinput in
  let pos_after_tag = U32.uint_to_t (U32.v pos + consumed_k) in
  [@inline_let]
  let _ = valid_facts p h input pos in
  assert (valid_content_pos p h input pos k' pos_after_tag);
  match maybe_enum_key_of_repr (sum_enum t) k' with
  | Known k -> valid_facts (dsnd (pc k)) h input pos_after_tag
  | _ -> ()

#pop-options

let valid_sum_elim_tag
  (h: HS.mem)
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_sum t p pc) h input pos
  ))
  (ensures (
    valid (parse_enum_key p (sum_enum t)) h input pos /\
    contents (parse_enum_key p (sum_enum t)) h input pos == sum_tag_of_data t (contents (parse_sum t p pc) h input pos)
  ))
= let _ = parse_sum_eq' t p pc (bytes_of_slice_from h input pos) in
  let _ = valid_facts (parse_sum t p pc) h input pos in
  let _ = valid_facts (parse_enum_key p (sum_enum t)) h input pos in
  ()

inline_for_extraction
let read_sum_tag
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (p32: leaf_reader p)
  (destr: dep_maybe_enum_destr_t (sum_enum t) (read_enum_key_t (sum_enum t)))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack (sum_key t)
  (requires (fun h ->
    valid (parse_sum t p pc) h input pos
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == sum_tag_of_data t (contents (parse_sum t p pc) h input pos)
  ))
= let h = HST.get () in
  [@inline_let] let _ = valid_sum_elim_tag h t p pc input pos in
  read_enum_key p32 (sum_enum t) destr input pos

inline_for_extraction
let jump_sum_aux
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: jumper p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (v_payload: ((k: sum_repr_type t)) -> Tot (jump_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k)))
: Tot (jumper (parse_sum t p pc))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = valid_sum_elim h t p pc input pos in
  let pos_after_tag = v input pos in
  let k' = p32 input pos in
  v_payload k' input pos_after_tag

inline_for_extraction
let jump_sum_aux_payload'
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (jumper (dsnd (pc x)))))
  (k: maybe_enum_key (sum_enum t))
: Tot (jump_sum_aux_payload_t t pc k)
= fun #rrel #rel input pos ->
    match k with
    | Known k ->
      [@inline_let]
      let _ = synth_sum_case_injective t k in
      pc32 k input pos
    | _ -> 0ul // dummy, but we MUST NOT remove this branch, otherwise extraction fails

inline_for_extraction
let jump_sum_aux_payload
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (jumper (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (jump_sum_aux_payload_t t pc))
  (k: sum_repr_type t)
: Tot (jump_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k))
= destr (jump_sum_aux_payload_eq t pc) (jump_sum_aux_payload_if t pc) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (jump_sum_aux_payload' t pc pc32) k

inline_for_extraction
let jump_sum
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: jumper p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (jumper (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (jump_sum_aux_payload_t t pc))
: Tot (jumper (parse_sum t p pc))
= jump_sum_aux t v p32 pc (jump_sum_aux_payload t pc pc32 destr)

inline_for_extraction
let read_sum_cases'
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (leaf_reader (dsnd (pc x)))))
  (k: sum_key t)
: Tot (leaf_reader (parse_sum_cases' t pc k))
= [@inline_let]
  let _ = synth_sum_case_injective t k in
        read_synth'
            (dsnd (pc k))
            (synth_sum_case t k)
            (pc32 k)
            ()

inline_for_extraction
let read_sum_cases_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot Type
= leaf_reader (parse_sum_cases' t pc k)

let read_sum_cases_t_eq
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (x y : read_sum_cases_t t pc k)
: GTot Type0
= True

inline_for_extraction
let read_sum_cases_t_if
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (if_combinator _ (read_sum_cases_t_eq t pc k))
= fun cond (sv_true: cond_true cond -> Tot (read_sum_cases_t t pc k)) (sv_false: cond_false cond -> Tot (read_sum_cases_t t pc k)) #_ #_ input pos ->
  if cond
  then (sv_true () input pos)
  else (sv_false () input pos)

inline_for_extraction
let read_sum_cases 
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (leaf_reader (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (read_sum_cases_t t pc))
  (k: sum_key t)
: Tot (leaf_reader (parse_sum_cases' t pc k))
= destr
    _
    (read_sum_cases_t_if t pc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (read_sum_cases' t pc pc32)
    k

#push-options "--z3rlimit 32"

inline_for_extraction
let read_sum
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (p32: leaf_reader (parse_enum_key p (sum_enum t)))
  (j: jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (leaf_reader (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (read_sum_cases_t t pc))
: Tot (leaf_reader (parse_sum t p pc))
=
  fun #_ #_ input pos ->
    let h = HST.get () in
    valid_facts (parse_sum t p pc) h input pos;
    parse_sum_eq' t p pc (bytes_of_slice_from h input pos);
    valid_facts (parse_enum_key p (sum_enum t)) h input pos;
    let k = p32 input pos in
    let pos' = jump_enum_key j (sum_enum t) input pos in
    valid_facts (parse_sum_cases' t pc k) h input pos' ;
    read_sum_cases t pc pc32 destr k input pos'

#pop-options

inline_for_extraction
let serialize32_sum_cases_t
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
: Tot Type
= serializer32 (serialize_sum_cases t pc sc k)

let serialize32_sum_cases_t_eq
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
  (x y: serialize32_sum_cases_t t sc k)
: GTot Type0
= True

inline_for_extraction
let serialize32_sum_cases_t_if
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (k: sum_key t)
: Tot (if_combinator _ (serialize32_sum_cases_t_eq t sc k))
= fun cond (sv_true: (cond_true cond -> Tot (serialize32_sum_cases_t t sc k))) (sv_false: (cond_false cond -> Tot (serialize32_sum_cases_t t sc k))) x #rrel #rel b pos ->
  if cond
  then (sv_true () x b pos)
  else (sv_false () x b pos)

inline_for_extraction
let serialize32_sum_cases_aux
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (k: sum_key t)
: Tot (serializer32 (serialize_sum_cases t pc sc k))
= fun x #rrel #rel b pos ->
  [@inline_let] let _ =
    Classical.forall_intro (parse_sum_cases_eq' t pc k);
    synth_sum_case_injective t k;
    synth_sum_case_inverse t k
  in
  serialize32_synth
    (sc32 k)
    (synth_sum_case t k)
    (synth_sum_case_recip t k)
    (fun x -> synth_sum_case_recip t k x)
    ()
    x
    b
    pos

inline_for_extraction
let serialize32_sum_cases
  (t: sum)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (destr: dep_enum_destr (sum_enum t) (serialize32_sum_cases_t t sc))
  (k: sum_key t)
: Tot (serializer32 (serialize_sum_cases t pc sc k))
= destr
    _
    (serialize32_sum_cases_t_if t sc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (serialize32_sum_cases_aux t sc sc32)
    k

inline_for_extraction
let serialize32_sum
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p {kt.parser_kind_subkind == Some ParserStrong})
  (s32: serializer32 (serialize_enum_key _ s (sum_enum t)))
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (destr: dep_enum_destr (sum_enum t) (serialize32_sum_cases_t t sc))
: Tot (serializer32 (serialize_sum t s sc))
= fun x #rrel #rel b pos ->
  serialize_sum_eq t s sc x;
  let tg = sum_tag_of_data t x in
  serialize32_nondep_then_aux s32 (serialize32_sum_cases t sc sc32 destr tg) tg x b pos

let clens_sum_tag
  (s: sum)
: Tot (clens (sum_type s) (sum_key s))
= {
    clens_cond = (fun _ -> True);
    clens_get = sum_tag_of_data s;
  }

let gaccessor_sum_tag
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
: Tot (gaccessor (parse_sum t p pc) (parse_enum_key p (sum_enum t)) (clens_sum_tag t))
= gaccessor_tagged_union_tag
    (parse_enum_key p (sum_enum t))
    (sum_tag_of_data t)
    (parse_sum_cases t pc)

inline_for_extraction
let accessor_sum_tag
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
: Tot (accessor (gaccessor_sum_tag t p pc))
= accessor_tagged_union_tag
    (parse_enum_key p (sum_enum t))
    (sum_tag_of_data t)
    (parse_sum_cases t pc)

let clens_sum_payload
  (s: sum)
  (k: sum_key s)
: Tot (clens (sum_type s) (sum_type_of_tag s k))
= {
    clens_cond = (fun (x: sum_type s) -> sum_tag_of_data s x == k);
    clens_get = (fun (x: sum_type s) -> synth_sum_case_recip s k x <: Ghost (sum_type_of_tag s k) (requires (sum_tag_of_data s x == k)) (ensures (fun _ -> True)));
  }

#push-options "--z3rlimit 32"

let gaccessor_clens_sum_payload'
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (gaccessor' (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k))
= fun (input: bytes) ->
  parse_sum_eq'' t p pc input;
  let res =
    match parse p input with
    | Some (_, consumed) ->
      synth_sum_case_inverse t k;
      synth_sum_case_injective t k;
      synth_injective_synth_inverse_synth_inverse_recip (synth_sum_case t k) (synth_sum_case_recip t k) ();
      (consumed)
    | _ -> 0 // dummy
  in
  (res <: (res: _ { gaccessor_post'  (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k) input res } ))

#push-options "--z3rlimit 64"

let gaccessor_clens_sum_payload_injective
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (sl sl' : bytes)
: Lemma
  (requires (
    gaccessor_pre (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k) sl /\
    gaccessor_pre (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k) sl' /\
    injective_precond (parse_sum t p pc) sl sl'
  ))
  (ensures (gaccessor_clens_sum_payload' t p pc k sl == gaccessor_clens_sum_payload' t p pc k sl'))
= parse_sum_eq'' t p pc sl;
  parse_sum_eq'' t p pc sl' ;
  parse_injective (parse_sum t p pc) sl sl' ;
  parse_injective p sl sl'

#pop-options

let gaccessor_clens_sum_payload_no_lookahead
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (sl sl' : bytes)
: Lemma
  (requires (
    (parse_sum_kind kt t pc).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k) sl /\
    gaccessor_pre (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k) sl' /\
    no_lookahead_on_precond (parse_sum t p pc) sl sl'
  ))
  (ensures (gaccessor_clens_sum_payload' t p pc k sl == gaccessor_clens_sum_payload' t p pc k sl'))
= parse_sum_eq'' t p pc sl;
  parse_sum_eq'' t p pc sl' ;
  parse_strong_prefix (parse_sum t p pc) sl sl' ;
  parse_injective p sl sl'

let gaccessor_clens_sum_payload
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (gaccessor (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_clens_sum_payload_injective t p pc k x));
  Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_clens_sum_payload_no_lookahead t p pc k x));
  gaccessor_prop_equiv (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k) (gaccessor_clens_sum_payload' t p pc k);
  gaccessor_clens_sum_payload' t p pc k

inline_for_extraction
let accessor_clens_sum_payload'
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid (parse_sum t p pc) h input pos /\
    (clens_sum_payload t k).clens_cond (contents (parse_sum t p pc) h input pos)
  ))
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    pos' == slice_access h (gaccessor_clens_sum_payload t p pc k) input pos
  ))
= 
  let h = HST.get () in
  [@inline_let]
  let _ =
    let pos' = get_valid_pos (parse_sum t p pc) h input pos in
    let large = bytes_of_slice_from h input pos in
    slice_access_eq h (gaccessor_clens_sum_payload t p pc k) input pos;
    valid_facts (parse_sum t p pc) h input pos;
    parse_sum_eq'' t p pc large;
    valid_facts p h input pos
  in
  j input pos

#pop-options

inline_for_extraction
let accessor_clens_sum_payload
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (accessor (gaccessor_clens_sum_payload t p pc k))
= fun #rrel #rel -> accessor_clens_sum_payload' t j pc k #rrel #rel

let clens_sum_cases_payload
  (s: sum)
  (k: sum_key s)
: Tot (clens (sum_cases s k) (sum_type_of_tag s k))
= {
    clens_cond = (fun (x: sum_cases s k) -> True);
    clens_get = (fun (x: sum_cases s k) -> synth_sum_case_recip s k x <: Ghost (sum_type_of_tag s k) (requires (True)) (ensures (fun _ -> True)));
  }

let gaccessor_clens_sum_cases_payload
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (gaccessor (parse_sum_cases' t pc k) (dsnd (pc k)) (clens_sum_cases_payload t k))
= synth_sum_case_injective t k;
  synth_sum_case_inverse t k;
  synth_injective_synth_inverse_synth_inverse_recip (synth_sum_case t k) (synth_sum_case_recip t k) ();
  gaccessor_ext
    (gaccessor_synth (dsnd (pc k)) (synth_sum_case t k) (synth_sum_case_recip t k) ())
    (clens_sum_cases_payload t k)
    ()

inline_for_extraction
let accessor_clens_sum_cases_payload
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (accessor (gaccessor_clens_sum_cases_payload t pc k))
= [@inline_let]
  let _ =
    synth_sum_case_injective t k;
    synth_sum_case_inverse t k;
    synth_injective_synth_inverse_synth_inverse_recip (synth_sum_case t k) (synth_sum_case_recip t k) ()
  in
  accessor_ext
    (accessor_synth (dsnd (pc k)) (synth_sum_case t k) (synth_sum_case_recip t k) ())
    (clens_sum_cases_payload t k)
    ()

inline_for_extraction
let validate_dsum_cases_t
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot Type
= validator (parse_dsum_cases' s f g x)

let validate_dsum_cases_eq
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (v1 v2 : validate_dsum_cases_t s f g x)
: GTot Type0
= True

inline_for_extraction
let validate_dsum_cases_if'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (cond: bool)
  (ift: (cond_true cond -> Tot (validate_dsum_cases_t s f g x)))
  (iff: (cond_false cond -> Tot (validate_dsum_cases_t s f g x)))
: Tot (validate_dsum_cases_t s f g x)
= fun #rrel #rel input len ->
  if cond
  then (ift () <: validate_dsum_cases_t s f g x) input len
  else (iff () <: validate_dsum_cases_t s f g x) input len

inline_for_extraction
let validate_dsum_cases_if
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (if_combinator _ (validate_dsum_cases_eq s f g x))
= validate_dsum_cases_if' s f g x

inline_for_extraction
let validate_dsum_cases'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (validator (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : validator g)
  (x: dsum_key s)
: Tot (validate_dsum_cases_t s f g x)
= [@inline_let]
  let _ = synth_dsum_case_injective s x in
  match x with
  | Known x' -> validate_synth (f' x') (synth_dsum_case s (Known x')) () <: validator (parse_dsum_cases' s f g x)
  | Unknown x' -> validate_synth g' (synth_dsum_case s (Unknown x')) () <: validator (parse_dsum_cases' s f g x)

inline_for_extraction
let validate_dsum_cases'_destr
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (validator (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : validator g)
  (destr: dep_enum_destr _ (fun k -> validate_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (validate_dsum_cases_t s f g x)
= fun #rrel #rel input pos ->
  match x with
  | Known k ->
    destr
      _
      (fun k -> validate_dsum_cases_if s f g (Known k))
      (fun _ _ -> ())
      (fun _ _ _ _ -> ())
      (fun k -> validate_dsum_cases' s f f' g' (Known k))
      k
      input
      pos
  | Unknown r -> validate_dsum_cases' s f f' g' (Unknown r) input pos

inline_for_extraction
let validate_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (validator (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : validator g)
  (destr: dep_enum_destr _ (fun k -> validate_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (validator (parse_dsum_cases s f g x))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    valid_facts (parse_dsum_cases' s f g x) h input (uint64_to_uint32 pos);
    valid_facts (parse_dsum_cases s f g x) h input (uint64_to_uint32 pos);
    parse_dsum_cases_eq' s f g x (bytes_of_slice_from h input (uint64_to_uint32 pos))
  in
  validate_dsum_cases'_destr s f f' g' destr x input pos

#push-options "--z3rlimit 40"
inline_for_extraction
let validate_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (v: validator p)
  (p32: leaf_reader p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (validator (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: validator g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (validate_dsum_cases_t t f g))
: Tot (validator (parse_dsum t p f g))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = parse_dsum_eq' t p f g (bytes_of_slice_from h input (uint64_to_uint32 pos)) in
  [@inline_let]
  let _ = valid_facts (parse_dsum t p f g) h input (uint64_to_uint32 pos) in
  [@inline_let]
  let _ = valid_facts p h input (uint64_to_uint32 pos) in
  let pos_after_tag = v input pos in
  if is_error pos_after_tag
  then pos_after_tag
  else
    let tg = p32 input (uint64_to_uint32 pos) in
    [@inline_let]
    let _ = valid_facts (parse_dsum_cases' t f g (maybe_enum_key_of_repr (dsum_enum t) tg)) h input (uint64_to_uint32 pos_after_tag) in
    destr (validate_dsum_cases_eq t f g) (validate_dsum_cases_if t f g) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (validate_dsum_cases' t f f32 g32) tg input pos_after_tag
#pop-options

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --initial_ifuel 8 --max_ifuel 8 --initial_fuel 2 --max_fuel 2"

let valid_dsum_intro_known
  (h: HS.mem)
  (t: dsum)
  (#kt: parser_kind)
  (p: parser kt (dsum_repr_type t))
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_maybe_enum_key p (dsum_enum t)) h input pos /\ (
    let k' = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    Known? k' /\ (
    let Known k = k' in
    valid (dsnd (f k)) h input (get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos)
  ))))
  (ensures (
    let Known k = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    let pos_payload = get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    valid_content_pos
      (parse_dsum t p f g) h input pos
      (synth_dsum_case t (Known k) (contents (dsnd (f k)) h input pos_payload))
      (get_valid_pos (dsnd (f k)) h input pos_payload)
  ))
= valid_facts (parse_maybe_enum_key p (dsum_enum t)) h input pos;
  let Known k = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  let pos_payload = get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  valid_facts (dsnd (f k)) h input pos_payload;
  valid_facts (parse_dsum t p f g) h input pos;
  parse_dsum_eq t p f g (bytes_of_slice_from h input pos)

let valid_dsum_intro_unknown
  (h: HS.mem)
  (t: dsum)
  (#kt: parser_kind)
  (p: parser kt (dsum_repr_type t))
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_maybe_enum_key p (dsum_enum t)) h input pos /\ (
    let k' = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    Unknown? k' /\
    valid g h input (get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos)
  )))
  (ensures (
    let Unknown r = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    let pos_payload = get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    valid_content_pos
      (parse_dsum t p f g) h input pos
      (synth_dsum_case t (Unknown r) (contents g h input pos_payload))
      (get_valid_pos g h input pos_payload)
  ))
= valid_facts (parse_maybe_enum_key p (dsum_enum t)) h input pos;
  let Unknown r = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  let pos_payload = get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  valid_facts g h input pos_payload;
  valid_facts (parse_dsum t p f g) h input pos;
  parse_dsum_eq t p f g (bytes_of_slice_from h input pos)

#reset-options

inline_for_extraction
let finalize_dsum_case_known
  (t: dsum)
  (#kt: parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (w: leaf_writer_strong s)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (destr: enum_repr_of_key'_t (dsum_enum t))
  (k: dsum_known_key t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack unit
  (requires (fun h ->
    let len_tag = serialized_length (serialize_enum_key _ s (dsum_enum t)) k in
    U32.v pos + len_tag < 4294967296 /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t len_tag in
    valid (dsnd (f k)) h input pos_payload /\
    writable input.base (U32.v pos) (U32.v pos_payload) h
  )))
  (ensures (fun h _ h' ->
    let len_tag = serialized_length (serialize_enum_key _ s (dsum_enum t)) k in
    let pos_payload = pos `U32.add` U32.uint_to_t len_tag in
    B.modifies (loc_slice_from_to input pos pos_payload) h h' /\
    valid_content_pos (parse_dsum t p f g) h' input pos (synth_dsum_case t (Known k) (contents (dsnd (f k)) h input pos_payload)) (get_valid_pos (dsnd (f k)) h input pos_payload)
  ))
= let pos1 = write_enum_key w (dsum_enum t) destr k input pos in
  let h = HST.get () in
  [@inline_let]
  let _ =
    valid_facts (parse_enum_key p (dsum_enum t)) h input pos;
    valid_facts (parse_maybe_enum_key p (dsum_enum t)) h input pos;
    let sq = bytes_of_slice_from h input pos in
    parse_enum_key_eq p (dsum_enum t) sq;
    parse_maybe_enum_key_eq p (dsum_enum t) sq;
    valid_dsum_intro_known h t p f g input pos
  in
  ()

inline_for_extraction
let finalize_dsum_case_unknown
  (t: dsum)
  (#kt: parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (w: leaf_writer_strong s)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (r: unknown_enum_repr (dsum_enum t))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack unit
  (requires (fun h ->
    let len_tag = serialized_length s r in
    U32.v pos + len_tag < 4294967296 /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t len_tag in
    valid g h input pos_payload /\
    writable input.base (U32.v pos) (U32.v pos_payload) h
  )))
  (ensures (fun h _ h' ->
    let len_tag = serialized_length s r in
    let pos_payload = pos `U32.add` U32.uint_to_t len_tag in
    B.modifies (loc_slice_from_to input pos pos_payload) h h' /\
    valid_content_pos (parse_dsum t p f g) h' input pos (synth_dsum_case t (Unknown r) (contents g h input pos_payload)) (get_valid_pos g h input pos_payload)
  ))
= let pos1 = w r input pos in
  let h = HST.get () in
  [@inline_let]
  let _ =
    valid_facts (parse_maybe_enum_key p (dsum_enum t)) h input pos;
    valid_facts p h input pos;
    let sq = bytes_of_slice_from h input pos in
    parse_maybe_enum_key_eq p (dsum_enum t) sq;
    valid_dsum_intro_unknown h t p f g input pos
  in
  ()

let valid_dsum_elim_tag
  (h: HS.mem)
  (t: dsum)
  (#kt: parser_kind)
  (p: parser kt (dsum_repr_type t))
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_dsum t p f g) h input pos
  ))
  (ensures (
    valid (parse_maybe_enum_key p (dsum_enum t)) h input pos /\
    contents (parse_maybe_enum_key p (dsum_enum t)) h input pos == dsum_tag_of_data t (contents (parse_dsum t p f g) h input pos)
  ))
= let _ = parse_dsum_eq_ t p f g (bytes_of_slice_from h input pos) in
  let _ = valid_facts (parse_dsum t p f g) h input pos in
  let _ = valid_facts (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  ()

inline_for_extraction
let read_dsum_tag
  (t: dsum)
  (#kt: parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (p32: leaf_reader p)
  (destr: maybe_enum_destr_t (maybe_enum_key (dsum_enum t)) (dsum_enum t))  
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack (dsum_key t)
  (requires (fun h ->
    valid (parse_dsum t p f g) h input pos
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == dsum_tag_of_data t (contents (parse_dsum t p f g) h input pos)
  ))
= let h = HST.get () in
  [@inline_let] let _ = valid_dsum_elim_tag h t p f g input pos in
  read_maybe_enum_key p32 (dsum_enum t) destr input pos 

#push-options "--z3rlimit 32"
let valid_dsum_elim_known
  (h: HS.mem)
  (t: dsum)
  (#kt: parser_kind)
  (p: parser kt (dsum_repr_type t))
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_dsum t p f g) h input pos /\
    Known? (dsum_tag_of_data t (contents (parse_dsum t p f g) h input pos))
  ))
  (ensures (
    valid (parse_maybe_enum_key p (dsum_enum t)) h input pos /\ (
    let k' = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    let pos_payload = get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    Known? k' /\ (
    let Known k = k' in
    valid (dsnd (f k)) h input pos_payload /\
    valid_content_pos
      (parse_dsum t p f g) h input pos
      (synth_dsum_case t (Known k) (contents (dsnd (f k)) h input pos_payload))
      (get_valid_pos (dsnd (f k)) h input pos_payload)
  ))))
= 
  valid_facts (parse_dsum t p f g) h input pos;
  parse_dsum_eq t p f g (bytes_of_slice_from h input pos);
  valid_facts (parse_maybe_enum_key p (dsum_enum t)) h input pos;
  let Known k = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  let pos_payload = get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  valid_facts (dsnd (f k)) h input pos_payload
#pop-options

let valid_dsum_elim_unknown
  (h: HS.mem)
  (t: dsum)
  (#kt: parser_kind)
  (p: parser kt (dsum_repr_type t))
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_dsum t p f g) h input pos /\
    Unknown? (dsum_tag_of_data t (contents (parse_dsum t p f g) h input pos))
  ))
  (ensures (
    valid (parse_maybe_enum_key p (dsum_enum t)) h input pos /\ (
    let k' = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    let pos_payload = get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    Unknown? k' /\ (
    let Unknown r = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
    valid g h input pos_payload /\
    valid_content_pos
      (parse_dsum t p f g) h input pos
      (synth_dsum_case t (Unknown r) (contents g h input pos_payload))
      (get_valid_pos g h input pos_payload)
  ))))
= 
  valid_facts (parse_dsum t p f g) h input pos;
  parse_dsum_eq t p f g (bytes_of_slice_from h input pos);
  valid_facts (parse_maybe_enum_key p (dsum_enum t)) h input pos;
  let Unknown r = contents (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  let pos_payload = get_valid_pos (parse_maybe_enum_key p (dsum_enum t)) h input pos in
  valid_facts g h input pos_payload

inline_for_extraction
let jump_dsum_cases_t
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot Type
= jumper (parse_dsum_cases' s f g x)

let jump_dsum_cases_eq
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (v1 v2 : jump_dsum_cases_t s f g x)
: GTot Type0
= True

inline_for_extraction
let jump_dsum_cases_if'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (cond: bool)
  (ift: (cond_true cond -> Tot (jump_dsum_cases_t s f g x)))
  (iff: (cond_false cond -> Tot (jump_dsum_cases_t s f g x)))
: Tot (jump_dsum_cases_t s f g x)
= fun #rrel #rel input len ->
  if cond
  then (ift () <: jump_dsum_cases_t s f g x) input len
  else (iff () <: jump_dsum_cases_t s f g x) input len

inline_for_extraction
let jump_dsum_cases_if
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (if_combinator _ (jump_dsum_cases_eq s f g x))
= jump_dsum_cases_if' s f g x

inline_for_extraction
let jump_dsum_cases'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (jumper (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : jumper g)
  (x: dsum_key s)
: Tot (jump_dsum_cases_t s f g x)
= synth_dsum_case_injective s x;
  match x with
  | Known x' -> jump_synth (f' x') (synth_dsum_case s (Known x')) () <: jumper (parse_dsum_cases' s f g x)
  | Unknown x' -> jump_synth g' (synth_dsum_case s (Unknown x')) () <: jumper (parse_dsum_cases' s f g x)

inline_for_extraction
let jump_dsum_cases'_destr
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (jumper (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : jumper g)
  (destr: dep_enum_destr _ (fun k -> jump_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (jump_dsum_cases_t s f g x)
= fun #rrel #rel input pos ->
  match x with
  | Known k ->
    destr
      _
      (fun k -> jump_dsum_cases_if s f g (Known k))
      (fun _ _ -> ())
      (fun _ _ _ _ -> ())
      (fun k -> jump_dsum_cases' s f f' g' (Known k))
      k
      input
      pos
  | Unknown r -> jump_dsum_cases' s f f' g' (Unknown r) input pos

inline_for_extraction
let jump_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (jumper (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : jumper g)
  (destr: dep_enum_destr _ (fun k -> jump_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (jumper (parse_dsum_cases s f g x))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    valid_facts (parse_dsum_cases' s f g x) h input pos;
    valid_facts (parse_dsum_cases s f g x) h input pos;
    parse_dsum_cases_eq' s f g x (bytes_of_slice_from h input pos)
  in
  jump_dsum_cases'_destr s f f' g' destr x input pos

#push-options "--z3rlimit 16"

inline_for_extraction
let jump_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (v: jumper p)
  (p32: leaf_reader p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (jumper (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: jumper g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (jump_dsum_cases_t t f g))
: Tot (jumper (parse_dsum t p f g))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = parse_dsum_eq' t p f g (bytes_of_slice_from h input pos) in
  [@inline_let]
  let _ = valid_facts (parse_dsum t p f g) h input pos in
  [@inline_let]
  let _ = valid_facts p h input pos in
  let pos_after_tag = v input pos in
  let tg = p32 input pos in
  [@inline_let]
  let _ = valid_facts (parse_dsum_cases' t f g (maybe_enum_key_of_repr (dsum_enum t) tg)) h input pos_after_tag in
  destr (jump_dsum_cases_eq t f g) (jump_dsum_cases_if t f g) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (jump_dsum_cases' t f f32 g32) tg input pos_after_tag

#pop-options

inline_for_extraction
let read_dsum_cases'
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (leaf_reader (dsnd (f x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (g32: leaf_reader g)
  (x: dsum_key t)
: Tot (leaf_reader (parse_dsum_cases' t f g x))
= fun #rrel #rel input pos ->
  [@inline_let]
  let _ = synth_dsum_case_injective t x in
  match x with
  | Known x' ->
    read_synth'
      (dsnd (f x'))
      (synth_dsum_case t (Known x'))
      (f32 x')
      ()
      input
      pos
  | Unknown x' ->
    read_synth'
      g
      (synth_dsum_case t (Unknown x'))
      g32
      ()
      input
      pos

inline_for_extraction
let read_dsum_cases_t
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (k: dsum_known_key t)
: Tot Type
= leaf_reader (parse_dsum_cases' t f g (Known k))

let read_dsum_cases_t_eq
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (k: dsum_known_key t)
  (x y : read_dsum_cases_t t f g k)
: GTot Type0
= True

inline_for_extraction
let read_dsum_cases_t_if
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (k: dsum_known_key t)
: Tot (if_combinator _ (read_dsum_cases_t_eq t f g k))
= fun cond (sv_true: cond_true cond -> Tot (read_dsum_cases_t t f g k)) (sv_false: cond_false cond -> Tot (read_dsum_cases_t t f g k)) #_ #_ input pos ->
  if cond
  then sv_true () input pos
  else sv_false () input pos

inline_for_extraction
let read_dsum_cases 
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (leaf_reader (dsnd (f x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (g32: leaf_reader g)
  (destr: dep_enum_destr _ (read_dsum_cases_t t f g))
  (x: dsum_key t)
: Tot (leaf_reader (parse_dsum_cases' t f g x))
= fun #_ #_ input pos ->
  match x with
  | Known k ->
    destr
      _
      (read_dsum_cases_t_if t f g)
      (fun _ _ -> ())
      (fun _ _ _ _ -> ())
      (fun k -> read_dsum_cases' t f f32 g g32 (Known k))
      k
      input
      pos
  | Unknown r ->
    read_dsum_cases' t f f32 g g32 (Unknown r) input pos

#push-options "--z3rlimit 16"

inline_for_extraction
let read_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (p32: leaf_reader (parse_maybe_enum_key p (dsum_enum t)))
  (j: jumper p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (leaf_reader (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: leaf_reader g)
  (destr: dep_enum_destr _ (read_dsum_cases_t t f g))
: Tot (leaf_reader (parse_dsum t p f g))
= fun #_ #_ input pos ->
  let h = HST.get () in
  valid_facts (parse_dsum t p f g) h input pos;
  parse_dsum_eq_ t p f g (bytes_of_slice_from h input pos);
  valid_facts (parse_maybe_enum_key p (dsum_enum t)) h input pos;
  let k = p32 input pos in
  let pos' = jump_maybe_enum_key j (dsum_enum t) input pos  in
  valid_facts (parse_dsum_cases' t f g k) h input pos' ;
  read_dsum_cases t f f32 g g32 destr k input pos'

#pop-options

inline_for_extraction
let serialize32_dsum_type_of_tag
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (serializer32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: serializer32 sg)
  (tg: dsum_key t)
: Tot (serializer32 (serialize_dsum_type_of_tag t f sf g sg tg))
= match tg with
  | Known x' -> serialize32_ext (dsnd (f x')) (sf x') (sf32 x') (parse_dsum_type_of_tag t f g tg) ()
  | Unknown x' -> serialize32_ext g sg sg32 (parse_dsum_type_of_tag t f g tg) ()

inline_for_extraction
let serialize32_dsum_cases_aux
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (serializer32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: serializer32 sg)
  (tg: dsum_key t)
: Tot (serializer32 (serialize_dsum_cases t f sf g sg tg))
= [@inline_let]
  let _ = synth_dsum_case_injective t tg in
  [@inline_let]
  let _ = synth_dsum_case_inverse t tg in
  serialize32_synth
    (serialize32_dsum_type_of_tag t f sf sf32 sg32 tg)
    (synth_dsum_case t tg) 
    (synth_dsum_case_recip t tg)
    (fun x -> synth_dsum_case_recip t tg x)
    ()

inline_for_extraction
let serialize32_dsum_cases_t
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (k: dsum_known_key t)
: Tot Type
= serializer32 (serialize_dsum_cases t f sf g sg (Known k))

let serialize32_dsum_cases_t_eq
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (k: dsum_known_key t)
  (x y: serialize32_dsum_cases_t t f sf g sg k)
: GTot Type0
= True

inline_for_extraction
let serialize32_dsum_cases_t_if
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (k: dsum_known_key t)
: Tot (if_combinator _ (serialize32_dsum_cases_t_eq t f sf g sg k))
= fun cond (sv_true: (cond_true cond -> Tot (serialize32_dsum_cases_t t f sf g sg k))) (sv_false: (cond_false cond -> Tot (serialize32_dsum_cases_t t f sf g sg k))) x #rrel #rel output pos ->
  if cond
  then (sv_true () x output pos)
  else (sv_false () x output pos)

inline_for_extraction
let serialize32_dsum_cases
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (serializer32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: serializer32 sg)
  (destr: dep_enum_destr _ (serialize32_dsum_cases_t t f sf g sg))
  (tg: dsum_key t)
: Tot (serializer32 (serialize_dsum_cases t f sf g sg tg))
= fun x #rrel #rel output pos ->
  match tg with
  | Known k ->
    destr
      _
      (serialize32_dsum_cases_t_if t f sf g sg)
      (fun _ _ -> ())
      (fun _ _ _ _ -> ())
      (fun k -> serialize32_dsum_cases_aux t f sf sf32 sg32 (Known k))
      k
      x
      output
      pos
  | Unknown r ->
    serialize32_dsum_cases_aux t f sf sf32 sg32 (Unknown r) x output pos

inline_for_extraction
let serialize32_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p {kt.parser_kind_subkind == Some ParserStrong})
  (s32: serializer32 (serialize_maybe_enum_key _ s (dsum_enum t)))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (serializer32 (sf x)))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (#sg: serializer g)
  (sg32: serializer32 sg)
  (destr: dep_enum_destr _ (serialize32_dsum_cases_t t f sf g sg))
: Tot (serializer32 (serialize_dsum t s f sf g sg))
= fun x #_ #_ output pos ->
  [@inline_let]
  let _ = serialize_dsum_eq' t s f sf g sg x in
  let tg = dsum_tag_of_data t x in
  serialize32_nondep_then_aux
    s32
    (serialize32_dsum_cases t f sf sf32 sg32 destr tg)
    tg
    x
    output
    pos

let clens_dsum_tag
  (s: dsum)
: Tot (clens (dsum_type s) (dsum_key s))
= {
    clens_cond = (fun _ -> True);
    clens_get = dsum_tag_of_data s;
  }

let gaccessor_dsum_tag
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
: Tot (gaccessor (parse_dsum t p f g) (parse_maybe_enum_key p (dsum_enum t)) (clens_dsum_tag t))
= gaccessor_tagged_union_tag
    (parse_maybe_enum_key p (dsum_enum t))
    (dsum_tag_of_data t)
    (parse_dsum_cases t f g)

inline_for_extraction
let accessor_dsum_tag
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
: Tot (accessor (gaccessor_dsum_tag t p f g))
= accessor_tagged_union_tag
    (parse_maybe_enum_key p (dsum_enum t))
    (dsum_tag_of_data t)
    (parse_dsum_cases t f g)

let clens_dsum_payload
  (s: dsum)
  (k: dsum_key s)
: Tot (clens (dsum_type s) (dsum_type_of_tag s k))
= {
    clens_cond = (fun (x: dsum_type s) -> dsum_tag_of_data s x == k);
    clens_get = (fun (x: dsum_type s) -> synth_dsum_case_recip s k x <: Ghost (dsum_type_of_tag s k) (requires (dsum_tag_of_data s x == k)) (ensures (fun _ -> True)));
  }

let clens_dsum_unknown_payload
  (s: dsum)
: Tot (clens (dsum_type s) (dsum_type_of_unknown_tag s))
= {
    clens_cond = (fun (x: dsum_type s) -> Unknown? (dsum_tag_of_data s x));
    clens_get = (fun (x: dsum_type s) -> synth_dsum_case_recip s (dsum_tag_of_data s x) x <: Ghost (dsum_type_of_unknown_tag s) (requires (Unknown? (dsum_tag_of_data s x))) (ensures (fun _ -> True)));
  }

#push-options "--z3rlimit 16"

let gaccessor_clens_dsum_payload'
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_key t)
: Tot (gaccessor' (parse_dsum t p f g) (parse_dsum_type_of_tag' t f g k) (clens_dsum_payload t k))
= fun (input: bytes) ->
  parse_dsum_eq3 t p f g input;
  let res =
    match parse p input with
    | Some (_, consumed) ->
      synth_dsum_case_inverse t k;
      synth_dsum_case_injective t k;
      synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t k) (synth_dsum_case_recip t k) ();
      (consumed)
    | _ -> (0) // dummy
  in
  (res <: (res: _ { gaccessor_post'  (parse_dsum t p f g) (parse_dsum_type_of_tag' t f g k) (clens_dsum_payload t k) input res } ))

let gaccessor_clens_dsum_payload_injective
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_key t)
  (sl sl' : bytes)
: Lemma
  (requires (
    gaccessor_pre (parse_dsum t p f g) (parse_dsum_type_of_tag' t f g k) (clens_dsum_payload t k) sl /\
    gaccessor_pre (parse_dsum t p f g) (parse_dsum_type_of_tag' t f g k) (clens_dsum_payload t k) sl' /\
    injective_precond (parse_dsum t p f g) sl sl'
  ))
  (ensures (
    gaccessor_clens_dsum_payload' t p f g k sl == gaccessor_clens_dsum_payload' t p f g k sl'
  ))
= 
  parse_dsum_eq3 t p f g sl;
  parse_dsum_eq3 t p f g sl';
  parse_injective (parse_dsum t p f g) sl sl' ;
  parse_injective p sl sl'

let gaccessor_clens_dsum_payload_no_lookahead
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_key t)
  (sl sl' : bytes)
: Lemma
  (requires (
    (parse_dsum_kind kt t f ku).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_dsum t p f g) (parse_dsum_type_of_tag' t f g k) (clens_dsum_payload t k) sl /\
    gaccessor_pre (parse_dsum t p f g) (parse_dsum_type_of_tag' t f g k) (clens_dsum_payload t k) sl' /\
    no_lookahead_on_precond (parse_dsum t p f g) sl sl'
  ))
  (ensures (
    gaccessor_clens_dsum_payload' t p f g k sl == gaccessor_clens_dsum_payload' t p f g k sl'
  ))
= parse_dsum_eq3 t p f g sl;
  parse_dsum_eq3 t p f g sl';
  parse_strong_prefix (parse_dsum t p f g) sl sl' ;
  parse_injective p sl sl'

let gaccessor_clens_dsum_payload
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_key t)
: Tot (gaccessor (parse_dsum t p f g) (parse_dsum_type_of_tag' t f g k) (clens_dsum_payload t k))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_clens_dsum_payload_injective t p f g k x));
  Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_clens_dsum_payload_no_lookahead t p f g k x));
  gaccessor_prop_equiv (parse_dsum t p f g) (parse_dsum_type_of_tag' t f g k) (clens_dsum_payload t k) (gaccessor_clens_dsum_payload' t p f g k);
  gaccessor_clens_dsum_payload' t p f g k

inline_for_extraction
let accessor_clens_dsum_payload'
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (j: jumper p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_key t)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid (parse_dsum t p f g) h input pos /\
    (clens_dsum_payload t k).clens_cond (contents (parse_dsum t p f g) h input pos)
  ))
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    pos' == slice_access h (gaccessor_clens_dsum_payload t p f g k) input pos
  ))
= 
  let h = HST.get () in
  [@inline_let]
  let _ =
    let pos' = get_valid_pos (parse_dsum t p f g) h input pos in
    let large = bytes_of_slice_from h input pos in
    slice_access_eq h (gaccessor_clens_dsum_payload t p f g k) input pos;
    valid_facts (parse_dsum t p f g) h input pos;
    parse_dsum_eq3 t p f g large;
    valid_facts p h input pos
  in
  j input pos

#pop-options

inline_for_extraction
let accessor_clens_dsum_payload
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (j: jumper p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_key t)
: Tot (accessor (gaccessor_clens_dsum_payload t p f g k))
= fun #rrel #rel -> accessor_clens_dsum_payload' t j f g k #rrel #rel

#push-options "--z3rlimit 16"

let gaccessor_clens_dsum_unknown_payload'
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
: Tot (gaccessor' (parse_dsum t p f g) g (clens_dsum_unknown_payload t))
= fun (input: bytes) ->
  parse_dsum_eq3 t p f g input;
  let res =
    match parse p input with
    | Some (tg, consumed) ->
      let k = maybe_enum_key_of_repr (dsum_enum t) tg in
      synth_dsum_case_inverse t k;
      synth_dsum_case_injective t k;
      synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t k) (synth_dsum_case_recip t k) ();
      (consumed)
    | _ -> (0) // dummy
  in
  (res <: (res: _ { gaccessor_post'  (parse_dsum t p f g) g (clens_dsum_unknown_payload t) input res } ))

let gaccessor_clens_dsum_unknown_payload_injective
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (sl sl' : bytes)
: Lemma
  (requires (
    gaccessor_pre (parse_dsum t p f g) g (clens_dsum_unknown_payload t) sl /\
    gaccessor_pre (parse_dsum t p f g) g (clens_dsum_unknown_payload t) sl' /\
    injective_precond (parse_dsum t p f g) sl sl'
  ))
  (ensures (gaccessor_clens_dsum_unknown_payload' t p f g sl == gaccessor_clens_dsum_unknown_payload' t p f g sl'))
= parse_dsum_eq3 t p f g sl;
  parse_dsum_eq3 t p f g sl';
  parse_injective (parse_dsum t p f g) sl sl' ;
  parse_injective p sl sl'

let gaccessor_clens_dsum_unknown_payload_no_lookahead
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (sl sl' : bytes)
: Lemma
  (requires (
    (parse_dsum_kind kt t f ku).parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre (parse_dsum t p f g) g (clens_dsum_unknown_payload t) sl /\
    gaccessor_pre (parse_dsum t p f g) g (clens_dsum_unknown_payload t) sl' /\
    no_lookahead_on_precond (parse_dsum t p f g) sl sl'
  ))
  (ensures (gaccessor_clens_dsum_unknown_payload' t p f g sl == gaccessor_clens_dsum_unknown_payload' t p f g sl'))
=
  parse_dsum_eq3 t p f g sl;
  parse_dsum_eq3 t p f g sl';
  parse_strong_prefix (parse_dsum t p f g) sl sl' ;
  parse_injective p sl sl'

let gaccessor_clens_dsum_unknown_payload
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
: Tot (gaccessor (parse_dsum t p f g) g (clens_dsum_unknown_payload t))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_clens_dsum_unknown_payload_injective t p f g x));
  Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_clens_dsum_unknown_payload_no_lookahead t p f g x));
  gaccessor_prop_equiv (parse_dsum t p f g) g (clens_dsum_unknown_payload t) (gaccessor_clens_dsum_unknown_payload' t p f g); 
  gaccessor_clens_dsum_unknown_payload' t p f g

inline_for_extraction
let accessor_clens_dsum_unknown_payload'
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (j: jumper p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid (parse_dsum t p f g) h input pos /\
    (clens_dsum_unknown_payload t).clens_cond (contents (parse_dsum t p f g) h input pos)
  ))
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    pos' == slice_access h (gaccessor_clens_dsum_unknown_payload t p f g) input pos
  ))
= 
  let h = HST.get () in
  [@inline_let]
  let _ =
    let pos' = get_valid_pos (parse_dsum t p f g) h input pos in
    let large = bytes_of_slice_from h input pos in
    slice_access_eq h (gaccessor_clens_dsum_unknown_payload t p f g) input pos;
    valid_facts (parse_dsum t p f g) h input pos;
    parse_dsum_eq3 t p f g large;
    valid_facts p h input pos
  in
  j input pos

#pop-options

inline_for_extraction
let accessor_clens_dsum_unknown_payload
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (j: jumper p { kt.parser_kind_subkind == Some ParserStrong })
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
: Tot (accessor (gaccessor_clens_dsum_unknown_payload t p f g))
= fun #rrel #rel -> accessor_clens_dsum_unknown_payload' t j f g #rrel #rel

let clens_dsum_cases_payload
  (s: dsum)
  (k: dsum_key s)
: Tot (clens (dsum_cases s k) (dsum_type_of_tag s k))
= {
    clens_cond = (fun (x: dsum_cases s k) -> True);
    clens_get = (fun (x: dsum_cases s k) -> synth_dsum_case_recip s k x <: Ghost (dsum_type_of_tag s k) (requires (True)) (ensures (fun _ -> True)));
  }

let gaccessor_clens_dsum_cases_known_payload
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_known_key t)
: Tot (gaccessor (parse_dsum_cases' t f g (Known k)) (dsnd (f k)) (clens_dsum_cases_payload t (Known k)))
= synth_dsum_case_injective t (Known k);
  synth_dsum_case_inverse t (Known k);
  synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t (Known k)) (synth_dsum_case_recip t (Known k)) ();
  gaccessor_ext
    (gaccessor_synth (dsnd (f k)) (synth_dsum_case t (Known k)) (synth_dsum_case_recip t (Known k)) ())
    (clens_dsum_cases_payload t (Known k))
    ()

inline_for_extraction
let accessor_clens_dsum_cases_known_payload
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_known_key t)
: Tot (accessor (gaccessor_clens_dsum_cases_known_payload t f g k))
= [@inline_let]
  let _ =
    synth_dsum_case_injective t (Known k);
    synth_dsum_case_inverse t (Known k);
    synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t (Known k)) (synth_dsum_case_recip t (Known k)) ()
  in
  accessor_ext
    (accessor_synth (dsnd (f k)) (synth_dsum_case t (Known k)) (synth_dsum_case_recip t (Known k)) ())
    (clens_dsum_cases_payload t (Known k))
    ()

let gaccessor_clens_dsum_cases_unknown_payload
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_unknown_key t)
: Tot (gaccessor (parse_dsum_cases' t f g (Unknown k)) g (clens_dsum_cases_payload t (Unknown k)))
= synth_dsum_case_injective t (Unknown k);
  synth_dsum_case_inverse t (Unknown k);
  synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t (Unknown k)) (synth_dsum_case_recip t (Unknown k)) ();
  gaccessor_ext
    (gaccessor_synth g (synth_dsum_case t (Unknown k)) (synth_dsum_case_recip t (Unknown k)) ())
    (clens_dsum_cases_payload t (Unknown k))
    ()

inline_for_extraction
let accessor_clens_dsum_cases_unknown_payload
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#ku: parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_unknown_key t)
: Tot (accessor (gaccessor_clens_dsum_cases_unknown_payload t f g k))
= [@inline_let]
  let _ =
    synth_dsum_case_injective t (Unknown k);
    synth_dsum_case_inverse t (Unknown k);
    synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t (Unknown k)) (synth_dsum_case_recip t (Unknown k)) ()
  in
  accessor_ext
    (accessor_synth g (synth_dsum_case t (Unknown k)) (synth_dsum_case_recip t (Unknown k)) ())
    (clens_dsum_cases_payload t (Unknown k))
    ()

module LowParse.Low.BitSum
include LowParse.Low.Base
include LowParse.Spec.BitSum

module U32 = FStar.UInt32
module HS = FStar.HyperStack

#push-options "--z3rlimit 16"

let valid_bitsum_intro
  (#kt: parser_kind)
  (b: bitsum)
  (p: parser kt b.t)
  (f: (x: bitsum'_key_type b.b) -> Tot (k: parser_kind & parser k (bitsum_type_of_tag b x)))
  (h: HS.mem)
  (#rrel: _)
  (#rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bitsum' b.b p) h sl pos /\ (
    let tg = contents (parse_bitsum' b.b p) h sl pos in
    let k = bitsum'_key_of_t b.b tg in
    valid (dsnd (f k)) h sl (get_valid_pos (parse_bitsum' b.b p) h sl pos)
  )))
  (ensures (
    let tg = contents (parse_bitsum' b.b p) h sl pos in
    let k = bitsum'_key_of_t b.b tg in
    let pos1 = get_valid_pos (parse_bitsum' b.b p) h sl pos in
    let y = contents (dsnd (f k)) h sl pos1 in
    valid_content_pos (parse_bitsum b p f) h sl pos (b.synth_case.f tg y) (get_valid_pos (dsnd (f k)) h sl pos1)
  ))
= valid_facts (parse_bitsum b p f) h sl pos;
  parse_bitsum_eq b p f (bytes_of_slice_from h sl pos);
  valid_facts (parse_bitsum' b.b p) h sl pos;
  let tg = contents (parse_bitsum' b.b p) h sl pos in
  let k = bitsum'_key_of_t b.b tg in
  let pos1 = get_valid_pos (parse_bitsum' b.b p) h sl pos in
  valid_facts (dsnd (f k)) h sl pos1

let valid_bitsum_elim'
  (#kt: parser_kind)
  (b: bitsum)
  (p: parser kt b.t)
  (f: (x: bitsum'_key_type b.b) -> Tot (k: parser_kind & parser k (bitsum_type_of_tag b x)))
  (h: HS.mem)
  (#rrel: _)
  (#rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bitsum b p f) h sl pos
  ))
  (ensures (
    valid (parse_bitsum' b.b p) h sl pos /\ (
    let tg = contents (parse_bitsum' b.b p) h sl pos in
    let k = bitsum'_key_of_t b.b tg in
    let pos1 = get_valid_pos (parse_bitsum' b.b p) h sl pos in
    valid (dsnd (f k)) h sl pos1 /\ (
    let y = contents (dsnd (f k)) h sl pos1 in
    valid_content_pos (parse_bitsum b p f) h sl pos (b.synth_case.f tg y) (get_valid_pos (dsnd (f k)) h sl pos1)
  ))))
= valid_facts (parse_bitsum b p f) h sl pos;
  parse_bitsum_eq b p f (bytes_of_slice_from h sl pos);
  valid_facts (parse_bitsum' b.b p) h sl pos;
  let tg = contents (parse_bitsum' b.b p) h sl pos in
  let k = bitsum'_key_of_t b.b tg in
  let pos1 = get_valid_pos (parse_bitsum' b.b p) h sl pos in
  valid_facts (dsnd (f k)) h sl pos1;
  valid_bitsum_intro b p f h sl pos

let valid_bitsum_elim
  (#kt: parser_kind)
  (b: bitsum)
  (p: parser kt b.t)
  (f: (x: bitsum'_key_type b.b) -> Tot (k: parser_kind & parser k (bitsum_type_of_tag b x)))
  (h: HS.mem)
  (#rrel: _)
  (#rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bitsum b p f) h sl pos
  ))
  (ensures (
    valid (parse_bitsum' b.b p) h sl pos /\ (
    let tg = contents (parse_bitsum' b.b p) h sl pos in
    let k = bitsum'_key_of_t b.b tg in
    let pos1 = get_valid_pos (parse_bitsum' b.b p) h sl pos in
    valid (dsnd (f k)) h sl pos1 /\
    valid_pos (parse_bitsum b p f) h sl pos (get_valid_pos (dsnd (f k)) h sl pos1) /\ (
    let x = contents (parse_bitsum b p f) h sl pos in
    let y = contents (dsnd (f k)) h sl pos1 in
    tg == b.tag_of_data (bitsum'_type b.b) id x /\
    x == b.synth_case.f tg y /\
    y == b.synth_case.g tg x
  ))))
= valid_bitsum_elim' b p f h sl pos;
  let tg = contents (parse_bitsum' b.b p) h sl pos in
  let k = bitsum'_key_of_t b.b tg in
  let pos1 = get_valid_pos (parse_bitsum' b.b p) h sl pos in
  let x = contents (parse_bitsum b p f) h sl pos in
  let y = contents (dsnd (f k)) h sl pos1 in
  assert (tg == b.tag_of_data (bitsum'_type b.b) id x);
  assert (x == b.synth_case.f tg y);
  b.synth_case.f_g_eq tg x;
  b.synth_case.f_inj tg (b.synth_case.g tg x) y

#pop-options

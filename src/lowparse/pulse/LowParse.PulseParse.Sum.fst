module LowParse.PulseParse.Sum
#lang-pulse
include LowParse.PulseParse.Enum
include LowParse.Spec.Sum
open LowParse.PulseParse.Combinators

module B = LowParse.Pulse.Combinators

inline_for_extraction
let validate_sum_cases_aux
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (vc: ((x: sum_key t) -> Tot (B.validator (dsnd (pc x)))))
  (k: sum_key t)
: Tot (B.validator (parse_sum_cases t pc k))
= [@inline_let]
  let _ = synth_sum_case_injective t k in
  validate_synth
    (B.validate_weaken
      (weaken_parse_cases_kind t pc)
      (vc k)
    )
    (synth_sum_case t k)

inline_for_extraction
let validate_sum_cases_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot Type
= B.validator (parse_sum_cases t pc k)

inline_for_extraction
fn validate_sum_cases_t_if'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (validate_sum_cases_t t pc k)))
  (sv_false: (cond_false cond -> Tot (validate_sum_cases_t t pc k)))
: (validate_sum_cases_t t pc k)
=
  (input: _)
  (pos: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    sv_true () input pos
  } else {
    sv_false () input pos
  }
}

inline_for_extraction
let validate_sum_cases_t_if
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: (if_combinator (validate_sum_cases_t t pc k) eq_trivial)
= validate_sum_cases_t_if' t pc k

inline_for_extraction
let validate_sum_cases 
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (vc: ((x: sum_key t) -> Tot (B.validator (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (validate_sum_cases_t t pc))
  (k: sum_key t)
: Tot (B.validator (parse_sum_cases t pc k))
= destr
    _
    (validate_sum_cases_t_if t pc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (validate_sum_cases_aux t pc vc)
    k

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
open Pulse.Lib.Pervasives

let validate_sum_aux_payload_postcond
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
  (offset: SZ.t)
  (v: bytes)
  (off: SZ.t)
  (res: bool)
: Tot prop
= match k with
  | Unknown _ -> res == false
  | Known k' -> B.validator_postcond (dsnd (pc k')) offset v off res

inline_for_extraction
let validate_sum_aux_payload_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot Type
=
  (input: S.slice byte) ->
  (poffset: ref SZ.t) ->
  (#offset: Ghost.erased SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt bool
  (requires
    pts_to input #pm v **
    pts_to poffset offset **
    pure (SZ.v offset <= Seq.length v)
  )
  (ensures (fun res ->
    pts_to input #pm v **
    exists* off .
    pts_to poffset off **
    pure (validate_sum_aux_payload_postcond
      t pc k offset v off res
  )))

inline_for_extraction
fn validate_sum_aux_payload_if'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
  (cond: bool)
  (ift: ((cond_true cond) -> Tot (validate_sum_aux_payload_t t pc k)))
  (iff: ((cond_false cond) -> Tot (validate_sum_aux_payload_t t pc k)))
: (validate_sum_aux_payload_t t pc k)
=
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  if cond {
    ift () input poffset
  } else {
    iff () input poffset
  }
}

inline_for_extraction
let validate_sum_aux_payload_if
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot (if_combinator (validate_sum_aux_payload_t t pc k) eq_trivial)
= validate_sum_aux_payload_if' t pc k

module PPB = LowParse.PulseParse.Base

#push-options "--z3rlimit 64"

inline_for_extraction
fn validate_sum_aux
  (t: sum u#0 u#0)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: B.validator p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (v_payload: ((k: sum_repr_type t)) -> Tot (validate_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k)))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: (B.validator (parse_sum t p pc))
=
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_sum_eq'' t p pc sinput;
  let offset_val = !poffset;
  let is_valid_tag = v input poffset;
  if is_valid_tag {
    let off = !poffset;
    let k' = PPB.read_parsed_from_validator_success p32 input offset_val off;
    Seq.lemma_eq_elim
      (Seq.slice sinput (SZ.v off - SZ.v offset_val) (Seq.length sinput))
      (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    let res = v_payload k' input poffset;
    if res {
      true
    } else {
      poffset := offset_val;
      false
    }
  } else {
    false
  }
}

#pop-options

inline_for_extraction
fn validate_sum_aux_payload'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (B.validator (dsnd (pc x)))))
  (k: maybe_enum_key (sum_enum t))
: (validate_sum_aux_payload_t t pc k)
=
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  match k {
    Known k' -> { pc32 k' input poffset }
    Unknown _ -> { false }
  }
}

inline_for_extraction
let validate_sum_aux_payload
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (B.validator (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (validate_sum_aux_payload_t t pc))
  (k: sum_repr_type t)
: Tot (validate_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k))
= destr (fun _ -> eq_trivial) (validate_sum_aux_payload_if t pc) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (validate_sum_aux_payload' t pc pc32) k

inline_for_extraction
let validate_sum
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: B.validator p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (B.validator (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (validate_sum_aux_payload_t t pc))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: Tot (B.validator (parse_sum t p pc))
= validate_sum_aux t v p32 pc (validate_sum_aux_payload t pc pc32 destr) ()

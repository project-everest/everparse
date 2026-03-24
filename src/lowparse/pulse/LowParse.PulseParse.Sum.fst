module LowParse.PulseParse.Sum
#lang-pulse
include LowParse.PulseParse.Enum
include LowParse.Spec.Sum
open LowParse.PulseParse.Combinators
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade

module B = LowParse.Pulse.Combinators
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
let validate_sum_cases_aux
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (vc: ((x: sum_key t) -> Tot (B.validator (dsnd (pc x)))))
  (k: sum_key t)
: Tot (B.validator (parse_sum_cases t pc k))
= [@inline_let]
  let _ = synth_sum_case_injective t k in
  B.validate_synth
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

(* ========== DSum validators ========== *)

let validate_dsum_cases_t
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot Type
= B.validator (parse_dsum_cases' s f g x)

inline_for_extraction
fn validate_dsum_cases_if'
  (s: dsum u#0 u#0)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (cond: bool)
  (ift: (cond_true cond -> Tot (validate_dsum_cases_t s f g x)))
  (iff: (cond_false cond -> Tot (validate_dsum_cases_t s f g x)))
: (validate_dsum_cases_t s f g x)
=
  (input: _)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    ift () input poffset
  } else {
    iff () input poffset
  }
}

inline_for_extraction
let validate_dsum_cases_if
  (s: dsum u#0 u#0)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (if_combinator (validate_dsum_cases_t s f g x) eq_trivial)
= validate_dsum_cases_if' s f g x

inline_for_extraction
let validate_dsum_cases'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f': (x: dsum_known_key s) -> Tot (B.validator (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g': B.validator g)
  (x: dsum_key s)
: Tot (validate_dsum_cases_t s f g x)
= [@inline_let]
  let _ = synth_dsum_case_injective s x in
  match x with
  | Known x' -> B.validate_synth (f' x') (synth_dsum_case s (Known x'))
  | Unknown x' -> B.validate_synth g' (synth_dsum_case s (Unknown x'))

inline_for_extraction
let validate_dsum_cases_dispatch
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (B.validator (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: B.validator g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (validate_dsum_cases_t t f g))
  (tg: dsum_repr_type t)
: Tot (validate_dsum_cases_t t f g (maybe_enum_key_of_repr (dsum_enum t) tg))
= destr (fun _ -> eq_trivial) (validate_dsum_cases_if t f g) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (validate_dsum_cases' t f f32 g32) tg

inline_for_extraction
let validate_dsum_cases'_destr
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (B.validator (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : B.validator g)
  (destr: dep_enum_destr (dsum_enum s) (fun k -> validate_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (validate_dsum_cases_t s f g x)
= match x with
  | Known k ->
    destr
      _
      (fun k -> validate_dsum_cases_if s f g (Known k))
      (fun _ _ -> ())
      (fun _ _ _ _ -> ())
      (fun k -> validate_dsum_cases' s f f' g' (Known k))
      k
  | Unknown r -> validate_dsum_cases' s f f' g' (Unknown r)

inline_for_extraction
let validate_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (B.validator (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : B.validator g)
  (destr: dep_enum_destr (dsum_enum s) (fun k -> validate_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (B.validator (parse_dsum_cases s f g x))
= Classical.forall_intro (parse_dsum_cases_eq' s f g x);
  B.validate_ext (validate_dsum_cases'_destr s f f' g' destr x) (parse_dsum_cases s f g x)

#push-options "--z3rlimit 64"

inline_for_extraction
fn validate_dsum
  (#kt: parser_kind)
  (t: dsum u#0 u#0)
  (#p: parser kt (dsum_repr_type t))
  (v: B.validator p)
  (p32: leaf_reader p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (B.validator (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: B.validator g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (validate_dsum_cases_t t f g))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: B.validator (parse_dsum t p f g)
=
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_dsum_eq' t p f g sinput;
  let offset_val = !poffset;
  let is_valid_tag = v input poffset;
  if is_valid_tag {
    let off = !poffset;
    let tg = PPB.read_parsed_from_validator_success p32 input offset_val off;
    Seq.lemma_eq_elim
      (Seq.slice sinput (SZ.v off - SZ.v offset_val) (Seq.length sinput))
      (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    parse_dsum_cases_eq' t f g (maybe_enum_key_of_repr (dsum_enum t) tg) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    let res = validate_dsum_cases_dispatch t f f32 g32 destr tg input poffset;
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

(* ========== Sum jumpers ========== *)

inline_for_extraction
let jump_sum_cases_aux
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (jc: ((x: sum_key t) -> Tot (B.jumper (dsnd (pc x)))))
  (k: sum_key t)
: Tot (B.jumper (parse_sum_cases t pc k))
= [@inline_let]
  let _ = synth_sum_case_injective t k in
  B.jump_synth
    (B.jump_ext
      (jc k)
      (weaken (weaken_parse_cases_kind t pc) (dsnd (pc k)))
    )
    (synth_sum_case t k)

inline_for_extraction
let jump_sum_cases_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot Type
= B.jumper (parse_sum_cases t pc k)

inline_for_extraction
fn jump_sum_cases_t_if'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (jump_sum_cases_t t pc k)))
  (sv_false: (cond_false cond -> Tot (jump_sum_cases_t t pc k)))
: (jump_sum_cases_t t pc k)
=
  (input: _)
  (offset: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    sv_true () input offset
  } else {
    sv_false () input offset
  }
}

inline_for_extraction
let jump_sum_cases_t_if
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: (if_combinator (jump_sum_cases_t t pc k) eq_trivial)
= jump_sum_cases_t_if' t pc k

inline_for_extraction
let jump_sum_cases
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (jc: ((x: sum_key t) -> Tot (B.jumper (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (jump_sum_cases_t t pc))
  (k: sum_key t)
: Tot (B.jumper (parse_sum_cases t pc k))
= destr
    _
    (jump_sum_cases_t_if t pc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (jump_sum_cases_aux t pc jc)
    k

let jump_sum_aux_payload_postcond
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
  (offset: SZ.t)
  (v: bytes)
  (res: SZ.t)
: Tot prop
= match k with
  | Unknown _ -> False
  | Known k' -> B.validator_success (dsnd (pc k')) offset v res

inline_for_extraction
let jump_sum_aux_payload_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot Type
=
  (input: S.slice byte) ->
  (offset: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t
  (requires
    pts_to input #pm v **
    pure (
      SZ.v offset <= Seq.length v /\ (
      match k with
      | Unknown _ -> False
      | Known k' -> B.jumper_pre (dsnd (pc k')) offset v
    ))
  )
  (ensures (fun res ->
    pts_to input #pm v **
    pure (jump_sum_aux_payload_postcond t pc k offset v res)
  ))

inline_for_extraction
fn jump_sum_aux_payload_if'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
  (cond: bool)
  (ift: ((cond_true cond) -> Tot (jump_sum_aux_payload_t t pc k)))
  (iff: ((cond_false cond) -> Tot (jump_sum_aux_payload_t t pc k)))
: (jump_sum_aux_payload_t t pc k)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  if cond {
    ift () input offset
  } else {
    iff () input offset
  }
}

inline_for_extraction
let jump_sum_aux_payload_if
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: maybe_enum_key (sum_enum t))
: Tot (if_combinator (jump_sum_aux_payload_t t pc k) eq_trivial)
= jump_sum_aux_payload_if' t pc k

#push-options "--z3rlimit 64"

inline_for_extraction
fn jump_sum_aux
  (t: sum u#0 u#0)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: B.jumper p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (j_payload: ((k: sum_repr_type t)) -> Tot (jump_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k)))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: (B.jumper (parse_sum t p pc))
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_sum_eq'' t p pc sinput;
  S.pts_to_len input;
  let off = j input offset;
  let k' = PPB.read_parsed_from_validator_success p32 input offset off;
  Seq.lemma_eq_elim
    (Seq.slice sinput (SZ.v off - SZ.v offset) (Seq.length sinput))
    (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
  j_payload k' input off
}

#pop-options

inline_for_extraction
fn jump_sum_aux_payload'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (B.jumper (dsnd (pc x)))))
  (k: maybe_enum_key (sum_enum t))
: (jump_sum_aux_payload_t t pc k)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  match k {
    Known k' -> { pc32 k' input offset }
    Unknown _ -> { 0sz }
  }
}

inline_for_extraction
let jump_sum_aux_payload
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (B.jumper (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (jump_sum_aux_payload_t t pc))
  (k: sum_repr_type t)
: Tot (jump_sum_aux_payload_t t pc (maybe_enum_key_of_repr (sum_enum t) k))
= destr (fun _ -> eq_trivial) (jump_sum_aux_payload_if t pc) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (jump_sum_aux_payload' t pc pc32) k

inline_for_extraction
let jump_sum
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: B.jumper p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (B.jumper (dsnd (pc x)))))
  (destr: dep_maybe_enum_destr_t (sum_enum t) (jump_sum_aux_payload_t t pc))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: Tot (B.jumper (parse_sum t p pc))
= jump_sum_aux t j p32 pc (jump_sum_aux_payload t pc pc32 destr) ()

(* ========== DSum jumpers ========== *)

let jump_dsum_cases_t
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot Type
= B.jumper (parse_dsum_cases' s f g x)

inline_for_extraction
fn jump_dsum_cases_if'
  (s: dsum u#0 u#0)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (cond: bool)
  (ift: (cond_true cond -> Tot (jump_dsum_cases_t s f g x)))
  (iff: (cond_false cond -> Tot (jump_dsum_cases_t s f g x)))
: (jump_dsum_cases_t s f g x)
=
  (input: _)
  (offset: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    ift () input offset
  } else {
    iff () input offset
  }
}

inline_for_extraction
let jump_dsum_cases_if
  (s: dsum u#0 u#0)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (if_combinator (jump_dsum_cases_t s f g x) eq_trivial)
= jump_dsum_cases_if' s f g x

inline_for_extraction
let jump_dsum_cases'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f': (x: dsum_known_key s) -> Tot (B.jumper (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g': B.jumper g)
  (x: dsum_key s)
: Tot (jump_dsum_cases_t s f g x)
= [@inline_let]
  let _ = synth_dsum_case_injective s x in
  match x with
  | Known x' -> B.jump_synth (f' x') (synth_dsum_case s (Known x'))
  | Unknown x' -> B.jump_synth g' (synth_dsum_case s (Unknown x'))

inline_for_extraction
let jump_dsum_cases_dispatch
  (t: dsum)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (B.jumper (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: B.jumper g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (jump_dsum_cases_t t f g))
  (tg: dsum_repr_type t)
: Tot (jump_dsum_cases_t t f g (maybe_enum_key_of_repr (dsum_enum t) tg))
= destr (fun _ -> eq_trivial) (jump_dsum_cases_if t f g) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (jump_dsum_cases' t f f32 g32) tg

inline_for_extraction
let jump_dsum_cases'_destr
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (B.jumper (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : B.jumper g)
  (destr: dep_enum_destr (dsum_enum s) (fun k -> jump_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (jump_dsum_cases_t s f g x)
= match x with
  | Known k ->
    destr
      _
      (fun k -> jump_dsum_cases_if s f g (Known k))
      (fun _ _ -> ())
      (fun _ _ _ _ -> ())
      (fun k -> jump_dsum_cases' s f f' g' (Known k))
      k
  | Unknown r -> jump_dsum_cases' s f f' g' (Unknown r)

inline_for_extraction
let jump_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (f' : (x: dsum_known_key s) -> Tot (B.jumper (dsnd (f x))))
  (#k: parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : B.jumper g)
  (destr: dep_enum_destr (dsum_enum s) (fun k -> jump_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (B.jumper (parse_dsum_cases s f g x))
= Classical.forall_intro (parse_dsum_cases_eq' s f g x);
  B.jump_ext (jump_dsum_cases'_destr s f f' g' destr x) (parse_dsum_cases s f g x)

#push-options "--z3rlimit 64"

inline_for_extraction
fn jump_dsum
  (#kt: parser_kind)
  (t: dsum u#0 u#0)
  (#p: parser kt (dsum_repr_type t))
  (j: B.jumper p)
  (p32: leaf_reader p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (B.jumper (dsnd (f x))))
  (#k': parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: B.jumper g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (jump_dsum_cases_t t f g))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: B.jumper (parse_dsum t p f g)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_dsum_eq' t p f g sinput;
  S.pts_to_len input;
  let off = j input offset;
  let tg = PPB.read_parsed_from_validator_success p32 input offset off;
  Seq.lemma_eq_elim
    (Seq.slice sinput (SZ.v off - SZ.v offset) (Seq.length sinput))
    (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
  parse_dsum_cases_eq' t f g (maybe_enum_key_of_repr (dsum_enum t) tg) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
  jump_dsum_cases_dispatch t f f32 g32 destr tg input off
}

#pop-options

(* ========== Zero-copy parse: read sum tag ========== *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn read_sum_tag
  (t: sum u#0 u#0)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: B.jumper p)
  (p32: leaf_reader p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (sum_type t))
  requires PPB.pts_to_parsed (parse_sum t p pc) input #pm v
  returns tag : sum_key t
  ensures PPB.pts_to_parsed (parse_sum t p pc) input #pm v **
          pure (tag == sum_tag_of_data t v)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_sum_eq'' t p pc bytes;
  parse_sum_eq' t p pc bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt p;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let off = j input 0sz;
  let k' = PPB.read_parsed_from_validator_success p32 input 0sz off;
  parse_enum_key_eq p (sum_enum t) bytes;
  synth_sum_case_inverse t (sum_tag_of_data t v);
  Trade.elim (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_sum t p pc) input #pm v);
  enum_key_of_repr (sum_enum t) k'
}

#pop-options

(* ========== Zero-copy parse: sum payload for a known tag ========== *)

let vmatch_sum_payload
  (#tl: Type)
  (t: sum)
  (k: sum_key t)
  (vmatch_k: tl -> sum_type_of_tag t k -> slprop)
  (xl: tl)
  (v: sum_type t)
: slprop
= if sum_tag_of_data t v = k then vmatch_k xl (synth_sum_case_recip t k v) else pure False

#push-options "--z3rlimit 128"

inline_for_extraction
fn zero_copy_parse_sum_payload
  (#tl: Type)
  (t: sum u#0 u#0)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: B.jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (#vmatch_k: tl -> sum_type_of_tag t k -> slprop)
  (w_k: PPB.zero_copy_parse vmatch_k (dsnd (pc k)))
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (sum_type t))
  (tag_eq: squash (sum_tag_of_data t v == k))
  requires PPB.pts_to_parsed (parse_sum t p pc) input #pm v
  returns res : tl
  ensures vmatch_sum_payload t k vmatch_k res v **
    Trade.trade
      (vmatch_sum_payload t k vmatch_k res v)
      (PPB.pts_to_parsed (parse_sum t p pc) input #pm v)
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_sum_eq'' t p pc bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt p;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  synth_sum_case_injective t k;
  synth_sum_case_inverse t k;
  let off = j input 0sz;
  let payload_bytes = Ghost.hide (Seq.slice bytes (SZ.v off) (Seq.length bytes));
  parse_synth_eq (dsnd (pc k)) (synth_sum_case t k) payload_bytes;
  let gx = Ghost.hide (fst (Some?.v (parse (dsnd (pc k)) payload_bytes)));
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_sum t p pc) input #pm v);
  Seq.lemma_eq_elim wb_payload (Ghost.reveal payload_bytes);
  PPB.pts_to_parsed_intro (dsnd (pc k)) input_payload gx;
  Trade.trans (PPB.pts_to_parsed (dsnd (pc k)) input_payload #(pm /. 2.0R) gx) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_sum t p pc) input #pm v);
  let res = w_k input_payload;
  Trade.trans (vmatch_k res gx) (PPB.pts_to_parsed (dsnd (pc k)) input_payload #(pm /. 2.0R) gx) (PPB.pts_to_parsed (parse_sum t p pc) input #pm v);
  Sum?.synth_case_recip_synth_case t k (Ghost.reveal gx);
  Trade.rewrite_with_trade
    (vmatch_k res gx)
    (vmatch_sum_payload t k vmatch_k res v);
  Trade.trans (vmatch_sum_payload t k vmatch_k res v) _ _;
  res
}

#pop-options

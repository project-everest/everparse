module LowParse.PulseParse.Sum
#lang-pulse
include LowParse.PulseParse.Enum
include LowParse.Spec.Sum
open LowParse.PulseParse.Combinators
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade

module B = LowParse.Pulse.Combinators
module LPB = LowParse.Pulse.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference

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
  (#kt: Ghost.erased parser_kind)
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
  (#kt: Ghost.erased parser_kind)
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
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot Type
= B.validator (parse_dsum_cases' s (Ghost.reveal f) g x)

inline_for_extraction
fn validate_dsum_cases_if'
  (s: dsum u#0 u#0)
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (#k: Ghost.erased parser_kind)
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
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (#k: Ghost.erased parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (if_combinator (validate_dsum_cases_t s f g x) eq_trivial)
= validate_dsum_cases_if' s f g x

inline_for_extraction
let validate_dsum_cases'
  (s: dsum)
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (f': (x: dsum_known_key s) -> Tot (B.validator (dsnd (Ghost.reveal f x))))
  (#k: Ghost.erased parser_kind)
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
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (f32: (x: dsum_known_key t) -> Tot (B.validator (dsnd (Ghost.reveal f x))))
  (#k': Ghost.erased parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: B.validator g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (validate_dsum_cases_t t f g))
  (tg: dsum_repr_type t)
: Tot (validate_dsum_cases_t t f g (maybe_enum_key_of_repr (dsum_enum t) tg))
= destr (fun _ -> eq_trivial) (validate_dsum_cases_if t f g) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (validate_dsum_cases' t f f32 g32) tg

inline_for_extraction
let validate_dsum_cases'_destr
  (s: dsum)
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (f' : (x: dsum_known_key s) -> Tot (B.validator (dsnd (Ghost.reveal f x))))
  (#k: Ghost.erased parser_kind)
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
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (f' : (x: dsum_known_key s) -> Tot (B.validator (dsnd (Ghost.reveal f x))))
  (#k: Ghost.erased parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : B.validator g)
  (destr: dep_enum_destr (dsum_enum s) (fun k -> validate_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (B.validator (parse_dsum_cases s (Ghost.reveal f) g x))
= Classical.forall_intro (parse_dsum_cases_eq' s (Ghost.reveal f) g x);
  B.validate_ext (validate_dsum_cases'_destr s f f' g' destr x) (parse_dsum_cases s (Ghost.reveal f) g x)

inline_for_extraction
fn validate_dsum_cases_fn
  (s: dsum)
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (f': (x: dsum_known_key s) -> Tot (B.validator (dsnd (Ghost.reveal f x))))
  (#k: Ghost.erased parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g': B.validator g)
  (destr: dep_maybe_enum_destr_t (dsum_enum s) (validate_dsum_cases_t s (Ghost.reveal f) g))
  (x: dsum_key s)
: B.validator (parse_dsum_cases s (Ghost.reveal f) g x)
=
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_dsum_cases_eq' s (Ghost.reveal f) g x sinput;
  validate_dsum_cases_dispatch s (Ghost.reveal f) f' g' destr (repr_of_maybe_enum_key (dsum_enum s) x) input poffset
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn validate_dsum
  (#kt: Ghost.erased parser_kind)
  (t: dsum u#0 u#0)
  (#p: parser kt (dsum_repr_type t))
  (v: B.validator p)
  (p32: leaf_reader p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (B.validator (dsnd (f x))))
  (#k': Ghost.erased parser_kind)
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
  (#kt: Ghost.erased parser_kind)
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
  (#kt: Ghost.erased parser_kind)
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
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot Type
= B.jumper (parse_dsum_cases' s (Ghost.reveal f) g x)

inline_for_extraction
fn jump_dsum_cases_if'
  (s: dsum u#0 u#0)
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (#k: Ghost.erased parser_kind)
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
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (#k: Ghost.erased parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (if_combinator (jump_dsum_cases_t s f g x) eq_trivial)
= jump_dsum_cases_if' s f g x

inline_for_extraction
let jump_dsum_cases'
  (s: dsum)
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (f': (x: dsum_known_key s) -> Tot (B.jumper (dsnd (Ghost.reveal f x))))
  (#k: Ghost.erased parser_kind)
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
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (f32: (x: dsum_known_key t) -> Tot (B.jumper (dsnd (Ghost.reveal f x))))
  (#k': Ghost.erased parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: B.jumper g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (jump_dsum_cases_t t f g))
  (tg: dsum_repr_type t)
: Tot (jump_dsum_cases_t t f g (maybe_enum_key_of_repr (dsum_enum t) tg))
= destr (fun _ -> eq_trivial) (jump_dsum_cases_if t f g) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (jump_dsum_cases' t f f32 g32) tg

inline_for_extraction
let jump_dsum_cases'_destr
  (s: dsum)
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (f' : (x: dsum_known_key s) -> Tot (B.jumper (dsnd (Ghost.reveal f x))))
  (#k: Ghost.erased parser_kind)
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
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (f' : (x: dsum_known_key s) -> Tot (B.jumper (dsnd (Ghost.reveal f x))))
  (#k: Ghost.erased parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g' : B.jumper g)
  (destr: dep_enum_destr (dsum_enum s) (fun k -> jump_dsum_cases_t s f g (Known k)))
  (x: dsum_key s)
: Tot (B.jumper (parse_dsum_cases s (Ghost.reveal f) g x))
= Classical.forall_intro (parse_dsum_cases_eq' s (Ghost.reveal f) g x);
  B.jump_ext (jump_dsum_cases'_destr s f f' g' destr x) (parse_dsum_cases s (Ghost.reveal f) g x)

inline_for_extraction
fn jump_dsum_cases_fn
  (s: dsum)
  (f: Ghost.erased ((x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x))))
  (f': (x: dsum_known_key s) -> Tot (B.jumper (dsnd (Ghost.reveal f x))))
  (#k: Ghost.erased parser_kind)
  (#g: parser k (dsum_type_of_unknown_tag s))
  (g': B.jumper g)
  (destr: dep_maybe_enum_destr_t (dsum_enum s) (jump_dsum_cases_t s f g))
  (x: dsum_key s)
: B.jumper (parse_dsum_cases s (Ghost.reveal f) g x)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_dsum_cases_eq' s (Ghost.reveal f) g x sinput;
  jump_dsum_cases_dispatch s f f' g' destr (repr_of_maybe_enum_key (dsum_enum s) x) input offset
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn jump_dsum
  (#kt: Ghost.erased parser_kind)
  (t: dsum u#0 u#0)
  (#p: parser kt (dsum_repr_type t))
  (j: B.jumper p)
  (p32: leaf_reader p)
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (f32: (x: dsum_known_key t) -> Tot (B.jumper (dsnd (f x))))
  (#k': Ghost.erased parser_kind)
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
  (#kt: Ghost.erased parser_kind)
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

(* ========== read_sum: leaf_reader for sum types ========== *)

let read_sum_cases_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot Type
= PPB.leaf_reader (parse_sum_cases' t pc k)

inline_for_extraction
fn read_sum_cases_t_if'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (read_sum_cases_t t pc k)))
  (iff: (cond_false cond -> Tot (read_sum_cases_t t pc k)))
: (read_sum_cases_t t pc k)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    ift () input
  } else {
    iff () input
  }
}

inline_for_extraction
let read_sum_cases_t_if
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (if_combinator (read_sum_cases_t t pc k) eq_trivial)
= read_sum_cases_t_if' t pc k

inline_for_extraction
let read_sum_cases'
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (PPB.leaf_reader (dsnd (pc x)))))
  (k: sum_key t)
: Tot (read_sum_cases_t t pc k)
= [@inline_let]
  let _ = synth_sum_case_injective t k in
  [@inline_let]
  let _ = synth_sum_case_inverse t k in
  PPB.leaf_reader_of_reader
    (read_synth' (PPB.reader_of_leaf_reader (pc32 k)) (synth_sum_case t k) (synth_sum_case_recip t k))

inline_for_extraction
let read_sum_cases
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (PPB.leaf_reader (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (read_sum_cases_t t pc))
  (k: sum_key t)
: Tot (read_sum_cases_t t pc k)
= destr
    _
    (read_sum_cases_t_if t pc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (read_sum_cases' t pc pc32)
    k


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

(* Robust helper for the sum-payload accessors (zero_copy_parse_sum_payload and
   accessor_clens_sum_payload): from the fact that [bytes] parses to [v] as a sum
   and that the tag consumes [off] bytes, derive that the payload parser succeeds
   on the payload sub-slice, consumes it entirely, and reconstructs [v] via
   synth_sum_case. Proved by explicit case analysis so that it is stable (verifies
   at fuel 0/ifuel 0, seed-independent), avoiding the quantifier-search instability
   of relying on parse_sum_eq'' inline (which caused a MacOS-only failure). *)
#push-options "--z3rlimit 32 --fuel 2 --ifuel 1"
let accessor_clens_sum_payload_lemma
  (t: sum)
  (#kt: parser_kind)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (bytes: bytes)
  (off: nat)
  (v: sum_type t)
: Lemma
  (requires (
    parse (parse_sum t p pc) bytes == Some (v, Seq.length bytes) /\
    sum_tag_of_data t v == k /\
    off <= Seq.length bytes /\
    (match parse p bytes with None -> False | Some (_, c) -> c == off)
  ))
  (ensures (
    let payload_bytes = Seq.slice bytes off (Seq.length bytes) in
    (match parse (dsnd (pc k)) payload_bytes with
     | None -> False
     | Some (x, consumed) ->
       consumed == Seq.length payload_bytes /\
       synth_sum_case t k x == v)
  ))
= parse_sum_eq'' t p pc bytes;
  let payload_bytes = Seq.slice bytes off (Seq.length bytes) in
  match parse p bytes with
  | Some (k', consumed_k) ->
    let mk = maybe_enum_key_of_repr (sum_enum t) k' in
    begin match mk with
    | Known kk ->
      begin match parse (dsnd (pc kk)) payload_bytes with
      | Some (x, consumed_x) ->
        assert (sum_tag_of_data t (synth_sum_case t kk x) == kk);
        assert (kk == k)
      | None -> ()
      end
    | Unknown _ -> ()
    end
#pop-options

#push-options "--z3rlimit 128"

inline_for_extraction
fn zero_copy_parse_sum_payload
  (#tl: Type)
  (t: sum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
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
  accessor_clens_sum_payload_lemma t p pc k bytes (SZ.v off) v;
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

(* ========== Sum accessor combinators ========== *)

include LowParse.CLens
module S = Pulse.Lib.Slice

let clens_sum_tag
  (t: sum)
: Tot (clens (sum_type t) (sum_key t))
= {
  clens_cond = (fun _ -> True);
  clens_get = sum_tag_of_data t;
}

let clens_sum_payload
  (t: sum)
  (k: sum_key t)
: Tot (clens (sum_type t) (sum_type_of_tag t k))
= {
  clens_cond = (fun (x: sum_type t) -> sum_tag_of_data t x == k);
  clens_get = (fun (x: sum_type t) -> synth_sum_case_recip t k x);
}

#push-options "--z3rlimit 128"

inline_for_extraction
fn accessor_sum_tag
  (t: sum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: B.jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_sum t p pc) (parse_enum_key p (sum_enum t)) (clens_sum_tag t)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (sum_type t))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_sum_eq'' t p pc bytes;
  parse_sum_eq' t p pc bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt p;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let off = j input 0sz;
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_r (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_tag #pm wb_tag) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_sum t p pc) input #pm v);
  parse_enum_key_eq p (sum_enum t) bytes;
  synth_sum_case_inverse t (sum_tag_of_data t v);
  parse_enum_key_eq p (sum_enum t) wb_tag;
  parse_strong_prefix p bytes wb_tag;
  PPB.pts_to_parsed_intro (parse_enum_key p (sum_enum t)) input_tag (sum_tag_of_data t v);
  Trade.trans (PPB.pts_to_parsed (parse_enum_key p (sum_enum t)) input_tag #(pm /. 2.0R) (sum_tag_of_data t v)) (S.pts_to input_tag #pm wb_tag) (PPB.pts_to_parsed (parse_sum t p pc) input #pm v);
  input_tag
}

inline_for_extraction
fn accessor_clens_sum_payload
  (t: sum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: B.jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (sum_type t))
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
  accessor_clens_sum_payload_lemma t p pc k bytes (SZ.v off) v;
  let gx = Ghost.hide (fst (Some?.v (parse (dsnd (pc k)) payload_bytes)));
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_sum t p pc) input #pm v);
  Seq.lemma_eq_elim wb_payload (Ghost.reveal payload_bytes);
  PPB.pts_to_parsed_intro (dsnd (pc k)) input_payload gx;
  Trade.trans (PPB.pts_to_parsed (dsnd (pc k)) input_payload #(pm /. 2.0R) gx) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_sum t p pc) input #pm v);
  Sum?.synth_case_recip_synth_case t k (Ghost.reveal gx);
  input_payload
}

#pop-options

(* ========== read_sum: leaf_reader for sum types ========== *)

// read_sum_payload_t: the destructor dispatches to a function that reads AND synths
// It takes a payload slice and returns sum_type t
let read_sum_payload_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot Type
= (input: S.slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased (sum_type_of_tag t k)) ->
  stt (sum_type t)
    (PPB.pts_to_parsed (dsnd (pc k)) input #pm v)
    (fun res -> PPB.pts_to_parsed (dsnd (pc k)) input #pm v ** pure (res == synth_sum_case t k (Ghost.reveal v)))

inline_for_extraction
fn read_sum_payload_if'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (read_sum_payload_t t pc k)))
  (iff: (cond_false cond -> Tot (read_sum_payload_t t pc k)))
: (read_sum_payload_t t pc k)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    ift () input
  } else {
    iff () input
  }
}

inline_for_extraction
let read_sum_payload_if
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: Tot (if_combinator (read_sum_payload_t t pc k) eq_trivial)
= read_sum_payload_if' t pc k

// read_sum_payload': per-key reader that reads raw value and applies synth_sum_case
inline_for_extraction
fn read_sum_payload'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (PPB.leaf_reader (dsnd (pc x)))))
  (k: sum_key t)
: read_sum_payload_t t pc k
= (input: _)
  (#pm: _)
  (#v: _)
{
  synth_sum_case_injective t k;
  let raw = pc32 k input;
  synth_sum_case t k raw
}

// read_sum_payload_dispatch: dispatches via destructor to read + synth
inline_for_extraction
let read_sum_payload_dispatch
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (PPB.leaf_reader (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (read_sum_payload_t t pc))
  (k: sum_key t)
: Tot (read_sum_payload_t t pc k)
= destr
    _
    (read_sum_payload_if t pc)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (read_sum_payload' t pc pc32)
    k

#push-options "--z3rlimit 32"

inline_for_extraction
fn read_sum
  (#kt: Ghost.erased parser_kind)
  (t: sum u#0 u#0)
  (#p: parser kt (sum_repr_type t))
  (p32: PPB.leaf_reader p)
  (j: B.jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (PPB.leaf_reader (dsnd (pc x)))))
  (destr: dep_enum_destr (sum_enum t) (read_sum_payload_t t pc))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.leaf_reader (parse_sum t p pc)
=
  (input: S.slice byte)
  (#pm: _)
  (#v: _)
{
  let k = read_sum_tag t j p32 pc () input;
  let payload = accessor_clens_sum_payload t j pc k () input;
  synth_sum_case_injective t k;
  synth_sum_case_inverse t k;
  let res = read_sum_payload_dispatch t pc pc32 destr k payload;
  Trade.elim _ _;
  res
}

#pop-options

(* ========== DSum clens definitions ========== *)

let clens_dsum_tag
  (t: dsum)
: Tot (clens (dsum_type t) (dsum_key t))
= {
  clens_cond = (fun _ -> True);
  clens_get = dsum_tag_of_data t;
}

let clens_dsum_payload
  (t: dsum)
  (k: dsum_key t)
: Tot (clens (dsum_type t) (dsum_type_of_tag t k))
= {
  clens_cond = (fun (x: dsum_type t) -> dsum_tag_of_data t x == k);
  clens_get = (fun (x: dsum_type t) -> synth_dsum_case_recip t k x);
}

(* DSum accessors follow the same pattern as Sum accessors:
   accessor_dsum_tag : accessor (parse_dsum t p (Ghost.reveal f) g) (parse_maybe_enum_key p (dsum_enum t)) (clens_dsum_tag t)
   accessor_clens_dsum_payload : accessor (parse_dsum t p (Ghost.reveal f) g) (parse_dsum_cases t (Ghost.reveal f) g k) (clens_dsum_payload t k)
   Implementation uses parse_dsum_eq', split_trade, and pts_to_parsed_intro.
   These follow the exact same pattern as accessor_sum_tag and accessor_clens_sum_payload above. *)


(* DSum tag accessor using parse_dsum_tag_of_data lemma *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn accessor_dsum_tag
  (t: dsum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (j: B.jumper p)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_dsum t p (Ghost.reveal f) g) (parse_maybe_enum_key p (dsum_enum t)) (clens_dsum_tag t)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dsum_type t))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_dsum_eq' t p f g bytes;
  parse_dsum_eq_ t p f g bytes;
  parse_dsum_tag_of_data t p f g bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt p;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let off = j input 0sz;
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_r (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_tag #pm wb_tag) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_dsum t p (Ghost.reveal f) g) input #pm v);
  parse_maybe_enum_key_eq p (dsum_enum t) bytes;
  parse_maybe_enum_key_eq p (dsum_enum t) wb_tag;
  parse_strong_prefix p bytes wb_tag;
  PPB.pts_to_parsed_intro (parse_maybe_enum_key p (dsum_enum t)) input_tag (dsum_tag_of_data t v);
  Trade.trans (PPB.pts_to_parsed (parse_maybe_enum_key p (dsum_enum t)) input_tag #(pm /. 2.0R) (dsum_tag_of_data t v)) (S.pts_to input_tag #pm wb_tag) (PPB.pts_to_parsed (parse_dsum t p (Ghost.reveal f) g) input #pm v);
  input_tag
}

(* DSum payload accessor: accesses parse_dsum_type_of_tag' from parse_dsum *)

inline_for_extraction
fn accessor_clens_dsum_payload
  (t: dsum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (j: B.jumper p)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (k: dsum_key t)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_dsum t p (Ghost.reveal f) g) (parse_dsum_type_of_tag' t (Ghost.reveal f) g k) (clens_dsum_payload t k)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dsum_type t))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_dsum_eq3 t p f g bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt p;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  synth_dsum_case_injective t k;
  synth_dsum_case_inverse t k;
  let off = j input 0sz;
  let payload_bytes = Ghost.hide (Seq.slice bytes (SZ.v off) (Seq.length bytes));
  parse_synth_eq (parse_dsum_type_of_tag' t (Ghost.reveal f) g k) (synth_dsum_case t k) payload_bytes;
  let gx = Ghost.hide (fst (Some?.v (parse (parse_dsum_type_of_tag' t (Ghost.reveal f) g k) payload_bytes)));
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_dsum t p (Ghost.reveal f) g) input #pm v);
  Seq.lemma_eq_elim wb_payload (Ghost.reveal payload_bytes);
  PPB.pts_to_parsed_intro (parse_dsum_type_of_tag' t (Ghost.reveal f) g k) input_payload gx;
  Trade.trans (PPB.pts_to_parsed (parse_dsum_type_of_tag' t (Ghost.reveal f) g k) input_payload #(pm /. 2.0R) gx) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_dsum t p (Ghost.reveal f) g) input #pm v);
  DSum?.synth_case_recip_synth_case t k (Ghost.reveal gx);
  input_payload
}

(* accessor_clens_dsum_payload': alias for accessor_clens_dsum_payload *)

inline_for_extraction
let accessor_clens_dsum_payload'
  (t: dsum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (j: B.jumper p)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (k: dsum_key t)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_dsum t p (Ghost.reveal f) g) (parse_dsum_type_of_tag' t (Ghost.reveal f) g k) (clens_dsum_payload t k)
= accessor_clens_dsum_payload t j f g k sq

(* DSum unknown payload accessor: accesses g from parse_dsum *)

let clens_dsum_unknown_payload
  (s: dsum)
: Tot (clens (dsum_type s) (dsum_type_of_unknown_tag s))
= {
  clens_cond = (fun (x: dsum_type s) -> Unknown? (dsum_tag_of_data s x));
  clens_get = (fun (x: dsum_type s) -> synth_dsum_case_recip s (dsum_tag_of_data s x) x <: Ghost (dsum_type_of_unknown_tag s) (requires (Unknown? (dsum_tag_of_data s x))) (ensures (fun _ -> True)));
}

inline_for_extraction
fn accessor_clens_dsum_unknown_payload
  (t: dsum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (j: B.jumper p)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_dsum t p (Ghost.reveal f) g) g (clens_dsum_unknown_payload t)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dsum_type t))
{
  PPB.pts_to_parsed_elim input;
  with bytes . assert (S.pts_to input #pm bytes);
  parse_dsum_eq3 t p f g bytes;
  S.pts_to_len input;
  parser_kind_prop_equiv kt p;
  Seq.lemma_eq_elim (Seq.slice bytes 0 (Seq.length bytes)) bytes;
  let k = Ghost.hide (dsum_tag_of_data t v);
  synth_dsum_case_injective t k;
  synth_dsum_case_inverse t k;
  let off = j input 0sz;
  let payload_bytes = Ghost.hide (Seq.slice bytes (SZ.v off) (Seq.length bytes));
  synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t k) (synth_dsum_case_recip t k) ();
  parse_synth_eq (parse_dsum_type_of_tag' t (Ghost.reveal f) g k) (synth_dsum_case t k) payload_bytes;
  let gx : Ghost.erased (dsum_type_of_tag t k) = Ghost.hide (fst (Some?.v (parse (parse_dsum_type_of_tag' t (Ghost.reveal f) g k) payload_bytes)));
  let input_tag, input_payload = split_trade input off;
  with wb_tag . assert (S.pts_to input_tag #pm wb_tag);
  with wb_payload . assert (S.pts_to input_payload #pm wb_payload);
  Trade.elim_hyp_l (S.pts_to input_tag #pm wb_tag) (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes);
  Trade.trans (S.pts_to input_payload #pm wb_payload) (S.pts_to input #pm bytes) (PPB.pts_to_parsed (parse_dsum t p (Ghost.reveal f) g) input #pm v);
  Seq.lemma_eq_elim wb_payload (Ghost.reveal payload_bytes);
  DSum?.synth_case_recip_synth_case t k (Ghost.reveal gx);
  PPB.pts_to_parsed_intro g input_payload (Ghost.reveal gx);
  Trade.trans (PPB.pts_to_parsed g input_payload #(pm /. 2.0R) (Ghost.reveal gx)) (S.pts_to input_payload #pm wb_payload) (PPB.pts_to_parsed (parse_dsum t p (Ghost.reveal f) g) input #pm v);
  input_payload
}

(* accessor_clens_dsum_unknown_payload': alias *)

inline_for_extraction
let accessor_clens_dsum_unknown_payload'
  (t: dsum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (j: B.jumper p)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_dsum t p (Ghost.reveal f) g) g (clens_dsum_unknown_payload t)
= accessor_clens_dsum_unknown_payload t j f g sq

(* DSum cases payload accessors (synth-based) *)

let clens_dsum_cases_payload
  (s: dsum)
  (k: dsum_key s)
: Tot (clens (dsum_cases s k) (dsum_type_of_tag s k))
= {
  clens_cond = (fun (x: dsum_cases s k) -> True);
  clens_get = (fun (x: dsum_cases s k) -> synth_dsum_case_recip s k x);
}

inline_for_extraction
let accessor_clens_dsum_cases_known_payload
  (t: dsum)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: Ghost.erased parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_known_key t)
: PPB.accessor (parse_dsum_cases' t (Ghost.reveal f) g (Known k)) (dsnd (Ghost.reveal f k)) (clens_dsum_cases_payload t (Known k))
= [@inline_let]
  let _ =
    synth_dsum_case_injective t (Known k);
    synth_dsum_case_inverse t (Known k);
    synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t (Known k)) (synth_dsum_case_recip t (Known k)) ()
  in
  accessor_ext
    (accessor_synth (synth_dsum_case t (Known k)) (synth_dsum_case_recip t (Known k)))
    (clens_dsum_cases_payload t (Known k))
    ()

inline_for_extraction
let accessor_clens_dsum_cases_unknown_payload
  (t: dsum)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#ku: Ghost.erased parser_kind)
  (g: parser ku (dsum_type_of_unknown_tag t))
  (k: dsum_unknown_key t)
: PPB.accessor (parse_dsum_cases' t (Ghost.reveal f) g (Unknown k)) g (clens_dsum_cases_payload t (Unknown k))
= [@inline_let]
  let _ =
    synth_dsum_case_injective t (Unknown k);
    synth_dsum_case_inverse t (Unknown k);
    synth_injective_synth_inverse_synth_inverse_recip (synth_dsum_case t (Unknown k)) (synth_dsum_case_recip t (Unknown k)) ()
  in
  accessor_ext
    (accessor_synth (synth_dsum_case t (Unknown k)) (synth_dsum_case_recip t (Unknown k)))
    (clens_dsum_cases_payload t (Unknown k))
    ()

(* Sum payload variant and cases payload *)

inline_for_extraction
let accessor_clens_sum_payload'
  (t: sum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (sum_repr_type t))
  (j: B.jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.accessor (parse_sum t p pc) (dsnd (pc k)) (clens_sum_payload t k)
= accessor_clens_sum_payload t j pc k sq

let clens_sum_cases_payload
  (s: sum)
  (k: sum_key s)
: Tot (clens (sum_cases s k) (sum_type_of_tag s k))
= {
  clens_cond = (fun (x: sum_cases s k) -> True);
  clens_get = (fun (x: sum_cases s k) -> synth_sum_case_recip s k x);
}

inline_for_extraction
let accessor_clens_sum_cases_payload
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (k: sum_key t)
: PPB.accessor (parse_sum_cases' t pc k) (dsnd (pc k)) (clens_sum_cases_payload t k)
= [@inline_let]
  let _ =
    synth_sum_case_injective t k;
    synth_sum_case_inverse t k;
    synth_injective_synth_inverse_synth_inverse_recip (synth_sum_case t k) (synth_sum_case_recip t k) ()
  in
  accessor_ext
    (accessor_synth (synth_sum_case t k) (synth_sum_case_recip t k))
    (clens_sum_cases_payload t k)
    ()

#pop-options

(* ========== read_dsum: leaf_reader for dsum types ========== *)

// read_dsum_payload_t: type for dep_maybe_enum_destr_t dispatching both Known and Unknown
let read_dsum_payload_t
  (t: dsum)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (x: dsum_key t)
: Tot Type
= (input: S.slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased (dsum_type_of_tag t x)) ->
  stt (dsum_type t)
    (PPB.pts_to_parsed (parse_dsum_type_of_tag' t (Ghost.reveal f) g x) input #pm v)
    (fun res -> PPB.pts_to_parsed (parse_dsum_type_of_tag' t (Ghost.reveal f) g x) input #pm v ** pure (res == synth_dsum_case t x (Ghost.reveal v)))

inline_for_extraction
fn read_dsum_payload_if'
  (t: dsum u#0 u#0)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (x: dsum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (read_dsum_payload_t t f g x)))
  (iff: (cond_false cond -> Tot (read_dsum_payload_t t f g x)))
: (read_dsum_payload_t t f g x)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    ift () input
  } else {
    iff () input
  }
}

inline_for_extraction
let read_dsum_payload_if
  (t: dsum u#0 u#0)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (x: dsum_key t)
: Tot (if_combinator (read_dsum_payload_t t f g x) eq_trivial)
= read_dsum_payload_if' t f g x

inline_for_extraction
fn read_dsum_payload'
  (t: dsum u#0 u#0)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (f32: (x: dsum_known_key t) -> Tot (PPB.leaf_reader (dsnd (Ghost.reveal f x))))
  (#k': Ghost.erased parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: PPB.leaf_reader g)
  (x: dsum_key t)
: read_dsum_payload_t t f g x
= (input: _)
  (#pm: _)
  (#v: _)
{
  synth_dsum_case_injective t x;
  match x {
    Known kk -> {
      let raw = f32 kk input;
      synth_dsum_case t (Known kk) raw
    }
    Unknown x' -> {
      let raw = g32 input;
      synth_dsum_case t (Unknown x') raw
    }
  }
}

inline_for_extraction
let validate_dsum_cases_dispatch_reader
  (t: dsum)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (f32: (x: dsum_known_key t) -> Tot (PPB.leaf_reader (dsnd (Ghost.reveal f x))))
  (#k': Ghost.erased parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: PPB.leaf_reader g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (read_dsum_payload_t t f g))
  (k: dsum_key t)
: Tot (read_dsum_payload_t t f g k)
= destr (fun _ -> eq_trivial) (read_dsum_payload_if t f g) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (read_dsum_payload' t f f32 g32) (repr_of_maybe_enum_key (dsum_enum t) k)

#push-options "--z3rlimit 64"

inline_for_extraction
fn read_dsum
  (#kt: Ghost.erased parser_kind)
  (t: dsum u#0 u#0)
  (#p: parser kt (dsum_repr_type t))
  (p32: PPB.leaf_reader (parse_maybe_enum_key p (dsum_enum t)))
  (j: B.jumper p)
  (f: Ghost.erased ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (f32: (x: dsum_known_key t) -> Tot (PPB.leaf_reader (dsnd (Ghost.reveal f x))))
  (#k': Ghost.erased parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (g32: PPB.leaf_reader g)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (read_dsum_payload_t t f g))
  (_: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.leaf_reader (parse_dsum t p (Ghost.reveal f) g)
=
  (input: S.slice byte)
  (#pm: _)
  (#v: _)
{
  let tag_slice = accessor_dsum_tag t j (Ghost.reveal f) g () input;
  let k = p32 tag_slice;
  Trade.elim _ _;
  let payload = accessor_clens_dsum_payload t j (Ghost.reveal f) g k () input;
  synth_dsum_case_injective t k;
  synth_dsum_case_inverse t k;
  let res = validate_dsum_cases_dispatch_reader t f f32 g32 destr k payload;
  Trade.elim _ _;
  res
}

#pop-options

(* ========== Copyful parser combinators for CLOSED sums (tagged unions) ========== *)

let sum_mid
  (t: sum)
  (mid_of_tag: sum_key t -> Type0)
: Type0
= (k: sum_key t & mid_of_tag k)

let vmatch_sum_case
  (t: sum)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (k: sum_key t)
  (xl: low)
  (cm: mid_of_tag k)
: slprop
= pure (tag_of_low xl == k) ** vmatch_cases k xl cm

let vmatch_sum
  (t: sum)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (xl: low)
  (m: sum_mid t mid_of_tag)
: slprop
= pure (tag_of_low xl == dfst m) ** vmatch_cases (dfst m) xl (dsnd m)

let sum_conv
  (t: sum)
  (mid_of_tag: sum_key t -> Type0)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (m: sum_mid t mid_of_tag)
: GTot (option (sum_type t))
= match conv_of_tag (dfst m) (dsnd m) with
  | Some vp -> Some (synth_sum_case t (dfst m) vp <: sum_type t)
  | None -> None

// free_sum_payload_t: per-key free for the payload of a known tag
let free_sum_payload_t
  (t: sum)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (k: sum_key t)
: Tot Type
= PPB.free_t (vmatch_cases k)

inline_for_extraction
fn free_sum_payload_if'
  (t: sum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (k: sum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (free_sum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)))
  (iff: (cond_false cond -> Tot (free_sum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)))
: (free_sum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)
=
  (xl: _)
  (#v: _)
{
  if cond {
    ift () xl
  } else {
    iff () xl
  }
}

inline_for_extraction
let free_sum_payload_if
  (t: sum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (k: sum_key t)
: Tot (if_combinator (free_sum_payload_t t low tag_of_low mid_of_tag vmatch_cases k) eq_trivial)
= free_sum_payload_if' t low tag_of_low mid_of_tag vmatch_cases k

inline_for_extraction
let free_sum_payload_dispatch
  (t: sum)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (f: (k: sum_key t) -> PPB.free_t (vmatch_cases k))
  (destr: dep_enum_destr (sum_enum t) (free_sum_payload_t t low tag_of_low mid_of_tag vmatch_cases))
  (k: sum_key t)
: Tot (free_sum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)
= destr
    _
    (free_sum_payload_if t low tag_of_low mid_of_tag vmatch_cases)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    f
    k

// free_sum: dispatch to the per-case free via a dep_enum_destr (first-order, extracts to C)
inline_for_extraction
fn free_sum
  (t: sum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (f: (k: sum_key t) -> PPB.free_t (vmatch_cases k))
  (destr: dep_enum_destr (sum_enum t) (free_sum_payload_t t low tag_of_low mid_of_tag vmatch_cases))
: PPB.free_t #low #(sum_mid t mid_of_tag) (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases)
=
  (xl: low)
  (#v: Ghost.erased (sum_mid t mid_of_tag))
{
  rewrite (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases xl v)
    as (pure (tag_of_low xl == dfst (Ghost.reveal v)) ** vmatch_cases (dfst (Ghost.reveal v)) xl (dsnd (Ghost.reveal v)));
  elim_pure_explicit (tag_of_low xl == dfst (Ghost.reveal v));
  let k = tag_of_low xl;
  rewrite (vmatch_cases (dfst (Ghost.reveal v)) xl (dsnd (Ghost.reveal v)))
    as (vmatch_cases k xl (dsnd (Ghost.reveal v)));
  free_sum_payload_dispatch t low tag_of_low mid_of_tag vmatch_cases f destr k xl;
  ()
}


// copyful_parse_sum_payload_t: per-key copyful parser for the payload of a known tag
// note: it uses vmatch_sum_case (the variant WITH the pure tag fact)
let copyful_parse_sum_payload_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
: Tot Type
= PPB.copyful_parse (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) (dsnd (pc k)) (conv_of_tag k)

inline_for_extraction
fn copyful_parse_sum_payload_if'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)))
  (iff: (cond_false cond -> Tot (copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)))
: (copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    ift () input
  } else {
    iff () input
  }
}

inline_for_extraction
let copyful_parse_sum_payload_if
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
: Tot (if_combinator (copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k) eq_trivial)
= copyful_parse_sum_payload_if' t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k

// copyful_parse_sum_payload_dispatch: dispatch via destructor to the per-key copyful parser
inline_for_extraction
let copyful_parse_sum_payload_dispatch
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (w: (k: sum_key t) -> PPB.copyful_parse (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) (dsnd (pc k)) (conv_of_tag k))
  (destr: dep_enum_destr (sum_enum t) (copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (k: sum_key t)
: Tot (copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
= destr
    _
    (copyful_parse_sum_payload_if t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    w
    k

#push-options "--z3rlimit 64"

inline_for_extraction
fn copyful_parse_sum
  (t: sum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (sum_repr_type t))
  (p32: PPB.leaf_reader p)
  (j: B.jumper p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (w: (k: sum_key t) -> copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (destr: dep_enum_destr (sum_enum t) (copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.copyful_parse (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases) (parse_sum t p pc) (sum_conv t mid_of_tag conv_of_tag)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (sum_type t))
{
  let k = read_sum_tag t j p32 pc () input;
  let payload = accessor_clens_sum_payload t j pc k () input;
  with pm' v2. assert (PPB.pts_to_parsed (dsnd (pc k)) payload #pm' v2);
  let res = copyful_parse_sum_payload_dispatch t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag w destr k payload;
  Trade.elim _ _;
  PPB.elim_vmatch_conv (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) (conv_of_tag k) res v2;
  with cm. assert (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k res cm ** pure (conv_of_tag k cm == Some (Ghost.reveal v2)));
  synth_sum_case_inverse t k;
  rewrite (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k res cm)
    as (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases res (| k, cm |));
  PPB.intro_vmatch_conv (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases) (sum_conv t mid_of_tag conv_of_tag) res (| k, cm |) (Ghost.reveal v);
  res
}

#pop-options

// copyful_parse_sum_case: build a per-case copyful parser from the field copyful parser
// and the low-type constructor `mk`. The two squashes are discharged by reduction at use site:
//   - tag_of_low (mk x) == k          (the constructor determines the tag)
//   - vmatch_cases k (mk x) cm == vmatch_field x cm   (vmatch_cases reduces to vmatch_field on this constructor)
inline_for_extraction
fn copyful_parse_sum_case
  (t: sum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
  (#tf: Type0)
  (#kf: Ghost.erased parser_kind)
  (#pf: parser kf (sum_type_of_tag t k))
  (#vmatch_field: tf -> mid_of_tag k -> slprop)
  (r: PPB.copyful_parse vmatch_field pf (conv_of_tag k))
  (mk: tf -> low)
  (sq_tag: squash (forall (x: tf) . tag_of_low (mk x) == k))
  (sq_vm: squash (forall (x: tf) (cm: mid_of_tag k) . vmatch_cases k (mk x) cm == vmatch_field x cm))
: PPB.copyful_parse (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) pf (conv_of_tag k)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  let lv = r input;
  PPB.elim_vmatch_conv vmatch_field (conv_of_tag k) lv (Ghost.reveal v);
  with cm. assert (vmatch_field lv cm ** pure (conv_of_tag k cm == Some (Ghost.reveal v)));
  let res = mk lv;
  rewrite (vmatch_field lv cm) as (vmatch_cases k res cm);
  fold (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k res cm);
  PPB.intro_vmatch_conv (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) (conv_of_tag k) res cm (Ghost.reveal v);
  res
}

// free_sum_case: build a per-case free from the field free and an option-valued
// discriminator `disc` (Some y on this constructor, None otherwise). The squash
// is discharged by reduction at use site:
//   vmatch_cases k xl cm == (match disc xl with Some y -> vmatch_field y cm | None -> pure False)
inline_for_extraction
fn free_sum_case
  (t: sum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (k: sum_key t)
  (#tf: Type0)
  (#vmatch_field: tf -> mid_of_tag k -> slprop)
  (free_field: PPB.free_t vmatch_field)
  (disc: low -> option tf)
  (sq: squash (forall (xl: low) (cm: mid_of_tag k) .
        vmatch_cases k xl cm == (match disc xl with | Some y -> vmatch_field y cm | None -> pure False)))
: PPB.free_t #low #(mid_of_tag k) (vmatch_cases k)
=
  (xl: low)
  (#cm: _)
{
  match disc xl {
    Some y -> {
      rewrite (vmatch_cases k xl cm) as (vmatch_field y cm);
      free_field y;
    }
    None -> {
      rewrite (vmatch_cases k xl cm) as (pure False);
      let _ = elim_pure_explicit False;
      ()
    }
  }
}

(* ========== Copyful parser + free for a sum payload at a known tag (implicit sums) ========== *)

// For implicit sums the tag is supplied externally (not parsed inline): the
// parser is [parse_sum_cases t pc k] and the high value is [sum_cases t k]
// (= refine_with_tag, isomorphic to the payload via synth_sum_case). The owned
// low representation, per-case copyful/free and destructors are exactly those of
// the closed owned sum; we just lift across the [synth_sum_case] isomorphism.

let sum_cases_conv
  (t: sum)
  (mid_of_tag: sum_key t -> Type0)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
  (cm: mid_of_tag k)
: GTot (option (sum_cases t k))
= match conv_of_tag k cm with
  | Some vp -> Some (synth_sum_case t k vp <: sum_cases t k)
  | None -> None

let vmatch_sum_cases
  (t: sum)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (k: sum_key t)
  (xl: low)
  (cm: mid_of_tag k)
: slprop
= vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k xl cm

#push-options "--z3rlimit 64"

inline_for_extraction
fn copyful_parse_sum_cases
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (w: (k: sum_key t) -> copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (destr: dep_enum_destr (sum_enum t) (copyful_parse_sum_payload_t t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (k: sum_key t)
: PPB.copyful_parse (vmatch_sum_cases t low tag_of_low mid_of_tag vmatch_cases k) (parse_sum_cases t pc k) (sum_cases_conv t mid_of_tag conv_of_tag k)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (sum_cases t k))
{
  synth_sum_case_injective t k;
  synth_sum_case_inverse t k;
  Classical.forall_intro (parse_sum_cases_eq' t pc k);
  PPB.pts_to_parsed_ext (parse_synth (dsnd (pc k)) (synth_sum_case t k)) input;
  pts_to_parsed_synth_l2r (dsnd (pc k)) (synth_sum_case t k) (synth_sum_case_recip t k) input;
  let res = copyful_parse_sum_payload_dispatch t pc low tag_of_low mid_of_tag vmatch_cases conv_of_tag w destr k input;
  pts_to_parsed_synth_r2l (dsnd (pc k)) (synth_sum_case t k) (synth_sum_case_recip t k) input (Ghost.reveal v);
  PPB.pts_to_parsed_ext (parse_sum_cases t pc k) input;
  PPB.elim_vmatch_conv (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) (conv_of_tag k) res (synth_sum_case_recip t k (Ghost.reveal v));
  with cm. assert (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k res cm ** pure (conv_of_tag k cm == Some (synth_sum_case_recip t k (Ghost.reveal v))));
  fold (vmatch_sum_cases t low tag_of_low mid_of_tag vmatch_cases k res cm);
  PPB.intro_vmatch_conv (vmatch_sum_cases t low tag_of_low mid_of_tag vmatch_cases k) (sum_cases_conv t mid_of_tag conv_of_tag k) res cm (Ghost.reveal v);
  res
}

#pop-options

inline_for_extraction
fn free_sum_cases
  (t: sum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (f: (k: sum_key t) -> PPB.free_t (vmatch_cases k))
  (destr: dep_enum_destr (sum_enum t) (free_sum_payload_t t low tag_of_low mid_of_tag vmatch_cases))
  (k: sum_key t)
: PPB.free_t #low #(mid_of_tag k) (vmatch_sum_cases t low tag_of_low mid_of_tag vmatch_cases k)
=
  (xl: low)
  (#cm: Ghost.erased (mid_of_tag k))
{
  unfold (vmatch_sum_cases t low tag_of_low mid_of_tag vmatch_cases k xl cm);
  unfold (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k xl cm);
  elim_pure_explicit (tag_of_low xl == k);
  free_sum_payload_dispatch t low tag_of_low mid_of_tag vmatch_cases f destr k xl;
  ()
}

(* ========== Copyful parser combinators for OPEN sums (dsum / tagged unions with default) ========== *)

// copyful_parse_false: a copyful parser for parse_false (the dead default case
// of a dsum's known-key dispatch). Its precondition entails False, so the body
// is unreachable.
inline_for_extraction
fn copyful_parse_false
  (vmatch: squash False -> squash False -> slprop)
: PPB.copyful_parse #(squash False) #(squash False) #(squash False) vmatch #parse_false_kind parse_false (fun (x: squash False) -> Some x)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  let _ = Ghost.reveal v;
  let res : squash False = false_elim ();
  rewrite (PPB.pts_to_parsed #_ #(squash False) parse_false input #pm v)
    as (PPB.pts_to_parsed #_ #(squash False) parse_false input #pm v ** PPB.vmatch_conv vmatch (fun (x: squash False) -> Some x) res v);
  res
}

// l2r_safe_writer_false: the dead default-case writer for parse_false (mirrors
// copyful_parse_false). Its low value is a proof of False, so the body is
// unreachable and the postcondition is discharged from the contradiction.
inline_for_extraction
fn l2r_safe_writer_false
  (vmatch: squash False -> squash False -> slprop)
  (s: serializer #parse_false_kind #(squash False) parse_false)
: PPB.l2r_safe_writer #(squash False) #(squash False) #(squash False) vmatch #parse_false_kind #parse_false s (fun (x: squash False) -> Some x)
=
  (x: squash False)
  (#y: Ghost.erased (squash False))
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: _)
{
  let _ = x;
  false_elim ()
}

(* ========== Copyful "safe serializer" (l2r_safe_writer) combinators for CLOSED sums ========== *)

// serialize_sum_eq_forall: the whole-sum serialized bytes decompose into the
// enum-key tag bytes followed by the per-case payload bytes (for every value).
let serialize_sum_eq_forall
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: Lemma
  (forall (x: sum_type t).
    serialize (serialize_sum t s sc) x ==
    (let tg = sum_tag_of_data t x in
     Seq.append (serialize (serialize_enum_key _ s (sum_enum t)) tg)
                (serialize (sc tg) (synth_sum_case_recip t tg x))))
= let aux (x: sum_type t) : Lemma
    (serialize (serialize_sum t s sc) x ==
     (let tg = sum_tag_of_data t x in
      Seq.append (serialize (serialize_enum_key _ s (sum_enum t)) tg)
                 (serialize (sc tg) (synth_sum_case_recip t tg x))))
  = serialize_sum_eq t s sc x
  in
  Classical.forall_intro aux

// l2r_safe_writer_sum_payload_t: per-key safe writer for the payload of a known tag
// (uses vmatch_sum_case, the variant WITH the pure tag fact)
let l2r_safe_writer_sum_payload_t
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
: Tot Type
= PPB.l2r_safe_writer (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) (sc k) (conv_of_tag k)

inline_for_extraction
fn l2r_safe_writer_sum_payload_if'
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)))
  (iff: (cond_false cond -> Tot (l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)))
: (l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
=
  (input: _)
  (#y: _)
  (out: _)
  (#v: _)
  (perr: _)
{
  if cond {
    ift () input out perr
  } else {
    iff () input out perr
  }
}

inline_for_extraction
let l2r_safe_writer_sum_payload_if
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
: Tot (if_combinator (l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k) eq_trivial)
= l2r_safe_writer_sum_payload_if' t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k

inline_for_extraction
let l2r_safe_writer_sum_payload_dispatch
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (w: (k: sum_key t) -> PPB.l2r_safe_writer (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) (sc k) (conv_of_tag k))
  (destr: dep_enum_destr (sum_enum t) (l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (k: sum_key t)
: Tot (l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
= destr
    _
    (l2r_safe_writer_sum_payload_if t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    w
    k

// l2r_safe_writer_sum_case: build a per-case safe writer from the field safe
// writer and an option-valued discriminator `disc` (Some y on this constructor,
// None otherwise). The writer CONSUMES the low value, so we mirror free_sum_case's
// extraction approach. The squash is discharged by reduction at use site:
//   vmatch_cases k xl cm == (match disc xl with Some y -> vmatch_field y cm | None -> pure False)
inline_for_extraction
fn l2r_safe_writer_sum_case
  (t: sum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
  (#tf: Type0)
  (#kf: Ghost.erased parser_kind)
  (#pf: parser kf (sum_type_of_tag t k))
  (#sf: serializer pf)
  (#vmatch_field: tf -> mid_of_tag k -> slprop)
  (wf: PPB.l2r_safe_writer vmatch_field sf (conv_of_tag k))
  (disc: low -> option tf)
  (sq: squash (forall (xl: low) (cm: mid_of_tag k) .
        vmatch_cases k xl cm == (match disc xl with | Some y -> vmatch_field y cm | None -> pure False)))
: PPB.l2r_safe_writer (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k) sf (conv_of_tag k)
=
  (xl: low)
  (#y: Ghost.erased (mid_of_tag k))
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: ref bool)
{
  unfold (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal y));
  elim_pure_explicit (tag_of_low xl == k);
  match disc xl {
    Some yf -> {
      rewrite (vmatch_cases k xl (Ghost.reveal y)) as (vmatch_field yf (Ghost.reveal y));
      let res = wf yf out perr;
      rewrite (vmatch_field yf (Ghost.reveal y)) as (vmatch_cases k xl (Ghost.reveal y));
      fold (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal y));
      res
    }
    None -> {
      rewrite (vmatch_cases k xl (Ghost.reveal y)) as (pure False);
      let _ = elim_pure_explicit False;
      intro_pure False ();
      rewrite (pure False) as (vmatch_cases k xl (Ghost.reveal y));
      fold (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal y));
      false_elim ()
    }
  }
}

#push-options "--z3rlimit 64"

let recip_case_id (t: sum) (k: sum_key t) (vp: sum_type_of_tag t k)
: Lemma (synth_sum_case_recip t k (synth_sum_case t k vp) == vp)
= Sum?.synth_case_recip_synth_case t k vp

// Postcondition lemma for the OK path: out = tag-bytes ++ payload-bytes.
let l2r_safe_writer_sum_postcond_lemma
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (mid_of_tag: sum_key t -> Type0)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (m: sum_mid t mid_of_tag)
  (vleft' vright': Seq.seq byte)
  (res1 res2 resf: SZ.t)
  (e2: bool)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: Lemma
  (requires (
    SZ.v res1 == Seq.length vleft' /\
    vleft' == serialize (serialize_enum_key _ s (sum_enum t)) (dfst m) /\
    (if e2 then SZ.v resf == SZ.v res1 else SZ.v resf == SZ.v res1 + SZ.v res2) /\
    l2r_safe_writer_postcond (conv_of_tag (dfst m)) (sc (dfst m)) (dsnd m) vright' res2 e2
  ))
  (ensures (
    l2r_safe_writer_postcond (sum_conv t mid_of_tag conv_of_tag) (serialize_sum t s sc)
      m (Seq.append vleft' vright') resf e2
  ))
= let k = dfst m in
  let cm = dsnd m in
  synth_sum_case_injective t k;
  synth_sum_case_inverse t k;
  match conv_of_tag k cm with
  | None -> ()
  | Some vp ->
    let yc : sum_cases t k = synth_sum_case t k vp in
    let yh : sum_type t = yc in
    assert (sum_tag_of_data t yh == k);
    serialize_sum_eq t s sc yh;
    recip_case_id t k vp;
    assert (synth_sum_case_recip t k yh == vp);
    assert (serialize (serialize_sum t s sc) yh ==
            Seq.append (serialize (serialize_enum_key _ s (sum_enum t)) k) (serialize (sc k) vp));
    slice_append_prefix vleft' vright' (Seq.length (serialize (sc k) vp))

// Postcondition lemma for the no-room path: the output is untouched and shorter
// than the (constant-size) tag, hence shorter than the whole serialization.
let l2r_safe_writer_sum_noroom_lemma
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (mid_of_tag: sum_key t -> Type0)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (m: sum_mid t mid_of_tag)
  (vout: Seq.seq byte)
  (resf tag_sz: SZ.t)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: Lemma
  (requires (
    Seq.length vout < SZ.v tag_sz /\
    kt.parser_kind_high == Some kt.parser_kind_low /\
    kt.parser_kind_low == SZ.v tag_sz
  ))
  (ensures (
    l2r_safe_writer_postcond (sum_conv t mid_of_tag conv_of_tag) (serialize_sum t s sc)
      m vout resf true
  ))
= let k = dfst m in
  synth_sum_case_injective t k;
  synth_sum_case_inverse t k;
  match conv_of_tag k (dsnd m) with
  | None -> ()
  | Some vp ->
    let yc : sum_cases t k = synth_sum_case t k vp in
    let yh : sum_type t = yc in
    assert (sum_tag_of_data t yh == k);
    serialize_sum_eq t s sc yh;
    serialize_length (serialize_enum_key _ s (sum_enum t)) k;
    assert (Seq.length (serialize (serialize_enum_key _ s (sum_enum t)) k) == SZ.v tag_sz)

inline_for_extraction
fn l2r_safe_writer_sum
  (t: sum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (wt: LPB.l2r_leaf_writer (serialize_enum_key _ s (sum_enum t)))
  (tag_sz: SZ.t {
    (Ghost.reveal kt).parser_kind_high == Some (Ghost.reveal kt).parser_kind_low /\
    (Ghost.reveal kt).parser_kind_low == SZ.v tag_sz
  })
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (w: (k: sum_key t) -> l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (destr: dep_enum_destr (sum_enum t) (l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (sq: squash ((Ghost.reveal kt).parser_kind_subkind == Some ParserStrong))
: PPB.l2r_safe_writer (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases) (serialize_sum t s sc) (sum_conv t mid_of_tag conv_of_tag)
=
  (xl: low)
  (#m: Ghost.erased (sum_mid t mid_of_tag))
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: ref bool)
{
  unfold (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases xl (Ghost.reveal m));
  elim_pure_explicit (tag_of_low xl == dfst (Ghost.reveal m));
  let k = tag_of_low xl;
  rewrite (vmatch_cases (dfst (Ghost.reveal m)) xl (dsnd (Ghost.reveal m)))
    as (vmatch_cases k xl (dsnd (Ghost.reveal m)));
  S.pts_to_len out;
  let l = S.len out;
  if (SZ.lt l tag_sz) {
    perr := true;
    rewrite (vmatch_cases k xl (dsnd (Ghost.reveal m)))
      as (vmatch_cases (dfst (Ghost.reveal m)) xl (dsnd (Ghost.reveal m)));
    fold (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases xl (Ghost.reveal m));
    l2r_safe_writer_sum_noroom_lemma t s pc sc mid_of_tag conv_of_tag (Ghost.reveal m) (Ghost.reveal v) tag_sz tag_sz sq;
    tag_sz
  } else {
    fold (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k xl (dsnd (Ghost.reveal m)));
    let left, right = S.split out tag_sz;
    S.pts_to_len left;
    serialize_length (serialize_enum_key _ s (sum_enum t)) k;
    let res1 = wt k left 0sz;
    with vleft'. assert (S.pts_to left vleft');
    S.pts_to_len left;
    assert (pure (vleft' == serialize (serialize_enum_key _ s (sum_enum t)) k));
    let res2 = l2r_safe_writer_sum_payload_dispatch t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag w destr k xl right perr;
    let e2 = !perr;
    with vright'. assert (S.pts_to right vright');
    S.pts_to_len right;
    S.join left right out;
    S.pts_to_len out;
    unfold (vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k xl (dsnd (Ghost.reveal m)));
    rewrite (vmatch_cases k xl (dsnd (Ghost.reveal m)))
      as (vmatch_cases (dfst (Ghost.reveal m)) xl (dsnd (Ghost.reveal m)));
    fold (vmatch_sum t low tag_of_low mid_of_tag vmatch_cases xl (Ghost.reveal m));
    let resf : SZ.t = if e2 { res1 } else { (SZ.add res1 res2 <: SZ.t) };
    l2r_safe_writer_sum_postcond_lemma t s pc sc mid_of_tag conv_of_tag (Ghost.reveal m) vleft' vright' res1 res2 resf e2 sq;
    resf
  }
}

#pop-options

let dsum_mid
  (t: dsum)
  (mid_of_tag: dsum_key t -> Type0)
: Type0
= (k: dsum_key t & mid_of_tag k)

let vmatch_dsum_case
  (t: dsum)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (k: dsum_key t)
  (xl: low)
  (cm: mid_of_tag k)
: slprop
= pure (tag_of_low xl == k) ** vmatch_cases k xl cm

let vmatch_dsum
  (t: dsum)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (xl: low)
  (m: dsum_mid t mid_of_tag)
: slprop
= pure (tag_of_low xl == dfst m) ** vmatch_cases (dfst m) xl (dsnd m)

let dsum_conv
  (t: dsum)
  (mid_of_tag: dsum_key t -> Type0)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (m: dsum_mid t mid_of_tag)
: GTot (option (dsum_type t))
= match conv_of_tag (dfst m) (dsnd m) with
  | Some vp -> Some (synth_dsum_case t (dfst m) vp <: dsum_type t)
  | None -> None

// copyful_parse_dsum_payload_t: per-key copyful for the payload of a known/unknown tag
let copyful_parse_dsum_payload_t
  (t: dsum)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (k: dsum_key t)
: Tot Type
= (input: S.slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased (dsum_type_of_tag t k)) ->
  stt low
    (PPB.pts_to_parsed (parse_dsum_type_of_tag' t f g k) input #pm v)
    (fun res ->
      PPB.pts_to_parsed (parse_dsum_type_of_tag' t f g k) input #pm v **
      PPB.vmatch_conv (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k) (conv_of_tag k) res v)

#push-options "--z3rlimit 64"

// Dispatch the per-key copyful parser via the first-order maybe-enum
// destructor (exactly as read_dsum does), so extraction is first-order C
// (an if-cascade on the tag) rather than a match on an abstract enum_key.
inline_for_extraction
fn copyful_parse_dsum_payload_if'
  (t: dsum u#0 u#0)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (x: dsum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag x)))
  (iff: (cond_false cond -> Tot (copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag x)))
: (copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag x)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  if cond {
    ift () input
  } else {
    iff () input
  }
}

inline_for_extraction
let copyful_parse_dsum_payload_if
  (t: dsum u#0 u#0)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (x: dsum_key t)
: Tot (if_combinator (copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag x) eq_trivial)
= copyful_parse_dsum_payload_if' t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag x

// the destructor leaf: at a concrete key x, dispatch to the per-case copyful w
inline_for_extraction
fn copyful_parse_dsum_payload_leaf
  (t: dsum u#0 u#0)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (w: (k: dsum_key t) -> copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (x: dsum_key t)
: (copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag x)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  w x input
}

inline_for_extraction
let copyful_parse_dsum_payload_dispatch
  (t: dsum)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (w: (k: dsum_key t) -> copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (k: dsum_key t)
: Tot (copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
= destr
    (fun _ -> eq_trivial)
    (copyful_parse_dsum_payload_if t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (copyful_parse_dsum_payload_leaf t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag w)
    (repr_of_maybe_enum_key (dsum_enum t) k)

inline_for_extraction
fn copyful_parse_dsum
  (t: dsum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (p32: PPB.leaf_reader (parse_maybe_enum_key p (dsum_enum t)))
  (j: B.jumper p)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (#k': Ghost.erased parser_kind)
  (#g: parser k' (dsum_type_of_unknown_tag t))
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (w: (k: dsum_key t) -> copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (copyful_parse_dsum_payload_t t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: PPB.copyful_parse (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases) (parse_dsum t p f g) (dsum_conv t mid_of_tag conv_of_tag)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (dsum_type t))
{
  let tag_slice = accessor_dsum_tag t j (Ghost.hide f) g () input;
  let k = p32 tag_slice;
  Trade.elim _ _;
  let payload = accessor_clens_dsum_payload t j (Ghost.hide f) g k () input;
  with pm' v2. assert (PPB.pts_to_parsed (parse_dsum_type_of_tag' t f g k) payload #pm' v2);
  let res = copyful_parse_dsum_payload_dispatch t f g low tag_of_low mid_of_tag vmatch_cases conv_of_tag w destr k payload;
  Trade.elim _ _;
  PPB.elim_vmatch_conv (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k) (conv_of_tag k) res v2;
  with cm. assert (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k res cm ** pure (conv_of_tag k cm == Some (Ghost.reveal v2)));
  synth_dsum_case_inverse t k;
  rewrite (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k res cm)
    as (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases res (| k, cm |));
  PPB.intro_vmatch_conv (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases) (dsum_conv t mid_of_tag conv_of_tag) res (| k, cm |) (Ghost.reveal v);
  res
}

#pop-options

// copyful_parse_dsum_case: build a per-case copyful from the field copyful and the
// low-type constructor `mk` (which, for the Unknown case, captures the raw repr).
inline_for_extraction
fn copyful_parse_dsum_case
  (t: dsum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (k: dsum_key t)
  (#tf: Type0)
  (#kf: Ghost.erased parser_kind)
  (#pf: parser kf (dsum_type_of_tag t k))
  (#vmatch_field: tf -> mid_of_tag k -> slprop)
  (r: PPB.copyful_parse vmatch_field pf (conv_of_tag k))
  (mk: tf -> low)
  (sq_tag: squash (forall (x: tf) . tag_of_low (mk x) == k))
  (sq_vm: squash (forall (x: tf) (cm: mid_of_tag k) . vmatch_cases k (mk x) cm == vmatch_field x cm))
: PPB.copyful_parse (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k) pf (conv_of_tag k)
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  let lv = r input;
  PPB.elim_vmatch_conv vmatch_field (conv_of_tag k) lv (Ghost.reveal v);
  with cm. assert (vmatch_field lv cm ** pure (conv_of_tag k cm == Some (Ghost.reveal v)));
  let res = mk lv;
  rewrite (vmatch_field lv cm) as (vmatch_cases k res cm);
  fold (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k res cm);
  PPB.intro_vmatch_conv (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k) (conv_of_tag k) res cm (Ghost.reveal v);
  res
}

(* free for open sums (dsum) *)

// Dispatch the per-key free via the first-order maybe-enum destructor (as
// read_dsum does), so that extraction is first-order C.
let free_dsum_payload_t
  (t: dsum)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (k: dsum_key t)
: Tot Type
= PPB.free_t (vmatch_cases k)

inline_for_extraction
fn free_dsum_payload_if'
  (t: dsum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (k: dsum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (free_dsum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)))
  (iff: (cond_false cond -> Tot (free_dsum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)))
: (free_dsum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)
=
  (xl: _)
  (#v: _)
{
  if cond {
    ift () xl
  } else {
    iff () xl
  }
}

inline_for_extraction
let free_dsum_payload_if
  (t: dsum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (k: dsum_key t)
: Tot (if_combinator (free_dsum_payload_t t low tag_of_low mid_of_tag vmatch_cases k) eq_trivial)
= free_dsum_payload_if' t low tag_of_low mid_of_tag vmatch_cases k

inline_for_extraction
fn free_dsum_payload_leaf
  (t: dsum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (f: (k: dsum_key t) -> PPB.free_t (vmatch_cases k))
  (k: dsum_key t)
: (free_dsum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)
=
  (xl: _)
  (#v: _)
{
  f k xl
}

inline_for_extraction
let free_dsum_payload_dispatch
  (t: dsum)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (f: (k: dsum_key t) -> PPB.free_t (vmatch_cases k))
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (free_dsum_payload_t t low tag_of_low mid_of_tag vmatch_cases))
  (k: dsum_key t)
: Tot (free_dsum_payload_t t low tag_of_low mid_of_tag vmatch_cases k)
= destr
    (fun _ -> eq_trivial)
    (free_dsum_payload_if t low tag_of_low mid_of_tag vmatch_cases)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (free_dsum_payload_leaf t low tag_of_low mid_of_tag vmatch_cases f)
    (repr_of_maybe_enum_key (dsum_enum t) k)

inline_for_extraction
fn free_dsum
  (t: dsum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (f: (k: dsum_key t) -> PPB.free_t (vmatch_cases k))
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (free_dsum_payload_t t low tag_of_low mid_of_tag vmatch_cases))
: PPB.free_t #low #(dsum_mid t mid_of_tag) (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases)
=
  (xl: low)
  (#v: Ghost.erased (dsum_mid t mid_of_tag))
{
  rewrite (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases xl v)
    as (pure (tag_of_low xl == dfst (Ghost.reveal v)) ** vmatch_cases (dfst (Ghost.reveal v)) xl (dsnd (Ghost.reveal v)));
  elim_pure_explicit (tag_of_low xl == dfst (Ghost.reveal v));
  let k = tag_of_low xl;
  rewrite (vmatch_cases (dfst (Ghost.reveal v)) xl (dsnd (Ghost.reveal v)))
    as (vmatch_cases k xl (dsnd (Ghost.reveal v)));
  free_dsum_payload_dispatch t low tag_of_low mid_of_tag vmatch_cases f destr k xl;
  ()
}

inline_for_extraction
fn free_dsum_case
  (t: dsum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (k: dsum_key t)
  (#tf: Type0)
  (#vmatch_field: tf -> mid_of_tag k -> slprop)
  (free_field: PPB.free_t vmatch_field)
  (disc: low -> option tf)
  (sq: squash (forall (xl: low) (cm: mid_of_tag k) .
        vmatch_cases k xl cm == (match disc xl with | Some y -> vmatch_field y cm | None -> pure False)))
: PPB.free_t #low #(mid_of_tag k) (vmatch_cases k)
=
  (xl: low)
  (#cm: _)
{
  match disc xl {
    Some y -> {
      rewrite (vmatch_cases k xl cm) as (vmatch_field y cm);
      free_field y;
    }
    None -> {
      rewrite (vmatch_cases k xl cm) as (pure False);
      let _ = elim_pure_explicit False;
      ()
    }
  }
}

(* ========== Copyful "safe serializer" (l2r_safe_writer) for IMPLICIT sums (sum_cases) ========== *)

#push-options "--z3rlimit 64"

// Bridge: the payload serializer bytes (serialize (sc k) vp) coincide with the
// whole [serialize_sum_cases] bytes for the synthesized case value, so the
// payload writer's postcond lifts to the sum_cases postcond unchanged.
let l2r_safe_writer_sum_cases_postcond_lemma
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (mid_of_tag: sum_key t -> Type0)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (k: sum_key t)
  (cm: mid_of_tag k)
  (v': Seq.seq byte)
  (res: SZ.t)
  (err: bool)
: Lemma
  (requires (
    l2r_safe_writer_postcond (conv_of_tag k) (sc k) cm v' res err
  ))
  (ensures (
    l2r_safe_writer_postcond (sum_cases_conv t mid_of_tag conv_of_tag k) (serialize_sum_cases t pc sc k) cm v' res err
  ))
= synth_sum_case_injective t k;
  synth_sum_case_inverse t k;
  match conv_of_tag k cm with
  | None -> ()
  | Some vp ->
    let yc : sum_cases t k = synth_sum_case t k vp in
    recip_case_id t k vp;
    serialize_synth_eq (dsnd (pc k)) (synth_sum_case t k) (sc k) (synth_sum_case_recip t k) () yc;
    assert (serialize (serialize_sum_cases t pc sc k) yc == serialize (sc k) vp)

inline_for_extraction
fn l2r_safe_writer_sum_cases
  (t: sum u#0 u#0)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((k: sum_key t) -> Tot (serializer (dsnd (pc k)))))
  (low: Type0)
  (tag_of_low: low -> sum_key t)
  (mid_of_tag: sum_key t -> Type0)
  (vmatch_cases: (k: sum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: sum_key t) -> mid_of_tag k -> GTot (option (sum_type_of_tag t k)))
  (w: (k: sum_key t) -> l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (destr: dep_enum_destr (sum_enum t) (l2r_safe_writer_sum_payload_t t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (k: sum_key t)
: PPB.l2r_safe_writer (vmatch_sum_cases t low tag_of_low mid_of_tag vmatch_cases k) (serialize_sum_cases t pc sc k) (sum_cases_conv t mid_of_tag conv_of_tag k)
=
  (xl: low)
  (#cm: Ghost.erased (mid_of_tag k))
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: ref bool)
{
  unfold (vmatch_sum_cases t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal cm));
  let res = l2r_safe_writer_sum_payload_dispatch t pc sc low tag_of_low mid_of_tag vmatch_cases conv_of_tag w destr k xl out perr;
  with v' err. assert (S.pts_to out v' ** vmatch_sum_case t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal cm) ** R.pts_to perr err ** pure (l2r_safe_writer_postcond (conv_of_tag k) (sc k) (Ghost.reveal cm) v' res err));
  fold (vmatch_sum_cases t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal cm));
  l2r_safe_writer_sum_cases_postcond_lemma t pc sc mid_of_tag conv_of_tag k (Ghost.reveal cm) v' res err;
  res
}

#pop-options

(* ========== Copyful "safe serializer" (l2r_safe_writer) combinators for OPEN sums (dsum) ========== *)

// l2r_safe_writer_dsum_payload_t: per-key safe writer for the payload of a
// known/unknown tag (uses vmatch_dsum_case, the variant WITH the pure tag fact).
// The per-tag payload serializer is [serialize_dsum_type_of_tag t f sr g sg k].
let l2r_safe_writer_dsum_payload_t
  (t: dsum)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (sr: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (k: dsum_key t)
: Tot Type
= PPB.l2r_safe_writer (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k) (serialize_dsum_type_of_tag t f sr g sg k) (conv_of_tag k)

inline_for_extraction
fn l2r_safe_writer_dsum_payload_if'
  (t: dsum u#0 u#0)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (sr: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (x: dsum_key t)
  (cond: bool)
  (ift: (cond_true cond -> Tot (l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag x)))
  (iff: (cond_false cond -> Tot (l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag x)))
: (l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag x)
=
  (input: _)
  (#y: _)
  (out: _)
  (#v: _)
  (perr: _)
{
  if cond {
    ift () input out perr
  } else {
    iff () input out perr
  }
}

inline_for_extraction
let l2r_safe_writer_dsum_payload_if
  (t: dsum u#0 u#0)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (sr: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (x: dsum_key t)
: Tot (if_combinator (l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag x) eq_trivial)
= l2r_safe_writer_dsum_payload_if' t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag x

inline_for_extraction
fn l2r_safe_writer_dsum_payload_leaf
  (t: dsum u#0 u#0)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (sr: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (w: (k: dsum_key t) -> l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (x: dsum_key t)
: (l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag x)
=
  (input: _)
  (#y: _)
  (out: _)
  (#v: _)
  (perr: _)
{
  w x input out perr
}

inline_for_extraction
let l2r_safe_writer_dsum_payload_dispatch
  (t: dsum)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (sr: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (w: (k: dsum_key t) -> l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (k: dsum_key t)
: Tot (l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
= destr
    (fun _ -> eq_trivial)
    (l2r_safe_writer_dsum_payload_if t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag)
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (l2r_safe_writer_dsum_payload_leaf t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag w)
    (repr_of_maybe_enum_key (dsum_enum t) k)

// l2r_safe_writer_dsum_case: build a per-case safe writer from the field safe
// writer and an option-valued discriminator `disc` (mirror l2r_safe_writer_sum_case).
inline_for_extraction
fn l2r_safe_writer_dsum_case
  (t: dsum u#0 u#0)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (k: dsum_key t)
  (#tf: Type0)
  (#kf: Ghost.erased parser_kind)
  (#pf: parser kf (dsum_type_of_tag t k))
  (#sf: serializer pf)
  (#vmatch_field: tf -> mid_of_tag k -> slprop)
  (wf: PPB.l2r_safe_writer vmatch_field sf (conv_of_tag k))
  (disc: low -> option tf)
  (sq: squash (forall (xl: low) (cm: mid_of_tag k) .
        vmatch_cases k xl cm == (match disc xl with | Some y -> vmatch_field y cm | None -> pure False)))
: PPB.l2r_safe_writer (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k) sf (conv_of_tag k)
=
  (xl: low)
  (#y: Ghost.erased (mid_of_tag k))
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: ref bool)
{
  unfold (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal y));
  elim_pure_explicit (tag_of_low xl == k);
  match disc xl {
    Some yf -> {
      rewrite (vmatch_cases k xl (Ghost.reveal y)) as (vmatch_field yf (Ghost.reveal y));
      let res = wf yf out perr;
      rewrite (vmatch_field yf (Ghost.reveal y)) as (vmatch_cases k xl (Ghost.reveal y));
      fold (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal y));
      res
    }
    None -> {
      rewrite (vmatch_cases k xl (Ghost.reveal y)) as (pure False);
      let _ = elim_pure_explicit False;
      intro_pure False ();
      rewrite (pure False) as (vmatch_cases k xl (Ghost.reveal y));
      fold (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k xl (Ghost.reveal y));
      false_elim ()
    }
  }
}

#push-options "--z3rlimit 64"

let recip_dcase_id (t: dsum) (k: dsum_key t) (vp: dsum_type_of_tag t k)
: Lemma (synth_dsum_case_recip t k (synth_dsum_case t k vp) == vp)
= DSum?.synth_case_recip_synth_case t k vp

// Postcondition lemma for the OK path: out = tag-bytes ++ payload-bytes.
let l2r_safe_writer_dsum_postcond_lemma
  (t: dsum)
  (#kt: parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (sr: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (mid_of_tag: dsum_key t -> Type0)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (m: dsum_mid t mid_of_tag)
  (vleft' vright': Seq.seq byte)
  (res1 res2 resf: SZ.t)
  (e2: bool)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: Lemma
  (requires (
    SZ.v res1 == Seq.length vleft' /\
    vleft' == serialize (serialize_maybe_enum_key _ s (dsum_enum t)) (dfst m) /\
    (if e2 then SZ.v resf == SZ.v res1 else SZ.v resf == SZ.v res1 + SZ.v res2) /\
    l2r_safe_writer_postcond (conv_of_tag (dfst m)) (serialize_dsum_type_of_tag t f sr g sg (dfst m)) (dsnd m) vright' res2 e2
  ))
  (ensures (
    l2r_safe_writer_postcond (dsum_conv t mid_of_tag conv_of_tag) (serialize_dsum t s f sr g sg)
      m (Seq.append vleft' vright') resf e2
  ))
= let k = dfst m in
  let cm = dsnd m in
  synth_dsum_case_injective t k;
  synth_dsum_case_inverse t k;
  match conv_of_tag k cm with
  | None -> ()
  | Some vp ->
    let yc : dsum_cases t k = synth_dsum_case t k vp in
    let yh : dsum_type t = yc in
    assert (dsum_tag_of_data t yh == k);
    serialize_dsum_eq' t s f sr g sg yh;
    recip_dcase_id t k vp;
    serialize_synth_eq _ (synth_dsum_case t k) (serialize_dsum_type_of_tag t f sr g sg k) (synth_dsum_case_recip t k) () yh;
    assert (synth_dsum_case_recip t k yh == vp);
    assert (serialize (serialize_dsum t s f sr g sg) yh ==
            Seq.append (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) k) (serialize (serialize_dsum_type_of_tag t f sr g sg k) vp));
    slice_append_prefix vleft' vright' (Seq.length (serialize (serialize_dsum_type_of_tag t f sr g sg k) vp))

// Postcondition lemma for the no-room path: the output is untouched and shorter
// than the (constant-size) tag, hence shorter than the whole serialization.
let l2r_safe_writer_dsum_noroom_lemma
  (t: dsum)
  (#kt: parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (sr: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (mid_of_tag: dsum_key t -> Type0)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (m: dsum_mid t mid_of_tag)
  (vout: Seq.seq byte)
  (resf tag_sz: SZ.t)
  (sq: squash (kt.parser_kind_subkind == Some ParserStrong))
: Lemma
  (requires (
    Seq.length vout < SZ.v tag_sz /\
    kt.parser_kind_high == Some kt.parser_kind_low /\
    kt.parser_kind_low == SZ.v tag_sz
  ))
  (ensures (
    l2r_safe_writer_postcond (dsum_conv t mid_of_tag conv_of_tag) (serialize_dsum t s f sr g sg)
      m vout resf true
  ))
= let k = dfst m in
  synth_dsum_case_injective t k;
  synth_dsum_case_inverse t k;
  match conv_of_tag k (dsnd m) with
  | None -> ()
  | Some vp ->
    let yc : dsum_cases t k = synth_dsum_case t k vp in
    let yh : dsum_type t = yc in
    assert (dsum_tag_of_data t yh == k);
    let tg = dsum_tag_of_data t yh in
    serialize_dsum_eq' t s f sr g sg yh;
    serialize_length (serialize_maybe_enum_key _ s (dsum_enum t)) k;
    Seq.lemma_len_append
      (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tg)
      (serialize (serialize_dsum_cases t f sr g sg tg) yh);
    assert (Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) k) == SZ.v tag_sz)

inline_for_extraction
fn l2r_safe_writer_dsum
  (t: dsum u#0 u#0)
  (#kt: Ghost.erased parser_kind)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (wt: LPB.l2r_leaf_writer (serialize_maybe_enum_key _ s (dsum_enum t)))
  (tag_sz: SZ.t {
    (Ghost.reveal kt).parser_kind_high == Some (Ghost.reveal kt).parser_kind_low /\
    (Ghost.reveal kt).parser_kind_low == SZ.v tag_sz
  })
  (f: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x))))
  (sr: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (sg: serializer g)
  (low: Type0)
  (tag_of_low: low -> dsum_key t)
  (mid_of_tag: dsum_key t -> Type0)
  (vmatch_cases: (k: dsum_key t) -> low -> mid_of_tag k -> slprop)
  (conv_of_tag: (k: dsum_key t) -> mid_of_tag k -> GTot (option (dsum_type_of_tag t k)))
  (w: (k: dsum_key t) -> l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag k)
  (destr: dep_maybe_enum_destr_t (dsum_enum t) (l2r_safe_writer_dsum_payload_t t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag))
  (sq: squash ((Ghost.reveal kt).parser_kind_subkind == Some ParserStrong))
: PPB.l2r_safe_writer (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases) (serialize_dsum t s f sr g sg) (dsum_conv t mid_of_tag conv_of_tag)
=
  (xl: low)
  (#m: Ghost.erased (dsum_mid t mid_of_tag))
  (out: S.slice byte)
  (#v: Ghost.erased (Seq.seq byte))
  (perr: ref bool)
{
  unfold (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases xl (Ghost.reveal m));
  elim_pure_explicit (tag_of_low xl == dfst (Ghost.reveal m));
  let k = tag_of_low xl;
  rewrite (vmatch_cases (dfst (Ghost.reveal m)) xl (dsnd (Ghost.reveal m)))
    as (vmatch_cases k xl (dsnd (Ghost.reveal m)));
  S.pts_to_len out;
  let l = S.len out;
  if (SZ.lt l tag_sz) {
    perr := true;
    rewrite (vmatch_cases k xl (dsnd (Ghost.reveal m)))
      as (vmatch_cases (dfst (Ghost.reveal m)) xl (dsnd (Ghost.reveal m)));
    fold (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases xl (Ghost.reveal m));
    l2r_safe_writer_dsum_noroom_lemma t s f sr g sg mid_of_tag conv_of_tag (Ghost.reveal m) (Ghost.reveal v) tag_sz tag_sz sq;
    tag_sz
  } else {
    fold (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k xl (dsnd (Ghost.reveal m)));
    let left, right = S.split out tag_sz;
    S.pts_to_len left;
    serialize_length (serialize_maybe_enum_key _ s (dsum_enum t)) k;
    let res1 = wt k left 0sz;
    with vleft'. assert (S.pts_to left vleft');
    S.pts_to_len left;
    assert (pure (vleft' == serialize (serialize_maybe_enum_key _ s (dsum_enum t)) k));
    let res2 = l2r_safe_writer_dsum_payload_dispatch t f sr g sg low tag_of_low mid_of_tag vmatch_cases conv_of_tag w destr k xl right perr;
    let e2 = !perr;
    with vright'. assert (S.pts_to right vright');
    S.pts_to_len right;
    S.join left right out;
    S.pts_to_len out;
    unfold (vmatch_dsum_case t low tag_of_low mid_of_tag vmatch_cases k xl (dsnd (Ghost.reveal m)));
    rewrite (vmatch_cases k xl (dsnd (Ghost.reveal m)))
      as (vmatch_cases (dfst (Ghost.reveal m)) xl (dsnd (Ghost.reveal m)));
    fold (vmatch_dsum t low tag_of_low mid_of_tag vmatch_cases xl (Ghost.reveal m));
    let resf : SZ.t = if e2 { res1 } else { (SZ.add res1 res2 <: SZ.t) };
    l2r_safe_writer_dsum_postcond_lemma t s f sr g sg mid_of_tag conv_of_tag (Ghost.reveal m) vleft' vright' res1 res2 resf e2 sq;
    resf
  }
}

#pop-options

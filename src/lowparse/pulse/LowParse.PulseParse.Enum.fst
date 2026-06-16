module LowParse.PulseParse.Enum
include LowParse.PulseParse.Base
include LowParse.Spec.Enum
open LowParse.PulseParse.Combinators

module B = LowParse.Pulse.Combinators

inline_for_extraction
let is_known
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: maybe_enum_key e)
: Tot (b: bool { b == Known? k } )
= match k with
  | Known _ -> true
  | _ -> false

inline_for_extraction
let validate_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr) (v: B.validator p) (p32: leaf_reader p)
  (e: enum key repr)
  (destr: maybe_enum_destr_t bool e)
  (_: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (B.validator (parse_enum_key p e)) =
  B.validate_synth
    (validate_filter v p32 (parse_enum_key_cond e)
      (fun r -> destr eq2 (default_if bool) (fun _ -> ()) (fun _ _ _ -> ()) (is_known e) r)
      ()
    )
    (parse_enum_key_synth e)

[@Norm]
let mk_validate_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr) (v: B.validator p) (p32: leaf_reader p)
  (e: enum key repr)
  (_: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (B.validator (parse_enum_key p e))
= validate_enum_key v p32 e (mk_maybe_enum_destr bool e) ()

inline_for_extraction
let validate_maybe_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr) (v: B.validator p)
  (e: enum key repr)
: Tot (B.validator (parse_maybe_enum_key p e))
= B.validate_synth
    v
    (maybe_enum_key_of_repr e)

inline_for_extraction
let jump_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr) (j: B.jumper p)
  (e: enum key repr)
: Tot (B.jumper (parse_enum_key p e))
= B.jump_synth
    (B.jump_filter j (parse_enum_key_cond e))
    (parse_enum_key_synth e)

inline_for_extraction
let jump_maybe_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr) (j: B.jumper p)
  (e: enum key repr)
: Tot (B.jumper (parse_maybe_enum_key p e))
= B.jump_synth j (maybe_enum_key_of_repr e)

(* PulseParse leaf_readers for enum keys *)

inline_for_extraction
let read_maybe_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr)
  (r: leaf_reader p)
  (e: enum key repr)
  (destr: maybe_enum_destr_t (maybe_enum_key e) e)
: Tot (leaf_reader (parse_maybe_enum_key p e))
= leaf_reader_of_reader
    (read_synth (reader_of_leaf_reader r)
      (maybe_enum_key_of_repr e)
      (repr_of_maybe_enum_key e)
      (fun x -> read_synth_cont_init
        (destr _ (default_if _) (fun _ -> ()) (fun _ _ _ -> ()) (fun k -> k) x)))

[@Norm]
let mk_read_maybe_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr)
  (r: leaf_reader p)
  (e: enum key repr)
: Tot (leaf_reader (parse_maybe_enum_key p e))
= read_maybe_enum_key r e (mk_maybe_enum_destr (maybe_enum_key e) e)

inline_for_extraction
let read_enum_key_prop
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: maybe_enum_key e)
  (k' : enum_key e)
: GTot prop
= match k with Known k_ -> (k_ <: key) == (k' <: key) | _ -> False

inline_for_extraction
let read_enum_key_t
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: maybe_enum_key e)
: Tot Type
= squash (Known? k) -> Tot (k' : enum_key e { read_enum_key_prop e k k' } )

inline_for_extraction
let read_enum_key_f
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e } )
  (k: maybe_enum_key e)
: Tot (read_enum_key_t e k)
= fun (sq: squash (Known? k)) ->
  match k with
  | Known k_ ->
    (k_ <: (k_ : enum_key e { read_enum_key_prop e k k_ } ))
  | _ ->
    (match e with (k_, _) :: _ ->
    [@inline_let] let _ = assert False; assert (read_enum_key_prop e k k_) in
    (k_ <: (k_ : enum_key e { read_enum_key_prop e k k_ } ))) // dummy, but needed to make extraction work

inline_for_extraction
let read_enum_key_eq
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: maybe_enum_key e)
: Tot (read_enum_key_t e k -> read_enum_key_t e k -> GTot prop)
= fun _ _ -> True

inline_for_extraction
let read_enum_key_if
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: maybe_enum_key e)
: Tot (if_combinator _ (read_enum_key_eq e k))
= fun
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (read_enum_key_t e k)))
  (sv_false: (cond_false cond -> Tot (read_enum_key_t e k)))
  (sq: squash (Known? k)) ->
  if cond
  then sv_true () sq
  else sv_false () sq

inline_for_extraction
let read_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr)
  (r: leaf_reader p)
  (e: enum key repr { Cons? e })
  (destr: dep_maybe_enum_destr_t e (read_enum_key_t e))
  (_: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (leaf_reader (parse_enum_key p e))
= serialize_enum_key_synth_inverse e;
  leaf_reader_of_reader
    (read_synth
      (read_filter (reader_of_leaf_reader r) (parse_enum_key_cond e))
      (parse_enum_key_synth e)
      (serialize_enum_key_synth_recip e)
      (fun (x: parse_filter_refine (parse_enum_key_cond e)) ->
        [@inline_let] let _ = assert (maybe_enum_key_of_repr e x == Known (enum_key_of_repr e x)) in
        read_synth_cont_init
          (destr (read_enum_key_eq e) (read_enum_key_if e)
            (fun _ _ -> ()) (fun _ _ _ _ -> ()) (read_enum_key_f e) x ())))

[@Norm]
let mk_read_enum_key
  (#key #repr: eqtype)
  (#k: Ghost.erased parser_kind) (#p: parser k repr)
  (r: leaf_reader p)
  (e: enum key repr { Cons? e })
  (_: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (leaf_reader (parse_enum_key p e))
= read_enum_key r e (mk_dep_maybe_enum_destr e (read_enum_key_t e)) ()

// For a repr that is a known enum member, maybe_enum_key_of_repr reduces to Known
// of the corresponding key.  Bridges the dependent-destructor result type.
let maybe_enum_key_of_repr_known
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: enum_repr e)
: Lemma (maybe_enum_key_of_repr e r == Known (enum_key_of_repr e r))
= ()

// Compute the (closed) enum key of a known repr via the reducible [@Norm]
// dependent destructor, instead of the spec list-walker enum_key_of_repr.  The
// result is propositionally equal to enum_key_of_repr e r, so callers can keep
// the latter in ghost position.  Used by read_sum_tag (LowParse.PulseParse.Sum).
inline_for_extraction
let enum_key_of_repr_destr
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e })
  (destr: dep_maybe_enum_destr_t e (read_enum_key_t e))
  (r: enum_repr e)
: Tot (k: enum_key e { k == enum_key_of_repr e r })
= maybe_enum_key_of_repr_known e r;
  destr (read_enum_key_eq e) (read_enum_key_if e)
    (fun _ _ -> ()) (fun _ _ _ _ -> ()) (read_enum_key_f e) r ()

[@Norm]
let mk_enum_key_of_repr_destr
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e })
  (r: enum_repr e)
: Tot (k: enum_key e { k == enum_key_of_repr e r })
= enum_key_of_repr_destr e (mk_dep_maybe_enum_destr e (read_enum_key_t e)) r

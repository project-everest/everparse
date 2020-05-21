module LowParse.Low.Enum
include LowParse.Spec.Enum
include LowParse.Low.Combinators

module I32 = FStar.Int32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

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
  (#k: parser_kind) (#p: parser k repr) (v: validator p) (p32: leaf_reader p)
  (e: enum key repr)
  (destr: maybe_enum_destr_t bool e)
: Tot (validator (parse_enum_key p e)) =
  validate_synth
    (validate_filter v p32 (parse_enum_key_cond e)
      (fun r -> destr eq2 (default_if bool) (fun _ -> ()) (fun _ _ _ -> ()) (is_known e) r))
    (parse_enum_key_synth e)
    ()

[@Norm]
let mk_validate_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (v: validator p) (p32: leaf_reader p)
  (e: enum key repr)
: Tot (validator (parse_enum_key p e))
= validate_enum_key v p32 e (mk_maybe_enum_destr bool e)

inline_for_extraction
let validate_maybe_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (v: validator p)
  (e: enum key repr)
: Tot (validator (parse_maybe_enum_key p e))
= validate_synth
    v
    (maybe_enum_key_of_repr e)
    ()

inline_for_extraction
let jump_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (j: jumper p)
  (e: enum key repr)
: Tot (jumper (parse_enum_key p e))
= jump_synth
    (jump_filter j (parse_enum_key_cond e))
    (parse_enum_key_synth e)
    ()

inline_for_extraction
let jump_maybe_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (j: jumper p)
  (e: enum key repr)
: Tot (jumper (parse_maybe_enum_key p e))
= jump_synth j (maybe_enum_key_of_repr e) ()

inline_for_extraction
let read_maybe_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (j: leaf_reader p)
  (e: enum key repr)
  (destr: maybe_enum_destr_t (maybe_enum_key e) e)
: Tot (leaf_reader (parse_maybe_enum_key p e))
= read_synth
    _
    (maybe_enum_key_of_repr e)
    (fun x -> destr _ (default_if _) (fun _ -> ()) (fun _ _ _ -> ()) (fun k -> k) x)
    j
    ()

[@Norm]
let mk_read_maybe_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (j: leaf_reader p)
  (e: enum key repr)
: Tot (leaf_reader (parse_maybe_enum_key p e))
= read_maybe_enum_key j e (mk_maybe_enum_destr (maybe_enum_key e) e)

inline_for_extraction
let read_enum_key_prop
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: maybe_enum_key e)
  (k' : enum_key e)
: GTot Type0
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
: Tot (read_enum_key_t e k -> read_enum_key_t e k -> GTot Type0)
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
  (#k: parser_kind) (#p: parser k repr) (p32: leaf_reader p)
  (e: enum key repr { Cons? e })
  (destr: dep_maybe_enum_destr_t e (read_enum_key_t e))
: Tot (leaf_reader (parse_enum_key p e))
= read_synth
    (parse_filter p (parse_enum_key_cond e))
    (parse_enum_key_synth e)
    (fun r -> destr (read_enum_key_eq e) (read_enum_key_if e) (fun _ _ -> ()) (fun _ _ _ _ -> ()) (read_enum_key_f e) r ())
    (read_filter p32 (parse_enum_key_cond e))
    ()

[@Norm]
let mk_read_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (p32: leaf_reader p)
  (e: enum key repr { Cons? e })
: Tot (leaf_reader (parse_enum_key p e))
= read_enum_key p32 e (mk_dep_maybe_enum_destr e (read_enum_key_t e))

inline_for_extraction
let write_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (#s: serializer p) (s32: leaf_writer_strong s)
  (e: enum key repr)
  (destr: enum_repr_of_key'_t e)
: Tot (leaf_writer_strong (serialize_enum_key _ s e))
= [@inline_let] let _ = serialize_enum_key_synth_inverse e in
  write_synth
    (write_filter s32 (parse_enum_key_cond e))
    (parse_enum_key_synth e)
    (serialize_enum_key_synth_recip e)
    (fun k -> destr k)
    ()

inline_for_extraction
let write_enum_key_weak
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (#s: serializer p) (s32: leaf_writer_weak s)
  (e: enum key repr)
  (destr: enum_repr_of_key'_t e)
: Tot (leaf_writer_weak (serialize_enum_key _ s e))
= [@inline_let] let _ = serialize_enum_key_synth_inverse e in
  write_synth_weak
    (write_filter_weak s32 (parse_enum_key_cond e))
    (parse_enum_key_synth e)
    (serialize_enum_key_synth_recip e)
    (fun k -> destr k)
    ()

inline_for_extraction
let write_maybe_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (#s: serializer p) (s32: leaf_writer_strong s)
  (e: enum key repr)
  (destr: enum_repr_of_key'_t e)
: Tot (leaf_writer_strong (serialize_maybe_enum_key _ s e))
= [@inline_let] let _ = serialize_enum_key_synth_inverse e in
  write_synth
    s32
    (maybe_enum_key_of_repr e)
    (repr_of_maybe_enum_key e)
    (fun k ->
      match k with 
      | Unknown r -> r
      | Known k -> destr k)
    ()

inline_for_extraction
let write_maybe_enum_key_weak
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (#s: serializer p) (s32: leaf_writer_weak s)
  (e: enum key repr)
  (destr: enum_repr_of_key'_t e)
: Tot (leaf_writer_weak (serialize_maybe_enum_key _ s e))
= [@inline_let] let _ = serialize_enum_key_synth_inverse e in
  write_synth_weak
    s32
    (maybe_enum_key_of_repr e)
    (repr_of_maybe_enum_key e)
    (fun k ->
      match k with 
      | Unknown r -> r
      | Known k -> destr k)
    ()

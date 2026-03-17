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
  (#k: parser_kind) (#p: parser k repr) (v: B.validator p) (p32: leaf_reader p)
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
  (#k: parser_kind) (#p: parser k repr) (v: B.validator p) (p32: leaf_reader p)
  (e: enum key repr)
  (_: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (B.validator (parse_enum_key p e))
= validate_enum_key v p32 e (mk_maybe_enum_destr bool e) ()

inline_for_extraction
let validate_maybe_enum_key
  (#key #repr: eqtype)
  (#k: parser_kind) (#p: parser k repr) (v: B.validator p)
  (e: enum key repr)
: Tot (B.validator (parse_maybe_enum_key p e))
= validate_synth
    v
    (maybe_enum_key_of_repr e)

module LowParseWriters.Parsers
include LowParseWriters

module LP = LowParse.Low
module Seq = FStar.Seq
module U32 = FStar.UInt32

inline_for_extraction
noextract
val get_parser_kind
  (p: parser)
: Tot (kind: LP.parser_kind { kind.LP.parser_kind_subkind == Some LP.ParserStrong })

val get_parser
  (p: parser)
: Tot (LP.parser (get_parser_kind p) (dfst p))

val get_serializer
  (p: parser)
: Tot (LP.serializer (get_parser p))

inline_for_extraction
noextract
val make_parser'
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Tot (parser' t)

inline_for_extraction
noextract
let make_parser
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Tot parser
= (| t, make_parser' p s j |)

val make_parser_correct
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (s: LP.serializer p)
  (j: LP.jumper p)
: Lemma
  (let p' = make_parser p s j in
   get_parser_kind p' == k /\
   get_parser p' == p /\
   get_serializer p' == s
  )
  [SMTPat (make_parser p s j)]

val size_correct
  (p: parser)
  (x: dfst p)
: Lemma
  (size p x == Seq.length (LP.serialize (get_serializer p) x))
  [SMTPat (size p x)]

val valid_synth_parser_eq
  (p1: parser)
  (p2: parser {
    dfst p1 == dfst p2 /\
    get_parser_kind p1 == get_parser_kind p2 /\
    get_parser p1 == LP.coerce (LP.parser (get_parser_kind p1) (dfst p1)) (get_parser p2)
  })
: Tot (valid_synth_t p1 p2 (fun _ -> True) (fun x -> x))

inline_for_extraction
val parse_synth
  (p1: parser)
  (#t2: Type)
  (f2: dfst p1 -> GTot t2)
  (f1: t2 -> GTot (dfst p1))
: Pure parser
  (requires (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
  (ensures (fun r ->
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1 /\
    dfst r == t2 /\
    get_parser_kind r == get_parser_kind p1 /\
    get_parser r == LP.coerce (LP.parser (get_parser_kind r) (dfst r)) (get_parser p1 `LP.parse_synth` f2) /\
    get_serializer r == LP.coerce (LP.serializer (get_parser r)) (LP.serialize_synth (get_parser p1) f2 (get_serializer p1) f1 ())
  ))

val valid_synth_parse_synth
  (p1: parser)
  (#t2: Type)
  (f2: dfst p1 -> GTot t2)
  (f1: t2 -> GTot (dfst p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (valid_synth_t p1 (parse_synth p1 f2 f1) (fun _ -> True) f2)

val parse_vldata
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (p' : parser {
    dfst p' == LP.parse_bounded_vldata_strong_t (U32.v min) (U32.v max) (get_serializer p) /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) (get_parser_kind p) /\
    get_parser p' == LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p) /\
    get_serializer p' == LP.serialize_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p)
  })

val valid_synth_parse_vldata
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 })
: Tot (valid_synth_t (parse_vldata p min max) (parse_vldata p min' max') (fun x -> U32.v min' <= size p x /\ size p x <= U32.v max' /\ LP.log256' (U32.v max') == LP.log256' (U32.v max))
(fun x -> x))

inline_for_extraction
type parser1 = (p: parser {
  match (get_parser_kind p).LP.parser_kind_high with
  | None -> False
  | Some max -> max > 0
})

inline_for_extraction
val rlptr: Type0
val valid_rlptr (p: parser1) : memory_invariant -> rlptr -> GTot Type0

let lptr (p: parser1) (inv: memory_invariant) =
  (x: rlptr { valid_rlptr p inv x })

val deref_list_spec (#p: parser1) (#inv: memory_invariant) (x: lptr p inv) : GTot (list (dfst p))

val valid_rlptr_frame
  (#p: parser1) (#inv: memory_invariant) (x: lptr p inv) (inv' : memory_invariant)
: Lemma
  (requires (
    inv `memory_invariant_includes` inv'
  ))
  (ensures (
    valid_rlptr p inv' x /\
    deref_list_spec #p #inv' x == deref_list_spec #p #inv x
  ))
  [SMTPatOr [
    [SMTPat (inv `memory_invariant_includes` inv'); SMTPat (valid_rlptr p inv x)];
    [SMTPat (inv `memory_invariant_includes` inv'); SMTPat (valid_rlptr p inv' x)];
  ]]

unfold
let destr_list_post
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
  (res: option (ptr p inv & lptr p inv))
: GTot Type0
= 
  match res, deref_list_spec x with
  | None, [] -> True
  | Some (hd, tl), hd' :: tl' ->
    deref_spec hd == hd' /\ deref_list_spec tl == tl'
  | _ -> False

inline_for_extraction
val destr_list
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
: Read (option (ptr p inv & lptr p inv)) (True) (destr_list_post x) inv

let rec list_exists
  (#p: parser1)
  (#inv: memory_invariant)
  (f_spec: Ghost.erased (dfst p -> Tot bool)) // reifying f below is not enough because of the ptr
  (f: ((x: ptr p inv) -> Read bool (True) (fun res -> res == Ghost.reveal f_spec (deref_spec x)) inv))
  (l: lptr p inv)
: Read bool (True) (fun res -> res == List.Tot.existsb f_spec (deref_list_spec l)) inv
  (decreases (List.Tot.length (deref_list_spec l)))
= match destr_list l with
  | None -> false
  | Some (hd, tl) ->
    if f hd
    then true
    else list_exists f_spec f tl

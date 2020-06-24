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

inline_for_extraction
val deref
  (#p: parser)
  (#inv: memory_invariant)
  (r: LP.leaf_reader (get_parser p))
  (x: ptr p inv)
: Read (dfst p) True (fun res -> res == deref_spec x) inv

inline_for_extraction
val start
  (#p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: dfst p)
: Write unit emp (p) (fun _ -> True) (fun _ _ y -> y == x) l

inline_for_extraction
val append
  (#fr: parser)
  (#p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: dfst p)
: Write unit fr (fr `star` p) (fun _ -> True) (fun w _ (w', x') -> w' == w /\ x' == x) l

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

inline_for_extraction
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
val parse_bounded_integer
  (sz: LP.integer_size)
: Tot (p' : parser {
    dfst p' == LP.bounded_integer sz /\
    get_parser_kind p' == LP.parse_bounded_integer_kind sz /\
    get_parser p' == LP.parse_bounded_integer sz /\
    get_serializer p' == LP.serialize_bounded_integer sz
  })

let parse_vldata_intro_spec
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_spec unit (parse_bounded_integer (LP.log256' (U32.v max)) `star` p) (parse_vldata p min max) (fun (_, vin) -> U32.v min <= size p vin /\ size p vin <= U32.v max) (fun (_, vin) _ vout -> vin == vout) (fun _ -> False))
=
  fun (_, vin) -> Correct ((), vin)

inline_for_extraction
val parse_vldata_intro_impl
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vldata_intro_spec p min max))

inline_for_extraction
let parse_vldata_intro
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Write unit (parse_bounded_integer (LP.log256' (U32.v max)) `star` p) (parse_vldata p min max) (fun (_, vin) -> U32.v min <= size p vin /\ size p vin <= U32.v max) (fun (_, vin) _ vout -> vin == vout) inv
= EWrite?.reflect (| parse_vldata_intro_spec p min max, parse_vldata_intro_impl p min max |)

inline_for_extraction
let parse_vldata_intro_frame
  (#inv: memory_invariant)
  (frame: parser)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Write unit ((frame `star` parse_bounded_integer (LP.log256' (U32.v max))) `star` p) (frame `star` parse_vldata p min max) (fun (_, vin) -> U32.v min <= size p vin /\ size p vin <= U32.v max) (fun ((fr, _), vin) _ (fr', vout) -> fr == fr' /\ (vin <: dfst p) == (vout <: dfst p)) inv
= valid_synth _ _ _ _ _ (valid_synth_star_assoc_1 _ _ _);
  frame2 _ _ _ _ _ _ _ _ (fun _ -> parse_vldata_intro p min max)

let parse_vldata_intro_weak_spec
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_spec unit (parse_bounded_integer (LP.log256' (U32.v max)) `star` p) (parse_vldata p min max) (fun _ -> True) (fun (_, vin) _ vout -> vin == vout) (fun (_, vin) -> ~ (U32.v min <= size p vin /\ size p vin <= U32.v max)))
=
  fun (_, vin) ->
    let sz = size p vin in
    if U32.v min <= sz && sz <= U32.v max
    then Correct ((), vin)
    else Error "parse_vldata_intro_weak_spec: out of bounds"

inline_for_extraction
val parse_vldata_intro_weak_impl
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vldata_intro_weak_spec p min max))

inline_for_extraction
let parse_vldata_intro_weak
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: EWrite unit (parse_bounded_integer (LP.log256' (U32.v max)) `star` p) (parse_vldata p min max) (fun _ -> True) (fun (_, vin) _ vout -> vin == vout) (fun (_, vin) -> ~ (U32.v min <= size p vin /\ size p vin <= U32.v max)) inv
= EWrite?.reflect (| _, parse_vldata_intro_weak_impl p min max |)

inline_for_extraction
let parse_vldata_intro_weak_frame
  (#inv: memory_invariant)
  (frame: parser)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: EWrite unit ((frame `star` parse_bounded_integer (LP.log256' (U32.v max))) `star` p) (frame `star` parse_vldata p min max) (fun _ -> True) (fun ((fr, _), vin) _ (fr', vout) -> fr == fr' /\ (vin <: dfst p) == (vout <: dfst p)) (fun (_, vin) -> ~ (U32.v min <= size p vin /\ size p vin <= U32.v max)) inv
= 
  valid_synth _ _ _ _ _ (valid_synth_star_assoc_1 _ _ _);
  frame2 _ _ _ _ _ _ _ _ (fun _ -> parse_vldata_intro_weak p min max)

inline_for_extraction
type parser1 = (p: parser {
  (get_parser_kind p).LP.parser_kind_low > 0
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

let parse_vllist_t
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot Type
= let s = LP.serialize_list (get_parser p) (get_serializer p) in
  LP.parse_bounded_vldata_strong_t (U32.v min) (U32.v max) s

inline_for_extraction
val parse_vllist
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (p' : parser {
    dfst p' == parse_vllist_t p min max /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) LP.parse_list_kind /\
    get_parser p' == LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) /\
    get_serializer p' == LP.serialize_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) /\
    True
  })

inline_for_extraction
val lptr_of_vllist_ptr
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (r: ptr (parse_vllist p min max) inv)
: Read (lptr p inv) True (fun r' -> deref_list_spec r' == (deref_spec r <: list (dfst p))) inv

let list_size
  (p: parser1)
  (x: list (dfst p))
: GTot nat
= Seq.length (LP.serialize (LP.serialize_list _ (get_serializer p)) x)

let parse_vllist_nil_spec
  (p: parser1)
  (max: U32.t { U32.v max > 0 })
: Tot (repr_spec unit emp (parse_vllist p 0ul max) (fun _ -> True) (fun _ _ x -> (x <: list (dfst p)) == [] /\ list_size p x == 0) (fun _ -> False))
= fun _ ->
  LP.serialize_list_nil _ (get_serializer p);
  Correct ((), ([] <: parse_vllist_t p 0ul max))

inline_for_extraction
val parse_vllist_nil_impl
  (#inv: memory_invariant)
  (p: parser1)
  (max: U32.t { U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vllist_nil_spec p max))

inline_for_extraction
let parse_vllist_nil
  (#inv: memory_invariant)
  (p: parser1)
  (max: U32.t { U32.v max > 0 })
: Write unit emp (parse_vllist p 0ul max) (fun _ -> True) (fun _ _ x -> (x <: list (dfst p)) == [] /\ list_size p x == 0) inv
= EWrite?.reflect (| _, parse_vllist_nil_impl p max |)

module L = FStar.List.Tot

#push-options "--z3rlimit 32"

let parse_vllist_snoc_spec
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_spec unit (parse_vllist p min max `star` p) (parse_vllist p min max)
    (fun (l, x) ->
      let sz = list_size p l + size p x in
      U32.v min <= sz /\ sz <= U32.v max)
    (fun (l, x) _ l' -> (l' <: list (dfst p)) == L.snoc ((l <: list (dfst p)), x) /\ list_size p l' == list_size p l + size p x)
    (fun _ -> False)
  )
= fun (l, x) ->
  LP.serialize_list_singleton _ (get_serializer p) x;
  LP.serialize_list_append _ (get_serializer p) l [x];
  Correct ((), L.snoc ((l <: list (dfst p)), x))

#pop-options

inline_for_extraction
val parse_vllist_snoc_impl
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vllist_snoc_spec p min max))

inline_for_extraction
let parse_vllist_snoc
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Write unit (parse_vllist p min max `star` p) (parse_vllist p min max)
    (fun (l, x) ->
      let sz = list_size p l + size p x in
      U32.v min <= sz /\ sz <= U32.v max)
    (fun (l, x) _ l' -> (l' <: list (dfst p)) == L.snoc ((l <: list (dfst p)), x) /\ list_size p l' == list_size p l + size p x)
    inv
=
  EWrite?.reflect (| _, parse_vllist_snoc_impl p min max |)

#push-options "--z3rlimit 32"

let parse_vllist_snoc_weak_spec
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_spec unit (parse_vllist p min max `star` p) (parse_vllist p min max)
    (fun _ -> True)
    (fun (l, x) _ l' -> (l' <: list (dfst p)) == L.snoc ((l <: list (dfst p)), x) /\ list_size p l' == list_size p l + size p x)
    (fun (l, x) ->
      let sz = list_size p l + size p x in
      ~ (U32.v min <= sz /\ sz <= U32.v max))
  )
= fun (l, x) ->
  let sz = list_size p l + size p x in
  if U32.v min <= sz && sz <= U32.v max
  then begin
    LP.serialize_list_singleton _ (get_serializer p) x;
    LP.serialize_list_append _ (get_serializer p) l [x];
    Correct ((), L.snoc ((l <: list (dfst p)), x))
  end else
    Error "parse_vllist_snoc_weak: out of bounds"

#pop-options

inline_for_extraction
val parse_vllist_snoc_weak_impl
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vllist_snoc_weak_spec p min max))

inline_for_extraction
let parse_vllist_snoc_weak
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: EWrite unit (parse_vllist p min max `star` p) (parse_vllist p min max)
    (fun _ -> True)
    (fun (l, x) _ l' -> (l' <: list (dfst p)) == L.snoc ((l <: list (dfst p)), x) /\ list_size p l' == list_size p l + size p x)
    (fun (l, x) ->
      let sz = list_size p l + size p x in
      ~ (U32.v min <= sz /\ sz <= U32.v max))
    inv
=
  EWrite?.reflect (| _, parse_vllist_snoc_weak_impl p min max |)

val valid_synth_parse_vllist
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 })
: Tot (valid_synth_t (parse_vllist p min max) (parse_vllist p min' max') (fun x -> U32.v min' <= list_size p x /\ list_size p x <= U32.v max' /\ LP.log256' (U32.v max') == LP.log256' (U32.v max))
(fun x -> x))

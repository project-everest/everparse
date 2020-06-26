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

val star_correct
  (p1 p2: parser)
: Lemma
  (get_parser_kind (p1 `star` p2) == get_parser_kind p1 `LP.and_then_kind` get_parser_kind p2 /\
  get_parser (p1 `star` p2) == get_parser p1 `LP.nondep_then` get_parser p2 /\
  get_serializer (p1 `star` p2) == get_serializer p1 `LP.serialize_nondep_then` get_serializer p2)
  [SMTPat (p1 `star` p2)]

inline_for_extraction
val deref
  (#p: parser)
  (#inv: memory_invariant)
  (r: LP.leaf_reader (get_parser p))
  (x: ptr p inv)
: Read (dfst p) True (fun res -> res == deref_spec x) inv

inline_for_extraction
val start
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: dfst p)
: Write unit emp (p) (fun _ -> True) (fun _ _ y -> y == x) l

inline_for_extraction
val append
  (#fr: parser)
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: dfst p)
: Write unit fr (fr `star` p) (fun _ -> True) (fun w _ (w', x') -> w' == w /\ x' == x) l

inline_for_extraction
val access
  (p1 p2: parser)
  (#lens: LP.clens (dfst p1) (dfst p2))
  (#inv: memory_invariant)
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
  (x: ptr p1 inv)
: Read (ptr p2 inv) (lens.LP.clens_cond (deref_spec x)) (fun res -> lens.LP.clens_cond (deref_spec x) /\ deref_spec res == lens.LP.clens_get (deref_spec x)) inv

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

val valid_synth_parse_synth_recip
  (p1: parser)
  (#t2: Type)
  (f2: dfst p1 -> GTot t2)
  (f1: t2 -> GTot (dfst p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (valid_synth_t (parse_synth p1 f2 f1) p1 (fun _ -> True) f1)

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
    else Error "parse_vldata_intro_weak: out of bounds"

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

let parse_vldata_recast_spec
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ LP.log256' (U32.v max) == LP.log256' (U32.v max')})
: Tot (repr_spec unit (parse_vldata p min max) (parse_vldata p min' max') (fun _ -> True) (fun vin _ vout -> (vin <: dfst p) == (vout <: dfst p)) (fun vin -> ~ (U32.v min' <= size p vin /\ size p vin <= U32.v max')))
=
  fun vin ->
    let sz = size p vin in
    if U32.v min' <= sz && sz <= U32.v max'
    then Correct ((), vin)
    else Error "parse_vldata_recast: out of bounds"

inline_for_extraction
val parse_vldata_recast_impl
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ LP.log256' (U32.v max) == LP.log256' (U32.v max')})
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vldata_recast_spec p min max min' max'))

inline_for_extraction
let parse_vldata_recast
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ LP.log256' (U32.v max) == LP.log256' (U32.v max')})
: EWrite unit (parse_vldata p min max) (parse_vldata p min' max') (fun _ -> True) (fun vin _ vout -> (vin <: dfst p) == (vout <: dfst p)) (fun vin -> ~ (U32.v min' <= size p vin /\ size p vin <= U32.v max')) inv
= EWrite?.reflect (| _, parse_vldata_recast_impl p min max min' max' |)

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

let list_size_nil
  (p: parser1)
: Lemma
  (list_size p [] == 0)
  [SMTPat (list_size p [])]
= LP.serialize_list_nil _ (get_serializer p)

let list_size_cons
  (p: parser1)
  (a: dfst p)
  (q: list (dfst p))
: Lemma
  (list_size p (a :: q) == size p a + list_size p q)
  [SMTPat (list_size p (a :: q))]
= LP.serialize_list_cons _ (get_serializer p) a q

module L = FStar.List.Tot

let rec list_size_append
  (p: parser1)
  (l1 l2: list (dfst p))
: Lemma
  (list_size p (l1 `L.append` l2) == list_size p l1 + list_size p l2)
  [SMTPat (list_size p (l1 `L.append` l2))]
= match l1 with
  | [] -> ()
  | a :: q -> list_size_append p q l2

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

let parse_vllist_recast_spec
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ LP.log256' (U32.v max) == LP.log256' (U32.v max')})
: Tot (repr_spec unit (parse_vllist p min max) (parse_vllist p min' max') (fun _ -> True) (fun vin _ vout -> (vin <: list (dfst p)) == (vout <: list (dfst p))) (fun vin -> ~ (U32.v min' <= list_size p vin /\ list_size p vin <= U32.v max')))
=
  fun vin ->
    let sz = list_size p vin in
    if U32.v min' <= sz && sz <= U32.v max'
    then Correct ((), vin)
    else Error "parse_vllist_recast: out of bounds"

inline_for_extraction
val parse_vllist_recast_impl
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ LP.log256' (U32.v max) == LP.log256' (U32.v max')})
: Tot (repr_impl _ _ _ _ _ _ inv (parse_vllist_recast_spec p min max min' max'))

inline_for_extraction
let parse_vllist_recast
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ LP.log256' (U32.v max) == LP.log256' (U32.v max')})
: EWrite unit (parse_vllist p min max) (parse_vllist p min' max') (fun _ -> True) (fun vin _ vout -> (vin <: list (dfst p)) == (vout <: list (dfst p))) (fun vin -> ~ (U32.v min' <= list_size p vin /\ list_size p vin <= U32.v max')) inv
= EWrite?.reflect (| _, parse_vllist_recast_impl p min max min' max' |)

inline_for_extraction
val parse_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot (p' : parser {
    dfst p' == LP.parse_bounded_vlbytes_t (U32.v min) (U32.v max) /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) LP.parse_all_bytes_kind /\
    get_parser p' == LP.parse_bounded_vlbytes (U32.v min) (U32.v max) /\
    get_serializer p' == LP.serialize_bounded_vlbytes (U32.v min) (U32.v max)
  })

module B = LowStar.Buffer

val get_vlbytes
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (p: ptr (parse_vlbytes min max) inv)
: Read
    (B.buffer LP.byte & U32.t)
    True
    (fun (b, len) ->
      B.live inv.h0 b /\
      len == B.len b /\
      B.as_seq inv.h0 b `Seq.equal` FStar.Bytes.reveal (deref_spec p)
    )
    inv

let put_vlbytes_spec
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: Ghost.erased (Seq.seq LP.byte) { U32.v min <= Seq.length l /\ Seq.length l <= U32.v max })
: Tot (repr_spec unit emp (parse_vlbytes min max) (fun _ -> True) (fun _ _ vout -> vout == FStar.Bytes.hide (Ghost.reveal l)) (fun _ -> False))
=
  fun _ -> Correct ((), FStar.Bytes.hide (Ghost.reveal l))

module HST = FStar.HyperStack.ST

inline_for_extraction
let put_vlbytes_impl_t
  (inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (len: U32.t { U32.v min <= U32.v len /\ U32.v len <= U32.v max })
  (l: Ghost.erased (Seq.seq LP.byte) { Seq.length l == U32.v len })
: Tot Type
=
    (b: B.buffer LP.byte) ->
    HST.Stack unit
    (requires (fun h ->
      B.modifies inv.lwrite inv.h0 h /\
      B.live h b /\
      B.len b == len /\
      inv.lwrite `B.loc_includes` B.loc_buffer b
    ))
    (ensures (fun h _ h' ->
      B.modifies (B.loc_buffer b) h h' /\
      B.as_seq h' b `Seq.equal` Ghost.reveal l
    ))

inline_for_extraction
val put_vlbytes_impl
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (len: U32.t { U32.v min <= U32.v len /\ U32.v len <= U32.v max })
  (l: Ghost.erased (Seq.seq LP.byte) { Seq.length l == U32.v len })
  (f: put_vlbytes_impl_t inv min max len l)
: Tot (repr_impl _ _ _ _ _ _ inv (put_vlbytes_spec min max l))

inline_for_extraction
let put_vlbytes
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (len: U32.t { U32.v min <= U32.v len /\ U32.v len <= U32.v max })
  (l: Ghost.erased (Seq.seq LP.byte) { Seq.length l == U32.v len })
  (f: put_vlbytes_impl_t inv min max len l)
: Write unit emp (parse_vlbytes min max) (fun _ -> True) (fun _ _ vout -> vout == FStar.Bytes.hide (Ghost.reveal l)) inv
= EWrite?.reflect (| _, put_vlbytes_impl min max len l f |)

let rec list_map'
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f: Ghost.erased (dfst p1 -> Tot (dfst p2)))
  (f' : (
    (x: ptr p1 inv) ->
    Write unit emp p2 (fun _ -> True) (fun _ _ out -> out == Ghost.reveal f (deref_spec x)) inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: EWrite
    unit
    (parse_vllist p2 min max)
    (parse_vllist p2 min max)
    (fun _ -> True)
    (fun lin _ lout -> (lout <: list (dfst p2)) == (lin <: list (dfst p2)) `L.append` L.map (Ghost.reveal f) (deref_list_spec l))
    (fun lin -> list_size p2 lin + list_size p2 (L.map (Ghost.reveal f) (deref_list_spec l)) > U32.v max)
    inv
  (decreases (deref_list_spec l))
=
  let lin = get_state () in
  match destr_list l with
  | None ->
    L.append_l_nil (Ghost.reveal lin <: list (dfst p2))
  | Some (hd, tl) ->
    frame _ _ _ _ _ _ _ (fun _ -> f' hd);
    parse_vllist_snoc_weak p2 min max;
    L.append_assoc (Ghost.reveal lin) [Ghost.reveal f (deref_spec hd)] (L.map (Ghost.reveal f) (deref_list_spec tl));
    list_map' p1 p2 f f' min max tl

let list_map
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f: Ghost.erased (dfst p1 -> Tot (dfst p2)))
  (f' : (
    (x: ptr p1 inv) ->
    Write unit emp p2 (fun _ -> True) (fun _ _ out -> out == Ghost.reveal f (deref_spec x)) inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: EWrite
    unit
    emp
    (parse_vllist p2 min max)
    (fun _ -> True)
    (fun _ _ lout -> (lout <: list (dfst p2)) == L.map (Ghost.reveal f) (deref_list_spec l))
    (fun _ -> let len = list_size p2 (L.map (Ghost.reveal f) (deref_list_spec l)) in len < U32.v min \/ len > U32.v max)
    inv
=
  parse_vllist_nil p2 max;
  list_map' p1 p2 f f' 0ul max l;
  parse_vllist_recast p2 0ul max min max

module LowParse.Spec.Base
include LowParse.Bytes
include LowParse.Norm

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

/// parse a value of type t
///
/// - the parser can fail (currently reporting an uninformative [None])
/// - it returns the parsed value as well as the number of bytes read
///   (this is intended to be the number of bytes to advance the input pointer)
///
/// note that the type now forbids lookahead; the parser cannot depend on
/// values beyond the returned offset
///
/// these parsers are used as specifications, and thus use unrepresentable types
/// such as byte sequences and natural numbers and are always pure

[@"substitute"]
inline_for_extraction
let consumed_length (b: bytes) : Tot Type = (n: nat { n <= Seq.length b } )

inline_for_extraction
let bare_parser (t:Type) : Tot Type = (b: bytes) -> GTot (option (t * consumed_length b))

let parse
  (#t: Type)
  (p: bare_parser t)
  (input: bytes)
: GTot (option (t * consumed_length input))
= p input

(** Injectivity of parsing *)

let injective_precond
  (#t: Type)
  (p: bare_parser t)
  (b1 b2: bytes)
: GTot Type0
= Some? (parse p b1) /\
  Some? (parse p b2) /\ (
    let (Some (v1, len1)) = parse p b1 in
    let (Some (v2, len2)) = parse p b2 in
    v1 == v2
  )

let injective_precond_ext
  (#t: Type)
  (p1 p2: bare_parser t)
  (b1 b2: bytes)
: Lemma
  (requires (
    parse p2 b1 == parse p1 b1 /\
    parse p2 b2 == parse p1 b2
  ))
  (ensures (
    injective_precond p2 b1 b2 <==> injective_precond p1 b1 b2
  ))
= ()

let injective_postcond
  (#t: Type)
  (p: bare_parser t)
  (b1 b2: bytes)
: GTot Type0
= Some? (parse p b1) /\
  Some? (parse p b2) /\ (
    let (Some (v1, len1)) = parse p b1 in
    let (Some (v2, len2)) = parse p b2 in
    (len1 <: nat) == (len2 <: nat) /\
    Seq.slice b1 0 len1 == Seq.slice b2 0 len2
  )

let injective_postcond_ext
  (#t: Type)
  (p1 p2: bare_parser t)
  (b1 b2: bytes)
: Lemma
  (requires (
    parse p2 b1 == parse p1 b1 /\
    parse p2 b2 == parse p1 b2
  ))
  (ensures (
    injective_postcond p2 b1 b2 <==> injective_postcond p1 b1 b2
  ))
= ()

let injective (#t: Type) (p: bare_parser t) : GTot Type0 =
  forall (b1 b2: bytes) . {:pattern (injective_precond p b1 b2) \/ (injective_postcond p b1 b2)}
  injective_precond p b1 b2 ==>
  injective_postcond p b1 b2

let injective_ext
  (#t: Type)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes) . parse p2 b == parse p1 b
  ))
  (ensures (
    injective p2 <==> injective p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_precond_ext p1 p2 b1));
  Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_postcond_ext p1 p2 b1))
  
let no_lookahead_on_precond
  (#t: Type)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= Some? (parse f x) /\ (
    let (Some v) = parse f x in
    let (_, off) = v in
    off <= Seq.length x' /\
    Seq.slice x' 0 off == Seq.slice x 0 off
  )

let no_lookahead_on_postcond
  (#t: Type)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= Some? (parse f x) ==> (
  let (Some v) = parse f x in
  let (y, _) = v in
  Some? (parse f x') /\ (
  let (Some v') = parse f x' in
  let (y', _) = v' in
  y == y'
  ))

let no_lookahead_on
  (#t: Type)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= no_lookahead_on_precond f x x' ==> no_lookahead_on_postcond f x x'

let no_lookahead_on_ext
  (#t: Type)
  (p1 p2: bare_parser t)
  (b1 b2: bytes)
: Lemma
  (requires (
    parse p2 b1 == parse p1 b1 /\
    parse p2 b2 == parse p1 b2
  ))
  (ensures (
    no_lookahead_on p2 b1 b2 <==> no_lookahead_on p1 b1 b2
  ))
= ()

let no_lookahead
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (x x' : bytes) . {:pattern (no_lookahead_on_precond f x x') \/ (no_lookahead_on_postcond f x x')} no_lookahead_on f x x'

let no_lookahead_ext
  (#t: Type)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes) . parse p2 b == parse p1 b
  ))
  (ensures (
    no_lookahead p2 <==> no_lookahead p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (no_lookahead_on_ext p1 p2 b1))


(** A parser that always consumes all its input *)

let consumes_all
  (#t: Type)
  (p: bare_parser t)
: GTot Type0
= forall (b: bytes) . {:pattern (parse p b)} Some? (parse p b) ==> (
    let (Some (_, len)) = parse p b in
    Seq.length b == len
  )

(** Parsing data of bounded size *)

let parses_at_least
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) . {:pattern (parse f s)}
  Some? (parse f s) ==> (
    let (_, consumed) = Some?.v (parse f s) in
    sz <= (consumed <: nat)
  )

let parses_at_least_0
  (#t: Type)
  (f: bare_parser t)
: Lemma
  (parses_at_least 0 f)
= ()

let parses_at_least_le
  (sz sz': nat)
  (#t: Type)
  (f: bare_parser t)
: Lemma
  (requires (
    parses_at_least sz f /\
    sz' <= sz
  ))
  (ensures (
    parses_at_least sz' f
  ))
= ()


(** A parser that always consumes at least one byte.

A list can be serialized only if the parser for elements always
consumes at least one byte. Anyway, since we require such a parser to
have the prefix property, this is always true except for the parser
for empty data.

*)

let parses_at_most
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) . {:pattern (parse f s)}
  Some? (parse f s) ==> (
    let (_, consumed) = Some?.v (parse f s) in
    sz >= (consumed <: nat)
  )

let is_constant_size_parser
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) . {:pattern (parse f s)}
  Some? (parse f s) ==> (
    let (_, consumed) = Some?.v (parse f s) in
    sz == (consumed <: nat)
  )

let is_constant_size_parser_equiv
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: Lemma
  (is_constant_size_parser sz f <==> (parses_at_least sz f /\ parses_at_most sz f))
= ()

let is_total_constant_size_parser
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) . {:pattern (parse f s) }
  (Seq.length s < sz) == (None? (parse f s))

type parser_subkind =
  | ParserStrong
  | ParserConsumesAll

let parser_subkind_prop (k: parser_subkind) (#t: Type) (f: bare_parser t) : GTot Type0 =
  match k with
  | ParserStrong ->
    no_lookahead f
  | ParserConsumesAll ->
    consumes_all f

type parser_kind_metadata_some =
  | ParserKindMetadataTotal
  | ParserKindMetadataFail

type parser_kind_metadata_t = option parser_kind_metadata_some

inline_for_extraction
type parser_kind' = {
  parser_kind_low: nat;
  parser_kind_high: option nat;
  parser_kind_subkind: option parser_subkind;
  parser_kind_metadata: parser_kind_metadata_t;
}

let parser_kind = (x: parser_kind' {
  Some? x.parser_kind_high ==> x.parser_kind_low <= Some?.v x.parser_kind_high
})

inline_for_extraction
let strong_parser_kind (lo hi: nat) (md: parser_kind_metadata_t) : Pure parser_kind
  (requires (lo <= hi))
  (ensures (fun _ -> True))
= {
    parser_kind_low = lo;
    parser_kind_high = Some hi;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = md;
  }

inline_for_extraction
let total_constant_size_parser_kind
  (sz: nat)
: Tot parser_kind
= strong_parser_kind sz sz (Some ParserKindMetadataTotal)

let parser_always_fails (#t: Type) (f: bare_parser t) : GTot Type0 =
  forall input . {:pattern (parse f input)} parse f input == None

let parser_kind_metadata_prop (#t: Type) (k: parser_kind) (f: bare_parser t) : GTot Type0 =
  match k.parser_kind_metadata with
  | None -> True
  | Some ParserKindMetadataTotal -> k.parser_kind_high == Some k.parser_kind_low ==> is_total_constant_size_parser k.parser_kind_low f
  | Some ParserKindMetadataFail -> parser_always_fails f

let parser_kind_prop' (#t: Type) (k: parser_kind) (f: bare_parser t) : GTot Type0 =
  injective f /\
  (Some? k.parser_kind_subkind ==> parser_subkind_prop (Some?.v k.parser_kind_subkind) f) /\
  parses_at_least k.parser_kind_low f /\
  (Some? k.parser_kind_high ==> (parses_at_most (Some?.v k.parser_kind_high) f)) /\
  parser_kind_metadata_prop k f

val parser_kind_prop (#a:Type) (k:parser_kind) (f:bare_parser a) : GTot Type0

val parser_kind_prop_equiv
  (#t: Type) (k: parser_kind) (f: bare_parser t)
: Lemma
  (parser_kind_prop k f <==> parser_kind_prop' k f)

val parser_kind_prop_ext
  (#t: Type)
  (k: parser_kind)
  (f1 f2: bare_parser t)
: Lemma
  (requires (forall (input: bytes) . parse f1 input == parse f2 input))
  (ensures (parser_kind_prop k f1 <==> parser_kind_prop k f2))

[@unifier_hint_injective]
inline_for_extraction
let parser
  (k: parser_kind)
  (t: Type)
: Tot Type
= (f: bare_parser t { parser_kind_prop k f } )

inline_for_extraction
let get_parser_kind
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot parser_kind
= k

inline_for_extraction
let get_parser_type
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= t

let parser_kind_prop_intro
  (k: parser_kind)
  (#t: Type)
  (f: parser k t)
: Lemma
  (parser_kind_prop k f)
= ()

let is_strong 
  (#k:parser_kind) 
  (#t:Type) 
  (p:parser k t)
: Tot (r:bool{r ==> k.parser_kind_subkind == Some (ParserStrong)})
= k.parser_kind_subkind = Some (ParserStrong)

let is_weaker_than
  (k1 k2: parser_kind)
: GTot Type0
= (Some? k1.parser_kind_metadata ==> k1.parser_kind_metadata == k2.parser_kind_metadata) /\
  ((k1.parser_kind_metadata <> Some ParserKindMetadataFail /\ k2.parser_kind_metadata <> Some ParserKindMetadataFail) ==> (
  (Some? k1.parser_kind_subkind ==> k1.parser_kind_subkind == k2.parser_kind_subkind) /\
  k1.parser_kind_low <= k2.parser_kind_low /\
  (Some? k1.parser_kind_high ==> (
    Some? k2.parser_kind_high /\
    Some?.v k2.parser_kind_high <= Some?.v k1.parser_kind_high
  ))))
  
val is_weaker_than_correct
  (k1: parser_kind)
  (k2: parser_kind)
  (#t: Type)
  (f: bare_parser t)
: Lemma
  (requires (parser_kind_prop k2 f /\ k1 `is_weaker_than` k2))
  (ensures (parser_kind_prop k1 f))

(* AR: see bug#1349 *)
unfold let coerce_to_bare_parser (t:Type) (k2:parser_kind) (p:parser k2 t)
  :Tot (bare_parser t) = p

let weaken (k1: parser_kind) (#k2: parser_kind) (#t: Type) (p2: parser k2 t) : Pure (parser k1 t)
  (requires (k1 `is_weaker_than` k2))
  (ensures (fun _ -> True))
= let p = coerce_to_bare_parser t k2 p2 in
  is_weaker_than_correct k1 k2 p;
  p <: parser k1 t

// inline_for_extraction
let strengthen (k: parser_kind) (#t: Type) (f: bare_parser t) : Pure (parser k t)
  (requires (parser_kind_prop k f))
  (ensures (fun _ -> True))
= f

#push-options "--z3rlimit 16"

[@"opaque_to_smt"]
inline_for_extraction
let is_some
  (#t: Type)
  (x: option t)
: Tot (y: bool { y == Some? x })
= match x with
  | Some _ -> true
  | _ -> false

[@"opaque_to_smt"]
inline_for_extraction
let some_v
  (#t: Type)
  (x: option t { Some? x })
: Tot (y: t { y == Some?.v x })
= match x with
  | Some y -> y

[@"opaque_to_smt"]
inline_for_extraction
let bool_and
  (b1 b2: bool)
: Tot (y: bool { y == (b1 && b2) })
= if b1 then b2 else false

[@"opaque_to_smt"]
inline_for_extraction
let bool_or
  (b1 b2: bool)
: Tot (y: bool { y == (b1 || b2) })
= if b1 then true else b2

inline_for_extraction
let glb
  (k1 k2: parser_kind)
: Pure parser_kind
  (requires True)
  (ensures (fun k ->
    k `is_weaker_than` k1 /\
    k `is_weaker_than` k2
//    (forall k' . (k' `is_weaker_than` k1 /\ k' `is_weaker_than` k2) ==> k' `is_weaker_than` k)
  ))
= match k1.parser_kind_metadata, k2.parser_kind_metadata with
  | _, Some ParserKindMetadataFail ->
  {
    parser_kind_low = k1.parser_kind_low;
    parser_kind_high = k1.parser_kind_high;
    parser_kind_subkind = k1.parser_kind_subkind;
    parser_kind_metadata = (match k1.parser_kind_metadata with Some ParserKindMetadataFail -> Some ParserKindMetadataFail | _ -> None);
  }
  | Some ParserKindMetadataFail, _ ->
  {
    parser_kind_low = k2.parser_kind_low;
    parser_kind_high = k2.parser_kind_high;
    parser_kind_subkind = k2.parser_kind_subkind;
    parser_kind_metadata = None;
  }
  | _ ->
  {
    parser_kind_low = (if k1.parser_kind_low < k2.parser_kind_low then k1.parser_kind_low else k2.parser_kind_low);
    parser_kind_high = (
      if is_some k1.parser_kind_high `bool_and` is_some k2.parser_kind_high
      then if some_v k2.parser_kind_high < some_v k1.parser_kind_high
	   then k1.parser_kind_high
	   else k2.parser_kind_high
      else None
    );
    parser_kind_metadata = if k1.parser_kind_metadata = k2.parser_kind_metadata then k1.parser_kind_metadata else None;
    parser_kind_subkind = if k1.parser_kind_subkind = k2.parser_kind_subkind then k1.parser_kind_subkind else None
  }

#pop-options

#push-options "--warn_error -271"
let default_parser_kind : (x: parser_kind {
  forall (t: Type) (p: bare_parser t) . {:pattern (parser_kind_prop x p)}
  injective p ==> parser_kind_prop x p
})
= let aux (t:Type) (k:parser_kind) (p:bare_parser t)
    : Lemma (parser_kind_prop k p <==> parser_kind_prop' k p)
      [SMTPat ()]
    = parser_kind_prop_equiv k p in
  
  let x = {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_metadata = None;
    parser_kind_subkind = None;
  } in
  x
#pop-options

// #set-options "--max_fuel 8 --max_ifuel 8"

module L = FStar.List.Tot

let rec glb_list_of
  (#t: eqtype)
  (f: (t -> Tot parser_kind))
  (l: list t)
: Pure parser_kind
  (requires True)
  (ensures (fun k ->
    (forall kl . L.mem kl l ==> k `is_weaker_than` (f kl))  /\
    (forall k' . (Cons? l /\ (forall kl . L.mem kl l ==> k' `is_weaker_than` (f kl))) ==> k' `is_weaker_than` k)
  ))
= match l with
  | [] -> default_parser_kind
  | [k] -> f k
  | k1 :: q ->
    let k' = glb_list_of f q in
    glb (f k1) k'

#reset-options

let glb_list
  (l: list parser_kind)
: Pure parser_kind
  (requires True)
  (ensures (fun k ->
    (forall kl . {:pattern (L.mem kl l)} L.mem kl l ==> k `is_weaker_than` kl)
//    (forall k' . (Cons? l /\ (forall kl . L.mem kl l ==> k' `is_weaker_than` kl)) ==> k' `is_weaker_than` k)
  ))
= glb_list_of id l

(* Coercions *)

unfold
inline_for_extraction
let coerce
  (t2: Type)
  (#t1: Type)
  (x: t1)
: Pure t2
  (requires (t1 == t2))
  (ensures (fun _ -> True))
= (x <: t2)

let coerce'
  (t2: Type)
  (#t1: Type)
  (x: t1)
: Pure t2
  (requires (t1 == t2))
  (ensures (fun _ -> True))
= (x <: t2)

unfold
let coerce_parser
  (t2: Type)
  (#k: parser_kind)
  (#t1: Type)
  (p: parser k t1)
: Pure (parser k t2)
  (requires (t2 == t1))
  (ensures (fun _ -> True))
= p

val parse_injective
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input1: bytes)
  (input2: bytes)
: Lemma
  (requires (
    injective_precond p input1 input2
  ))
  (ensures (
    injective_postcond p input1 input2
  ))

val parse_strong_prefix
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input1: bytes)
  (input2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\ (
    match parse p input1 with
    | Some (x, consumed) ->
      consumed <= Seq.length input2 /\
      Seq.slice input1 0 consumed `Seq.equal` Seq.slice input2 0 consumed
    | _ -> False
  )))
  (ensures (
    match parse p input1 with
    | Some (x, consumed) ->
      consumed <= Seq.length input2 /\
      parse p input2 == Some (x, consumed)
    | _ -> False
  ))

(* Pure serializers *)

inline_for_extraction
let bare_serializer
  (t: Type)
: Tot Type
= t -> GTot bytes

let serializer_correct
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: bare_serializer t)
: GTot Type0
= forall (x: t) .{:pattern (parse p (f x))} parse p (f x) == Some (x, Seq.length (f x))

let serializer_correct_ext
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (f: bare_serializer t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Lemma
  (requires (t1 == t2 /\ (forall (input: bytes) . parse p1 input == parse p2 input)))
  (ensures (serializer_correct p1 f <==> serializer_correct p2 f))
= ()

let serializer_complete
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: bare_serializer t)
: GTot Type0
= forall (s: bytes) . {:pattern (parse p s)}
  Some? (parse p s) ==> (
    let (Some (x, len)) = parse p s in
    f x == Seq.slice s 0 len
  )

val serializer_correct_implies_complete
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: bare_serializer t)
: Lemma
  (requires (serializer_correct p f))
  (ensures (serializer_complete p f))

[@unifier_hint_injective]
inline_for_extraction
let serializer
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (f: bare_serializer t { serializer_correct p f } )

let mk_serializer
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: bare_serializer t)
  (prf: (
    (x: t) ->
    Lemma
    (parse p (f x) == Some (x, Seq.length (f x)))
  ))
: Tot (serializer p)
= Classical.forall_intro prf;
  f

unfold
let coerce_serializer
  (t2: Type)
  (#k: parser_kind)
  (#t1: Type)
  (#p: parser k t1)
  (s: serializer p)
  (u: unit { t2 == t1 } )
: Tot (serializer (coerce_parser t2 p))
= s

let serialize_ext
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Pure (serializer p2)
  (requires (t1 == t2 /\ (forall (input: bytes) . parse p1 input == parse p2 input)))
  (ensures (fun _ -> True))
= serializer_correct_ext p1 s1 p2;
  (s1 <: bare_serializer t2)

let serialize_ext'
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Pure (serializer p2)
  (requires (t1 == t2 /\ k1 == k2 /\ p1 == p2))
  (ensures (fun _ -> True))
= serialize_ext p1 s1 p2

let serialize
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: GTot bytes
= s x

let parse_serialize
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (parse p (serialize s x) == Some (x, Seq.length (serialize s x)))
= ()

let parsed_data_is_serialize
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: bytes)
: Lemma
  (requires (Some? (parse p x)))
  (ensures (
    let Some (y, consumed) = parse p x in
    (serialize s y `Seq.append` Seq.slice x consumed (Seq.length x)) `Seq.equal` x
  ))
= let Some (y, consumed) = parse p x in
  parse_injective p (serialize s y) x

let serializer_unique
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s1 s2: serializer p)
  (x: t)
: Lemma
  (s1 x == s2 x)
= (* need these because of patterns *)
  let _ = parse p (s1 x) in
  let _ = parse p (s2 x) in
  serializer_correct_implies_complete p s2

let serializer_injective
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s: serializer p)
  (x1 x2: t)
: Lemma
  (requires (s x1 == s x2))
  (ensures (x1 == x2))
= (* patterns, again *)
  assert (parse p (s x1) == parse p (s x2))

val serializer_parser_unique'
  (#k1: parser_kind)
  (#t: Type)
  (p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (s: bare_serializer t)
  (x: bytes)
: Lemma
  (requires (
    is_strong p1 /\
    is_strong p2 /\
    serializer_correct p1 s /\
    serializer_correct p2 s /\
    Some? (parse p1 x)
  ))
  (ensures (
    parse p1 x == parse p2 x
  ))

let serializer_parser_unique
  (#k1: parser_kind)
  (#t: Type)
  (p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (s: bare_serializer t)
  (x: bytes)
: Lemma
  (requires (
    is_strong p1 /\
    is_strong p2 /\
    serializer_correct p1 s /\
    serializer_correct p2 s
  ))
  (ensures (
    p1 x == p2 x
  ))
= if Some? (p1 x)
  then serializer_parser_unique' p1 p2 s x
  else if Some? (p2 x)
  then serializer_parser_unique' p2 p1 s x
  else ()

val serialize_length
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (let x = Seq.length (serialize s x) in
   k.parser_kind_low <= x /\ (
   match k.parser_kind_high with
   | None -> True
   | Some y -> x <= y
  ))
  [SMTPat (Seq.length (serialize s x))]

val serialize_not_fail
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (k.parser_kind_metadata <> Some ParserKindMetadataFail)
  [SMTPat (serialize s x)]

let serialize_strong_prefix
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x1 x2: t)
  (q1 q2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    serialize s x1 `Seq.append` q1 == serialize s x2 `Seq.append` q2
  ))
  (ensures (x1 == x2 /\ q1 == q2))
= parse_strong_prefix p (serialize s x1) (serialize s x1 `Seq.append` q1);
  parse_strong_prefix p (serialize s x2) (serialize s x2 `Seq.append` q2);
  Seq.lemma_append_inj (serialize s x1) q1 (serialize s x2) q2

let parse_truncate
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (x: t)
  (n: nat)
: Lemma
  (requires (
    n < Seq.length (serialize s x)
  ))
  (ensures (
    parse p (Seq.slice (serialize s x) 0 n) == None
  ))
= let sq0 = serialize s x in
  let sq1 = Seq.slice sq0 0 n in
  match parse p sq1 with
  | None -> ()
  | Some (x', consumed) ->
    parse_strong_prefix p sq1 sq0

let seq_upd_seq
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
: Pure (s_ : Seq.seq t { Seq.length s_ == Seq.length s } )
  (requires (i + Seq.length s' <= Seq.length s))
  (ensures (fun _ -> True))
= Seq.append
    (Seq.slice s 0 i)
    (Seq.append s' (Seq.slice s (i + Seq.length s') (Seq.length s)))

let index_seq_upd_seq
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
  (j: nat)
: Lemma
  (requires (i + Seq.length s' <= Seq.length s /\ j < Seq.length s))
  (ensures (
    Seq.index (seq_upd_seq s i s') j == (if i <= j && j < i + Seq.length s' then Seq.index s' (j - i) else Seq.index s j)))
= ()

let seq_upd_seq_slice
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
: Lemma
  (requires (i + Seq.length s' <= Seq.length s))
  (ensures (Seq.slice (seq_upd_seq s i s') i (i + Seq.length s') == s'))
= assert (Seq.slice (seq_upd_seq s i s') i (i + Seq.length s') `Seq.equal` s')

let seq_upd_seq_slice'
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
  (j1 j2: nat)
: Lemma
  (requires (i + Seq.length s' <= Seq.length s /\ i <= j1 /\ j1 <= j2 /\ j2 <= i + Seq.length s'))
  (ensures (Seq.slice (seq_upd_seq s i s') j1 j2 == Seq.slice s' (j1 - i) (j2 - i)))
= seq_upd_seq_slice s i s';
  Seq.slice_slice (seq_upd_seq s i s') i (i + Seq.length s') (j1 - i) (j2 - i)

let seq_upd_seq_slice_left
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
: Lemma
  (requires (i + Seq.length s' <= Seq.length s))
  (ensures (Seq.slice (seq_upd_seq s i s') 0 i == Seq.slice s 0 i))
= assert (Seq.slice (seq_upd_seq s i s') 0 i `Seq.equal` Seq.slice s 0 i)

let seq_upd_seq_slice_left'
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
  (j1 j2: nat)
: Lemma
  (requires (i + Seq.length s' <= Seq.length s /\ j1 <= j2 /\ j2 <= i))
  (ensures (Seq.slice (seq_upd_seq s i s') j1 j2 == Seq.slice s j1 j2))
= seq_upd_seq_slice_left s i s';
  Seq.slice_slice (seq_upd_seq s i s') 0 i j1 j2

let seq_upd_seq_slice_right
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
: Lemma
  (requires (i + Seq.length s' <= Seq.length s))
  (ensures (Seq.slice (seq_upd_seq s i s') (i + Seq.length s') (Seq.length s) == Seq.slice s (i + Seq.length s') (Seq.length s)))
= assert (Seq.slice (seq_upd_seq s i s') (i + Seq.length s') (Seq.length s) `Seq.equal` Seq.slice s (i + Seq.length s') (Seq.length s))

let seq_upd_seq_slice_right'
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
  (j1 j2: nat)
: Lemma
  (requires (i + Seq.length s' <= j1 /\ j1 <= j2 /\ j2 <= Seq.length s))
  (ensures (Seq.slice (seq_upd_seq s i s') j1 j2 == Seq.slice s j1 j2))
= seq_upd_seq_slice_right s i s';
  Seq.slice_slice (seq_upd_seq s i s') (i + Seq.length s') (Seq.length s) (j1 - (i + Seq.length s')) (j2 - (i + Seq.length s'))

let seq_upd_seq_empty
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
: Lemma
  (requires (i <= Seq.length s /\ Seq.length s' == 0))
  (ensures (seq_upd_seq s i s' == s))
= assert (seq_upd_seq s i s' `Seq.equal` s)

let seq_upd_seq_slice_idem
  (#t: Type)
  (s: Seq.seq t)
  (lo hi: nat)
: Lemma
  (requires (lo <= hi /\ hi <= Seq.length s))
  (ensures (seq_upd_seq s lo (Seq.slice s lo hi) == s))
= assert (seq_upd_seq s lo (Seq.slice s lo hi) `Seq.equal` s)
  
let seq_upd_seq_left
  (#t: Type)
  (s: Seq.seq t)
  (s' : Seq.seq t)
: Lemma
  (requires (Seq.length s' <= Seq.length s))
  (ensures (seq_upd_seq s 0 s' == Seq.append s' (Seq.slice s (Seq.length s') (Seq.length s))))
= assert (seq_upd_seq s 0 s' `Seq.equal` Seq.append s' (Seq.slice s (Seq.length s') (Seq.length s)))

let seq_upd_seq_right
  (#t: Type)
  (s: Seq.seq t)
  (s' : Seq.seq t)
: Lemma
  (requires (Seq.length s' <= Seq.length s))
  (ensures (seq_upd_seq s (Seq.length s - Seq.length s') s' == Seq.append (Seq.slice s 0 (Seq.length s - Seq.length s')) s'))
= assert (seq_upd_seq s (Seq.length s - Seq.length s') s' `Seq.equal` Seq.append (Seq.slice s 0 (Seq.length s - Seq.length s')) s')

let seq_upd_seq_right_to_left
  (#t: Type)
  (s1: Seq.seq t)
  (i1: nat)
  (s2: Seq.seq t)
  (i2: nat)
  (s3: Seq.seq t)
: Lemma
  (requires (i1 + Seq.length s2 <= Seq.length s1 /\ i2 + Seq.length s3 <= Seq.length s2))
  (ensures (
    seq_upd_seq s1 i1 (seq_upd_seq s2 i2 s3) == seq_upd_seq (seq_upd_seq s1 i1 s2) (i1 + i2) s3
  ))
= assert (seq_upd_seq s1 i1 (seq_upd_seq s2 i2 s3) `Seq.equal` seq_upd_seq (seq_upd_seq s1 i1 s2) (i1 + i2) s3)

let seq_upd_seq_seq_upd_seq_slice
  (#t: Type)
  (s1: Seq.seq t)
  (i1: nat)
  (hi: nat)
  (i2: nat)
  (s3: Seq.seq t)
: Lemma
  (requires (i1 <= hi /\ hi <= Seq.length s1 /\ i1 + i2 + Seq.length s3 <= hi))
  (ensures (
    seq_upd_seq s1 i1 (seq_upd_seq (Seq.slice s1 i1 hi) i2 s3) == seq_upd_seq s1 (i1 + i2) s3
  ))
= assert (seq_upd_seq s1 i1 (seq_upd_seq (Seq.slice s1 i1 hi) i2 s3) `Seq.equal` seq_upd_seq s1 (i1 + i2) s3)

let seq_upd_seq_disj_comm
  (#t: Type)
  (s: Seq.seq t)
  (i1: nat)
  (s1: Seq.seq t)
  (i2: nat)
  (s2: Seq.seq t)
: Lemma
  (requires (
    i1 + Seq.length s1 <= Seq.length s /\
    i2 + Seq.length s2 <= Seq.length s /\
    (i1 + Seq.length s1 <= i2 \/ i2 + Seq.length s2 <= i1)
  ))
  (ensures (
    seq_upd_seq (seq_upd_seq s i1 s1) i2 s2 == seq_upd_seq (seq_upd_seq s i2 s2) i1 s1
  ))
= assert (seq_upd_seq (seq_upd_seq s i1 s1) i2 s2 `Seq.equal` seq_upd_seq (seq_upd_seq s i2 s2) i1 s1)

let seq_upd_seq_seq_upd
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (x: t)
: Lemma
  (requires (i < Seq.length s))
  (ensures (Seq.upd s i x == seq_upd_seq s i (Seq.create 1 x)))
= assert (Seq.upd s i x `Seq.equal` seq_upd_seq s i (Seq.create 1 x))

let seq_append_seq_upd_seq_l
  (#t: Type)
  (s: Seq.seq t)
  (i': nat)
  (s' : Seq.seq t)
  (sl : Seq.seq t)
: Lemma
  (requires (i' + Seq.length s' <= Seq.length s))
  (ensures (
    Seq.length sl + i' <= Seq.length (sl `Seq.append` s) /\
    sl `Seq.append` seq_upd_seq s i' s' == seq_upd_seq (sl `Seq.append` s) (Seq.length sl + i') s'
  ))
= assert (sl `Seq.append` seq_upd_seq s i' s' `Seq.equal` seq_upd_seq (sl `Seq.append` s) (Seq.length sl + i') s')

let seq_append_seq_upd_seq_r
  (#t: Type)
  (s: Seq.seq t)
  (i': nat)
  (s' : Seq.seq t)
  (sr : Seq.seq t)
: Lemma
  (requires (i' + Seq.length s' <= Seq.length s))
  (ensures (
    i' <= Seq.length (s `Seq.append` sr) /\
    seq_upd_seq s i' s' `Seq.append` sr == seq_upd_seq (s `Seq.append` sr) i' s'
  ))
= assert ((seq_upd_seq s i' s' `Seq.append` sr) `Seq.equal` seq_upd_seq (s `Seq.append` sr) i' s')

let seq_upd_bw_seq
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
  (s' : Seq.seq t)
: Pure (s_ : Seq.seq t { Seq.length s_ == Seq.length s } )
  (requires (i + Seq.length s' <= Seq.length s))
  (ensures (fun _ -> True))
= seq_upd_seq s (Seq.length s - i - Seq.length s') s'

let seq_upd_bw_seq_right
  (#t: Type)
  (s: Seq.seq t)
  (s' : Seq.seq t)
: Lemma
  (requires (Seq.length s' <= Seq.length s))
  (ensures (seq_upd_bw_seq s 0 s' == Seq.append (Seq.slice s 0 (Seq.length s - Seq.length s')) s'))
= seq_upd_seq_right s s'

(* for tagged unions *)

inline_for_extraction
let refine_with_tag (#tag_t: Type) (#data_t: Type) (tag_of_data: (data_t -> GTot tag_t)) (x: tag_t) : Tot Type =
  (y: data_t { tag_of_data y == x } )

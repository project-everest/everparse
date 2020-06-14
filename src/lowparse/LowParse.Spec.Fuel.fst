module LowParse.Spec.Fuel
include LowParse.Spec.Base

module Seq = FStar.Seq

let injective_fuel (fuel: nat) (#t: Type) (p: bare_parser t) : GTot Type0 =
  forall (b1 b2: bytes) . {:pattern (injective_precond p b1 b2) \/ (injective_postcond p b1 b2)}
  (injective_precond p b1 b2 /\ Seq.length b1 < fuel /\ Seq.length b2 < fuel) ==>
  injective_postcond p b1 b2

let no_lookahead_fuel
  (fuel: nat)
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (x x' : bytes) . {:pattern (no_lookahead_on_precond f x x') \/ (no_lookahead_on_postcond f x x')} (Seq.length x < fuel /\ Seq.length x' < fuel) ==> no_lookahead_on f x x'

let consumes_all_fuel
  (fuel: nat)
  (#t: Type)
  (p: bare_parser t)
: GTot Type0
= forall (b: bytes { Seq.length b < fuel }) . {:pattern (parse p b)} Some? (parse p b) ==> (
    let (Some (_, len)) = parse p b in
    Seq.length b == len
  )

let parser_subkind_prop_fuel (fuel: nat) (k: parser_subkind) (#t: Type) (f: bare_parser t) : GTot Type0 =
  match k with
  | ParserStrong ->
    no_lookahead_fuel fuel f
  | ParserConsumesAll ->
    consumes_all_fuel fuel f

let parses_at_least_fuel
  (fuel: nat)
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes { Seq.length s < fuel }) . {:pattern (parse f s)}
  Some? (parse f s) ==> (
    let (_, consumed) = Some?.v (parse f s) in
    sz <= (consumed <: nat)
  )

let parses_at_most_fuel
  (fuel: nat)
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes { Seq.length s < fuel }) . {:pattern (parse f s)}
  Some? (parse f s) ==> (
    let (_, consumed) = Some?.v (parse f s) in
    sz >= (consumed <: nat)
  )

let is_total_constant_size_parser_fuel
  (fuel: nat)
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes { Seq.length s < fuel }) . {:pattern (parse f s) }
  (Seq.length s < sz) == (None? (parse f s))

let parser_always_fails_fuel (fuel: nat) (#t: Type) (f: bare_parser t) : GTot Type0 =
  forall (input: bytes { Seq.length input < fuel }) . {:pattern (parse f input)} parse f input == None

let parser_kind_metadata_prop_fuel (fuel: nat) (#t: Type) (k: parser_kind) (f: bare_parser t) : GTot Type0 =
  match k.parser_kind_metadata with
  | None -> True
  | Some ParserKindMetadataTotal -> k.parser_kind_high == Some k.parser_kind_low ==> is_total_constant_size_parser_fuel fuel k.parser_kind_low f
  | Some ParserKindMetadataFail -> parser_always_fails_fuel fuel f

let parser_kind_prop_fuel (fuel: nat) (#t: Type) (k: parser_kind) (f: bare_parser t) : GTot Type0 =
  injective_fuel fuel f /\
  (Some? k.parser_kind_subkind ==> parser_subkind_prop_fuel fuel (Some?.v k.parser_kind_subkind) f) /\
  parses_at_least_fuel fuel k.parser_kind_low f /\
  (Some? k.parser_kind_high ==> (parses_at_most_fuel fuel (Some?.v k.parser_kind_high) f)) /\
  parser_kind_metadata_prop_fuel fuel k f

unfold
let parser_kind_prop' (#t: Type) (k: parser_kind) (f: bare_parser t) : GTot Type0 =
  injective f /\
  (Some? k.parser_kind_subkind ==> parser_subkind_prop (Some?.v k.parser_kind_subkind) f) /\
  parses_at_least k.parser_kind_low f /\
  (Some? k.parser_kind_high ==> (parses_at_most (Some?.v k.parser_kind_high) f)) /\
  parser_kind_metadata_prop k f

let injective_fuel_correct
  (#t: Type) (f: bare_parser t)
: Lemma
  (requires (forall fuel . injective_fuel fuel f))
  (ensures (injective f))
= assert (forall x y . injective_precond f x y ==> injective_fuel (Seq.length x + Seq.length y + 1) f)

let parses_at_least_fuel_correct
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: Lemma
  (requires (forall fuel . parses_at_least_fuel fuel sz f))
  (ensures (parses_at_least sz f))
= assert (forall x . Some? (parse f x) ==> parses_at_least_fuel (Seq.length x + 1) sz f)

let parses_at_most_fuel_correct
  (sz: nat)
  (#t: Type)
  (f: bare_parser t)
: Lemma
  (requires (forall fuel . parses_at_most_fuel fuel sz f))
  (ensures (parses_at_most sz f))
= assert (forall x . Some? (parse f x) ==> parses_at_most_fuel (Seq.length x + 1) sz f)

let parser_subkind_prop_fuel_correct
  (k: parser_subkind) (#t: Type) (f: bare_parser t)
: Lemma
  (requires (forall fuel . parser_subkind_prop_fuel fuel k f))
  (ensures (parser_subkind_prop k f))
= assert (forall x y . no_lookahead_on_precond f x y ==> parser_subkind_prop_fuel (Seq.length x + Seq.length y + 1) k f);
  assert (forall x . Some? (parse f x) ==> parser_subkind_prop_fuel (Seq.length x + 1) k f)

let parser_kind_metadata_prop_fuel_correct
  (#t: Type) (k: parser_kind) (f: bare_parser t)
: Lemma
  (requires (forall fuel . parser_kind_metadata_prop_fuel fuel k f))
  (ensures (parser_kind_metadata_prop k f))
= assert (forall x . let p =  (parse f x) in parser_kind_metadata_prop_fuel (Seq.length x + 1) k f)

let parser_kind_prop_fuel_correct
  (#t: Type) (k: parser_kind) (f: bare_parser t)
: Lemma
  (requires (forall fuel . parser_kind_prop_fuel fuel k f))
  (ensures (parser_kind_prop' k f))
= injective_fuel_correct f;
  begin match k.parser_kind_subkind with
  | None -> ()
  | Some k' -> parser_subkind_prop_fuel_correct k' f
  end;
  parses_at_least_fuel_correct k.parser_kind_low f;
  begin match k.parser_kind_high with
  | None -> ()
  | Some max -> parses_at_most_fuel_correct max f
  end;
  parser_kind_metadata_prop_fuel_correct k f

let parser_kind_prop_fuel_complete'
  (fuel: nat) (#t: Type) (k: parser_kind) (f: bare_parser t)
: Lemma
  (requires (parser_kind_prop' k f))
  (ensures (parser_kind_prop_fuel fuel k f))
= ()

let parser_kind_prop_fuel_complete
  (fuel: nat) (#t: Type) (k: parser_kind) (f: bare_parser t)
: Lemma
  (requires (parser_kind_prop k f))
  (ensures (parser_kind_prop_fuel fuel k f))
= parser_kind_prop_equiv k f

let no_lookahead_fuel_ext
  (fuel: nat)
  (#t: Type)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes { Seq.length b < fuel }) . parse p2 b == parse p1 b
  ))
  (ensures (
    no_lookahead_fuel fuel p2 <==> no_lookahead_fuel fuel p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (no_lookahead_on_ext p1 p2 b1))

let injective_fuel_ext
  (fuel: nat)
  (#t: Type)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes { Seq.length b < fuel }) . parse p2 b == parse p1 b
  ))
  (ensures (
    injective_fuel fuel p2 <==> injective_fuel fuel p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_precond_ext p1 p2 b1));
  Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_postcond_ext p1 p2 b1))

let parser_kind_prop_fuel_ext
  (fuel: nat)
  (#t: Type)
  (k: parser_kind)
  (f1 f2: bare_parser t)
: Lemma
  (requires (forall (input: bytes { Seq.length input < fuel }) . parse f1 input == parse f2 input))
  (ensures (parser_kind_prop_fuel fuel k f1 <==> parser_kind_prop_fuel fuel k f2))
= no_lookahead_fuel_ext fuel f1 f2;
  injective_fuel_ext fuel f1 f2

let close_by_fuel
  (#t: Type)
  (f: (nat -> Tot (bare_parser t)))
  (closure: ((b: bytes) -> GTot (n: nat { Seq.length b < n })))
: Tot (bare_parser t)
= fun x -> f (closure x) x

let close_by_fuel_correct
  (#t: Type)
  (k: parser_kind)
  (f: (nat -> Tot (bare_parser t)))
  (closure: ((b: bytes) -> GTot (n: nat { Seq.length b < n })))
  (f_ext: (
    (fuel: nat) ->
    (b: bytes { Seq.length b < fuel }) ->
    Lemma
    (f fuel b == f (closure b) b)
  ))
  (f_prop: (
    (fuel: nat) ->
    Lemma
    (parser_kind_prop_fuel fuel k (f fuel))
  ))
: Lemma
  (parser_kind_prop k (close_by_fuel f closure))
= let prf
    (fuel: nat)
  : Lemma
    (parser_kind_prop_fuel fuel k (close_by_fuel f closure))
  = f_prop fuel;
    let g
      (b: bytes { Seq.length b < fuel })
    : Lemma
      (parse (close_by_fuel f closure) b == parse (f fuel) b)
    = f_ext fuel b
    in
    Classical.forall_intro g;
    parser_kind_prop_fuel_ext fuel k (close_by_fuel f closure) (f fuel)
  in
  Classical.forall_intro prf;
  parser_kind_prop_fuel_correct k (close_by_fuel f closure);
  parser_kind_prop_equiv k (close_by_fuel f closure)

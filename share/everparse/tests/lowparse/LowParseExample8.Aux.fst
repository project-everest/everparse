module LowParseExample8.Aux

(* Spec + sum definition for Example8, as a regular F* module.
   Ported from tests/lowparse/LowParseExample8.fst *)

module LP = LowParse.Spec.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16

include LowParse.Spec.Int
include LowParse.Spec.Combinators
include LowParse.Spec.Enum
include LowParse.Spec.Tac.Enum
include LowParse.Spec.Sum
include LowParse.Spec.Tac.Sum

module L = FStar.List.Tot

type k_t : eqtype =
| Ka
| Kb

noeq
type t' =
| Ta of U8.t
| Tb of U16.t

inline_for_extraction
let key (x: t') : Tot k_t = match x with
| Ta _ -> Ka
| Tb _ -> Kb

inline_for_extraction
let t (k: k_t) : Tot Type = (x: t' { key x == k } )

inline_for_extraction
let u8 : eqtype = U8.t

inline_for_extraction
let k_enum : enum k_t u8 =
  [@inline_let]
  let e : list (k_t & U8.t) = [
    Ka, 18uy;
    Kb, 42uy;
  ]
  in
  [@inline_let]
  let _ : squash (L.noRepeats (list_map fst e) /\ L.noRepeats (list_map snd e)) =
    assert_norm (L.noRepeats (list_map fst e));
    assert_norm (L.noRepeats (list_map snd e))
  in
  e

inline_for_extraction
unfold
let case_as_case_enum
  (x: k_t)
: Tot (y: enum_key k_enum { y == x } )
= match x with
  | Ka -> [@inline_let] let _ = assert_norm (list_mem Ka (list_map fst k_enum)) in Ka
  | Kb -> [@inline_let] let _ = assert_norm (list_mem Ka (list_map fst k_enum)) in Kb

inline_for_extraction
let cases_of_t
  (x: t')
: Tot (y: enum_key k_enum { y == key x } )
= match x with
  | Ta _ -> case_as_case_enum Ka
  | Tb _ -> case_as_case_enum Kb

inline_for_extraction
let type_of_case
  (x: k_t)
: Tot Type0
= match x with
  | Ka -> U8.t
  | Kb -> U16.t

unfold
inline_for_extraction
let to_type_of_case
  (x: k_t)
  (#x' : k_t)
  (y: type_of_case x')
: Pure (norm [delta_only [(`%type_of_case)]; iota] (type_of_case x))
  (requires (x == x'))
  (ensures (fun y' -> y' == y))
= [@inline_let]
  let _ = norm_spec [delta_only [(`%type_of_case)] ; iota] (type_of_case x) in
  y

unfold
inline_for_extraction
let to_refine_with_tag (k: enum_key k_enum) (x: t') : Pure (refine_with_tag cases_of_t k)
  (requires (
    norm [delta; iota; zeta] (cases_of_t x) == k
  ))
  (ensures (fun y -> y == x))
= [@inline_let]
  let _ = norm_spec [delta; iota; zeta] (cases_of_t x) in
  x

inline_for_extraction
let synth_case
  (x: enum_key k_enum)
  (y: type_of_case x)
: Tot (refine_with_tag cases_of_t x)
= match x with
  | Ka -> to_refine_with_tag x (Ta (to_type_of_case Ka y))
  | Kb -> to_refine_with_tag x (Tb (to_type_of_case Kb y))

unfold
inline_for_extraction
let from_type_of_case
  (#x' : k_t)
  (x: k_t)
  (y: norm [delta_only [(`%type_of_case)]; iota] (type_of_case x))
: Pure (type_of_case x')
  (requires (x == x'))
  (ensures (fun y' -> y' == y))
= [@inline_let]
  let _ = norm_spec [delta_only [(`%type_of_case)] ; iota] (type_of_case x) in
  y

let synth_case_recip_pre
  (k: enum_key k_enum)
  (x: refine_with_tag cases_of_t k)
: GTot bool
= match k with
  | Ka -> (Ta? x)
  | Kb -> (Tb? x)

module T = LowParse.TacLib

let synth_case_recip_pre_intro1
  (k: enum_key k_enum)
: Tot (
  (x: t') ->
  Tot (squash (k == cases_of_t x ==> synth_case_recip_pre k x == true)))
= _ by (synth_case_recip_pre_tac ())

let synth_case_recip_pre_intro
  (k: enum_key k_enum)
  (x: refine_with_tag cases_of_t k)
: Lemma (synth_case_recip_pre k x == true)
= norm_spec [delta; iota] (synth_case_recip_pre k x);
  assert (k == cases_of_t x);
  let _ = synth_case_recip_pre_intro1 k x in
  assert (k == cases_of_t x ==> synth_case_recip_pre k x == true);
  ()

inline_for_extraction
let synth_case_recip
  (k: enum_key k_enum)
  (x: refine_with_tag cases_of_t k)
: Tot (type_of_case k)
= match k with
  | Ka -> [@inline_let] let _ = synth_case_recip_pre_intro Ka x in (match x with Ta y -> (from_type_of_case Ka y))
  | Kb -> [@inline_let] let _ = synth_case_recip_pre_intro Kb x in (match x with Tb y -> (from_type_of_case Kb y))

inline_for_extraction
let t_sum : sum
= make_sum' k_enum cases_of_t type_of_case synth_case synth_case_recip
    (_ by (make_sum_synth_case_recip_synth_case_tac ()))
    (_ by (synth_case_synth_case_recip_tac ()))

let parse_cases
  (x: sum_key t_sum)
: Tot (k: parser_kind & parser k (type_of_case x))
= match x with
  | Ka -> (| _, parse_u8 |)
  | Kb -> (| _, parse_u16 |)

inline_for_extraction
let parse_t_kind : LP.parser_kind = LP.strong_parser_kind 1 2 (Some LP.ParserKindMetadataTotal)

let _ : squash (parse_t_kind == weaken_parse_cases_kind t_sum parse_cases) = _ by (T.trefl ())

let t_eq_lemma (k: k_t) : Lemma (t k == sum_cases t_sum (case_as_case_enum k)) [SMTPat (t k)] =
  match k with
  | Ka -> assert_norm (t Ka == sum_cases t_sum (case_as_case_enum Ka))
  | Kb -> assert_norm (t Kb == sum_cases t_sum (case_as_case_enum Kb))

let parse_t (k: k_t) : LP.parser parse_t_kind (t k) = parse_sum_cases t_sum parse_cases (case_as_case_enum k)

let serialize_cases (x: sum_key t_sum) : Tot (LP.serializer (dsnd (parse_cases x))) =
  match x with
  | Ka -> (serialize_u8 <: LP.serializer (dsnd (parse_cases x)))
  | Kb -> (serialize_u16 <: LP.serializer (dsnd (parse_cases x)))

let serialize_t (k: k_t) : LP.serializer (parse_t k) = serialize_sum_cases t_sum parse_cases serialize_cases (case_as_case_enum k)

module LowParseExample.Aux

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot

let parse_case_B_filter
  (x: U16.t)
: GTot bool
= U16.v x > 0

inline_for_extraction
let case_B = (x: U16.t { parse_case_B_filter x } )

noeq
type t =
  | A of (U8.t * U8.t)
  | B of case_B
  | V2 of U16.t
  | V3 of U16.t
  | V4 of  U16.t
  | V5 of U16.t
  | V6 of U16.t
  | V7 of U16.t
  | V8 of U16.t
  | V9 of U16.t
  | W2 of U16.t
  | W3 of U16.t
  | W4 of  U16.t
  | W5 of U16.t
  | W6 of U16.t
  | W7 of U16.t
  | W8 of U16.t
  | W9 of U16.t

type cases : eqtype =
  | Case_A
  | Case_B
  | Case_V2
  | Case_V3
  | Case_V4
  | Case_V5
  | Case_V6
  | Case_V7
  | Case_V8
  | Case_V9
  | Case_W2
  | Case_W3
  | Case_W4
  | Case_W5
  | Case_W6
  | Case_W7
  | Case_W8
  | Case_W9

inline_for_extraction
let u8 : eqtype = U8.t

inline_for_extraction
let case_enum : LP.enum cases u8 =
  [@inline_let]
  let e : list (cases * U8.t) = [
    Case_A, 18uy;
    Case_B, 42uy;
    Case_V2, 71uy;
    Case_V3, 72uy;
    Case_V4, 73uy;
    Case_V5, 74uy;
    Case_V6, 75uy;
    Case_V7, 76uy;
    Case_V8, 77uy;
    Case_V9, 78uy;
    Case_W2, 81uy;
    Case_W3, 82uy;
    Case_W4, 83uy;
    Case_W5, 84uy;
    Case_W6, 85uy;
    Case_W7, 86uy;
    Case_W8, 87uy;
    Case_W9, 88uy;
  ]
  in
  [@inline_let]
  let _ : squash (L.noRepeats (LP.list_map fst e) /\ L.noRepeats (LP.list_map snd e)) =
    assert_norm (L.noRepeats (LP.list_map fst e));
    assert_norm (L.noRepeats (LP.list_map snd e))
  in
  e

// #reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2 --query_stats --z3refresh"

// #set-options "--debug_level SMTQuery --debug LowParseExample.Aux --print_full_names"

// NOTE: this coercion is necessary otherwise cases_of_t does not typecheck for large sum types. In fact, the return value of cases_of_t is LP.enum_key case_enum instead of cases (i.e. the enum is not necessarily total)

inline_for_extraction
unfold
let case_as_case_enum
  (x: cases { norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst case_enum)) == true } )
: Tot (LP.enum_key case_enum)
= [@inline_let]
  let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst case_enum)) in
  x

inline_for_extraction
let cases_of_t
  (x: t)
: Tot (LP.enum_key case_enum)
= match x with
  | A _ -> case_as_case_enum Case_A
  | B _ -> case_as_case_enum Case_B
  | V2 _ -> case_as_case_enum Case_V2
  | V3 _ -> case_as_case_enum Case_V3
  | V4 _ -> case_as_case_enum Case_V4
  | V5 _ -> case_as_case_enum Case_V5
  | V6 _ -> case_as_case_enum Case_V6
  | V7 _ -> case_as_case_enum Case_V7
  | V8 _ -> case_as_case_enum Case_V8
  | V9 _ -> case_as_case_enum Case_V9
  | W2 _ -> case_as_case_enum Case_W2
  | W3 _ -> case_as_case_enum Case_W3
  | W4 _ -> case_as_case_enum Case_W4
  | W5 _ -> case_as_case_enum Case_W5
  | W6 _ -> case_as_case_enum Case_W6
  | W7 _ -> case_as_case_enum Case_W7
  | W8 _ -> case_as_case_enum Case_W8
  | W9 _ -> case_as_case_enum Case_W9

inline_for_extraction
let type_of_case
  (x: cases)
: Tot Type0
= match x with
  | Case_A -> U8.t * U8.t
  | Case_B -> case_B
  | Case_V2 -> U16.t
  | Case_V3 -> U16.t
  | Case_V4 -> U16.t
  | Case_V5 -> U16.t
  | Case_V6 -> U16.t
  | Case_V7 -> U16.t
  | Case_V8 -> U16.t
  | Case_V9 -> U16.t
  | Case_W2 -> U16.t
  | Case_W3 -> U16.t
  | Case_W4 -> U16.t
  | Case_W5 -> U16.t
  | Case_W6 -> U16.t
  | Case_W7 -> U16.t
  | Case_W8 -> U16.t
  | Case_W9 -> U16.t

// BEGIN typechecking performance improvements thanks to normalization and tactics

unfold
inline_for_extraction
let to_type_of_case
  (x: cases)
  (#x' : cases)
  (y: type_of_case x')
: Pure (norm [delta_only [(`%type_of_case)]; iota] (type_of_case x))
  (requires (x == x'))
  (ensures (fun y' -> y' == y))
= [@inline_let]
  let _ = norm_spec [delta_only [(`%type_of_case)] ; iota] (type_of_case x) in
  y

unfold
inline_for_extraction
let to_refine_with_tag (k: LP.enum_key case_enum) (x: t) : Pure (LP.refine_with_tag cases_of_t k)
  (requires (
    norm [delta; iota; zeta] (cases_of_t x) == k
  ))
  (ensures (fun y -> y == x))
= [@inline_let]
  let _ = norm_spec [delta; iota; zeta] (cases_of_t x) in
  x

inline_for_extraction
let synth_case
  (x: LP.enum_key case_enum)
  (y: type_of_case x)
: Tot (LP.refine_with_tag cases_of_t x)
= match x with
  | Case_A -> to_refine_with_tag x (A (to_type_of_case Case_A y))      | Case_A -> A y
  | Case_B -> to_refine_with_tag x (B (to_type_of_case Case_B y))
  | Case_V2 -> to_refine_with_tag x (V2 (to_type_of_case Case_V2 y))
  | Case_V3 -> to_refine_with_tag x (V3 (to_type_of_case Case_V3 y))
  | Case_V4 -> to_refine_with_tag x (V4 (to_type_of_case Case_V4 y))
  | Case_V5 -> to_refine_with_tag x (V5 (to_type_of_case Case_V5 y))
  | Case_V6 -> to_refine_with_tag x (V6 (to_type_of_case Case_V6 y))
  | Case_V7 -> to_refine_with_tag x (V7 (to_type_of_case Case_V7 y))
  | Case_V8 -> to_refine_with_tag x (V8 (to_type_of_case Case_V8 y))
  | Case_V9 -> to_refine_with_tag x (V9 (to_type_of_case Case_V9 y))
  | Case_W2 -> to_refine_with_tag x (W2 (to_type_of_case Case_W2 y))
  | Case_W3 -> to_refine_with_tag x (W3 (to_type_of_case Case_W3 y))
  | Case_W4 -> to_refine_with_tag x (W4 (to_type_of_case Case_W4 y))
  | Case_W5 -> to_refine_with_tag x (W5 (to_type_of_case Case_W5 y))
  | Case_W6 -> to_refine_with_tag x (W6 (to_type_of_case Case_W6 y))
  | Case_W7 -> to_refine_with_tag x (W7 (to_type_of_case Case_W7 y))
  | Case_W8 -> to_refine_with_tag x (W8 (to_type_of_case Case_W8 y))
  | Case_W9 -> to_refine_with_tag x (W9 (to_type_of_case Case_W9 y))


unfold
inline_for_extraction
let from_type_of_case
  (#x' : cases)
  (x: cases)
  (y: norm [delta_only [(`%type_of_case)]; iota] (type_of_case x))
: Pure (type_of_case x')
  (requires (x == x'))
  (ensures (fun y' -> y' == y))
= [@inline_let]
  let _ = norm_spec [delta_only [(`%type_of_case)] ; iota] (type_of_case x) in
  y

let synth_case_recip_pre
  (k: LP.enum_key case_enum)
  (x: LP.refine_with_tag cases_of_t k)
: GTot bool
= match k with
  | Case_A -> (A? x)
  | Case_B -> (B? x)
  | Case_V2 -> (V2? x)
  | Case_V3 -> (V3? x)
  | Case_V4 -> (V4? x)
  | Case_V5 -> (V5? x)
  | Case_V6 -> (V6? x)
  | Case_V7 -> (V7? x)
  | Case_V8 -> (V8? x)
  | Case_V9 -> (V9? x)
  | Case_W2 -> (W2? x)
  | Case_W3 -> (W3? x)
  | Case_W4 -> (W4? x)
  | Case_W5 -> (W5? x)
  | Case_W6 -> (W6? x)
  | Case_W7 -> (W7? x)
  | Case_W8 -> (W8? x)
  | Case_W9 -> (W9? x)

module T = LowParse.TacLib

let synth_case_recip_pre_intro1
  (k: LP.enum_key case_enum)
: Tot (
  (x: t) ->
  Tot (squash (k == cases_of_t x ==> synth_case_recip_pre k x == true)))
= _ by (LP.synth_case_recip_pre_tac ())

let synth_case_recip_pre_intro
  (k: LP.enum_key case_enum)
  (x: LP.refine_with_tag cases_of_t k)
: Lemma (synth_case_recip_pre k x == true)
= norm_spec [delta; iota] (synth_case_recip_pre k x);
  assert (k == cases_of_t x);
  let _ = synth_case_recip_pre_intro1 k x in
  assert (k == cases_of_t x ==> synth_case_recip_pre k x == true); // FIXME: this is a BUG in F*, this assert should not be needed
  ()

inline_for_extraction
let synth_case_recip
  (k: LP.enum_key case_enum)
  (x: LP.refine_with_tag cases_of_t k)
: Tot (type_of_case k)
= match k with
  | Case_A -> [@inline_let] let _ = synth_case_recip_pre_intro Case_A x in (match x with A y -> (from_type_of_case Case_A y))
  | Case_B -> [@inline_let] let _ = synth_case_recip_pre_intro Case_B x in (match x with B y -> (from_type_of_case Case_B y))
  | Case_V2 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_V2 x in (match x with V2 y -> (from_type_of_case Case_V2 y))
  | Case_V3 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_V3 x in (match x with V3 y -> (from_type_of_case Case_V3 y))
  | Case_V4 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_V4 x in (match x with V4 y -> (from_type_of_case Case_V4 y))
  | Case_V5 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_V5 x in (match x with V5 y -> (from_type_of_case Case_V5 y))
  | Case_V6 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_V6 x in (match x with V6 y -> (from_type_of_case Case_V6 y))
  | Case_V7 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_V7 x in (match x with V7 y -> (from_type_of_case Case_V7 y))
  | Case_V8 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_V8 x in (match x with V8 y -> (from_type_of_case Case_V8 y))
  | Case_V9 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_V9 x in (match x with V9 y -> (from_type_of_case Case_V9 y))
  | Case_W2 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_W2 x in (match x with W2 y -> (from_type_of_case Case_W2 y))
  | Case_W3 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_W3 x in (match x with W3 y -> (from_type_of_case Case_W3 y))
  | Case_W4 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_W4 x in (match x with W4 y -> (from_type_of_case Case_W4 y))
  | Case_W5 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_W5 x in (match x with W5 y -> (from_type_of_case Case_W5 y))
  | Case_W6 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_W6 x in (match x with W6 y -> (from_type_of_case Case_W6 y))
  | Case_W7 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_W7 x in (match x with W7 y -> (from_type_of_case Case_W7 y))
  | Case_W8 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_W8 x in (match x with W8 y -> (from_type_of_case Case_W8 y))
  | Case_W9 -> [@inline_let] let _ = synth_case_recip_pre_intro Case_W9 x in (match x with W9 y -> (from_type_of_case Case_W9 y))


// END typechecking performance improvements

inline_for_extraction
let t_sum : LP.sum
= LP.make_sum' case_enum cases_of_t type_of_case synth_case synth_case_recip
    (_ by (LP.make_sum_synth_case_recip_synth_case_tac ()))
    (_ by (LP.synth_case_synth_case_recip_tac ()))

let parse_case_B : LP.parser _ case_B =
  LP.parse_filter LP.parse_u16 parse_case_B_filter

let parse_cases
  (x: LP.sum_key t_sum)
: Tot (k: LP.parser_kind & LP.parser k (type_of_case x))
= match x with
  | Case_A -> (| _, LP.parse_u8 `LP.nondep_then` LP.parse_u8 |)
  | Case_B -> (| _, parse_case_B |)
  | _ -> (| _, LP.parse_u16 |)

let parse_t : LP.parser _ t =
  LP.parse_sum t_sum LP.parse_u8 parse_cases

(*
let parse32_case_B : LP.parser32 parse_case_B =
  LP.parse32_filter LP.parse32_u16 parse_case_B_filter (fun x -> U16.gt x 0us)

inline_for_extraction
let parse32_cases
  (x: LP.sum_key t_sum)
: Tot (LP.parser32 (dsnd (parse_cases x)))
= match x with
  | Case_A -> (LP.parse32_nondep_then LP.parse32_u8 LP.parse32_u8 <: LP.parser32 (dsnd (parse_cases x)))
  | Case_B -> (parse32_case_B <: LP.parser32 (dsnd (parse_cases x)))
  | _ -> (LP.parse32_u16 <: LP.parser32 (dsnd (parse_cases x)))

inline_for_extraction
let parse32_case_destr
: (LP.enum_destr_t (option (t * FStar.UInt32.t)) case_enum)
= _ by (LP.enum_destr_tac case_enum)

let parse32_case_enum
: LP.parser32 (LP.parse_enum_key LP.parse_u8 case_enum)
= _ by (LP.parse32_enum_key_tac LP.parse32_u8 case_enum ())

let parse32_t
: LP.parser32 parse_t
= LP.parse32_sum t_sum _ parse32_case_enum _ parse32_cases parse32_case_destr
*)

let serialize_case_B : LP.serializer parse_case_B =
  LP.serialize_filter LP.serialize_u16 parse_case_B_filter

let serialize_cases
  (x: LP.sum_key t_sum)
: Tot (LP.serializer (dsnd (parse_cases x)))
= match x with
  | Case_A -> (LP.serialize_nondep_then _ LP.serialize_u8 () _ LP.serialize_u8 <: LP.serializer (dsnd (parse_cases x)))
  | Case_B -> (serialize_case_B <: LP.serializer (dsnd (parse_cases x)))
  | _ -> (LP.serialize_u16 <: LP.serializer (dsnd (parse_cases x)))

let serialize_t : LP.serializer parse_t =
  LP.serialize_sum t_sum LP.serialize_u8 serialize_cases

// inline_for_extraction
let serialize32_case_B: LP.serializer32 serialize_case_B =
  LP.serialize32_filter LP.serialize32_u16 parse_case_B_filter

#push-options "--z3rlimit 20"

inline_for_extraction
let serialize32_cases
  (x: LP.sum_key t_sum)
: Tot (LP.serializer32 (serialize_cases x))
= match x with
  | Case_A -> (LP.serialize32_nondep_then LP.serialize32_u8 () LP.serialize32_u8 () <: LP.serializer32 (serialize_cases x))
  | Case_B -> (serialize32_case_B <: LP.serializer32 (serialize_cases x))
  | _ -> (LP.serialize32_u16 <: LP.serializer32 (serialize_cases x))

#pop-options

// inline_for_extraction
let serialize32_key : LP.serializer32 (LP.serialize_enum_key _ LP.serialize_u8 case_enum) =
  _ by (LP.serialize32_enum_key_gen_tac LP.serialize32_u8 case_enum ())

inline_for_extraction
let serialize32_destr : LP.dep_enum_destr case_enum (LP.serialize32_sum_destr_codom t_sum) =
  (_ by (LP.dep_enum_destr_tac ()))

let serialize32_t : LP.serializer32 serialize_t =
  [@inline_let]
  let _ =  assert_norm (LP.serializer32_sum_gen_precond (LP.get_parser_kind LP.parse_u8) (LP.weaken_parse_cases_kind t_sum parse_cases)) in
  LP.serialize32_sum
    t_sum
    _
    serialize32_key
    _
    serialize32_cases
    serialize32_destr
    ()

module LL = LowParse.Low

module U32 = FStar.UInt32

let validate_case_B
: LL.validator parse_case_B
= LL.validate_filter (LL.validate_u16 ()) LL.read_u16 parse_case_B_filter (fun x -> x `U16.gt` 0us)

inline_for_extraction
let validate_cases 
  (x: LP.enum_key case_enum)
: Tot (LL.validator (dsnd (parse_cases x)))
= match x with
  | Case_B -> (validate_case_B <: LL.validator (dsnd (parse_cases x)))
  | Case_A -> (((LL.validate_u8 ()) `LL.validate_nondep_then` (LL.validate_u8 ())) <: LL.validator (dsnd (parse_cases x)))
  | _ -> (LL.validate_u16 () <: LL.validator (dsnd (parse_cases x)))

let validate_t
: LL.validator parse_t
= LL.validate_sum t_sum (LL.validate_u8 ()) LL.read_u8 _ validate_cases (_ by (LP.dep_maybe_enum_destr_t_tac ()))

(*
// inline_for_extraction
let size32_key : LP.size32 (LP.serialize_enum_key _ LP.serialize_u8 case_enum) =
  _ by (LP.size32_enum_key_gen_tac LP.size32_u8 case_enum ())

// inline_for_extraction
let size32_case_B: LP.size32 serialize_case_B =
  LP.size32_filter LP.size32_u16 parse_case_B_filter

inline_for_extraction
let size32_cases
  (x: LP.sum_key t_sum)
: Tot (LP.size32 (serialize_cases x))
= match x with
  | Case_A -> (LP.size32_nondep_then LP.size32_u8 () LP.size32_u8 <: LP.size32 (serialize_cases x))
  | Case_B -> (size32_case_B <: LP.size32 (serialize_cases x))
  | _ -> (LP.size32_u16 <: LP.size32 (serialize_cases x))

let size32_t : LP.size32 serialize_t =
  assert_norm (LP.size32_sum_gen_precond (LP.get_parser_kind LP.parse_u8) (LP.weaken_parse_cases_kind t_sum parse_cases));
  LP.size32_sum
    t_sum
    _
    size32_key
    _
    size32_cases
    (_ by (LP.dep_enum_destr_tac ()))
    ()


let parse_t_array_precond () : Lemma
  (LP.fldata_array_precond
      parse_t
      54
      18
    == true)
= assert_norm (
    LP.fldata_array_precond
      parse_t
      54
      18
    == true   
  )

let parse_t_array : LP.parser _ (LP.array t 18) =
  parse_t_array_precond ();
  LP.parse_array serialize_t 54 18

// inline_for_extraction
let parse32_t_array : LP.parser32 parse_t_array =
  [@inline_let]
  let _ = parse_t_array_precond () in
  LP.parse32_array serialize_t parse32_t 54 54ul 18 ()

let serialize_t_array : LP.serializer parse_t_array =
  parse_t_array_precond ();
  LP.serialize_array serialize_t 54 18 ()

// inline_for_extraction
let serialize32_t_array : LP.serializer32 serialize_t_array =
  [@inline_let]
  let _ = parse_t_array_precond () in
  LP.serialize32_array #_ #_ #parse_t #serialize_t serialize32_t 54 18 ()

// NOTE: in this example, byte-size bounds do not need to exactly match element-count bounds (which would be 15 and 21 respectively)

let parse_t_vlarray_precond () : Lemma
  (LP.vldata_vlarray_precond 13 22 parse_t 5 7 == true)
= assert_norm (LP.vldata_vlarray_precond 13 22 parse_t 5 7 == true)

let parse_t_vlarray : LP.parser _ (LP.vlarray t 5 7) =
  parse_t_vlarray_precond ();
  LP.parse_vlarray 13 22 serialize_t 5 7 ()

// inline_for_extraction
let parse32_t_vlarray : LP.parser32 parse_t_vlarray =
  [@inline_let]
  let _ = parse_t_vlarray_precond () in
  LP.parse32_vlarray 13 13ul 22 22ul serialize_t parse32_t 5 7 ()

let serialize_t_vlarray : LP.serializer parse_t_vlarray =
  parse_t_vlarray_precond ();
  LP.serialize_vlarray 13 22 serialize_t 5 7 ()

// inline_for_extraction
let serialize32_t_vlarray : LP.serializer32 serialize_t_vlarray =
  [@inline_let]
  let _ = parse_t_vlarray_precond () in
  LP.serialize32_vlarray 13 22 #_ #_ #parse_t #serialize_t serialize32_t 5 7 ()
*)

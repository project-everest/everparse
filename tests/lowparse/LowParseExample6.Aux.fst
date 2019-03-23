module LowParseExample6.Aux

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot

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
  ]
  in
  [@inline_let]
  let _ : squash (L.noRepeats (LP.list_map fst e) /\ L.noRepeats (LP.list_map snd e)) =
    assert_norm (L.noRepeats (LP.list_map fst e));
    assert_norm (L.noRepeats (LP.list_map snd e))
  in
  e

inline_for_extraction
let case_B = (x: U16.t { U16.v x > 0 } )

noeq
type t =
  | A of (U8.t * U8.t)
  | B of case_B
  | C : LP.unknown_enum_repr case_enum -> U16.t -> t
  | V2 of U16.t
  | V3 of U16.t
  | V4 of  U16.t
  | V5 of U16.t
  | V6 of U16.t
  | V7 of U16.t
  | V8 of U16.t
  | V9 of U16.t

inline_for_extraction
unfold
let known_case_as_case_enum
  (x: cases { norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst case_enum)) == true } )
: Tot (LP.enum_key case_enum)
= [@inline_let]
  let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst case_enum)) in
  x

inline_for_extraction
let cases_of_t
  (x: t)
: Tot (LP.maybe_enum_key case_enum)
= match x with
  | A _ -> LP.Known (known_case_as_case_enum Case_A)
  | B _ -> LP.Known (known_case_as_case_enum Case_B)
  | V2 _ -> LP.Known (known_case_as_case_enum Case_V2)
  | V3 _ -> LP.Known (known_case_as_case_enum Case_V3)
  | V4 _ -> LP.Known (known_case_as_case_enum Case_V4)
  | V5 _ -> LP.Known (known_case_as_case_enum Case_V5)
  | V6 _ -> LP.Known (known_case_as_case_enum Case_V6)
  | V7 _ -> LP.Known (known_case_as_case_enum Case_V7)
  | V8 _ -> LP.Known (known_case_as_case_enum Case_V8)
  | V9 _ -> LP.Known (known_case_as_case_enum Case_V9)
  | C x _ -> LP.Unknown x

inline_for_extraction
let type_of_known_case
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

unfold
inline_for_extraction
let to_type_of_known_case
  (k: LP.enum_key case_enum)
  (x: cases)
  (q: squash ((k <: cases) == x))
  (#x' : LP.maybe_enum_key case_enum)
  (y: LP.dsum_type_of_tag' case_enum type_of_known_case U16.t x')
: Pure (norm [delta_only [(`%type_of_known_case)]; iota] (type_of_known_case x))
  (requires (LP.Known k == x'))
  (ensures (fun y' -> y' == y))
= [@inline_let]
  let _ = norm_spec [delta_only [(`%type_of_known_case)] ; iota] (type_of_known_case k) in
  y

unfold
inline_for_extraction
let to_refine_with_tag (k: LP.maybe_enum_key case_enum) (x: t) : Pure (LP.refine_with_tag cases_of_t k)
  (requires (
    norm [delta; iota; zeta] (cases_of_t x) == k
  ))
  (ensures (fun y -> y == x))
= [@inline_let]
  let _ = norm_spec [delta; iota; zeta] (cases_of_t x) in
  x

inline_for_extraction
let synth_known_case
  (k: LP.enum_key case_enum)
  (y: LP.dsum_type_of_tag' case_enum type_of_known_case U16.t (LP.Known k))
: Tot (LP.refine_with_tag cases_of_t (LP.Known k))
= [@inline_let]
  let x = LP.Known k in
  match k with
  | Case_A -> to_refine_with_tag x (A (to_type_of_known_case k Case_A () y))
  | Case_B -> to_refine_with_tag x (B (to_type_of_known_case k Case_B () y))
  | Case_V2 -> to_refine_with_tag x (V2 (to_type_of_known_case k Case_V2 () y))
  | Case_V3 -> to_refine_with_tag x (V3 (to_type_of_known_case k Case_V3 () y))
  | Case_V4 -> to_refine_with_tag x (V4 (to_type_of_known_case k Case_V4 () y))
  | Case_V5 -> to_refine_with_tag x (V5 (to_type_of_known_case k Case_V5 () y))
  | Case_V6 -> to_refine_with_tag x (V6 (to_type_of_known_case k Case_V6 () y))
  | Case_V7 -> to_refine_with_tag x (V7 (to_type_of_known_case k Case_V7 () y))
  | Case_V8 -> to_refine_with_tag x (V8 (to_type_of_known_case k Case_V8 () y))
  | Case_V9 -> to_refine_with_tag x (V9 (to_type_of_known_case k Case_V9 () y))

inline_for_extraction
let synth_case
  (x: LP.maybe_enum_key case_enum)
  (y: LP.dsum_type_of_tag' case_enum type_of_known_case U16.t x)
: Tot (LP.refine_with_tag cases_of_t x)
= match x with
  | LP.Known k -> synth_known_case k y
  | LP.Unknown k -> to_refine_with_tag x (C k y)

unfold
inline_for_extraction
let from_type_of_known_case
  (x' : LP.enum_key case_enum)
  (x: cases)
  (y: norm [delta_only [(`%type_of_known_case)]; iota] (type_of_known_case x))
: Pure (type_of_known_case x')
  (requires (x == x'))
  (ensures (fun y' -> y' == y))
= [@inline_let]
  let _ = norm_spec [delta_only [(`%type_of_known_case)] ; iota] (type_of_known_case x) in
  y

let synth_case_recip_pre
  (k: LP.maybe_enum_key case_enum)
  (x: LP.refine_with_tag cases_of_t k)
: GTot bool
= match k with
  | LP.Known Case_A -> (A? x)
  | LP.Known Case_B -> (B? x)
  | LP.Known Case_V2 -> (V2? x)
  | LP.Known Case_V3 -> (V3? x)
  | LP.Known Case_V4 -> (V4? x)
  | LP.Known Case_V5 -> (V5? x)
  | LP.Known Case_V6 -> (V6? x)
  | LP.Known Case_V7 -> (V7? x)
  | LP.Known Case_V8 -> (V8? x)
  | LP.Known Case_V9 -> (V9? x)
  | _ -> (C? x)

let synth_case_recip_pre_intro1
  (k: LP.maybe_enum_key case_enum)
: Tot (
  (x: t) ->
  Tot (squash (k == cases_of_t x ==> synth_case_recip_pre k x == true)))
= _ by (LP.synth_case_recip_pre_tac ()) // note: the same tactic works for both closed and open sums

let synth_case_recip_pre_intro
  (k: LP.maybe_enum_key case_enum)
  (x: LP.refine_with_tag cases_of_t k)
: Lemma (synth_case_recip_pre k x == true)
= norm_spec [delta; iota] (synth_case_recip_pre k x);
  assert (k == cases_of_t x);
  let _ = synth_case_recip_pre_intro1 k x in
  assert (k == cases_of_t x ==> synth_case_recip_pre k x == true); // FIXME: this is a BUG in F*, this assert should not be needed
  ()

inline_for_extraction
let synth_case_recip
  (k: LP.maybe_enum_key case_enum)
  (x: LP.refine_with_tag cases_of_t k)
: Tot (LP.dsum_type_of_tag' case_enum type_of_known_case U16.t k)
= match k with
  | LP.Known k' ->
    begin match k' with
    | Case_A ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_A) x in
      (match x with A y -> from_type_of_known_case k' Case_A y)
    | Case_B ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_B) x in
      (match x with B y -> from_type_of_known_case k' Case_B y)
    | Case_V2 ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_V2) x in
      (match x with V2 y -> from_type_of_known_case k' Case_V2 y)
    | Case_V3 ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_V3) x in
      (match x with V3 y -> from_type_of_known_case k' Case_V3 y)
    | Case_V4 ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_V4) x in
      (match x with V4 y -> from_type_of_known_case k' Case_V4 y)
    | Case_V5 ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_V5) x in
      (match x with V5 y -> from_type_of_known_case k' Case_V5 y)
    | Case_V6 ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_V6) x in
      (match x with V6 y -> from_type_of_known_case k' Case_V6 y)
    | Case_V7 ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_V7) x in
      (match x with V7 y -> from_type_of_known_case k' Case_V7 y)
    | Case_V8 ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_V8) x in
      (match x with V8 y -> from_type_of_known_case k' Case_V8 y)
    | Case_V9 ->
      [@inline_let]
      let _ = synth_case_recip_pre_intro (LP.Known Case_V9) x in
      (match x with V9 y -> from_type_of_known_case k' Case_V9 y)
    end
  | LP.Unknown z ->
    [@inline_let]
    let _ = synth_case_recip_pre_intro (LP.Unknown z) x in
    (match x with C _ y ->  (y <: LP.dsum_type_of_tag' case_enum type_of_known_case U16.t k))

inline_for_extraction
let t_sum : LP.dsum
= LP.make_dsum' case_enum cases_of_t type_of_known_case U16.t synth_case synth_case_recip
    (_ by (LP.make_dsum_synth_case_recip_synth_case_known_tac ()))
    (_ by (LP.make_dsum_synth_case_recip_synth_case_unknown_tac ()))
    (_ by (LP.synth_case_synth_case_recip_tac ()))

let parse_case_B_filter
  (x: U16.t)
: GTot bool
= U16.v x > 0

let parse_case_B : LP.parser _ case_B =
  LP.parse_filter LP.parse_u16 parse_case_B_filter

let parse_known_cases
  (x: LP.dsum_known_key t_sum)
: Tot (k: LP.parser_kind & LP.parser k (type_of_known_case x))
= match x with
  | Case_A -> (| _, LP.parse_u8 `LP.nondep_then` LP.parse_u8 |)
  | Case_B -> (| _, parse_case_B |)
  | _ -> (| _, LP.parse_u16 |)

let parse_t : LP.parser _ t =
  LP.parse_dsum t_sum LP.parse_u8 parse_known_cases LP.parse_u16

let parse32_cases_B
: (LP.parser32 parse_case_B)
= LP.parse32_filter LP.parse32_u16 parse_case_B_filter (fun x -> U16.gt x 0us)

inline_for_extraction
let parse32_known_cases
  (x: LP.dsum_known_key t_sum)
: Tot (LP.parser32 (dsnd (parse_known_cases x)))
= match x with
  | Case_A -> LP.parse32_u8 `LP.parse32_nondep_then` LP.parse32_u8
  | Case_B -> parse32_cases_B
  | _ -> LP.parse32_u16

let parse32_t
: LP.parser32 parse_t
= LP.parse32_dsum t_sum LP.parse32_u8 parse_known_cases parse32_known_cases LP.parse32_u16 (_ by (LP.maybe_enum_destr_t_tac ()))

let serialize_case_B : LP.serializer parse_case_B =
  LP.serialize_filter LP.serialize_u16 parse_case_B_filter

let serialize_known_cases
  (x: LP.dsum_known_key t_sum)
: Tot (LP.serializer (dsnd (parse_known_cases x)))
= match x with
  | Case_A -> LP.serialize_nondep_then _ LP.serialize_u8 () _ LP.serialize_u8
  | Case_B -> serialize_case_B
  | _ -> LP.serialize_u16

let serialize_t
: LP.serializer parse_t
= LP.serialize_dsum t_sum LP.serialize_u8 _ serialize_known_cases _ LP.serialize_u16

let serialize32_case_B: LP.serializer32 serialize_case_B =
  LP.serialize32_filter LP.serialize32_u16 parse_case_B_filter

#push-options "--z3rlimit 32"

inline_for_extraction
let serialize32_known_cases
  (x: LP.dsum_known_key t_sum)
: Tot (LP.serializer32 (serialize_known_cases x))
= match x with
  | Case_A -> LP.serialize32_nondep_then LP.serialize32_u8 () LP.serialize32_u8 ()
  | Case_B -> serialize32_case_B
  | _ -> LP.serialize32_u16

#pop-options

let serialize32_key: LP.serializer32 (LP.serialize_maybe_enum_key _ LP.serialize_u8 case_enum) =
  _ by (LP.serialize32_maybe_enum_key_tac LP.serialize32_u8 case_enum ())

let serialize32_t
: LP.serializer32 serialize_t
= [@inline_let]
  let _ = assert_norm (LP.serializer32_sum_gen_precond (LP.get_parser_kind LP.parse_u8) (LP.weaken_parse_dsum_cases_kind t_sum parse_known_cases (LP.get_parser_kind LP.parse_u16))) in
  LP.serialize32_dsum t_sum _ serialize32_key _ _ serialize32_known_cases LP.serialize32_u16 (_ by (LP.dep_enum_destr_tac ())) ()

let size32_case_B: LP.size32 serialize_case_B =
  LP.size32_filter LP.size32_u16 parse_case_B_filter

#push-options "--z3rlimit 20"

inline_for_extraction
let size32_known_cases
  (x: LP.dsum_known_key t_sum)
: Tot (LP.size32 (serialize_known_cases x))
= match x with
  | Case_A ->
    LP.coerce (LP.size32 (serialize_known_cases x)) (LP.size32_nondep_then LP.size32_u8 () LP.size32_u8)
  | Case_B -> LP.coerce (LP.size32 (serialize_known_cases x)) size32_case_B
  | _ -> LP.coerce (LP.size32 (serialize_known_cases x)) LP.size32_u16

#pop-options

let size32_key : LP.size32 (LP.serialize_maybe_enum_key _ LP.serialize_u8 case_enum) =
  _ by (LP.size32_maybe_enum_key_tac LP.size32_u8 case_enum ())

let size32_t
: LP.size32 serialize_t
= [@inline_let]
  let _ = assert_norm (LP.size32_sum_gen_precond (LP.get_parser_kind LP.parse_u8) (LP.weaken_parse_dsum_cases_kind t_sum parse_known_cases (LP.get_parser_kind LP.parse_u16))) in
  LP.size32_dsum t_sum _ size32_key _ _ size32_known_cases LP.size32_u16 (_ by (LP.dep_enum_destr_tac ())) ()

(*
module LL = LowParse.Low

let validate32_case_B : LL.validator32 parse_case_B =
  LL.validate32_filter LL.validate32_u16 LL.parse32_u16 parse_case_B_filter (fun x -> x `U16.gt` 0us)

inline_for_extraction
let validate32_known_cases
  (x: LP.dsum_known_key t_sum)
: Tot (LL.validator32 (dsnd (parse_known_cases x)))
= match x with
  | Case_A ->
    LL.coerce (LL.validator32 (dsnd (parse_known_cases x))) (LL.validate32_nondep_then LL.validate32_u8 LL.validate32_u8)
  | Case_B ->
    LL.coerce (LL.validator32 (dsnd (parse_known_cases x))) validate32_case_B
  | _ ->
    LL.coerce (LL.validator32 (dsnd (parse_known_cases x))) LL.validate32_u16

let validate32_t : LL.validator32 parse_t =
  LL.validate32_dsum
    t_sum
    LL.validate32_u8
    LL.parse32_u8
    _
    validate32_known_cases
    LL.validate32_u16
    (_ by (LP.dep_maybe_enum_destr_t_tac ()))
*)

(*
inline_for_extraction
let parse32_cases_A
: (LP.parser32 parse_case_A)
=
    [@inline_let]
    let _ = synth_case_A_inj () in
    LP.parse32_synth
      _
      synth_case_A
      (fun x -> synth_case_A x)
      (LP.parse32_nondep_then LP.parse32_u8 LP.parse32_u8)
      ()

inline_for_extraction
let parse32_cases_B
: (LP.parser32 parse_case_B)
=
    [@inline_let]
    let _ = synth_case_B_inj () in
    LP.parse32_synth
      _
      synth_case_B
      (fun (x: U16.t { parse_case_B_filter x == true } ) -> synth_case_B x)
      (LP.parse32_filter LP.parse32_u16 parse_case_B_filter (fun x -> U16.gt x 0us))
      ()

inline_for_extraction
let parse32_cases'
  (x: LP.dsum_known_key t_sum)
: Tot (LP.parser32 (dsnd (parse_cases' x)))
= match x with
  | Case_A -> parse32_cases_A
  | Case_B -> parse32_cases_B

inline_for_extraction
let parse32_cases_C
  (x: LP.unknown_enum_repr case_enum)
: Tot (LP.parser32 (parse_case_C x))
=   [@inline_let]
    let _ = synth_case_C_inj x in
    LP.parse32_synth
      _
      (synth_case_C x)
      (fun (y: U16.t) -> synth_case_C x y)
      (LP.parse32_u16)
      ()

inline_for_extraction
let parse32_cases
: (x: LP.dsum_key t_sum) ->
  Tot (LP.parser32 (parse_cases x))
= LP.parse32_dsum_cases t_sum parse_cases' parse32_cases' parse_case_C parse32_cases_C

module T = FStar.Tactics

inline_for_extraction
let destr_case_enum
  (t: Type)
: Tot (LP.maybe_enum_destr_t t case_enum)
= _ by (LP.maybe_enum_destr_t_tac ())

inline_for_extraction
let parse32_t
: LP.parser32 parse_t
= LP.parse32_dsum_gen
    _
    LP.parse32_u8
    _
    parse32_cases
    (destr_case_enum _)

(*
FStar.Tactics.synth_by_tactic
    (LP.parse32_sum_tac
      t_sum
      LP.parse32_u8
      parse32_cases
      parse_t
      ()
    )
*)


let cases_of_t_A (x: t) : Lemma
  (cases_of_t x == LP.Known Case_A <==> A? x)
= ()

inline_for_extraction
let synth_case_A_inv (z: LP.dsum_cases t_sum (LP.Known Case_A)) : Tot (z: (U8.t * U8.t)) =
  [@inline_let]
  let z' : t = z in
  let _ = cases_of_t_A z' in
  match z' with
  | A res -> res

let synth_case_A_inv_correct () : Lemma
  (LP.synth_inverse synth_case_A synth_case_A_inv)
= ()

let cases_of_t_B (x: t) : Lemma
  (cases_of_t x == LP.Known Case_B <==> B? x)
= ()

inline_for_extraction
let synth_case_B_inv (z: LP.dsum_cases t_sum (LP.Known Case_B)) : Tot (z: U16.t { UInt16.v z > 0 } ) =
  [@inline_let]
  let z' : t = z in
  let _ = cases_of_t_B z' in
  match z' with
  | B res -> res

let synth_case_B_inv_correct () : Lemma
  (LP.synth_inverse synth_case_B synth_case_B_inv)
= ()

let cases_of_t_C (x: t) : Lemma
  ((LP.Unknown? (cases_of_t x) <==> C? x) /\ (match cases_of_t x, x with
    | LP.Unknown k1, C k2 _ -> k1 == k2
    | _ -> True
  ))
= ()

inline_for_extraction
let synth_case_C_inv (x: LP.unknown_enum_repr case_enum) (y: LP.dsum_cases t_sum (LP.Unknown x)) : Tot U16.t =
  [@inline_let]
  let z : t = y in
  let _ = cases_of_t_C z in
  match z with
  | C _ y -> y

let synth_case_C_inv_correct (x: LP.unknown_enum_repr case_enum) : Lemma (LP.synth_inverse (synth_case_C x) (synth_case_C_inv x))
= Classical.forall_intro cases_of_t_C

let serialize_case_A
: LP.serializer parse_case_A
= 
    synth_case_A_inj ();
    synth_case_A_inv_correct ();
      (LP.serialize_synth
        (LP.nondep_then LP.parse_u8 LP.parse_u8)
        synth_case_A
        (LP.serialize_nondep_then LP.parse_u8 LP.serialize_u8 () LP.parse_u8 LP.serialize_u8)
        synth_case_A_inv
        ()
      )

let serialize_case_B
: LP.serializer parse_case_B
= 
    synth_case_B_inj ();
    synth_case_B_inv_correct ();
      (LP.serialize_synth
        (LP.parse_filter LP.parse_u16 parse_case_B_filter)
        synth_case_B
        (LP.serialize_filter #_ #_ #LP.parse_u16 LP.serialize_u16 parse_case_B_filter)
        synth_case_B_inv
        ()
      )

let serialize_case_C
  (x: LP.unknown_enum_repr case_enum)
: Tot (LP.serializer (parse_case_C x))
= synth_case_C_inj x;
  synth_case_C_inv_correct x;
  LP.serialize_synth
    LP.parse_u16
    (synth_case_C x)
    LP.serialize_u16
    (synth_case_C_inv x)
    ()

let serialize_cases'
  (x: LP.dsum_known_key t_sum)
: Tot (LP.serializer (dsnd (parse_cases' x)))
= match x with
  | Case_A -> serialize_case_A
  | Case_B -> serialize_case_B

let serialize_cases
: (x: LP.dsum_key t_sum) ->
  Tot (LP.serializer (parse_cases x))
= LP.serialize_dsum_cases t_sum parse_cases' serialize_cases' parse_case_C serialize_case_C

let serialize_t : LP.serializer parse_t =
  LP.serialize_dsum t_sum LP.serialize_u8 serialize_cases

inline_for_extraction
let serialize32_case_A
: LP.serializer32 (serialize_case_A)
= 
      [@inline_let]
      let _ = synth_case_A_inj () in
      [@inline_let]
      let _ = synth_case_A_inv_correct () in
      LP.serialize32_synth
        _
        synth_case_A
        _
        (LP.serialize32_nondep_then #_ #_ #LP.parse_u8 #LP.serialize_u8 LP.serialize32_u8 () #_ #_ #LP.parse_u8 #LP.serialize_u8 LP.serialize32_u8 ())
        synth_case_A_inv
        (fun x -> synth_case_A_inv x)
        ()

inline_for_extraction
let serialize32_case_B
: LP.serializer32 (serialize_case_B)
=
      [@inline_let]
      let _ = synth_case_B_inj () in
      [@inline_let]
      let _ = synth_case_B_inv_correct () in
      LP.serialize32_synth
        (LP.parse_filter LP.parse_u16 parse_case_B_filter)
        synth_case_B
        (LP.serialize_filter LP.serialize_u16 parse_case_B_filter)
        (LP.serialize32_filter LP.serialize32_u16 parse_case_B_filter)
        synth_case_B_inv
        (fun x -> synth_case_B_inv x)
        ()

inline_for_extraction
let serialize32_case_C
  (x: LP.unknown_enum_repr case_enum)
: Tot (LP.serializer32 (serialize_case_C x))
=
      [@inline_let]
      let _ = synth_case_C_inj x in
      [@inline_let]
      let _ = synth_case_C_inv_correct x in
      LP.serialize32_synth
        LP.parse_u16
        (synth_case_C x)
        LP.serialize_u16
        LP.serialize32_u16
        (synth_case_C_inv x)
        (fun y -> synth_case_C_inv x y)
        ()

inline_for_extraction
let serialize32_cases'
  (x: LP.dsum_known_key t_sum)
: Tot (LP.serializer32 (serialize_cases' x))
= match x with
  | Case_A -> serialize32_case_A
  | Case_B -> serialize32_case_B

inline_for_extraction
let dep_destr
  (t: (k: LP.enum_key case_enum) -> Tot Type)
: Tot (LP.dep_enum_destr case_enum t)
= _ by (LP.dep_enum_destr_tac ())

inline_for_extraction
let serialize32_cases
: (x: LP.dsum_key t_sum) ->
  Tot (LP.serializer32 (serialize_cases x))
= LP.serialize32_dsum_cases
    t_sum
    parse_cases'
    serialize_cases'
    serialize32_cases'
    _
    _
    serialize32_case_C
    (dep_destr _)

inline_for_extraction
let serialize32_key : LP.serializer32 (LP.serialize_maybe_enum_key _ LP.serialize_u8 (LP.dsum_enum t_sum))
= _ by (LP.serialize32_maybe_enum_key_tac LP.serialize32_u8 (LP.dsum_enum t_sum) ())

inline_for_extraction
let serialize32_t : LP.serializer32 serialize_t =
  [@inline_let]
  let (u: unit {
    LP.serializer32_sum_gen_precond
      LP.parse_u8_kind
      (LP.weaken_parse_dsum_cases_kind' t_sum parse_cases' parse_case_C)
  }) = assert_norm (
    LP.serializer32_sum_gen_precond
      LP.parse_u8_kind
      (LP.weaken_parse_dsum_cases_kind' t_sum parse_cases' parse_case_C)
  )
  in
  LP.serialize32_dsum_gen
    t_sum
    serialize32_key
    serialize32_cases
    ()
    (fun x -> cases_of_t x)


(*
  FStar.Tactics.synth_by_tactic (LP.serialize32_sum_tac
    t_sum
    #_
    #LP.serialize_u8
    LP.serialize32_u8
    serialize32_cases
    u
    (fun x -> cases_of_t x)
    serialize_t
    ()
  )

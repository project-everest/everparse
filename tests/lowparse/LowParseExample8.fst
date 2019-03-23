module LowParseExample8

module LP = LowParse.Spec
module LS = LowParse.SLow
module LL = LowParse.Low
module U8 = FStar.UInt8
module U16 = FStar.UInt16

module L = FStar.List.Tot

inline_for_extraction
let u8 : eqtype = U8.t

inline_for_extraction
let k_enum : LP.enum k_t u8 =
  [@inline_let]
  let e : list (k_t * U8.t) = [
    Ka, 18uy;
    Kb, 42uy;
  ]
  in
  [@inline_let]
  let _ : squash (L.noRepeats (LP.list_map fst e) /\ L.noRepeats (LP.list_map snd e)) =
    assert_norm (L.noRepeats (LP.list_map fst e));
    assert_norm (L.noRepeats (LP.list_map snd e))
  in
  e

inline_for_extraction
unfold
let case_as_case_enum
  (x: k_t)
: Tot (y: LP.enum_key k_enum { y == x } )
= match x with
  | Ka -> [@inline_let] let _ = assert_norm (LP.list_mem Ka (LP.list_map fst k_enum)) in Ka
  | Kb -> [@inline_let] let _ = assert_norm (LP.list_mem Ka (LP.list_map fst k_enum)) in Kb

inline_for_extraction
let cases_of_t
  (x: t')
: Tot (y: LP.enum_key k_enum { y == key x } )
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
let to_refine_with_tag (k: LP.enum_key k_enum) (x: t') : Pure (LP.refine_with_tag cases_of_t k)
  (requires (
    norm [delta; iota; zeta] (cases_of_t x) == k
  ))
  (ensures (fun y -> y == x))
= [@inline_let]
  let _ = norm_spec [delta; iota; zeta] (cases_of_t x) in
  x


inline_for_extraction
let synth_case
  (x: LP.enum_key k_enum)
  (y: type_of_case x)
: Tot (LP.refine_with_tag cases_of_t x)
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
  (k: LP.enum_key k_enum)
  (x: LP.refine_with_tag cases_of_t k)
: GTot bool
= match k with
  | Ka -> (Ta? x)
  | Kb -> (Tb? x)

module T = LowParse.TacLib

let synth_case_recip_pre_intro1
  (k: LP.enum_key k_enum)
: Tot (
  (x: t') ->
  Tot (squash (k == cases_of_t x ==> synth_case_recip_pre k x == true)))
= _ by (LS.synth_case_recip_pre_tac ())

let synth_case_recip_pre_intro
  (k: LP.enum_key k_enum)
  (x: LP.refine_with_tag cases_of_t k)
: Lemma (synth_case_recip_pre k x == true)
= norm_spec [delta; iota] (synth_case_recip_pre k x);
  assert (k == cases_of_t x);
  let _ = synth_case_recip_pre_intro1 k x in
  assert (k == cases_of_t x ==> synth_case_recip_pre k x == true); // FIXME: this is a BUG in F*, this assert should not be needed
  ()

inline_for_extraction
let synth_case_recip
  (k: LP.enum_key k_enum)
  (x: LP.refine_with_tag cases_of_t k)
: Tot (type_of_case k)
= match k with
  | Ka -> [@inline_let] let _ = synth_case_recip_pre_intro Ka x in (match x with Ta y -> (from_type_of_case Ka y))
  | Kb -> [@inline_let] let _ = synth_case_recip_pre_intro Kb x in (match x with Tb y -> (from_type_of_case Kb y))

inline_for_extraction
let t_sum : LP.sum
= LP.make_sum' k_enum cases_of_t type_of_case synth_case synth_case_recip
    (_ by (LS.make_sum_synth_case_recip_synth_case_tac ()))
    (_ by (LS.synth_case_synth_case_recip_tac ()))

let parse_cases
  (x: LP.sum_key t_sum)
: Tot (k: LP.parser_kind & LP.parser k (type_of_case x))
= match x with
  | Ka -> (| _, LP.parse_u8 |)
  | Kb -> (| _, LP.parse_u16 |)

let _ : squash (parse_t_kind == LP.weaken_parse_cases_kind t_sum parse_cases) = _ by (T.trefl ())

let t_eq_lemma (k: k_t) : Lemma (t k == LP.sum_cases t_sum (case_as_case_enum k)) [SMTPat (t k)] =
  match k with
  | Ka -> assert_norm (t Ka == LP.sum_cases t_sum (case_as_case_enum Ka))
  | Kb -> assert_norm (t Kb == LP.sum_cases t_sum (case_as_case_enum Kb))

let parse_t k = LP.parse_sum_cases t_sum parse_cases (case_as_case_enum k)

let serialize_cases (x: LP.sum_key t_sum) : Tot (LP.serializer (dsnd (parse_cases x))) =
  match x with
  | Ka -> (LP.serialize_u8 <: LP.serializer (dsnd (parse_cases x)))
  | Kb -> (LP.serialize_u16 <: LP.serializer (dsnd (parse_cases x)))

let serialize_t k = LP.serialize_sum_cases t_sum parse_cases serialize_cases (case_as_case_enum k)

inline_for_extraction
let parse32_cases (k: LP.sum_key t_sum) : Tot (LS.parser32 (dsnd (parse_cases k))) = match k with
  | Ka -> (LS.parse32_u8 <: LS.parser32 (dsnd (parse_cases k)))
  | Kb -> (LS.parse32_u16 <: LS.parser32 (dsnd (parse_cases k)))

let parse32_t k =
  [@inline_let] let _ = assert (k == case_as_case_enum k) in
  [@inline_let] let k : LP.sum_key t_sum = k in
  LS.parse32_sum_cases t_sum parse_cases parse32_cases (_ by (LS.dep_enum_destr_tac ())) k

inline_for_extraction
let serialize32_cases (k: LP.sum_key t_sum) : Tot (LS.serializer32 (serialize_cases k)) = match k with
  | Ka -> (LS.serialize32_u8 <: LS.serializer32 (serialize_cases k))
  | Kb -> (LS.serialize32_u16 <: LS.serializer32 (serialize_cases k))

let serialize32_t k =
  [@inline_let] let _ = assert (k == case_as_case_enum k) in
  [@inline_let] let k : LP.sum_key t_sum = k in
  LS.serialize32_sum_cases t_sum serialize_cases serialize32_cases (_ by (LS.dep_enum_destr_tac ())) k

inline_for_extraction
let size32_cases (k: LP.sum_key t_sum) : Tot (LS.size32 (serialize_cases k)) = match k with
  | Ka -> (LS.size32_u8 <: LS.size32 (serialize_cases k))
  | Kb -> (LS.size32_u16 <: LS.size32 (serialize_cases k))

let size32_t k =
  [@inline_let] let _ = assert (k == case_as_case_enum k) in
  [@inline_let] let k : LP.sum_key t_sum = k in
  LS.size32_sum_cases t_sum serialize_cases size32_cases (_ by (LS.dep_enum_destr_tac ())) k

inline_for_extraction
let validate_cases (k: LP.sum_key t_sum) : Tot (LL.validator (dsnd (parse_cases k))) = match k with
  | Ka -> (LL.validate_u8 () <: LL.validator (dsnd (parse_cases k)))
  | Kb -> (LL.validate_u16 () <: LL.validator (dsnd (parse_cases k)))

let validate_t k =
  [@inline_let] let _ = assert (k == case_as_case_enum k) in
  [@inline_let] let k : LP.sum_key t_sum = k in
  LL.validate_sum_cases t_sum parse_cases validate_cases (_ by (LS.dep_enum_destr_tac ())) k

inline_for_extraction
let jump_cases (k: LP.sum_key t_sum) : Tot (LL.jumper (dsnd (parse_cases k))) = match k with
  | Ka -> (LL.jump_u8 <: LL.jumper (dsnd (parse_cases k)))
  | Kb -> (LL.jump_u16 <: LL.jumper (dsnd (parse_cases k)))

let jump_t k =
  [@inline_let] let _ = assert (k == case_as_case_enum k) in
  [@inline_let] let k : LP.sum_key t_sum = k in
  LL.jump_sum_cases t_sum parse_cases jump_cases (_ by (LS.dep_enum_destr_tac ())) k

let main argc argv =
  C.EXIT_SUCCESS

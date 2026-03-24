module LowParseExample9.Aux

(* Spec + dsum definition for Example9, as a regular F* module.
   Ported from tests/lowparse/LowParseExample9.fst + .fsti
   Dropped SLow/Low parts. *)

include LowParse.Spec.Int
include LowParse.Spec.Combinators
include LowParse.Spec.Enum
include LowParse.Spec.Tac.Enum
include LowParse.Spec.Sum
include LowParse.Spec.Tac.Sum

module LP = LowParse.Spec.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let kt_repr : eqtype = U8.t
inline_for_extraction let kt_repr_eq (x1 x2: kt_repr) : Tot bool = (x1 = x2)
let known_kt_repr (v:U8.t) : bool = v `kt_repr_eq` 0z || (v `kt_repr_eq` 1z || (false))

type kt =
  | Ka
  | Kb
  | Unknown_kt of (v:U8.t{not (known_kt_repr v)})

type tt =
  | Case_ka of U8.t
  | Case_kb of U16.t
  | Case_Unknown_kt: v:kt_repr{not (known_kt_repr v)} -> U32.t -> tt

inline_for_extraction let tag_of_tt (x:tt) : kt = match x with
  | Case_ka _ -> Ka
  | Case_kb _ -> Kb
  | Case_Unknown_kt v _ -> Unknown_kt v

inline_for_extraction
let t (k: kt) : Tot Type = (x: tt { tag_of_tt x == k } )

inline_for_extraction
let parse_t_kind : LP.parser_kind = LP.strong_parser_kind 1 4 (Some LP.ParserKindMetadataTotal)

inline_for_extraction let kt_enum : enum kt U8.t =
  [@inline_let] let e = [
    Ka, 0z;
    Kb, 1z;
  ] in
  [@inline_let] let _ =
    assert_norm (L.noRepeats (list_map fst e))
  in
  [@inline_let] let _ = 
    assert_norm (L.noRepeats (list_map snd e))
  in e

inline_for_extraction let synth_kt (x:maybe_enum_key kt_enum) : kt = 
  match x with
  | Known k -> k
  | Unknown y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = assert_norm (list_mem v (list_map snd kt_enum) == known_kt_repr v) in
    Unknown_kt v

inline_for_extraction let synth_kt_inv (x:kt) : maybe_enum_key kt_enum = 
  match x with
  | Unknown_kt y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = assert_norm (list_mem v (list_map snd kt_enum) == known_kt_repr v) in
    Unknown v
  | x ->
    [@inline_let] let x1 : kt = x in
    [@inline_let] let _ : squash(not (Unknown_kt? x1) ==> list_mem x1 (list_map fst kt_enum)) =
      _ by (LowParse.Spec.Tac.Enum.synth_maybe_enum_key_inv_unknown_tac x1)
    in
    Known (x1 <: enum_key kt_enum)

let lemma_synth_kt_inv' () : Lemma
  (synth_inverse synth_kt_inv synth_kt)
= forall_maybe_enum_key kt_enum (fun x -> synth_kt_inv (synth_kt x) == x)
    (_ by (LowParse.Spec.Tac.Enum.forall_maybe_enum_key_known_tac ()))
    (_ by (LowParse.Spec.Tac.Enum.forall_maybe_enum_key_unknown_tac ()))

let lemma_synth_kt_inj () : Lemma
  (synth_injective synth_kt) = 
  lemma_synth_kt_inv' ();
  synth_inverse_synth_injective synth_kt synth_kt_inv

#push-options "--max_ifuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"
let lemma_synth_kt_inv () : Lemma
  (synth_inverse synth_kt synth_kt_inv) = allow_inversion kt; ()
#pop-options

#set-options "--z3rlimit 120"

inline_for_extraction unfold let known_kt_as_enum_key
  (x: kt { norm [delta_only [`%list_mem; `%list_map; `%fst; `%kt_enum]; zeta; iota; primops] (list_mem x (list_map fst kt_enum)) == true })
  : enum_key kt_enum =
  [@inline_let] let _ = norm_spec [delta_only [`%list_mem; `%list_map; `%fst; `%kt_enum]; zeta; iota; primops] (list_mem x (list_map fst kt_enum)) in x

inline_for_extraction let unknown_kt_as_enum_key (r:kt_repr) : Pure (unknown_enum_repr kt_enum)
  (requires known_kt_repr r == false) (ensures fun _ -> True) =
  [@inline_let] let _ = assert_norm(list_mem r (list_map snd kt_enum) == known_kt_repr r) in r

inline_for_extraction let unknown_enum_repr_kt_as_repr (r:unknown_enum_repr kt_enum) : Pure kt_repr
  (requires True) (ensures fun r -> known_kt_repr r == false) =
  [@inline_let] let _ = assert_norm(list_mem r (list_map snd kt_enum) == known_kt_repr r) in r

inline_for_extraction let key_of_tt (x:tt) : maybe_enum_key kt_enum =
  match x with
  | Case_ka _ -> Known (known_kt_as_enum_key Ka)
  | Case_kb _ -> Known (known_kt_as_enum_key Kb)
  | Case_Unknown_kt v _ -> Unknown (unknown_kt_as_enum_key v)

inline_for_extraction let tt_case_of_kt (x:kt) : Type0 =
  match x with
  | Ka -> U8.t
  | Kb -> U16.t
  | Unknown_kt _ -> squash False

unfold inline_for_extraction let tt_value_type (x:maybe_enum_key kt_enum) =
  dsum_type_of_tag' kt_enum tt_case_of_kt U32.t x

unfold inline_for_extraction let tt_refine (k:maybe_enum_key kt_enum) (x:tt)
  : Pure (refine_with_tag key_of_tt k)
  (requires key_of_tt x == k) (ensures fun y -> y == x) =
  [@inline_let] let _ = norm_spec [delta_only [`%key_of_tt]; iota; zeta] (key_of_tt x) in x

unfold inline_for_extraction let tt_type_of_known_case (k: enum_key kt_enum)
  (x:kt) (q: squash ((k <: kt) == x))
  (#x' : maybe_enum_key kt_enum) (y: tt_value_type x')
  : Pure (norm [delta_only [(`%tt_case_of_kt)]; iota] (tt_case_of_kt x))
  (requires (Known k == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%tt_case_of_kt)]; iota] (tt_case_of_kt k) in y

unfold inline_for_extraction let tt_known_case (k: enum_key kt_enum)
  (x: kt) (y: norm [delta_only [(`%tt_case_of_kt)]; iota] (tt_case_of_kt x))
  : Pure (tt_case_of_kt k) (requires (k == x)) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%tt_case_of_kt)] ; iota] (tt_case_of_kt x) in y

inline_for_extraction let synth_known_tt_cases (k:enum_key kt_enum)
  (y:tt_value_type (Known k)) : refine_with_tag key_of_tt (Known k) =
  match k with
  | Ka ->
    [@inline_let] let x : tt = Case_ka (tt_type_of_known_case k Ka () y) in
    [@inline_let] let _ = assert_norm (key_of_tt x == Known Ka) in
    tt_refine (Known Ka) x
  | Kb ->
    [@inline_let] let x : tt = Case_kb (tt_type_of_known_case k Kb () y) in
    [@inline_let] let _ = assert_norm (key_of_tt x == Known Kb) in
    tt_refine (Known Kb) x

inline_for_extraction let synth_tt_cases (x:maybe_enum_key kt_enum)
  (y:tt_value_type x) : refine_with_tag key_of_tt x =
  match x with
  | Unknown v ->
    [@inline_let] let x : tt = Case_Unknown_kt (unknown_enum_repr_kt_as_repr v) y in
    [@inline_let] let _ = assert_norm (key_of_tt x == Unknown v) in
    tt_refine (Unknown v) x
  | Known k -> synth_known_tt_cases k y

unfold inline_for_extraction let from_tt_case_of_kt (#x':kt) (x:kt)
  (y: norm [delta_only [(`%tt_case_of_kt)]; iota] (tt_case_of_kt x))
  : Pure (tt_case_of_kt x') (requires (x == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%tt_case_of_kt)] ; iota] (tt_case_of_kt x) in y

let synth_tt_cases_recip_pre (k:maybe_enum_key kt_enum)
  (x:refine_with_tag key_of_tt k) : GTot bool =
  match k with
  | Known Ka -> Case_ka? x
  | Known Kb -> Case_kb? x
  | Known _ -> false
  | Unknown _ -> Case_Unknown_kt? x

let synth_tt_cases_recip_pre_intro' (x: tt) : Lemma (synth_tt_cases_recip_pre (key_of_tt x) x) = ()
let synth_tt_cases_recip_pre_intro (k:maybe_enum_key kt_enum)
  (x:refine_with_tag key_of_tt k)
  : Lemma (synth_tt_cases_recip_pre k x == true) =
  synth_tt_cases_recip_pre_intro' x

inline_for_extraction let synth_tt_cases_recip (k:maybe_enum_key kt_enum)
  (x:refine_with_tag key_of_tt k) : (tt_value_type k) =
  match k with
  | Unknown z ->
    [@inline_let] let _ = synth_tt_cases_recip_pre_intro (Unknown z) x in
    (match x with Case_Unknown_kt _ y ->  (y <: tt_value_type k))
  | Known k' ->
    match k' with
    | Ka -> [@inline_let] let _ = synth_tt_cases_recip_pre_intro (Known Ka) x in
      (match x with Case_ka y -> tt_known_case k' Ka y)
    | Kb -> [@inline_let] let _ = synth_tt_cases_recip_pre_intro (Known Kb) x in
      (match x with Case_kb y -> tt_known_case k' Kb y)
   | _ -> [@inline_let] let _ = synth_tt_cases_recip_pre_intro (Known k') in false_elim ()

inline_for_extraction let tt_sum : dsum = make_dsum' kt_enum key_of_tt
  tt_case_of_kt U32.t synth_tt_cases synth_tt_cases_recip
  (_ by (LowParse.Spec.Tac.Sum.make_dsum_synth_case_recip_synth_case_known_tac ()))
  (_ by (LowParse.Spec.Tac.Sum.make_dsum_synth_case_recip_synth_case_unknown_tac ()))
  (_ by (LowParse.Spec.Tac.Sum.synth_case_synth_case_recip_tac ()))

noextract let parse_tt_cases (x:dsum_known_key tt_sum)
  : k:parser_kind & parser k (tt_case_of_kt x) =
  match x with
  | Ka -> let u : (k: parser_kind & parser k (tt_case_of_kt Ka)) = (| _, parse_u8 |) in u
  | Kb -> let u : (k: parser_kind & parser k (tt_case_of_kt Kb)) = (| _, parse_u16 |) in u
  | _ -> (| _, parse_false |)

noextract let serialize_tt_cases (x:dsum_known_key tt_sum)
  : serializer (dsnd (parse_tt_cases x)) =
  match x with
  | Ka -> let u : serializer (dsnd (parse_tt_cases Ka)) = serialize_u8 in u
  | Kb -> let u : serializer (dsnd (parse_tt_cases Kb)) = serialize_u16 in u
  | _ -> serialize_false

(* Synth to align t k with dsum types *)

inline_for_extraction
let synth_t (k: kt) (x: refine_with_tag key_of_tt (synth_kt_inv k)) : Tot (t k) = x

inline_for_extraction
let synth_t_recip (k: kt) (x: t k) : Tot (refine_with_tag key_of_tt (synth_kt_inv k)) = x

let synth_t_inj (k: kt) : Lemma (synth_injective (synth_t k)) = ()

let synth_t_inv (k: kt) : Lemma (synth_inverse (synth_t k) (synth_t_recip k)) = ()

let parse_t (k: kt) : LP.parser parse_t_kind (t k) =
  parse_dsum_cases tt_sum parse_tt_cases parse_u32 (synth_kt_inv k) `parse_synth` synth_t k

let serialize_t (k: kt) : LP.serializer (parse_t k) =
  serialize_synth
    _
    (synth_t k)
    (serialize_dsum_cases tt_sum parse_tt_cases serialize_tt_cases parse_u32 serialize_u32 (synth_kt_inv k))
    (synth_t_recip k)
    ()

let parse_dsum_cases_eq_forall
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Lemma (forall input . parse (parse_dsum_cases s f g x) input == parse (parse_dsum_cases' s f g x) input)
= Classical.forall_intro (parse_dsum_cases_eq' s f g x)

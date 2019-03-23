module LowParseExample9

module LP = LowParse.Spec
module LS = LowParse.SLow
module LL = LowParse.Low
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

(* BEGIN QuackyDucky output as of 8884d37904cb71bae96551d26b0bc7ad496b709f *)

inline_for_extraction let kt_enum : LP.enum kt U8.t =
  [@inline_let] let e = [
    Ka, 0z;
    Kb, 1z;
  ] in
  [@inline_let] let _ =
    assert_norm (L.noRepeats (LP.list_map fst e))
  in
  [@inline_let] let _ = 
    assert_norm (L.noRepeats (LP.list_map snd e))
  in e

inline_for_extraction let synth_kt (x:LP.maybe_enum_key kt_enum) : kt = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = assert_norm (LP.list_mem v (LP.list_map snd kt_enum) == known_kt_repr v) in
    Unknown_kt v

inline_for_extraction let synth_kt_inv (x:kt) : LP.maybe_enum_key kt_enum = 
  match x with
  | Unknown_kt y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = assert_norm (LP.list_mem v (LP.list_map snd kt_enum) == known_kt_repr v) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : kt = x in
    [@inline_let] let _ : squash(not (Unknown_kt? x1) ==> LP.list_mem x1 (LP.list_map fst kt_enum)) =
      _ by (LS.synth_maybe_enum_key_inv_unknown_tac x1)
    in
    LP.Known (x1 <: LP.enum_key kt_enum)

let lemma_synth_kt_inv' () : Lemma
  (LP.synth_inverse synth_kt_inv synth_kt)
= LP.forall_maybe_enum_key kt_enum (fun x -> synth_kt_inv (synth_kt x) == x)
    (_ by (LS.forall_maybe_enum_key_known_tac ()))
    (_ by (LS.forall_maybe_enum_key_unknown_tac ()))

let lemma_synth_kt_inj () : Lemma
  (LP.synth_injective synth_kt) = 
  lemma_synth_kt_inv' ();
  LP.synth_inverse_synth_injective synth_kt synth_kt_inv

#push-options "--max_ifuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"
let lemma_synth_kt_inv () : Lemma
  (LP.synth_inverse synth_kt synth_kt_inv) = allow_inversion kt; ()

#pop-options

// Need high Z3 limits for large sum types
#set-options "--z3rlimit 120"

inline_for_extraction unfold let known_kt_as_enum_key
  (x: kt { norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst kt_enum)) == true })
  : LP.enum_key kt_enum =
  [@inline_let] let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst kt_enum)) in x

inline_for_extraction let unknown_kt_as_enum_key (r:kt_repr) : Pure (LP.unknown_enum_repr kt_enum)
  (requires known_kt_repr r == false) (ensures fun _ -> True) =
  [@inline_let] let _ = assert_norm(LP.list_mem r (LP.list_map snd kt_enum) == known_kt_repr r) in r

inline_for_extraction let unknown_enum_repr_kt_as_repr (r:LP.unknown_enum_repr kt_enum) : Pure kt_repr
  (requires True) (ensures fun r -> known_kt_repr r == false) =
  [@inline_let] let _ = assert_norm(LP.list_mem r (LP.list_map snd kt_enum) == known_kt_repr r) in r

inline_for_extraction let key_of_tt (x:tt) : LP.maybe_enum_key kt_enum =
  match x with
  | Case_ka _ -> LP.Known (known_kt_as_enum_key Ka)
  | Case_kb _ -> LP.Known (known_kt_as_enum_key Kb)
  | Case_Unknown_kt v _ -> LP.Unknown (unknown_kt_as_enum_key v)

inline_for_extraction let tt_case_of_kt (x:kt) : Type0 =
  match x with
  | Ka -> U8.t
  | Kb -> U16.t
  | Unknown_kt _ -> squash False

unfold inline_for_extraction let tt_value_type (x:LP.maybe_enum_key kt_enum) =
  LP.dsum_type_of_tag' kt_enum tt_case_of_kt U32.t x

unfold inline_for_extraction let tt_refine (k:LP.maybe_enum_key kt_enum) (x:tt)
  : Pure (LP.refine_with_tag key_of_tt k)
  (requires key_of_tt x == k) (ensures fun y -> y == x) =
  [@inline_let] let _ = norm_spec [delta; iota; zeta] (key_of_tt x) in x

unfold inline_for_extraction let tt_type_of_known_case (k: LP.enum_key kt_enum)
  (x:kt) (q: squash ((k <: kt) == x))
  (#x' : LP.maybe_enum_key kt_enum) (y: tt_value_type x')
  : Pure (norm [delta_only [(`%tt_case_of_kt)]; iota] (tt_case_of_kt x))
  (requires (LP.Known k == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%tt_case_of_kt)]; iota] (tt_case_of_kt k) in y

unfold inline_for_extraction let tt_known_case (k: LP.enum_key kt_enum)
  (x: kt) (y: norm [delta_only [(`%tt_case_of_kt)]; iota] (tt_case_of_kt x))
  : Pure (tt_case_of_kt k) (requires (k == x)) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%tt_case_of_kt)] ; iota] (tt_case_of_kt x) in y

inline_for_extraction let synth_known_tt_cases (k:LP.enum_key kt_enum)
  (y:tt_value_type (LP.Known k)) : LP.refine_with_tag key_of_tt (LP.Known k) =
  match k with
  | Ka ->
    [@inline_let] let x : tt = Case_ka (tt_type_of_known_case k Ka () y) in
    [@inline_let] let _ = assert_norm (key_of_tt x == LP.Known Ka) in
    tt_refine (LP.Known Ka) x
  | Kb ->
    [@inline_let] let x : tt = Case_kb (tt_type_of_known_case k Kb () y) in
    [@inline_let] let _ = assert_norm (key_of_tt x == LP.Known Kb) in
    tt_refine (LP.Known Kb) x

inline_for_extraction let synth_tt_cases (x:LP.maybe_enum_key kt_enum)
  (y:tt_value_type x) : LP.refine_with_tag key_of_tt x =
  match x with
  | LP.Unknown v ->
    [@inline_let] let x : tt = Case_Unknown_kt (unknown_enum_repr_kt_as_repr v) y in
    [@inline_let] let _ = assert_norm (key_of_tt x == LP.Unknown v) in
    tt_refine (LP.Unknown v) x
  | LP.Known k -> synth_known_tt_cases k y

unfold inline_for_extraction let from_tt_case_of_kt (#x':kt) (x:kt)
  (y: norm [delta_only [(`%tt_case_of_kt)]; iota] (tt_case_of_kt x))
  : Pure (tt_case_of_kt x') (requires (x == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%tt_case_of_kt)] ; iota] (tt_case_of_kt x) in y

let synth_tt_cases_recip_pre (k:LP.maybe_enum_key kt_enum)
  (x:LP.refine_with_tag key_of_tt k) : GTot bool =
  match k with
  | LP.Known Ka -> Case_ka? x
  | LP.Known Kb -> Case_kb? x
  | LP.Known _ -> false
  | LP.Unknown _ -> Case_Unknown_kt? x

let synth_tt_cases_recip_pre_intro' (x: tt) : Lemma (synth_tt_cases_recip_pre (key_of_tt x) x) = ()
let synth_tt_cases_recip_pre_intro (k:LP.maybe_enum_key kt_enum)
  (x:LP.refine_with_tag key_of_tt k)
  : Lemma (synth_tt_cases_recip_pre k x == true) =
  synth_tt_cases_recip_pre_intro' x

inline_for_extraction let synth_tt_cases_recip (k:LP.maybe_enum_key kt_enum)
  (x:LP.refine_with_tag key_of_tt k) : (tt_value_type k) =
  match k with
  | LP.Unknown z ->
    [@inline_let] let _ = synth_tt_cases_recip_pre_intro (LP.Unknown z) x in
    (match x with Case_Unknown_kt _ y ->  (y <: tt_value_type k))
  | LP.Known k' ->
    match k' with
    | Ka -> [@inline_let] let _ = synth_tt_cases_recip_pre_intro (LP.Known Ka) x in
      (match x with Case_ka y -> tt_known_case k' Ka y)
    | Kb -> [@inline_let] let _ = synth_tt_cases_recip_pre_intro (LP.Known Kb) x in
      (match x with Case_kb y -> tt_known_case k' Kb y)
   | _ -> [@inline_let] let _ = synth_tt_cases_recip_pre_intro (LP.Known k') in false_elim ()


inline_for_extraction let tt_sum : LP.dsum = LP.make_dsum' kt_enum key_of_tt
  tt_case_of_kt U32.t synth_tt_cases synth_tt_cases_recip
  (_ by (LS.make_dsum_synth_case_recip_synth_case_known_tac ()))
  (_ by (LS.make_dsum_synth_case_recip_synth_case_unknown_tac ()))
  (_ by (LS.synth_case_synth_case_recip_tac ()))

noextract let parse_tt_cases (x:LP.dsum_known_key tt_sum)
  : k:LP.parser_kind & LP.parser k (tt_case_of_kt x) =
  match x with
  | Ka -> let u : (k: LP.parser_kind & LP.parser k (tt_case_of_kt Ka)) = (| _, LP.parse_u8 |) in u
  | Kb -> let u : (k: LP.parser_kind & LP.parser k (tt_case_of_kt Kb)) = (| _, LP.parse_u16 |) in u
  | _ -> (| _, LP.parse_false |)


noextract let serialize_tt_cases (x:LP.dsum_known_key tt_sum)
  : LP.serializer (dsnd (parse_tt_cases x)) =
  match x with
  | Ka -> let u : LP.serializer (dsnd (parse_tt_cases Ka)) = LP.serialize_u8 in u
  | Kb -> let u : LP.serializer (dsnd (parse_tt_cases Kb)) = LP.serialize_u16 in u
  | _ -> LP.serialize_false


inline_for_extraction noextract let parse32_tt_cases (x:LP.dsum_known_key tt_sum)
  : LS.parser32 (dsnd (parse_tt_cases x)) =
  match x with
  | Ka -> [@inline_let] let u : LS.parser32 (dsnd (parse_tt_cases Ka)) = LS.parse32_u8 in u
  | Kb -> [@inline_let] let u : LS.parser32 (dsnd (parse_tt_cases Kb)) = LS.parse32_u16 in u
  | _ -> LS.parse32_false


inline_for_extraction noextract let serialize32_tt_cases (x:LP.dsum_known_key tt_sum)
  : LS.serializer32 (serialize_tt_cases x) =
  match x with
  | Ka -> [@inline_let] let u : LS.serializer32 (serialize_tt_cases Ka) = LS.serialize32_u8 in u
  | Kb -> [@inline_let] let u : LS.serializer32 (serialize_tt_cases Kb) = LS.serialize32_u16 in u
  | _ -> LS.serialize32_false


inline_for_extraction noextract let size32_tt_cases (x:LP.dsum_known_key tt_sum)
  : LS.size32 (serialize_tt_cases x) =
  match x with
  | Ka -> [@inline_let] let u : LS.size32 (serialize_tt_cases Ka) = LS.size32_u8 in u
  | Kb -> [@inline_let] let u : LS.size32 (serialize_tt_cases Kb) = LS.size32_u16 in u
  | _ -> LS.size32_false


inline_for_extraction noextract let validate_tt_cases (x:LP.dsum_known_key tt_sum)
  : LL.validator (dsnd (parse_tt_cases x)) =
  match x with
  | Ka -> [@inline_let] let u : LL.validator (dsnd (parse_tt_cases Ka)) = (LL.validate_u8 ()) in u
  | Kb -> [@inline_let] let u : LL.validator (dsnd (parse_tt_cases Kb)) = (LL.validate_u16 ()) in u
  | _ -> LL.validate_false ()


inline_for_extraction noextract let jump_tt_cases (x:LP.dsum_known_key tt_sum)
  : LL.jumper (dsnd (parse_tt_cases x)) =
  match x with
  | Ka -> [@inline_let] let u : LL.jumper (dsnd (parse_tt_cases Ka)) = LL.jump_u8 in u
  | Kb -> [@inline_let] let u : LL.jumper (dsnd (parse_tt_cases Kb)) = LL.jump_u16 in u
  | _ -> LL.jump_false

(* END QuackyDucky output *)

let _ : squash (LL.weaken_parse_dsum_cases_kind tt_sum parse_tt_cases LP.parse_u32_kind == parse_t_kind) = _ by (FStar.Tactics.trefl ())

(* Alas, the two types (t k) and (LP.refine_with_tag key_of_tt (synth_kt_inv k)) are not equal. So we need to do a synth. *)

inline_for_extraction
let synth_t (k: kt) (x: LP.refine_with_tag key_of_tt (synth_kt_inv k)) : Tot (t k) = x

inline_for_extraction
let synth_t_recip (k: kt) (x: t k) : Tot (LP.refine_with_tag key_of_tt (synth_kt_inv k)) = x

let synth_t_inj (k: kt) : Lemma (LP.synth_injective (synth_t k)) = ()

let synth_t_inv (k: kt) : Lemma (LP.synth_inverse (synth_t k) (synth_t_recip k)) = ()

let parse_t k = LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32 (synth_kt_inv k) `LP.parse_synth` synth_t k

let serialize_t k =
  LP.serialize_synth
    _
    (synth_t k)
    (LP.serialize_dsum_cases tt_sum parse_tt_cases serialize_tt_cases LP.parse_u32 LP.serialize_u32 (synth_kt_inv k))
    (synth_t_recip k)
    ()

let parse32_t k =
  LS.parse32_synth'
    (LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32 (synth_kt_inv k))
    (synth_t k)
    (LS.parse32_compose_context synth_kt_inv (LP.refine_with_tag key_of_tt) 
      (LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32)
      (LS.parse32_dsum_cases tt_sum parse_tt_cases parse32_tt_cases LP.parse_u32 LS.parse32_u32 (_ by (LS.dep_enum_destr_tac ())))
      k
    )
    ()

let serialize32_t k =
  LS.serialize32_synth'
    (LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32 (synth_kt_inv k))
    (synth_t k)
    (LP.serialize_dsum_cases tt_sum parse_tt_cases serialize_tt_cases LP.parse_u32 LP.serialize_u32 (synth_kt_inv k))
    (LS.serialize32_compose_context synth_kt_inv (LP.refine_with_tag key_of_tt)
      (LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32)
      (LP.serialize_dsum_cases tt_sum parse_tt_cases serialize_tt_cases LP.parse_u32 LP.serialize_u32)
      (LS.serialize32_dsum_cases tt_sum parse_tt_cases serialize_tt_cases serialize32_tt_cases LS.serialize32_u32 (_ by (LS.dep_enum_destr_tac ())))
      k
    )
    (synth_t_recip k)
    ()

let size32_t k =
  LS.size32_synth'
    (LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32 (synth_kt_inv k))
    (synth_t k)
    (LP.serialize_dsum_cases tt_sum parse_tt_cases serialize_tt_cases LP.parse_u32 LP.serialize_u32 (synth_kt_inv k))
    (LS.size32_compose_context synth_kt_inv (LP.refine_with_tag key_of_tt)
      (LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32)
      (LP.serialize_dsum_cases tt_sum parse_tt_cases serialize_tt_cases LP.parse_u32 LP.serialize_u32)
      (LS.size32_dsum_cases tt_sum parse_tt_cases serialize_tt_cases size32_tt_cases LS.size32_u32 (_ by (LS.dep_enum_destr_tac ())))
      k
    )
    (synth_t_recip k)
    ()

let validate_t k =
  LL.validate_synth
    (LL.validate_compose_context synth_kt_inv (LP.refine_with_tag key_of_tt)
      (LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32)
      (LL.validate_dsum_cases tt_sum parse_tt_cases validate_tt_cases (LL.validate_u32 ()) (_ by (LS.dep_enum_destr_tac ())))
      k
    )
    (synth_t k)
    ()

let jump_t k =
  LL.jump_synth
    (LL.jump_compose_context synth_kt_inv (LP.refine_with_tag key_of_tt)
      (LP.parse_dsum_cases tt_sum parse_tt_cases LP.parse_u32)
      (LL.jump_dsum_cases tt_sum parse_tt_cases jump_tt_cases LL.jump_u32 (_ by (LS.dep_enum_destr_tac ())))
      k
    )
    (synth_t k)
    ()

let main argc argv =
  C.EXIT_SUCCESS

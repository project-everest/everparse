module Parse_alertLevel

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let alertLevel_enum : LP.enum alertLevel U8.t =
  [@inline_let] let e = [
    Warning, 1z;
    Fatal, 2z;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_alertLevel' (x:LP.maybe_enum_key alertLevel_enum) : Tot alertLevel' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd alertLevel_enum)) in
    Unknown_alertLevel v

let lemma_synth_alertLevel'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key alertLevel_enum).
    synth_alertLevel' x1 == synth_alertLevel' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_alertLevel'_inv (x:alertLevel') : Tot (LP.maybe_enum_key alertLevel_enum) = 
  match x with
  | Unknown_alertLevel y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd alertLevel_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst alertLevel_enum)) in
    LP.Known (x1 <: LP.enum_key alertLevel_enum)

let lemma_synth_alertLevel'_inv () : Lemma
  (forall (x: LP.maybe_enum_key alertLevel_enum). synth_alertLevel'_inv (synth_alertLevel' x) == x) = ()

let parse_maybe_alertLevel_key : LP.parser _ (LP.maybe_enum_key alertLevel_enum) =
  LP.parse_maybe_enum_key LP.parse_u8 alertLevel_enum

let serialize_maybe_alertLevel_key : LP.serializer parse_maybe_alertLevel_key =
  LP.serialize_maybe_enum_key LP.parse_u8 LP.serialize_u8 alertLevel_enum

let parse_alertLevel' : LP.parser _ alertLevel' =
  lemma_synth_alertLevel'_inj ();
  parse_maybe_alertLevel_key `LP.parse_synth` synth_alertLevel'

let serialize_alertLevel' : LP.serializer parse_alertLevel' =
  lemma_synth_alertLevel'_inj ();
  lemma_synth_alertLevel'_inv ();
  LP.serialize_synth _ synth_alertLevel' serialize_maybe_alertLevel_key synth_alertLevel'_inv ()

inline_for_extraction let parse32_maybe_alertLevel_key : LP.parser32 parse_maybe_alertLevel_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u8 alertLevel_enum parse_maybe_alertLevel_key ())

inline_for_extraction let parse32_alertLevel' : LP.parser32 parse_alertLevel' =
  lemma_synth_alertLevel'_inj ();
  LP.parse32_synth _ synth_alertLevel' (fun x->synth_alertLevel' x) parse32_maybe_alertLevel_key ()

inline_for_extraction let serialize32_maybe_alertLevel_key : LP.serializer32 serialize_maybe_alertLevel_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u8 #LP.serialize_u8 // FIXME(implicits for machine int parsers)
    LP.serialize32_u8 alertLevel_enum serialize_maybe_alertLevel_key ())

inline_for_extraction let serialize32_alertLevel' : LP.serializer32 serialize_alertLevel' =
  lemma_synth_alertLevel'_inj ();
  lemma_synth_alertLevel'_inv ();
  LP.serialize32_synth _ synth_alertLevel' _ serialize32_maybe_alertLevel_key synth_alertLevel'_inv (fun x->synth_alertLevel'_inv x) ()

let alertLevel_bytes x = serialize32_alertLevel' x <: LP.bytes32

let parse_alertLevel' x =
  LP.parse32_total parse32_alertLevel' v;
  match parse32_alertLevel' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_alertLevel x =
  LP.parse32_total parse32_alertLevel' v;
  match parse32_alertLevel' x with
  | Some (v, _) -> if v = Unknown_alertLevel then None else Some v
  | None -> None


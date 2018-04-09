module Parse_extensionType

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let extensionType_enum : LP.enum extensionType U16.t =
  [@inline_let] let e = [
    Supported_groups, 10us;
    Signature_algorithms, 13us;
    Key_share, 40us;
    Pre_shared_key, 41us;
    Early_data, 42us;
    Cookie, 44us;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_extensionType' (x:LP.maybe_enum_key extensionType_enum) : Tot extensionType' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd extensionType_enum)) in
    Unknown_extensionType v

let lemma_synth_extensionType'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key extensionType_enum).
    synth_extensionType' x1 == synth_extensionType' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_extensionType'_inv (x:extensionType') : Tot (LP.maybe_enum_key extensionType_enum) = 
  match x with
  | Unknown_extensionType y ->
    [@inline_let] let v : U16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd extensionType_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst extensionType_enum)) in
    LP.Known (x1 <: LP.enum_key extensionType_enum)

let lemma_synth_extensionType'_inv () : Lemma
  (forall (x: LP.maybe_enum_key extensionType_enum). synth_extensionType'_inv (synth_extensionType' x) == x) = ()

let parse_maybe_extensionType_key : LP.parser _ (LP.maybe_enum_key extensionType_enum) =
  LP.parse_maybe_enum_key LP.parse_u16 extensionType_enum

let serialize_maybe_extensionType_key : LP.serializer parse_maybe_extensionType_key =
  LP.serialize_maybe_enum_key LP.parse_u16 LP.serialize_u16 extensionType_enum

let parse_extensionType' : LP.parser _ extensionType' =
  lemma_synth_extensionType'_inj ();
  parse_maybe_extensionType_key `LP.parse_synth` synth_extensionType'

let serialize_extensionType' : LP.serializer parse_extensionType' =
  lemma_synth_extensionType'_inj ();
  lemma_synth_extensionType'_inv ();
  LP.serialize_synth _ synth_extensionType' serialize_maybe_extensionType_key synth_extensionType'_inv ()

inline_for_extraction let parse32_maybe_extensionType_key : LP.parser32 parse_maybe_extensionType_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u16 extensionType_enum parse_maybe_extensionType_key ())

inline_for_extraction let parse32_extensionType' : LP.parser32 parse_extensionType' =
  lemma_synth_extensionType'_inj ();
  LP.parse32_synth _ synth_extensionType' (fun x->synth_extensionType' x) parse32_maybe_extensionType_key ()

inline_for_extraction let serialize32_maybe_extensionType_key : LP.serializer32 serialize_maybe_extensionType_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u16 #LP.serialize_u16 // FIXME(implicits for machine int parsers)
    LP.serialize32_u16 extensionType_enum serialize_maybe_extensionType_key ())

inline_for_extraction let serialize32_extensionType' : LP.serializer32 serialize_extensionType' =
  lemma_synth_extensionType'_inj ();
  lemma_synth_extensionType'_inv ();
  LP.serialize32_synth _ synth_extensionType' _ serialize32_maybe_extensionType_key synth_extensionType'_inv (fun x->synth_extensionType'_inv x) ()

let extensionType_bytes x = serialize32_extensionType' x <: LP.bytes32

let parse_extensionType' x =
  LP.parse32_total parse32_extensionType' v;
  match parse32_extensionType' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_extensionType x =
  LP.parse32_total parse32_extensionType' v;
  match parse32_extensionType' x with
  | Some (v, _) -> if v = Unknown_extensionType then None else Some v
  | None -> None


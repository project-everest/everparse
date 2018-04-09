module Parse_ticketExtensionType

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let ticketExtensionType_enum : LP.enum ticketExtensionType U16.t =
  [@inline_let] let e = [
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_ticketExtensionType' (x:LP.maybe_enum_key ticketExtensionType_enum) : Tot ticketExtensionType' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd ticketExtensionType_enum)) in
    Unknown_ticketExtensionType v

let lemma_synth_ticketExtensionType'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key ticketExtensionType_enum).
    synth_ticketExtensionType' x1 == synth_ticketExtensionType' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_ticketExtensionType'_inv (x:ticketExtensionType') : Tot (LP.maybe_enum_key ticketExtensionType_enum) = 
  match x with
  | Unknown_ticketExtensionType y ->
    [@inline_let] let v : U16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd ticketExtensionType_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst ticketExtensionType_enum)) in
    LP.Known (x1 <: LP.enum_key ticketExtensionType_enum)

let lemma_synth_ticketExtensionType'_inv () : Lemma
  (forall (x: LP.maybe_enum_key ticketExtensionType_enum). synth_ticketExtensionType'_inv (synth_ticketExtensionType' x) == x) = ()

let parse_maybe_ticketExtensionType_key : LP.parser _ (LP.maybe_enum_key ticketExtensionType_enum) =
  LP.parse_maybe_enum_key LP.parse_u16 ticketExtensionType_enum

let serialize_maybe_ticketExtensionType_key : LP.serializer parse_maybe_ticketExtensionType_key =
  LP.serialize_maybe_enum_key LP.parse_u16 LP.serialize_u16 ticketExtensionType_enum

let parse_ticketExtensionType' : LP.parser _ ticketExtensionType' =
  lemma_synth_ticketExtensionType'_inj ();
  parse_maybe_ticketExtensionType_key `LP.parse_synth` synth_ticketExtensionType'

let serialize_ticketExtensionType' : LP.serializer parse_ticketExtensionType' =
  lemma_synth_ticketExtensionType'_inj ();
  lemma_synth_ticketExtensionType'_inv ();
  LP.serialize_synth _ synth_ticketExtensionType' serialize_maybe_ticketExtensionType_key synth_ticketExtensionType'_inv ()

inline_for_extraction let parse32_maybe_ticketExtensionType_key : LP.parser32 parse_maybe_ticketExtensionType_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u16 ticketExtensionType_enum parse_maybe_ticketExtensionType_key ())

inline_for_extraction let parse32_ticketExtensionType' : LP.parser32 parse_ticketExtensionType' =
  lemma_synth_ticketExtensionType'_inj ();
  LP.parse32_synth _ synth_ticketExtensionType' (fun x->synth_ticketExtensionType' x) parse32_maybe_ticketExtensionType_key ()

inline_for_extraction let serialize32_maybe_ticketExtensionType_key : LP.serializer32 serialize_maybe_ticketExtensionType_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u16 #LP.serialize_u16 // FIXME(implicits for machine int parsers)
    LP.serialize32_u16 ticketExtensionType_enum serialize_maybe_ticketExtensionType_key ())

inline_for_extraction let serialize32_ticketExtensionType' : LP.serializer32 serialize_ticketExtensionType' =
  lemma_synth_ticketExtensionType'_inj ();
  lemma_synth_ticketExtensionType'_inv ();
  LP.serialize32_synth _ synth_ticketExtensionType' _ serialize32_maybe_ticketExtensionType_key synth_ticketExtensionType'_inv (fun x->synth_ticketExtensionType'_inv x) ()

let ticketExtensionType_bytes x = serialize32_ticketExtensionType' x <: LP.bytes32

let parse_ticketExtensionType' x =
  LP.parse32_total parse32_ticketExtensionType' v;
  match parse32_ticketExtensionType' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_ticketExtensionType x =
  LP.parse32_total parse32_ticketExtensionType' v;
  match parse32_ticketExtensionType' x with
  | Some (v, _) -> if v = Unknown_ticketExtensionType then None else Some v
  | None -> None


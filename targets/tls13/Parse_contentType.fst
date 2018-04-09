module Parse_contentType

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let contentType_enum : LP.enum contentType U8.t =
  [@inline_let] let e = [
    Alert, 21z;
    Handshake, 22z;
    Application_data, 23z;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_contentType' (x:LP.maybe_enum_key contentType_enum) : Tot contentType' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd contentType_enum)) in
    Unknown_contentType v

let lemma_synth_contentType'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key contentType_enum).
    synth_contentType' x1 == synth_contentType' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_contentType'_inv (x:contentType') : Tot (LP.maybe_enum_key contentType_enum) = 
  match x with
  | Unknown_contentType y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd contentType_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst contentType_enum)) in
    LP.Known (x1 <: LP.enum_key contentType_enum)

let lemma_synth_contentType'_inv () : Lemma
  (forall (x: LP.maybe_enum_key contentType_enum). synth_contentType'_inv (synth_contentType' x) == x) = ()

let parse_maybe_contentType_key : LP.parser _ (LP.maybe_enum_key contentType_enum) =
  LP.parse_maybe_enum_key LP.parse_u8 contentType_enum

let serialize_maybe_contentType_key : LP.serializer parse_maybe_contentType_key =
  LP.serialize_maybe_enum_key LP.parse_u8 LP.serialize_u8 contentType_enum

let parse_contentType' : LP.parser _ contentType' =
  lemma_synth_contentType'_inj ();
  parse_maybe_contentType_key `LP.parse_synth` synth_contentType'

let serialize_contentType' : LP.serializer parse_contentType' =
  lemma_synth_contentType'_inj ();
  lemma_synth_contentType'_inv ();
  LP.serialize_synth _ synth_contentType' serialize_maybe_contentType_key synth_contentType'_inv ()

inline_for_extraction let parse32_maybe_contentType_key : LP.parser32 parse_maybe_contentType_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u8 contentType_enum parse_maybe_contentType_key ())

inline_for_extraction let parse32_contentType' : LP.parser32 parse_contentType' =
  lemma_synth_contentType'_inj ();
  LP.parse32_synth _ synth_contentType' (fun x->synth_contentType' x) parse32_maybe_contentType_key ()

inline_for_extraction let serialize32_maybe_contentType_key : LP.serializer32 serialize_maybe_contentType_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u8 #LP.serialize_u8 // FIXME(implicits for machine int parsers)
    LP.serialize32_u8 contentType_enum serialize_maybe_contentType_key ())

inline_for_extraction let serialize32_contentType' : LP.serializer32 serialize_contentType' =
  lemma_synth_contentType'_inj ();
  lemma_synth_contentType'_inv ();
  LP.serialize32_synth _ synth_contentType' _ serialize32_maybe_contentType_key synth_contentType'_inv (fun x->synth_contentType'_inv x) ()

let contentType_bytes x = serialize32_contentType' x <: LP.bytes32

let parse_contentType' x =
  LP.parse32_total parse32_contentType' v;
  match parse32_contentType' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_contentType x =
  LP.parse32_total parse32_contentType' v;
  match parse32_contentType' x with
  | Some (v, _) -> if v = Unknown_contentType then None else Some v
  | None -> None


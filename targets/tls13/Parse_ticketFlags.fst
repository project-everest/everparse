module Parse_ticketFlags

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let ticketFlags_enum : LP.enum ticketFlags U32.t =
  [@inline_let] let e = [
    Allow_early_data, 1ul;
    Allow_dhe_resumption, 2ul;
    Allow_psk_resumption, 4ul;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_ticketFlags' (x:LP.maybe_enum_key ticketFlags_enum) : Tot ticketFlags' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U32.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd ticketFlags_enum)) in
    Unknown_ticketFlags v

let lemma_synth_ticketFlags'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key ticketFlags_enum).
    synth_ticketFlags' x1 == synth_ticketFlags' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_ticketFlags'_inv (x:ticketFlags') : Tot (LP.maybe_enum_key ticketFlags_enum) = 
  match x with
  | Unknown_ticketFlags y ->
    [@inline_let] let v : U32.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd ticketFlags_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst ticketFlags_enum)) in
    LP.Known (x1 <: LP.enum_key ticketFlags_enum)

let lemma_synth_ticketFlags'_inv () : Lemma
  (forall (x: LP.maybe_enum_key ticketFlags_enum). synth_ticketFlags'_inv (synth_ticketFlags' x) == x) = ()

let parse_maybe_ticketFlags_key : LP.parser _ (LP.maybe_enum_key ticketFlags_enum) =
  LP.parse_maybe_enum_key LP.parse_u32 ticketFlags_enum

let serialize_maybe_ticketFlags_key : LP.serializer parse_maybe_ticketFlags_key =
  LP.serialize_maybe_enum_key LP.parse_u32 LP.serialize_u32 ticketFlags_enum

let parse_ticketFlags' : LP.parser _ ticketFlags' =
  lemma_synth_ticketFlags'_inj ();
  parse_maybe_ticketFlags_key `LP.parse_synth` synth_ticketFlags'

let serialize_ticketFlags' : LP.serializer parse_ticketFlags' =
  lemma_synth_ticketFlags'_inj ();
  lemma_synth_ticketFlags'_inv ();
  LP.serialize_synth _ synth_ticketFlags' serialize_maybe_ticketFlags_key synth_ticketFlags'_inv ()

inline_for_extraction let parse32_maybe_ticketFlags_key : LP.parser32 parse_maybe_ticketFlags_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u32 ticketFlags_enum parse_maybe_ticketFlags_key ())

inline_for_extraction let parse32_ticketFlags' : LP.parser32 parse_ticketFlags' =
  lemma_synth_ticketFlags'_inj ();
  LP.parse32_synth _ synth_ticketFlags' (fun x->synth_ticketFlags' x) parse32_maybe_ticketFlags_key ()

inline_for_extraction let serialize32_maybe_ticketFlags_key : LP.serializer32 serialize_maybe_ticketFlags_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u32 #LP.serialize_u32 // FIXME(implicits for machine int parsers)
    LP.serialize32_u32 ticketFlags_enum serialize_maybe_ticketFlags_key ())

inline_for_extraction let serialize32_ticketFlags' : LP.serializer32 serialize_ticketFlags' =
  lemma_synth_ticketFlags'_inj ();
  lemma_synth_ticketFlags'_inv ();
  LP.serialize32_synth _ synth_ticketFlags' _ serialize32_maybe_ticketFlags_key synth_ticketFlags'_inv (fun x->synth_ticketFlags'_inv x) ()

let ticketFlags_bytes x = serialize32_ticketFlags' x <: LP.bytes32

let parse_ticketFlags' x =
  LP.parse32_total parse32_ticketFlags' v;
  match parse32_ticketFlags' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_ticketFlags x =
  LP.parse32_total parse32_ticketFlags' v;
  match parse32_ticketFlags' x with
  | Some (v, _) -> if v = Unknown_ticketFlags then None else Some v
  | None -> None


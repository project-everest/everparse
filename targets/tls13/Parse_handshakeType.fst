module Parse_handshakeType

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let handshakeType_enum : LP.enum handshakeType U8.t =
  [@inline_let] let e = [
    Client_hello, 1z;
    Server_hello, 2z;
    New_session_ticket, 4z;
    Hello_retry_request, 6z;
    Encrypted_extensions, 8z;
    Certificate, 11z;
    Certificate_request, 13z;
    Certificate_verify, 15z;
    Finished, 20z;
    Key_update, 24z;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_handshakeType' (x:LP.maybe_enum_key handshakeType_enum) : Tot handshakeType' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd handshakeType_enum)) in
    Unknown_handshakeType v

let lemma_synth_handshakeType'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key handshakeType_enum).
    synth_handshakeType' x1 == synth_handshakeType' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_handshakeType'_inv (x:handshakeType') : Tot (LP.maybe_enum_key handshakeType_enum) = 
  match x with
  | Unknown_handshakeType y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd handshakeType_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst handshakeType_enum)) in
    LP.Known (x1 <: LP.enum_key handshakeType_enum)

let lemma_synth_handshakeType'_inv () : Lemma
  (forall (x: LP.maybe_enum_key handshakeType_enum). synth_handshakeType'_inv (synth_handshakeType' x) == x) = ()

let parse_maybe_handshakeType_key : LP.parser _ (LP.maybe_enum_key handshakeType_enum) =
  LP.parse_maybe_enum_key LP.parse_u8 handshakeType_enum

let serialize_maybe_handshakeType_key : LP.serializer parse_maybe_handshakeType_key =
  LP.serialize_maybe_enum_key LP.parse_u8 LP.serialize_u8 handshakeType_enum

let parse_handshakeType' : LP.parser _ handshakeType' =
  lemma_synth_handshakeType'_inj ();
  parse_maybe_handshakeType_key `LP.parse_synth` synth_handshakeType'

let serialize_handshakeType' : LP.serializer parse_handshakeType' =
  lemma_synth_handshakeType'_inj ();
  lemma_synth_handshakeType'_inv ();
  LP.serialize_synth _ synth_handshakeType' serialize_maybe_handshakeType_key synth_handshakeType'_inv ()

inline_for_extraction let parse32_maybe_handshakeType_key : LP.parser32 parse_maybe_handshakeType_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u8 handshakeType_enum parse_maybe_handshakeType_key ())

inline_for_extraction let parse32_handshakeType' : LP.parser32 parse_handshakeType' =
  lemma_synth_handshakeType'_inj ();
  LP.parse32_synth _ synth_handshakeType' (fun x->synth_handshakeType' x) parse32_maybe_handshakeType_key ()

inline_for_extraction let serialize32_maybe_handshakeType_key : LP.serializer32 serialize_maybe_handshakeType_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u8 #LP.serialize_u8 // FIXME(implicits for machine int parsers)
    LP.serialize32_u8 handshakeType_enum serialize_maybe_handshakeType_key ())

inline_for_extraction let serialize32_handshakeType' : LP.serializer32 serialize_handshakeType' =
  lemma_synth_handshakeType'_inj ();
  lemma_synth_handshakeType'_inv ();
  LP.serialize32_synth _ synth_handshakeType' _ serialize32_maybe_handshakeType_key synth_handshakeType'_inv (fun x->synth_handshakeType'_inv x) ()

let handshakeType_bytes x = serialize32_handshakeType' x <: LP.bytes32

let parse_handshakeType' x =
  LP.parse32_total parse32_handshakeType' v;
  match parse32_handshakeType' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_handshakeType x =
  LP.parse32_total parse32_handshakeType' v;
  match parse32_handshakeType' x with
  | Some (v, _) -> if v = Unknown_handshakeType then None else Some v
  | None -> None


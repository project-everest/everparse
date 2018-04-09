module Parse_alertDescription

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let alertDescription_enum : LP.enum alertDescription U8.t =
  [@inline_let] let e = [
    Close_notify, 0z;
    End_of_early_data, 1z;
    Unexpected_message, 10z;
    Bad_record_mac, 20z;
    Record_overflow, 22z;
    Handshake_failure, 40z;
    Bad_certificate, 42z;
    Unsupported_certificate, 43z;
    Certificate_revoked, 44z;
    Certificate_expired, 45z;
    Certificate_unknown, 46z;
    Illegal_parameter, 47z;
    Unknown_ca, 48z;
    Access_denied, 49z;
    Decode_error, 50z;
    Decrypt_error, 51z;
    Protocol_version, 70z;
    Insufficient_security, 71z;
    Internal_error, 80z;
    Inappropriate_fallback, 86z;
    User_canceled, 90z;
    Missing_extension, 109z;
    Unsupported_extension, 110z;
    Certificate_unobtainable, 111z;
    Unrecognized_name, 112z;
    Bad_certificate_status_response, 113z;
    Bad_certificate_hash_value, 114z;
    Unknown_psk_identity, 115z;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_alertDescription' (x:LP.maybe_enum_key alertDescription_enum) : Tot alertDescription' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd alertDescription_enum)) in
    Unknown_alertDescription v

let lemma_synth_alertDescription'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key alertDescription_enum).
    synth_alertDescription' x1 == synth_alertDescription' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_alertDescription'_inv (x:alertDescription') : Tot (LP.maybe_enum_key alertDescription_enum) = 
  match x with
  | Unknown_alertDescription y ->
    [@inline_let] let v : U8.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd alertDescription_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst alertDescription_enum)) in
    LP.Known (x1 <: LP.enum_key alertDescription_enum)

let lemma_synth_alertDescription'_inv () : Lemma
  (forall (x: LP.maybe_enum_key alertDescription_enum). synth_alertDescription'_inv (synth_alertDescription' x) == x) = ()

let parse_maybe_alertDescription_key : LP.parser _ (LP.maybe_enum_key alertDescription_enum) =
  LP.parse_maybe_enum_key LP.parse_u8 alertDescription_enum

let serialize_maybe_alertDescription_key : LP.serializer parse_maybe_alertDescription_key =
  LP.serialize_maybe_enum_key LP.parse_u8 LP.serialize_u8 alertDescription_enum

let parse_alertDescription' : LP.parser _ alertDescription' =
  lemma_synth_alertDescription'_inj ();
  parse_maybe_alertDescription_key `LP.parse_synth` synth_alertDescription'

let serialize_alertDescription' : LP.serializer parse_alertDescription' =
  lemma_synth_alertDescription'_inj ();
  lemma_synth_alertDescription'_inv ();
  LP.serialize_synth _ synth_alertDescription' serialize_maybe_alertDescription_key synth_alertDescription'_inv ()

inline_for_extraction let parse32_maybe_alertDescription_key : LP.parser32 parse_maybe_alertDescription_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u8 alertDescription_enum parse_maybe_alertDescription_key ())

inline_for_extraction let parse32_alertDescription' : LP.parser32 parse_alertDescription' =
  lemma_synth_alertDescription'_inj ();
  LP.parse32_synth _ synth_alertDescription' (fun x->synth_alertDescription' x) parse32_maybe_alertDescription_key ()

inline_for_extraction let serialize32_maybe_alertDescription_key : LP.serializer32 serialize_maybe_alertDescription_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u8 #LP.serialize_u8 // FIXME(implicits for machine int parsers)
    LP.serialize32_u8 alertDescription_enum serialize_maybe_alertDescription_key ())

inline_for_extraction let serialize32_alertDescription' : LP.serializer32 serialize_alertDescription' =
  lemma_synth_alertDescription'_inj ();
  lemma_synth_alertDescription'_inv ();
  LP.serialize32_synth _ synth_alertDescription' _ serialize32_maybe_alertDescription_key synth_alertDescription'_inv (fun x->synth_alertDescription'_inv x) ()

let alertDescription_bytes x = serialize32_alertDescription' x <: LP.bytes32

let parse_alertDescription' x =
  LP.parse32_total parse32_alertDescription' v;
  match parse32_alertDescription' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_alertDescription x =
  LP.parse32_total parse32_alertDescription' v;
  match parse32_alertDescription' x with
  | Some (v, _) -> if v = Unknown_alertDescription then None else Some v
  | None -> None


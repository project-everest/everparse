module Parse_signatureScheme

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let signatureScheme_enum : LP.enum signatureScheme U16.t =
  [@inline_let] let e = [
    Rsa_pkcs1_sha1, 513us;
    Rsa_pkcs1_sha256, 1025us;
    Rsa_pkcs1_sha384, 1281us;
    Rsa_pkcs1_sha512, 1537us;
    Ecdsa_secp256r1_sha256, 1027us;
    Ecdsa_secp384r1_sha384, 1283us;
    Ecdsa_secp521r1_sha512, 1539us;
    Rsa_pss_sha256, 1792us;
    Rsa_pss_sha384, 1793us;
    Rsa_pss_sha512, 1794us;
    Ed25519, 1795us;
    Ed448, 1796us;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_signatureScheme' (x:LP.maybe_enum_key signatureScheme_enum) : Tot signatureScheme' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd signatureScheme_enum)) in
    Unknown_signatureScheme v

let lemma_synth_signatureScheme'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key signatureScheme_enum).
    synth_signatureScheme' x1 == synth_signatureScheme' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_signatureScheme'_inv (x:signatureScheme') : Tot (LP.maybe_enum_key signatureScheme_enum) = 
  match x with
  | Unknown_signatureScheme y ->
    [@inline_let] let v : U16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd signatureScheme_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst signatureScheme_enum)) in
    LP.Known (x1 <: LP.enum_key signatureScheme_enum)

let lemma_synth_signatureScheme'_inv () : Lemma
  (forall (x: LP.maybe_enum_key signatureScheme_enum). synth_signatureScheme'_inv (synth_signatureScheme' x) == x) = ()

let parse_maybe_signatureScheme_key : LP.parser _ (LP.maybe_enum_key signatureScheme_enum) =
  LP.parse_maybe_enum_key LP.parse_u16 signatureScheme_enum

let serialize_maybe_signatureScheme_key : LP.serializer parse_maybe_signatureScheme_key =
  LP.serialize_maybe_enum_key LP.parse_u16 LP.serialize_u16 signatureScheme_enum

let parse_signatureScheme' : LP.parser _ signatureScheme' =
  lemma_synth_signatureScheme'_inj ();
  parse_maybe_signatureScheme_key `LP.parse_synth` synth_signatureScheme'

let serialize_signatureScheme' : LP.serializer parse_signatureScheme' =
  lemma_synth_signatureScheme'_inj ();
  lemma_synth_signatureScheme'_inv ();
  LP.serialize_synth _ synth_signatureScheme' serialize_maybe_signatureScheme_key synth_signatureScheme'_inv ()

inline_for_extraction let parse32_maybe_signatureScheme_key : LP.parser32 parse_maybe_signatureScheme_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u16 signatureScheme_enum parse_maybe_signatureScheme_key ())

inline_for_extraction let parse32_signatureScheme' : LP.parser32 parse_signatureScheme' =
  lemma_synth_signatureScheme'_inj ();
  LP.parse32_synth _ synth_signatureScheme' (fun x->synth_signatureScheme' x) parse32_maybe_signatureScheme_key ()

inline_for_extraction let serialize32_maybe_signatureScheme_key : LP.serializer32 serialize_maybe_signatureScheme_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u16 #LP.serialize_u16 // FIXME(implicits for machine int parsers)
    LP.serialize32_u16 signatureScheme_enum serialize_maybe_signatureScheme_key ())

inline_for_extraction let serialize32_signatureScheme' : LP.serializer32 serialize_signatureScheme' =
  lemma_synth_signatureScheme'_inj ();
  lemma_synth_signatureScheme'_inv ();
  LP.serialize32_synth _ synth_signatureScheme' _ serialize32_maybe_signatureScheme_key synth_signatureScheme'_inv (fun x->synth_signatureScheme'_inv x) ()

let signatureScheme_bytes x = serialize32_signatureScheme' x <: LP.bytes32

let parse_signatureScheme' x =
  LP.parse32_total parse32_signatureScheme' v;
  match parse32_signatureScheme' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_signatureScheme x =
  LP.parse32_total parse32_signatureScheme' v;
  match parse32_signatureScheme' x with
  | Some (v, _) -> if v = Unknown_signatureScheme then None else Some v
  | None -> None


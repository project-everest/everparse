module Parse_namedGroup

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let namedGroup_enum : LP.enum namedGroup U16.t =
  [@inline_let] let e = [
    Secp256r1, 23us;
    Secp384r1, 24us;
    Secp521r1, 25us;
    X25519, 29us;
    X448, 30us;
    Ffdhe2048, 256us;
    Ffdhe3072, 257us;
    Ffdhe4096, 258us;
    Ffdhe6144, 259us;
    Ffdhe8192, 260us;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_namedGroup' (x:LP.maybe_enum_key namedGroup_enum) : Tot namedGroup' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : U16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd namedGroup_enum)) in
    Unknown_namedGroup v

let lemma_synth_namedGroup'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key namedGroup_enum).
    synth_namedGroup' x1 == synth_namedGroup' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_namedGroup'_inv (x:namedGroup') : Tot (LP.maybe_enum_key namedGroup_enum) = 
  match x with
  | Unknown_namedGroup y ->
    [@inline_let] let v : U16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd namedGroup_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst namedGroup_enum)) in
    LP.Known (x1 <: LP.enum_key namedGroup_enum)

let lemma_synth_namedGroup'_inv () : Lemma
  (forall (x: LP.maybe_enum_key namedGroup_enum). synth_namedGroup'_inv (synth_namedGroup' x) == x) = ()

let parse_maybe_namedGroup_key : LP.parser _ (LP.maybe_enum_key namedGroup_enum) =
  LP.parse_maybe_enum_key LP.parse_u16 namedGroup_enum

let serialize_maybe_namedGroup_key : LP.serializer parse_maybe_namedGroup_key =
  LP.serialize_maybe_enum_key LP.parse_u16 LP.serialize_u16 namedGroup_enum

let parse_namedGroup' : LP.parser _ namedGroup' =
  lemma_synth_namedGroup'_inj ();
  parse_maybe_namedGroup_key `LP.parse_synth` synth_namedGroup'

let serialize_namedGroup' : LP.serializer parse_namedGroup' =
  lemma_synth_namedGroup'_inj ();
  lemma_synth_namedGroup'_inv ();
  LP.serialize_synth _ synth_namedGroup' serialize_maybe_namedGroup_key synth_namedGroup'_inv ()

inline_for_extraction let parse32_maybe_namedGroup_key : LP.parser32 parse_maybe_namedGroup_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u16 namedGroup_enum parse_maybe_namedGroup_key ())

inline_for_extraction let parse32_namedGroup' : LP.parser32 parse_namedGroup' =
  lemma_synth_namedGroup'_inj ();
  LP.parse32_synth _ synth_namedGroup' (fun x->synth_namedGroup' x) parse32_maybe_namedGroup_key ()

inline_for_extraction let serialize32_maybe_namedGroup_key : LP.serializer32 serialize_maybe_namedGroup_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u16 #LP.serialize_u16 // FIXME(implicits for machine int parsers)
    LP.serialize32_u16 namedGroup_enum serialize_maybe_namedGroup_key ())

inline_for_extraction let serialize32_namedGroup' : LP.serializer32 serialize_namedGroup' =
  lemma_synth_namedGroup'_inj ();
  lemma_synth_namedGroup'_inv ();
  LP.serialize32_synth _ synth_namedGroup' _ serialize32_maybe_namedGroup_key synth_namedGroup'_inv (fun x->synth_namedGroup'_inv x) ()

let namedGroup_bytes x = serialize32_namedGroup' x <: LP.bytes32

let parse_namedGroup' x =
  LP.parse32_total parse32_namedGroup' v;
  match parse32_namedGroup' x with
  | Some (v, _) -> Some v
  | None -> None

let parse_namedGroup x =
  LP.parse32_total parse32_namedGroup' v;
  match parse32_namedGroup' x with
  | Some (v, _) -> if v = Unknown_namedGroup then None else Some v
  | None -> None


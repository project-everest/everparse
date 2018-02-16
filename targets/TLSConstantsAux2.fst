module TLSConstantsAux2
include TLSConstantsAux1

open FStar.String
open FStar.Seq
open FStar.Date
open FStar.Bytes
open FStar.Error
open TLSError
open Parse
//open CoreCrypto // avoid?!


module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -Parse -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false"

inline_for_extraction
let protocolVersion_enum : LP.enum protocolVersion (byte * byte) =
  [@inline_let]
  let e = [
    SSL_3p0, (3z, 0z);
    TLS_1p0, (3z, 1z);
    TLS_1p1, (3z, 2z);
    TLS_1p2, (3z, 3z);
    TLS_1p3, (3z, 4z);
  ]
  in
  [@inline_let]
  let prf : squash (L.noRepeats (L.map fst e) /\ L.noRepeats (L.map fst e)) =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in
  e

inline_for_extraction
let synth_protocolVersion'
  (x: LP.maybe_enum_key protocolVersion_enum)
: Tot protocolVersion'
= match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    let (a, b) = (y <: (byte * byte)) in
    UnknownVersion a b

let rec not_mem
  (#t: eqtype)
  (x: t)
  (l: list t)
: Tot (y: bool { y == true <==> L.mem x l == false } )
= match l with
  | [] -> true
  | a :: q ->
    let f = not_mem x q in
    (x <> a && f)

inline_for_extraction
let synth_protocolVersion'_recip
  (x: protocolVersion')
: Tot (LP.maybe_enum_key protocolVersion_enum)
= match x with
  | UnknownVersion a b ->
    let (y: (byte * byte)) = (a, b) in
    assert (normalize_term (not_mem y (L.map snd protocolVersion_enum)) == true);
    LP.Unknown y
  | x -> LP.Known x

let synth_protocolVersion'_recip_correct () : Lemma
  (forall (x: LP.maybe_enum_key protocolVersion_enum) . synth_protocolVersion'_recip (synth_protocolVersion' x) == x)
= ()

let parse_maybe_protocolVersion_key : LP.parser _ (LP.maybe_enum_key protocolVersion_enum) =
  LP.parse_maybe_enum_key (LP.parse_u8 `LP.nondep_then` LP.parse_u8) protocolVersion_enum

let synth_protocolVersion'_inj () : Lemma (forall (x1 x2: LP.maybe_enum_key protocolVersion_enum) .
  synth_protocolVersion' x1 == synth_protocolVersion' x2 ==> x1 == x2)
= ()

let serialize_maybe_protocolVersion_key : LP.serializer parse_maybe_protocolVersion_key =
  LP.serialize_maybe_enum_key _ (LP.serialize_nondep_then _ LP.serialize_u8 () _ LP.serialize_u8) protocolVersion_enum

let parse_protocolVersion' : LP.parser _ protocolVersion' =
  synth_protocolVersion'_inj ();
  parse_maybe_protocolVersion_key `LP.parse_synth` synth_protocolVersion'

let serialize_protocolVersion' : LP.serializer parse_protocolVersion' =
  synth_protocolVersion'_inj ();
  synth_protocolVersion'_recip_correct ();
  LP.serialize_synth _ synth_protocolVersion'  serialize_maybe_protocolVersion_key synth_protocolVersion'_recip ()

inline_for_extraction
let parse32_maybe_protocolVersion_key : LP.parser32 parse_maybe_protocolVersion_key =
  FStar.Tactics.synth_by_tactic
    (LP.parse32_maybe_enum_key_tac
      (LP.parse32_u8 `LP.parse32_nondep_then` LP.parse32_u8)
      protocolVersion_enum
      parse_maybe_protocolVersion_key
      ()
    )

(* actual term generated:
<<
LowParse.SLow.Enum.parse32_maybe_enum_key_gen (LowParse.SLow.Combinators.parse32_nondep_then LowParse.SLow.Int.parse32_u8
      LowParse.SLow.Int.parse32_u8)
  protocolVersion_enum
  (LowParse.SLow.Enum.maybe_enum_key_of_repr'_t_cons protocolVersion_enum
      ()
      (LowParse.SLow.Enum.maybe_enum_key_of_repr'_t_cons (LowParse.SLow.Enum.enum_tail protocolVersion_enum
            )
          ()
          (LowParse.SLow.Enum.maybe_enum_key_of_repr'_t_cons (LowParse.SLow.Enum.enum_tail (LowParse.SLow.Enum.enum_tail 
                      protocolVersion_enum))
              ()
              (LowParse.SLow.Enum.maybe_enum_key_of_repr'_t_cons (LowParse.SLow.Enum.enum_tail (LowParse.SLow.Enum.enum_tail 
                          (LowParse.SLow.Enum.enum_tail protocolVersion_enum)))
                  ()
                  (LowParse.SLow.Enum.maybe_enum_key_of_repr'_t_cons_nil (LowParse.SLow.Enum.enum_tail 
                          (LowParse.SLow.Enum.enum_tail (LowParse.SLow.Enum.enum_tail (LowParse.SLow.Enum.enum_tail 
                                      protocolVersion_enum))))
                      ())))))
>>
*)

inline_for_extraction
let parse32_protocolVersion' : LP.parser32 parse_protocolVersion' =
  synth_protocolVersion'_inj () ;
  LP.parse32_synth
    _
    synth_protocolVersion'
    (fun x -> synth_protocolVersion' x)
    parse32_maybe_protocolVersion_key
    ()


inline_for_extraction
let
serialize32_maybe_protocolVersion_key : LP.serializer32 serialize_maybe_protocolVersion_key =
  FStar.Tactics.synth_by_tactic
    (LP.serialize32_maybe_enum_key_tac
      (LP.serialize32_nondep_then #_ #_ #LP.parse_u8 #LP.serialize_u8 LP.serialize32_u8 () #_ #_ #LP.parse_u8 #LP.serialize_u8 LP.serialize32_u8 ())
      protocolVersion_enum
      serialize_maybe_protocolVersion_key
      ()
    )

inline_for_extraction
let serialize32_protocolVersion' : LP.serializer32 serialize_protocolVersion' =
  synth_protocolVersion'_inj ();
  synth_protocolVersion'_recip_correct ();
  LP.serialize32_synth
    _
    synth_protocolVersion'
    _
    serialize32_maybe_protocolVersion_key
    synth_protocolVersion'_recip
    (fun x -> synth_protocolVersion'_recip x)
    ()

(** Serializing function for the protocol version *)
inline_for_extraction
let versionBytes (input: protocolVersion') : Tot (lbytes 2) =
  serialize32_protocolVersion' input <: LP.bytes32


(** TODO: move elsewhere (FStar.Math.Lemmas?) *)

let le_antisym (x1 x2: int) : Lemma (requires (x1 <= x2 /\ x2 <= x1)) (ensures (x1 == x2)) = ()

(** END TODO: move *)

(** Parsing function for the protocol version *)
(* NOTE: this interface (as well as versionBytes) is dubious, since:
   - it makes explicit the size of bytes to parse
   - nothing tells that all input bytes were actually consumed
   In particular, this interface means that the caller is responsible for correctly splitting the input buffer *before* calling the parser.
*)
inline_for_extraction
val parseVersion: pinverse_t versionBytes
let parseVersion v =
  LP.parse32_total parse32_protocolVersion' v;
  let (Some (value, _)) = parse32_protocolVersion' v in
  Correct value

(* The following surprisingly succeeds. *)
val inverse_version: x:_ -> Lemma
  (requires True)
  (ensures lemma_inverse_g_f versionBytes parseVersion x)
let inverse_version x = ()

val pinverse_version: x: lbytes 2 -> Lemma
  (requires True)
  (ensures (lemma_pinverse_f_g Bytes.equal versionBytes parseVersion x))

(* The following fails, as expected. *)
// let pinverse_version x = ()
(* We have to call an explicit lemma, albeit generic *)

let pinverse_version x =
  LP.parse32_total parse32_protocolVersion' x;
  let (Correct c) = parseVersion x in
  let (Some (c', consumed)) = parse32_protocolVersion' x in
  assert (c == c');
  let f () : Lemma (2 <= UInt32.v consumed /\ UInt32.v consumed <= 2) =
    let k = LP.get_parser_kind parse_protocolVersion' in
    assert (k.LP.parser_kind_low == 2);
    assert (k.LP.parser_kind_high == Some 2);
    LP.parse32_size #k #protocolVersion' #parse_protocolVersion' parse32_protocolVersion' x c consumed;
    ()
  in
  f ();
  le_antisym (UInt32.v consumed) 2;
  assert (UInt32.v consumed == 2);
  LP.parser32_then_serializer32' parse32_protocolVersion' serialize32_protocolVersion' x c' consumed;
  ()

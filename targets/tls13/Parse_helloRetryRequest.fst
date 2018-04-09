module Parse_helloRetryRequest

open FStar.Bytes
open Parse_protocolVersion
open Parse_cipherSuite
open Parse_namedGroup
open Parse_extension

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot
module Seq = FStar.Seq

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

let helloRetryRequest_extensions_byteSize x = Seq.length (LP.serialize (LP.serialize_list _ extension_serializer) x)
  
let helloRetryRequest_extensions_byteSize32 x =
  LP.size32_list extension_size32 () x

type helloRetryRequest_extensions' = LP.parse_bounded_vldata_strong_t 0 65535 (LP.serialize_list _ extension_serializer)

type helloRetryRequest' = ((((
  (server_version: protocolVersion)) *
  (cipher_suite: cipherSuite)) *
  (selected_group: namedGroup)) *
  (extensions: helloRetryRequest_extensions'))

inline_for_extraction
let synth_helloRetryRequest
  (x: helloRetryRequest')
: Tot helloRetryRequest
= let ((((server_version), cipher_suite), selected_group), extensions) = x in
  {
    server_version = server_version;
    cipher_suite = cipher_suite;
    selected_group = selected_group;
    extensions = extensions;
  }

let synth_helloRetryRequest_injective () : Lemma
  (LP.synth_injective synth_helloRetryRequest)
= ()

inline_for_extraction
let synth_helloRetryRequest_recip
  (x: helloRetryRequest)
: Tot helloRetryRequest'
= ((((x.server_version), x.cipher_suite), x.selected_group), x.extensions)

let synth_helloRetryRequest_inverse () : Lemma
  (LP.synth_inverse synth_helloRetryRequest synth_helloRetryRequest_recip)
= ()

let helloRetryRequest'_parser : LP.parser _ helloRetryRequest' =
  protocolVersion_parser `LP.nondep_then`
  cipherSuite_parser `LP.nondep_then`
  namedGroup_parser `LP.nondep_then`
  LP.parse_bounded_vldata_strong 0 65535 (LP.serialize_list _ extension_serializer)

inline_for_extraction
let helloRetryRequest'_parser_kind = LP.get_parser_kind helloRetryRequest'_parser

let helloRetryRequest_parser_kind_metadata = helloRetryRequest'_parser_kind.LP.parser_kind_metadata

let helloRetryRequest_parser =
  synth_helloRetryRequest_injective ();
  assert_norm (helloRetryRequest_parser_kind == helloRetryRequest'_parser_kind);
  helloRetryRequest'_parser `LP.parse_synth` synth_helloRetryRequest

inline_for_extraction
let helloRetryRequest'_parser32 : LP.parser32 helloRetryRequest'_parser =
  protocolVersion_parser32 `LP.parse32_nondep_then`
  cipherSuite_parser32 `LP.parse32_nondep_then`
  namedGroup_parser32 `LP.parse32_nondep_then`
  LP.parse32_bounded_vldata_strong 0 0ul 65535 65535ul (LP.serialize_list _ extension_serializer) (LP.parse32_list extension_parser32)

let helloRetryRequest_parser32 =
  [@inline_let]
  let _ = synth_helloRetryRequest_injective () in
  [@inline_let]
  let _ = assert_norm (helloRetryRequest_parser_kind == helloRetryRequest'_parser_kind) in
  LP.parse32_synth
    _
    synth_helloRetryRequest
    (fun x -> synth_helloRetryRequest x)
    helloRetryRequest'_parser32
    ()

let helloRetryRequest'_serializer : LP.serializer helloRetryRequest'_parser =
  LP.serialize_nondep_then
    _ (LP.serialize_nondep_then 
      _ (LP.serialize_nondep_then
        _ protocolVersion_serializer ()
        _ cipherSuite_serializer
      ) ()
      _ namedGroup_serializer
    ) ()
    _ (LP.serialize_bounded_vldata_strong 0 65535 (LP.serialize_list _ extension_serializer))

let helloRetryRequest_serializer =
  [@inline_let]
  let _ = synth_helloRetryRequest_injective () in
  [@inline_let]
  let _ = synth_helloRetryRequest_inverse () in
  [@inline_let]
  let _ = assert_norm (helloRetryRequest_parser_kind == helloRetryRequest'_parser_kind) in
  LP.serialize_synth
    _
    synth_helloRetryRequest
    helloRetryRequest'_serializer
    synth_helloRetryRequest_recip
    ()

let helloRetryRequest'_serializer32 : LP.serializer32 helloRetryRequest'_serializer =
  LP.serialize32_nondep_then
    (LP.serialize32_nondep_then 
      (LP.serialize32_nondep_then
        protocolVersion_serializer32 ()
        cipherSuite_serializer32 ()
      ) ()
      namedGroup_serializer32 ()
    ) ()
    (LP.serialize32_bounded_vldata_strong 0 65535 (LP.partial_serialize32_list _ extension_serializer extension_serializer32 ())) ()

let helloRetryRequest_serializer32 =
  [@inline_let]
  let _ = synth_helloRetryRequest_injective () in
  [@inline_let]
  let _ = synth_helloRetryRequest_inverse () in
  [@inline_let]
  let _ = assert_norm (helloRetryRequest_parser_kind == helloRetryRequest'_parser_kind) in
  LP.serialize32_synth
    _
    synth_helloRetryRequest
    _
    helloRetryRequest'_serializer32
    synth_helloRetryRequest_recip
    (fun x -> synth_helloRetryRequest_recip x)
    ()

let helloRetryRequest'_size32 : LP.size32 helloRetryRequest'_serializer =
  LP.size32_nondep_then
    (LP.size32_nondep_then 
      (LP.size32_nondep_then
        protocolVersion_size32 ()
        cipherSuite_size32
      ) ()
      namedGroup_size32
    ) ()
    (LP.size32_bounded_vldata_strong 0 65535 (LP.size32_list extension_size32 ()) 2ul (* <-- this is the size of the size header, i.e. log256 65535 *) )

let helloRetryRequest_size32 =
  [@inline_let]
  let _ = synth_helloRetryRequest_injective () in
  [@inline_let]
  let _ = synth_helloRetryRequest_inverse () in
  [@inline_let]
  let _ = assert_norm (helloRetryRequest_parser_kind == helloRetryRequest'_parser_kind) in
  LP.size32_synth
    _
    synth_helloRetryRequest
    _
    helloRetryRequest'_size32
    synth_helloRetryRequest_recip
    (fun x -> synth_helloRetryRequest_recip x)
    ()

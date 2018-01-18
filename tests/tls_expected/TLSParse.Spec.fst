module TLSParse.Spec
open LowParse.Spec

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot
module Seq = FStar.Seq
module U32 = FStar.UInt32

type protocolVersion = U16.t

let parse_protocolVersion : parser _ protocolVersion =
  parse_u16

let parse_random_precond : parse_array_precond parse_u8 32ul =
  let f () : Lemma
    (array_type_of_parser_kind_precond parse_u8 (U32.v 32ul))
  = assert_norm (array_type_of_parser_kind_precond parse_u8 (U32.v 32ul))
  in
  parse_array_precond_intro parse_u8 32ul f

type random = array_type_of_parser parse_random_precond

module U32 = FStar.UInt32

let _ = assert_norm (random == (s: Seq.seq byte { Seq.length s == 32 } ))

let parse_random : parser _ random =
  parse_array parse_random_precond

type cipherSuite =
  | TLS_AES_128_GCM_SHA256
  | TLS_AES_256_GCM_SHA384
  | TLS_CHACHA20_POLY1305_SHA256
  | TLS_AES_128_CCM_SHA256
  | TLS_AES_128_CCM_8_SHA256

#set-options "--initial_fuel 32 --max_fuel 32 --initial_ifuel 32 --max_ifuel 32 --z3rlimit 64"

let cipherSuite_enum : total_enum cipherSuite (U8.t * U8.t) =
  let l = [
    TLS_AES_128_GCM_SHA256,       (0x13uy, 0x01uy);
    TLS_AES_256_GCM_SHA384,       (0x13uy, 0x02uy);
    TLS_CHACHA20_POLY1305_SHA256, (0x13uy, 0x03uy);
    TLS_AES_128_CCM_SHA256,       (0x13uy, 0x04uy);
    TLS_AES_128_CCM_8_SHA256,     (0x13uy, 0x05uy);
  ]
  in
  assert_norm (L.noRepeats (L.map fst l));
  assert_norm (L.noRepeats (L.map snd l));
  l

let parse_cipherSuite : parser _ cipherSuite =
  parse_total_enum_key (nondep_then parse_u8 parse_u8) cipherSuite_enum

let maybe_cipherSuite = maybe_total_enum_key cipherSuite_enum

let parse_maybe_cipherSuite : parser _ maybe_cipherSuite =
  parse_maybe_total_enum_key (nondep_then parse_u8 parse_u8) cipherSuite_enum

type extensionType =
  | EXT_server_name
  | EXT_max_fragment_length
  | EXT_status_request
  | EXT_supported_groups
  | EXT_signature_algorithms
  | EXT_use_srtp
  | EXT_heartbeat
  | EXT_application_layer_protocol_negotiation
  | EXT_signed_certificate_timestamp
  | EXT_client_certificate_type
  | EXT_server_certificate_type
  | EXT_padding
  | EXT_key_share
  | EXT_pre_shared_key
  | EXT_early_data
  | EXT_supported_versions
  | EXT_cookie
  | EXT_psk_key_exchange_modes
  | EXT_certificate_authorities
  | EXT_old_filters
  | EXT_post_handshake_auth

let extensionType_enum : total_enum extensionType U16.t =
  let l = [
    EXT_server_name,                             0us;
    EXT_max_fragment_length,                     1us;
    EXT_status_request,                          5us;
    EXT_supported_groups,                       10us;
    EXT_signature_algorithms,                   13us;
    EXT_use_srtp,                               14us;
    EXT_heartbeat,                              15us;
    EXT_application_layer_protocol_negotiation, 16us;
    EXT_signed_certificate_timestamp,           18us;
    EXT_client_certificate_type,                19us;
    EXT_server_certificate_type,                20us;
    EXT_padding,                                21us;
    EXT_key_share,                              40us;
    EXT_pre_shared_key,                         41us;
    EXT_early_data,                             42us;
    EXT_supported_versions,                     43us;
    EXT_cookie,                                 44us;
    EXT_psk_key_exchange_modes,                 45us;
    EXT_certificate_authorities,                47us;
    EXT_old_filters,                            48us;
    EXT_post_handshake_auth,                    49us;
  ]
  in
  assert_norm (L.noRepeats (L.map fst l));
  assert_norm (L.noRepeats (L.map snd l));
  l

let parse_extensionType : parser _ extensionType =
  parse_total_enum_key parse_u16 extensionType_enum

type maybe_extensionType = maybe_total_enum_key extensionType_enum

let parse_maybe_extensionType : parser _ maybe_extensionType =
  parse_maybe_total_enum_key parse_u16 extensionType_enum

noeq
type extension = {
  extension_type: maybe_extensionType;
  extension_data: Seq.seq byte;
}

let extension_presynth = (
  maybe_extensionType * (
  Seq.seq byte
))

module U32 = FStar.UInt32

#set-options "--initial_fuel 64 --max_fuel 64 --initial_ifuel 64 --max_ifuel 64 --z3rlimit 256"

let parse_extension_presynth : parser _ extension_presynth = 
  assert_norm (U32.v 65535ul > 0);
  (
    parse_maybe_extensionType `nondep_then` (
    parse_bounded_vlbytes 0ul 65535ul (parse_seq parse_u8)
  ))

let synth_extension (data: extension_presynth) : Tot extension =
  match data with (
    extension_type,
    extension_data
  ) -> {
    extension_type = extension_type;
    extension_data = extension_data;
  }

let parse_extension : parser _ extension =
  parse_extension_presynth `parse_synth` synth_extension

let clientHello_legacy_session_id_t_precond :
  (parse_vlarray_precond parse_u8 0ul 32ul)
= let f () : Lemma
    (vlarray_type_of_parser_kind_precond parse_u8 0ul 32ul)
  = assert_norm (vlarray_type_of_parser_kind_precond parse_u8 0ul 32ul == true)
  in
  parse_vlarray_precond_intro parse_u8 0ul 32ul f

let clientHello_legacy_session_id_t : Type0 =
  vlarray_type_of_parser clientHello_legacy_session_id_t_precond

let parse_clientHello_legacy_session_id_t : parser _ clientHello_legacy_session_id_t =
  parse_vlarray clientHello_legacy_session_id_t_precond

noeq
type clientHello = {
  legacy_version: (legacy_version: protocolVersion { legacy_version = 0x0303us } );
  random: random;
  legacy_session_id: clientHello_legacy_session_id_t;
  cipher_suites: Seq.seq maybe_cipherSuite;
  legacy_compression_methods: Seq.seq byte;
  extensions: Seq.seq extension;
}

type clientHello_presynth = (
  (legacy_version: protocolVersion {legacy_version = 0x0303us}) * (
  random * (
  clientHello_legacy_session_id_t * (
  Seq.seq maybe_cipherSuite * (
  Seq.seq byte * (
  Seq.seq extension
  ))))))

#set-options "--initial_fuel 64 --max_fuel 64 --initial_ifuel 64 --max_ifuel 64 --z3rlimit 1024"

let parse_clientHello_presynth : parser _ clientHello_presynth =
  assert_norm (U32.v 32ul > 0);
  assert_norm (U32.v 65534ul > 0);
  assert_norm (U32.v 255ul > 0);
  (
    parse_filter parse_protocolVersion (fun (legacy_version: protocolVersion) -> legacy_version = 0x0303us) `nondep_then` (
    parse_random `nondep_then` (
    parse_clientHello_legacy_session_id_t `nondep_then` (
    parse_bounded_vlbytes 2ul 65534ul (parse_seq parse_maybe_cipherSuite) `nondep_then` (
    parse_bounded_vlbytes 1ul 255ul (parse_seq parse_u8) `nondep_then` (
    parse_bounded_vlbytes 8ul 65534ul (parse_seq parse_extension)
  ))))))

let synth_clientHello (data: clientHello_presynth) : Tot clientHello = match data with (
    legacy_version, (
    random, (
    legacy_session_id, (
    cipher_suites, (
    legacy_compression_methods, (
    extensions
  )))))) -> {
    legacy_version = legacy_version;
    random = random;
    legacy_session_id = legacy_session_id;
    cipher_suites = cipher_suites;
    legacy_compression_methods = legacy_compression_methods;
    extensions = extensions;
  }

let parse_clientHello : parser _ clientHello =
  parse_clientHello_presynth `parse_synth` synth_clientHello

(*
let parse_clientHello_unsynth : clientHello -> Tot clientHello_data = fun x -> (
  x.legacy_version, (
  x.random, (
  x.legacy_session_id, (
  x.cipher_suites, (
  x.legacy_compression_methods, (
  x.extensions
))))))

let parse_clientHello_unsynth_correct () : Lemma
  (forall x . parse_clientHello_unsynth (parse_clientHello_synth x) == x)
= ()

let injective_prf (#t1 #t2: Type0) (f: t1 -> Tot t2) : GTot Type0 =
  unit -> Lemma (forall x x' . f x == f x' ==> x == x')

(*
let parse_clientHello_synth_injective : injective_prf parse_clientHello_synth =
  fun () -> ()

#reset-options

let parse_synth'
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (f2_inj: injective_prf f2)
: Tot (parser k t2)
= f2_inj ();
  parse_synth p1 f2
*)

assume
val parse_synth'
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
//  (f2_inj: injective_prf f2)
: Tot (parser k t2)
 


(*

unfold
let get_parser_kind (#k: parser_kind) (#t: Type0) (p: parser k t) = k

  parse_synth' #(get_parser_kind parse_clientHello_data) #clientHello_data #clientHello parse_clientHello_data parse_clientHello_synth
  
  
  // parse_clientHello_synth_injective

(*


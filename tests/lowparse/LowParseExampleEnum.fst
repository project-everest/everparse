module LowParseExampleEnum

module U8 = FStar.UInt8
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 3 --max_ifuel 3"

type alertDescription : eqtype =
  | Close_notify
  | Unexpected_message
  | Bad_record_mac
  | Record_overflow
  | Handshake_failure
  | Bad_certificate
  | Unsupported_certificate
  | Certificate_revoked
  | Certificate_expired
  | Certificate_unknown
  | Illegal_parameter
  | Unknown_ca
  | Access_denied
  | Decode_error
  | Decrypt_error
  | Protocol_version
  | Insufficient_security
  | Internal_error
  | Inappropriate_fallback
  | User_canceled
  | Missing_extension
  | Unsupported_extension
  | Unrecognized_name
  | Bad_certificate_status_response
  | Unknown_psk_identity
  | Certificate_required
  | No_application_protocol

inline_for_extraction let alertDescription_enum : LP.enum alertDescription U8.t =
  [@inline_let] let e = [
    Close_notify, 0z;
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
    Unrecognized_name, 112z;
    Bad_certificate_status_response, 113z;
    Unknown_psk_identity, 115z;
    Certificate_required, 116z;
    No_application_protocol, 120z;
  ] in
  [@inline_let] let _ =
    assert_norm (L.noRepeats (LP.list_map fst e));
    assert_norm (L.noRepeats (LP.list_map snd e))
  in e

module T = FStar.Tactics

#set-options "--no_smt"

let x : LP.maybe_enum_key_of_repr'_t alertDescription_enum =
  T.synth_by_tactic (fun () -> LP.maybe_enum_key_of_repr_tac alertDescription_enum ())

module CBOR.Pulse.Raw.EverParse.SerializeCborEq

(* Tiny helper exposing that `serialize_cbor v` (which is opaque since
   `serialize_cbor` is declared with `val` in `CBOR.Spec.Raw.Format.fsti`)
   equals the EverParse-level `bare_serialize serialize_raw_data_item v`.
   We friend `CBOR.Spec.Raw.Format` ONLY here so the equation is visible
   without disturbing other modules' proofs. *)

friend CBOR.Spec.Raw.Format

module F = CBOR.Spec.Raw.EverParse
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators

open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse

let serialize_cbor_eq_bare_serialize v =
  (* serialize_cbor v == F.tot_serialize_raw_data_item v (by friend def)
     serialize_raw_data_item = serializer_of_tot_serializer tot_serialize_raw_data_item
     serializer_of_tot_serializer s = s
     bare_serialize s v = s v
     So all four are definitionally equal. *)
  ()

let pair_byte_compare_eq_cbor_compare_pair kv1 kv2 =
  let s = serialize_raw_data_item in
  let pair_ser = LPC.serialize_nondep_then s s in
  (* Step 1: bare_serialize pair_ser kv == bare_serialize s (fst kv) ++ bare_serialize s (snd kv) *)
  LPC.serialize_nondep_then_eq s s kv1;
  LPC.serialize_nondep_then_eq s s kv2;
  (* Step 2: bytes_lex_compare distributes over the concat (LowParse form;
     SMTPat in CBOR.Spec.Raw.Format bridges to Format.bytes_lex_compare). *)
  bytes_lex_compare_serialize_strong_prefix s
    (fst kv1) (fst kv2)
    (LP.bare_serialize s (snd kv1)) (LP.bare_serialize s (snd kv2));
  (* Step 3: connect cbor_compare to Format.bytes_lex_compare on bare_serialize. *)
  cbor_compare_correct (fst kv1) (fst kv2);
  cbor_compare_correct (snd kv1) (snd kv2);
  serialize_cbor_eq_bare_serialize (fst kv1);
  serialize_cbor_eq_bare_serialize (fst kv2);
  serialize_cbor_eq_bare_serialize (snd kv1);
  serialize_cbor_eq_bare_serialize (snd kv2)



module CBOR.Pulse.Raw.EverParse.SerializeCborEq

(* Tiny helper exposing that `serialize_cbor v` (which is opaque since
   `serialize_cbor` is declared with `val` in `CBOR.Spec.Raw.Format.fsti`)
   equals the EverParse-level `bare_serialize serialize_raw_data_item v`.
   We friend `CBOR.Spec.Raw.Format` ONLY here so the equation is visible
   without disturbing other modules' proofs. *)

friend CBOR.Spec.Raw.Format

module F = CBOR.Spec.Raw.EverParse
module LP = LowParse.Spec.Base

open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse

let serialize_cbor_eq_bare_serialize v =
  (* serialize_cbor v == F.tot_serialize_raw_data_item v (by friend def)
     serialize_raw_data_item = serializer_of_tot_serializer tot_serialize_raw_data_item
     serializer_of_tot_serializer s = s
     bare_serialize s v = s v
     So all four are definitionally equal. *)
  ()


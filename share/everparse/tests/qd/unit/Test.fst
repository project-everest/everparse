module Test
#lang-pulse

(* A client of the Pulse API that `qd -pulse` generates for unittests.rfc.

   The rest of this suite only checks that the generated code verifies,
   extracts and compiles. Nothing consumed it, so a generated validator,
   jumper or accessor could have been unusable at its own interface and this
   suite would still have been green. This is the Pulse counterpart of the
   `employee_test` client in the deleted Low* `tests/sample`, which used
   `employee_validator` + `accessor_employee_salary` + `read_u16`.

   t8 is the interesting target: its two leading fields are variable-length
   (`t5 y`, `t1 z<0..255>`), so reaching the fixed-width `x1` exercises the
   generated jumpers rather than a constant offset. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Spec.Base

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module I32 = FStar.Int32
module A = Pulse.Lib.Array
module PPB = LowParse.PulseParse.Base
module LPPI = LowParse.Pulse.Int
module LPSI = LowParse.Spec.Int
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
let read_u16 : PPB.leaf_reader LPSI.parse_u16 =
  PPB.leaf_reader_of_serialized (LPPI.read_u16' ())

(* Validate a t8, then project field x1 through the generated accessor. *)
fn t8_read_x1
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires S.pts_to input #pm v
  returns res: U16.t
  ensures S.pts_to input #pm v
{
  let mut poffset = 0sz;
  let is_valid = T8.t8_validator input poffset;
  if is_valid {
    let off = !poffset;
    let input' = PPB.peek_trade_gen T8.t8_parser input 0sz off;
    with v1. assert (PPB.pts_to_parsed T8.t8_parser input' #(pm /. 2.0R) v1);
    let sub = T8.accessor_t8_x1 input';
    with v2 pm2. assert (PPB.pts_to_parsed LPSI.parse_u16 sub #pm2 v2);
    let x = read_u16 sub;
    Trade.elim (PPB.pts_to_parsed LPSI.parse_u16 sub #pm2 v2)
               (PPB.pts_to_parsed T8.t8_parser input' #(pm /. 2.0R) v1);
    Trade.elim (PPB.pts_to_parsed T8.t8_parser input' #(pm /. 2.0R) v1)
               (S.pts_to input #pm v);
    x
  } else {
    0us
  }
}

(* A well-formed t8, laid out by hand. Note the TLS presentation-syntax rule
   that `t3 t4[8]` is 8 *bytes* (4 elements of the 2-byte t3), not 8 elements:

     0..7   t4 x   = 4 * t3, t3 = opaque[2]   (fixed, 8 bytes)
     8      t5 y   = empty vector             (1-byte length prefix, 0x00)
     9      t1 z   = empty vector             (1-byte length prefix, 0x00)
     10..11 x1 : uint16  <- the field read back below
     12..21 x2..x6 : uint16
     22..25 x7 : uint32                                       total 26 bytes

   26 is exactly the minimum length qd computes for t8 (LINFO<t8> minLen=26). *)
fn test ()
  requires emp
  returns ok: bool
  ensures emp
{
  let mut arr = [| 0uy ; 26sz |];
  let input = S.from_array arr 26sz;
  input.(10sz) <- 0x12uy;
  input.(11sz) <- 0x34uy;
  let res = t8_read_x1 input;
  S.to_array input;
  U16.eq res 0x1234us
}

(* Non-zero exit if the generated validator/jumper/accessor chain does not
   round-trip the field we planted, so the suite fails loudly rather than
   merely proving the code compiles. *)
fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{
  let ok = test ();
  if ok { 0l } else { 1l }
}

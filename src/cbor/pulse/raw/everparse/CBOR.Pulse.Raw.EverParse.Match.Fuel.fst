module CBOR.Pulse.Raw.EverParse.Match.Fuel
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Match

open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open LowParse.Pulse.Base
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Base
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type

let rec cbor_raw_match_fuel
  (n: nat)
:
  (pm: perm) ->
  (xl: cbor_raw) ->
  (xh: raw_data_item) ->
  Tot slprop
= if n = 0
  then fun _ _ _ -> pure False
  else cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1))

let cbor_raw_match_fuel_eq_zero
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
: Lemma
  (cbor_raw_match_fuel 0 pm xl xh == pure False)
= ()

let cbor_raw_match_fuel_eq_succ
  (n: nat)
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
: Lemma
  (requires (n > 0))
  (ensures (
    cbor_raw_match_fuel n pm xl xh ==
    cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm xl xh
  ))
= ()

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn rec cbor_raw_match_fuel_share
  (n: nat)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match_fuel n pm xl xh
ensures cbor_raw_match_fuel n (pm /. 2.0R) xl xh **
        cbor_raw_match_fuel n (pm /. 2.0R) xl xh
decreases n
{
  if (n = 0) {
    cbor_raw_match_fuel_eq_zero pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (pure False);
    unreachable ()
  } else {
    let n' : nat = n - 1;
    cbor_raw_match_fuel_eq_succ n pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') pm xl (Ghost.reveal xh));
    ghost fn share_rec
      (x1: cbor_raw) (#p0: perm) (#x2: raw_data_item)
    requires cbor_raw_match_fuel n' p0 x1 x2
    ensures cbor_raw_match_fuel n' (p0 /. 2.0R) x1 x2 **
            cbor_raw_match_fuel n' (p0 /. 2.0R) x1 x2
    {
      cbor_raw_match_fuel_share n' x1 #p0 #x2
    };
    cbor_raw_match_aux_share
      (cbor_raw_match_fuel n')
      share_rec
      parse_raw_data_item
      xl;
    cbor_raw_match_fuel_eq_succ n (pm /. 2.0R) xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') (pm /. 2.0R) xl (Ghost.reveal xh))
         as (cbor_raw_match_fuel n (pm /. 2.0R) xl (Ghost.reveal xh));
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') (pm /. 2.0R) xl (Ghost.reveal xh))
         as (cbor_raw_match_fuel n (pm /. 2.0R) xl (Ghost.reveal xh));
  }
}

ghost
fn rec cbor_raw_match_fuel_gather
  (n: nat)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
  (#pm': perm)
  (#xh': Ghost.erased raw_data_item)
requires cbor_raw_match_fuel n pm xl xh **
         cbor_raw_match_fuel n pm' xl xh'
ensures cbor_raw_match_fuel n (pm +. pm') xl xh **
        pure (xh == xh')
decreases n
{
  if (n = 0) {
    cbor_raw_match_fuel_eq_zero pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (pure False);
    unreachable ()
  } else {
    let n' : nat = n - 1;
    cbor_raw_match_fuel_eq_succ n pm xl (Ghost.reveal xh);
    cbor_raw_match_fuel_eq_succ n pm' xl (Ghost.reveal xh');
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') pm xl (Ghost.reveal xh));
    rewrite (cbor_raw_match_fuel n pm' xl (Ghost.reveal xh'))
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') pm' xl (Ghost.reveal xh'));
    ghost fn gather_rec
      (x1: cbor_raw) (#pm0: perm) (#x2: raw_data_item) (#pm0': perm) (x2': raw_data_item { x2' << Ghost.reveal xh' })
    requires cbor_raw_match_fuel n' pm0 x1 x2 ** cbor_raw_match_fuel n' pm0' x1 x2'
    ensures cbor_raw_match_fuel n' (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
    {
      cbor_raw_match_fuel_gather n' x1 #pm0 #x2 #pm0' #x2'
    };
    cbor_raw_match_aux_gather
      (cbor_raw_match_fuel n')
      parse_raw_data_item
      xl
      #pm #xh #pm' #xh'
      gather_rec;
    cbor_raw_match_fuel_eq_succ n (pm +. pm') xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') (pm +. pm') xl (Ghost.reveal xh))
         as (cbor_raw_match_fuel n (pm +. pm') xl (Ghost.reveal xh));
  }
}

#pop-options

ghost
fn cbor_raw_match_fuel_share_t
  (n: nat)
: share_t (cbor_raw_match_fuel n)
= (xl: cbor_raw)
  (#pm: perm)
  (#xh: raw_data_item)
{
  cbor_raw_match_fuel_share n xl #pm #(Ghost.hide xh)
}

ghost
fn cbor_raw_match_fuel_gather_t
  (n: nat)
: gather_t (cbor_raw_match_fuel n)
= (xl: cbor_raw)
  (#pm: perm)
  (#xh: raw_data_item)
  (#pm': perm)
  (#xh': raw_data_item)
{
  cbor_raw_match_fuel_gather n xl #pm #(Ghost.hide xh) #pm' #(Ghost.hide xh')
}

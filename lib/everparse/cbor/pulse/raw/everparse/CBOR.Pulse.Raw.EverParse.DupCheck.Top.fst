module CBOR.Pulse.Raw.EverParse.DupCheck.Top
#lang-pulse
open CBOR.Spec.Raw.EverParse.DupCheck
open CBOR.Pulse.Raw.EverParse.DupCheck
open LowParse.Spec.Base
open Pulse.Lib.Pervasives

(* Top-level sort-based map key duplicate check on a whole input buffer
   whose prefix has been validated by `validate_raw_data_item_bounded`. *)

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8

let div_le (a l: nat) (k: pos) : Lemma
  (a * k <= l <==> a <= l / k)
= FStar.Math.Lemmas.euclidean_division_definition l k;
  if a <= l / k
  then FStar.Math.Lemmas.lemma_mult_le_right k a (l / k)
  else FStar.Math.Lemmas.lemma_mult_le_right k (l / k + 1) a

let sort_scratch_ok_correct (d n l: nat) : Lemma
  (requires d > 0)
  (ensures (3 * n * d <= l <==> n <= (l / 3) / d))
= div_le (n * d) l 3;
  div_le n (l / 3) d;
  assert (3 * n * d == (n * d) * 3)

let dupcheck_sort_scratch_ok (d n len: SZ.t) : Tot (res: bool { res == (3 * SZ.v n * SZ.v d <= SZ.v len) })
= if d = 0sz
  then true
  else begin
    sort_scratch_ok_correct (SZ.v d) (SZ.v n) (SZ.v len);
    SZ.lte n (SZ.div (SZ.div len 3sz) d)
  end

let bounded_item_bnd (d n: nat) (x: raw_data_item) : Lemma
  (requires CBOR.Spec.Raw.Base.raw_data_item_bounded d n x)
  (ensures List.Tot.for_all (item_bnd n d) [x])
= ()

let check_dups_top_post (x: raw_data_item) (res: bool) : Lemma
  (requires res == check_dups [x])
  (ensures res == valid_raw_data_item x)
= CBOR.Spec.Raw.DupCheck.check_dups_valid x

fn check_dups_top
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (d n: SZ.t)
  (sc: S.slice SZ.t)
  (x: Ghost.erased raw_data_item)
  (off: Ghost.erased nat)
requires
  pts_to b #p bB ** (exists* s . pts_to sc s) ** pure (
    (match parse CBOR.Spec.Raw.EverParse.parse_raw_data_item bB with
     | Some (x', c) -> x' == Ghost.reveal x /\ c == Ghost.reveal off
     | None -> False) /\
    CBOR.Spec.Raw.Base.raw_data_item_bounded (SZ.v d) (SZ.v n) x /\
    SZ.v (S.len sc) >= 3 * SZ.v n * SZ.v d
  )
returns res: bool
ensures
  pts_to b #p bB ** (exists* s . pts_to sc s) ** pure (res == valid_raw_data_item x)
{
  CBOR.Spec.Raw.EverParse.Items.items_at_single bB x off;
  items_at_append_nil bB 0 1 [Ghost.reveal x];
  bounded_item_bnd (SZ.v d) (SZ.v n) x;
  let mut pout = 0sz;
  let res = check_items b #p #bB (Ghost.hide (SZ.v n)) (Ghost.hide (SZ.v d)) sc 0sz 1sz (Ghost.hide [Ghost.reveal x]) (Ghost.hide []) (Ghost.hide 0) pout;
  check_dups_top_post x res;
  res
}

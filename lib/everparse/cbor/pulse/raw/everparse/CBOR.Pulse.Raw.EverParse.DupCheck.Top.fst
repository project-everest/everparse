module CBOR.Pulse.Raw.EverParse.DupCheck.Top
#lang-pulse
open CBOR.Spec.Raw.EverParse.DupCheck
open CBOR.Pulse.Raw.EverParse.DupCheck
open LowParse.Spec.Base
open Pulse.Lib.Pervasives

(* Top-level map key duplicate checks on a whole input buffer whose
   prefix has been validated by `validate_raw_data_item_bounded`:
   sort-based, or hash-based with a caller-provided SipHash key. *)

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module A = Pulse.Lib.Array

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

let dupcheck_sort_scratch_ok (map_depth_bound map_length_bound scratch_len: SZ.t) : Tot (res: bool { res == (3 * SZ.v map_length_bound * SZ.v map_depth_bound <= SZ.v scratch_len) })
= if map_depth_bound = 0sz
  then true
  else begin
    sort_scratch_ok_correct (SZ.v map_depth_bound) (SZ.v map_length_bound) (SZ.v scratch_len);
    SZ.lte map_length_bound (SZ.div (SZ.div scratch_len 3sz) map_depth_bound)
  end

let bounded_item_bnd (d n: nat) (x: raw_data_item) : Lemma
  (requires CBOR.Spec.Raw.Base.raw_data_item_bounded d n x)
  (ensures List.Tot.for_all (item_bnd n d) [x])
= ()

let check_dups_top_post (x: raw_data_item) (res: bool) : Lemma
  (requires res == check_dups [x])
  (ensures res == valid_raw_data_item x)
= CBOR.Spec.Raw.DupCheck.check_dups_valid x

fn check_dups_top_gen
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (d n: SZ.t)
  (sc: S.slice SZ.t)
  (k0 k1: U64.t)
  (hv: S.slice U64.t)
  (idx: S.slice SZ.t)
  (x: Ghost.erased raw_data_item)
  (off: Ghost.erased nat)
requires
  pts_to b #p bB ** (exists* s . pts_to sc s) ** (exists* s . pts_to hv s) ** (exists* s . pts_to idx s) ** pure (
    (match parse CBOR.Spec.Raw.EverParse.parse_raw_data_item bB with
     | Some (x', c) -> x' == Ghost.reveal x /\ c == Ghost.reveal off
     | None -> False) /\
    CBOR.Spec.Raw.Base.raw_data_item_bounded (SZ.v d) (SZ.v n) x /\
    SZ.v (S.len sc) >= 3 * SZ.v n * SZ.v d
  )
returns res: bool
ensures
  pts_to b #p bB ** (exists* s . pts_to sc s) ** (exists* s . pts_to hv s) ** (exists* s . pts_to idx s) ** pure (res == valid_raw_data_item x)
{
  CBOR.Spec.Raw.EverParse.Items.items_at_single bB x off;
  items_at_append_nil bB 0 1 [Ghost.reveal x];
  bounded_item_bnd (SZ.v d) (SZ.v n) x;
  let mut pout = 0sz;
  let res = check_items b #p #bB (Ghost.hide (SZ.v n)) (Ghost.hide (SZ.v d)) sc k0 k1 hv idx 0sz 1sz (Ghost.hide [Ghost.reveal x]) (Ghost.hide []) (Ghost.hide 0) pout;
  check_dups_top_post x res;
  res
}

(* Sort-based: no hash scratch space, so that all maps are sorted with `cc` *)

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
  with s . assert (pts_to sc s);
  S.pts_to_len sc;
  let idx, sc' = S.split sc 0sz;
  S.pts_to_len sc';
  let mut a = [| 0uL; 1sz |];
  let hv = S.from_array a 1sz;
  let res = check_dups_top_gen b d n sc' 0uL 0uL hv idx x off;
  S.to_array hv;
  S.join idx sc' sc;
  res
}

(* Hash-based: the first `n` elements of the scratch space hold the
   indices of map keys being sorted, the hash scratch space holds their
   hashes *)

let hash_scratch_ok_correct (d n l: nat) : Lemma
  (requires n <= l)
  (ensures (3 * n * d + n <= l <==> 3 * n * d <= l - n))
= ()

let dupcheck_hash_scratch_ok (map_depth_bound map_length_bound scratch_len hash_scratch_len: SZ.t) : Tot (res: bool { res == (3 * SZ.v map_length_bound * SZ.v map_depth_bound + SZ.v map_length_bound <= SZ.v scratch_len && SZ.v map_length_bound <= SZ.v hash_scratch_len) })
= if SZ.lte map_length_bound scratch_len && SZ.lte map_length_bound hash_scratch_len
  then begin
    hash_scratch_ok_correct (SZ.v map_depth_bound) (SZ.v map_length_bound) (SZ.v scratch_len);
    dupcheck_sort_scratch_ok map_depth_bound map_length_bound (SZ.sub scratch_len map_length_bound)
  end
  else false

fn check_dups_top_hash
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (d n: SZ.t)
  (k0 k1: U64.t)
  (sc: S.slice SZ.t)
  (hv: S.slice U64.t)
  (x: Ghost.erased raw_data_item)
  (off: Ghost.erased nat)
requires
  pts_to b #p bB ** (exists* s . pts_to sc s) ** (exists* s . pts_to hv s) ** pure (
    (match parse CBOR.Spec.Raw.EverParse.parse_raw_data_item bB with
     | Some (x', c) -> x' == Ghost.reveal x /\ c == Ghost.reveal off
     | None -> False) /\
    CBOR.Spec.Raw.Base.raw_data_item_bounded (SZ.v d) (SZ.v n) x /\
    SZ.v (S.len sc) >= 3 * SZ.v n * SZ.v d + SZ.v n
  )
returns res: bool
ensures
  pts_to b #p bB ** (exists* s . pts_to sc s) ** (exists* s . pts_to hv s) ** pure (res == valid_raw_data_item x)
{
  with s . assert (pts_to sc s);
  S.pts_to_len sc;
  let idx, sc' = S.split sc n;
  S.pts_to_len sc';
  let res = check_dups_top_gen b d n sc' k0 k1 hv idx x off;
  S.join idx sc' sc;
  res
}

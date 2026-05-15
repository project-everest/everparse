module CBOR.Pulse.Raw.EverParse.ReadFields
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Type
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.EverParse.Match
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module Access = CBOR.Pulse.Raw.EverParse.Access

(* ======== Field-level value prop ======== *)

(* A stronger version of cbor_raw_match_cases_prop that also captures
   the value equalities obtained from the header match. *)
let cbor_raw_match_fields_prop (x: cbor_raw) (y: raw_data_item) : prop =
  match x, y with
  | CBOR_Case_Simple v, Simple w -> v == w
  | CBOR_Case_Int v, Int64 ty vi ->
    v.cbor_int_type == ty /\ v.cbor_int_value == vi.value
  | CBOR_Case_String v, String ty vi sv ->
    v.cbor_string_type == ty
  | CBOR_Case_Array v, Array vi sub ->
    U64.v (U64.uint_to_t (SZ.v (IT.mixed_list_length v.cbor_array_ptr))) == List.Tot.length sub
  | CBOR_Case_Map v, Map vi sub ->
    U64.v (U64.uint_to_t (SZ.v (IT.mixed_list_length v.cbor_map_ptr))) == List.Tot.length sub
  | CBOR_Case_Tagged v, Tagged vi sub ->
    v.cbor_tagged_tag.value == vi.value
  | CBOR_Case_Tagged_Serialized v, Tagged vi sub ->
    v.cbor_tagged_serialized_tag.value == vi.value
  | _, _ -> False

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

let cbor_raw_match_fields_of_header
  (x: cbor_raw)
  (y: raw_data_item)
  (h: header)
  (_: squash (cbor_raw_get_header x == Some h))
  (_: squash (dfst (synth_raw_data_item_recip y) == h))
: Lemma (cbor_raw_match_fields_prop x y)
= ()

#pop-options

(* The ghost function that extracts field values from cbor_raw_match.
   Follows the same unfold/fold pattern as cbor_raw_match_cases in Access.fst. *)

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_match_fields
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y
ensures cbor_raw_match pm x y ** pure (cbor_raw_match_fields_prop x y)
{
  // Unfold cbor_raw_match to cbor_raw_match_aux
  cbor_raw_match_unfold_aux x;
  // Unfold the chain of let-definitions to get the header pure fact
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  // Extract the header fact
  let the_prop = cbor_raw_get_header x ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
  let sq = elim_pure_explicit the_prop;
  // Prove cbor_raw_match_fields_prop
  cbor_raw_match_fields_of_header x (Ghost.reveal y)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))) sq ();
  // Refold everything
  intro_pure the_prop sq;
  rewrite
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  // Refold cbor_raw_match
  cbor_raw_match_fold_aux x;
  ()
}
```

#pop-options

(* ======== Simple value reader ======== *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"

let cbor_raw_simple_value (x: cbor_raw) : Tot (option simple_value) =
  match x with
  | CBOR_Case_Simple v -> Some v
  | _ -> None

```pulse
fn cbor_raw_read_simple_value
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y ** pure (Simple? (Ghost.reveal y))
returns res: simple_value
ensures cbor_raw_match pm x y ** pure (Ghost.reveal y == Simple res)
{
  cbor_raw_match_fields pm x;
  let res = Some?.v (cbor_raw_simple_value x);
  res
}
```

(* ======== Int64 value reader ======== *)

let cbor_raw_int64_value (x: cbor_raw) : Tot (option U64.t) =
  match x with
  | CBOR_Case_Int v -> Some v.cbor_int_value
  | _ -> None

let int64_value_of (y: raw_data_item) : Tot (option U64.t) =
  match y with
  | Int64 _ v -> Some v.value
  | _ -> None

```pulse
fn cbor_raw_read_int64_value
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y ** pure (Int64? (Ghost.reveal y))
returns res: U64.t
ensures cbor_raw_match pm x y ** pure (int64_value_of (Ghost.reveal y) == Some res)
{
  cbor_raw_match_fields pm x;
  let res = Some?.v (cbor_raw_int64_value x);
  res
}
```

(* ======== String length reader ======== *)

let cbor_raw_string_length (x: cbor_raw) : Tot (option U64.t) =
  match x with
  | CBOR_Case_String v -> Some (SZ.sizet_to_uint64 (S.len v.cbor_string_ptr))
  | _ -> None

(* ======== Tagged tag reader ======== *)

let cbor_raw_tagged_tag (x: cbor_raw) : Tot (option U64.t) =
  match x with
  | CBOR_Case_Tagged v -> Some v.cbor_tagged_tag.value
  | CBOR_Case_Tagged_Serialized v -> Some v.cbor_tagged_serialized_tag.value
  | _ -> None

let tagged_tag_value_of (y: raw_data_item) : Tot (option U64.t) =
  match y with
  | Tagged tag _ -> Some tag.value
  | _ -> None

```pulse
fn cbor_raw_read_tagged_tag
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y ** pure (Tagged? (Ghost.reveal y))
returns res: U64.t
ensures cbor_raw_match pm x y ** pure (tagged_tag_value_of (Ghost.reveal y) == Some res)
{
  cbor_raw_match_fields pm x;
  let res = Some?.v (cbor_raw_tagged_tag x);
  res
}
```

(* ======== Array length reader ======== *)

let cbor_raw_array_length (x: cbor_raw) : Tot (option U64.t) =
  match x with
  | CBOR_Case_Array v -> Some (SZ.sizet_to_uint64 (IT.mixed_list_length v.cbor_array_ptr))
  | _ -> None

let array_length_of (y: raw_data_item) : Tot (option nat) =
  match y with
  | Array _ v -> Some (List.Tot.length v)
  | _ -> None

```pulse
fn cbor_raw_read_array_length
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y ** pure (Array? (Ghost.reveal y))
returns res: U64.t
ensures cbor_raw_match pm x y ** pure (array_length_of (Ghost.reveal y) == Some (U64.v res))
{
  cbor_raw_match_fields pm x;
  let res = Some?.v (cbor_raw_array_length x);
  res
}
```

(* ======== Map length reader ======== *)

let cbor_raw_map_length (x: cbor_raw) : Tot (option U64.t) =
  match x with
  | CBOR_Case_Map v -> Some (SZ.sizet_to_uint64 (IT.mixed_list_length v.cbor_map_ptr))
  | _ -> None

let map_length_of (y: raw_data_item) : Tot (option nat) =
  match y with
  | Map _ v -> Some (List.Tot.length v)
  | _ -> None

```pulse
fn cbor_raw_read_map_length
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y ** pure (Map? (Ghost.reveal y))
returns res: U64.t
ensures cbor_raw_match pm x y ** pure (map_length_of (Ghost.reveal y) == Some (U64.v res))
{
  cbor_raw_match_fields pm x;
  let res = Some?.v (cbor_raw_map_length x);
  res
}
```

#pop-options

(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module CDDL.Spec
include CDDL.Spec.ArrayGroup
include CDDL.Spec.MapGroup
include CDDL.Spec.Misc
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Multi-purpose recursive combinator, to allow disjunctions between destructors

let rec multi_rec
  (phi_base: typ)
  (phi_array: (b: Cbor.raw_data_item) -> bounded_typ b -> array_group3 (Some b))
  (phi_map: (b: Cbor.raw_data_item) -> bounded_typ b -> map_group (Some b))
  (phi_tag: U64.t -> (b: Cbor.raw_data_item) -> bounded_typ b -> bounded_typ b)
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
= phi_base x ||
  begin match x with
  | Cbor.Array v ->
    match_array_group3 (phi_array x (multi_rec phi_base phi_array phi_map phi_tag)) v
  | Cbor.Map v ->
    matches_map_group (phi_map x (multi_rec phi_base phi_array phi_map phi_tag)) v
  | Cbor.Tagged tag v ->
    phi_tag tag x (multi_rec phi_base phi_array phi_map phi_tag) v
  | _ -> false
  end

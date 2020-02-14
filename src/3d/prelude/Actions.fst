(*
   Copyright 2019 Microsoft Research

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
module Actions
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module LPL = LowParse.Low.Base
module LPLC = LowParse.Low.Combinators
module LPLL = LowParse.Low.List
module LPLF = LowParse.Spec.FLData
module Cast = FStar.Int.Cast
module HS = FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open Prelude
module B = LowStar.Buffer

inline_for_extraction
let action #nz (#k:parser_kind nz) (#t:Type) (p:parser k t)
           (inv:slice_inv) (l:eloc) (on_success:bool) (a:Type)
  = sl: input_buffer_t ->
    pos:LPL.pos_t ->
    res:U64.t ->
    Stack a
      (requires fun h ->
        let open LPL in
        inv sl.LPL.base h /\
        loc_not_unused_in h `loc_includes` l /\
        address_liveness_insensitive_locs `loc_includes` l /\
        l `loc_disjoint` loc_buffer sl.base /\
        (U64.v res <= U64.v validator_max_length ==>
           valid_pos p h sl (uint64_to_uint32 pos) (uint64_to_uint32 res)) /\
        (on_success ==> U64.v res <= U64.v validator_max_length))
      (ensures fun h0 _ h1 ->
        modifies l h0 h1 /\
        h1 `extends` h0 /\
        inv sl.LPL.base h1)

inline_for_extraction
let validate_with_action_t #nz (#k:parser_kind nz) (#t:Type) (p:parser k t) (inv:slice_inv) (l:eloc) (allow_reading:bool) =
  (sl: input_buffer_t) ->
  (pos: U64.t) ->
  Stack U64.t
  (requires fun h ->
    let open LPL in
    inv sl.LPL.base h /\
    loc_not_unused_in h `loc_includes` l /\
    address_liveness_insensitive_locs `loc_includes` l /\
    l `loc_disjoint` loc_buffer sl.base /\
    live_slice h sl /\
    U64.v pos <= U32.v sl.len)
  (ensures fun h res h' ->
    let open LPL in
    modifies l h h' /\
    h' `extends` h /\
    inv sl.LPL.base h' /\ (
    if U64.v res <= U64.v validator_max_length
    then
      valid_pos p h sl (uint64_to_uint32 pos) (uint64_to_uint32 res)
    else True))

inline_for_extraction noextract
let act_with_comment
  (s: string)
  #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
  (#inv:slice_inv) (#l:eloc) (#b:_) (res:Type)
  (a: action p inv l b res)
: Tot (action p inv l b res)
= fun (input:input_buffer_t) startPosition endPosition ->
  LPL.comment s;
  a input startPosition endPosition

inline_for_extraction
let leaf_reader
  #nz
  (#k: parser_kind nz)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (sl: input_buffer_t) ->
  (pos: U32.t) ->
  Stack t
  (requires (fun h ->
    LPL.valid p h sl pos))
  (ensures (fun h res h' ->
    modifies loc_none h h' /\
    h' `extends` h /\
    res == LPL.contents p h sl pos
  ))

inline_for_extraction noextract
let lift_leaf_reader #nz (#k:parser_kind nz) #t (#p:parser k t) (r:LPL.leaf_reader p)
  : leaf_reader p
  = fun input startPosition -> r input startPosition

[@ CMacro ]
let validator_error_action_failed : LPL.validator_error = normalize_term (LPL.set_validator_error_kind 0uL 5uL)

inline_for_extraction
noextract
let validate_with_success_action (name: string) #nz (#k1:parser_kind nz) #t1 (#p1:parser k1 t1) (#inv1:_) (#l1:eloc) (#ar:_)
                         (v1:validate_with_action_t p1 inv1 l1 ar)
                         (#inv2:_) (#l2:eloc) #b (a:action p1 inv2 l2 b bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun   (input: input_buffer_t)
        startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then
         [@(rename_let ("action_success_" ^ name))]
         let b = a input startPosition pos1 in
         if not b then validator_error_action_failed else pos1
    else pos1

inline_for_extraction noextract
let validate_with_error_action (name: string) #nz (#k1:parser_kind nz) #t1 (#p1:parser k1 t1) (#inv1:_) (#l1:eloc) (#ar:_)
                         (v1:validate_with_action_t p1 inv1 l1 ar)
                         (#inv2:_) (#l2:eloc) (a:action p1 inv2 l2 false bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun   (input: input_buffer_t)
        startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then pos1
    else
         [@(rename_let ("action_error_" ^ name))]
         let b = a input startPosition pos1 in
         if not b then validator_error_action_failed else pos1

inline_for_extraction noextract
let validate_ret
  : validate_with_action_t (parse_ret ()) true_inv eloc_none true
  = fun input startPosition -> LPLC.validate_ret () input startPosition

inline_for_extraction noextract
let validate_pair
       (name1: string)
       #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
       (#inv1:_) (#l1:eloc) (#ar1:_) (v1:validate_with_action_t p1 inv1 l1 ar1)
       #nz2 (#k2:parser_kind nz2) #t2 (#p2:parser k2 t2)
       (#inv2:_) (#l2:eloc) (#ar2:_) (v2:validate_with_action_t p2 inv2 l2 ar2)
  : validate_with_action_t (p1 `parse_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false
  = fun   (input: input_buffer_t)
        startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_nondep_then h p1 p2 input (LPL.uint64_to_uint32 startPosition) in
    [@(rename_let ("positionAfter" ^ name1))]
    let pos1 = v1 input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if LPL.is_error pos1
    then begin
      pos1
    end
    else
      [@inline_let] let _ = LPL.valid_facts p2 h input (LPL.uint64_to_uint32 pos1) in
      v2 input pos1

inline_for_extraction noextract
let validate_dep_pair
      (name1: string)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      #nz2 (#k2:parser_kind nz2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t (p1 `parse_dep_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false)
  = fun (input: input_buffer_t) startPosition ->
      let h = HST.get () in
      [@inline_let] let _ = LPLC.valid_dtuple2 h p1 p2 input (LPL.uint64_to_uint32 startPosition) in
      [@(rename_let ("positionAfter" ^ name1))]
      let pos1 = v1 input startPosition in
      let h1 = HST.get() in
      if LPL.is_error pos1
      then begin
        pos1
      end
      else
        [@(rename_let ("" ^ name1))]
        let x = r1 input (LPL.uint64_to_uint32 startPosition) in
        let h15 = HST.get () in
        let _ = modifies_address_liveness_insensitive_unused_in h h15 in
        [@inline_let] let _ = LPLC.valid_facts (p2 x) h input (LPL.uint64_to_uint32 pos1) in
        v2 x input pos1

[@ CMacro ]
let validator_error_constraint_failed : LPL.validator_error = normalize_term (LPL.set_validator_error_kind 0uL 6uL)

[@ CInline ]
let check_constraint_ok (ok:bool) (position:U64.t) : Tot U64.t =
      if ok
      then position
      else validator_error_constraint_failed

[@ CInline ]
let check_constraint_ok_with_field_id (ok:bool) (startPosition: LPL.pos_t) (endPosition:U64.t) (fieldId: field_id) : Tot U64.t =
      if ok
      then endPosition
      else LPL.set_validator_error_pos_and_code validator_error_constraint_failed startPosition fieldId

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine f -> Type) (#p2:(x:refine f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
  = fun (input: input_buffer_t) startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f input (LPL.uint64_to_uint32 startPosition) in
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        res
      end
      else begin
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("pos_or_error_after_" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition res id1 in
        if LPL.is_error res1
        then res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             // [@(rename_let ("action_" ^ name1))]
             // let action_result =  in
             if not (a field_value input startPosition res)
             then LPL.set_validator_error_pos_and_code validator_error_action_failed startPosition id1 //action failed
             else begin
               let open LPL in
               // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 input (LPL.uint64_to_uint32 res1) in
               [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 input (LPL.uint64_to_uint32 startPosition) in
               v2 field_value input res1
             end
        end

#push-options "--z3rlimit 16"

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action_total_zero_parser'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine f -> Type) (#p2:(x:refine f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Pure (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
         (requires (
           let open LP in
           k1.parser_kind_high == Some 0 /\
           k1.parser_kind_metadata == Some ParserKindMetadataTotal
         ))
         (ensures (fun _ -> True))
  = fun (input: input_buffer_t) startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f input (LPL.uint64_to_uint32 startPosition) in
      [@inline_let] let _ = LPLC.valid_facts p1 h0 input (LPL.uint64_to_uint32 startPosition) in
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("pos_or_error_after_" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition startPosition id1 in
        if LPL.is_error res1
        then res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h0 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             // [@(rename_let ("action_" ^ name1))]
             // let action_result =  in
             if not (a field_value input startPosition startPosition)
             then LPL.set_validator_error_pos_and_code validator_error_action_failed startPosition id1 //action failed
             else begin
               let open LPL in
               // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 input (LPL.uint64_to_uint32 res1) in
               [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 input (LPL.uint64_to_uint32 startPosition) in
               v2 field_value input res1
             end
        end

#pop-options

inline_for_extraction noextract
let validate_dep_pair_with_refinement'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine f -> Type) (#p2:(x:refine f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (l1 `eloc_union` l2)
             false)
  = fun (input: input_buffer_t) startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f input (LPL.uint64_to_uint32 startPosition) in
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        res
      end
      else begin
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionOrErrorAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition res id1 in
        if LPL.is_error res1
        then res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 input (LPL.uint64_to_uint32 res1) in
             [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 input (LPL.uint64_to_uint32 startPosition) in
             v2 field_value input res1
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_total_zero_parser'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine f -> Type) (#p2:(x:refine f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Pure (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (l1 `eloc_union` l2)
             false)
         (requires (
           let open LP in
           k1.parser_kind_high == Some 0 /\
           k1.parser_kind_metadata == Some ParserKindMetadataTotal
         ))
         (ensures (fun _ -> True))
  = fun (input: input_buffer_t) startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f input (LPL.uint64_to_uint32 startPosition) in
      [@inline_let] let _ = LPLC.valid_facts p1 h0 input (LPL.uint64_to_uint32 startPosition) in
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionOrErrorAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition startPosition id1 in
        if LPL.is_error res1
        then res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h0 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 input (LPL.uint64_to_uint32 res1) in
             [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 input (LPL.uint64_to_uint32 startPosition) in
             v2 field_value input res1
        end


inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine f -> Type) (#p2:(x:refine f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t ((p1 `parse_filter` f) `parse_dep_pair` p2)
                                (conj_inv inv1 (conj_inv inv1' inv2))
                                (l1 `eloc_union` (l1' `eloc_union` l2))
                                false)
  = if
      p1_is_constant_size_without_actions &&
      k1.LP.parser_kind_high = Some 0 &&
      k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal
    then
      validate_dep_pair_with_refinement_and_action_total_zero_parser' name1 id1 v1 r1 f a v2
    else
      validate_dep_pair_with_refinement_and_action' name1 id1 v1 r1 f a v2

inline_for_extraction noextract
let validate_dep_pair_with_action
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 (#k2:parser_kind nz2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             (p1 `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
  = fun (input: input_buffer_t) startPosition ->
      let h0 = HST.get () in
      let res = v1 input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        res
      end
      else begin
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        let h2 = HST.get() in
        modifies_address_liveness_insensitive_unused_in h1 h2;
        let action_result = a field_value input startPosition res in
        if not action_result
        then validator_error_action_failed //action failed
        else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] let _ = LPLC.valid_dtuple2 h0 p1 p2 input (LPL.uint64_to_uint32 startPosition) in
               v2 field_value input res
             end
      end

inline_for_extraction noextract
let validate_dep_pair_with_refinement
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine f -> Type) (#p2:(x:refine f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t ((p1 `parse_filter` f) `parse_dep_pair` p2)
                                (conj_inv inv1 inv2)
                                (l1 `eloc_union` l2)
                                false)
  = if
      p1_is_constant_size_without_actions &&
      k1.LP.parser_kind_high = Some 0 &&
      k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal
    then
      validate_dep_pair_with_refinement_total_zero_parser' name1 id1 v1 r1 f v2
    else
      validate_dep_pair_with_refinement' name1 id1 v1 r1 f v2

inline_for_extraction noextract
let validate_filter' (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : Tot (validate_with_action_t #nz (p `LPC.parse_filter` f) inv l false)
  = fun input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_filter h p f input (LPL.uint64_to_uint32 startPosition) in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v input startPosition in
    let h1 = HST.get () in
    if LPL.is_error res
    then res
    else begin
      LowStar.Comment.comment cr;
      [@(rename_let ("" ^ name))]
      let field_value = r input (LPL.uint64_to_uint32 startPosition) in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      check_constraint_ok ok res
    end

inline_for_extraction noextract
let validate_filter (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : Tot (validate_with_action_t (p `parse_filter` f) inv l false)
  = validate_filter' name v r f cr cf

inline_for_extraction noextract
let validate_filter'_with_action
                    (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) #inva (#la:eloc) (a: t -> action #nz #(filter_kind k) #_ (p `LPC.parse_filter` f) inva la b bool)
  : Tot (validate_with_action_t #nz (p `LPC.parse_filter` f) (conj_inv inv inva) (eloc_union l la) false)
  = fun input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_filter h p f input (LPL.uint64_to_uint32 startPosition) in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v input startPosition in
    let h1 = HST.get () in
    if LPL.is_error res
    then res
    else begin
      LowStar.Comment.comment cr;
      [@(rename_let ("" ^ name))]
      let field_value = r input (LPL.uint64_to_uint32 startPosition) in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      if ok
        then let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h h15 in
             if a field_value input startPosition res
             then res
             else validator_error_action_failed
      else validator_error_constraint_failed
    end

inline_for_extraction noextract
let validate_filter_with_action
                    (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) #inva (#la:eloc) (a: t -> action (p `parse_filter` f) inva la b bool)
  : Tot (validate_with_action_t #nz (p `parse_filter` f) (conj_inv inv inva) (eloc_union l la) false)
  = validate_filter'_with_action name v r f cr cf a


inline_for_extraction noextract
let validate_with_dep_action
                    (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p)
                    (#b:bool) #inva (#la:eloc) (a: t -> action p inva la b bool)
  : Tot (validate_with_action_t #nz p (conj_inv inv inva) (eloc_union l la) false)
  = fun input startPosition ->
    let h = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v input startPosition in
    let h1 = HST.get () in
    if LPL.is_error res
    then res
    else begin
      [@(rename_let ("" ^ name))]
      let field_value = r input (LPL.uint64_to_uint32 startPosition) in
      let h15 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h15 in
      if a field_value input startPosition res
      then res
      else validator_error_action_failed
    end


private
let valid_weaken #nz (#k:parser_kind nz) #t (p:parser k t)
                 #nz' (k':parser_kind nz'{k' `is_weaker_than` k}) (h:HS.mem)
                 (input:input_buffer_t) (pos:U32.t)
  : Lemma ((forall res. {:pattern (LPL.valid_pos (LP.weaken k' p) h input pos res)}
             LPL.valid_pos p h input pos res <==> LPL.valid_pos (LP.weaken k' p) h input pos res) /\
           (LPL.valid p h input pos <==> LPL.valid (LP.weaken k' p) h input pos))
 =  LPL.valid_facts p h input pos;
    LPL.valid_facts (LP.weaken k' p) h input pos

inline_for_extraction noextract
let validate_weaken #nz (#k:parser_kind nz) #t (#p:parser k t)
                    #inv #l #ar (v:validate_with_action_t p inv l ar)
                    #nz' (k':parser_kind nz'{k' `is_weaker_than` k})
  : Tot (validate_with_action_t (parse_weaken p k') inv l ar)
  = fun (input:input_buffer_t) startPosition ->
    let open LPLC in
    let h = HST.get () in
    [@inline_let]
    let _ = valid_weaken k' p h input (LPL.uint64_to_uint32 startPosition) in
    v input startPosition

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_left #nz  (#k:parser_kind nz) #t (p:parser k t)
                      #nz' (k':parser_kind nz')
  : Tot (parser (glb k' k) t)
  = LP.weaken (glb k' k) p

inline_for_extraction noextract
let validate_weaken_left (#nz:_) (#k:parser_kind nz) (#t:_) (#p:parser k t)
                         (#inv:_) (#l:_) #ar (v:validate_with_action_t p inv l ar)
                         (#nz':_) (k':parser_kind nz')
  : validate_with_action_t (parse_weaken_left p k') inv l ar
  = validate_weaken v (glb k' k)

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_right #nz  (#k:parser_kind nz) #t (p:parser k t)
                       #nz' (k':parser_kind nz')
  : Tot (parser (glb k k') t)
  = LP.weaken (glb k k') p

inline_for_extraction noextract
let validate_weaken_right (#nz:_) (#k:parser_kind nz) (#t:_) (#p:parser k t)
                         (#inv:_) (#l:_) #ar (v:validate_with_action_t p inv l ar)
                         (#nz':_) (k':parser_kind nz')
  : validate_with_action_t (parse_weaken_right p k') inv l ar
  = validate_weaken v (glb k k')

inline_for_extraction noextract
let validate_impos ()
  : Tot (validate_with_action_t (parse_impos ()) true_inv eloc_none true)
  = fun _ _ -> validator_error_impossible

inline_for_extraction noextract
let validate_with_error #nz (#k:parser_kind nz) #t (#p:parser k t)
                        #inv #l #ar (c:field_id) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t p inv l ar)
  = fun input startPosition ->
    let endPositionOrError = v input startPosition in
    LPL.maybe_set_error_code endPositionOrError startPosition c

noextract inline_for_extraction
let validate_ite #nz (#k:parser_kind nz) (#a:Type) (#b:Type)
                 #inv1 #l1 #ar1 #inv2 #l2 #ar2
                 (e:bool)
                 (p1:squash e -> parser k a) (v1:(squash e -> validate_with_action_t (p1()) inv1 l1 ar1))
                 (p2:squash (not e) -> parser k b) (v2:(squash (not e) -> validate_with_action_t (p2()) inv2 l2 ar2))
  : Tot (validate_with_action_t (parse_ite e p1 p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false)
  = fun (input:input_buffer_t) startPosition ->
      if e then v1 () input startPosition else v2 () input startPosition

unfold
let validate_list_inv
  (#k: LPL.parser_kind)
  (#t: Type0)
  (p: LPL.parser k t)
  (inv: slice_inv)
  (l: loc)
  (g0 g1: Ghost.erased HS.mem)
  (sl: input_buffer_t)
  (pos0: U32.t)
  (bpos: pointer U64.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let h0 = Ghost.reveal g0 in
  let h1 = Ghost.reveal g1 in
  inv sl.LPL.base h0 /\
  h `extends` h0 /\
  loc_not_unused_in h0 `loc_includes` l /\
  l `loc_disjoint` loc_buffer sl.LPL.base /\
  l `loc_disjoint` loc_buffer bpos /\
  address_liveness_insensitive_locs `loc_includes` l /\
  disjoint sl.LPL.base bpos /\
  k.LPL.parser_kind_subkind == Some LPL.ParserStrong /\
  k.LPL.parser_kind_low > 0 /\
  U32.v pos0 <= U32.v sl.LPL.len /\
  LPL.live_slice h0 sl /\
  live h1 bpos /\
  modifies loc_none h0 h1 /\
  modifies (l `loc_union` loc_buffer bpos) h1 h /\ (
  let pos1 = Seq.index (as_seq h bpos) 0 in
  if
    LPL.is_error pos1
  then
    stop == true
  else
    U32.v pos0 <= U64.v pos1 /\
    U64.v pos1 <= U32.v sl.LPL.len /\
    (LPL.valid_exact (LPLL.parse_list p) h0 sl pos0 sl.LPL.len <==>
     LPL.valid_exact (LPLL.parse_list p) h0 sl (Cast.uint64_to_uint32 pos1) sl.LPL.len) /\
    (stop == true ==> U64.v pos1 == U32.v sl.LPL.len)
  )

#push-options "--z3rlimit_factor 4"

inline_for_extraction
noextract
let validate_list_body
  (n:U32.t)
  (#k:parser_kind true)
  #t
  (#p:parser k t)
  #inv #l #ar
  (v: validate_with_action_t p inv l ar)
  (g0 g1: Ghost.erased HS.mem)
  (sl: input_buffer_t)
  (pos0: LPL.pos_t)
  (bpos: pointer U64.t)
: HST.Stack bool
  (requires (fun h -> validate_list_inv p inv l g0 g1 sl (LPL.uint64_to_uint32 pos0) bpos h false))
  (ensures (fun h res h' ->
    validate_list_inv p inv l g0 g1 sl (LPL.uint64_to_uint32 pos0) bpos h false /\
    validate_list_inv p inv l g0 g1 sl (LPL.uint64_to_uint32 pos0) bpos h' res
  ))
= let h = HST.get () in
  let elementStartPosition = index bpos 0ul in
  assert (U64.v elementStartPosition <= U32.v sl.LPL.len);
  if elementStartPosition = Cast.uint32_to_uint64 sl.LPL.len
  then true
  else begin
    Classical.move_requires (LPLL.valid_exact_list_cons p (Ghost.reveal g0) sl (LPL.uint64_to_uint32 elementStartPosition)) sl.LPL.len;
    Classical.move_requires (LPLL.valid_exact_list_cons_recip p (Ghost.reveal g0) sl (LPL.uint64_to_uint32 elementStartPosition)) sl.LPL.len;
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in (Ghost.reveal g0) h1;
    let elementEndPosition = v sl elementStartPosition in
    upd bpos 0ul elementEndPosition;
    LPL.is_error elementEndPosition
  end

#pop-options

#push-options "--z3rlimit_factor 4"
inline_for_extraction
noextract
let validate_list'
  (n:U32.t)
  (#k:parser_kind true)
  #t
  (#p:parser k t)
  #inv #l #ar
  (v: validate_with_action_t p inv l ar)
  (sl: input_buffer_t)
  (pos: U64.t)
: HST.Stack U64.t
  (requires (fun h ->
    U64.v pos <= U32.v sl.LPL.len /\
    inv sl.LPL.base h /\
    loc_not_unused_in h `loc_includes` l /\
    l `loc_disjoint` loc_buffer sl.LPL.base /\
    address_liveness_insensitive_locs `loc_includes` l /\
    LPL.live_slice h sl
  ))
  (ensures (fun h res h' ->
    modifies l h h' /\
    inv sl.LPL.base h' /\
    (LPL.is_success res ==> (LPL.valid_exact (LPLL.parse_list p) h sl (LPL.uint64_to_uint32 pos) sl.LPL.len /\ U64.v res == U32.v sl.LPL.len))
  ))
= let h0 = HST.get () in
  let g0 = Ghost.hide h0 in
  HST.push_frame ();
  let h02 = HST.get () in
  fresh_frame_modifies h0 h02;
  let currentPosition = alloca pos 1ul in
  let h1 = HST.get () in
  let g1 = Ghost.hide h1 in
  C.Loops.do_while (validate_list_inv p inv l g0 g1 sl (LPL.uint64_to_uint32 pos) currentPosition) (fun _ -> validate_list_body n v g0 g1 sl pos currentPosition);
  LPLL.valid_exact_list_nil p h0 sl sl.LPL.len;
  let finalPositionOrError = index currentPosition 0ul in
  HST.pop_frame ();
  let h' = HST.get () in
  assert (h' `extends` h0);
  finalPositionOrError
#pop-options

noextract
inline_for_extraction
let validate_nlist
  (n:U32.t)
  (#k:parser_kind true)
  #t
  (#p:parser k t)
  #inv #l #ar
  (v: validate_with_action_t p inv l ar)
: Tot (validate_with_action_t (parse_nlist n p) inv l false)
= fun input pos ->
  let h = HST.get () in
  LPL.valid_facts (parse_nlist n p) h input (LPL.uint64_to_uint32 pos);
  LPLF.parse_fldata_consumes_all_correct (LPLL.parse_list p) (U32.v n) (LPL.bytes_of_slice_from h input (LPL.uint64_to_uint32 pos));
  if (Cast.uint32_to_uint64 input.LPL.len `U64.sub` pos) `U64.lt` Cast.uint32_to_uint64 n
  then LPL.validator_error_not_enough_data
  else begin
    let listInput = LPL.make_slice input.LPL.base (LPL.uint64_to_uint32 pos `U32.add` n) in
    LPL.valid_exact_equiv (LPLL.parse_list p) h listInput (LPL.uint64_to_uint32 pos) (LPL.uint64_to_uint32 pos `U32.add` n);
    validate_list' n v listInput pos
  end

noextract
inline_for_extraction
let validate_nlist_constant_size_without_actions
  (n_is_const: bool)
  (n:U32.t)
  (#k:parser_kind true)
  #t (#p:parser k t) #inv #l #ar
  (v: validate_with_action_t p inv l ar)
: Tot (validate_with_action_t (parse_nlist n p) inv l false)
= if
    let open LP in
    k.parser_kind_subkind = Some ParserStrong &&
    k.parser_kind_high = Some k.parser_kind_low &&
    k.parser_kind_metadata = Some ParserKindMetadataTotal &&
    k.parser_kind_low < 4294967296
  then
    (fun input startPosition ->
      let h = HST.get () in
      assert (forall h' . {:pattern (B.modifies B.loc_none h h')} (B.modifies B.loc_none h h' /\ inv input.LPL.base h) ==> h' `extends` h);
      assert (forall h' . {:pattern (B.modifies B.loc_none h h')} (B.modifies B.loc_none h h' /\ inv input.LPL.base h) ==> inv input.LPL.base h');
      validate_nlist_total_constant_size n_is_const n p input startPosition
    )
  else
    validate_nlist n v

inline_for_extraction noextract
let validate_with_comment (c:string)
                          #nz (#k:parser_kind nz) #t (#p:parser k t)
                          #inv #l #ar (v:validate_with_action_t p inv l ar)
  : validate_with_action_t p inv l ar
  = fun input startPosition ->
    LowParse.Low.Base.comment c;
    v input startPosition

inline_for_extraction noextract
let validate_weaken_inv_loc #nz (#k:parser_kind nz) #t (#p:parser k t)
                            #inv (#l:eloc) #ar
                            (inv':slice_inv{inv' `inv_implies` inv}) (l':eloc{l' `eloc_includes` l})
                            (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t p inv' l' ar)
  = v

////////////////////////////////////////////////////////////////////////////////
//Base types
////////////////////////////////////////////////////////////////////////////////
inline_for_extraction noextract
let read_filter #nz
                (#k: parser_kind nz)
                (#t: Type0)
                (#p: parser k t)
                (p32: leaf_reader p)
                (f: (t -> bool))
    : leaf_reader (parse_filter p f)
    = fun input startPosition ->
        let h = HST.get () in
        assert (LPL.valid #triv #triv #(filter_kind k) #(Prelude.refine t f) (parse_filter p f) h input startPosition);
        assert (parse_filter p f == LPC.parse_filter #k #t p f);
        assert (LPL.valid #triv #triv #(filter_kind k) #(Prelude.refine t f) (LPC.parse_filter #k #t p f) h input startPosition);
        assert (LPL.valid #triv #triv #(filter_kind k) #(x:t{f x}) (LPC.parse_filter #k #t p f) h input startPosition);
        assert (LPL.valid #triv #triv #(LPC.parse_filter_kind k) #(x:t{f x}) (LPC.parse_filter #k #t p f) h input startPosition);
        assert_norm (Prelude.refine t f == LPC.parse_filter_refine f);
        [@inline_let] let _ = LPLC.valid_filter h p f input startPosition in
        assert (LPL.valid p h input startPosition);
        p32 input startPosition


inline_for_extraction noextract
let validate____UINT8
  : validator parse____UINT8
  = fun input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a UINT8, i.e., 1 byte";
    LowParse.Low.Int.validate_u8 () input startPosition

inline_for_extraction noextract
let read____UINT8
  : leaf_reader parse____UINT8
  = LowParse.Low.Int.read_u8 #_ #_

inline_for_extraction noextract
let validate____UINT16
  : validator parse____UINT16
  = fun input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a UINT16, i.e., 2 bytes";
    LowParse.Low.BoundedInt.validate_u16_le () input startPosition

inline_for_extraction noextract
let read____UINT16
  : leaf_reader parse____UINT16
  = LowParse.Low.BoundedInt.read_u16_le #_ #_

inline_for_extraction noextract
let validate____UINT32
  : validator parse____UINT32
  = fun input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a ULONG, i.e., 4 bytes";
    LowParse.Low.BoundedInt.validate_u32_le () input startPosition

inline_for_extraction noextract
let read____UINT32
  : leaf_reader parse____UINT32
  = LowParse.Low.BoundedInt.read_u32_le #_ #_

inline_for_extraction noextract
let validate____UINT64
  : validator parse____UINT64
  = fun input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a ULONG64, i.e., 8 bytes";
    LowParse.Low.Int.validate_u64_le () input startPosition

inline_for_extraction noextract
let read____UINT64
  : leaf_reader parse____UINT64
  = LowParse.Low.Int.read_u64_le #_ #_

inline_for_extraction noextract
let validate_unit
  : validator parse_unit
  = validate_ret

inline_for_extraction noextract
let read_unit
  : leaf_reader (parse_ret ())
  = LPLC.read_ret () #_ #_

inline_for_extraction noextract
let validate_unit_refinement' (f:unit -> bool) (cf:string)
  : Tot (validate_with_action_t #false (parse_unit `LPC.parse_filter` f) true_inv eloc_none true)
  = fun input startPosition ->
      let h = HST.get () in
      [@inline_let] let _ = LPLC.valid_facts (parse_unit) h input (LPL.uint64_to_uint32 startPosition) in
      [@inline_let] let _ = LPLC.valid_filter h parse_unit f input (LPL.uint64_to_uint32 startPosition) in
      LowStar.Comment.comment cf;
      if f ()
      then
        startPosition
      else validator_error_constraint_failed

inline_for_extraction noextract
let validate_unit_refinement (f:unit -> bool) (cf:string)
  : Tot (validator (parse_unit `parse_filter` f))
  = validate_unit_refinement' f cf

////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
let action_return
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#a:Type) (x:a)
  : action p true_inv eloc_none false a
  = fun input startPosition endPosition -> x

noextract
inline_for_extraction
let action_bind
      (name: string)
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      #bf (#a:Type) (f: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (#b:Type) (g: (a -> action p invg lg bg b))
  : Tot (action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) b)
  = fun input startPosition endPosition ->
    let h0 = HST.get () in
    [@(rename_let ("" ^ name))]
    let x = f input startPosition endPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g x input startPosition endPosition

noextract
inline_for_extraction
let action_seq
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      #bf (#a:Type) (f: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (#b:Type) (g: action p invg lg bg b)
  : Tot (action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) b)
  = fun input startPosition endPosition ->
    let h0 = HST.get () in
    let _ = f input startPosition endPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g input startPosition endPosition

noextract
inline_for_extraction
let action_ite
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      (guard:bool)
      #bf (#a:Type) (then_: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (#b:Type) (else_: action p invg lg bg a)
  : action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) a
  = fun input startPosition endPosition -> if guard then then_ input startPosition endPosition else else_ input startPosition endPosition

noextract
inline_for_extraction
let action_abort
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
  : action p true_inv eloc_none false bool
  = fun input startPosition endPosition -> false

noextract
inline_for_extraction
let action_field_pos
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none false U32.t
   = fun _ startPosition _ -> LPL.uint64_to_uint32 startPosition


noextract
inline_for_extraction
let action_field_ptr
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none true (B.buffer LowParse.Bytes.byte)
   = fun input startPosition _ ->
       let open LowParse.Slice in
       B.moffset triv input.base (LPL.uint64_to_uint32 startPosition)

noextract
inline_for_extraction
let action_deref
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a)
   : action p (ptr_inv x) loc_none false a
   = fun _ _ _ -> !*x

noextract
inline_for_extraction
let action_assignment
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a) (v:a)
   : action p (ptr_inv x) (ptr_loc x) false unit
   = fun _ _ _ -> x *= v

noextract
inline_for_extraction
let action_read_value
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (r:leaf_reader p)
   : action p true_inv eloc_none true t
   = fun input startPosition endPosition ->
     r input (LPL.uint64_to_uint32 startPosition)

noextract
inline_for_extraction
let action_weaken
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#inv:slice_inv) (#l:eloc) (#b:_) (#a:_) (act:action p inv l b a)
      (#inv':slice_inv{inv' `inv_implies` inv}) (#l':eloc{l' `eloc_includes` l})
   : action p inv' l' b a
   = act

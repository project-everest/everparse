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
module LPL = EverParse3d.InputBuffer
module R = EverParse3d.Readable
module LPLC = LowParse.Low.Combinators
module LPLL = LowParse.Low.List
module LPLF = LowParse.Spec.FLData
module Cast = FStar.Int.Cast
module HS = FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
friend Prelude
open Prelude
module B = LowStar.Buffer

(* FIXME: Those functions CANNOT be put into a KReMLin root because:

Bundling creates a dependency cycle:
ResultOps.check_constraint_ok_with_field_id (found in file EverParse) mentions FStar.Monotonic.HyperStack.mem (found in file SHOULDNOTBETHERE)
FStar.Seq.Base.slice (found in file SHOULDNOTBETHERE) mentions Prims.nat (found in file EverParse)
Fat

*)

inline_for_extraction
noextract
let check_constraint_ok (maybe_fail: B.pointer U64.t) (ok:bool) (position:U32.t) : HST.Stack U32.t
  (requires (fun h -> B.live h maybe_fail))
  (ensures (fun h res h' ->
    B.modifies (if ok then B.loc_none else B.loc_buffer maybe_fail) h h' /\
    res == position /\
    ((~ ok) ==> LPL.is_error (B.get h' maybe_fail 0))
  ))
=
      if not ok
      then B.upd maybe_fail 0ul validator_error_constraint_failed;
      position

inline_for_extraction
noextract
let check_constraint_ok_with_field_id (maybe_fail: B.pointer U64.t) (ok:bool) (startPosition: U32.t) (endPosition:U32.t) (fieldId: field_id) : HST.Stack U32.t
  (requires (fun h -> B.live h maybe_fail))
  (ensures (fun h res h' ->
    B.modifies (if ok then B.loc_none else B.loc_buffer maybe_fail) h h' /\
    res == (if ok then endPosition else startPosition) /\
    ((~ ok) ==> LPL.is_error (B.get h' maybe_fail 0))
  ))
=
      if ok
      then endPosition
      else begin
        B.upd maybe_fail 0ul (LPL.set_validator_error_pos_and_code validator_error_constraint_failed 0uL fieldId);
        startPosition
      end

inline_for_extraction
noextract
let set_error_code
  (maybe_fail: B.pointer U64.t)
  (endPosition: U32.t)
  (startPosition: U32.t)
  (code: LPL.error_code)
 : HST.Stack U32.t
   (requires (fun h -> B.live h maybe_fail))
   (ensures (fun h res h' ->
     let is_error = LPL.is_error (B.get h maybe_fail 0) in
     B.modifies (if is_error then B.loc_buffer maybe_fail else B.loc_none) h h' /\
     res == (if is_error then startPosition else endPosition) /\
     (is_error ==> LPL.is_error (B.get h' maybe_fail 0))
   ))
  = let maybe_error = B.index maybe_fail 0ul in
    if LPL.is_error maybe_error
    then begin
      if LPL.get_validator_error_code maybe_error = 0uL
      then B.upd maybe_fail 0ul (LPL.set_validator_error_code maybe_error code);
      startPosition
    end else endPosition


inline_for_extraction
let action #nz (#k:parser_kind nz) (#t:Type) (p:parser k t)
           (inv:slice_inv) (l:eloc) (on_success:bool) (a:Type)
  =
    (maybe_fail: B.pointer U64.t) ->
    #len: U32.t ->
    sl: input_buffer_t len ->
    pos:U32.t ->
    res:U32.t ->
    Stack a
      (requires fun h ->
        let open LPL in
        let is_success = LPL.is_success (B.get h maybe_fail 0) in
        B.live h maybe_fail /\
        B.loc_buffer maybe_fail `B.loc_disjoint` LPL.loc_input_buffer sl /\
        l `B.loc_disjoint` B.loc_buffer maybe_fail /\
        LPL.live_input_buffer h sl /\
        inv (LPL.slice_of sl).LPL.base h /\
        loc_not_unused_in h `loc_includes` l /\
        address_liveness_insensitive_locs `loc_includes` l /\
        l `loc_disjoint` LPL.loc_input_buffer sl /\
        (is_success ==>
           valid_pos p h (LPL.slice_of sl) pos res) /\
        (on_success ==> is_success))
      (ensures fun h0 _ h1 ->
        modifies l h0 h1 /\
        h1 `extends` h0 /\
        inv (LPL.slice_of sl).LPL.base h1)

inline_for_extraction
let validate_with_action_t #nz (#k:parser_kind nz) (#t:Type) (p:parser k t) (inv:slice_inv) (l:eloc) (allow_reading:bool) =
  (maybe_fail: B.pointer U64.t) ->
  (#len: U32.t) ->
  (sl: input_buffer_t len) ->
  (pos: U32.t) ->
  Stack U32.t
  (requires fun h ->
    let open LPL in
    live_input_buffer h sl /\
    inv (slice_of sl).base h /\
    loc_not_unused_in h `loc_includes` l /\
    address_liveness_insensitive_locs `loc_includes` l /\
    l `loc_disjoint` (LPL.loc_input_buffer sl `B.loc_union` B.loc_buffer maybe_fail) /\
    LPL.loc_input_buffer sl `B.loc_disjoint` B.loc_buffer maybe_fail /\
    B.live h maybe_fail /\
    U32.v pos <= U32.v (slice_of sl).len /\
    R.readable h (perm_of sl) (pos) (slice_of sl).len
  )
  (ensures fun h res h' ->
    let open LPL in
    let is_success = LPL.is_success (B.get h' maybe_fail 0) in
    h' `extends` h /\
    live_input_buffer h' sl /\
    inv (slice_of sl).base h' /\
    (is_success ==> valid_pos p h (slice_of sl) pos res) /\
    modifies
      (B.loc_buffer maybe_fail `B.loc_union` (if allow_reading then l else l `loc_union` (R.loc_perm_from_to (perm_of sl) pos (if is_success then res else (slice_of sl).len))))
      h h' /\
    ((~ allow_reading) ==> R.unreadable h' (perm_of sl) pos (if is_success then res else (slice_of sl).len))
  )

let validate_eta v =
  fun maybe_fail input startPosition -> v maybe_fail input startPosition

inline_for_extraction noextract
let act_with_comment
  (s: string)
  #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
  (#inv:slice_inv) (#l:eloc) (#b:_) (res:Type)
  (a: action p inv l b res)
: Tot (action p inv l b res)
= fun maybe_fail input startPosition endPosition ->
  LPL.comment s;
  a maybe_fail input startPosition endPosition

inline_for_extraction
let leaf_reader
  #nz
  (#k: parser_kind nz)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (#len: U32.t) ->
  (sl: input_buffer_t len) ->
  (pos: U32.t) ->
  Stack t
  (requires (fun h ->
    LPL.valid p h (LPL.slice_of sl) pos /\
    R.readable h (LPL.perm_of sl) pos (LPL.get_valid_pos p h (LPL.slice_of sl) pos)
  ))
  (ensures (fun h res h' ->
    let pos' = LPL.get_valid_pos p h (LPL.slice_of sl) pos in
    modifies (R.loc_perm_from_to (LPL.perm_of sl) pos pos') h h' /\
    R.unreadable h' (LPL.perm_of sl) pos pos' /\
    h' `extends` h /\
    res == LPL.contents p h (LPL.slice_of sl) pos
  ))

inline_for_extraction noextract
let lift_constant_size_leaf_reader #nz (#k:parser_kind nz) #t (#p:parser k t) (r:LPL.leaf_reader p) (sz: U32.t { k.LPL.parser_kind_high == Some k.LPL.parser_kind_low /\ k.LPL.parser_kind_low == U32.v sz })
  : leaf_reader p
  = fun input startPosition ->
      LPL.read_with_perm r (LPL.jump_constant_size p sz ()) input startPosition

inline_for_extraction
noextract
let with_drop_if
  (#t: Type)
  (cond: bool)
  (inv: slice_inv)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (from: U32.t)
  (fto: ((x: t) -> Tot U32.t))
  (x: t)
: HST.Stack t
  (requires (fun h ->
    let to = fto x in
    U32.v from <= U32.v to /\
    U32.v to <= U32.v (LPL.slice_of sl).LPL.len /\
    LPL.live_input_buffer h sl /\
    inv (LPL.slice_of sl).LPL.base h
  ))
  (ensures (fun h res h' ->
    B.modifies (if cond then R.loc_perm_from_to (LPL.perm_of sl) from (fto x) else B.loc_none) h h' /\
    LPL.live_input_buffer h' sl /\
    (cond ==> R.unreadable h' (LPL.perm_of sl) from (fto x)) /\
    inv (LPL.slice_of sl).LPL.base h' /\
    res == x
  ))
= let h1 = HST.get () in
  if cond then LPL.drop sl from (fto x);
  let h2 = HST.get () in
  [@inline_let] let _ = assert (h2 `extends` h1) in
  x

inline_for_extraction
noextract
let validate_drop
   #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t) (#inv:slice_inv) (#l:eloc) (#allow_reading:bool)
   (v: validate_with_action_t p inv l allow_reading)
: Tot (validate_with_action_t p inv l false)
= fun
  maybe_fail
  input
  startPosition ->
  let res = v maybe_fail input startPosition in
  let to = if LPL.is_success (B.index maybe_fail 0ul) then res else LPL.slice_length input in
  let h1 = HST.get () in
  LPL.drop input startPosition to;
  let h2 = HST.get () in
  [@inline_let] let _ = assert (h2 `extends` h1) in
  res

#push-options "--z3rlimit 16"
inline_for_extraction
noextract
let validate_with_success_action' (name: string) #nz (#k1:parser_kind nz) #t1 (#p1:parser k1 t1) (#inv1:_) (#l1:eloc) (#ar:_)
                         (v1:validate_with_action_t p1 inv1 l1 ar)
                         (#inv2:_) (#l2:eloc) #b (a:action p1 inv2 l2 b bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun   
        maybe_fail
        input
        startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 maybe_fail input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success (B.index maybe_fail 0ul)
    then
         [@(rename_let ("action_success_" ^ name))]
         let b = a maybe_fail input startPosition pos1 in
         if not b
         then begin
           B.upd maybe_fail 0ul validator_error_action_failed;
           let h2 = HST.get () in
           assert (h2 `extends` h1);
           with_drop_if (not ar) (conj_inv inv1 inv2) input startPosition (fun _ -> LPL.slice_length input) pos1
         end else
           pos1
    else
         pos1
#pop-options

let validate_with_success_action
  name
  #nz #k1 #t1 #p1 #inv1 #l1 #ar v1
  #inv2 #l2 #b a
= validate_drop (validate_with_success_action' name v1 a)

#push-options "--z3rlimit 16"
inline_for_extraction noextract
let validate_with_error_action' (name: string) #nz (#k1:parser_kind nz) #t1 (#p1:parser k1 t1) (#inv1:_) (#l1:eloc) (#ar:_)
                         (v1:validate_with_action_t p1 inv1 l1 ar)
                         (#inv2:_) (#l2:eloc) (a:action p1 inv2 l2 false bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun
        maybe_fail
        input
        startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 maybe_fail input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success (B.index maybe_fail 0ul)
    then pos1
    else begin
         [@(rename_let ("action_error_" ^ name))]
         let b = a maybe_fail input startPosition pos1 in
         if not b then B.upd maybe_fail 0ul validator_error_action_failed;
         let h2 = HST.get () in
         assert (h2 `extends` h1);
         pos1
    end
#pop-options

let validate_with_error_action
  name
  #nz #k1 #t1 #p1 #inv1 #l1 #ar v1
  #inv2 #l2 a
= validate_drop (validate_with_error_action' name v1 a)

inline_for_extraction noextract
let validate_ret
  : validate_with_action_t (parse_ret ()) true_inv eloc_none true
  = fun maybe_fail input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPL.valid_facts (parse_ret ()) h (LPL.slice_of input) (startPosition) in
    startPosition

#push-options "--z3rlimit 16"

inline_for_extraction noextract
let validate_pair'
       (name1: string)
       #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
       (#inv1:_) (#l1:eloc) (#ar1:_) (v1:validate_with_action_t p1 inv1 l1 ar1)
       #nz2 (#k2:parser_kind nz2) #t2 (#p2:parser k2 t2)
       (#inv2:_) (#l2:eloc) (#ar2:_) (v2:validate_with_action_t p2 inv2 l2 ar2)
  : validate_with_action_t (p1 `parse_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) (ar1 && ar2)
  = fun   
        maybe_fail
        input
        startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_nondep_then h p1 p2 (LPL.slice_of input) (startPosition) in
    [@(rename_let ("positionAfter" ^ name1))]
    let pos1 = v1 maybe_fail input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if LPL.is_error (B.index maybe_fail 0ul)
    then begin
      with_drop_if (not (ar1 && ar2)) (conj_inv inv1 inv2) input (startPosition) (fun _ -> LPL.slice_length input) pos1
    end
    else
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (startPosition) (pos1) (LPL.slice_length input) in
      [@inline_let] let _ = LPL.valid_facts p2 h (LPL.slice_of input) (pos1) in
      let res = v2 maybe_fail input pos1 in
      let is_success = LPL.is_success (B.index maybe_fail 0ul) in
      with_drop_if (not (ar1 && ar2)) (conj_inv inv1 inv2) input (startPosition) (fun x -> if is_success then x else LPL.slice_length input) res

let validate_pair
  name1
  #nz1 #k1 #t1 #p1 #inv1 #l1 #ar1 v1
  #nz2 #k2 #t2 #p2 #inv2 #l2 #ar2 v2
= validate_drop (validate_pair' name1 v1 v2)

inline_for_extraction noextract
let validate_dep_pair
      (name1: string)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      #nz2 (#k2:parser_kind nz2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t (p1 `parse_dep_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false)
  = fun maybe_fail input startPosition ->
      let h = HST.get () in
      [@inline_let] let _ = LPLC.valid_dtuple2 h p1 p2 (LPL.slice_of input) (startPosition) in
      [@(rename_let ("positionAfter" ^ name1))]
      let pos1 = v1 maybe_fail input startPosition in
      let h1 = HST.get() in
      if LPL.is_error (B.index maybe_fail 0ul)
      then begin
        with_drop_if true (conj_inv inv1 inv2) input (startPosition) (fun _ -> LPL.slice_length input) pos1
      end
      else
        [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (startPosition) (pos1) (LPL.slice_length input) in
        [@(rename_let ("" ^ name1))]
        let x = r1 input (startPosition) in
        let h15 = HST.get () in
        let _ = modifies_address_liveness_insensitive_unused_in h h15 in
        [@inline_let] let _ = LPLC.valid_facts (p2 x) h (LPL.slice_of input) (pos1) in
        let res = v2 x maybe_fail input pos1 in
        let is_success = LPL.is_success (B.index maybe_fail 0ul) in
        with_drop_if true (conj_inv inv1 inv2) input (startPosition) (fun y -> if is_success then y else LPL.slice_length input) res

#pop-options

#push-options "--z3rlimit 128"

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
  = fun maybe_fail input startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f (LPL.slice_of input) (startPosition) in
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 maybe_fail input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error (B.index maybe_fail 0ul)
      then begin
        with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun _ -> LPL.slice_length input) res
      end
      else begin
        [@inline_let] let _ = R.readable_split h0 (LPL.perm_of input) (startPosition) (res) (LPL.slice_length input) in
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("pos_or_error_after_" ^ name1))]
        let res1 = check_constraint_ok_with_field_id maybe_fail ok startPosition res id1 in
        let h2 = HST.get () in
        assert (h2 `extends` h1);
        if LPL.is_error (B.index maybe_fail 0ul)
        then
          with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun _ -> LPL.slice_length input) res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             // [@(rename_let ("action_" ^ name1))]
             // let action_result =  in
             if not (a field_value maybe_fail input startPosition res)
             then begin
               B.upd maybe_fail 0ul (LPL.set_validator_error_pos_and_code validator_error_action_failed 0uL id1);
               let h3 = HST.get () in
               assert (h3 `extends` h2);
               with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun _ -> LPL.slice_length input) startPosition //action failed
             end else begin
               let open LPL in
               // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 (LPL.slice_of input) (res1) in
               [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 (LPL.slice_of input) (startPosition) in
               let res = v2 field_value maybe_fail input res1 in
               let is_success = LPL.is_success (B.index maybe_fail 0ul) in
               with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun x -> if is_success then x else LPL.slice_length input) res
             end
        end

#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action_total_zero_parser'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
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
  = fun maybe_fail input startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f (LPL.slice_of input) (startPosition) in
      [@inline_let] let _ = LPLC.valid_facts p1 h0 (LPL.slice_of input) (startPosition) in
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@inline_let] let _ = R.readable_split h0 (LPL.perm_of input) (startPosition) (startPosition) (LPL.slice_length input) in
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("pos_or_error_after_" ^ name1))]
        let res1 = check_constraint_ok_with_field_id maybe_fail ok startPosition startPosition id1 in
        let h1 = HST.get () in
        assert (h1 `extends` h0);
        if LPL.is_error (B.index maybe_fail 0ul)
        then
             with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun _ -> LPL.slice_length input) res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h0 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             // [@(rename_let ("action_" ^ name1))]
             // let action_result =  in
             if not (a field_value maybe_fail input startPosition startPosition)
             then begin
               B.upd maybe_fail 0ul (LPL.set_validator_error_pos_and_code validator_error_action_failed 0uL id1);
               let h3 = HST.get () in
               assert (h3 `extends` h2);
               with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun _ -> LPL.slice_length input) startPosition //action failed
             end else begin
               let open LPL in
               // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 (LPL.slice_of input) (res1) in
               [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 (LPL.slice_of input) (startPosition) in
               let res = v2 field_value maybe_fail input res1 in
               let is_success = LPL.is_success (B.index maybe_fail 0ul) in
               with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun x -> if is_success then x else LPL.slice_length input) res
             end
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (l1 `eloc_union` l2)
             false)
  = fun maybe_fail input startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f (LPL.slice_of input) (startPosition) in
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 maybe_fail input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error (B.index maybe_fail 0ul)
      then begin
        with_drop_if true (conj_inv inv1 inv2) input (startPosition) (fun _ -> LPL.slice_length input) res
      end
      else begin
        [@inline_let] let _ = R.readable_split h0 (LPL.perm_of input) (startPosition) (res) (LPL.slice_length input) in
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id maybe_fail ok startPosition res id1 in
        let h1 = HST.get () in
        assert (h1 `extends` h0);
        if LPL.is_error (B.index maybe_fail 0ul)
        then
             with_drop_if true (conj_inv inv1 inv2) input (startPosition) (fun _ -> LPL.slice_length input) res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 (LPL.slice_of input) (res1) in
             [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 (LPL.slice_of input) (startPosition) in
             let res = v2 field_value maybe_fail input res1 in
             let is_success = LPL.is_success (B.index maybe_fail 0ul) in
             with_drop_if true (conj_inv inv1 inv2) input (startPosition) (fun y -> if is_success then y else LPL.slice_length input) (res)
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_total_zero_parser'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
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
  = fun maybe_fail input startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f (LPL.slice_of input) (startPosition) in
      [@inline_let] let _ = LPLC.valid_facts p1 h0 (LPL.slice_of input) (startPosition) in
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@inline_let] let _ = R.readable_split h0 (LPL.perm_of input) (startPosition) (startPosition) (LPL.slice_length input) in
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id maybe_fail ok startPosition startPosition id1 in
        let h1 = HST.get () in
        assert (h1 `extends` h0);
        if LPL.is_error (B.index maybe_fail 0ul)
        then with_drop_if true (conj_inv inv1 inv2) input (startPosition) (fun _ -> LPL.slice_length input) res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h0 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 (LPL.slice_of input) (res1) in
             [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 (LPL.slice_of input) (startPosition) in
             let res = v2 field_value maybe_fail input res1 in
             let is_success = LPL.is_success (B.index maybe_fail 0ul) in
             with_drop_if true (conj_inv inv1 inv2) input (startPosition) (fun y -> if is_success then y else LPL.slice_length input) (res)
        end

#pop-options

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t ((p1 `parse_filter` f) `parse_dep_pair` p2)
                                (conj_inv inv1 (conj_inv inv1' inv2))
                                (l1 `eloc_union` (l1' `eloc_union` l2))
                                false)
  = if
      p1_is_constant_size_without_actions `LP.bool_and`
      (k1.LP.parser_kind_high = Some 0) `LP.bool_and`
      (k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal)
    then
      validate_dep_pair_with_refinement_and_action_total_zero_parser' name1 id1 v1 r1 f a v2
    else
      validate_dep_pair_with_refinement_and_action' name1 id1 v1 r1 f a v2

#push-options "--z3rlimit 64"

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
  = fun maybe_fail input startPosition ->
      let h0 = HST.get () in
      let res = v1 maybe_fail input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error (B.index maybe_fail 0ul)
      then begin
        with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun _ -> LPL.slice_length input) res
      end
      else begin
        [@inline_let] let _ = R.readable_split h0 (LPL.perm_of input) (startPosition) (res) (LPL.slice_length input) in
        let field_value = r1 input (startPosition) in
        let h2 = HST.get() in
        modifies_address_liveness_insensitive_unused_in h1 h2;
        let action_result = a field_value maybe_fail input startPosition res in
        if not action_result
        then begin
          B.upd maybe_fail 0ul validator_error_action_failed;
          let h2 = HST.get () in
          assert (h2 `extends` h1);
          with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun _ -> LPL.slice_length input) startPosition //action failed
        end else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] let _ = LPLC.valid_dtuple2 h0 p1 p2 (LPL.slice_of input) (startPosition) in
               let res = v2 field_value maybe_fail input res in
               let is_success = LPL.is_success (B.index maybe_fail 0ul) in
               with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (startPosition) (fun y -> if is_success then y else LPL.slice_length input) (res)
             end
      end

#pop-options

inline_for_extraction noextract
let validate_dep_pair_with_refinement
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 (#k2:parser_kind nz2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t ((p1 `parse_filter` f) `parse_dep_pair` p2)
                                (conj_inv inv1 inv2)
                                (l1 `eloc_union` l2)
                                false)
  = if
      p1_is_constant_size_without_actions `LP.bool_and`
      (k1.LP.parser_kind_high = Some 0) `LP.bool_and`
      (k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal)
    then
      validate_dep_pair_with_refinement_total_zero_parser' name1 id1 v1 r1 f v2
    else
      validate_dep_pair_with_refinement' name1 id1 v1 r1 f v2

inline_for_extraction noextract
let validate_filter' (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : Tot (validate_with_action_t #nz (p `LPC.parse_filter` f) inv l false)
  = fun maybe_fail input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_filter h p f (LPL.slice_of input) (startPosition) in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v maybe_fail input startPosition in
    let h1 = HST.get () in
    if LPL.is_error (B.index maybe_fail 0ul)
    then with_drop_if true inv input (startPosition) (fun _ -> LPL.slice_length input) res
    else begin
      LowStar.Comment.comment cr;
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (startPosition) (res) (LPL.slice_length input) in
      [@(rename_let ("" ^ name))]
      let field_value = r input (startPosition) in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      let res = check_constraint_ok maybe_fail ok res in
      let is_success = LPL.is_success (B.index maybe_fail 0ul) in
      let h2 = HST.get () in
      assert (h2 `extends` h1);
      with_drop_if true inv input (startPosition) (fun y -> if is_success then y else LPL.slice_length input) (res)
    end

inline_for_extraction noextract
let validate_filter (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : Tot (validate_with_action_t (p `parse_filter` f) inv l false)
  = validate_filter' name v r f cr cf

#push-options "--z3rlimit 16"
inline_for_extraction noextract
let validate_filter'_with_action
                    (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) #inva (#la:eloc) (a: t -> action #nz #(filter_kind k) #_ (p `LPC.parse_filter` f) inva la b bool)
  : Tot (validate_with_action_t #nz (p `LPC.parse_filter` f) (conj_inv inv inva) (eloc_union l la) false)
  = fun maybe_fail input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_filter h p f (LPL.slice_of input) (startPosition) in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v maybe_fail input startPosition in
    let h1 = HST.get () in
    if LPL.is_error (B.index maybe_fail 0ul)
    then with_drop_if true (conj_inv inv inva) input (startPosition) (fun _ -> LPL.slice_length input) res
    else begin
      LowStar.Comment.comment cr;
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (startPosition) (res) (LPL.slice_length input) in
      [@(rename_let ("" ^ name))]
      let field_value = r input (startPosition) in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      if ok
        then let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h h15 in
             if a field_value maybe_fail input startPosition res
             then res
             else begin
               B.upd maybe_fail 0ul validator_error_action_failed;
               let h2 = HST.get () in
               assert (h2 `extends` h1);
               with_drop_if true (conj_inv inv inva) input (startPosition) (fun _ -> LPL.slice_length input) res
             end
      else begin
        B.upd maybe_fail 0ul validator_error_constraint_failed;
        let h2 = HST.get () in
        assert (h2 `extends` h1);
        with_drop_if true (conj_inv inv inva) input (startPosition) (fun _ -> LPL.slice_length input) res
      end
    end
#pop-options

inline_for_extraction noextract
let validate_filter_with_action
                    (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) #inva (#la:eloc) (a: t -> action (p `parse_filter` f) inva la b bool)
  : Tot (validate_with_action_t #nz (p `parse_filter` f) (conj_inv inv inva) (eloc_union l la) false)
  = validate_filter'_with_action name v r f cr cf a

#push-options "--z3rlimit 16"
inline_for_extraction noextract
let validate_with_dep_action
                    (name: string) #nz (#k:parser_kind nz) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p)
                    (#b:bool) #inva (#la:eloc) (a: t -> action p inva la b bool)
  : Tot (validate_with_action_t #nz p (conj_inv inv inva) (eloc_union l la) false)
  = fun maybe_fail input startPosition ->
    let h = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v maybe_fail input startPosition in
    let h1 = HST.get () in
    if LPL.is_error (B.index maybe_fail 0ul)
    then with_drop_if true (conj_inv inv inva) input (startPosition) (fun _ -> LPL.slice_length input) res
    else begin
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (startPosition) (res) (LPL.slice_length input) in
      [@(rename_let ("" ^ name))]
      let field_value = r input (startPosition) in
      let h15 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h15 in
      if a field_value maybe_fail input startPosition res
      then res
      else begin
        B.upd maybe_fail 0ul validator_error_action_failed;
        let h2 = HST.get () in
        assert (h2 `extends` h1);
        with_drop_if true (conj_inv inv inva) input (startPosition) (fun _ -> LPL.slice_length input) res
      end
    end
#pop-options

inline_for_extraction noextract
let validate_weaken #nz (#k:parser_kind nz) #t (#p:parser k t)
                    #inv #l #ar (v:validate_with_action_t p inv l ar)
                    #nz' (k':parser_kind nz'{k' `is_weaker_than` k})
  : Tot (validate_with_action_t (parse_weaken p k') inv l ar)
  = fun maybe_fail input startPosition ->
    let open LPLC in
    let h = HST.get () in
    [@inline_let]
    let _ = valid_weaken k' p h (LPL.slice_of input) (startPosition) in
    v maybe_fail input startPosition

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
  = fun maybe_fail _ startPosition -> 
    B.upd maybe_fail 0ul validator_error_impossible;
    startPosition

inline_for_extraction noextract
let validate_with_error #nz (#k:parser_kind nz) #t (#p:parser k t)
                        #inv #l #ar (c:field_id) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t p inv l ar)
  = fun maybe_fail input startPosition ->
    let h0 = HST.get () in
    let endPosition = v maybe_fail input startPosition in
    let res = set_error_code maybe_fail endPosition startPosition c in
    let h1 = HST.get () in
    assert (h1 `extends` h0);
    res

noextract inline_for_extraction
let validate_ite #nz (#k:parser_kind nz) (#a:Type) (#b:Type)
                 #inv1 #l1 #ar1 #inv2 #l2 #ar2
                 (e:bool)
                 (p1:squash e -> parser k a) (v1:(squash e -> validate_with_action_t (p1()) inv1 l1 ar1))
                 (p2:squash (not e) -> parser k b) (v2:(squash (not e) -> validate_with_action_t (p2()) inv2 l2 ar2))
  : Tot (validate_with_action_t (parse_ite e p1 p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false)
  = fun maybe_fail input startPosition ->
      if e then validate_drop (v1 ()) maybe_fail input startPosition else validate_drop (v2 ()) maybe_fail input startPosition

unfold
let validate_list_inv
  (#k: LPL.parser_kind)
  (#t: Type)
  (p: LPL.parser k t)
  (inv: slice_inv)
  (l: loc)
  (g0 g1: Ghost.erased HS.mem)
  (maybe_fail: pointer U64.t)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos0: U32.t)
  (bpos: pointer U32.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let h0 = Ghost.reveal g0 in
  let h1 = Ghost.reveal g1 in
  let pos1 = Seq.index (as_seq h bpos) 0 in
  let err = B.get h maybe_fail 0 in
  inv (LPL.slice_of sl).LPL.base h0 /\
  h `extends` h0 /\
  loc_not_unused_in h0 `loc_includes` l /\
  l `loc_disjoint` LPL.loc_input_buffer sl /\
  l `loc_disjoint` loc_buffer bpos /\
  l `loc_disjoint` loc_buffer maybe_fail /\
  address_liveness_insensitive_locs `loc_includes` l /\
  B.loc_buffer bpos `B.loc_disjoint` LPL.loc_input_buffer sl /\
  B.loc_buffer bpos `B.loc_disjoint` B.loc_buffer maybe_fail /\
  LPL.loc_input_buffer sl `B.loc_disjoint` B.loc_buffer maybe_fail /\
  k.LPL.parser_kind_subkind == Some LPL.ParserStrong /\
  k.LPL.parser_kind_low > 0 /\
  U32.v pos0 <= U32.v (LPL.slice_of sl).LPL.len /\
  LPL.live_input_buffer h0 sl /\
  live h1 bpos /\
  live h1 maybe_fail /\
  modifies loc_none h0 h1 /\ (
  if
    LPL.is_error err
  then
    stop == true
  else
    U32.v pos0 <= U32.v pos1 /\
    U32.v pos1 <= U32.v (LPL.slice_of sl).LPL.len /\
    R.readable h (LPL.perm_of sl) (pos1) (LPL.slice_length sl) /\
    (LPL.valid_exact (LPLL.parse_list p) h0 (LPL.slice_of sl) pos0 (LPL.slice_of sl).LPL.len <==>
     LPL.valid_exact (LPLL.parse_list p) h0 (LPL.slice_of sl) (pos1) (LPL.slice_of sl).LPL.len) /\
    (stop == true ==> U32.v pos1 == U32.v (LPL.slice_of sl).LPL.len)
  ) /\
  modifies (l `loc_union` B.loc_buffer maybe_fail `loc_union` loc_buffer bpos `loc_union` R.loc_perm_from_to (LPL.perm_of sl) pos0 (if LPL.is_error err then LPL.slice_length sl else pos1)) h1 h

#push-options "--z3rlimit 128"

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
  (maybe_fail: pointer U64.t)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos0: U32.t)
  (bpos: pointer U32.t)
: HST.Stack bool
  (requires (fun h -> validate_list_inv p inv l g0 g1 maybe_fail sl (pos0) bpos h false))
  (ensures (fun h res h' ->
    validate_list_inv p inv l g0 g1 maybe_fail sl (pos0) bpos h false /\
    validate_list_inv p inv l g0 g1 maybe_fail sl (pos0) bpos h' res
  ))
= let h = HST.get () in
  let elementStartPosition = index bpos 0ul in
  assert (U32.v elementStartPosition <= U32.v (LPL.slice_of sl).LPL.len);
  if elementStartPosition = (LPL.slice_length sl)
  then true
  else begin
    Classical.move_requires (LPLL.valid_exact_list_cons p (Ghost.reveal g0) (LPL.slice_of sl) (elementStartPosition)) (LPL.slice_of sl).LPL.len;
    Classical.move_requires (LPLL.valid_exact_list_cons_recip p (Ghost.reveal g0) (LPL.slice_of sl) (elementStartPosition)) (LPL.slice_of sl).LPL.len;
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in (Ghost.reveal g0) h1;
    let elementEndPosition = v maybe_fail sl elementStartPosition in
    upd bpos 0ul elementEndPosition;
    let err = B.index maybe_fail 0ul in
    (if LPL.is_success err then R.readable_split h1 (LPL.perm_of sl) (elementStartPosition) (elementEndPosition) (LPL.slice_length sl));
    LPL.is_error err
  end

#pop-options

#push-options "--z3rlimit 64"
inline_for_extraction
noextract
let validate_list'
  (n:U32.t)
  (#k:parser_kind true)
  #t
  (#p:parser k t)
  #inv #l #ar
  (v: validate_with_action_t p inv l ar)
  (maybe_fail: pointer U64.t)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v pos <= U32.v (LPL.slice_of sl).LPL.len /\
    inv (LPL.slice_of sl).LPL.base h /\
    loc_not_unused_in h `loc_includes` l /\
    l `loc_disjoint` LPL.loc_input_buffer sl /\
    address_liveness_insensitive_locs `loc_includes` l /\
    l `loc_disjoint` B.loc_buffer maybe_fail /\
    B.loc_buffer maybe_fail `loc_disjoint` LPL.loc_input_buffer sl /\
    B.live h maybe_fail /\
    R.readable h (LPL.perm_of sl) (pos) (LPL.slice_of sl).LPL.len /\
    LPL.live_slice h (LPL.slice_of sl)
  ))
  (ensures (fun h res h' ->
    let err = B.get h' maybe_fail 0 in
    inv (LPL.slice_of sl).LPL.base h' /\
    (LPL.is_success err ==> (LPL.valid_exact (LPLL.parse_list p) h (LPL.slice_of sl) (pos) (LPL.slice_of sl).LPL.len /\ U32.v res == U32.v (LPL.slice_of sl).LPL.len)) /\
    modifies (l `B.loc_union` B.loc_buffer maybe_fail `B.loc_union` R.loc_perm_from_to (LPL.perm_of sl) (pos) (if LPL.is_success err then res else LPL.slice_length sl)) h h'
  ))
= if LPL.is_error (B.index maybe_fail 0ul)
  then pos
  else begin
    let h0 = HST.get () in
    let g0 = Ghost.hide h0 in
    HST.push_frame ();
    let h02 = HST.get () in
    fresh_frame_modifies h0 h02;
    let currentPosition = alloca pos 1ul in
    let h1 = HST.get () in
    let g1 = Ghost.hide h1 in
    C.Loops.do_while (validate_list_inv p inv l g0 g1 maybe_fail sl (pos) currentPosition) (fun _ -> validate_list_body n v g0 g1 maybe_fail sl pos currentPosition);
    LPLL.valid_exact_list_nil p h0 (LPL.slice_of sl) (LPL.slice_of sl).LPL.len;
    let finalPosition = index currentPosition 0ul in
    HST.pop_frame ();
    let h' = HST.get () in
    assert (h' `extends` h0);
    finalPosition
  end
#pop-options

#push-options "--z3rlimit 32"
#restart-solver
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
= fun maybe_fail input pos ->
  let h = HST.get () in
  LPL.valid_facts (parse_nlist n p) h (LPL.slice_of input) (pos);
  LPLF.parse_fldata_consumes_all_correct (LPLL.parse_list p) (U32.v n) (LPL.bytes_of_slice_from h (LPL.slice_of input) (pos));
  if ((LPL.slice_length input) `U32.sub` pos) `U32.lt` n
  then begin
    B.upd maybe_fail 0ul LPL.validator_error_not_enough_data;
    let h' = HST.get () in
    assert (h' `extends` h);
    with_drop_if true inv input (pos) (fun _ -> LPL.slice_length input) pos
  end else begin
    let listInput = LPL.truncate_input_buffer input (pos `U32.add` n) in
    LPL.valid_exact_equiv (LPLL.parse_list p) h (LPL.slice_of listInput) (pos) (pos `U32.add` n);
    R.readable_split h (LPL.perm_of input) (pos) (LPL.slice_length listInput) (LPL.slice_length input);
    let res = validate_list' n v maybe_fail listInput pos in
    let is_success = LPL.is_success (B.index maybe_fail 0ul) in
    with_drop_if true inv input (pos) (fun x -> if is_success then x else LPL.slice_length input) (res)
  end
#pop-options

[@unifier_hint_injective]
inline_for_extraction
noextract
let validator_no_read #nz (#k: parser_kind nz) (#t: Type) (p: parser k t) : Tot Type =
  (maybe_fail: B.pointer U64.t) ->
  (len: U32.t) ->
  (sl: Ghost.erased (input_buffer_t len)) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    LPL.live_input_buffer h sl /\
    U32.v pos <= U32.v len /\
    B.live h maybe_fail /\
    B.loc_buffer maybe_fail `B.loc_disjoint` LPL.loc_input_buffer sl
  ))
  (ensures (fun h res h' ->
    B.modifies (B.loc_buffer maybe_fail) h h' /\
    (LPL.is_success (B.get h' maybe_fail 0) ==> LPL.valid_pos p h (LPL.slice_of sl) (pos) (res)
  )))

inline_for_extraction
noextract
let validate_total_constant_size_no_read
  #nz
  (#k: parser_kind nz)
  (#t: Type)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    let open LP in
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  })
: Tot (validator_no_read p)
= fun maybe_fail len input pos ->
  let h = HST.get () in
  [@inline_let] let _ = LPL.valid_total_constant_size h p (U32.v sz) (LPL.slice_of input) (pos) in
  if U32.lt (len `U32.sub` pos) sz
  then begin
    B.upd maybe_fail 0ul LPL.validator_error_not_enough_data;
    pos
  end else
    (pos `U32.add` sz)

inline_for_extraction noextract
let validate_nlist_total_constant_size_mod_ok (n:U32.t) (#k:parser_kind true) (#t: Type) (p:parser k t)
  : Pure (validator_no_read (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296 /\
    U32.v n % k.LP.parser_kind_low == 0
  ))
  (ensures (fun _ -> True))
= 
      (fun maybe_fail len sl pos ->
         let h = FStar.HyperStack.ST.get () in
         [@inline_let]
         let _ =
           parse_nlist_total_fixed_size_kind_correct n p;
           LPL.valid_facts (parse_nlist n p) h (LPL.slice_of sl) (pos);
           LPL.valid_facts (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) h (LPL.slice_of sl) (pos)
         in
         validate_total_constant_size_no_read #false (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) (n) () maybe_fail len sl pos
      )

inline_for_extraction noextract
let validate_nlist_constant_size_mod_ko (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Pure (validator_no_read (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.LP.parser_kind_low <> 0
  ))
  (ensures (fun _ -> True))
= 
  (fun maybe_fail len sl pos ->
     let h = FStar.HyperStack.ST.get () in
     [@inline_let]
     let _ =
       LPL.valid_facts (parse_nlist n p) h (LPL.slice_of sl) (pos)
     in
     [@inline_let]
     let f () : Lemma
       (requires (LPL.valid (parse_nlist n p) h (LPL.slice_of sl) (pos)))
       (ensures False)
     = let sq = LPL.bytes_of_slice_from h (LPL.slice_of sl) (pos) in
       let sq' = Ghost.hide (Seq.slice sq 0 (U32.v n)) in
       LowParse.Spec.List.list_length_constant_size_parser_correct p sq' ;
       let Some (l, _) = LP.parse (parse_nlist n p) sq in
       assert (U32.v n == FStar.List.Tot.length l `Prims.op_Multiply` k.LP.parser_kind_low) ;
       FStar.Math.Lemmas.cancel_mul_mod (FStar.List.Tot.length l) k.LP.parser_kind_low ;
       assert (U32.v n % k.LP.parser_kind_low == 0)
     in
     [@inline_let]
     let _ = Classical.move_requires f () in
     B.upd maybe_fail 0ul validator_error_list_size_not_multiple;
     pos
  )

inline_for_extraction noextract
let validate_nlist_total_constant_size' (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Pure (validator_no_read (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296
  ))
  (ensures (fun _ -> True))
= fun maybe_fail len sl pos ->
  if n `U32.rem` U32.uint_to_t k.LP.parser_kind_low = 0ul
  then validate_nlist_total_constant_size_mod_ok n p maybe_fail len sl pos
  else validate_nlist_constant_size_mod_ko n p maybe_fail len sl pos

inline_for_extraction noextract
let validate_nlist_total_constant_size (n_is_const: bool) (n:U32.t) (#k:parser_kind true) (#t: Type) (p:parser k t)
: Pure (validator_no_read (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind = Some ParserStrong /\
    k.parser_kind_high = Some k.parser_kind_low /\
    k.parser_kind_metadata = Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296
  ))
  (ensures (fun _ -> True))
=
  if
    if k.LP.parser_kind_low = 1
    then true
    else if n_is_const
    then U32.v n % k.LP.parser_kind_low = 0
    else false
  then
    validate_nlist_total_constant_size_mod_ok n p
  else if
    if n_is_const
    then U32.v n % k.LP.parser_kind_low <> 0
    else false
  then
    validate_nlist_constant_size_mod_ko n p
  else
    validate_nlist_total_constant_size' n p

noextract
inline_for_extraction
let validate_nlist_constant_size_without_actions
  (n_is_const: bool)
  (n:U32.t)
  (#k:parser_kind true)
  #t (#p:parser k t) #inv #l #ar
  (v: validate_with_action_t p inv l ar)
: Tot (validate_with_action_t (parse_nlist n p) inv l false)
= 
  if
    let open LP in
    k.parser_kind_subkind = Some ParserStrong &&
    k.parser_kind_high = Some k.parser_kind_low &&
    k.parser_kind_metadata = Some ParserKindMetadataTotal &&
    k.parser_kind_low < 4294967296
  then
    (fun maybe_fail #len input startPosition ->
      let h = HST.get () in
      assert (forall h' . {:pattern (B.modifies B.loc_none h h')} (B.modifies B.loc_none h h' /\ inv (LPL.slice_of input).LPL.base h) ==> h' `extends` h);
      assert (forall h' . {:pattern (B.modifies B.loc_none h h')} (B.modifies B.loc_none h h' /\ inv (LPL.slice_of input).LPL.base h) ==> inv (LPL.slice_of input).LPL.base h');
      let res = validate_nlist_total_constant_size n_is_const n p maybe_fail (LPL.slice_length input) input startPosition in
      let is_success = LPL.is_success (B.index maybe_fail 0ul) in
      let h' = HST.get () in
      assert (h' `extends` h);
      with_drop_if true inv input (startPosition) (fun y -> if is_success then y else LPL.slice_length input) (res)
    )
  else
    validate_nlist n v

#push-options "--z3rlimit 32"

noextract inline_for_extraction
let validate_t_at_most' (n:U32.t) (#k:parser_kind true) (#t:_) (#p:parser k t)
                       (#inv:_) (#l:_) (#ar:_) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t (parse_t_at_most n p) inv l ar)
  = fun maybe_fail input startPosition ->
    let h = HST.get () in
    let _ =
      LPL.valid_weaken kind_t_at_most (LowParse.Spec.FLData.parse_fldata (LPC.nondep_then p LowParse.Spec.Bytes.parse_all_bytes) (U32.v n)) h (LPL.slice_of input) (startPosition);
      LPL.valid_facts (LowParse.Spec.FLData.parse_fldata (LPC.nondep_then p LowParse.Spec.Bytes.parse_all_bytes) (U32.v n)) h (LPL.slice_of input) (startPosition)
    in
    if ((LPL.slice_length input) `U32.sub` startPosition) `U32.lt` n
    then begin
      B.upd maybe_fail 0ul LPL.validator_error_not_enough_data;
      let h' = HST.get () in
      assert (h' `extends` h);
      with_drop_if (not ar) inv input (startPosition) (fun _ -> LPL.slice_length input) startPosition
    end else
      [@inline_let] let input' = LPL.truncate_input_buffer input (startPosition `U32.add` n) in
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (startPosition) (LPL.slice_length input') (LPL.slice_length input) in
      [@inline_let] let _ =
        LPL.valid_facts (LPC.nondep_then p LowParse.Spec.Bytes.parse_all_bytes) h (LPL.slice_of input') (startPosition);
        LPLC.valid_nondep_then h p LowParse.Spec.Bytes.parse_all_bytes (LPL.slice_of input') (startPosition)
      in
      // FIXME: I'd need a name here
      let positionAfterContents = v maybe_fail input' startPosition in
      let h1 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h1 in
      if LPL.is_error (B.index maybe_fail 0ul)
      then with_drop_if (not ar) inv input (startPosition) (fun _ -> LPL.slice_length input) positionAfterContents
      else
        [@inline_let] let _ =
          LPL.valid_facts LowParse.Spec.Bytes.parse_all_bytes h (LPL.slice_of input') (positionAfterContents)
        in
        with_drop_if (not ar) inv input (startPosition) (fun _ -> startPosition `U32.add` n) (startPosition `U32.add` n)

let validate_t_at_most
  n
  #k #t #p #inv #l #ar v
= validate_drop (validate_t_at_most' n v)

noextract inline_for_extraction
let validate_t_exact' (n:U32.t) (#nz:bool) (#k:parser_kind nz) (#t:_) (#p:parser k t)
                       (#inv:_) (#l:_) (#ar:_) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t (parse_t_exact n p) inv l ar)
  = fun maybe_fail input startPosition ->
    let h = HST.get () in
    let _ =
      LPL.valid_weaken kind_t_at_most (LowParse.Spec.FLData.parse_fldata p (U32.v n)) h (LPL.slice_of input) (startPosition);
      LPL.valid_facts (LowParse.Spec.FLData.parse_fldata p (U32.v n)) h (LPL.slice_of input) (startPosition)
    in
    if ((LPL.slice_length input) `U32.sub` startPosition) `U32.lt` n
    then begin
      B.upd maybe_fail 0ul LPL.validator_error_not_enough_data;
      let h1 = HST.get () in
      assert (h1 `extends` h);
      with_drop_if (not ar) inv input (startPosition) (fun _ -> LPL.slice_length input) startPosition
    end else
      [@inline_let] let input' = LPL.truncate_input_buffer input (startPosition `U32.add` n) in
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (startPosition) (LPL.slice_length input') (LPL.slice_length input) in
      [@inline_let] let _ =
        LPL.valid_facts p h (LPL.slice_of input') (startPosition)
      in
      // FIXME: I'd need a name here
      let positionAfterContents = v maybe_fail input' startPosition in
      let h1 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h1 in
      if LPL.is_error (B.index maybe_fail 0ul)
      then with_drop_if (not ar) inv input (startPosition) (fun _ -> LPL.slice_length input) positionAfterContents
      else if (positionAfterContents) <> LPL.slice_length input'
      then begin
        B.upd maybe_fail 0ul validator_error_unexpected_padding;
        let h2 = HST.get () in
        assert (h2 `extends` h);
        with_drop_if (not ar) inv input (startPosition) (fun _ -> LPL.slice_length input) startPosition
      end
      else with_drop_if (not ar) inv input (startPosition) (fun _ -> startPosition `U32.add` n) (startPosition `U32.add` n)

#pop-options

let validate_t_exact
  n
  #nz #k #t #p #inv #l #ar v
= validate_drop (validate_t_exact' n v)

inline_for_extraction noextract
let validate_with_comment (c:string)
                          #nz (#k:parser_kind nz) #t (#p:parser k t)
                          #inv #l #ar (v:validate_with_action_t p inv l ar)
  : validate_with_action_t p inv l ar
  = fun maybe_fail input startPosition ->
    LowParse.Low.Base.comment c;
    v maybe_fail input startPosition

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
                (#t: Type)
                (#p: parser k t)
                (p32: leaf_reader p)
                (f: (t -> bool))
    : leaf_reader (parse_filter p f)
    = fun input startPosition ->
        let h = HST.get () in
        assert (LPL.valid #triv #triv #(filter_kind k) #(Prelude.refine t f) (parse_filter p f) h (LPL.slice_of input) startPosition);
        assert (parse_filter p f == LPC.parse_filter #k #t p f);
        assert (LPL.valid #triv #triv #(filter_kind k) #(Prelude.refine t f) (LPC.parse_filter #k #t p f) h (LPL.slice_of input) startPosition);
        assert (LPL.valid #triv #triv #(filter_kind k) #(x:t{f x}) (LPC.parse_filter #k #t p f) h (LPL.slice_of input) startPosition);
        assert (LPL.valid #triv #triv #(LPC.parse_filter_kind k) #(x:t{f x}) (LPC.parse_filter #k #t p f) h (LPL.slice_of input) startPosition);
        assert_norm (Prelude.refine t f == LPC.parse_filter_refine f);
        [@inline_let] let _ = LPLC.valid_filter h p f (LPL.slice_of input) startPosition in
        assert (LPL.valid p h (LPL.slice_of input) startPosition);
        p32 input startPosition

inline_for_extraction noextract
let validate____UINT8
  : validator parse____UINT8
  = fun maybe_fail input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a UINT8, i.e., 1 byte";
    validate_total_constant_size_no_read parse____UINT8 1ul () maybe_fail (LPL.slice_length input) (Ghost.hide input) startPosition

inline_for_extraction noextract
let read____UINT8
  : leaf_reader parse____UINT8
  = lift_constant_size_leaf_reader LowParse.Low.Int.read_u8 1ul

inline_for_extraction noextract
let validate____UINT16
  : validator parse____UINT16
  = fun maybe_fail input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a UINT16, i.e., 2 bytes";
    validate_total_constant_size_no_read parse____UINT16 2ul () maybe_fail (LPL.slice_length input) (Ghost.hide input) startPosition

inline_for_extraction noextract
let read____UINT16
  : leaf_reader parse____UINT16
  = lift_constant_size_leaf_reader LowParse.Low.BoundedInt.read_u16_le 2ul


inline_for_extraction noextract
let validate____UINT32
  : validator parse____UINT32
  = fun maybe_fail input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a ULONG, i.e., 4 bytes";
    validate_total_constant_size_no_read parse____UINT32 4ul () maybe_fail (LPL.slice_length input) (Ghost.hide input) startPosition

inline_for_extraction noextract
let read____UINT32
  : leaf_reader parse____UINT32
  = lift_constant_size_leaf_reader LowParse.Low.BoundedInt.read_u32_le 4ul

inline_for_extraction noextract
let validate____UINT64
  : validator parse____UINT64
  = fun maybe_fail input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a ULONG64, i.e., 8 bytes";
    validate_total_constant_size_no_read parse____UINT64 8ul () maybe_fail (LPL.slice_length input) (Ghost.hide input) startPosition

inline_for_extraction noextract
let read____UINT64
  : leaf_reader parse____UINT64
  = lift_constant_size_leaf_reader LowParse.Low.Int.read_u64_le 8ul

inline_for_extraction noextract
let validate_unit
  : validator parse_unit
  = validate_ret

inline_for_extraction noextract
let read_unit
  : leaf_reader (parse_ret ())
  = lift_constant_size_leaf_reader (LPLC.read_ret ()) 0ul

inline_for_extraction noextract
let validate_unit_refinement' (f:unit -> bool) (cf:string)
  : Tot (validate_with_action_t #false (parse_unit `LPC.parse_filter` f) true_inv eloc_none true)
  = fun maybe_fail input startPosition ->
      let h = HST.get () in
      [@inline_let] let _ = LPLC.valid_facts (parse_unit) h (LPL.slice_of input) (startPosition) in
      [@inline_let] let _ = LPLC.valid_filter h parse_unit f (LPL.slice_of input) (startPosition) in
      LowStar.Comment.comment cf;
      if f ()
      then
        startPosition
      else begin
        B.upd maybe_fail 0ul validator_error_constraint_failed;
        startPosition
      end

inline_for_extraction noextract
let validate_unit_refinement (f:unit -> bool) (cf:string)
  : Tot (validator (parse_unit `parse_filter` f))
  = validate_unit_refinement' f cf


(* Reimplement validate_list_up_to with readability (but no actions) *)

module LUT = LowParse.Low.ListUpTo

unfold
let validate_list_up_to_inv
  (#k: parser_kind true)
  (#t: eqtype)
  (p: parser k t)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
  (maybe_fail: B.pointer U64.t)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos0: U32.t)
  (h0: HS.mem)
  (bpos: B.pointer U32.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let open LPL in
  let pos = B.deref h bpos in
  let q = LUT.parse_list_up_to (cond_string_up_to terminator) p prf in
  B.live h0 bpos /\
  live_input_buffer h0 sl /\
  live_input_buffer h sl /\
  B.loc_disjoint (LPL.loc_input_buffer sl) (B.loc_buffer bpos) /\
  B.live h0 maybe_fail /\
  B.loc_disjoint (LPL.loc_input_buffer sl `B.loc_union` B.loc_buffer bpos) (B.loc_buffer maybe_fail) /\
  begin if is_success (B.get h maybe_fail 0)
  then
    U32.v pos0 <= U32.v pos /\
    U32.v pos <= U32.v (slice_of sl).len /\
    B.modifies (B.loc_buffer maybe_fail `B.loc_union` B.loc_buffer bpos `B.loc_union` R.loc_perm_from_to (perm_of sl) pos0 pos) h0 h /\
    R.unreadable h (perm_of sl) pos0 pos /\
    R.readable h (perm_of sl) pos (slice_of sl).len /\
    begin if stop
    then
      valid_pos q h0 (slice_of sl) pos0 pos
    else
      (valid q h0 (slice_of sl) pos0 <==> valid q h0 (slice_of sl) pos) /\
      ((valid q h0 (slice_of sl) pos0 /\ valid q h0 (slice_of sl) pos) ==>
        get_valid_pos q h0 (slice_of sl) pos0 == get_valid_pos q h0 (slice_of sl) pos
      )
    end
  else
    U32.v pos0 <= U32.v (slice_of sl).len /\
    B.modifies (B.loc_buffer maybe_fail `B.loc_union` B.loc_buffer bpos `B.loc_union` R.loc_perm_from_to (perm_of sl) pos0 (slice_of sl).len) h0 h /\
    R.unreadable h (perm_of sl) pos0 (slice_of sl).len /\
    stop == true /\
    True // (~ (valid q h0 (slice_of sl) pos0)) // we lost completeness because of actions
  end

#push-options "--z3rlimit 32"

inline_for_extraction
let validate_list_up_to_body
  (#k: parser_kind true)
  (#t: eqtype)
  (#p: parser k t)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
  (v: validator p)
  (r: leaf_reader p)
  (maybe_fail: B.pointer U64.t)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos0: U32.t)
  (h0: HS.mem)
  (bpos: B.pointer U32.t)
: HST.Stack bool
  (requires (fun h ->
    validate_list_up_to_inv p terminator prf maybe_fail sl pos0 h0 bpos h false
  ))
  (ensures (fun h stop h' ->
    validate_list_up_to_inv p terminator prf maybe_fail sl pos0 h0 bpos h false /\
    validate_list_up_to_inv p terminator prf maybe_fail sl pos0 h0 bpos h' stop
  ))
=
  let open LPL in
  let open LUT in
  let h = HST.get () in
  let pos = B.index bpos 0ul in
  valid_facts (parse_list_up_to (cond_string_up_to terminator) p prf) h0 (slice_of sl) (pos);
  parse_list_up_to_eq (cond_string_up_to terminator) p prf (bytes_of_slice_from h0 (slice_of sl) (pos));
  valid_facts p h0 (slice_of sl) (pos);
  let pos1 = v maybe_fail sl pos in
  B.upd bpos 0ul pos1;
  if is_error (B.index maybe_fail 0ul)
  then begin
    drop sl (pos) (slice_length sl);
    let h = HST.get () in
    R.unreadable_split h (perm_of sl) pos0 (pos) (slice_length sl);
    true
  end else begin
    valid_facts (parse_list_up_to (cond_string_up_to terminator) p prf) h0 (slice_of sl) (pos1);
    let h = HST.get () in
    R.readable_split h (perm_of sl) (pos) (pos1) (slice_length sl);
    let x = r sl (pos) in
    let h = HST.get () in
    R.unreadable_split h (perm_of sl) pos0 (pos) (pos1);
    cond_string_up_to terminator x
  end

inline_for_extraction
noextract
let validate_list_up_to
  (#k: parser_kind true)
  (#t: eqtype)
  (#p: parser k t)
  (v: validator p)
  (r: leaf_reader p)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
: Tot (validate_with_action_t #true (LUT.parse_list_up_to (cond_string_up_to terminator) p prf) true_inv eloc_none false)
=
  fun maybe_fail sl pos ->
  if LPL.is_error (B.index maybe_fail 0ul)
  then begin
    LPL.drop sl (pos) (LPL.slice_length sl);
    pos
  end else begin
    HST.push_frame ();
    let bpos = B.alloca pos 1ul in
    let h2 = HST.get () in
    R.unreadable_empty h2 (LPL.perm_of sl) (pos);
    C.Loops.do_while
      (validate_list_up_to_inv p terminator prf maybe_fail sl (pos) h2 bpos)
      (fun _ -> validate_list_up_to_body terminator prf v r maybe_fail sl (pos) h2 bpos)
      ;
    let res = B.index bpos 0ul in
    HST.pop_frame ();
    res
  end

#pop-options

let validate_string
  #k #t #p v r terminator
=
  LP.parser_kind_prop_equiv k p;
  validate_weaken (validate_list_up_to v r terminator (fun _ _ _ -> ())) _

////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
let action_return
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#a:Type) (x:a)
  : action p true_inv eloc_none false a
  = fun _ input startPosition endPosition -> x

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
  = fun maybe_fail input startPosition endPosition ->
    let h0 = HST.get () in
    [@(rename_let ("" ^ name))]
    let x = f maybe_fail input startPosition endPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g x maybe_fail input startPosition endPosition

noextract
inline_for_extraction
let action_seq
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      #bf (#a:Type) (f: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (#b:Type) (g: action p invg lg bg b)
  : Tot (action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) b)
  = fun maybe_fail input startPosition endPosition ->
    let h0 = HST.get () in
    let _ = f maybe_fail input startPosition endPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g maybe_fail input startPosition endPosition

noextract
inline_for_extraction
let action_ite
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      (guard:bool)
      #bf (#a:Type) (then_: squash guard -> action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (else_: squash (not guard) -> action p invg lg bg a)
  : action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) a
  = fun maybe_fail input startPosition endPosition ->
      if guard 
      then then_ () maybe_fail input startPosition endPosition 
      else else_ () maybe_fail input startPosition endPosition

noextract
inline_for_extraction
let action_abort
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
  : action p true_inv eloc_none false bool
  = fun _ input startPosition endPosition -> false

noextract
inline_for_extraction
let action_field_pos
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none false U32.t
   = fun _ _ startPosition _ -> startPosition


noextract
inline_for_extraction
let action_field_ptr
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none true LPL.puint8
   = fun _ input startPosition _ ->
       let open LowParse.Slice in
       LPL.offset input (startPosition)

noextract
inline_for_extraction
let action_deref
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a)
   : action p (ptr_inv x) loc_none false a
   = fun _ _ _ _ -> !*x

noextract
inline_for_extraction
let action_assignment
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a) (v:a)
   : action p (ptr_inv x) (ptr_loc x) false unit
   = fun _ _ _ _ -> x *= v

(* FIXME: This is now unsound.
noextract
inline_for_extraction
let action_read_value
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (r:leaf_reader p)
   : action p true_inv eloc_none true t
   = fun input startPosition endPosition ->
     r input (LPL.uint64_to_uint32 startPosition)
*)

noextract
inline_for_extraction
let action_weaken
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (#inv:slice_inv) (#l:eloc) (#b:_) (#a:_) (act:action p inv l b a)
      (#inv':slice_inv{inv' `inv_implies` inv}) (#l':eloc{l' `eloc_includes` l})
   : action p inv' l' b a
   = act

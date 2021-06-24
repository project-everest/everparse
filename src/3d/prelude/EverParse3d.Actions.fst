module EverParse3d.Actions
friend Prelude

module LPE = LowParse.Low.ErrorCode
open FStar.Tactics.Typeclasses

let action
  p inv l on_success a
=
    (#input_buffer_t: Type0) ->
    (#[tcresolve ()]_: I.input_stream_inst input_buffer_t) ->
    sl: Ghost.erased input_buffer_t ->
    Stack a
      (requires fun h ->
        I.live (Ghost.reveal sl) h /\
        inv (I.footprint (Ghost.reveal sl)) h /\
        loc_not_unused_in h `loc_includes` l /\
        address_liveness_insensitive_locs `loc_includes` l /\
        l `loc_disjoint` I.footprint (Ghost.reveal sl)
      )
      (ensures fun h0 _ h1 ->
        modifies l h0 h1 /\
        h1 `extends` h0 /\
        inv (I.footprint (Ghost.reveal sl)) h1)

module LP = LowParse.Spec.Base
module LPL = LowParse.Low.Base

unfold
let valid_len
  (#input_buffer_t: Type0)
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (sl: input_buffer_t)
  (len: nat)
: Tot prop
= I.live sl h /\
  begin
    let s = I.get_remaining sl h in
    begin match LP.parse p s with
    | None -> False
    | Some (_, len') -> len == len'
    end
  end

let valid
  (#input_buffer_t: Type0)
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (sl: input_buffer_t)
: Tot prop
= I.live sl h /\
  Some? (LP.parse p (I.get_remaining sl h))

let validate_with_action_t' (#k:LP.parser_kind) (#t:Type) (p:LP.parser k t) (inv:slice_inv) (l:eloc) (allow_reading:bool) =
  (#input_buffer_t: Type0) ->
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t) ->
  (sl: input_buffer_t) ->
  (startPosition: U64.t) ->
  Stack U64.t
  (requires fun h ->
    I.live sl h /\
    inv (I.footprint sl) h /\
    loc_not_unused_in h `loc_includes` l /\
    address_liveness_insensitive_locs `loc_includes` l /\
    l `loc_disjoint` I.footprint sl /\
    U64.v startPosition + Seq.length (I.get_remaining sl h) == I.length_all #_ #inst sl
  )
  (ensures fun h res h' ->
    I.live sl h' /\
    modifies (l `loc_union` I.footprint sl) h h' /\
    h' `extends` h /\
    inv (I.footprint sl) h' /\
    begin if LPE.is_success res
    then
      let s = I.get_remaining sl h in
      let len = U64.v res - U64.v startPosition in
      len >= 0 /\
      valid_len p h sl len /\
      I.get_remaining sl h' == (if allow_reading then s else Seq.slice s len (Seq.length s))
    else
      True
    end
    )

let validate_with_action_t p inv l allow_reading = validate_with_action_t' p inv l allow_reading

let validate_eta v =
  fun sl -> v sl

let act_with_comment
  s res a
=
  fun sl ->
  LPL.comment s;
  a sl

let leaf_reader
  #nz
  #k
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (#input_buffer_t: Type) ->
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t) ->
  (sl: input_buffer_t) ->
  Stack t
  (requires (fun h ->
    valid p h sl
  ))
  (ensures (fun h res h' ->
    let s = I.get_remaining sl h in
    I.live sl h' /\
    modifies (I.footprint sl) h h' /\
    h' `extends` h /\
    begin match LP.parse p s with
    | None -> False
    | Some (y, len) ->
      res == y /\
      I.get_remaining sl h' == Seq.slice s len (Seq.length s)
    end
  ))

inline_for_extraction
noextract
let validate_with_success_action' (name: string) #nz #wk (#k1:parser_kind nz wk) #t1 (#p1:parser k1 t1) (#inv1:_) (#l1:eloc) (#ar:_)
                         (v1:validate_with_action_t p1 inv1 l1 ar)
                         (#inv2:_) (#l2:eloc) #b (a:action p1 inv2 l2 b bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun input startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then
         [@(rename_let ("action_success_" ^ name))]
         let b = a input in
         if not b
         then validator_error_action_failed
         else pos1
    else
         pos1

inline_for_extraction
noextract
let validate_drop_true
   (#k:LP.parser_kind) (#t:Type) (#p:LP.parser k t) (#inv:slice_inv) (#l:eloc) (v: validate_with_action_t' p inv l true)
: Tot (validate_with_action_t' p inv l false)
= fun input startPosition ->
  let res = v input startPosition in
  if LPE.is_success res
  then begin
    let h1 = HST.get () in
    I.skip input (LPE.uint64_to_uint32 (res `U64.sub` startPosition));
    let h2 = HST.get () in
    assert (h2 `extends` h1)
  end;
  res

inline_for_extraction
noextract
let validate_drop
   (#k:LP.parser_kind) (#t:Type) (#p:LP.parser k t) (#inv:slice_inv) (#l:eloc) #allow_reading (v: validate_with_action_t' p inv l allow_reading)
: Tot (validate_with_action_t' p inv l false)
= if allow_reading
  then validate_drop_true v
  else v

let validate_with_success_action
  name v1 a
= validate_drop (validate_with_success_action' name v1 a)

inline_for_extraction noextract
let validate_with_error_action' (name: string) #nz #wk (#k1:parser_kind nz wk) #t1 (#p1:parser k1 t1) (#inv1:_) (#l1:eloc) (#ar:_)
                         (v1:validate_with_action_t p1 inv1 l1 ar)
                         (#inv2:_) (#l2:eloc) (a:action p1 inv2 l2 false bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun input startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then pos1
    else
         [@(rename_let ("action_error_" ^ name))]
         let b = a input in
         if not b then validator_error_action_failed else pos1

let validate_with_error_action
  name v1 a
= validate_drop (validate_with_error_action' name v1 a)

inline_for_extraction noextract
let validate_ret
  : validate_with_action_t (parse_ret ()) true_inv eloc_none true
  = fun input startPosition ->
    startPosition

#push-options "--z3rlimit 16"

module LPC = LowParse.Spec.Combinators

inline_for_extraction noextract
let validate_pair
       (name1: string)
       #nz1 (#k1:parser_kind nz1 WeakKindStrongPrefix) #t1 (#p1:parser k1 t1)
       (#inv1:_) (#l1:eloc) (#ar1:_) (v1:validate_with_action_t p1 inv1 l1 ar1)
       #nz2 #wk2 (#k2:parser_kind nz2 wk2) #t2 (#p2:parser k2 t2)
       (#inv2:_) (#l2:eloc) (#ar2:_) (v2:validate_with_action_t p2 inv2 l2 ar2)
  : validate_with_action_t (p1 `parse_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false
  = fun input startPosition ->
    let h = HST.get () in
    LPC.nondep_then_eq p1 p2 (I.get_remaining input h);
    [@(rename_let ("positionAfter" ^ name1))]
    let pos1 = validate_drop v1 input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if LPL.is_error pos1
    then
      pos1
    else
      validate_drop v2 input pos1

inline_for_extraction noextract
let validate_dep_pair
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t (p1 `parse_dep_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false)
  = fun input startPosition ->
      let h = HST.get () in
      LPC.parse_dtuple2_eq p1 p2 (I.get_remaining input h);
      [@(rename_let ("positionAfter" ^ name1))]
      let pos1 = v1 input startPosition in
      let h1 = HST.get() in
      if LPL.is_error pos1
      then begin
        pos1
      end
      else
        [@(rename_let ("" ^ name1))]
        let x = r1 input in
        let h15 = HST.get () in
        let _ = modifies_address_liveness_insensitive_unused_in h h15 in
        validate_drop (v2 x) input pos1

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action'
      (name1: string)
      (id1: field_id)
      (#nz1: _) (#k1:parser_kind nz1 _) (#t1: _) (#p1:parser k1 t1)
      (#inv1: _) (#l1: _) (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      (#inv1': _) (#l1': _) (#b: _) (a:t1 -> action p1 inv1' l1' b bool)
      (#nz2: _) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f) -> parser k2 (t2 x))
      (#inv2: _) (#l2: _) (#ar2: _) (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
  =
  fun input startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        res
      end
      else begin
        assert (I.get_remaining input h1 == I.get_remaining input h0);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("pos_or_error_after_" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition res id1 in
        if LPL.is_error res1
        then
          res1
        else
             let h2 = HST.get() in
             modifies_address_liveness_insensitive_unused_in h1 h2;
             if not (a field_value input)
             then (LPL.set_validator_error_pos_and_code validator_error_action_failed startPosition id1) //action failed
             else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) input res1
             end
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action_total_zero_parser'
      (name1: string)
      (id1: field_id)
      (#nz1: _) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: _) (#p1:parser k1 t1) (r1: leaf_reader p1)
      (inv1: _) (l1: _)
      (f: t1 -> bool)
      (#inv1': _) (#l1': _) (#b: _) (a:t1 -> action p1 inv1' l1' b bool)
      (#nz2: _) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#inv2: _) (#l2: _) (#ar2: _) (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
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
  = fun input startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("pos_or_error_after_" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition startPosition id1 in
        if LPL.is_error res1
        then
             res1
        else let h2 = HST.get() in
             modifies_address_liveness_insensitive_unused_in h0 h2;
             if not (a field_value input)
             then (LPL.set_validator_error_pos_and_code validator_error_action_failed startPosition id1) //action failed
             else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) input res1
             end
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
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
      validate_dep_pair_with_refinement_and_action_total_zero_parser' name1 id1 r1 inv1 l1 f a v2
    else
      validate_dep_pair_with_refinement_and_action' name1 id1 v1 r1 f a v2


inline_for_extraction noextract
let validate_dep_pair_with_action
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             (p1 `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
  = fun input startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ p1 #_ #t2 p2 (I.get_remaining input h0);
      let res = v1 input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        res
      end
      else begin
        let field_value = r1 input in
        let h2 = HST.get() in
        modifies_address_liveness_insensitive_unused_in h1 h2;
        let action_result = a field_value input in
        if not action_result
        then validator_error_action_failed //action failed
        else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) input res
             end
      end

inline_for_extraction noextract
let validate_dep_pair_with_refinement'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (l1 `eloc_union` l2)
             false)
  = fun input startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
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
        let field_value = r1 input in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionOrErrorAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition res id1 in
        if LPL.is_error res1
        then
             res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             validate_drop (v2 field_value) input res1
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_total_zero_parser'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      (inv1: _) (l1: _) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
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
  = fun input startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input in
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
             validate_drop (v2 field_value) input res1
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
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
      validate_dep_pair_with_refinement_total_zero_parser' name1 id1 inv1 l1 r1 f v2
    else
      validate_dep_pair_with_refinement' name1 id1 v1 r1 f v2

inline_for_extraction noextract
let validate_filter (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : Tot (validate_with_action_t #nz #WeakKindStrongPrefix (p `LPC.parse_filter` f) inv l false)
  = fun input startPosition ->
    let h = HST.get () in
    LPC.parse_filter_eq p f (I.get_remaining input h);
    [@(rename_let ("positionAfter" ^ name))]
    let res = v input startPosition in
    let h1 = HST.get () in
    if LPL.is_error res
    then res
    else begin
      LowStar.Comment.comment cr;
      [@(rename_let ("" ^ name))]
      let field_value = r input in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      check_constraint_ok ok res
    end


inline_for_extraction noextract
let validate_filter_with_action
                    (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) #inva (#la:eloc) (a: t -> action #nz #WeakKindStrongPrefix #(filter_kind k) #_ (p `LPC.parse_filter` f) inva la b bool)
  : Tot (validate_with_action_t #nz #WeakKindStrongPrefix (p `LPC.parse_filter` f) (conj_inv inv inva) (eloc_union l la) false)
  = fun input startPosition ->
    let h = HST.get () in
    LPC.parse_filter_eq p f (I.get_remaining input h);
    [@(rename_let ("positionAfter" ^ name))]
    let res = v input startPosition in
    let h1 = HST.get () in
    if LPL.is_error res
    then res
    else begin
      LowStar.Comment.comment cr;
      [@(rename_let ("" ^ name))]
      let field_value = r input in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      if ok
        then let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h h15 in
             if a field_value input
             then res
             else validator_error_action_failed
      else validator_error_constraint_failed
    end

inline_for_extraction noextract
let validate_with_dep_action
                    (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
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
      let field_value = r input in
      let h15 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h15 in
      if a field_value input
      then res
      else validator_error_action_failed
    end

inline_for_extraction noextract
let validate_weaken #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
                    #inv #l #ar (v:validate_with_action_t p inv l ar)
                    #nz' #wk' (k':parser_kind nz' wk'{k' `is_weaker_than` k})
  : Tot (validate_with_action_t (parse_weaken p k') inv l ar)
  = fun input startPosition ->
    let h = HST.get () in
    v input startPosition


/// Parser: weakening kinds

inline_for_extraction noextract
let validate_weaken_left (#nz:_) #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                         (#inv:_) (#l:_) #ar (v:validate_with_action_t p inv l ar)
                         (#nz':_) #wk' (k':parser_kind nz' wk')
  : validate_with_action_t (parse_weaken_left p k') inv l ar
  = validate_weaken v (glb k' k)

/// Parser: weakening kinds

inline_for_extraction noextract
let validate_weaken_right (#nz:_) #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                         (#inv:_) (#l:_) #ar (v:validate_with_action_t p inv l ar)
                         (#nz':_) #wk' (k':parser_kind nz' wk')
  : validate_with_action_t (parse_weaken_right p k') inv l ar
  = validate_weaken v (glb k k')

inline_for_extraction noextract
let validate_impos ()
  : Tot (validate_with_action_t (parse_impos ()) true_inv eloc_none true)
  = fun _ _ -> validator_error_impossible

inline_for_extraction noextract
let validate_with_error
  c v
  = fun input startPosition ->
    let endPositionOrError = v input startPosition in
    LPL.maybe_set_error_code endPositionOrError startPosition c

noextract inline_for_extraction
let validate_ite
  e p1 v1 p2 v2
  = fun input startPosition ->
      if e then validate_drop (v1 ()) input startPosition else validate_drop (v2 ()) input startPosition

module LPLL = LowParse.Spec.List

unfold
let validate_list_inv
  (#input_buffer_t: Type)
  (#[tcresolve ()] inst: I.input_stream_inst input_buffer_t)
  (#k: LPL.parser_kind)
  (#t: Type)
  (p: LPL.parser k t)
  (inv: slice_inv)
  (l: loc)
  (g0 g1: Ghost.erased HS.mem)
  (sl: input_buffer_t)
  (pos0: U64.t)
  (bpos: pointer U64.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let h0 = Ghost.reveal g0 in
  let h1 = Ghost.reveal g1 in
  let pos1 = Seq.index (as_seq h bpos) 0 in
  inv (I.footprint sl) h0 /\
  h `extends` h0 /\
  loc_not_unused_in h0 `loc_includes` l /\
  l `loc_disjoint` I.footprint sl /\
  l `loc_disjoint` loc_buffer bpos /\
  address_liveness_insensitive_locs `loc_includes` l /\
  B.loc_buffer bpos `B.loc_disjoint` I.footprint sl /\
  I.live sl h0 /\
  I.live sl h /\
  U64.v pos0 + Seq.length (I.get_remaining sl h0) <= I.length_all #_ #inst sl /\
  live h1 bpos /\
  modifies loc_none h0 h1 /\ (
  if
    LPL.is_error pos1
  then
    stop == true
  else
    U64.v pos0 <= U64.v pos1 /\
    U64.v pos1 + Seq.length (I.get_remaining sl h) <= I.length_all #_ #inst sl /\
    (valid (LPLL.parse_list p) h0 sl <==>
     valid (LPLL.parse_list p) h sl) /\
    (stop == true ==> Seq.length (I.get_remaining sl h) == 0)
  ) /\
  modifies (l `loc_union` loc_buffer bpos `loc_union` I.footprint sl) h1 h

#pop-options

module EverParse3d.Actions
friend Prelude

module LPE = LowParse.Low.ErrorCode

let action
  p inv l on_success a
=
    sl: Ghost.erased input_buffer_t ->
    Stack a
      (requires fun h ->
        I.live sl h /\
        inv sl h /\
        loc_not_unused_in h `loc_includes` l /\
        address_liveness_insensitive_locs `loc_includes` l /\
        l `loc_disjoint` I.footprint sl
      )
      (ensures fun h0 _ h1 ->
        modifies l h0 h1 /\
        h1 `extends` h0 /\
        inv sl h1)

module LP = LowParse.Spec.Base
module LPL = LowParse.Low.Base

unfold
let valid_pos
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (sl: input_buffer_t)
  (pos: nat)
  (pos': nat)
: Tot prop
= I.live sl h /\
  begin
    let s = I.get_remaining sl h in
    pos <= Seq.length s /\
    begin match LP.parse p (Seq.slice s pos (Seq.length s)) with
    | None -> False
    | Some (_, len) -> pos' == pos + len
    end
  end

let valid
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (sl: input_buffer_t)
: Tot prop
= I.live sl h /\
  Some? (LP.parse p (I.get_remaining sl h))

let validate_with_action_t' (#k:LP.parser_kind) (#t:Type) (p:LP.parser k t) (inv:slice_inv) (l:eloc) (allow_reading:bool) =
  (sl: input_buffer_t) ->
  (startPosition: U64.t) ->
  Stack U64.t
  (requires fun h ->
    I.live sl h /\
    inv sl h /\
    loc_not_unused_in h `loc_includes` l /\
    address_liveness_insensitive_locs `loc_includes` l /\
    l `loc_disjoint` I.footprint sl /\
    (allow_reading ==> U64.v startPosition <= Seq.length (I.get_remaining sl h))
  )
  (ensures fun h res h' ->
    I.live sl h' /\
    modifies (l `loc_union` I.footprint sl) h h' /\
    h' `extends` h /\
    inv sl h' /\
    begin if LPE.is_success res
    then
      let pos = if allow_reading then U64.v startPosition else 0 in
      let s = I.get_remaining sl h in
      valid_pos p h sl (U64.v res) /\
      I.get_remaining sl h' == (if allow_reading then s else Seq.slice s (U64.v res) (Seq.length s))
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

inline_for_extraction
let leaf_reader
  #nz
  #k
  (#t: Type)
  (p: parser k t)
: Tot Type
= (sl: input_buffer_t) ->
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
   #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (#inv:slice_inv) (#l:eloc) (v: validate_with_action_t p inv l true)
: Tot (validate_with_action_t p inv l false)
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
   #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (#inv:slice_inv) (#l:eloc) #allow_reading (v: validate_with_action_t p inv l allow_reading)
: Tot (validate_with_action_t p inv l false)
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

inline_for_extraction noextract
let validate_pair'
       (name1: string)
       #nz1 (#k1:parser_kind nz1 WeakKindStrongPrefix) #t1 (#p1:parser k1 t1)
       (#inv1:_) (#l1:eloc) (#ar1:_) (v1:validate_with_action_t p1 inv1 l1 ar1)
       #nz2 #wk2 (#k2:parser_kind nz2 wk2) #t2 (#p2:parser k2 t2)
       (#inv2:_) (#l2:eloc) (#ar2:_) (v2:validate_with_action_t p2 inv2 l2 ar2)
  : validate_with_action_t (p1 `parse_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) (ar1 && ar2)
  = fun input startPosition ->
    let h = HST.get () in
    [@(rename_let ("positionAfter" ^ name1))]
    let pos1 = v1 input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if LPL.is_error pos1
    then
      pos1
    else
      v2 input pos1

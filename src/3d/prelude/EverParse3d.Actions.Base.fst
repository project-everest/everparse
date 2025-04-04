module EverParse3d.Actions.Base
friend EverParse3d.Kinds
friend EverParse3d.Prelude
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
module B = LowStar.Buffer
module I = EverParse3d.InputStream.Base
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module CP = EverParse3d.CopyBuffer
module PA = EverParse3d.ProbeActions
module AppCtxt = EverParse3d.AppCtxt
module LPE = EverParse3d.ErrorCode
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
module B = LowStar.Buffer
module U8 = FStar.UInt8
module P = EverParse3d.Prelude
module F = FStar.FunctionalExtensionality
let hinv = HS.mem ^-> prop
let liveness_inv = i:hinv {
  forall l h0 h1. {:pattern (i h1); (modifies l h0 h1)}  i h0 /\ modifies l h0 h1 /\ address_liveness_insensitive_locs `loc_includes` l ==> i h1
}
let mem_inv  = liveness_inv
let slice_inv = mem_inv
let inv_implies (inv0 inv1:slice_inv) =
  forall h.
    inv0 h ==> inv1 h
let true_inv : slice_inv = F.on HS.mem #prop (fun _ -> True)
let conj_inv (i0 i1:slice_inv) : slice_inv = F.on HS.mem #prop (fun h -> i0 h /\ i1 h)
let eloc = (l: FStar.Ghost.erased B.loc { B.address_liveness_insensitive_locs `B.loc_includes` l })
let eloc_union (l1 l2:eloc) : Tot eloc = B.loc_union l1 l2
let eloc_none : eloc = B.loc_none
let eloc_includes (l1 l2:eloc) = B.loc_includes l1 l2 /\ True
let eloc_disjoint (l1 l2:eloc) = B.loc_disjoint l1 l2 /\ True
let inv_implies_refl inv = ()
let inv_implies_true inv0 = ()
let inv_implies_conj inv0 inv1 inv2 h01 h02 = ()
let conj_inv_true_left_unit i =
  FStar.PredicateExtensionality.predicateExtensionality _ (conj_inv true_inv i) i
let conj_inv_true_right_unit i =
  FStar.PredicateExtensionality.predicateExtensionality _ (conj_inv i true_inv) i

let eloc_includes_none l = ()
let eloc_includes_union l0 l1 l2 h01 h02 = ()
let eloc_includes_refl l = ()
let eloc_union_none_left_unit l = ()
let eloc_union_none_right_unit l = ()

let disjointness_pre = prop
let disjointness_trivial = True
let disjoint l1 l2 = eloc_disjoint l1 l2
let conj_disjointness p1 p2 = p1 /\ p2
let imp_disjointness p1 p2 = p1 ==> p2
let disjoint_none_r l =
  FStar.PropositionalExtensionality.apply
      (disjoint l eloc_none)
      (disjointness_trivial)
let disjoint_none_l l =
  FStar.PropositionalExtensionality.apply
      (disjoint  eloc_none l)
      (disjointness_trivial)

let conj_disjointness_trivial_left_unit (d:disjointness_pre)
  = FStar.PropositionalExtensionality.apply (disjointness_trivial `conj_disjointness` d) d

let conj_disjointness_trivial_right_unit (d:disjointness_pre)
  = FStar.PropositionalExtensionality.apply (d `conj_disjointness` disjointness_trivial) d

let imp_disjointness_refl (d:disjointness_pre)
  = ()
  
let index_equations ()
  = introduce forall d. _
    with conj_inv_true_left_unit d;
    introduce forall d. _
    with conj_inv_true_right_unit d;
    introduce forall l. _
    with eloc_union_none_right_unit l;
    introduce forall l. _
    with eloc_union_none_left_unit l;
    introduce forall l. _
    with disjoint_none_r l;
    introduce forall l. _
    with disjoint_none_l l;
    introduce forall d. _
    with conj_disjointness_trivial_left_unit d;
    introduce forall d. _
    with conj_disjointness_trivial_right_unit d;
    introduce forall d. _
    with imp_disjointness_refl d;
    introduce forall i. _
    with inv_implies_refl i;
    introduce forall i. _
    with inv_implies_true i;
    introduce forall i0 i1 i2. 
        (i0 `inv_implies` i1 /\
         i0 `inv_implies` i2) ==>
        (i0 `inv_implies` (i1 `conj_inv` i2))
    with introduce _ ==> _
    with _ . inv_implies_conj i0 i1 i2 () ();
    introduce forall l. _
    with eloc_includes_none l;
    introduce forall l0 l1 l2. (l0 `eloc_includes` l1 /\
         l0 `eloc_includes` l2) ==>
        (l0 `eloc_includes` (l1 `eloc_union` l2))
    with introduce _ ==> _
    with _ . eloc_includes_union l0 l1 l2 () ();
    introduce forall l. _
    with eloc_includes_refl l

let bpointer a = B.pointer a
let ptr_loc #a (x:B.pointer a) : Tot eloc = B.loc_buffer x
let ptr_inv #a (x:B.pointer a) : slice_inv = F.on HS.mem #prop (fun h -> B.live h x /\ True)
let app_ctxt = AppCtxt.app_ctxt
let app_loc (x:AppCtxt.app_ctxt) (l:eloc) : eloc = 
  AppCtxt.properties x;
  AppCtxt.loc_of x `loc_union` l
let app_loc_fp (x:AppCtxt.app_ctxt) (has_action:bool) (l:eloc) : eloc = 
  if has_action then AppCtxt.ghost_loc_of x `loc_union` app_loc x l
  else app_loc x l

inline_for_extraction
noextract
let input_buffer_t = EverParse3d.InputStream.All.t

inline_for_extraction
let error_handler = 
    typename:string ->
    fieldname:string ->
    error_reason:string ->
    error_code:U64.t ->
    ctxt: app_ctxt ->
    sl: input_buffer_t ->
    pos: LPE.pos_t ->
    Stack unit
      (requires fun h ->
        I.live sl h /\
        true_inv h /\
        B.live h ctxt /\
        loc_not_unused_in h `loc_includes` app_loc_fp ctxt true eloc_none /\
        address_liveness_insensitive_locs `loc_includes` app_loc_fp ctxt true eloc_none /\
        app_loc_fp ctxt true eloc_none `loc_disjoint` I.footprint sl /\
        U64.v pos <= Seq.length (I.get_read sl h)
      )
      (ensures fun h0 _ h1 ->
        let sl = Ghost.reveal sl in
        modifies (app_loc ctxt eloc_none) h0 h1 /\
        B.live h1 ctxt /\
        true_inv h1)

let action
  inv disj l on_success returns_true a
=   (# [EverParse3d.Util.solve_from_ctx ()] I.extra_t #input_buffer_t) ->
    ctxt: app_ctxt ->
    error_handler_fn : error_handler ->
    sl: input_buffer_t ->
    len: I.tlen sl ->
    pos: LPE.pos_t ->
    posf: LPE.pos_t ->
    Stack a
      (requires fun h ->
        I.live sl h /\
        disj /\
        inv h /\
        B.live h ctxt /\
        B.live h (AppCtxt.action_ghost_ptr ctxt) /\
        loc_not_unused_in h `loc_includes` app_loc_fp ctxt true l /\
        address_liveness_insensitive_locs `loc_includes` app_loc_fp ctxt true l /\
        app_loc_fp ctxt true l `loc_disjoint` I.footprint sl /\
        U64.v pos <= U64.v posf /\
        U64.v posf == Seq.length (I.get_read sl h)
      )
      (ensures fun h0 res h1 ->
        let sl = Ghost.reveal sl in
        modifies (app_loc_fp ctxt true l) h0 h1 /\
        B.live h1 ctxt /\
        inv h1 /\
        (returns_true ==> res === true))

module LP = LowParse.Spec.Base
module LPL = LowParse.Low.Base

unfold
let valid_consumed
  (#input_buffer_t: Type0)
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (h': HS.mem)
  (sl: input_buffer_t)
: Tot prop
= I.live sl h /\
  I.live sl h' /\
  begin
    let s = I.get_remaining sl h in
    begin match LP.parse p s with
    | None -> False
    | Some (_, len) -> I.get_remaining sl h' `Seq.equal` Seq.slice s len (Seq.length s)
    end
  end

unfold
let valid_length
  (#input_buffer_t: Type0)
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (sl: input_buffer_t)
  (len: int)
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

inline_for_extraction noextract
let validate_with_action_t' 
     (#k:LP.parser_kind)
     (#t:Type)
     (p:LP.parser k t)
     (inv:slice_inv)
     (disj:disjointness_pre)
     (l:eloc)
     (has_action:bool)
     (allow_reading:bool)
: Type 
= (# [EverParse3d.Util.solve_from_ctx ()] I.extra_t #input_buffer_t) ->
  (ctxt: app_ctxt) ->
  (error_handler_fn : error_handler) ->
  (sl: input_buffer_t) ->
  (len: I.tlen sl) ->
  (pos: LPE.pos_t) ->
  Stack U64.t
  (requires fun h ->
    I.live sl h /\
    disj /\
    inv h /\
    B.live h ctxt /\
    B.live h (AppCtxt.action_ghost_ptr ctxt) /\
    loc_not_unused_in h `loc_includes` app_loc_fp ctxt true l /\
    address_liveness_insensitive_locs `loc_includes` app_loc_fp ctxt true l /\
    U64.v pos == Seq.length (I.get_read sl h) /\
    app_loc_fp ctxt true l `loc_disjoint` I.footprint sl
  )
  (ensures fun h res h' ->
    I.live sl h' /\
    modifies (app_loc_fp ctxt has_action l `loc_union` I.perm_footprint sl) h h' /\
    inv h' /\
    B.live h' ctxt /\
    (((~ allow_reading) \/ LPE.is_error res) ==> U64.v (LPE.get_validator_error_pos res) == Seq.length (I.get_read sl h')) /\
    begin let s = I.get_remaining sl h in
    if LPE.is_success res
    then
      begin if allow_reading
      then U64.v res >= U64.v pos /\ valid_length p h sl (U64.v res - U64.v pos) /\ I.get_remaining sl h' == s
      else valid_consumed p h h' sl
      end
    else
      let s' = I.get_remaining sl h' in
      (LPE.get_validator_error_kind res <> LPE.get_validator_error_kind LPE.validator_error_action_failed ==> None? (LP.parse p s)) /\
      Seq.length s' <= Seq.length s /\
      s' `Seq.equal` Seq.slice s (Seq.length s - Seq.length s') (Seq.length s)
    end
    )

let validate_with_action_t p inv disj l has_action allow_reading = validate_with_action_t' p inv disj l has_action allow_reading

let validate_eta v =
  fun ctxt error_handler_fn sl pos -> v ctxt error_handler_fn sl pos

let act_with_comment
  s res a
=
  fun ctxt err sl len pos posf ->
  LPL.comment s;
  a ctxt err sl len pos posf

let leaf_reader
  #nz
  #k
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (# [EverParse3d.Util.solve_from_ctx ()] _extra_t : I.extra_t #input_buffer_t ) ->
  (sl: input_buffer_t) ->
  (pos: LPE.pos_t) ->
  Stack t
  (requires (fun h ->
    valid p h sl /\
    U64.v pos == Seq.length (I.get_read sl h)
  ))
  (ensures (fun h res h' ->
    let s = I.get_remaining sl h in
    I.live sl h' /\
    modifies (I.perm_footprint sl) h h' /\
    begin match LP.parse p s with
    | None -> False
    | Some (y, len) ->
      res == y /\
      I.get_remaining sl h' == Seq.slice s len (Seq.length s)
    end
  ))

#push-options "--z3rlimit 32"

inline_for_extraction
noextract
let validate_with_success_action'
      (name: string)
      #nz #wk (#k1:parser_kind nz wk)
      #t1 (#p1:parser k1 t1)
      (#inv1:_) (#disj1:_) (#l1:eloc) #ha
      (v1:validate_with_action_t p1 inv1 disj1 l1 ha false)
      (#inv2:_) (#disj2:_) (#l2:eloc) #b #rt
      (a:action inv2 disj2 l2 b rt bool)
  : validate_with_action_t p1 
      (conj_inv inv1 inv2)
      (conj_disjointness disj1 disj2)
      (l1 `eloc_union` l2)
      true false
  = fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos0 = start_position in
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 ctxt error_handler_fn input input_length pos0 in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPE.is_success pos1
    then
         [@(rename_let ("action_success_" ^ name))]
         let b = a ctxt error_handler_fn input input_length pos0 pos1 in
         let h2 = HST.get () in
         modifies_address_liveness_insensitive_unused_in h1 h2;
         if rt
         then pos1
         else (
           if not b
           then LPE.set_validator_error_pos LPE.validator_error_action_failed pos1
           else pos1
         )
    else
         pos1

inline_for_extraction
noextract
let validate_drop_true
     (#k:LP.parser_kind) 
     (#t:Type)
     (#p:LP.parser k t)
     (#inv:slice_inv)
     (#disj:disjointness_pre)
     (#l:eloc) #ha
     (v: validate_with_action_t' p inv disj l ha true)
: Tot (validate_with_action_t' p inv disj l ha false)
= fun ctxt error_handler_fn input input_length start_position ->
  [@inline_let] let pos = start_position in
  let res = v ctxt error_handler_fn input input_length pos in
  I.skip_if_success input pos res;
  res

inline_for_extraction
noextract
let validate_drop
     (#k:LP.parser_kind)
     (#t:Type)
     (#p:LP.parser k t)
     (#inv:slice_inv)
     (#disj:disjointness_pre)
     (#l:eloc)
     #ha #allow_reading
     (v: validate_with_action_t' p inv disj l ha allow_reading)
: Tot (validate_with_action_t' p inv disj l ha false)
= if allow_reading
  then validate_drop_true v
  else v

let validate_without_reading v = validate_drop v

let validate_with_success_action
  name v1 a
= validate_with_success_action' name (validate_drop v1) a

inline_for_extraction noextract
let validate_with_error_handler
      (typename:string) 
      (fieldname:string)
      #nz
      #wk
      (#k1:parser_kind nz wk)
      #t1
      (#p1:parser k1 t1)
      (#inv1 #disj1:_)
      (#l1:eloc)
      (#ha #ar:_)
      (v1:validate_with_action_t p1 inv1 disj1 l1 ha ar)
  : validate_with_action_t p1 inv1 disj1 l1 ha ar
  = fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos0 = start_position in
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ typename))]
    let pos1 = v1 ctxt error_handler_fn input input_length pos0 in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPE.is_success pos1
    then pos1
    else (
         error_handler_fn typename fieldname (LPE.error_reason_of_result pos1) (LPE.get_validator_error_kind pos1) ctxt input pos0;
         pos1
    )

inline_for_extraction noextract
let validate_ret
  : validate_with_action_t (parse_ret ()) true_inv disjointness_trivial eloc_none false true
  = fun ctxt error_handler_fn input input_length start_position ->
    start_position

#push-options "--z3rlimit 32"

module LPC = LowParse.Spec.Combinators

inline_for_extraction
noextract
let validate_total_constant_size_no_read'
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (sz: U64.t)
  (u: unit {
    k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
    k.LP.parser_kind_low == U64.v sz /\
    k.LP.parser_kind_metadata == Some LP.ParserKindMetadataTotal
  })
  inv disj l
: validate_with_action_t' p inv disj l false true
= fun ctxt error_handler_fn input input_length start_position ->
  [@inline_let] let pos = start_position in
  let h = HST.get () in
  LP.parser_kind_prop_equiv k p; 
  let hasBytes = I.has input input_length pos sz in
  let h2 = HST.get () in
  modifies_address_liveness_insensitive_unused_in h h2;
  if hasBytes
  then pos `U64.add` sz
  else LPE.set_validator_error_pos LPE.validator_error_not_enough_data pos

inline_for_extraction
noextract
let validate_total_constant_size_no_read
  #nz #wk
  (#k: parser_kind nz wk)
  (#t: Type)
  (p: parser k t)
  (sz: U64.t)
  (u: unit {
    k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
    k.LP.parser_kind_low == U64.v sz /\
    k.LP.parser_kind_metadata == Some LP.ParserKindMetadataTotal
  })
  inv disj l
: Tot (validate_with_action_t p inv disj l false true)
= validate_total_constant_size_no_read' p sz u inv disj l

inline_for_extraction noextract
let validate_pair
       (name1: string)
       #nz1 (#k1:parser_kind nz1 WeakKindStrongPrefix) #t1 (#p1:parser k1 t1)
       (k1_const: bool)
       (#inv1 #disj1:_) (#l1:eloc) (#ha1 #ar1:_) (v1:validate_with_action_t p1 inv1 disj1 l1 ha1 ar1)
       #nz2 #wk2 (#k2:parser_kind nz2 wk2) #t2 (#p2:parser k2 t2)
       (k2_const: bool)
       (#inv2 #disj2:_) (#l2:eloc) (#ha2 #ar2:_) (v2:validate_with_action_t p2 inv2 disj2 l2 ha2 ar2)
  : validate_with_action_t
      (p1 `parse_pair` p2)
      (conj_inv inv1 inv2)
      (conj_disjointness disj1 disj2)
      (l1 `eloc_union` l2)
      (ha1 || ha2)
      false
  =
    if k1_const && k2_const &&
      (not ha1) && (not ha2) && // IMPORTANT: do not erase actions from v1, v2
      k1.parser_kind_high = Some k1.parser_kind_low &&
      k1.parser_kind_metadata = Some LP.ParserKindMetadataTotal &&
      k2.parser_kind_high = Some k2.parser_kind_low &&
      k2.parser_kind_metadata = Some LP.ParserKindMetadataTotal &&
      k1.parser_kind_low + k2.parser_kind_low < 4294967296
    then
      validate_drop (validate_total_constant_size_no_read (p1 `parse_pair` p2) (U64.uint_to_t (k1.parser_kind_low + k2.parser_kind_low)) () (conj_inv inv1 inv2) (conj_disjointness disj1 disj2) (l1 `eloc_union` l2))
    else
    fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos = start_position in
    let h = HST.get () in
    LPC.nondep_then_eq p1 p2 (I.get_remaining input h);
    [@(rename_let ("positionAfter" ^ name1))]
    let pos1 = validate_drop v1 ctxt error_handler_fn input input_length pos in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if LPE.is_error pos1
    then
      pos1
    else
      validate_drop v2 ctxt error_handler_fn input input_length pos1

inline_for_extraction noextract
let validate_dep_pair
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #disj1 #l1 #ha1 (v1:validate_with_action_t p1 inv1 disj1 l1 ha1 true) (r1: leaf_reader p1)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #disj2 #l2 #ha2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 disj2 l2 ha2 ar2))
  = fun ctxt error_handler_fn input input_length start_position ->
      [@inline_let] let pos = start_position in
      let h = HST.get () in
      LPC.parse_dtuple2_eq p1 p2 (I.get_remaining input h);
      [@(rename_let ("positionAfter" ^ name1))]
      let pos1 = v1 ctxt error_handler_fn input input_length pos in
      let h1 = HST.get() in
      if LPE.is_error pos1
      then begin
        pos1
      end
      else
        [@(rename_let ("" ^ name1))]
        let x = r1 input pos in
        let h15 = HST.get () in
        let _ = modifies_address_liveness_insensitive_unused_in h h15 in
        validate_drop (v2 x) ctxt error_handler_fn input input_length pos1

#pop-options

#push-options "--z3rlimit 64"
#restart-solver

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action'
      (name1: string)
      (#nz1: _) (#k1:parser_kind nz1 _) (#t1: _) (#p1:parser k1 t1)
      (#inv1 #disj1 #l1 #ha1: _) (v1:validate_with_action_t p1 inv1 disj1 l1 ha1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      (#inv1' #disj1' #l1' #b #rt: _) (a:t1 -> action inv1' disj1' l1' b rt bool)
      (#nz2 #wk2: _) (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f) -> parser k2 (t2 x))
      (#inv2 #disj2 #l2 #ha2 #ar2: _) (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 disj2 l2 ha2 ar2))
: validate_with_action_t
      ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
      (conj_inv inv1 (conj_inv inv1' inv2))
      (conj_disjointness disj1 (conj_disjointness disj1' disj2))
      (l1 `eloc_union` (l1' `eloc_union` l2))
      true
      false
= fun ctxt error_handler_fn input input_length startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 ctxt error_handler_fn input input_length startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPE.is_error res
      then begin
        res
      end
      else begin
        assert (I.get_remaining input h1 == I.get_remaining input h0);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input startPosition in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionAfter" ^ name1))]
        let res1 = LPE.check_constraint_ok ok res in
        let h2 = HST.get() in
        if LPE.is_error res1
        then
          res1
        else begin
             modifies_address_liveness_insensitive_unused_in h1 h2;
             let action_result = a field_value ctxt error_handler_fn input input_length startPosition res1 in
             if rt
             then (
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) ctxt error_handler_fn input input_length res1
             )
             else (
              if not action_result
              then LPE.set_validator_error_pos LPE.validator_error_action_failed res1 //action failed
              else begin
                let h15 = HST.get () in
                let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
                validate_drop (v2 field_value) ctxt error_handler_fn input input_length res1
              end
             )
        end
      end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action_total_zero_parser'
      (name1: string)
      (#nz1: _) (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1: _) (#p1:parser k1 t1) (r1: leaf_reader p1)
      (inv1 disj1 l1: _)
      (f: t1 -> bool)
      (#inv1' #disj1' #l1' #b #rt: _) (a:t1 -> action inv1' disj1' l1' b rt bool)
      (#nz2 #wk2: _) (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#inv2 #disj2 #l2 #ha2 #ar2: _) (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 disj2 l2 ha2 ar2))
  : Pure (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (conj_disjointness disj1 (conj_disjointness disj1' disj2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             true
             false)
         (requires (
           let open LP in
           k1.parser_kind_high == Some 0 /\
           k1.parser_kind_metadata == Some ParserKindMetadataTotal
         ))
         (ensures (fun _ -> True))
  = fun ctxt error_handler_fn input input_length startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input startPosition in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionAfter" ^ name1))]
        let res1 = LPE.check_constraint_ok ok startPosition in
        if LPE.is_error res1
        then
             res1
        else let h2 = HST.get() in
             modifies_address_liveness_insensitive_unused_in h0 h2;
             let action_result = a field_value ctxt error_handler_fn input input_length startPosition res1 in
             if rt
             then (
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) ctxt error_handler_fn input input_length res1
             )
             else (
              if not action_result
              then LPE.set_validator_error_pos LPE.validator_error_action_failed startPosition //action failed
              else begin
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) ctxt error_handler_fn input input_length res1
              end
             )
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #disj1 #l1 #ha1 (v1:validate_with_action_t p1 inv1 disj1 l1 ha1 true)
      (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #disj1' #l1' #b #rt (a:t1 -> action inv1' disj1' l1' b rt bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #disj2 #l2 #ha2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 disj2 l2 ha2 ar2))
  = if
      p1_is_constant_size_without_actions `LP.bool_and`
      (k1.LP.parser_kind_high = Some 0) `LP.bool_and`
      (k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal)
    then
      validate_dep_pair_with_refinement_and_action_total_zero_parser' name1 r1 inv1 disj1 l1 f a v2
    else
      validate_dep_pair_with_refinement_and_action' name1 v1 r1 f a v2


inline_for_extraction noextract
let validate_dep_pair_with_action
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #disj1 #l1 #ha1 (v1:validate_with_action_t p1 inv1 disj1 l1 ha1 true) (r1: leaf_reader p1)
      #inv1' #disj1' #l1' #b #rt (a:t1 -> action inv1' disj1' l1' b rt bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #disj2 #l2 #ha2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 disj2 l2 ha2 ar2))
  = fun ctxt error_handler_fn input input_length startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ p1 #_ #t2 p2 (I.get_remaining input h0);
      let res = v1 ctxt error_handler_fn input input_length startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPE.is_error res
      then begin
        res
      end
      else begin
        let field_value = r1 input startPosition in
        let h2 = HST.get() in
        modifies_address_liveness_insensitive_unused_in h1 h2;
        let action_result = a field_value ctxt error_handler_fn input input_length startPosition res in
        let h3 = HST.get () in
        modifies_address_liveness_insensitive_unused_in h2 h3;
        if rt 
        then (
          validate_drop (v2 field_value) ctxt error_handler_fn input input_length res
        )
        else (
          if not action_result
          then LPE.set_validator_error_pos LPE.validator_error_action_failed res //action failed
          else
                validate_drop (v2 field_value) ctxt error_handler_fn input input_length res
       )

      end

inline_for_extraction noextract
let validate_dep_pair_with_refinement'
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #disj1 #l1 #ha1 (v1:validate_with_action_t p1 inv1 disj1 l1 ha1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #disj2 #l2 #ha2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 disj2 l2 ha2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (conj_disjointness disj1 disj2)
             (l1 `eloc_union` l2)
             (ha1||ha2)
             false)
  = fun ctxt error_handler_fn input input_length startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 ctxt error_handler_fn input input_length startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPE.is_error res
      then begin
        res
      end
      else begin
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input startPosition in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionAfter" ^ name1))]
        let res1 = LPE.check_constraint_ok ok res in
        if LPE.is_error res1
        then
             res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             validate_drop (v2 field_value) ctxt error_handler_fn input input_length res1
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_total_zero_parser'
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      (inv1 disj1 l1: _) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #disj2 #l2 #ha2 #ar2
      ha1 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 disj2 l2 ha2 ar2))
  : Pure (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (conj_disjointness disj1 disj2)
             (l1 `eloc_union` l2)
             (ha1 || ha2)
             false)
         (requires (
           let open LP in
           k1.parser_kind_high == Some 0 /\
           k1.parser_kind_metadata == Some ParserKindMetadataTotal
         ))
         (ensures (fun _ -> True))
  = fun ctxt error_handler_fn input input_length startPosition ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input startPosition in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionAfter" ^ name1))]
        let res1 = LPE.check_constraint_ok ok startPosition in
        if LPE.is_error res1
        then res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h0 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             validate_drop (v2 field_value) ctxt error_handler_fn input input_length res1
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #disj1 #l1 #ha1 (v1:validate_with_action_t p1 inv1 disj1 l1 ha1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #disj2 #l2 #ar2 #ha2
      (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 disj2 l2 ha2 ar2))
= if
    p1_is_constant_size_without_actions `LP.bool_and`
    (k1.LP.parser_kind_high = Some 0) `LP.bool_and`
    (k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal)
  then
    validate_dep_pair_with_refinement_total_zero_parser' name1 inv1 disj1 l1 r1 f ha1 v2
  else
    validate_dep_pair_with_refinement' name1 v1 r1 f v2

inline_for_extraction noextract
let validate_filter
      (name: string)
      #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
      #inv #disj #l #ha (v:validate_with_action_t p inv disj l ha true)
      (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
= fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos = start_position in
    let h = HST.get () in
    LPC.parse_filter_eq p f (I.get_remaining input h);
    [@(rename_let ("positionAfter" ^ name))]
    let res = v ctxt error_handler_fn input input_length pos in
    let h1 = HST.get () in
    if LPE.is_error res
    then res
    else begin
      LowStar.Comment.comment cr;
      [@(rename_let ("" ^ name))]
      let field_value = r input pos in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      LPE.check_constraint_ok ok res
    end

inline_for_extraction noextract
let validate_filter_with_action
      (name: string) 
      #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
      #inv #disj #l #ha (v:validate_with_action_t p inv disj l ha true)
      (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
      (#b #rt:bool) #inva #disja (#la:eloc)
      (a: t -> action inva disja la b rt bool)
= fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos0 = start_position in
    let h = HST.get () in
    LPC.parse_filter_eq p f (I.get_remaining input h);
    [@(rename_let ("positionAfter" ^ name))]
    let res = v ctxt error_handler_fn input input_length pos0 in
    let h1 = HST.get () in
    if LPE.is_error res
    then res
    else begin
      LowStar.Comment.comment cr;
      [@(rename_let ("" ^ name))]
      let field_value = r input pos0 in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      if ok
        then let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h h15 in
             let action_result = a field_value ctxt error_handler_fn input input_length pos0 res in
             if rt 
             then res
             else if action_result
             then res
             else LPE.set_validator_error_pos LPE.validator_error_action_failed res
      else LPE.set_validator_error_pos LPE.validator_error_constraint_failed res
    end

inline_for_extraction noextract
let validate_with_dep_action
      (name: string)
      #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
      #inv #disj #l #ha
      (v:validate_with_action_t p inv disj l ha true)
      (r:leaf_reader p)
      (#b #rt:bool) #inva #disja (#la:eloc)
      (a: t -> action inva disja la b rt bool)
= fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos0 = start_position in
    let h = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v ctxt error_handler_fn input input_length pos0 in
    let h1 = HST.get () in
    if LPE.is_error res
    then res
    else begin
      [@(rename_let ("" ^ name))]
      let field_value = r input pos0 in
      let h15 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h15 in
      let action_result = a field_value ctxt error_handler_fn input input_length pos0 res in
      if rt then res
      else if action_result
      then res
      else LPE.set_validator_error_pos LPE.validator_error_action_failed res
    end

inline_for_extraction noextract
let validate_weaken
      #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
      #inv #disj #l #ha #ar (v:validate_with_action_t p inv disj l ha ar)
      #nz' #wk' (k':parser_kind nz' wk'{k' `is_weaker_than` k})
: validate_with_action_t (parse_weaken p k') inv disj l ha ar
= fun ctxt error_handler_fn input input_length start_position ->
    v ctxt error_handler_fn input input_length start_position


/// Parser: weakening kinds

inline_for_extraction noextract
let validate_weaken_left 
      #nz #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
      #inv #disj #l #ar #ha (v:validate_with_action_t p inv disj l ha ar)
      #nz' #wk' (k':parser_kind nz' wk')
= validate_weaken v (glb k' k)

/// Parser: weakening kinds

inline_for_extraction noextract
let validate_weaken_right
      #nz #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
      #inv #disj #l #ar #ha (v:validate_with_action_t p inv disj l ha ar)
      #nz' #wk' (k':parser_kind nz' wk')
= validate_weaken v (glb k k')

inline_for_extraction noextract
let validate_impos ()
= fun _ _ _ _ start_position -> LPE.set_validator_error_pos LPE.validator_error_impossible start_position

noextract inline_for_extraction
let validate_ite
      e p1 v1 p2 v2
= fun ctxt error_handler_fn input input_len start_position ->
      if e 
      then validate_drop (v1 ()) ctxt error_handler_fn input input_len start_position
      else validate_drop (v2 ()) ctxt error_handler_fn input input_len start_position

module LPLL = LowParse.Spec.List

unfold
let validate_list_inv
      (#k: LPL.parser_kind)
      (#t: Type)
      (p: LPL.parser k t)
      (inv: slice_inv)
      (disj: disjointness_pre)
      (l: eloc)
      (g0 g1: Ghost.erased HS.mem)
      (ctxt:app_ctxt)
      (sl: input_buffer_t)
      (bres: pointer U64.t)
      (ha:bool)
      (h: HS.mem)
      (stop: bool)
: GTot Type0
= let h0 = Ghost.reveal g0 in
  let h1 = Ghost.reveal g1 in
  let res = Seq.index (as_seq h bres) 0 in
  inv h0 /\
  disj /\
  loc_not_unused_in h0 `loc_includes` app_loc_fp ctxt true l /\
  app_loc_fp ctxt true l `loc_disjoint` I.footprint sl /\
  app_loc_fp ctxt true l `loc_disjoint` loc_buffer bres /\
  address_liveness_insensitive_locs `loc_includes` app_loc_fp ctxt true l /\
  B.loc_buffer bres `B.loc_disjoint` I.footprint sl /\
  I.live sl h0 /\
  I.live sl h /\
  live h0 ctxt /\
  live h ctxt /\
  live h (AppCtxt.action_ghost_ptr ctxt) /\
  live h1 bres /\
  begin
    let s = I.get_remaining sl h0 in
    let s' = I.get_remaining sl h in
    Seq.length s' <= Seq.length s /\
    s' `Seq.equal` Seq.slice s (Seq.length s - Seq.length s') (Seq.length s)
  end /\
  modifies loc_none h0 h1 /\ (
  if
    LPE.is_error res
  then
    // validation *or action* failed
    stop == true /\
    U64.v (LPE.get_validator_error_pos res) == Seq.length (I.get_read sl h) /\
    (LPE.get_validator_error_kind res <> LPE.get_validator_error_kind LPE.validator_error_action_failed ==> ~ (valid (LPLL.parse_list p) h0 sl))
  else
    U64.v res == Seq.length (I.get_read sl h) /\
    (valid (LPLL.parse_list p) h0 sl <==>
     valid (LPLL.parse_list p) h sl) /\
    (stop == true ==> (valid (LPLL.parse_list p) h sl /\ Seq.length (I.get_remaining sl h) == 0))
  ) /\
  modifies (app_loc_fp ctxt ha l `loc_union` loc_buffer bres `loc_union` I.perm_footprint sl) h1 h

inline_for_extraction
noextract
let validate_list_body
  (# [EverParse3d.Util.solve_from_ctx ()] _extra_t : I.extra_t #input_buffer_t )
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #disj #l #ha #ar
  (v: validate_with_action_t' p inv disj l ha ar)
  (g0 g1: Ghost.erased HS.mem)
  (ctxt:app_ctxt)
  (error_handler_fn:error_handler)
  (sl: input_buffer_t)
  (sl_len: I.tlen sl)
  (bres: pointer U64.t)
: HST.Stack bool
  (requires (fun h -> validate_list_inv p inv disj l g0 g1 ctxt sl bres ha h false))
  (ensures (fun h res h' ->
    validate_list_inv p inv disj l g0 g1 ctxt sl bres ha h false /\
    validate_list_inv p inv disj l g0 g1 ctxt sl bres ha h' res
  ))
=
  let h = HST.get () in
  LPLL.parse_list_eq p (I.get_remaining sl h);
  let position = !* bres in
  if not (I.has sl sl_len position 1uL)
  then true
  else begin
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in (Ghost.reveal g0) h1;
    let result = validate_drop v ctxt error_handler_fn sl sl_len position in
    upd bres 0ul result;
    LPE.is_error result
  end

inline_for_extraction
noextract
let validate_list'
  (# [EverParse3d.Util.solve_from_ctx ()] _extra_t : I.extra_t #input_buffer_t )
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #disj #l #ha #ar
  (v: validate_with_action_t' p inv disj l ha ar)
  (ctxt: app_ctxt)
  (error_handler_fn: error_handler)
  (sl: input_buffer_t)
  (sl_len: I.tlen sl)
  (pos: LPE.pos_t)
: HST.Stack U64.t
  (requires (fun h ->
    inv h /\
    disj /\
    loc_not_unused_in h `loc_includes` app_loc_fp ctxt true l /\
    app_loc_fp ctxt true l `loc_disjoint` I.footprint sl /\
    address_liveness_insensitive_locs `loc_includes` app_loc_fp ctxt true l /\
    B.live h ctxt /\
    I.live sl h /\
    B.live h (AppCtxt.action_ghost_ptr ctxt) /\
    U64.v pos == Seq.length (I.get_read sl h)
  ))
  (ensures (fun h res h' ->
    let s = I.get_remaining sl h in
    inv h' /\
    B.live h' ctxt /\
    I.live sl h' /\
    begin
      let s' = I.get_remaining sl h' in
      Seq.length s' <= Seq.length s /\
      s' `Seq.equal` Seq.slice s (Seq.length s - Seq.length s') (Seq.length s)
    end /\
    begin match LP.parse (LPLL.parse_list p) s with
    | None -> LPE.is_success res == false
    | Some (_, len) ->
      if LPE.is_success res
      then I.get_remaining sl h' `Seq.equal` Seq.slice s len (Seq.length s) /\
           U64.v res == Seq.length (I.get_read sl h')
      else LPE.get_validator_error_kind res == LPE.get_validator_error_kind LPE.validator_error_action_failed
    end /\
    (LPE.is_success res == false ==> U64.v (LPE.get_validator_error_pos res) == Seq.length (I.get_read sl h')) /\
    modifies (app_loc_fp ctxt ha l `B.loc_union` I.perm_footprint sl) h h'
  ))
= let h0 = HST.get () in
  let g0 = Ghost.hide h0 in
  HST.push_frame ();
  let h02 = HST.get () in
  fresh_frame_modifies h0 h02;
  let result = alloca pos 1ul in
  let h1 = HST.get () in
  let g1 = Ghost.hide h1 in
  I.live_not_unused_in sl h0;
  C.Loops.do_while
    (validate_list_inv p inv disj l g0 g1 ctxt sl result ha)
    (fun _ -> validate_list_body v g0 g1 ctxt error_handler_fn sl sl_len result);
  let finalResult = index result 0ul in
  let h2 = HST.get () in
  HST.pop_frame ();
  let h' = HST.get () in
  assert (B.modifies (app_loc_fp ctxt ha l `B.loc_union` I.perm_footprint sl) h0 h');
  LP.parser_kind_prop_equiv LPLL.parse_list_kind (LPLL.parse_list p);
  finalResult

inline_for_extraction
noextract
let validate_list
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #disj #l #ha #ar
  (v: validate_with_action_t' p inv disj l ha ar)
: validate_with_action_t' (LowParse.Spec.List.parse_list p) inv disj l ha false
= fun ctxt error_handler_fn input input_length start_position ->
  validate_list' v ctxt error_handler_fn input input_length start_position

#push-options "--z3rlimit 32"
#restart-solver

module LPLF = LowParse.Low.FLData

noextract
inline_for_extraction
let validate_fldata_consumes_all
      (n:U32.t)
      (#k: LP.parser_kind)
      #t
      (#p: LP.parser k t)
      #inv #disj #l #ha #ar
      (v: validate_with_action_t' p inv disj l ha ar  { k.LP.parser_kind_subkind == Some LP.ParserConsumesAll })
: validate_with_action_t' (LowParse.Spec.FLData.parse_fldata p (U32.v n)) inv disj l ha false
= fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos = start_position in
    let h = HST.get () in
    LPLF.parse_fldata_consumes_all_correct p (U32.v n) (I.get_remaining input h);
    let hasEnoughBytes = I.has input input_length pos (Cast.uint32_to_uint64 n) in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if not hasEnoughBytes
    then LPE.set_validator_error_pos LPE.validator_error_not_enough_data pos
    else begin
      let truncatedInput = I.truncate input pos (Cast.uint32_to_uint64 n) in
      let truncatedInputLength = I.truncate_len input pos (Cast.uint32_to_uint64 n) truncatedInput in
      let h2 = HST.get () in
      modifies_address_liveness_insensitive_unused_in h h2;
      I.is_prefix_of_prop truncatedInput input h2;
      assert (I.get_remaining truncatedInput h2 `Seq.equal` Seq.slice (I.get_remaining input h) 0 (U32.v n));
      let res = validate_drop v ctxt error_handler_fn truncatedInput truncatedInputLength pos in
      let h3 = HST.get () in
      I.is_prefix_of_prop truncatedInput input h3;
      res
    end

#pop-options

#push-options "--z3rlimit_factor 16 --z3cliopt smt.arith.nl=false"
#restart-solver

noextract
inline_for_extraction
let validate_fldata
      (n:U32.t)
      (#k: LP.parser_kind)
      #t
      (#p: LP.parser k t)
      #inv #disj #l #ha #ar
      (v: validate_with_action_t' p inv disj l ha ar)
: validate_with_action_t' (LowParse.Spec.FLData.parse_fldata p (U32.v n)) inv disj l ha false
= fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos = start_position in
    let h = HST.get () in
    let hasEnoughBytes = I.has input input_length pos (Cast.uint32_to_uint64 n) in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if not hasEnoughBytes
    then LPE.set_validator_error_pos LPE.validator_error_not_enough_data pos
    else begin
      let truncatedInput = I.truncate input pos (Cast.uint32_to_uint64 n) in
      let truncatedInputLength = I.truncate_len input pos (Cast.uint32_to_uint64 n) truncatedInput in
      let h2 = HST.get () in
      modifies_address_liveness_insensitive_unused_in h h2;
      I.is_prefix_of_prop truncatedInput input h2;
      assert (I.get_remaining truncatedInput h2 `Seq.equal` Seq.slice (I.get_remaining input h) 0 (U32.v n));
      let res = validate_drop v ctxt error_handler_fn truncatedInput truncatedInputLength pos in
      let h3 = HST.get () in
      modifies_address_liveness_insensitive_unused_in h h3;
      I.is_prefix_of_prop truncatedInput input h3;
      if LPE.is_error res
      then res
      else begin
        let stillHasBytes = I.has truncatedInput truncatedInputLength res 1uL in
        let h4 = HST.get () in
        modifies_address_liveness_insensitive_unused_in h h4;
        if stillHasBytes
        then LPE.set_validator_error_pos LPE.validator_error_unexpected_padding res
        else res
      end
    end

#pop-options

noextract
inline_for_extraction
let validate_nlist
  (n:U32.t)
  (n_is_const:option nat { memoizes_n_as_const n_is_const n})
  #wk
  (#k:parser_kind true wk)
  #t
  (#p:parser k t)
  #inv #disj #l #ha #ar
  (v: validate_with_action_t p inv disj l ha ar)
: Tot (validate_with_action_t (parse_nlist n n_is_const p) inv disj l ha false)
= fun ctxt error_handler_fn input input_length start_position ->
    validate_fldata_consumes_all n (validate_list v) ctxt error_handler_fn input input_length start_position

inline_for_extraction noextract
let validate_nlist_total_constant_size_mod_ok
      (n:U32.t)
      (n_is_const:option nat { memoizes_n_as_const n_is_const n})
      #wk 
      (#k:parser_kind true wk)
      (#t: Type)
      (p:parser k t)
      inv
      disj
      l
  : Pure (validate_with_action_t (parse_nlist n n_is_const p) inv disj l false true)
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296 /\
    U32.v n % k.LP.parser_kind_low == 0
  ))
  (ensures (fun _ -> True))
= [@inline_let]
  let _ =
    parse_nlist_total_fixed_size_kind_correct n n_is_const p
  in
  validate_total_constant_size_no_read'
    (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n n_is_const p))
    (Cast.uint32_to_uint64 n)
    () inv disj l

inline_for_extraction noextract
let validate_nlist_constant_size_mod_ko
      (n:U32.t)
      (n_is_const:option nat{ memoizes_n_as_const n_is_const n})
      (#wk: _)
      (#k:parser_kind true wk)
      #t
      (p:parser k t)
      inv disj l
  : Pure (validate_with_action_t (parse_nlist n n_is_const p) inv disj l false true)
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.LP.parser_kind_low <> 0
  ))
  (ensures (fun _ -> True))
= 
  (fun ctxt error_handler_fn input input_length start_position ->
     [@inline_let] let pos = start_position in
     let h = FStar.HyperStack.ST.get () in
     [@inline_let]
     let f () : Lemma
       (requires (Some? (LP.parse (parse_nlist n n_is_const p) (I.get_remaining input h))))
       (ensures False)
     = let sq = I.get_remaining input h in
       let sq' = Seq.slice sq 0 (U32.v n) in
       LowParse.Spec.List.list_length_constant_size_parser_correct p sq' ;
       let Some (l, _) = LP.parse (parse_nlist n n_is_const p) sq in
       assert (U32.v n == FStar.List.Tot.length l `Prims.op_Multiply` k.LP.parser_kind_low) ;
       FStar.Math.Lemmas.cancel_mul_mod (FStar.List.Tot.length l) k.LP.parser_kind_low ;
       assert (U32.v n % k.LP.parser_kind_low == 0)
     in
     [@inline_let]
     let _ = Classical.move_requires f () in
     LPE.set_validator_error_pos LPE.validator_error_list_size_not_multiple pos
  )

inline_for_extraction noextract
let validate_nlist_total_constant_size'
      (n:U32.t)
      (n_is_const:option nat { memoizes_n_as_const n_is_const n })
      #wk
      (#k:parser_kind true wk)
      #t
      (p:parser k t)
      inv disj l
  : Pure (validate_with_action_t (parse_nlist n n_is_const p) inv disj l false true)
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296
  ))
  (ensures (fun _ -> True))
= fun ctxt error_handler_fn input start_position -> // n is not an integer constant, so we need to eta-expand and swap fun and if
  if n `U32.rem` U32.uint_to_t k.LP.parser_kind_low = 0ul
  then validate_nlist_total_constant_size_mod_ok n n_is_const p inv disj l ctxt error_handler_fn input start_position
  else validate_nlist_constant_size_mod_ko n n_is_const p inv disj l ctxt error_handler_fn input start_position

inline_for_extraction noextract
let validate_nlist_total_constant_size
      (n:U32.t)
      (n_is_const: option nat { memoizes_n_as_const n_is_const n })
      #wk
      (#k:parser_kind true wk)
      (#t: Type)
      (p:parser k t)
      inv disj l
: Pure (validate_with_action_t (parse_nlist n n_is_const p) inv disj l false true)
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
    else match n_is_const with
         | Some n -> n % k.LP.parser_kind_low = 0
         | _ -> false
  then
    validate_nlist_total_constant_size_mod_ok n n_is_const p inv disj l
  else if
    match n_is_const with
    | Some n -> n % k.LP.parser_kind_low <> 0
    | _ -> false
  then
    validate_nlist_constant_size_mod_ko n n_is_const p inv disj l
  else
    validate_nlist_total_constant_size' n n_is_const p inv disj l

noextract
inline_for_extraction
let validate_nlist_constant_size_without_actions
    (n:U32.t)
    (n_is_const:option nat { memoizes_n_as_const n_is_const n })
    (payload_is_constant_size: bool)
    #wk
    (#k:parser_kind true wk)
    #t (#p:parser k t) #inv #disj #l #ar
    (v: validate_with_action_t p inv disj l false ar)
: Tot (validate_with_action_t (parse_nlist n n_is_const p) inv disj l false false)
= 
  if payload_is_constant_size
  then (
    if
      let open LP in
      k.parser_kind_subkind = Some ParserStrong &&
      k.parser_kind_high = Some k.parser_kind_low &&
      k.parser_kind_metadata = Some ParserKindMetadataTotal &&
      k.parser_kind_low < 4294967296
    then
      validate_drop (validate_nlist_total_constant_size n n_is_const p inv disj l)
    else
      validate_nlist n n_is_const v
  )
  else
    validate_nlist n n_is_const v

#push-options "--z3rlimit_factor 16 --z3cliopt smt.arith.nl=false"
#restart-solver

noextract inline_for_extraction
let validate_t_at_most
      (n:U32.t) #nz #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
      #inv #disj #l #ha #ar (v:validate_with_action_t p inv disj l ha ar)
  : Tot (validate_with_action_t (parse_t_at_most n p) inv disj l ha false)
  = fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos = start_position in
    let h = HST.get () in
    let hasBytes = I.has input input_length pos (Cast.uint32_to_uint64 n) in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if not hasBytes
    then
      LPE.set_validator_error_pos LPE.validator_error_not_enough_data pos
    else
      let truncatedInput = I.truncate input pos (Cast.uint32_to_uint64 n) in
      let truncatedInputLength = I.truncate_len input pos (Cast.uint32_to_uint64 n) truncatedInput in
      let h2 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h2 in
      let _ = I.is_prefix_of_prop truncatedInput input h2 in
      let _ = assert (I.get_remaining truncatedInput h2 `Seq.equal` Seq.slice (I.get_remaining input h) 0 (U32.v n)) in
      [@inline_let] let _ = LPC.nondep_then_eq p parse_all_bytes (I.get_remaining truncatedInput h2) in
      let result = validate_drop v ctxt error_handler_fn truncatedInput truncatedInputLength pos in
      let h3 = HST.get () in
      let _ = I.is_prefix_of_prop truncatedInput input h3 in
      if LPE.is_error result
      then result
      else begin
        let _ = I.empty truncatedInput truncatedInputLength result in
        let h4 = HST.get () in
        modifies_address_liveness_insensitive_unused_in h h4;
        let _ = I.is_prefix_of_prop truncatedInput input h4 in
        pos `U64.add` Cast.uint32_to_uint64 n
      end

#pop-options

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false"
#restart-solver

noextract inline_for_extraction
let validate_t_exact
      (n:U32.t) #nz #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
      #inv #disj #l #ha #ar
      (v:validate_with_action_t p inv disj l ha ar)
: validate_with_action_t (parse_t_exact n p) inv disj l ha false
= fun ctxt error_handler_fn input input_length start_position ->
    [@inline_let] let pos = start_position in
    let h = HST.get () in
    let hasBytes = I.has input input_length pos (Cast.uint32_to_uint64 n) in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if not hasBytes
    then
      LPE.set_validator_error_pos LPE.validator_error_not_enough_data pos
    else
      let truncatedInput = I.truncate input pos (Cast.uint32_to_uint64 n) in
      let truncatedInputLength = I.truncate_len input pos (Cast.uint32_to_uint64 n) truncatedInput in
      let h2 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h2 in
      let _ = I.is_prefix_of_prop truncatedInput input h2 in
      let _ = assert (I.get_remaining truncatedInput h2 `Seq.equal` Seq.slice (I.get_remaining input h) 0 (U32.v n)) in
      [@inline_let] let _ = LPC.nondep_then_eq p parse_all_bytes (I.get_remaining truncatedInput h2) in
      let result = validate_drop v ctxt error_handler_fn truncatedInput truncatedInputLength pos in
      let h3 = HST.get () in
      let _ = I.is_prefix_of_prop truncatedInput input h3 in
      if LPE.is_error result
      then result
      else begin
        let stillHasBytes = I.has truncatedInput truncatedInputLength result 1uL in
        let h4 = HST.get () in
        modifies_address_liveness_insensitive_unused_in h h4;
        I.is_prefix_of_prop truncatedInput input h4;
        if stillHasBytes
        then LPE.set_validator_error_pos LPE.validator_error_unexpected_padding result
        else result
      end

#pop-options

inline_for_extraction noextract
let validate_with_comment
      (c:string)
      #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
      #inv #disj #l #ha #ar (v:validate_with_action_t p inv disj l ha ar)
: validate_with_action_t p inv disj l ha ar
= fun ctxt error_handler_fn input input_length start_position ->
    LowParse.Low.Base.comment c;
    v ctxt error_handler_fn input input_length start_position

inline_for_extraction noextract
let validate_weaken_inv_loc
      #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
      #inv #disj (#l:eloc) #ha #ar
      (inv':slice_inv{inv' `inv_implies` inv})
      (disj':_{ disj' `imp_disjointness` disj})
      (l':eloc{l' `eloc_includes` l})
      (v:validate_with_action_t p inv disj l ha ar)
  : Tot (validate_with_action_t p inv' disj' l' ha ar)
  = v


////////////////////////////////////////////////////////////////////////////////
//Base types
////////////////////////////////////////////////////////////////////////////////
inline_for_extraction noextract
let read_filter #nz
                (#k: parser_kind nz WeakKindStrongPrefix)
                (#t: Type)
                (#p: parser k t)
                (p32: leaf_reader p)
                (f: (t -> bool))
    : leaf_reader (parse_filter p f)
    = fun input pos ->
        let h = HST.get () in
        assert (parse_filter p f == LPC.parse_filter #k #t p f);
        assert_norm (P.refine t f == LPC.parse_filter_refine f);
        LPC.parse_filter_eq p f (I.get_remaining input h);
        p32 input pos

inline_for_extraction noextract
let read_impos 
  : leaf_reader (parse_impos())
  = fun sl pos -> 
      false_elim ()

inline_for_extraction noextract
let validate____UINT8
  : validator parse____UINT8
  = validate_with_comment
      "Checking that we have enough space for a UINT8, i.e., 1 byte"
      (validate_total_constant_size_no_read parse____UINT8 1uL () _ _ _)

inline_for_extraction noextract
let lift_reader
  (#nz: _)
  (#k: parser_kind nz WeakKindStrongPrefix)
  (#t: _)
  (p: parser k t)
  (r: LPL.leaf_reader p)
  (sz32: U32.t)
  (sz: U64.t)
: Pure (leaf_reader p)
  (requires (
    U32.v sz32 == U64.v sz /\
    U64.v sz > 0 /\
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
    k.LP.parser_kind_low = U64.v sz
  ))
  (ensures (fun _ -> True))
= fun input pos ->
  LP.parser_kind_prop_equiv k p;
  I.read t k p r input pos sz

inline_for_extraction noextract
let read____UINT8
  : leaf_reader parse____UINT8
= lift_reader _ LowParse.Low.Int.read_u8 1ul 1uL

inline_for_extraction noextract
let validate____UINT8BE
  : validator parse____UINT8BE
  = validate_with_comment
      "Checking that we have enough space for a UINT8BE, i.e., 1 byte"
      (validate_total_constant_size_no_read parse____UINT8BE 1uL () _ _ _)

inline_for_extraction noextract
let read____UINT8BE
  : leaf_reader parse____UINT8BE
= lift_reader _ LowParse.Low.Int.read_u8 1ul 1uL

inline_for_extraction noextract
let validate____UINT16BE
  : validator parse____UINT16BE
  = validate_with_comment
      "Checking that we have enough space for a UINT16BE, i.e., 2 bytes"
      (validate_total_constant_size_no_read parse____UINT16BE 2uL () _ _ _)

inline_for_extraction noextract
let read____UINT16BE
  : leaf_reader parse____UINT16BE
= lift_reader _ LowParse.Low.Int.read_u16 2ul 2uL

inline_for_extraction noextract
let validate____UINT32BE
  : validator parse____UINT32BE
  = validate_with_comment
      "Checking that we have enough space for a UINT32BE, i.e., 4 bytes"
      (validate_total_constant_size_no_read parse____UINT32BE 4uL () _ _ _)

inline_for_extraction noextract
let read____UINT32BE
  : leaf_reader parse____UINT32BE
= lift_reader _ LowParse.Low.Int.read_u32 4ul 4uL

inline_for_extraction noextract
let validate____UINT64BE
  : validator parse____UINT64BE
  = validate_with_comment
      "Checking that we have enough space for a UINT64BE, i.e., 8 bytes"
      (validate_total_constant_size_no_read parse____UINT64BE 8uL () _ _ _)

inline_for_extraction noextract
let read____UINT64BE
  : leaf_reader parse____UINT64BE
= lift_reader _ LowParse.Low.Int.read_u64 8ul 8uL

inline_for_extraction noextract
let validate____UINT16
  : validator parse____UINT16
  = validate_with_comment
      "Checking that we have enough space for a UINT16, i.e., 2 bytes"
      (validate_total_constant_size_no_read parse____UINT16 2uL () _ _ _)

inline_for_extraction noextract
let read____UINT16
  : leaf_reader parse____UINT16
= lift_reader _ LowParse.Low.BoundedInt.read_u16_le 2ul 2uL

inline_for_extraction noextract
let validate____UINT32
  : validator parse____UINT32
  = validate_with_comment
      "Checking that we have enough space for a UINT32, i.e., 4 bytes"
      (validate_total_constant_size_no_read parse____UINT32 4uL () _ _ _)

inline_for_extraction noextract
let read____UINT32
  : leaf_reader parse____UINT32
= lift_reader _ LowParse.Low.BoundedInt.read_u32_le 4ul 4uL

inline_for_extraction noextract
let validate____UINT64
  : validator parse____UINT64
  = validate_with_comment
      "Checking that we have enough space for a UINT64, i.e., 8 bytes"
      (validate_total_constant_size_no_read parse____UINT64 8uL () _ _ _)

inline_for_extraction noextract
let read____UINT64
  : leaf_reader parse____UINT64
= lift_reader _ LowParse.Low.Int.read_u64_le 8ul 8uL

inline_for_extraction noextract
let validate_unit
= fun _ _ input _ start_position -> start_position

inline_for_extraction noextract
let read_unit
= fun input pos -> ()

inline_for_extraction noextract
let validate_unit_refinement (f:unit -> bool) (cf:string)
  : validator (parse_unit `parse_filter` f)
= fun _ _ input _ start_position ->
    [@inline_let] let pos = start_position in
    let h = HST.get () in
    LPC.parse_filter_eq parse_unit f (I.get_remaining input h);
    LowStar.Comment.comment cf;
    if f ()
    then pos
    else LPE.set_validator_error_pos LPE.validator_error_constraint_failed pos


(* Reimplement validate_list_up_to with readability (but no actions) *)

module LUT = LowParse.Low.ListUpTo

unfold
let validate_list_up_to_inv
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (p: parser k t)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
  (ctxt: app_ctxt)
  (sl: input_buffer_t)
  (h0: HS.mem)
  (bres: B.pointer U64.t)
  (ha:bool)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
=
  let res = B.deref h bres in
  let q = LUT.parse_list_up_to (cond_string_up_to terminator) p prf in
  B.live h0 bres /\
  I.live sl h0 /\
  I.live sl h /\
  B.loc_disjoint (I.footprint sl) (B.loc_buffer bres `B.loc_union` app_loc_fp ctxt true loc_none) /\
  B.loc_disjoint (B.loc_buffer bres) (app_loc_fp ctxt true loc_none) /\
  B.live h0 ctxt /\
  B.live h ctxt /\
  B.live h (AppCtxt.action_ghost_ptr ctxt) /\
  loc_not_unused_in h `loc_includes` app_loc_fp ctxt true loc_none /\
  address_liveness_insensitive_locs `loc_includes` (app_loc_fp ctxt true loc_none) /\
  B.modifies (B.loc_buffer bres `B.loc_union` I.perm_footprint sl `B.loc_union` app_loc_fp ctxt ha loc_none) h0 h /\
  begin
    let s = I.get_remaining sl h0 in
    let s' = I.get_remaining sl h in
    Seq.length s' <= Seq.length s /\
    s' `Seq.equal` Seq.slice s (Seq.length s - Seq.length s') (Seq.length s) /\
    begin if LPE.is_error res
    then
      // validation *or action* failed
      stop == true /\
      U64.v (LPE.get_validator_error_pos res) == Seq.length (I.get_read sl h) /\
      (LPE.get_validator_error_kind res <> LPE.get_validator_error_kind LPE.validator_error_action_failed ==> None? (LP.parse q s))
    else
    U64.v res == Seq.length (I.get_read sl h) /\
    begin if stop
    then valid_consumed q h0 h sl
    else match LP.parse q s, LP.parse q s' with
    | None, None -> True
    | Some (_, consumed), Some (_, consumed') -> consumed' + Seq.length s - Seq.length s' == consumed
    | _ -> False
    end end
  end

inline_for_extraction
let validate_list_up_to_body
  (# [EverParse3d.Util.solve_from_ctx ()] _extra_t : I.extra_t #input_buffer_t )
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (#p: parser k t) (#ha:bool)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
  (v: validator_maybe_action p ha)
  (r: leaf_reader p)
  (ctxt:app_ctxt)
  (error_handler_fn:error_handler)
  (sl: input_buffer_t)
  (sl_len: I.tlen sl)
  (h0: HS.mem)
  (bres: B.pointer U64.t)
: HST.Stack bool
  (requires (fun h ->
    validate_list_up_to_inv p terminator prf ctxt sl h0 bres ha h false
  ))
  (ensures (fun h stop h' ->
    validate_list_up_to_inv p terminator prf ctxt sl h0 bres ha h false /\
    validate_list_up_to_inv p terminator prf ctxt sl h0 bres ha h' stop
  ))
=
  let h = HST.get () in
  assert (  loc_not_unused_in h `loc_includes` app_loc_fp ctxt true loc_none);
  LUT.parse_list_up_to_eq (cond_string_up_to terminator) p prf (I.get_remaining sl h);
  let position = !* bres in
  let result = v ctxt error_handler_fn sl sl_len position in
  B.upd bres 0ul result;
  if LPE.is_error result
  then begin
    true
  end else begin
    let value = r sl position in
    cond_string_up_to terminator value
  end

inline_for_extraction
noextract
let validate_list_up_to
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (#p: parser k t) (#ha:bool)
  (v: validator_maybe_action p ha)
  (r: leaf_reader p)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
: validate_with_action_t #true #WeakKindStrongPrefix
    (LUT.parse_list_up_to (cond_string_up_to terminator) p prf)
    true_inv disjointness_trivial eloc_none ha false
= fun ctxt error_handler_fn sl sl_len pos ->
    let h0 = HST.get () in
    HST.push_frame ();
    let h1 = HST.get () in
    fresh_frame_modifies h0 h1;
    let bres = B.alloca pos 1ul in
    let h2 = HST.get () in
    I.live_not_unused_in sl h0;
    C.Loops.do_while
      (validate_list_up_to_inv p terminator prf ctxt sl h2 bres ha)
      (fun _ -> validate_list_up_to_body terminator prf v r ctxt error_handler_fn sl sl_len h2 bres)
      ;
    let result = B.index bres 0ul in
    HST.pop_frame ();
    result

let validate_string
      (#k: parser_kind true WeakKindStrongPrefix)
      (#t: eqtype)
      (#[@@@erasable] p: parser k t)
      (#ha:_)
      (v: validator_maybe_action p ha)
      (r: leaf_reader p)
      (terminator: t)
= LP.parser_kind_prop_equiv k p;
  validate_list_up_to v r terminator (fun _ _ _ -> ())

let validate_all_bytes = fun _ _ input input_length start_position ->
  I.empty input input_length start_position

let validate_all_zeros =
  validate_list (validate_filter "parse_zeros" validate____UINT8 read____UINT8 is_zero "check if zero" "")


////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
let action_return
      (#a:Type) (x:a)
  = fun _ _ _ _ _ _ -> x

noextract
inline_for_extraction
let action_return_true
  = fun _ _ _ _ _ _ -> true

noextract
inline_for_extraction
let action_bind
      (name: string)
      (#invf:slice_inv) #disjf (#lf:eloc)
      #bf #rtf (#a:Type) (f: action invf disjf lf bf rtf a)
      (#invg:slice_inv) #disjg (#lg:eloc) #bg #rtg
      (#b:Type) (g: (a -> action invg disjg lg bg rtg b))
= fun ctxt error_handler_fn input input_length pos posf ->
    let h0 = HST.get () in
    [@(rename_let ("" ^ name))]
    let x = f ctxt error_handler_fn input input_length pos posf in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g x ctxt error_handler_fn input input_length pos posf

noextract
inline_for_extraction
let action_seq
      (#invf:slice_inv) #disjf (#lf:eloc)
      #bf #rtf (#a:Type) (f: action invf disjf lf bf rtf a)
      (#invg:slice_inv) #disjg (#lg:eloc) #bg #rtg
      (#b:Type) (g: action invg disjg lg bg rtg b)
= fun ctxt error_handler_fn input input_length pos posf ->
    let h0 = HST.get () in
    let _ = f ctxt error_handler_fn input input_length pos posf in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g ctxt error_handler_fn input input_length pos posf

noextract
inline_for_extraction
let action_ite
      (#invf:slice_inv) #disjf (#lf:eloc)
      (guard:bool)
      #bf #rtf (#a:Type) (then_: squash guard -> action invf disjf lf bf rtf a)
      (#invg:slice_inv) #disjg (#lg:eloc) #bg #rtg
      (else_: squash (not guard) -> action invg disjg lg bg rtg a)
= fun ctxt error_handler_fn input input_length pos posf ->
    if guard 
    then then_ () ctxt error_handler_fn input input_length pos posf
    else else_ () ctxt error_handler_fn input input_length pos posf

noextract
inline_for_extraction
let action_abort
= fun _ _ _ _ _ _ -> false

noextract
inline_for_extraction
let action_field_pos_64
= fun _ _ _ _ pos _ -> pos

(* FIXME: this is now unsound in general (only valid for flat buffer)
noextract
inline_for_extraction
let action_field_ptr
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none true LPL.puint8
   = fun input startPosition _ ->
       let open LowParse.Slice in
       LPL.offset input (LPL.uint64_to_uint32 startPosition)
*)
module T = FStar.Tactics
let ptr_inv_elim (x:B.pointer 'a)
: Lemma
  (ensures forall h. ptr_inv x h ==> B.live h x)
= introduce forall h. ptr_inv x h ==> B.live h x
       with assert (ptr_inv x h ==> B.live h x)
                by (T.norm [delta])

noextract
inline_for_extraction
let action_deref
      (#a:_) (x:B.pointer a)
= fun _ _ _ _ _ _ -> 
    ptr_inv_elim x;
    !*x

noextract
inline_for_extraction
let action_assignment
      (#a:_) (x:B.pointer a) (v:a)
= fun _ _ _ _ _ _ ->
    ptr_inv_elim x;
    x *= v

noextract
inline_for_extraction
let action_weaken #inv #disj #l #b #a act #inv' #disj' #l' = act

let external_action t l =
  unit -> Stack t (fun _ -> True) (fun h0 _ h1 -> B.modifies l h0 h1)

noextract
inline_for_extraction
let mk_external_action  #_ f = fun _ _ _ _ _ _ -> f ()
  
let copy_buffer_inv (x:CP.copy_buffer_t)
: slice_inv
= CP.properties x;
  F.on HS.mem #prop (CP.inv x)
let copy_buffer_loc (x:CP.copy_buffer_t)
: eloc
= CP.loc_of x

inline_for_extraction
noextract
let init_and_probe 
      (init:PA.init_probe_dest_t)
      (prep_dest_sz:U64.t)
      (probe:PA.probe_m unit true)
: PA.probe_m unit false
= PA.seq_probe_m () (PA.init_probe_m init prep_dest_sz) probe

inline_for_extraction
noextract
let probe_then_validate 
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#inv:slice_inv)
      (#disj:_)
      (#l:eloc)
      (#ha #allow_reading:bool)
      (#ptr_t:Type0)
      (typename:string)
      (fieldname:string)
      (v:validate_with_action_t p inv disj l ha allow_reading)
      (src:ptr_t)
      (as_u64:ptr_t -> PA.pure_external_action U64.t)
      (nullable:bool)
      (dest:CP.copy_buffer_t)
      (init:PA.init_probe_dest_t)
      (prep_dest_sz:U64.t)
      (probe:PA.probe_m unit true)
  = fun ctxt error_handler_fn input input_length pos posf ->
      CP.properties dest;
      let h0 = HST.get () in
      let src64 = as_u64 src () in
      if nullable && src64 = 0uL
      then (
        //nullable pointers are accepted without probing, if they are null
        true
      )
      else (
        let b = PA.run_probe_m (init_and_probe init prep_dest_sz probe) src64 dest in
        let h1 = HST.get () in
        modifies_address_liveness_insensitive_unused_in h0 h1;
        if b <> 0uL
        then (
          let result = v ctxt error_handler_fn (CP.stream_of dest) (CP.stream_len dest) 0uL in
          not (LPE.is_error result)
        )
        else (
          error_handler_fn typename fieldname
            LPE.(error_reason_of_result validator_error_probe_failed)
            LPE.(get_validator_error_kind validator_error_probe_failed)
            ctxt input pos;
          false
        )
      )

#pop-options
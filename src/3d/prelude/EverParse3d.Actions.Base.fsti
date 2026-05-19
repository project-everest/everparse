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
module EverParse3d.Actions.Base
module Cast = FStar.Int.Cast
open EverParse3d.Prelude
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module CP = EverParse3d.CopyBuffer
module PA = EverParse3d.ProbeActions

inline_for_extraction
noextract
let is_range_okay = EverParse3d.ErrorCode.is_range_okay

[@@erasable]
val slice_inv : Type u#1
val inv_implies (inv0 inv1: slice_inv) : Tot prop
val true_inv : slice_inv
val conj_inv (i0 i1: slice_inv) : Tot slice_inv
[@@erasable]
val eloc : Type0
val eloc_union (l1 l2: eloc) : Tot eloc
val eloc_none : eloc
val eloc_includes (l1 l2: eloc) : Tot prop
val eloc_disjoint (l1 l2: eloc) : Tot prop
val inv_implies_refl (inv: slice_inv) : Tot (squash (inv `inv_implies` inv))

val inv_implies_true (inv0:slice_inv) : Tot (squash (inv0 `inv_implies` true_inv))

val inv_implies_conj (inv0 inv1 inv2: slice_inv) (h01: squash (inv0 `inv_implies` inv1)) (h02: squash (inv0 `inv_implies` inv2)) : Tot (squash (inv0 `inv_implies` (inv1 `conj_inv` inv2)))

val conj_inv_true_left_unit (inv:slice_inv) : Tot (squash (true_inv `conj_inv` inv == inv))

val conj_inv_true_right_unit (inv:slice_inv) : Tot (squash (inv `conj_inv` true_inv == inv))

val eloc_includes_none (l1:eloc) : Tot (squash (l1 `eloc_includes` eloc_none))

val eloc_includes_union (l0: eloc) (l1 l2: eloc) (h01: squash (l0 `eloc_includes` l1)) (h02: squash (l0 `eloc_includes` l2)) : Tot (squash (l0 `eloc_includes` (l1 `eloc_union` l2)))

val eloc_includes_refl (l: eloc) : Tot (squash (l `eloc_includes` l))

val eloc_union_none_left_unit (l:eloc) : Tot (squash (eloc_none `eloc_union` l == l))

val eloc_union_none_right_unit (l:eloc) : Tot (squash (l `eloc_union` eloc_none == l))

[@@erasable]
val disjointness_pre : Type u#1
val disjointness_trivial : disjointness_pre
val disjoint (l1 l2:eloc) : disjointness_pre
val conj_disjointness (d0 d1:disjointness_pre) : disjointness_pre
val imp_disjointness (d1 d2:disjointness_pre) : prop
val disjoint_none_r (l:eloc)
  : squash (disjoint l eloc_none == disjointness_trivial)
val disjoint_none_l (l:eloc)
  : squash (disjoint eloc_none l == disjointness_trivial)   
val conj_disjointness_trivial_left_unit (d:disjointness_pre)
  : squash ((disjointness_trivial `conj_disjointness` d) == d)
val conj_disjointness_trivial_right_unit (d:disjointness_pre)
  : squash ((d `conj_disjointness` disjointness_trivial) == d)
val imp_disjointness_refl (d:disjointness_pre)
  : squash (imp_disjointness d d)

val index_equations (_:unit)
  : Lemma
    (ensures (
      //true_inv left unit
      (forall (d:slice_inv).
        {:pattern (true_inv `conj_inv` d)} (true_inv `conj_inv` d) == d) /\
      //true_inv right unit
      (forall (d:slice_inv).
        {:pattern (d `conj_inv` true_inv)} (d `conj_inv` true_inv) == d) /\
      //eloc_none left unit
      (forall (l:eloc).
        {:pattern (l `eloc_union` eloc_none)} (l `eloc_union` eloc_none) == l) /\
      //eloc_none right unit
      (forall (l:eloc).
        {:pattern (eloc_none `eloc_union` l)} (eloc_none `eloc_union` l) == l) /\
      //disjoint eloc_none right trivial
      (forall (l:eloc).
        {:pattern (disjoint l eloc_none)} (disjoint l eloc_none) == disjointness_trivial) /\
      //disjoint eloc_none left trivial
      (forall (l:eloc).
        {:pattern (disjoint eloc_none l)} (disjoint eloc_none l) == disjointness_trivial) /\
      //disjointness_pre right unit
      (forall (d:disjointness_pre).
        {:pattern (conj_disjointness d disjointness_trivial)} (conj_disjointness d disjointness_trivial) == d) /\
      //disjointness_pre left unit
      (forall (d:disjointness_pre).
        {:pattern (conj_disjointness disjointness_trivial d)} (conj_disjointness disjointness_trivial d) == d) /\
      //imp_disjointness refl
      (forall (d:disjointness_pre).
        {:pattern (imp_disjointness d d)} imp_disjointness d d) /\
      //inv_implies refl
      (forall (i:slice_inv).
        {:pattern (inv_implies i i)} inv_implies i i) /\ 
      //inv_implies true_inv right trivial
      (forall (i:slice_inv).
        {:pattern (inv_implies i true_inv)} inv_implies i true_inv) /\
      //inv_implies_conj
      (forall (i0 i1 i2:slice_inv).
        {:pattern (i0 `inv_implies` (i1 `conj_inv` i2))}
        (i0 `inv_implies` i1 /\
         i0 `inv_implies` i2) ==>
        (i0 `inv_implies` (i1 `conj_inv` i2))) /\
      //eloc_includes_none
      (forall (l:eloc).
        {:pattern (l `eloc_includes` eloc_none)} l `eloc_includes` eloc_none) /\
      //eloc_includes_union
      (forall (l0 l1 l2:eloc).
        {:pattern (l0 `eloc_includes` (l1 `eloc_union` l2))}
        (l0 `eloc_includes` l1 /\
         l0 `eloc_includes` l2) ==>
        (l0 `eloc_includes` (l1 `eloc_union` l2))) /\
      //eloc_includes_refl
      (forall (l:eloc).
        {:pattern (l `eloc_includes` l)} (l `eloc_includes` l))
    ))

inline_for_extraction
noextract
val bpointer (a: Type0) : Tot Type0

val ptr_loc (#a: _) (x: bpointer a) : Tot eloc
val ptr_inv (#a: _) (x: bpointer a) : Tot slice_inv

inline_for_extraction noextract
val action
      (liveness_inv:slice_inv)
      (disj:disjointness_pre)
      (modifies_l:eloc)
      (on_success:bool)
      (always_succeeds:bool)
      (a:Type0)
      (use_error_handler:bool)
    : Type0

inline_for_extraction noextract
val validate_with_action_t
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (p:parser k t)
      (liveness_inv:slice_inv)
      (disj:disjointness_pre)
      (l:eloc)
      (has_action:bool)
      (allow_reading:bool)
      (use_error_handler:bool)
    : Type0

inline_for_extraction noextract
val validate_eta
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] inv:slice_inv)
      (#[@@@erasable] disj:disjointness_pre)
      (#[@@@erasable] l:eloc)
      (#has_action #allow_reading:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t p inv disj l has_action allow_reading use_error_handler)
: Tot (validate_with_action_t p inv disj l has_action allow_reading use_error_handler)

inline_for_extraction noextract
val act_with_comment
      (s: string)
      (#[@@@erasable] inv:slice_inv)
      (#[@@@erasable] disj:disjointness_pre)
      (#[@@@erasable] l:eloc)
      (#b #rt:_)
      (#use_error_handler:bool)
      (res:Type)
      (a: action inv disj l b rt res use_error_handler)
: Tot (action inv disj l b rt res use_error_handler)

inline_for_extraction noextract
val leaf_reader
      (#nz:bool)
      (#k: parser_kind nz WeakKindStrongPrefix)
      (#t: Type)
      (p: parser k t)
 : Type u#0

inline_for_extraction noextract
val validate_without_reading
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] inv:slice_inv)
      (#[@@@erasable] disj:disjointness_pre)
      (#[@@@erasable] l:eloc)
      (#has_action #allow_reading:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t p inv disj l has_action allow_reading use_error_handler)
: Tot (validate_with_action_t p inv disj l has_action false use_error_handler)

inline_for_extraction noextract
val validate_with_success_action
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#[@@@erasable] t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] inv1:slice_inv)
      (#[@@@erasable] disj1:disjointness_pre)
      (#[@@@erasable] l1:eloc)
      (#has_action #allow_reading:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_t p1 inv1 disj1 l1 has_action allow_reading use_error_handler)
      (#[@@@erasable] inv2:slice_inv)
      (#[@@@erasable] disj2:disjointness_pre)
      (#[@@@erasable] l2:eloc)
      (#b #rt:bool)
      (a:action inv2 disj2 l2 b rt bool use_error_handler)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (conj_disjointness disj1 disj2) (l1 `eloc_union` l2) true false use_error_handler

inline_for_extraction noextract
val validate_with_error_handler
      (typename: string)
      (fieldname: string)
      (#nz: _)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#[@@@erasable] t1: Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] inv1:slice_inv)
      (#[@@@erasable] disj:disjointness_pre)
      (#[@@@erasable] l1:eloc)
      (#has_action #ar:_)
      (#use_error_handler:bool)
      (v1:validate_with_action_t p1 inv1 disj l1 has_action ar use_error_handler)
  : validate_with_action_t p1 inv1 disj l1 has_action ar use_error_handler

inline_for_extraction noextract
val validate_ret
      (#use_error_handler:bool)
  : validate_with_action_t (parse_ret ()) true_inv disjointness_trivial eloc_none false true use_error_handler

inline_for_extraction noextract
val validate_pair
       (name1: string)
       (#nz1:_)
       (#k1:parser_kind nz1 WeakKindStrongPrefix)
       (#[@@@erasable] t1:Type)
       (#[@@@erasable] p1:parser k1 t1)
       (k1_const: bool)
       (#[@@@erasable] inv1:slice_inv)
       (#[@@@erasable] disj1:disjointness_pre)
       (#[@@@erasable] l1:eloc)
       (#has_action1 #allow_reading1:bool)
       (#use_error_handler:bool)
       (v1:validate_with_action_t p1 inv1 disj1 l1 has_action1 allow_reading1 use_error_handler)
       (#nz2:_)
       (#wk2: _)
       (#k2:parser_kind nz2 wk2)
       (#[@@@erasable] t2:Type)
       (#[@@@erasable] p2:parser k2 t2)
       (k2_const: bool)
       (#[@@@erasable] inv2:slice_inv)
       (#[@@@erasable] disj2:disjointness_pre)
       (#[@@@erasable] l2:eloc)
       (#has_action2 #allow_reading2:bool)
       (v2:validate_with_action_t p2 inv2 disj2 l2 has_action2 allow_reading2 use_error_handler)
  : validate_with_action_t
      (p1 `parse_pair` p2)
      (conj_inv inv1 inv2)
      (conj_disjointness disj1 disj2)
      (l1 `eloc_union` l2)
      (has_action1 || has_action2)
      false
      use_error_handler

inline_for_extraction noextract
val validate_dep_pair
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] inv1:slice_inv)
      (#[@@@erasable] disj1:disjointness_pre)
      (#[@@@erasable] l1:eloc)
      (#has_action1:_)
      (#use_error_handler:bool)
      (v1:validate_with_action_t p1 inv1 disj1 l1 has_action1 true use_error_handler)
      (r1: leaf_reader p1)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:t1 -> Type)
      (#[@@@erasable] p2:(x:t1 -> parser k2 (t2 x)))
      (#[@@@erasable] inv2:slice_inv)
      (#[@@@erasable] disj2:disjointness_pre)
      (#[@@@erasable] l2:eloc)
      (#has_action2 #allow_reading2:bool)
      (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 disj2 l2 has_action2 allow_reading2 use_error_handler))
  : validate_with_action_t
      (p1 `parse_dep_pair` p2)
      (conj_inv inv1 inv2)
      (conj_disjointness disj1 disj2)
      (l1 `eloc_union` l2)
      (has_action1 || has_action2)
      false
      use_error_handler

inline_for_extraction noextract
val validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] inv1:slice_inv)
      (#[@@@erasable] disj1:disjointness_pre)
      (#[@@@erasable] l1:eloc)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_t p1 inv1 disj1 l1 has_action1 true use_error_handler)
      (r1: leaf_reader p1)
      (f: t1 -> bool)
      (#[@@@erasable] inv1':slice_inv)
      (#[@@@erasable] disj1':disjointness_pre)
      (#[@@@erasable] l1':eloc)
      (#b #rt:_)
      (a:t1 -> action inv1' disj1' l1' b rt bool use_error_handler)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:refine _ f -> Type)
      (#[@@@erasable] p2:(x:refine _ f -> parser k2 (t2 x)))
      (#[@@@erasable] inv2:slice_inv)
      (#[@@@erasable] disj2:disjointness_pre)
      (#[@@@erasable] l2:eloc)
      (#has_action2 #allow_reading2:bool)
      (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 disj2 l2 has_action2 allow_reading2 use_error_handler))
  : validate_with_action_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      (conj_inv inv1 (conj_inv inv1' inv2))
      (conj_disjointness disj1 (conj_disjointness disj1' disj2))
      (l1 `eloc_union` (l1' `eloc_union` l2))
      true
      false
      use_error_handler

inline_for_extraction noextract
val validate_dep_pair_with_action
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] inv1:slice_inv)
      (#[@@@erasable] disj1:disjointness_pre)
      (#[@@@erasable] l1:eloc)
      (#has_action1:_)
      (#use_error_handler:bool)
      (v1:validate_with_action_t p1 inv1 disj1 l1 has_action1 true use_error_handler)
      (r1: leaf_reader p1)
      (#[@@@erasable] inv1':slice_inv)
      (#[@@@erasable] disj1':disjointness_pre)
      (#[@@@erasable] l1':eloc)
      (#b #rt:_)
      (a:t1 -> action inv1' disj1' l1' b rt bool use_error_handler)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:t1 -> Type)
      (#[@@@erasable] p2:(x:t1 -> parser k2 (t2 x)))
      (#[@@@erasable] inv2:slice_inv)
      (#[@@@erasable] disj2:disjointness_pre)
      (#[@@@erasable] l2:eloc)
      (#has_action2 #allow_reading2:_)
      (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 disj2 l2 has_action2 allow_reading2 use_error_handler))
  : validate_with_action_t
      (p1 `(parse_dep_pair #nz1)` p2)
      (conj_inv inv1 (conj_inv inv1' inv2))
      (conj_disjointness disj1 (conj_disjointness disj1' disj2))
      (l1 `eloc_union` (l1' `eloc_union` l2))
      true
      false
      use_error_handler

inline_for_extraction noextract
val validate_dep_pair_with_refinement
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] inv1:slice_inv)
      (#[@@@erasable] disj1:disjointness_pre)      
      (#[@@@erasable] l1:eloc)
      (#has_action1:_)
      (#use_error_handler:bool)
      (v1:validate_with_action_t p1 inv1 disj1 l1 has_action1 true use_error_handler)
      (r1: leaf_reader p1)
      (f: t1 -> bool)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:refine _ f -> Type)
      (#[@@@erasable] p2:(x:refine _ f -> parser k2 (t2 x)))
      (#[@@@erasable] inv2:slice_inv)
      (#[@@@erasable] disj2:disjointness_pre)
      (#[@@@erasable] l2:eloc)
      (#allow_reading2:bool)
      (#has_action2:_)
      (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 disj2 l2 has_action2 allow_reading2 use_error_handler))
  : validate_with_action_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      (conj_inv inv1 inv2)
      (conj_disjointness disj1 disj2)
      (l1 `eloc_union` l2)
      (has_action1 || has_action2)
      false
      use_error_handler

inline_for_extraction noextract
val validate_filter
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t p inv disj l has_action true use_error_handler)
       (r:leaf_reader p)
       (f:t -> bool)
       (cr:string)
       (cf:string)
  : validate_with_action_t (p `parse_filter` f) inv disj l has_action false use_error_handler

inline_for_extraction noextract
val validate_filter_with_action
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t p inv disj l has_action true use_error_handler)
       (r:leaf_reader p)
       (f:t -> bool)
       (cr:string)
       (cf:string)
       (#b #rt:bool)
       (#[@@@erasable] inva:slice_inv)
       (#[@@@erasable] disja:disjointness_pre)                   
       (#[@@@erasable] la:eloc)
       (a: t -> action inva disja la b rt bool use_error_handler)
  : validate_with_action_t #nz
      (p `parse_filter` f)
      (conj_inv inv inva)
      (conj_disjointness disj disja)
      (eloc_union l la)
      true
      false
      use_error_handler

inline_for_extraction noextract
val validate_with_dep_action
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t p inv disj l has_action true use_error_handler)
       (r:leaf_reader p)
       (#b #rt:bool)
       (#[@@@erasable] inva:slice_inv)
       (#[@@@erasable] disja:disjointness_pre)                   
       (#[@@@erasable] la:eloc)
       (a: t -> action inva disja la b rt bool use_error_handler)
  : validate_with_action_t #nz
      p
      (conj_inv inv inva)
      (conj_disjointness disj disja)
      (eloc_union l la)
      true
      false
      use_error_handler

inline_for_extraction noextract
val validate_weaken_left
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#allow_reading:bool)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t p inv disj l has_action allow_reading use_error_handler)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_t (parse_weaken_left p k') inv disj l has_action allow_reading use_error_handler

inline_for_extraction noextract
val validate_weaken_right
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#allow_reading:bool)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t p inv disj l has_action allow_reading use_error_handler)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_t (parse_weaken_right p k') inv disj l has_action allow_reading use_error_handler

inline_for_extraction noextract
val validate_impos
       (#use_error_handler:bool)
       (_:unit)
  : validate_with_action_t (parse_impos ()) true_inv disjointness_trivial eloc_none false true use_error_handler

noextract inline_for_extraction
val validate_ite
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (e:bool)
       (#[@@@erasable] a:squash e -> Type)
       (#[@@@erasable] b:squash (not e) -> Type)
       (#[@@@erasable] inv1:slice_inv)
       (#[@@@erasable] disj1:disjointness_pre)
       (#[@@@erasable] l1:eloc)
       (#ha1 #ar1:_)
       (#[@@@erasable] inv2:slice_inv)
       (#[@@@erasable] disj2:disjointness_pre)
       (#[@@@erasable] l2:eloc)
       (#ha2 #ar2:_)
       (#use_error_handler:bool)
       ([@@@erasable] p1:squash e -> parser k (a()))
       (v1:(squash e -> validate_with_action_t (p1()) inv1 disj1 l1 ha1 ar1 use_error_handler))
       ([@@@erasable] p2:squash (not e) -> parser k (b()))
       (v2:(squash (not e) -> validate_with_action_t (p2()) inv2 disj2 l2 ha2 ar2 use_error_handler))
  : validate_with_action_t
      (parse_ite e p1 p2)
      (conj_inv inv1 inv2)
      (conj_disjointness disj1 disj2)
      (l1 `eloc_union` l2)
      (ha1 || ha2)
      false
      use_error_handler

noextract inline_for_extraction
val validate_nlist
       (n:U32.t)
       (n_is_const:option nat { memoizes_n_as_const n_is_const n})
       (#wk: _)
       (#k:parser_kind true wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#ha #allow_reading:bool)
       (#use_error_handler:bool)
       (v: validate_with_action_t p inv disj l ha allow_reading use_error_handler)
: validate_with_action_t (parse_nlist n n_is_const p) inv disj l ha false use_error_handler

noextract inline_for_extraction
val validate_nlist_constant_size_without_actions
       (n:U32.t)
       (n_is_const: option nat { memoizes_n_as_const n_is_const n })
       (payload_is_constant_size:bool)
       (#wk: _)
       (#k:parser_kind true wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#allow_reading:bool)
       (#use_error_handler:bool)
       (v: validate_with_action_t p inv disj l false allow_reading use_error_handler)
: Tot (validate_with_action_t (parse_nlist n n_is_const p) inv disj l false false use_error_handler)

noextract inline_for_extraction
val validate_t_at_most
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#ha #ar:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t p inv disj l ha ar use_error_handler)
  : Tot (validate_with_action_t (parse_t_at_most n p) inv disj l ha false use_error_handler)

noextract inline_for_extraction
val validate_t_exact
       (n:U32.t)
       (#nz:bool)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#ha #ar:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t p inv disj l ha ar use_error_handler)
  : Tot (validate_with_action_t (parse_t_exact n p) inv disj l ha false use_error_handler)

inline_for_extraction noextract
val validate_with_comment
       (c:string)
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#ha #allow_reading:bool)
       (#use_error_handler:bool)
       (v:validate_with_action_t p inv disj l ha allow_reading use_error_handler)
  : validate_with_action_t p inv disj l ha allow_reading use_error_handler

inline_for_extraction noextract
val validate_weaken_inv_loc
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] inv:slice_inv)
       (#[@@@erasable] disj:disjointness_pre)                   
       (#[@@@erasable] l:eloc)
       (#ha #allow_reading:bool)
       (#use_error_handler:bool)
       ([@@@erasable] inv':slice_inv{inv' `inv_implies` inv})
       ([@@@erasable] disj':disjointness_pre { disj' `imp_disjointness` disj })
       ([@@@erasable] l':eloc{l' `eloc_includes` l})
       (v:validate_with_action_t p inv disj l ha allow_reading use_error_handler)
  : Tot (validate_with_action_t p inv' disj' l' ha allow_reading use_error_handler)

inline_for_extraction noextract
val read_filter
       (#nz:_)
       (#k: parser_kind nz WeakKindStrongPrefix)
       (#t: Type)
       (#[@@@erasable] p: parser k t)
       (p32: leaf_reader p)
       (f: (t -> bool))
    : leaf_reader (parse_filter p f)

inline_for_extraction noextract
val read_impos
    : leaf_reader (parse_impos())

inline_for_extraction
let validator #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t) (#use_error_handler:bool)
  = validate_with_action_t p true_inv disjointness_trivial eloc_none false true use_error_handler

inline_for_extraction
let validator_maybe_action #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t) (has_action:bool) (#use_error_handler:bool)
  = validate_with_action_t p true_inv disjointness_trivial eloc_none has_action true use_error_handler

inline_for_extraction noextract
val validate____UINT8 (#use_error_handler:bool)
  : validator parse____UINT8 #use_error_handler

inline_for_extraction noextract
val read____UINT8
  : leaf_reader parse____UINT8

inline_for_extraction noextract
val validate____UINT8BE (#use_error_handler:bool)
  : validator parse____UINT8BE #use_error_handler

inline_for_extraction noextract
val read____UINT8BE
  : leaf_reader parse____UINT8BE

inline_for_extraction noextract
val validate____UINT16BE (#use_error_handler:bool)
  : validator parse____UINT16BE #use_error_handler

inline_for_extraction noextract
val read____UINT16BE
  : leaf_reader parse____UINT16BE

inline_for_extraction noextract
val validate____UINT32BE (#use_error_handler:bool)
  : validator parse____UINT32BE #use_error_handler

inline_for_extraction noextract
val read____UINT32BE
  : leaf_reader parse____UINT32BE

inline_for_extraction noextract
val validate____UINT64BE (#use_error_handler:bool)
  : validator parse____UINT64BE #use_error_handler

inline_for_extraction noextract
val read____UINT64BE
  : leaf_reader parse____UINT64BE

inline_for_extraction noextract
val validate____UINT16 (#use_error_handler:bool)
  : validator parse____UINT16 #use_error_handler

inline_for_extraction noextract
val read____UINT16
  : leaf_reader parse____UINT16

inline_for_extraction noextract
val validate____UINT32 (#use_error_handler:bool)
  : validator parse____UINT32 #use_error_handler

inline_for_extraction noextract
val read____UINT32
  : leaf_reader parse____UINT32

inline_for_extraction noextract
val validate____UINT64 (#use_error_handler:bool)
  : validator parse____UINT64 #use_error_handler

inline_for_extraction noextract
val read____UINT64
  : leaf_reader parse____UINT64

inline_for_extraction noextract
val validate_unit (#use_error_handler:bool)
  : validator parse_unit #use_error_handler

inline_for_extraction noextract
val read_unit
  : leaf_reader (parse_ret ())

inline_for_extraction noextract
val validate_unit_refinement (f:unit -> bool) (cf:string) (#use_error_handler:bool)
  : validator (parse_unit `parse_filter` f) #use_error_handler

inline_for_extraction noextract
val validate_string
       (#k: parser_kind true WeakKindStrongPrefix)
       (#t: eqtype)
       (#[@@@erasable] p: parser k t)
       (#ha:_)
       (#use_error_handler:bool)
       (v: validator_maybe_action p ha #use_error_handler)
       (r: leaf_reader p)
       (terminator: t)
  : Tot (validate_with_action_t (parse_string p terminator) true_inv disjointness_trivial eloc_none ha false use_error_handler)

inline_for_extraction noextract
val validate_all_bytes (#use_error_handler:bool)
  : validate_with_action_t parse_all_bytes true_inv disjointness_trivial eloc_none false false use_error_handler // could be true

inline_for_extraction noextract
val validate_all_zeros (#use_error_handler:bool)
  : validate_with_action_t parse_all_zeros true_inv disjointness_trivial eloc_none false false use_error_handler

////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
val action_return
      (#a:Type)
      (x:a)
      (#use_error_handler:bool)
  : action true_inv disjointness_trivial eloc_none false false a use_error_handler

noextract
inline_for_extraction
val action_return_true (#use_error_handler:bool)
  : action true_inv disjointness_trivial eloc_none false true bool use_error_handler

noextract
inline_for_extraction
val action_bind
      (name: string)
      (#[@@@erasable] invf:slice_inv)
      (#[@@@erasable] disjf:disjointness_pre)
      (#[@@@erasable] lf:eloc)
      (#bf #rtf:_)
      (#a:Type)
      (#use_error_handler:bool)
      (f: action invf disjf lf bf rtf a use_error_handler)
      (#[@@@erasable] invg:slice_inv)
      (#[@@@erasable] disjg:disjointness_pre)
      (#[@@@erasable] lg:eloc)
      (#bg #rt:_)
      (#b:Type)
      (g: (a -> action invg disjg lg bg rt b use_error_handler))
  : action
      (conj_inv invf invg)
      (conj_disjointness disjf disjg)
      (eloc_union lf lg)
      (bf || bg)
      rt
      b
      use_error_handler

noextract
inline_for_extraction
val action_seq
      (#[@@@erasable] invf:slice_inv)
      (#[@@@erasable] disjf:disjointness_pre)
      (#[@@@erasable] lf:eloc)
      (#bf #rtf:_)
      (#a:Type)
      (#use_error_handler:bool)
      (f: action invf disjf lf bf rtf a use_error_handler)
      (#[@@@erasable] invg:slice_inv)
      (#[@@@erasable] disjg:disjointness_pre)
      (#[@@@erasable] lg:eloc)
      (#bg #rtg:_)
      (#b:Type)
      (g: action invg disjg lg bg rtg b use_error_handler)
  : action
      (conj_inv invf invg)
      (conj_disjointness disjf disjg)
      (eloc_union lf lg)
      (bf || bg)
      rtg
      b
      use_error_handler

noextract
inline_for_extraction
val action_ite
      (#[@@@erasable] invf:slice_inv)
      (#[@@@erasable] disjf:disjointness_pre)
      (#[@@@erasable] lf:eloc)
      (guard:bool)
      (#bf #rtf:_)
      (#a:Type)
      (#use_error_handler:bool)
      (then_: squash guard -> action invf disjf lf bf rtf a use_error_handler)
      (#[@@@erasable] invg:slice_inv)
      (#[@@@erasable] disjg:disjointness_pre)
      (#[@@@erasable] lg:eloc)
      (#bg #rtg:_)
      (else_: squash (not guard) -> action invg disjg lg bg rtg a use_error_handler)
  : action
      (conj_inv invf invg)
      (conj_disjointness disjf disjg)
      (eloc_union lf lg)
      (bf || bg)
      (rtf && rtg)
      a
      use_error_handler

noextract
inline_for_extraction
val action_abort (#use_error_handler:bool)
  : action true_inv disjointness_trivial eloc_none false false bool use_error_handler

noextract
inline_for_extraction
val action_field_pos_64 (#use_error_handler:bool)
   : action true_inv disjointness_trivial eloc_none false false U64.t use_error_handler

noextract
inline_for_extraction
val action_deref
      (#a:_)
      (x:bpointer a)
      (#use_error_handler:bool)
   : action (ptr_inv x) disjointness_trivial eloc_none false false a use_error_handler

noextract
inline_for_extraction
val action_assignment
      (#a:_)
      (x:bpointer a)
      (v:a)
      (#use_error_handler:bool)
   : action (ptr_inv x) disjointness_trivial (ptr_loc x) false false unit use_error_handler

noextract
inline_for_extraction
val action_weaken
      (#[@@@erasable] inv:slice_inv)
      (#[@@@erasable] disj:disjointness_pre)
      (#[@@@erasable] l:eloc)
      (#b #rt:_)
      (#a:_)
      (#use_error_handler:bool)
      (act:action inv disj l b rt a use_error_handler)
      (#[@@@erasable] inv':slice_inv{inv' `inv_implies` inv})
      (#[@@@erasable] disj':disjointness_pre { disj' `imp_disjointness` disj })
      (#l':eloc{l' `eloc_includes` l})
   : action inv' disj' l' b rt a use_error_handler

inline_for_extraction
noextract
val external_action (t: Type0) (l: eloc) : Tot Type0

noextract
inline_for_extraction
val mk_external_action
  (#t: Type)
  (#l:eloc) ($f: external_action t l)
  (#use_error_handler:bool)
  : action true_inv disjointness_trivial l false false t use_error_handler

val copy_buffer_inv (x:CP.copy_buffer_t) : slice_inv
val copy_buffer_loc (x:CP.copy_buffer_t) : eloc


inline_for_extraction
noextract
val probe_then_validate
      (#nz:bool)
      (#maybe_zero_offset:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#inv:slice_inv)
      (#disj:disjointness_pre)
      (#l:eloc)
      (#ha #allow_reading:bool)
      (#ptr_t:Type0)
      (#use_error_handler:bool)
      (typename:string)
      (fieldname:string)
      (v:validate_with_action_t p inv disj l ha allow_reading use_error_handler)
      (src:ptr_t)
      (as_u64: ptr_t -> PA.pure_external_action U64.t)
      (nullable:bool)
      (dest:CP.copy_buffer_t)
      (init:PA.init_probe_dest_t)
      (prep_dest_sz:U64.t)
      (probe:PA.probe_m unit true maybe_zero_offset)
  : action (conj_inv inv (copy_buffer_inv dest))
           (conj_disjointness disj (disjoint (copy_buffer_loc dest) l))
           (eloc_union l (copy_buffer_loc dest)) 
           true
           false
           bool
           use_error_handler

// Some actions are valid only for specific backends (buffer, extern, etc.)

[@@erasable]
noeq
type backend_flag_t =
| BackendFlagBuffer
| BackendFlagExtern

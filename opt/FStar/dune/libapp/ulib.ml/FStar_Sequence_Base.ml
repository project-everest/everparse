open Prims
type 'ty seq = 'ty Prims.list
let length (uu___ : 'ty seq) : Prims.nat=
  (Obj.magic FStar_List_Tot_Base.length) uu___
let empty (uu___ : unit) : 'ty seq= (fun uu___ -> Obj.magic []) uu___
let singleton (uu___ : 'ty) : 'ty seq= (fun v -> Obj.magic [v]) uu___
let index (s : 'ty seq) (i : Prims.nat) : 'ty=
  FStar_List_Tot_Base.index (Obj.magic s) i
let op_Dollar_At (uu___ : unit) : 'uuuuu seq -> Prims.nat -> 'uuuuu= index
let build (uu___1 : 'ty seq) (uu___ : 'ty) : 'ty seq=
  (fun s v -> Obj.magic (FStar_List_Tot_Base.append (Obj.magic s) [v]))
    uu___1 uu___
let op_Dollar_Colon_Colon (uu___ : unit) :
  'uuuuu seq -> 'uuuuu -> 'uuuuu seq= build
let append (uu___1 : 'ty seq) (uu___ : 'ty seq) : 'ty seq=
  (Obj.magic FStar_List_Tot_Base.append) uu___1 uu___
let op_Dollar_Plus (uu___ : unit) : 'uuuuu seq -> 'uuuuu seq -> 'uuuuu seq=
  append
let update (s : 'ty seq) (i : Prims.nat) (v : 'ty) : 'ty seq=
  let uu___ = FStar_List_Tot_Base.split3 (Obj.magic s) i in
  match uu___ with
  | (s1, uu___1, s2) ->
      append (Obj.magic s1) (append (Obj.magic [v]) (Obj.magic s2))
type ('ty, 's, 'v) contains = Obj.t
let take (uu___1 : 'ty seq) (uu___ : Prims.nat) : 'ty seq=
  (fun s howMany ->
     let uu___ = FStar_List_Tot_Base.splitAt howMany (Obj.magic s) in
     match uu___ with | (result, uu___1) -> Obj.magic result) uu___1 uu___
let drop (uu___1 : 'ty seq) (uu___ : Prims.nat) : 'ty seq=
  (fun s howMany ->
     let uu___ = FStar_List_Tot_Base.splitAt howMany (Obj.magic s) in
     match uu___ with | (uu___1, result) -> Obj.magic result) uu___1 uu___
type ('ty, 's0, 's1) equal = unit
type ('uuuuu, 's0, 's1) op_Dollar_Equals_Equals = unit
type ('ty, 's0, 's1) is_prefix = unit
type ('uuuuu, 's0, 's1) op_Dollar_Less_Equals = unit
let rank (v : 'ty) : 'ty= v
type length_of_empty_is_zero_fact = unit
type length_zero_implies_empty_fact = unit
type singleton_length_one_fact = unit
type build_increments_length_fact = unit
type 'uuuuu index_into_build_fact = unit
type append_sums_lengths_fact = unit
type 'uuuuu index_into_singleton_fact = unit
type 'uuuuu index_after_append_fact = unit
type update_maintains_length_fact = unit
type update_then_index_fact = unit
type contains_iff_exists_index_fact = unit
type empty_doesnt_contain_anything_fact = unit
type build_contains_equiv_fact = unit
type take_contains_equiv_exists_fact = unit
type drop_contains_equiv_exists_fact = unit
type equal_def_fact = unit
type extensionality_fact = unit
type is_prefix_def_fact = unit
type take_length_fact = unit
type 'uuuuu index_into_take_fact = unit
type drop_length_fact = unit
type 'uuuuu index_into_drop_fact = unit
type 'uuuuu drop_index_offset_fact = unit
type 'uuuuu append_then_take_or_drop_fact = unit
type 'uuuuu take_commutes_with_in_range_update_fact = unit
type 'uuuuu take_ignores_out_of_range_update_fact = unit
type 'uuuuu drop_commutes_with_in_range_update_fact = unit
type 'uuuuu drop_ignores_out_of_range_update_fact = unit
type 'uuuuu drop_commutes_with_build_fact = unit
type rank_def_fact = unit
type element_ranks_less_fact = unit
type drop_ranks_less_fact = unit
type take_ranks_less_fact = unit
type append_take_drop_ranks_less_fact = unit
type drop_zero_fact = unit
type take_zero_fact = unit
type 'uuuuu drop_then_drop_fact = unit
type all_seq_facts = unit

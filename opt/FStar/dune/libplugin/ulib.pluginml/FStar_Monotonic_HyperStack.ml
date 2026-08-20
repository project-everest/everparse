open Fstarcompiler
open Prims
let is_in (r : unit) (h : FStar_Monotonic_HyperHeap.hmap) : Prims.bool=
  FStar_Map.contains h ()
let is_heap_color (c : Prims.int) : Prims.bool= c <= Prims.int_zero
type sid = unit
type 'm map_invariant_predicate = unit
type 'h downward_closed_predicate = unit
type ('tip, 'h) tip_top_predicate = unit
type ('h, 'n) rid_ctr_pred_predicate = unit
type 'm map_invariant = unit
type 'h downward_closed = unit
type ('tip, 'h) tip_top = unit
type ('h, 'n) rid_ctr_pred = unit
type ('tip, 'h) is_tip = unit
type ('h, 'ctr, 'tip) is_wf_with_ctr_and_tip = unit
type mem' =
  | HS of Prims.int * FStar_Monotonic_HyperHeap.hmap * unit 
let uu___is_HS (projectee : mem') : Prims.bool= true
let __proj__HS__item__rid_ctr (projectee : mem') : Prims.int=
  match projectee with | HS (rid_ctr, h, tip) -> rid_ctr
let __proj__HS__item__h (projectee : mem') : FStar_Monotonic_HyperHeap.hmap=
  match projectee with | HS (rid_ctr, h, tip) -> h

let mk_mem (rid_ctr : Prims.int) (h : FStar_Monotonic_HyperHeap.hmap)
  (tip : unit) : mem'= HS (rid_ctr, h, ())
let get_hmap (m : mem') : FStar_Monotonic_HyperHeap.hmap=
  __proj__HS__item__h m
let get_rid_ctr (m : mem') : Prims.int= __proj__HS__item__rid_ctr m

type mem = mem'
let empty_mem : mem=
  let empty_map =
    FStar_Map.restrict (FStar_Set.empty ())
      (FStar_Map.const FStar_Monotonic_Heap.emp) in
  let h = FStar_Map.upd empty_map () FStar_Monotonic_Heap.emp in
  mk_mem Prims.int_one h ()
type 'm poppable = unit
let remove_elt (s : 'a FStar_Set.set) (x : 'a) : 'a FStar_Set.set=
  FStar_Set.intersect s (FStar_Set.complement (FStar_Set.singleton x))
type ('m0, 'm1) popped = unit
let pop (m0 : mem) : mem=
  let uu___ = ((get_hmap m0), (), (get_rid_ctr m0)) in
  match uu___ with
  | (h0, tip0, rid_ctr0) ->
      let dom = remove_elt (FStar_Map.domain h0) () in
      let h1 = FStar_Map.restrict dom h0 in mk_mem rid_ctr0 h1 ()
type ('a, 'rel) mreference' =
  | MkRef of unit * ('a, 'rel) FStar_Monotonic_Heap.mref 
let uu___is_MkRef (projectee : ('a, 'rel) mreference') : Prims.bool= true

let __proj__MkRef__item__ref (projectee : ('a, 'rel) mreference') :
  ('a, 'rel) FStar_Monotonic_Heap.mref=
  match projectee with | MkRef (frame, ref) -> ref
type ('a, 'rel) mreference = ('a, 'rel) mreference'

let mk_mreference (id : unit) (r : ('a, 'rel) FStar_Monotonic_Heap.mref) :
  ('a, 'rel) mreference= MkRef ((), r)
let as_ref (x : ('uuuuu, 'uuuuu1) mreference) :
  ('uuuuu, 'uuuuu1) FStar_Monotonic_Heap.mref= __proj__MkRef__item__ref x
type ('a, 'rel) mstackref = ('a, 'rel) mreference
type ('a, 'rel) mref = ('a, 'rel) mreference
type ('a, 'rel) mmmstackref = ('a, 'rel) mreference
type ('a, 'rel) mmmref = ('a, 'rel) mreference
type ('i, 'a, 'rel) s_mref = ('a, 'rel) mreference
let live_region (m : mem) (i : unit) : Prims.bool=
  FStar_Map.contains (get_hmap m) ()
type ('a, 'rel, 'm, 's) contains = unit
type ('a, 'rel, 'r, 'm) unused_in = unit
type ('a, 'rel, 'm, 'r) contains_ref_in_its_region =
  ('a, 'rel, Obj.t, Obj.t) FStar_Monotonic_Heap.contains
type ('a, 'rel, 'r, 'm0, 'm1) fresh_ref = unit
type ('i, 'm0, 'm1) fresh_region = unit
let alloc (id : unit) (init : 'a) (mm : Prims.bool) (m : mem) :
  (('a, 'rel) mreference * mem)=
  let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
  match uu___ with
  | (h, rid_ctr, tip) ->
      let uu___1 = FStar_Monotonic_Heap.alloc (FStar_Map.sel h ()) init mm in
      (match uu___1 with
       | (r, id_h) ->
           let h1 = FStar_Map.upd h () id_h in
           ((mk_mreference () r), (mk_mem rid_ctr h1 ())))
let free (r : ('a, 'rel) mreference) (m : mem) : mem=
  let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
  match uu___ with
  | (h, rid_ctr, tip) ->
      let i_h = FStar_Map.sel h () in
      let i_h1 = FStar_Monotonic_Heap.free_mm i_h (as_ref r) in
      let h1 = FStar_Map.upd h () i_h1 in mk_mem rid_ctr h1 ()
let upd_tot (m : mem) (r : ('a, 'rel) mreference) (v : 'a) : mem=
  let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
  match uu___ with
  | (h, rid_ctr, tip) ->
      let i_h = FStar_Map.sel h () in
      let i_h1 = FStar_Monotonic_Heap.upd_tot i_h (as_ref r) v in
      let h1 = FStar_Map.upd h () i_h1 in mk_mem rid_ctr h1 ()
let sel_tot (m : mem) (r : ('a, 'rel) mreference) : 'a=
  FStar_Monotonic_Heap.sel_tot (FStar_Map.sel (get_hmap m) ()) (as_ref r)
type ('m0, 'm1) fresh_frame = unit
let hs_push_frame (m : mem) : mem=
  let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
  match uu___ with
  | (h, rid_ctr, tip) ->
      let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp in
      mk_mem (rid_ctr + Prims.int_one) h1 ()
let new_eternal_region (m : mem) (parent : unit)
  (c : Prims.int FStar_Pervasives_Native.option) : (unit * mem)=
  let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
  match uu___ with
  | (h, rid_ctr, tip) ->
      let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp in
      ((), (mk_mem (rid_ctr + Prims.int_one) h1 ()))
let new_freeable_heap_region (m : mem) (parent : unit) : (unit * mem)=
  let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
  match uu___ with
  | (h, rid_ctr, tip) ->
      let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp in
      ((), (mk_mem (rid_ctr + Prims.int_one) h1 ()))
let free_heap_region (m0 : mem) (r : unit) : mem=
  let uu___ = ((get_hmap m0), (get_rid_ctr m0)) in
  match uu___ with
  | (h0, rid_ctr0) ->
      let dom = remove_elt (FStar_Map.domain h0) () in
      let h1 = FStar_Map.restrict dom h0 in mk_mem (get_rid_ctr m0) h1 ()
type ('s, 'm0, 'm1) modifies = unit
type ('s, 'm0, 'm1) modifies_transitively = unit
type 'm0 heap_only = unit
let top_frame (m : mem) : FStar_Monotonic_Heap.heap=
  FStar_Map.sel (get_hmap m) ()
type ('id, 'h0, 'h1) modifies_one = unit
type ('id, 's, 'h0, 'h1) modifies_ref = unit
type some_ref =
  | Ref of unit * unit * (Obj.t, Obj.t) mreference 
let uu___is_Ref (projectee : some_ref) : Prims.bool= true
let __proj__Ref__item___2 (projectee : some_ref) : (Obj.t, Obj.t) mreference=
  match projectee with | Ref (a, rel, _2) -> _2
type some_refs = some_ref Prims.list
let rec regions_of_some_refs (rs : some_refs) : unit FStar_Set.set=
  match rs with
  | [] -> FStar_Set.empty ()
  | (Ref (uu___, uu___1, r))::tl ->
      FStar_Set.union (FStar_Set.singleton ()) (regions_of_some_refs tl)
type ('i, 'rs, 'h0, 'h1) modifies_some_refs = Obj.t
let norm_steps : Fstarcompiler.FStarC_NormSteps.norm_step Prims.list=
  [Fstarcompiler.FStarC_NormSteps.iota;
  Fstarcompiler.FStarC_NormSteps.zeta;
  Fstarcompiler.FStarC_NormSteps.delta;
  Fstarcompiler.FStarC_NormSteps.delta_only
    ["FStar.Monotonic.HyperStack.regions_of_some_refs";
    "FStar.Monotonic.HyperStack.refs_in_region";
    "FStar.Monotonic.HyperStack.modifies_some_refs"];
  Fstarcompiler.FStarC_NormSteps.primops]
type ('rs, 'h0, 'h1) mods = unit
type aref =
  | ARef of unit * FStar_Monotonic_Heap.aref 
let uu___is_ARef (projectee : aref) : Prims.bool= true

let __proj__ARef__item__aref_aref (projectee : aref) :
  FStar_Monotonic_Heap.aref=
  match projectee with | ARef (aref_region, aref_aref) -> aref_aref
let dummy_aref : aref= ARef ((), FStar_Monotonic_Heap.dummy_aref)
let aref_of (r : ('uuuuu, 'uuuuu1) mreference) : aref=
  ARef ((), (FStar_Monotonic_Heap.aref_of (as_ref r)))
type ('a, 'h) aref_unused_in = unit
type ('h, 'a, 'v, 'rel) aref_live_at = unit
let reference_of (h : mem) (a : aref) (v : unit) (rel : unit) :
  (Obj.t, Obj.t) mreference=
  MkRef
    ((),
      (FStar_Monotonic_Heap.ref_of (FStar_Map.sel (__proj__HS__item__h h) ())
         (__proj__ARef__item__aref_aref a) () ()))

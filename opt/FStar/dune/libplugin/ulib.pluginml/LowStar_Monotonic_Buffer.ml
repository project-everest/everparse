open Fstarcompiler
open Prims
type 'a srel = unit
type ('a, 'len, 'rel, 'i, 'j, 'suburel) compatible_subseq_preorder = unit
type ('a, 'len, 'pre, 'uuuuu, 'uuuuu1) srel_to_lsrel = 'pre
type ('a, 'len, 'rel, 'i, 'j, 'suburel) compatible_sub_preorder = unit
type ('a, 'rrel, 'rel) mbuffer =
  | Null 
  | Buffer of FStar_UInt32.t * (('a, Obj.t) FStar_Seq_Properties.lseq,
  ('a, Obj.t, 'rrel, unit, unit) srel_to_lsrel)
  FStar_HyperStack_ST.mreference * FStar_UInt32.t * unit 
let uu___is_Null (projectee : ('a, 'rrel, 'rel) mbuffer) : Prims.bool=
  match projectee with | Null -> true | uu___ -> false
let uu___is_Buffer (projectee : ('a, 'rrel, 'rel) mbuffer) : Prims.bool=
  match projectee with
  | Buffer (max_length, content, idx, length) -> true
  | uu___ -> false
let __proj__Buffer__item__max_length (projectee : ('a, 'rrel, 'rel) mbuffer)
  : FStar_UInt32.t=
  match projectee with
  | Buffer (max_length, content, idx, length) -> max_length
let __proj__Buffer__item__content (projectee : ('a, 'rrel, 'rel) mbuffer) :
  (('a, Obj.t) FStar_Seq_Properties.lseq,
    ('a, Obj.t, 'rrel, unit, unit) srel_to_lsrel)
    FStar_HyperStack_ST.mreference=
  match projectee with | Buffer (max_length, content, idx, length) -> content
let __proj__Buffer__item__idx (projectee : ('a, 'rrel, 'rel) mbuffer) :
  FStar_UInt32.t=
  match projectee with | Buffer (max_length, content, idx, length) -> idx
let mnull (uu___ : unit) : ('uuuuu, 'uuuuu1, 'uuuuu2) mbuffer= Null
type ('uuuuu, 'uuuuu1, 'uuuuu2, 'b, 'h) unused_in = Obj.t
type ('t, 'rrel, 'rel, 'b) buffer_compatible = Obj.t
type ('uuuuu, 'rrel, 'rel, 'h, 'b) live = Obj.t

type ('a, 'rrel, 'rel, 'b, 'i, 'len, 'suburel) compatible_sub = unit
type ubuffer_ =
  {
  b_max_length: Prims.nat ;
  b_offset: Prims.nat ;
  b_length: Prims.nat ;
  b_is_mm: Prims.bool }
let __proj__Mkubuffer___item__b_max_length (projectee : ubuffer_) :
  Prims.nat=
  match projectee with
  | { b_max_length; b_offset; b_length; b_is_mm;_} -> b_max_length
let __proj__Mkubuffer___item__b_offset (projectee : ubuffer_) : Prims.nat=
  match projectee with
  | { b_max_length; b_offset; b_length; b_is_mm;_} -> b_offset
let __proj__Mkubuffer___item__b_length (projectee : ubuffer_) : Prims.nat=
  match projectee with
  | { b_max_length; b_offset; b_length; b_is_mm;_} -> b_length
let __proj__Mkubuffer___item__b_is_mm (projectee : ubuffer_) : Prims.bool=
  match projectee with
  | { b_max_length; b_offset; b_length; b_is_mm;_} -> b_is_mm
type ('region, 'addr) ubuffer' = ubuffer_
type ('region, 'addr) ubuffer = unit

type ('r, 'a, 'b, 'h, 'hu) ubuffer_preserved' = unit
type ('r, 'a, 'b, 'h, 'hu) ubuffer_preserved = unit

type ('larger, 'smaller) ubuffer_includes' = unit
type ('r1, 'r2, 'a1, 'a2, 'larger, 'smaller) ubuffer_includes0 = unit
type ('r, 'a, 'larger, 'smaller) ubuffer_includes = unit
type ('x1, 'x2) ubuffer_disjoint' = Obj.t
type ('r1, 'r2, 'a1, 'a2, 'b1, 'b2) ubuffer_disjoint0 = unit
type ('r, 'a, 'b1, 'b2) ubuffer_disjoint = unit
type ('h1, 'h2) modifies_0_preserves_mreferences = unit
type ('h1, 'h2) modifies_0_preserves_regions = unit
type ('h1, 'h2) modifies_0_preserves_not_unused_in = unit
type ('h1, 'h2) modifies_0' = unit
type ('h1, 'h2) modifies_0 = unit
type ('a, 'rrel, 'rel, 'b, 'h1, 'h2) modifies_1_preserves_mreferences = unit
type ('a, 'rrel, 'rel, 'b, 'h1, 'h2) modifies_1_preserves_ubuffers = unit
type ('a, 'rrel, 'rel, 'b, 'from, 'to1, 'h1,
  'h2) modifies_1_from_to_preserves_ubuffers = unit
type ('a, 'rrel, 'rel, 'b, 'h1, 'h2) modifies_1_preserves_livenesses = unit
type ('a, 'rrel, 'rel, 'b, 'h1, 'h2) modifies_1' = unit
type ('a, 'rrel, 'rel, 'b, 'h1, 'h2) modifies_1 = unit
type ('a, 'rrel, 'rel, 'b, 'from, 'to1, 'h1, 'h2) modifies_1_from_to = Obj.t
type ('a, 'rrel, 'rel, 'b, 'h1,
  'h2) modifies_addr_of_preserves_not_unused_in = unit
type ('a, 'rrel, 'rel, 'b, 'h1, 'h2) modifies_addr_of' = unit
type ('a, 'rrel, 'rel, 'b, 'h1, 'h2) modifies_addr_of = unit
type loc = unit
type ('s1, 's2) loc_includes = unit
type ('s1, 's2) loc_disjoint = unit
type buf_t =
  (unit, unit, unit, (Obj.t, Obj.t, Obj.t) mbuffer) FStar_Pervasives.dtuple4
let buf (b : ('a, 'rrel, 'rel) mbuffer) : buf_t=
  FStar_Pervasives.Mkdtuple4 ((), (), (), (Obj.magic b))
type ('h, 'l) all_live = Obj.t
type 'l all_disjoint = Obj.t
type 'l loc_pairwise_disjoint = Obj.t
type ('s, 'h1, 'h2) modifies = unit
type ('h, 'ra) does_not_contain_addr = unit
type ('l, 'h) loc_in = unit
type ('l, 'h) loc_not_in = unit
type ('l, 'h, 'hu) fresh_loc = unit
type ('a1, 'a2, 'rrel1, 'rel1, 'rrel2, 'rel2, 'b1, 'b2) disjoint = unit
type ('a1, 'a2, 'rrel1, 'rel1, 'rrel2, 'rel2, 'b1, 'b2) includes = unit
type ('a, 'rrel, 'rel) mpointer = ('a, 'rrel, 'rel) mbuffer
type ('a, 'rrel, 'rel) mpointer_or_null = ('a, 'rrel, 'rel) mbuffer
let is_null (b : ('uuuuu, 'uuuuu1, 'uuuuu2) mbuffer) : Prims.bool=
  uu___is_Null b
let msub (b : ('a, 'rrel, 'rel) mbuffer) (i : FStar_UInt32.t) (len : unit) :
  ('a, 'rrel, 'suburel) mbuffer=
  match b with
  | Null -> Null
  | Buffer (max_len, content, i0, len0) ->
      Buffer (max_len, content, (FStar_UInt32.add i0 i), ())
let moffset (b : ('a, 'rrel, 'rel) mbuffer) (i : FStar_UInt32.t) :
  ('a, 'rrel, 'suburel) mbuffer=
  match b with
  | Null -> Null
  | Buffer (max_len, content, i0, len) ->
      Buffer (max_len, content, (FStar_UInt32.add i0 i), ())
let index (b : ('uuuuu, 'uuuuu1, 'uuuuu2) mbuffer) (i : FStar_UInt32.t) :
  'uuuuu=
  let s = FStar_HyperStack_ST.op_Bang (__proj__Buffer__item__content b) in
  FStar_Seq_Base.index s
    ((FStar_UInt32.v (__proj__Buffer__item__idx b)) + (FStar_UInt32.v i))
let upd' (b : ('uuuuu, 'uuuuu1, 'uuuuu2) mbuffer) (i : FStar_UInt32.t)
  (v : 'uuuuu) : unit=
  let h = FStar_HyperStack_ST.get () in
  let uu___ = b in
  match uu___ with
  | Buffer (max_length, content, idx, len) ->
      let s0 = FStar_HyperStack_ST.op_Bang content in
      let sb0 =
        FStar_Seq_Base.slice s0 (FStar_UInt32.v idx)
          (FStar_UInt32.v max_length) in
      let s_upd = FStar_Seq_Base.upd sb0 (FStar_UInt32.v i) v in
      let sf =
        FStar_Seq_Properties.replace_subseq s0 (FStar_UInt32.v idx)
          (FStar_UInt32.v max_length) s_upd in
      FStar_HyperStack_ST.op_Colon_Equals content sf
let upd (b : ('a, 'rrel, 'rel) mbuffer) (i : FStar_UInt32.t) (v : 'a) : 
  unit= let h = FStar_HyperStack_ST.get () in upd' b i v
type ('a, 'rrel, 'rel, 'b) recallable = unit
type ('uuuuu, 'uuuuu1, 'uuuuu2, 'b) region_lifetime_buf = unit
type ('a, 'rrel, 'rel) rrel_rel_always_compatible = unit
let recall (b : ('uuuuu, 'uuuuu1, 'uuuuu2) mbuffer) : unit=
  if uu___is_Null b
  then ()
  else FStar_HyperStack_ST.recall (__proj__Buffer__item__content b)
type 'a spred = unit
type ('a, 'p, 'rel) stable_on = unit
type ('a, 'rrel, 'rel, 'b, 'p, 'h) spred_as_mempred = unit
type ('uuuuu, 'rrel, 'rel, 'b, 'p) witnessed = Obj.t
let witness_p (b : ('a, 'rrel, 'rel) mbuffer) (p : unit) : unit=
  match b with
  | Null -> ()
  | Buffer (uu___, content, uu___1, uu___2) ->
      FStar_HyperStack_ST.witness_p content ()
let recall_p (b : ('uuuuu, 'uuuuu1, 'uuuuu2) mbuffer) (p : unit) : unit=
  match b with
  | Null -> ()
  | Buffer (uu___, content, uu___1, uu___2) ->
      FStar_HyperStack_ST.recall_p content ()
let witnessed_functorial_st (b1 : ('a, 'rrel, 'rel1) mbuffer)
  (b2 : ('a, 'rrel, 'rel2) mbuffer) (i : FStar_UInt32.t)
  (len : FStar_UInt32.t) (s1 : unit) (s2 : unit) : unit= ()
type ('a, 'rrel, 'rel, 'b) freeable = unit
let free (b : ('uuuuu, 'uuuuu1, 'uuuuu2) mbuffer) : unit=
  FStar_HyperStack_ST.rfree (__proj__Buffer__item__content b)
type ('a, 'rrel, 'rel, 'len) lmbuffer = ('a, 'rrel, 'rel) mbuffer
type ('a, 'rrel, 'rel, 'b, 'h0, 'h1, 's) alloc_post_mem_common = unit
type ('a, 'rrel, 'rel, 'len, 'r) lmbuffer_or_null = ('a, 'rrel, 'rel) mbuffer
type ('a, 'rrel, 'rel, 'b, 'h0, 'h1, 's) alloc_partial_post_mem_common = unit
type ('r, 'len) malloc_pre = unit
let alloc_heap_common (r : unit) (len : FStar_UInt32.t)
  (s : 'a FStar_Seq_Base.seq) (mm : Prims.bool) : ('a, 'rrel, 'rrel) mbuffer=
  let content =
    if mm
    then FStar_HyperStack_ST.ralloc_mm () s
    else FStar_HyperStack_ST.ralloc () s in
  let b = Buffer (len, content, Stdint.Uint32.zero, ()) in b
let mgcmalloc (r : unit) (init : 'uuuuu) (len : FStar_UInt32.t) :
  ('uuuuu, 'uuuuu1, 'uuuuu1) mbuffer=
  alloc_heap_common () len (FStar_Seq_Base.create (FStar_UInt32.v len) init)
    false
let read_sub_buffer (b : ('a, 'rrel, 'rel) mbuffer) (idx : FStar_UInt32.t)
  (len : FStar_UInt32.t) : 'a FStar_Seq_Base.seq=
  let s = FStar_HyperStack_ST.op_Bang (__proj__Buffer__item__content b) in
  let s1 =
    FStar_Seq_Base.slice s (FStar_UInt32.v (__proj__Buffer__item__idx b))
      (FStar_UInt32.v (__proj__Buffer__item__max_length b)) in
  FStar_Seq_Base.slice s1 (FStar_UInt32.v idx)
    ((FStar_UInt32.v idx) + (FStar_UInt32.v len))
let mgcmalloc_and_blit (r : unit) (uu___ : unit) (uu___1 : unit)
  (src : ('uuuuu, Obj.t, Obj.t) mbuffer) (id_src : FStar_UInt32.t)
  (len : FStar_UInt32.t) : ('uuuuu, 'uuuuu1, 'uuuuu1) mbuffer=
  let uu___2 = read_sub_buffer src id_src len in
  alloc_heap_common () len uu___2 false
let mgcmalloc_partial (r : unit) (init : 'a) (len : FStar_UInt32.t) :
  ('a, 'rrel, 'rrel) mbuffer= mgcmalloc () init len
let mmalloc (r : unit) (init : 'uuuuu) (len : FStar_UInt32.t) :
  ('uuuuu, 'uuuuu1, 'uuuuu1) mbuffer=
  alloc_heap_common () len (FStar_Seq_Base.create (FStar_UInt32.v len) init)
    true
let mmalloc_and_blit (r : unit) (uu___ : unit) (uu___1 : unit)
  (src : ('uuuuu, Obj.t, Obj.t) mbuffer) (id_src : FStar_UInt32.t)
  (len : FStar_UInt32.t) : ('uuuuu, 'uuuuu1, 'uuuuu1) mbuffer=
  let uu___2 = read_sub_buffer src id_src len in
  alloc_heap_common () len uu___2 true
let mmalloc_partial (r : unit) (init : 'a) (len : FStar_UInt32.t) :
  ('a, 'rrel, 'rrel) mbuffer= mmalloc () init len
let alloca_pre (len : FStar_UInt32.t) : Prims.bool=
  (FStar_UInt32.v len) > Prims.int_zero
let malloca (init : 'a) (len : FStar_UInt32.t) : ('a, 'rrel, 'rrel) mbuffer=
  let content =
    FStar_HyperStack_ST.salloc
      (FStar_Seq_Base.create (FStar_UInt32.v len) init) in
  Buffer (len, content, Stdint.Uint32.zero, ())
let malloca_and_blit (src : ('a, 'uuuuu, 'uuuuu1) mbuffer)
  (id_src : FStar_UInt32.t) (len : FStar_UInt32.t) :
  ('a, 'rrel, 'rrel) mbuffer=
  let content =
    let uu___ = read_sub_buffer src id_src len in
    FStar_HyperStack_ST.salloc uu___ in
  Buffer (len, content, Stdint.Uint32.zero, ())
type ('a, 'init) alloca_of_list_pre = unit
let malloca_of_list (init : 'a Prims.list) : ('a, 'rrel, 'rrel) mbuffer=
  let len = FStar_UInt32.uint_to_t (FStar_List_Tot_Base.length init) in
  let s = FStar_Seq_Base.seq_of_list init in
  let content = FStar_HyperStack_ST.salloc s in
  Buffer (len, content, Stdint.Uint32.zero, ())
type ('a, 'r, 'init) gcmalloc_of_list_pre = unit
let mgcmalloc_of_list (r : unit) (init : 'a Prims.list) :
  ('a, 'rrel, 'rrel) mbuffer=
  let len = FStar_UInt32.uint_to_t (FStar_List_Tot_Base.length init) in
  let s = FStar_Seq_Base.seq_of_list init in
  let content = FStar_HyperStack_ST.ralloc () s in
  Buffer (len, content, Stdint.Uint32.zero, ())
let mgcmalloc_of_list_partial (r : unit) (init : 'a Prims.list) :
  ('a, 'rrel, 'rrel) mbuffer= mgcmalloc_of_list () init
type ('h, 'd, 'len) alloc_drgn_pre = unit
let mmalloc_drgn (d : FStar_HyperStack_ST.drgn) (init : 'a)
  (len : FStar_UInt32.t) : ('a, 'rrel, 'rrel) mbuffer=
  let content =
    FStar_HyperStack_ST.ralloc_drgn d
      (FStar_Seq_Base.create (FStar_UInt32.v len) init) in
  Buffer (len, content, Stdint.Uint32.zero, ())
let mmalloc_drgn_mm (d : FStar_HyperStack_ST.drgn) (init : 'a)
  (len : FStar_UInt32.t) : ('a, 'rrel, 'rrel) mbuffer=
  let content =
    FStar_HyperStack_ST.ralloc_drgn_mm d
      (FStar_Seq_Base.create (FStar_UInt32.v len) init) in
  Buffer (len, content, Stdint.Uint32.zero, ())
let mmalloc_drgn_and_blit (d : FStar_HyperStack_ST.drgn)
  (src : ('a, 'uuuuu, 'uuuuu1) mbuffer) (id_src : FStar_UInt32.t)
  (len : FStar_UInt32.t) : ('a, 'rrel, 'rrel) mbuffer=
  let content =
    let uu___ = read_sub_buffer src id_src len in
    FStar_HyperStack_ST.ralloc_drgn d uu___ in
  Buffer (len, content, Stdint.Uint32.zero, ())
let blit (src : ('a, 'rrel1, 'rel1) mbuffer) (idx_src : FStar_UInt32.t)
  (dst : ('a, 'rrel2, 'rel2) mbuffer) (idx_dst : FStar_UInt32.t)
  (len : FStar_UInt32.t) : unit=
  match (src, dst) with
  | (Buffer (uu___, uu___1, uu___2, uu___3), Buffer
     (uu___4, uu___5, uu___6, uu___7)) ->
      if len = Stdint.Uint32.zero
      then ()
      else
        (let h = FStar_HyperStack_ST.get () in
         let uu___9 = src in
         match uu___9 with
         | Buffer (max_length1, content1, idx1, length1) ->
             let uu___10 = dst in
             (match uu___10 with
              | Buffer (max_length2, content2, idx2, length2) ->
                  let s_full1 = FStar_HyperStack_ST.op_Bang content1 in
                  let s_full2 = FStar_HyperStack_ST.op_Bang content2 in
                  let s1 =
                    FStar_Seq_Base.slice s_full1 (FStar_UInt32.v idx1)
                      (FStar_UInt32.v max_length1) in
                  let s2 =
                    FStar_Seq_Base.slice s_full2 (FStar_UInt32.v idx2)
                      (FStar_UInt32.v max_length2) in
                  let s_sub_src =
                    FStar_Seq_Base.slice s1 (FStar_UInt32.v idx_src)
                      ((FStar_UInt32.v idx_src) + (FStar_UInt32.v len)) in
                  let s2' =
                    FStar_Seq_Properties.replace_subseq s2
                      (FStar_UInt32.v idx_dst)
                      ((FStar_UInt32.v idx_dst) + (FStar_UInt32.v len))
                      s_sub_src in
                  let s_full2' =
                    FStar_Seq_Properties.replace_subseq s_full2
                      (FStar_UInt32.v idx2) (FStar_UInt32.v max_length2) s2' in
                  (FStar_HyperStack_ST.op_Colon_Equals content2 s_full2';
                   (let h1 = FStar_HyperStack_ST.get () in ()))))
  | (uu___, uu___1) -> ()
let fill' (b : ('t, 'rrel, 'rel) mbuffer) (z : 't) (len : FStar_UInt32.t) :
  unit=
  if len = Stdint.Uint32.zero
  then ()
  else
    (let h = FStar_HyperStack_ST.get () in
     let uu___1 = b in
     match uu___1 with
     | Buffer (max_length, content, idx, length) ->
         let s_full = FStar_HyperStack_ST.op_Bang content in
         let s =
           FStar_Seq_Base.slice s_full (FStar_UInt32.v idx)
             (FStar_UInt32.v max_length) in
         let s_src = FStar_Seq_Base.create (FStar_UInt32.v len) z in
         let s' =
           FStar_Seq_Properties.replace_subseq s Prims.int_zero
             (FStar_UInt32.v len) s_src in
         let s_full' =
           FStar_Seq_Properties.replace_subseq s_full (FStar_UInt32.v idx)
             ((FStar_UInt32.v idx) + (FStar_UInt32.v len)) s_src in
         (FStar_HyperStack_ST.op_Colon_Equals content s_full';
          (let h' = FStar_HyperStack_ST.get () in ())))
let fill (b : ('t, 'rrel, 'rel) mbuffer) (z : 't) (len : FStar_UInt32.t) :
  unit= fill' b z len
type ('region, 'addr) abuffer' = ('region, 'addr) ubuffer'
type ('region, 'addr) abuffer = unit
let coerce (uu___ : 't1) : 't2= (fun x1 -> Obj.magic x1) uu___

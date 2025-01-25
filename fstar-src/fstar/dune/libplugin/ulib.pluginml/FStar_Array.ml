open Fstarcompiler
open Prims
type 'a array = 'a FStar_Seq_Base.seq FStar_ST.ref
type ('a, 'h, 's) contains =
  ('a FStar_Seq_Base.seq, unit, unit, unit) FStar_Monotonic_Heap.contains
type ('a, 'arr, 'h) unused_in =
  ('a FStar_Seq_Base.seq, unit, unit, unit) FStar_Monotonic_Heap.unused_in
let op_At_Bar : 'a . 'a array -> 'a array -> 'a array =
  fun s1 ->
    fun s2 ->
      let s1' = FStar_Ref.op_Bang s1 in
      let s2' = FStar_Ref.op_Bang s2 in
      FStar_ST.alloc (FStar_Seq_Base.append s1' s2')
type ('a, 's, 'h0, 'x, 'h1) create_post = unit
let of_seq : 'a . 'a FStar_Seq_Base.seq -> 'a array =
  fun s -> FStar_ST.alloc s
let to_seq : 'a . 'a array -> 'a FStar_Seq_Base.seq =
  fun s -> FStar_Ref.op_Bang s
let of_list : 'a . 'a Prims.list -> 'a array =
  fun l -> of_seq (FStar_Seq_Base.seq_of_list l)
let create : 'a . Prims.nat -> 'a -> 'a array =
  fun n -> fun init -> FStar_ST.alloc (FStar_Seq_Base.create n init)
let index : 'a . 'a array -> Prims.nat -> 'a =
  fun x -> fun n -> let s = to_seq x in FStar_Seq_Base.index s n
let upd : 'a . 'a array -> Prims.nat -> 'a -> unit =
  fun x ->
    fun n ->
      fun v ->
        let s = FStar_Ref.op_Bang x in
        let s' = FStar_Seq_Base.upd s n v in FStar_Ref.op_Colon_Equals x s'
let length : 'a . 'a array -> Prims.nat =
  fun x -> let s = FStar_Ref.op_Bang x in FStar_Seq_Base.length s
let op :
  'a . ('a FStar_Seq_Base.seq -> 'a FStar_Seq_Base.seq) -> 'a array -> unit =
  fun f ->
    fun x ->
      let s = FStar_Ref.op_Bang x in
      let s' = f s in FStar_Ref.op_Colon_Equals x s'
let swap : 'a . 'a array -> Prims.nat -> Prims.nat -> unit =
  fun x ->
    fun i ->
      fun j ->
        let tmpi = index x i in
        let tmpj = index x j in upd x j tmpi; upd x i tmpj
let rec copy_aux : 'a . 'a array -> 'a array -> Prims.nat -> unit =
  fun s ->
    fun cpy ->
      fun ctr ->
        let uu___ = let uu___1 = length cpy in uu___1 - ctr in
        match uu___ with
        | uu___1 when uu___1 = Prims.int_zero -> ()
        | uu___1 ->
            ((let uu___3 = index s ctr in upd cpy ctr uu___3);
             copy_aux s cpy (ctr + Prims.int_one))
let copy : 'a . 'a array -> 'a array =
  fun s ->
    let cpy =
      let uu___ = length s in
      let uu___1 = index s Prims.int_zero in create uu___ uu___1 in
    copy_aux s cpy Prims.int_zero; cpy
let rec blit_aux :
  'a .
    'a array ->
      Prims.nat -> 'a array -> Prims.nat -> Prims.nat -> Prims.nat -> unit
  =
  fun s ->
    fun s_idx ->
      fun t ->
        fun t_idx ->
          fun len ->
            fun ctr ->
              match len - ctr with
              | uu___ when uu___ = Prims.int_zero -> ()
              | uu___ ->
                  ((let uu___2 = index s (s_idx + ctr) in
                    upd t (t_idx + ctr) uu___2);
                   blit_aux s s_idx t t_idx len (ctr + Prims.int_one))
let blit :
  'a . 'a array -> Prims.nat -> 'a array -> Prims.nat -> Prims.nat -> unit =
  fun s ->
    fun s_idx ->
      fun t ->
        fun t_idx -> fun len -> blit_aux s s_idx t t_idx len Prims.int_zero
let sub : 'a . 'a array -> Prims.nat -> Prims.nat -> 'a array =
  fun s ->
    fun idx ->
      fun len ->
        let h0 = FStar_ST.get () in
        let t = let uu___ = index s Prims.int_zero in create len uu___ in
        blit s idx t Prims.int_zero len; (let h1 = FStar_ST.get () in t)
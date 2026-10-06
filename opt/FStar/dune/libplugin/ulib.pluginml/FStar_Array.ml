open Fstarcompiler
open Prims
type 'a array = 'a FStar_Seq_Base.seq FStar_ST.ref
type ('a, 'h, 's) contains =
  ('a FStar_Seq_Base.seq, unit, 'h, Obj.t) FStar_Monotonic_Heap.contains
type ('a, 'arr, 'h) unused_in =
  ('a FStar_Seq_Base.seq, unit, Obj.t, 'h) FStar_Monotonic_Heap.unused_in
let op_At_Bar (s1 : 'a array) (s2 : 'a array) : 'a array=
  let s1' = FStar_Ref.op_Bang s1 in
  let s2' = FStar_Ref.op_Bang s2 in
  FStar_ST.alloc (FStar_Seq_Base.append s1' s2')
type ('a, 's, 'h0, 'x, 'h1) create_post = unit
let of_seq (s : 'a FStar_Seq_Base.seq) : 'a array= FStar_ST.alloc s
let to_seq (s : 'a array) : 'a FStar_Seq_Base.seq= FStar_Ref.op_Bang s
let of_list (l : 'a Prims.list) : 'a array=
  of_seq (FStar_Seq_Base.seq_of_list l)
let create (n : Prims.nat) (init : 'a) : 'a array=
  FStar_ST.alloc (FStar_Seq_Base.create n init)
let index (x : 'a array) (n : Prims.nat) : 'a=
  let s = to_seq x in FStar_Seq_Base.index s n
let upd (x : 'a array) (n : Prims.nat) (v : 'a) : unit=
  let s = FStar_Ref.op_Bang x in
  let s' = FStar_Seq_Base.upd s n v in FStar_Ref.op_Colon_Equals x s'
let length (x : 'a array) : Prims.nat=
  let s = FStar_Ref.op_Bang x in FStar_Seq_Base.length s
let op (f : 'a FStar_Seq_Base.seq -> 'a FStar_Seq_Base.seq) (x : 'a array) :
  unit=
  let s = FStar_Ref.op_Bang x in
  let s' = f s in FStar_Ref.op_Colon_Equals x s'
let swap (x : 'a array) (i : Prims.nat) (j : Prims.nat) : unit=
  let tmpi = index x i in let tmpj = index x j in upd x j tmpi; upd x i tmpj
let rec copy_aux : 'a . 'a array -> 'a array -> Prims.nat -> unit =
  fun s cpy ctr ->
    let uu___ = let uu___1 = length cpy in uu___1 - ctr in
    match uu___ with
    | uu___1 when uu___1 = Prims.int_zero -> ()
    | uu___1 ->
        ((let uu___3 = index s ctr in upd cpy ctr uu___3);
         copy_aux s cpy (ctr + Prims.int_one))
let copy (s : 'a array) : 'a array=
  let cpy =
    let uu___ = length s in
    let uu___1 = index s Prims.int_zero in create uu___ uu___1 in
  copy_aux s cpy Prims.int_zero; cpy
let rec blit_aux :
  'a .
    'a array ->
      Prims.nat -> 'a array -> Prims.nat -> Prims.nat -> Prims.nat -> unit
  =
  fun s s_idx t t_idx len ctr ->
    match len - ctr with
    | uu___ when uu___ = Prims.int_zero -> ()
    | uu___ ->
        ((let uu___2 = index s (s_idx + ctr) in upd t (t_idx + ctr) uu___2);
         blit_aux s s_idx t t_idx len (ctr + Prims.int_one))
let blit (s : 'a array) (s_idx : Prims.nat) (t : 'a array)
  (t_idx : Prims.nat) (len : Prims.nat) : unit=
  blit_aux s s_idx t t_idx len Prims.int_zero
let sub (s : 'a array) (idx : Prims.nat) (len : Prims.nat) : 'a array=
  let h0 = FStar_ST.get () in
  let t = let uu___ = index s Prims.int_zero in create len uu___ in
  blit s idx t Prims.int_zero len; (let h1 = FStar_ST.get () in t)

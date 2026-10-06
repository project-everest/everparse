open Prims
type base_typ =
  | TUInt 
  | TUInt8 
  | TUInt16 
  | TUInt32 
  | TUInt64 
  | TInt 
  | TInt8 
  | TInt16 
  | TInt32 
  | TInt64 
  | TChar 
  | TBool 
  | TUnit 
let uu___is_TUInt (projectee : base_typ) : Prims.bool=
  match projectee with | TUInt -> true | uu___ -> false
let uu___is_TUInt8 (projectee : base_typ) : Prims.bool=
  match projectee with | TUInt8 -> true | uu___ -> false
let uu___is_TUInt16 (projectee : base_typ) : Prims.bool=
  match projectee with | TUInt16 -> true | uu___ -> false
let uu___is_TUInt32 (projectee : base_typ) : Prims.bool=
  match projectee with | TUInt32 -> true | uu___ -> false
let uu___is_TUInt64 (projectee : base_typ) : Prims.bool=
  match projectee with | TUInt64 -> true | uu___ -> false
let uu___is_TInt (projectee : base_typ) : Prims.bool=
  match projectee with | TInt -> true | uu___ -> false
let uu___is_TInt8 (projectee : base_typ) : Prims.bool=
  match projectee with | TInt8 -> true | uu___ -> false
let uu___is_TInt16 (projectee : base_typ) : Prims.bool=
  match projectee with | TInt16 -> true | uu___ -> false
let uu___is_TInt32 (projectee : base_typ) : Prims.bool=
  match projectee with | TInt32 -> true | uu___ -> false
let uu___is_TInt64 (projectee : base_typ) : Prims.bool=
  match projectee with | TInt64 -> true | uu___ -> false
let uu___is_TChar (projectee : base_typ) : Prims.bool=
  match projectee with | TChar -> true | uu___ -> false
let uu___is_TBool (projectee : base_typ) : Prims.bool=
  match projectee with | TBool -> true | uu___ -> false
let uu___is_TUnit (projectee : base_typ) : Prims.bool=
  match projectee with | TUnit -> true | uu___ -> false
type array_length_t = FStar_UInt32.t
type typ =
  | TBase of base_typ 
  | TStruct of struct_typ 
  | TUnion of struct_typ 
  | TArray of array_length_t * typ 
  | TPointer of typ 
  | TNPointer of typ 
  | TBuffer of typ 
and struct_typ =
  {
  name: Prims.string ;
  fields: (Prims.string * typ) Prims.list }
let uu___is_TBase (projectee : typ) : Prims.bool=
  match projectee with | TBase b -> true | uu___ -> false
let __proj__TBase__item__b (projectee : typ) : base_typ=
  match projectee with | TBase b -> b
let uu___is_TStruct (projectee : typ) : Prims.bool=
  match projectee with | TStruct l -> true | uu___ -> false
let __proj__TStruct__item__l (projectee : typ) : struct_typ=
  match projectee with | TStruct l -> l
let uu___is_TUnion (projectee : typ) : Prims.bool=
  match projectee with | TUnion l -> true | uu___ -> false
let __proj__TUnion__item__l (projectee : typ) : struct_typ=
  match projectee with | TUnion l -> l
let uu___is_TArray (projectee : typ) : Prims.bool=
  match projectee with | TArray (length, t) -> true | uu___ -> false
let __proj__TArray__item__length (projectee : typ) : array_length_t=
  match projectee with | TArray (length, t) -> length
let __proj__TArray__item__t (projectee : typ) : typ=
  match projectee with | TArray (length, t) -> t
let uu___is_TPointer (projectee : typ) : Prims.bool=
  match projectee with | TPointer t -> true | uu___ -> false
let __proj__TPointer__item__t (projectee : typ) : typ=
  match projectee with | TPointer t -> t
let uu___is_TNPointer (projectee : typ) : Prims.bool=
  match projectee with | TNPointer t -> true | uu___ -> false
let __proj__TNPointer__item__t (projectee : typ) : typ=
  match projectee with | TNPointer t -> t
let uu___is_TBuffer (projectee : typ) : Prims.bool=
  match projectee with | TBuffer t -> true | uu___ -> false
let __proj__TBuffer__item__t (projectee : typ) : typ=
  match projectee with | TBuffer t -> t
let __proj__Mkstruct_typ__item__name (projectee : struct_typ) : Prims.string=
  match projectee with | { name; fields;_} -> name
let __proj__Mkstruct_typ__item__fields (projectee : struct_typ) :
  (Prims.string * typ) Prims.list=
  match projectee with | { name; fields;_} -> fields
type struct_typ' = (Prims.string * typ) Prims.list
type union_typ = struct_typ
type 'l struct_field' = Prims.string
type 'l struct_field = Obj.t struct_field'
type 'l union_field = 'l struct_field
let typ_of_struct_field' (l : struct_typ') (f : Obj.t struct_field') : 
  typ=
  let y =
    FStar_Pervasives_Native.__proj__Some__item__v
      (FStar_List_Tot_Base.assoc f l) in
  y
let typ_of_struct_field (l : struct_typ) (f : Obj.t struct_field) : typ=
  typ_of_struct_field' l.fields f
let typ_of_union_field (l : union_typ) (f : Obj.t union_field) : typ=
  typ_of_struct_field l f
type ('dummyV0, 'dummyV1) step =
  | StepField of struct_typ * Obj.t struct_field 
  | StepUField of union_typ * Obj.t struct_field 
  | StepCell of FStar_UInt32.t * typ * FStar_UInt32.t 
let uu___is_StepField (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : Prims.bool=
  match projectee with | StepField (l, fd) -> true | uu___ -> false
let __proj__StepField__item__l (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : struct_typ=
  match projectee with | StepField (l, fd) -> l
let __proj__StepField__item__fd (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : Obj.t struct_field=
  match projectee with | StepField (l, fd) -> fd
let uu___is_StepUField (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : Prims.bool=
  match projectee with | StepUField (l, fd) -> true | uu___ -> false
let __proj__StepUField__item__l (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : union_typ=
  match projectee with | StepUField (l, fd) -> l
let __proj__StepUField__item__fd (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : Obj.t struct_field=
  match projectee with | StepUField (l, fd) -> fd
let uu___is_StepCell (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : Prims.bool=
  match projectee with
  | StepCell (length, value, index) -> true
  | uu___ -> false
let __proj__StepCell__item__length (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : FStar_UInt32.t=
  match projectee with | StepCell (length, value, index) -> length
let __proj__StepCell__item__value (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : typ=
  match projectee with | StepCell (length, value, index) -> value
let __proj__StepCell__item__index (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) step) : FStar_UInt32.t=
  match projectee with | StepCell (length, value, index) -> index
type ('from, 'dummyV0) path =
  | PathBase 
  | PathStep of typ * typ * ('from, Obj.t) path * (Obj.t, Obj.t) step 
let uu___is_PathBase (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) path) : Prims.bool=
  match projectee with | PathBase -> true | uu___ -> false
let uu___is_PathStep (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) path) : Prims.bool=
  match projectee with
  | PathStep (through, to2, p, s) -> true
  | uu___ -> false
let __proj__PathStep__item__through (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) path) : typ=
  match projectee with | PathStep (through, to2, p, s) -> through
let __proj__PathStep__item__to (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) path) : typ=
  match projectee with | PathStep (through, to2, p, s) -> to2
let __proj__PathStep__item__p (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) path) : (Obj.t, Obj.t) path=
  match projectee with | PathStep (through, to2, p, s) -> p
let __proj__PathStep__item__s (from : typ) (to1 : typ)
  (projectee : (Obj.t, Obj.t) path) : (Obj.t, Obj.t) step=
  match projectee with | PathStep (through, to2, p, s) -> s
type 'to1 _npointer =
  | Pointer of typ * FStar_Monotonic_HyperStack.aref * (Obj.t, 'to1) path 
  | NullPtr 
let uu___is_Pointer (to1 : typ) (projectee : Obj.t _npointer) : Prims.bool=
  match projectee with | Pointer (from, contents, p) -> true | uu___ -> false
let __proj__Pointer__item__from (to1 : typ) (projectee : Obj.t _npointer) :
  typ= match projectee with | Pointer (from, contents, p) -> from
let __proj__Pointer__item__contents (to1 : typ) (projectee : Obj.t _npointer)
  : FStar_Monotonic_HyperStack.aref=
  match projectee with | Pointer (from, contents, p) -> contents
let __proj__Pointer__item__p (to1 : typ) (projectee : Obj.t _npointer) :
  (Obj.t, Obj.t) path=
  match projectee with | Pointer (from, contents, p) -> p
let uu___is_NullPtr (to1 : typ) (projectee : Obj.t _npointer) : Prims.bool=
  match projectee with | NullPtr -> true | uu___ -> false
type 't npointer = 't _npointer
let nullptr (t : typ) : Obj.t npointer= NullPtr
type 't pointer = 't npointer
type 't buffer_root =
  | BufferRootSingleton of 't pointer 
  | BufferRootArray of array_length_t * Obj.t pointer 
let uu___is_BufferRootSingleton (t : typ) (projectee : Obj.t buffer_root) :
  Prims.bool=
  match projectee with | BufferRootSingleton p -> true | uu___ -> false
let __proj__BufferRootSingleton__item__p (t : typ)
  (projectee : Obj.t buffer_root) : Obj.t pointer=
  match projectee with | BufferRootSingleton p -> p
let uu___is_BufferRootArray (t : typ) (projectee : Obj.t buffer_root) :
  Prims.bool=
  match projectee with
  | BufferRootArray (max_length, p) -> true
  | uu___ -> false
let __proj__BufferRootArray__item__max_length (t : typ)
  (projectee : Obj.t buffer_root) : array_length_t=
  match projectee with | BufferRootArray (max_length, p) -> max_length
let __proj__BufferRootArray__item__p (t : typ)
  (projectee : Obj.t buffer_root) : Obj.t pointer=
  match projectee with | BufferRootArray (max_length, p) -> p
let buffer_root_length (t : typ) (b : Obj.t buffer_root) : FStar_UInt32.t=
  match b with
  | BufferRootSingleton uu___ -> Stdint.Uint32.one
  | BufferRootArray (len, uu___) -> len
type 't _buffer =
  | Buffer of 't buffer_root * FStar_UInt32.t * FStar_UInt32.t 
let uu___is_Buffer (t : typ) (projectee : Obj.t _buffer) : Prims.bool= true
let __proj__Buffer__item__broot (t : typ) (projectee : Obj.t _buffer) :
  Obj.t buffer_root=
  match projectee with | Buffer (broot, bidx, blength) -> broot
let __proj__Buffer__item__bidx (t : typ) (projectee : Obj.t _buffer) :
  FStar_UInt32.t=
  match projectee with | Buffer (broot, bidx, blength) -> bidx
let __proj__Buffer__item__blength (t : typ) (projectee : Obj.t _buffer) :
  FStar_UInt32.t=
  match projectee with | Buffer (broot, bidx, blength) -> blength
type 't buffer = 't _buffer
type 't type_of_base_typ = Obj.t
type ('length, 't) array = 't FStar_Seq_Base.seq
type ('l, 'typeuofutyp, 'f) type_of_struct_field'' = 'typeuofutyp
type ('l, 'typeuofutyp, 'f) type_of_struct_field' =
  (Obj.t, 'typeuofutyp, 'f) type_of_struct_field''
type ('key, 'value) gtdata = ('key, 'value) Prims.dtuple2
let _gtdata_get_key (u : ('key, 'value) gtdata) : 'key=
  FStar_Pervasives.dfst u
let gtdata_get_value (u : ('key, 'value) gtdata) (k : 'key) : 'value=
  let uu___ = u in match uu___ with | Prims.Mkdtuple2 (uu___1, v) -> v
let gtdata_create (k : 'key) (v : 'value) : ('key, 'value) gtdata=
  Prims.Mkdtuple2 (k, v)
type 't type_of_typ' = Obj.t
type 'l struct1 = Obj.t
type 'l union = Obj.t
type 't type_of_typ = Obj.t
type ('l, 'uuuuu) type_of_struct_field = Obj.t
let _union_get_key (l : union_typ) (v : Obj.t) : Obj.t struct_field=
  _gtdata_get_key (Obj.magic v)
let struct_sel (l : struct_typ) (s : Obj.t) (f : Obj.t struct_field) : 
  Obj.t= FStar_DependentMap.sel (Obj.magic s) f
let dfst_struct_field (s : struct_typ)
  (p : (Obj.t struct_field, Obj.t) Prims.dtuple2) : Prims.string=
  let uu___ = p in match uu___ with | Prims.Mkdtuple2 (f, uu___1) -> f
type 's struct_literal = ('s struct_field, Obj.t) Prims.dtuple2 Prims.list
let struct_literal_wf (s : struct_typ) (l : Obj.t struct_literal) :
  Prims.bool=
  (FStar_List_Tot_Base.sortWith FStar_String.compare
     (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst s.fields))
    =
    (FStar_List_Tot_Base.sortWith FStar_String.compare
       (FStar_List_Tot_Base.map (dfst_struct_field s) l))
let fun_of_list (s : struct_typ) (l : Obj.t struct_literal)
  (f : Obj.t struct_field) : Obj.t=
  let f' = f in
  let phi p = (dfst_struct_field s p) = f' in
  match FStar_List_Tot_Base.find phi l with
  | FStar_Pervasives_Native.Some p ->
      let uu___ = p in (match uu___ with | Prims.Mkdtuple2 (uu___1, v) -> v)
  | uu___ -> FStar_Pervasives.false_elim ()
let struct_upd (uu___3 : struct_typ) (uu___2 : Obj.t)
  (uu___1 : Obj.t struct_field) (uu___ : Obj.t) : Obj.t=
  (fun l s f v -> Obj.magic (FStar_DependentMap.upd (Obj.magic s) f v))
    uu___3 uu___2 uu___1 uu___
let struct_create_fun (uu___1 : struct_typ)
  (uu___ : Obj.t struct_field -> Obj.t) : Obj.t=
  (fun l f -> Obj.magic (FStar_DependentMap.create f)) uu___1 uu___
let struct_create (s : struct_typ) (l : Obj.t struct_literal) : Obj.t=
  struct_create_fun s (fun_of_list s l)
let union_get_value (l : union_typ) (v : Obj.t) (fd : Obj.t struct_field) :
  Obj.t= gtdata_get_value (Obj.magic v) fd
let union_create (uu___2 : union_typ) (uu___1 : Obj.t struct_field)
  (uu___ : Obj.t) : Obj.t=
  (fun l fd v -> Obj.magic (gtdata_create fd v)) uu___2 uu___1 uu___
let rec dummy_val (t : typ) : Obj.t=
  match t with
  | TBase b ->
      Obj.repr
        (match b with
         | TUInt -> Obj.repr Prims.int_zero
         | TUInt8 -> Obj.repr (FStar_UInt8.uint_to_t Prims.int_zero)
         | TUInt16 -> Obj.repr (FStar_UInt16.uint_to_t Prims.int_zero)
         | TUInt32 -> Obj.repr (FStar_UInt32.uint_to_t Prims.int_zero)
         | TUInt64 -> Obj.repr (FStar_UInt64.uint_to_t Prims.int_zero)
         | TInt -> Obj.repr Prims.int_zero
         | TInt8 -> Obj.repr (FStar_Int8.int_to_t Prims.int_zero)
         | TInt16 -> Obj.repr (FStar_Int16.int_to_t Prims.int_zero)
         | TInt32 -> Obj.repr (FStar_Int32.int_to_t Prims.int_zero)
         | TInt64 -> Obj.repr (FStar_Int64.int_to_t Prims.int_zero)
         | TChar -> Obj.repr 99
         | TBool -> Obj.repr false
         | TUnit -> Obj.repr ())
  | TStruct l ->
      Obj.repr
        (struct_create_fun l (fun f -> dummy_val (typ_of_struct_field l f)))
  | TUnion l ->
      Obj.repr
        (let dummy_field =
           FStar_List_Tot_Base.hd
             (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l.fields) in
         union_create l dummy_field
           (dummy_val (typ_of_struct_field l dummy_field)))
  | TArray (length, t1) ->
      Obj.repr (FStar_Seq_Base.create (FStar_UInt32.v length) (dummy_val t1))
  | TPointer t1 ->
      Obj.repr
        (Pointer (t1, FStar_Monotonic_HyperStack.dummy_aref, PathBase))
  | TNPointer t1 -> Obj.repr NullPtr
  | TBuffer t1 ->
      Obj.repr
        (Buffer
           ((BufferRootSingleton
               (Pointer (t1, FStar_Monotonic_HyperStack.dummy_aref, PathBase))),
             Stdint.Uint32.zero, Stdint.Uint32.one))
type 't otype_of_typ = Obj.t
type ('l, 'uuuuu) otype_of_struct_field = Obj.t
type 'l ostruct =
  ('l struct_field, Obj.t) FStar_DependentMap.t
    FStar_Pervasives_Native.option
let ostruct_sel (l : struct_typ) (s : Obj.t ostruct) (f : Obj.t struct_field)
  : Obj.t=
  FStar_DependentMap.sel (FStar_Pervasives_Native.__proj__Some__item__v s) f
let ostruct_upd (l : struct_typ) (s : Obj.t ostruct) (f : Obj.t struct_field)
  (v : Obj.t) : Obj.t ostruct=
  FStar_Pervasives_Native.Some
    (FStar_DependentMap.upd (FStar_Pervasives_Native.__proj__Some__item__v s)
       f v)
let ostruct_create (l : struct_typ) (f : Obj.t struct_field -> Obj.t) :
  Obj.t ostruct= FStar_Pervasives_Native.Some (FStar_DependentMap.create f)
type 'l ounion =
  ('l struct_field, Obj.t) gtdata FStar_Pervasives_Native.option
let ounion_get_key (l : union_typ) (v : Obj.t ounion) : Obj.t struct_field=
  _gtdata_get_key (FStar_Pervasives_Native.__proj__Some__item__v v)
let ounion_get_value (l : union_typ) (v : Obj.t ounion)
  (fd : Obj.t struct_field) : Obj.t=
  gtdata_get_value (FStar_Pervasives_Native.__proj__Some__item__v v) fd
let ounion_create (l : union_typ) (fd : Obj.t struct_field) (v : Obj.t) :
  Obj.t ounion= FStar_Pervasives_Native.Some (gtdata_create fd v)
let struct_field_is_readable (l : struct_typ)
  (ovalue_is_readable : typ -> Obj.t -> Prims.bool) (v : Obj.t ostruct)
  (s : Prims.string) : Prims.bool=
  if
    FStar_List_Tot_Base.mem s
      (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l.fields)
  then ovalue_is_readable (typ_of_struct_field l s) (ostruct_sel l v s)
  else true
let rec ovalue_is_readable (t : typ) (v : Obj.t) : Prims.bool=
  match t with
  | TStruct l ->
      let v1 = Obj.magic v in
      (FStar_Pervasives_Native.uu___is_Some v1) &&
        (let keys =
           FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l.fields in
         let pred t' v2 = ovalue_is_readable t' v2 in
         FStar_List_Tot_Base.for_all (struct_field_is_readable l pred v1)
           keys)
  | TUnion l ->
      let v1 = Obj.magic v in
      (FStar_Pervasives_Native.uu___is_Some v1) &&
        (let k = ounion_get_key l v1 in
         ovalue_is_readable (typ_of_struct_field l k)
           (ounion_get_value l v1 k))
  | TArray (len, t1) ->
      let v1 = Obj.magic v in
      (FStar_Pervasives_Native.uu___is_Some v1) &&
        (FStar_Seq_Properties.for_all (ovalue_is_readable t1)
           (FStar_Pervasives_Native.__proj__Some__item__v v1))
  | TBase t1 ->
      let v1 = Obj.magic v in FStar_Pervasives_Native.uu___is_Some v1
  | TPointer t1 ->
      let v1 = Obj.magic v in FStar_Pervasives_Native.uu___is_Some v1
  | TNPointer t1 ->
      let v1 = Obj.magic v in FStar_Pervasives_Native.uu___is_Some v1
  | TBuffer t1 ->
      let v1 = Obj.magic v in FStar_Pervasives_Native.uu___is_Some v1
let ostruct_field_of_struct_field (l : struct_typ)
  (ovalue_of_value : typ -> Obj.t -> Obj.t) (v : Obj.t)
  (f : Obj.t struct_field) : Obj.t=
  ovalue_of_value (typ_of_struct_field l f) (struct_sel l v f)
let rec ovalue_of_value (t : typ) (v : Obj.t) : Obj.t=
  match t with
  | TStruct l ->
      Obj.repr
        (let oval t' v' = ovalue_of_value t' v' in
         ostruct_create l (ostruct_field_of_struct_field l oval v))
  | TArray (len, t1) ->
      Obj.repr
        (let v1 = Obj.magic v in
         let f i = ovalue_of_value t1 (FStar_Seq_Base.index v1 i) in
         let v' = FStar_Seq_Base.init (FStar_UInt32.v len) f in
         FStar_Pervasives_Native.Some v')
  | TUnion l ->
      Obj.repr
        (let v1 = v in
         let k = _union_get_key l v1 in
         ounion_create l k
           (ovalue_of_value (typ_of_struct_field l k)
              (union_get_value l v1 k)))
  | uu___ -> Obj.repr (FStar_Pervasives_Native.Some v)
let rec value_of_ovalue (t : typ) (v : Obj.t) : Obj.t=
  match t with
  | TStruct l ->
      let v1 = Obj.magic v in
      if FStar_Pervasives_Native.uu___is_Some v1
      then
        let phi f =
          value_of_ovalue (typ_of_struct_field l f) (ostruct_sel l v1 f) in
        struct_create_fun l phi
      else dummy_val t
  | TArray (len, t') ->
      let v1 = Obj.magic v in
      (match v1 with
       | FStar_Pervasives_Native.None -> Obj.repr (dummy_val t)
       | FStar_Pervasives_Native.Some v2 ->
           Obj.repr
             (let phi i = value_of_ovalue t' (FStar_Seq_Base.index v2 i) in
              FStar_Seq_Base.init (FStar_UInt32.v len) phi))
  | TUnion l ->
      let v1 = Obj.magic v in
      (match v1 with
       | FStar_Pervasives_Native.None -> dummy_val t
       | uu___ ->
           let k = ounion_get_key l v1 in
           union_create l k
             (value_of_ovalue (typ_of_struct_field l k)
                (ounion_get_value l v1 k)))
  | TBase b ->
      let v1 = Obj.magic v in
      (match v1 with
       | FStar_Pervasives_Native.None -> dummy_val t
       | FStar_Pervasives_Native.Some v2 -> v2)
  | TPointer t' ->
      let v1 = Obj.magic v in
      (match v1 with
       | FStar_Pervasives_Native.None -> Obj.repr (dummy_val t)
       | FStar_Pervasives_Native.Some v2 -> Obj.repr v2)
  | TNPointer t' ->
      let v1 = Obj.magic v in
      (match v1 with
       | FStar_Pervasives_Native.None -> Obj.repr (dummy_val t)
       | FStar_Pervasives_Native.Some v2 -> Obj.repr v2)
  | TBuffer t' ->
      let v1 = Obj.magic v in
      (match v1 with
       | FStar_Pervasives_Native.None -> Obj.repr (dummy_val t)
       | FStar_Pervasives_Native.Some v2 -> Obj.repr v2)
let none_ovalue (t : typ) : Obj.t=
  match t with
  | TStruct l -> Obj.repr FStar_Pervasives_Native.None
  | TArray (len, t') -> Obj.repr FStar_Pervasives_Native.None
  | TUnion l -> Obj.repr FStar_Pervasives_Native.None
  | TBase b -> Obj.repr FStar_Pervasives_Native.None
  | TPointer t' -> Obj.repr FStar_Pervasives_Native.None
  | TNPointer t' -> Obj.repr FStar_Pervasives_Native.None
  | TBuffer t' -> Obj.repr FStar_Pervasives_Native.None
let step_sel (from : typ) (to1 : typ) (m' : Obj.t) (s : (Obj.t, Obj.t) step)
  : Obj.t=
  match s with
  | StepField (l, fd) ->
      let m'1 = Obj.magic m' in
      (match m'1 with
       | FStar_Pervasives_Native.None -> none_ovalue to1
       | uu___ -> ostruct_sel l m'1 fd)
  | StepUField (l, fd) ->
      let m'1 = Obj.magic m' in
      (match m'1 with
       | FStar_Pervasives_Native.None -> none_ovalue to1
       | uu___ ->
           if fd = (ounion_get_key l m'1)
           then ounion_get_value l m'1 fd
           else none_ovalue to1)
  | StepCell (length, value, i) ->
      let m'1 = Obj.magic m' in
      (match m'1 with
       | FStar_Pervasives_Native.None -> none_ovalue to1
       | FStar_Pervasives_Native.Some m'2 ->
           FStar_Seq_Base.index m'2 (FStar_UInt32.v i))
let rec path_sel (from : typ) (to1 : typ) (m : Obj.t)
  (p : (Obj.t, Obj.t) path) : Obj.t=
  match p with
  | PathBase -> m
  | PathStep (through', to', p', s) ->
      let m' = path_sel from through' m p' in step_sel through' to' m' s
let step_upd (from : typ) (to1 : typ) (m : Obj.t) (s : (Obj.t, Obj.t) step)
  (v : Obj.t) : Obj.t=
  match s with
  | StepField (l, fd) ->
      Obj.repr
        (let m1 = Obj.magic m in
         match m1 with
         | FStar_Pervasives_Native.None ->
             let phi fd' =
               if fd' = fd
               then v
               else none_ovalue (typ_of_struct_field l fd') in
             ostruct_create l phi
         | FStar_Pervasives_Native.Some uu___ -> ostruct_upd l m1 fd v)
  | StepCell (len, uu___, i) ->
      Obj.repr
        (let m1 = Obj.magic m in
         match m1 with
         | FStar_Pervasives_Native.None ->
             let phi j =
               if j = (FStar_UInt32.v i) then v else none_ovalue to1 in
             let m' =
               FStar_Pervasives_Native.Some
                 (FStar_Seq_Base.init (FStar_UInt32.v len) phi) in
             m'
         | FStar_Pervasives_Native.Some m2 ->
             let m' =
               FStar_Pervasives_Native.Some
                 (FStar_Seq_Base.upd m2 (FStar_UInt32.v i) v) in
             m')
  | StepUField (l, fd) -> Obj.repr (ounion_create l fd v)
let rec path_upd (from : typ) (to1 : typ) (m : Obj.t)
  (p : (Obj.t, Obj.t) path) (v : Obj.t) : Obj.t=
  match p with
  | PathBase -> v
  | PathStep (through', to', p', st) ->
      let s = path_sel from through' m p' in
      path_upd from through' m p' (step_upd through' to' s st v)
let rec path_concat (from : typ) (through : typ) (to1 : typ)
  (p : (Obj.t, Obj.t) path) (q : (Obj.t, Obj.t) path) : (Obj.t, Obj.t) path=
  match q with
  | PathBase -> p
  | PathStep (through', to', q', st) ->
      PathStep (through', to', (path_concat from through through' p q'), st)
let rec path_length (from : typ) (to1 : typ) (p : (Obj.t, Obj.t) path) :
  Prims.nat=
  match p with
  | PathBase -> Prims.int_zero
  | PathStep (uu___, uu___1, p', uu___2) ->
      Prims.int_one + (path_length from uu___ p')
let step_eq (from : typ) (to1 : typ) (to2 : typ) (s1 : (Obj.t, Obj.t) step)
  (s2 : (Obj.t, Obj.t) step) : Prims.bool=
  match s1 with
  | StepField (l1, fd1) ->
      let uu___ = s2 in
      (match uu___ with | StepField (uu___1, fd2) -> fd1 = fd2)
  | StepCell (uu___, uu___1, i1) ->
      let uu___2 = s2 in
      (match uu___2 with | StepCell (uu___3, uu___4, i2) -> i1 = i2)
  | StepUField (l1, fd1) ->
      let uu___ = s2 in
      (match uu___ with | StepUField (uu___1, fd2) -> fd1 = fd2)
type ('from, 'dummyV0, 'dummyV1, 'dummyV2, 'dummyV3) path_disjoint_t =
  | PathDisjointStep of typ * typ * typ * ('from, Obj.t) path * (Obj.t,
  Obj.t) step * (Obj.t, Obj.t) step 
  | PathDisjointIncludes of typ * typ * ('from, Obj.t) path * ('from, 
  Obj.t) path * typ * typ * ('from, Obj.t) path * ('from, Obj.t) path *
  ('from, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t 
let uu___is_PathDisjointStep (from : typ) (to1 : typ) (to2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  Prims.bool=
  match projectee with
  | PathDisjointStep (through, to11, to21, p, s1, s2) -> true
  | uu___ -> false
let __proj__PathDisjointStep__item__through (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) : 
  typ=
  match projectee with
  | PathDisjointStep (through, to11, to21, p, s1, s2) -> through
let __proj__PathDisjointStep__item__to1 (from : typ) (to1 : typ) (to2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) : 
  typ=
  match projectee with
  | PathDisjointStep (through, to11, to21, p, s1, s2) -> to11
let __proj__PathDisjointStep__item__to2 (from : typ) (to1 : typ) (to2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) : 
  typ=
  match projectee with
  | PathDisjointStep (through, to11, to21, p, s1, s2) -> to21
let __proj__PathDisjointStep__item__p (from : typ) (to1 : typ) (to2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  (Obj.t, Obj.t) path=
  match projectee with
  | PathDisjointStep (through, to11, to21, p, s1, s2) -> p
let __proj__PathDisjointStep__item__s1 (from : typ) (to1 : typ) (to2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  (Obj.t, Obj.t) step=
  match projectee with
  | PathDisjointStep (through, to11, to21, p, s1, s2) -> s1
let __proj__PathDisjointStep__item__s2 (from : typ) (to1 : typ) (to2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  (Obj.t, Obj.t) step=
  match projectee with
  | PathDisjointStep (through, to11, to21, p, s1, s2) -> s2
let uu___is_PathDisjointIncludes (from : typ) (to1 : typ) (to2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  Prims.bool=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      true
  | uu___ -> false
let __proj__PathDisjointIncludes__item__to1 (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) : 
  typ=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      to11
let __proj__PathDisjointIncludes__item__to2 (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) : 
  typ=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      to21
let __proj__PathDisjointIncludes__item__p1 (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  (Obj.t, Obj.t) path=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      p11
let __proj__PathDisjointIncludes__item__p2 (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  (Obj.t, Obj.t) path=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      p21
let __proj__PathDisjointIncludes__item__to1' (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) : 
  typ=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      to1'
let __proj__PathDisjointIncludes__item__to2' (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) : 
  typ=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      to2'
let __proj__PathDisjointIncludes__item__p1' (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  (Obj.t, Obj.t) path=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      p1'
let __proj__PathDisjointIncludes__item__p2' (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  (Obj.t, Obj.t) path=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      p2'
let __proj__PathDisjointIncludes__item___8 (from : typ) (to1 : typ)
  (to2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t) :
  (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t=
  match projectee with
  | PathDisjointIncludes (to11, to21, p11, p21, to1', to2', p1', p2', _8) ->
      _8
type ('from, 'value1, 'value2, 'p1, 'p2) path_disjoint = unit
let rec path_equal (from : typ) (value1 : typ) (value2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path) : Prims.bool=
  match p1 with
  | PathBase -> uu___is_PathBase from value2 p2
  | PathStep (uu___, uu___1, p1', s1) ->
      (uu___is_PathStep from value2 p2) &&
        (let uu___2 = p2 in
         (match uu___2 with
          | PathStep (uu___3, uu___4, p2', s2) ->
              (path_equal from uu___ uu___3 p1' p2') &&
                (step_eq uu___ uu___1 uu___4 s1 s2)))
type ('from, 'value1, 'value2, 'p1, 'p2) path_disjoint_decomp_t =
  | PathDisjointDecomp of typ * ('from, Obj.t) path * typ * (Obj.t, Obj.t)
  step * (Obj.t, 'value1) path * typ * (Obj.t, Obj.t) step * (Obj.t, 
  'value2) path * unit 
let uu___is_PathDisjointDecomp (from : typ) (value1 : typ) (value2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  Prims.bool= true
let __proj__PathDisjointDecomp__item__d_through (from : typ) (value1 : typ)
  (value2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  typ=
  match projectee with
  | PathDisjointDecomp
      (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8) -> d_through
let __proj__PathDisjointDecomp__item__d_p (from : typ) (value1 : typ)
  (value2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  (Obj.t, Obj.t) path=
  match projectee with
  | PathDisjointDecomp
      (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8) -> d_p
let __proj__PathDisjointDecomp__item__d_v1 (from : typ) (value1 : typ)
  (value2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  typ=
  match projectee with
  | PathDisjointDecomp
      (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8) -> d_v1
let __proj__PathDisjointDecomp__item__d_s1 (from : typ) (value1 : typ)
  (value2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  (Obj.t, Obj.t) step=
  match projectee with
  | PathDisjointDecomp
      (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8) -> d_s1
let __proj__PathDisjointDecomp__item__d_p1' (from : typ) (value1 : typ)
  (value2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  (Obj.t, Obj.t) path=
  match projectee with
  | PathDisjointDecomp
      (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8) -> d_p1'
let __proj__PathDisjointDecomp__item__d_v2 (from : typ) (value1 : typ)
  (value2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  typ=
  match projectee with
  | PathDisjointDecomp
      (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8) -> d_v2
let __proj__PathDisjointDecomp__item__d_s2 (from : typ) (value1 : typ)
  (value2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  (Obj.t, Obj.t) step=
  match projectee with
  | PathDisjointDecomp
      (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8) -> d_s2
let __proj__PathDisjointDecomp__item__d_p2' (from : typ) (value1 : typ)
  (value2 : typ) (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path)
  (projectee : (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t) :
  (Obj.t, Obj.t) path=
  match projectee with
  | PathDisjointDecomp
      (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8) -> d_p2'
let rec path_destruct_l (t0 : typ) (t2 : typ) (p : (Obj.t, Obj.t) path) :
  (typ, ((Obj.t, Obj.t) step, (Obj.t, Obj.t) path) Prims.dtuple2)
    Prims.dtuple2 FStar_Pervasives_Native.option=
  match p with
  | PathBase -> FStar_Pervasives_Native.None
  | PathStep (uu___, uu___1, p', s) ->
      (match path_destruct_l t0 uu___ p' with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some
             (Prims.Mkdtuple2 (t2, (Prims.Mkdtuple2 (s, PathBase))))
       | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
           (t_, Prims.Mkdtuple2 (s_, p_))) ->
           FStar_Pervasives_Native.Some
             (Prims.Mkdtuple2
                (t_,
                  (Prims.Mkdtuple2 (s_, (PathStep (uu___, uu___1, p_, s)))))))
let rec path_equal' (from : typ) (to1 : typ) (to2 : typ)
  (p1 : (Obj.t, Obj.t) path) (p2 : (Obj.t, Obj.t) path) : Prims.bool=
  match path_destruct_l from to1 p1 with
  | FStar_Pervasives_Native.None -> uu___is_PathBase from to2 p2
  | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
      (t1, Prims.Mkdtuple2 (s1, p1'))) ->
      (match path_destruct_l from to2 p2 with
       | FStar_Pervasives_Native.None -> false
       | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
           (t2, Prims.Mkdtuple2 (s2, p2'))) ->
           (step_eq from t1 t2 s1 s2) && (path_equal' t1 to1 to2 p1' p2'))
let _field (l : struct_typ) (p : Obj.t pointer) (fd : Obj.t struct_field) :
  Obj.t pointer=
  let uu___ = p in
  match uu___ with
  | Pointer (from, contents, p') ->
      let p'1 = p' in
      let p'' =
        PathStep
          ((TStruct l), (typ_of_struct_field l fd), p'1, (StepField (l, fd))) in
      Pointer (from, contents, p'')
let _cell (length : array_length_t) (value : typ) (p : Obj.t pointer)
  (i : FStar_UInt32.t) : Obj.t pointer=
  let uu___ = p in
  match uu___ with
  | Pointer (from, contents, p') ->
      let p'1 = p' in
      let p'' =
        PathStep
          ((TArray (length, value)), value, p'1,
            (StepCell (length, value, i))) in
      Pointer (from, contents, p'')
let _ufield (l : union_typ) (p : Obj.t pointer) (fd : Obj.t struct_field) :
  Obj.t pointer=
  let uu___ = p in
  match uu___ with
  | Pointer (from, contents, p') ->
      let p'1 = p' in
      let p'' =
        PathStep
          ((TUnion l), (typ_of_struct_field l fd), p'1, (StepUField (l, fd))) in
      Pointer (from, contents, p'')
type ('value, 'p, 'h) unused_in = Obj.t
type pointer_ref_contents = (typ, Obj.t) Prims.dtuple2
type ('value, 'h, 'p) live = Obj.t
type ('value, 'h, 'p) nlive = Obj.t
type ('a, 'h, 'b) readable = unit
type ('l, 'h, 'p, 's) readable_struct_fields' = Obj.t
type ('l, 'h, 'p, 's) readable_struct_fields = Obj.t
type ('l, 'h, 'p, 'fd) is_active_union_field = unit
type ('a, 'h, 'b, 'hu, 'bu) equal_values = unit
let _singleton_buffer_of_pointer (t : typ) (p : Obj.t pointer) :
  Obj.t buffer=
  let uu___ = p in
  match uu___ with
  | Pointer (from, contents, pth) ->
      (match pth with
       | PathStep (uu___1, uu___2, pth', StepCell (ln, ty, i)) ->
           Buffer
             ((BufferRootArray (ln, (Pointer (from, contents, pth')))), i,
               Stdint.Uint32.one)
       | uu___1 ->
           Buffer
             ((BufferRootSingleton p), Stdint.Uint32.zero, Stdint.Uint32.one))
let singleton_buffer_of_pointer (t : typ) (p : Obj.t pointer) : Obj.t buffer=
  _singleton_buffer_of_pointer t p
let buffer_of_array_pointer (t : typ) (length : array_length_t)
  (p : Obj.t pointer) : Obj.t buffer=
  Buffer ((BufferRootArray (length, p)), Stdint.Uint32.zero, length)
type ('t, 'h, 'b) buffer_live = Obj.t
type ('t, 'b, 'h) buffer_unused_in = Obj.t
let sub_buffer (t : typ) (b : Obj.t buffer) (i : FStar_UInt32.t)
  (len : FStar_UInt32.t) : Obj.t buffer=
  Buffer
    ((__proj__Buffer__item__broot t b),
      (FStar_UInt32.add (__proj__Buffer__item__bidx t b) i), len)
let offset_buffer (t : typ) (b : Obj.t buffer) (i : FStar_UInt32.t) :
  Obj.t buffer=
  sub_buffer t b i (FStar_UInt32.sub (__proj__Buffer__item__blength t b) i)
let pointer_of_buffer_cell (t : typ) (b : Obj.t buffer) (i : FStar_UInt32.t)
  : Obj.t pointer=
  match __proj__Buffer__item__broot t b with
  | BufferRootSingleton p -> p
  | BufferRootArray (uu___, p) ->
      _cell uu___ t p (FStar_UInt32.add (__proj__Buffer__item__bidx t b) i)
type ('t, 'h, 'b) buffer_readable' = unit
type ('t, 'h, 'b) buffer_readable = unit
type ('value1, 'value2, 'p1, 'p2) disjoint = Obj.t
type loc_aux =
  | LocBuffer of typ * Obj.t buffer 
  | LocPointer of typ * Obj.t pointer 
let uu___is_LocBuffer (projectee : loc_aux) : Prims.bool=
  match projectee with | LocBuffer (t, b) -> true | uu___ -> false
let __proj__LocBuffer__item__t (projectee : loc_aux) : typ=
  match projectee with | LocBuffer (t, b) -> t
let __proj__LocBuffer__item__b (projectee : loc_aux) : Obj.t buffer=
  match projectee with | LocBuffer (t, b) -> b
let uu___is_LocPointer (projectee : loc_aux) : Prims.bool=
  match projectee with | LocPointer (t, p) -> true | uu___ -> false
let __proj__LocPointer__item__t (projectee : loc_aux) : typ=
  match projectee with | LocPointer (t, p) -> t
let __proj__LocPointer__item__p (projectee : loc_aux) : Obj.t pointer=
  match projectee with | LocPointer (t, p) -> p
type ('t1, 't2, 'b, 'p) buffer_includes_pointer = unit
type ('s, 't, 'p) loc_aux_includes_pointer = Obj.t
type ('s, 't, 'b) loc_aux_includes_buffer = unit
type ('s, 's2) loc_aux_includes = Obj.t
type ('t1, 't2, 'b, 'p) disjoint_buffer_vs_pointer = unit
type ('l, 't, 'p) loc_aux_disjoint_pointer = Obj.t
type ('l, 't, 'b) loc_aux_disjoint_buffer = unit
type ('l1, 'l2) loc_aux_disjoint = Obj.t
type ('t, 'p, 'h, 'hu) pointer_preserved = unit
type ('t, 'b, 'h, 'hu) buffer_preserved = unit
type ('l, 'h, 'hu) loc_aux_preserved = Obj.t
type ('l, 'r, 'n) loc_aux_in_addr = Obj.t
type ('r, 'n) aloc = loc_aux
type loc = unit

type ('s1, 's2) loc_includes = unit
type ('s1, 's2) loc_disjoint = unit
type ('s, 'h1, 'h2) modifies = unit
type ('h0, 'h1) modifies_0 = unit
type ('t, 'p, 'h0, 'h1) modifies_1 = unit
let screate (value : typ) (s : Obj.t FStar_Pervasives_Native.option) :
  Obj.t pointer=
  let h0 = FStar_HyperStack_ST.get () in
  let s1 =
    match s with
    | FStar_Pervasives_Native.Some s2 -> ovalue_of_value value s2
    | uu___ -> none_ovalue value in
  let content = FStar_HyperStack_ST.salloc (Prims.Mkdtuple2 (value, s1)) in
  let aref = FStar_Monotonic_HyperStack.aref_of content in
  let p = Pointer (value, aref, PathBase) in
  let h1 = FStar_HyperStack_ST.get () in p
let ecreate (t : typ) (r : unit) (s : Obj.t FStar_Pervasives_Native.option) :
  Obj.t pointer=
  let h0 = FStar_HyperStack_ST.get () in
  let s0 = s in
  let s1 =
    match s with
    | FStar_Pervasives_Native.Some s2 -> ovalue_of_value t s2
    | uu___ -> none_ovalue t in
  let content = FStar_HyperStack_ST.ralloc () (Prims.Mkdtuple2 (t, s1)) in
  let aref = FStar_Monotonic_HyperStack.aref_of content in
  let p = Pointer (t, aref, PathBase) in
  let h1 = FStar_HyperStack_ST.get () in p
let field (l : struct_typ) (p : Obj.t pointer) (fd : Obj.t struct_field) :
  Obj.t pointer= _field l p fd
let ufield (l : union_typ) (p : Obj.t pointer) (fd : Obj.t struct_field) :
  Obj.t pointer= _ufield l p fd
let cell (length : array_length_t) (value : typ) (p : Obj.t pointer)
  (i : FStar_UInt32.t) : Obj.t pointer= _cell length value p i
let reference_of (value : typ) (h : FStar_Monotonic_HyperStack.mem)
  (p : Obj.t pointer) : pointer_ref_contents FStar_HyperStack.reference=
  let x =
    Obj.magic
      (FStar_Monotonic_HyperStack.reference_of h
         (__proj__Pointer__item__contents value p) () ()) in
  x
let read (value : typ) (p : Obj.t pointer) : Obj.t=
  let h = FStar_HyperStack_ST.get () in
  let r = reference_of value h p in
  FStar_HyperStack_ST.witness_region ();
  FStar_HyperStack_ST.witness_hsref r;
  (let uu___2 = FStar_HyperStack_ST.op_Bang r in
   match uu___2 with
   | Prims.Mkdtuple2 (uu___3, c) ->
       value_of_ovalue value
         (path_sel uu___3 value c (__proj__Pointer__item__p value p)))
let is_null (t : typ) (p : Obj.t npointer) : Prims.bool=
  match p with | NullPtr -> true | uu___ -> false
let owrite (a : typ) (b : Obj.t pointer) (z : Obj.t) : unit=
  let h0 = FStar_HyperStack_ST.get () in
  let r = reference_of a h0 b in
  FStar_HyperStack_ST.witness_region ();
  FStar_HyperStack_ST.witness_hsref r;
  (let v0 = FStar_HyperStack_ST.op_Bang r in
   let uu___2 = v0 in
   match uu___2 with
   | Prims.Mkdtuple2 (t, c0) ->
       let c1 = path_upd t a c0 (__proj__Pointer__item__p a b) z in
       let v1 = Prims.Mkdtuple2 (t, c1) in
       (FStar_HyperStack_ST.op_Colon_Equals r v1;
        (let h1 = FStar_HyperStack_ST.get () in ())))
let write (a : typ) (b : Obj.t pointer) (z : Obj.t) : unit=
  owrite a b (ovalue_of_value a z)
let write_union_field (l : union_typ) (p : Obj.t pointer)
  (fd : Obj.t struct_field) : unit=
  let field_t = typ_of_struct_field l fd in
  let vu =
    FStar_Pervasives_Native.Some (gtdata_create fd (none_ovalue field_t)) in
  let vu1 = Obj.magic vu in owrite (TUnion l) p vu1
let read_buffer (t : typ) (b : Obj.t buffer) (i : FStar_UInt32.t) : Obj.t=
  let uu___ = pointer_of_buffer_cell t b i in read t uu___
let write_buffer (t : typ) (b : Obj.t buffer) (i : FStar_UInt32.t)
  (v : Obj.t) : unit=
  let uu___ = pointer_of_buffer_cell t b i in write t uu___ v
type ('t, 'blarge, 'bsmall) buffer_includes = unit
type ('uuuuu, 'uuuuu1) cloc_aloc = ('uuuuu, 'uuuuu1) aloc


open Fstarcompiler
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
let (uu___is_TUInt : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TUInt -> true | uu___ -> false
let (uu___is_TUInt8 : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TUInt8 -> true | uu___ -> false
let (uu___is_TUInt16 : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TUInt16 -> true | uu___ -> false
let (uu___is_TUInt32 : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TUInt32 -> true | uu___ -> false
let (uu___is_TUInt64 : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TUInt64 -> true | uu___ -> false
let (uu___is_TInt : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TInt -> true | uu___ -> false
let (uu___is_TInt8 : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TInt8 -> true | uu___ -> false
let (uu___is_TInt16 : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TInt16 -> true | uu___ -> false
let (uu___is_TInt32 : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TInt32 -> true | uu___ -> false
let (uu___is_TInt64 : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TInt64 -> true | uu___ -> false
let (uu___is_TChar : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TChar -> true | uu___ -> false
let (uu___is_TBool : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TBool -> true | uu___ -> false
let (uu___is_TUnit : base_typ -> Prims.bool) =
  fun projectee -> match projectee with | TUnit -> true | uu___ -> false
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
let (uu___is_TBase : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBase b -> true | uu___ -> false
let (__proj__TBase__item__b : typ -> base_typ) =
  fun projectee -> match projectee with | TBase b -> b
let (uu___is_TStruct : typ -> Prims.bool) =
  fun projectee -> match projectee with | TStruct l -> true | uu___ -> false
let (__proj__TStruct__item__l : typ -> struct_typ) =
  fun projectee -> match projectee with | TStruct l -> l
let (uu___is_TUnion : typ -> Prims.bool) =
  fun projectee -> match projectee with | TUnion l -> true | uu___ -> false
let (__proj__TUnion__item__l : typ -> struct_typ) =
  fun projectee -> match projectee with | TUnion l -> l
let (uu___is_TArray : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TArray (length, t) -> true | uu___ -> false
let (__proj__TArray__item__length : typ -> array_length_t) =
  fun projectee -> match projectee with | TArray (length, t) -> length
let (__proj__TArray__item__t : typ -> typ) =
  fun projectee -> match projectee with | TArray (length, t) -> t
let (uu___is_TPointer : typ -> Prims.bool) =
  fun projectee -> match projectee with | TPointer t -> true | uu___ -> false
let (__proj__TPointer__item__t : typ -> typ) =
  fun projectee -> match projectee with | TPointer t -> t
let (uu___is_TNPointer : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TNPointer t -> true | uu___ -> false
let (__proj__TNPointer__item__t : typ -> typ) =
  fun projectee -> match projectee with | TNPointer t -> t
let (uu___is_TBuffer : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBuffer t -> true | uu___ -> false
let (__proj__TBuffer__item__t : typ -> typ) =
  fun projectee -> match projectee with | TBuffer t -> t
let (__proj__Mkstruct_typ__item__name : struct_typ -> Prims.string) =
  fun projectee -> match projectee with | { name; fields;_} -> name
let (__proj__Mkstruct_typ__item__fields :
  struct_typ -> (Prims.string * typ) Prims.list) =
  fun projectee -> match projectee with | { name; fields;_} -> fields
type struct_typ' = (Prims.string * typ) Prims.list
type union_typ = struct_typ
type 'l struct_field' = Prims.string
type 'l struct_field = Obj.t struct_field'
type 'l union_field = 'l struct_field
let (typ_of_struct_field' : struct_typ' -> Obj.t struct_field' -> typ) =
  fun l ->
    fun f ->
      let y =
        FStar_Pervasives_Native.__proj__Some__item__v
          (FStar_List_Tot_Base.assoc f l) in
      y
let (typ_of_struct_field : struct_typ -> Obj.t struct_field -> typ) =
  fun l -> fun f -> typ_of_struct_field' l.fields f
let (typ_of_union_field : union_typ -> Obj.t union_field -> typ) =
  fun l -> fun f -> typ_of_struct_field l f
type ('dummyV0, 'dummyV1) step =
  | StepField of struct_typ * Obj.t struct_field 
  | StepUField of union_typ * Obj.t struct_field 
  | StepCell of FStar_UInt32.t * typ * FStar_UInt32.t 
let (uu___is_StepField : typ -> typ -> (Obj.t, Obj.t) step -> Prims.bool) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | StepField (l, fd) -> true | uu___ -> false
let (__proj__StepField__item__l :
  typ -> typ -> (Obj.t, Obj.t) step -> struct_typ) =
  fun from ->
    fun to1 -> fun projectee -> match projectee with | StepField (l, fd) -> l
let (__proj__StepField__item__fd :
  typ -> typ -> (Obj.t, Obj.t) step -> Obj.t struct_field) =
  fun from ->
    fun to1 ->
      fun projectee -> match projectee with | StepField (l, fd) -> fd
let (uu___is_StepUField : typ -> typ -> (Obj.t, Obj.t) step -> Prims.bool) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | StepUField (l, fd) -> true | uu___ -> false
let (__proj__StepUField__item__l :
  typ -> typ -> (Obj.t, Obj.t) step -> union_typ) =
  fun from ->
    fun to1 ->
      fun projectee -> match projectee with | StepUField (l, fd) -> l
let (__proj__StepUField__item__fd :
  typ -> typ -> (Obj.t, Obj.t) step -> Obj.t struct_field) =
  fun from ->
    fun to1 ->
      fun projectee -> match projectee with | StepUField (l, fd) -> fd
let (uu___is_StepCell : typ -> typ -> (Obj.t, Obj.t) step -> Prims.bool) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with
        | StepCell (length, value, index) -> true
        | uu___ -> false
let (__proj__StepCell__item__length :
  typ -> typ -> (Obj.t, Obj.t) step -> FStar_UInt32.t) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | StepCell (length, value, index) -> length
let (__proj__StepCell__item__value :
  typ -> typ -> (Obj.t, Obj.t) step -> typ) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | StepCell (length, value, index) -> value
let (__proj__StepCell__item__index :
  typ -> typ -> (Obj.t, Obj.t) step -> FStar_UInt32.t) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | StepCell (length, value, index) -> index
type ('from, 'dummyV0) path =
  | PathBase 
  | PathStep of typ * typ * ('from, Obj.t) path * (Obj.t, Obj.t) step 
let (uu___is_PathBase : typ -> typ -> (Obj.t, Obj.t) path -> Prims.bool) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | PathBase -> true | uu___ -> false
let (uu___is_PathStep : typ -> typ -> (Obj.t, Obj.t) path -> Prims.bool) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with
        | PathStep (through, to2, p, s) -> true
        | uu___ -> false
let (__proj__PathStep__item__through :
  typ -> typ -> (Obj.t, Obj.t) path -> typ) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | PathStep (through, to2, p, s) -> through
let (__proj__PathStep__item__to : typ -> typ -> (Obj.t, Obj.t) path -> typ) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | PathStep (through, to2, p, s) -> to2
let (__proj__PathStep__item__p :
  typ -> typ -> (Obj.t, Obj.t) path -> (Obj.t, Obj.t) path) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | PathStep (through, to2, p, s) -> p
let (__proj__PathStep__item__s :
  typ -> typ -> (Obj.t, Obj.t) path -> (Obj.t, Obj.t) step) =
  fun from ->
    fun to1 ->
      fun projectee ->
        match projectee with | PathStep (through, to2, p, s) -> s
type 'to1 _npointer =
  | Pointer of typ * FStar_Monotonic_HyperStack.aref * (Obj.t, 'to1) path 
  | NullPtr 
let (uu___is_Pointer : typ -> Obj.t _npointer -> Prims.bool) =
  fun to1 ->
    fun projectee ->
      match projectee with
      | Pointer (from, contents, p) -> true
      | uu___ -> false
let (__proj__Pointer__item__from : typ -> Obj.t _npointer -> typ) =
  fun to1 ->
    fun projectee ->
      match projectee with | Pointer (from, contents, p) -> from
let (__proj__Pointer__item__contents :
  typ -> Obj.t _npointer -> FStar_Monotonic_HyperStack.aref) =
  fun to1 ->
    fun projectee ->
      match projectee with | Pointer (from, contents, p) -> contents
let (__proj__Pointer__item__p :
  typ -> Obj.t _npointer -> (Obj.t, Obj.t) path) =
  fun to1 ->
    fun projectee -> match projectee with | Pointer (from, contents, p) -> p
let (uu___is_NullPtr : typ -> Obj.t _npointer -> Prims.bool) =
  fun to1 ->
    fun projectee -> match projectee with | NullPtr -> true | uu___ -> false
type 't npointer = 't _npointer
let (nullptr : typ -> Obj.t npointer) = fun t -> NullPtr
type 't pointer = 't npointer
type 't buffer_root =
  | BufferRootSingleton of 't pointer 
  | BufferRootArray of array_length_t * Obj.t pointer 
let (uu___is_BufferRootSingleton : typ -> Obj.t buffer_root -> Prims.bool) =
  fun t ->
    fun projectee ->
      match projectee with | BufferRootSingleton p -> true | uu___ -> false
let (__proj__BufferRootSingleton__item__p :
  typ -> Obj.t buffer_root -> Obj.t pointer) =
  fun t -> fun projectee -> match projectee with | BufferRootSingleton p -> p
let (uu___is_BufferRootArray : typ -> Obj.t buffer_root -> Prims.bool) =
  fun t ->
    fun projectee ->
      match projectee with
      | BufferRootArray (max_length, p) -> true
      | uu___ -> false
let (__proj__BufferRootArray__item__max_length :
  typ -> Obj.t buffer_root -> array_length_t) =
  fun t ->
    fun projectee ->
      match projectee with | BufferRootArray (max_length, p) -> max_length
let (__proj__BufferRootArray__item__p :
  typ -> Obj.t buffer_root -> Obj.t pointer) =
  fun t ->
    fun projectee ->
      match projectee with | BufferRootArray (max_length, p) -> p
let (buffer_root_length : typ -> Obj.t buffer_root -> FStar_UInt32.t) =
  fun t ->
    fun b ->
      match b with
      | BufferRootSingleton uu___ -> Stdint.Uint32.one
      | BufferRootArray (len, uu___) -> len
type 't _buffer =
  | Buffer of 't buffer_root * FStar_UInt32.t * FStar_UInt32.t 
let (uu___is_Buffer : typ -> Obj.t _buffer -> Prims.bool) =
  fun t -> fun projectee -> true
let (__proj__Buffer__item__broot : typ -> Obj.t _buffer -> Obj.t buffer_root)
  =
  fun t ->
    fun projectee ->
      match projectee with | Buffer (broot, bidx, blength) -> broot
let (__proj__Buffer__item__bidx : typ -> Obj.t _buffer -> FStar_UInt32.t) =
  fun t ->
    fun projectee ->
      match projectee with | Buffer (broot, bidx, blength) -> bidx
let (__proj__Buffer__item__blength : typ -> Obj.t _buffer -> FStar_UInt32.t)
  =
  fun t ->
    fun projectee ->
      match projectee with | Buffer (broot, bidx, blength) -> blength
type 't buffer = 't _buffer
type 't type_of_base_typ = Obj.t
type ('length, 't) array = 't FStar_Seq_Base.seq
type ('l, 'typeuofutyp, 'f) type_of_struct_field'' = 'typeuofutyp
type ('l, 'typeuofutyp, 'f) type_of_struct_field' =
  (Obj.t, 'typeuofutyp, 'f) type_of_struct_field''
type ('key, 'value) gtdata = ('key, 'value) Fstarcompiler.Prims.dtuple2
let _gtdata_get_key : 'key 'value . ('key, 'value) gtdata -> 'key =
  fun u -> FStar_Pervasives.dfst u
let gtdata_get_value : 'key 'value . ('key, 'value) gtdata -> 'key -> 'value
  =
  fun u ->
    fun k ->
      let uu___ = u in
      match uu___ with | Fstarcompiler.Prims.Mkdtuple2 (uu___1, v) -> v
let gtdata_create : 'key 'value . 'key -> 'value -> ('key, 'value) gtdata =
  fun k -> fun v -> Fstarcompiler.Prims.Mkdtuple2 (k, v)
type 't type_of_typ' = Obj.t
type 'l struct1 = Obj.t
type 'l union = Obj.t
type 't type_of_typ = Obj.t
type ('l, 'uuuuu) type_of_struct_field = Obj.t
let (_union_get_key : union_typ -> Obj.t -> Obj.t struct_field) =
  fun l -> fun v -> _gtdata_get_key (Obj.magic v)
let (struct_sel : struct_typ -> Obj.t -> Obj.t struct_field -> Obj.t) =
  fun l -> fun s -> fun f -> FStar_DependentMap.sel (Obj.magic s) f
let (dfst_struct_field :
  struct_typ ->
    (Obj.t struct_field, Obj.t) Fstarcompiler.Prims.dtuple2 -> Prims.string)
  =
  fun s ->
    fun p ->
      let uu___ = p in
      match uu___ with | Fstarcompiler.Prims.Mkdtuple2 (f, uu___1) -> f
type 's struct_literal =
  ('s struct_field, Obj.t) Fstarcompiler.Prims.dtuple2 Prims.list
let (struct_literal_wf : struct_typ -> Obj.t struct_literal -> Prims.bool) =
  fun s ->
    fun l ->
      (FStar_List_Tot_Base.sortWith FStar_String.compare
         (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst s.fields))
        =
        (FStar_List_Tot_Base.sortWith FStar_String.compare
           (FStar_List_Tot_Base.map (dfst_struct_field s) l))
let (fun_of_list :
  struct_typ -> Obj.t struct_literal -> Obj.t struct_field -> Obj.t) =
  fun s ->
    fun l ->
      fun f ->
        let f' = f in
        let phi p = (dfst_struct_field s p) = f' in
        match FStar_List_Tot_Base.find phi l with
        | FStar_Pervasives_Native.Some p ->
            let uu___ = p in
            (match uu___ with
             | Fstarcompiler.Prims.Mkdtuple2 (uu___1, v) -> v)
        | uu___ -> FStar_Pervasives.false_elim ()
let (struct_upd :
  struct_typ -> Obj.t -> Obj.t struct_field -> Obj.t -> Obj.t) =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun l ->
             fun s ->
               fun f ->
                 fun v ->
                   Obj.magic (FStar_DependentMap.upd (Obj.magic s) f v))
            uu___3 uu___2 uu___1 uu___
let (struct_create_fun :
  struct_typ -> (Obj.t struct_field -> Obj.t) -> Obj.t) =
  fun uu___1 ->
    fun uu___ ->
      (fun l -> fun f -> Obj.magic (FStar_DependentMap.create f)) uu___1
        uu___
let (struct_create : struct_typ -> Obj.t struct_literal -> Obj.t) =
  fun s -> fun l -> struct_create_fun s (fun_of_list s l)
let (union_get_value : union_typ -> Obj.t -> Obj.t struct_field -> Obj.t) =
  fun l -> fun v -> fun fd -> gtdata_get_value (Obj.magic v) fd
let (union_create : union_typ -> Obj.t struct_field -> Obj.t -> Obj.t) =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun l -> fun fd -> fun v -> Obj.magic (gtdata_create fd v)) uu___2
          uu___1 uu___
let rec (dummy_val : typ -> Obj.t) =
  fun t ->
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
        Obj.repr
          (FStar_Seq_Base.create (FStar_UInt32.v length) (dummy_val t1))
    | TPointer t1 ->
        Obj.repr
          (Pointer (t1, FStar_Monotonic_HyperStack.dummy_aref, PathBase))
    | TNPointer t1 -> Obj.repr NullPtr
    | TBuffer t1 ->
        Obj.repr
          (Buffer
             ((BufferRootSingleton
                 (Pointer
                    (t1, FStar_Monotonic_HyperStack.dummy_aref, PathBase))),
               Stdint.Uint32.zero, Stdint.Uint32.one))
type 't otype_of_typ = Obj.t
type ('l, 'uuuuu) otype_of_struct_field = Obj.t
type 'l ostruct =
  ('l struct_field, Obj.t) FStar_DependentMap.t
    FStar_Pervasives_Native.option
let (ostruct_sel :
  struct_typ -> Obj.t ostruct -> Obj.t struct_field -> Obj.t) =
  fun l ->
    fun s ->
      fun f ->
        FStar_DependentMap.sel
          (FStar_Pervasives_Native.__proj__Some__item__v s) f
let (ostruct_upd :
  struct_typ -> Obj.t ostruct -> Obj.t struct_field -> Obj.t -> Obj.t ostruct)
  =
  fun l ->
    fun s ->
      fun f ->
        fun v ->
          FStar_Pervasives_Native.Some
            (FStar_DependentMap.upd
               (FStar_Pervasives_Native.__proj__Some__item__v s) f v)
let (ostruct_create :
  struct_typ -> (Obj.t struct_field -> Obj.t) -> Obj.t ostruct) =
  fun l ->
    fun f -> FStar_Pervasives_Native.Some (FStar_DependentMap.create f)
type 'l ounion =
  ('l struct_field, Obj.t) gtdata FStar_Pervasives_Native.option
let (ounion_get_key : union_typ -> Obj.t ounion -> Obj.t struct_field) =
  fun l ->
    fun v ->
      _gtdata_get_key (FStar_Pervasives_Native.__proj__Some__item__v v)
let (ounion_get_value :
  union_typ -> Obj.t ounion -> Obj.t struct_field -> Obj.t) =
  fun l ->
    fun v ->
      fun fd ->
        gtdata_get_value (FStar_Pervasives_Native.__proj__Some__item__v v) fd
let (ounion_create :
  union_typ -> Obj.t struct_field -> Obj.t -> Obj.t ounion) =
  fun l ->
    fun fd -> fun v -> FStar_Pervasives_Native.Some (gtdata_create fd v)
let (struct_field_is_readable :
  struct_typ ->
    (typ -> Obj.t -> Prims.bool) ->
      Obj.t ostruct -> Prims.string -> Prims.bool)
  =
  fun l ->
    fun ovalue_is_readable ->
      fun v ->
        fun s ->
          if
            FStar_List_Tot_Base.mem s
              (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l.fields)
          then
            ovalue_is_readable (typ_of_struct_field l s) (ostruct_sel l v s)
          else true
let rec (ovalue_is_readable : typ -> Obj.t -> Prims.bool) =
  fun t ->
    fun v ->
      match t with
      | TStruct l ->
          let v1 = Obj.magic v in
          (FStar_Pervasives_Native.uu___is_Some v1) &&
            (let keys =
               FStar_List_Tot_Base.map FStar_Pervasives_Native.fst l.fields in
             let pred t' = fun v2 -> ovalue_is_readable t' v2 in
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
let (ostruct_field_of_struct_field :
  struct_typ ->
    (typ -> Obj.t -> Obj.t) -> Obj.t -> Obj.t struct_field -> Obj.t)
  =
  fun l ->
    fun ovalue_of_value ->
      fun v ->
        fun f -> ovalue_of_value (typ_of_struct_field l f) (struct_sel l v f)
let rec (ovalue_of_value : typ -> Obj.t -> Obj.t) =
  fun t ->
    fun v ->
      match t with
      | TStruct l ->
          Obj.repr
            (let oval t' = fun v' -> ovalue_of_value t' v' in
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
let rec (value_of_ovalue : typ -> Obj.t -> Obj.t) =
  fun t ->
    fun v ->
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
let (none_ovalue : typ -> Obj.t) =
  fun t ->
    match t with
    | TStruct l -> Obj.repr FStar_Pervasives_Native.None
    | TArray (len, t') -> Obj.repr FStar_Pervasives_Native.None
    | TUnion l -> Obj.repr FStar_Pervasives_Native.None
    | TBase b -> Obj.repr FStar_Pervasives_Native.None
    | TPointer t' -> Obj.repr FStar_Pervasives_Native.None
    | TNPointer t' -> Obj.repr FStar_Pervasives_Native.None
    | TBuffer t' -> Obj.repr FStar_Pervasives_Native.None
let (step_sel : typ -> typ -> Obj.t -> (Obj.t, Obj.t) step -> Obj.t) =
  fun from ->
    fun to1 ->
      fun m' ->
        fun s ->
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
let rec (path_sel : typ -> typ -> Obj.t -> (Obj.t, Obj.t) path -> Obj.t) =
  fun from ->
    fun to1 ->
      fun m ->
        fun p ->
          match p with
          | PathBase -> m
          | PathStep (through', to', p', s) ->
              let m' = path_sel from through' m p' in
              step_sel through' to' m' s
let (step_upd : typ -> typ -> Obj.t -> (Obj.t, Obj.t) step -> Obj.t -> Obj.t)
  =
  fun from ->
    fun to1 ->
      fun m ->
        fun s ->
          fun v ->
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
                   | FStar_Pervasives_Native.Some uu___ ->
                       ostruct_upd l m1 fd v)
            | StepCell (len, uu___, i) ->
                Obj.repr
                  (let m1 = Obj.magic m in
                   match m1 with
                   | FStar_Pervasives_Native.None ->
                       let phi j =
                         if j = (FStar_UInt32.v i)
                         then v
                         else none_ovalue to1 in
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
let rec (path_upd :
  typ -> typ -> Obj.t -> (Obj.t, Obj.t) path -> Obj.t -> Obj.t) =
  fun from ->
    fun to1 ->
      fun m ->
        fun p ->
          fun v ->
            match p with
            | PathBase -> v
            | PathStep (through', to', p', st) ->
                let s = path_sel from through' m p' in
                path_upd from through' m p' (step_upd through' to' s st v)
let rec (path_concat :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path -> (Obj.t, Obj.t) path -> (Obj.t, Obj.t) path)
  =
  fun from ->
    fun through ->
      fun to1 ->
        fun p ->
          fun q ->
            match q with
            | PathBase -> p
            | PathStep (through', to', q', st) ->
                PathStep
                  (through', to', (path_concat from through through' p q'),
                    st)
let rec (path_length : typ -> typ -> (Obj.t, Obj.t) path -> Prims.nat) =
  fun from ->
    fun to1 ->
      fun p ->
        match p with
        | PathBase -> Prims.int_zero
        | PathStep (uu___, uu___1, p', uu___2) ->
            Prims.int_one + (path_length from uu___ p')
let (step_eq :
  typ ->
    typ -> typ -> (Obj.t, Obj.t) step -> (Obj.t, Obj.t) step -> Prims.bool)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun s1 ->
          fun s2 ->
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
let (uu___is_PathDisjointStep :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> Prims.bool)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointStep (through, to11, to21, p, s1, s2) -> true
              | uu___ -> false
let (__proj__PathDisjointStep__item__through :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> typ)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointStep (through, to11, to21, p, s1, s2) -> through
let (__proj__PathDisjointStep__item__to1 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> typ)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointStep (through, to11, to21, p, s1, s2) -> to11
let (__proj__PathDisjointStep__item__to2 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> typ)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointStep (through, to11, to21, p, s1, s2) -> to21
let (__proj__PathDisjointStep__item__p :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t ->
              (Obj.t, Obj.t) path)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointStep (through, to11, to21, p, s1, s2) -> p
let (__proj__PathDisjointStep__item__s1 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t ->
              (Obj.t, Obj.t) step)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointStep (through, to11, to21, p, s1, s2) -> s1
let (__proj__PathDisjointStep__item__s2 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t ->
              (Obj.t, Obj.t) step)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointStep (through, to11, to21, p, s1, s2) -> s2
let (uu___is_PathDisjointIncludes :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> Prims.bool)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> true
              | uu___ -> false
let (__proj__PathDisjointIncludes__item__to1 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> typ)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> to11
let (__proj__PathDisjointIncludes__item__to2 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> typ)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> to21
let (__proj__PathDisjointIncludes__item__p1 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t ->
              (Obj.t, Obj.t) path)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> p11
let (__proj__PathDisjointIncludes__item__p2 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t ->
              (Obj.t, Obj.t) path)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> p21
let (__proj__PathDisjointIncludes__item__to1' :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> typ)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> to1'
let (__proj__PathDisjointIncludes__item__to2' :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t -> typ)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> to2'
let (__proj__PathDisjointIncludes__item__p1' :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t ->
              (Obj.t, Obj.t) path)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> p1'
let (__proj__PathDisjointIncludes__item__p2' :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t ->
              (Obj.t, Obj.t) path)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> p2'
let (__proj__PathDisjointIncludes__item___8 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t ->
              (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_t)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointIncludes
                  (to11, to21, p11, p21, to1', to2', p1', p2', _8) -> _8
type ('from, 'value1, 'value2, 'p1, 'p2) path_disjoint = unit
let rec (path_equal :
  typ ->
    typ -> typ -> (Obj.t, Obj.t) path -> (Obj.t, Obj.t) path -> Prims.bool)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
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
let (uu___is_PathDisjointDecomp :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t ->
              Prims.bool)
  =
  fun from ->
    fun value1 -> fun value2 -> fun p1 -> fun p2 -> fun projectee -> true
let (__proj__PathDisjointDecomp__item__d_through :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t -> typ)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointDecomp
                  (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8)
                  -> d_through
let (__proj__PathDisjointDecomp__item__d_p :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t ->
              (Obj.t, Obj.t) path)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointDecomp
                  (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8)
                  -> d_p
let (__proj__PathDisjointDecomp__item__d_v1 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t -> typ)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointDecomp
                  (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8)
                  -> d_v1
let (__proj__PathDisjointDecomp__item__d_s1 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t ->
              (Obj.t, Obj.t) step)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointDecomp
                  (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8)
                  -> d_s1
let (__proj__PathDisjointDecomp__item__d_p1' :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t ->
              (Obj.t, Obj.t) path)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointDecomp
                  (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8)
                  -> d_p1'
let (__proj__PathDisjointDecomp__item__d_v2 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t -> typ)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointDecomp
                  (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8)
                  -> d_v2
let (__proj__PathDisjointDecomp__item__d_s2 :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t ->
              (Obj.t, Obj.t) step)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointDecomp
                  (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8)
                  -> d_s2
let (__proj__PathDisjointDecomp__item__d_p2' :
  typ ->
    typ ->
      typ ->
        (Obj.t, Obj.t) path ->
          (Obj.t, Obj.t) path ->
            (Obj.t, Obj.t, Obj.t, Obj.t, Obj.t) path_disjoint_decomp_t ->
              (Obj.t, Obj.t) path)
  =
  fun from ->
    fun value1 ->
      fun value2 ->
        fun p1 ->
          fun p2 ->
            fun projectee ->
              match projectee with
              | PathDisjointDecomp
                  (d_through, d_p, d_v1, d_s1, d_p1', d_v2, d_s2, d_p2', _8)
                  -> d_p2'
let rec (path_destruct_l :
  typ ->
    typ ->
      (Obj.t, Obj.t) path ->
        (typ,
          ((Obj.t, Obj.t) step, (Obj.t, Obj.t) path)
            Fstarcompiler.Prims.dtuple2)
          Fstarcompiler.Prims.dtuple2 FStar_Pervasives_Native.option)
  =
  fun t0 ->
    fun t2 ->
      fun p ->
        match p with
        | PathBase -> FStar_Pervasives_Native.None
        | PathStep (uu___, uu___1, p', s) ->
            (match path_destruct_l t0 uu___ p' with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some
                   (Fstarcompiler.Prims.Mkdtuple2
                      (t2, (Fstarcompiler.Prims.Mkdtuple2 (s, PathBase))))
             | FStar_Pervasives_Native.Some (Fstarcompiler.Prims.Mkdtuple2
                 (t_, Fstarcompiler.Prims.Mkdtuple2 (s_, p_))) ->
                 FStar_Pervasives_Native.Some
                   (Fstarcompiler.Prims.Mkdtuple2
                      (t_,
                        (Fstarcompiler.Prims.Mkdtuple2
                           (s_, (PathStep (uu___, uu___1, p_, s)))))))
let rec (path_equal' :
  typ ->
    typ -> typ -> (Obj.t, Obj.t) path -> (Obj.t, Obj.t) path -> Prims.bool)
  =
  fun from ->
    fun to1 ->
      fun to2 ->
        fun p1 ->
          fun p2 ->
            match path_destruct_l from to1 p1 with
            | FStar_Pervasives_Native.None -> uu___is_PathBase from to2 p2
            | FStar_Pervasives_Native.Some (Fstarcompiler.Prims.Mkdtuple2
                (t1, Fstarcompiler.Prims.Mkdtuple2 (s1, p1'))) ->
                (match path_destruct_l from to2 p2 with
                 | FStar_Pervasives_Native.None -> false
                 | FStar_Pervasives_Native.Some
                     (Fstarcompiler.Prims.Mkdtuple2
                     (t2, Fstarcompiler.Prims.Mkdtuple2 (s2, p2'))) ->
                     (step_eq from t1 t2 s1 s2) &&
                       (path_equal' t1 to1 to2 p1' p2'))
let (_field :
  struct_typ -> Obj.t pointer -> Obj.t struct_field -> Obj.t pointer) =
  fun l ->
    fun p ->
      fun fd ->
        let uu___ = p in
        match uu___ with
        | Pointer (from, contents, p') ->
            let p'1 = p' in
            let p'' =
              PathStep
                ((TStruct l), (typ_of_struct_field l fd), p'1,
                  (StepField (l, fd))) in
            Pointer (from, contents, p'')
let (_cell :
  array_length_t -> typ -> Obj.t pointer -> FStar_UInt32.t -> Obj.t pointer)
  =
  fun length ->
    fun value ->
      fun p ->
        fun i ->
          let uu___ = p in
          match uu___ with
          | Pointer (from, contents, p') ->
              let p'1 = p' in
              let p'' =
                PathStep
                  ((TArray (length, value)), value, p'1,
                    (StepCell (length, value, i))) in
              Pointer (from, contents, p'')
let (_ufield :
  union_typ -> Obj.t pointer -> Obj.t struct_field -> Obj.t pointer) =
  fun l ->
    fun p ->
      fun fd ->
        let uu___ = p in
        match uu___ with
        | Pointer (from, contents, p') ->
            let p'1 = p' in
            let p'' =
              PathStep
                ((TUnion l), (typ_of_struct_field l fd), p'1,
                  (StepUField (l, fd))) in
            Pointer (from, contents, p'')
type ('value, 'p, 'h) unused_in = Obj.t
type pointer_ref_contents = (typ, Obj.t) Fstarcompiler.Prims.dtuple2
type ('value, 'h, 'p) live = Obj.t
type ('value, 'h, 'p) nlive = Obj.t
type ('a, 'h, 'b) readable = unit
type ('l, 'h, 'p, 's) readable_struct_fields' = Obj.t
type ('l, 'h, 'p, 's) readable_struct_fields = Obj.t
type ('l, 'h, 'p, 'fd) is_active_union_field = unit
type ('a, 'h, 'b, 'hu, 'bu) equal_values = unit
let (_singleton_buffer_of_pointer : typ -> Obj.t pointer -> Obj.t buffer) =
  fun t ->
    fun p ->
      let uu___ = p in
      match uu___ with
      | Pointer (from, contents, pth) ->
          (match pth with
           | PathStep (uu___1, uu___2, pth', StepCell (ln, ty, i)) ->
               Buffer
                 ((BufferRootArray (ln, (Pointer (from, contents, pth')))),
                   i, Stdint.Uint32.one)
           | uu___1 ->
               Buffer
                 ((BufferRootSingleton p), Stdint.Uint32.zero,
                   Stdint.Uint32.one))
let (singleton_buffer_of_pointer : typ -> Obj.t pointer -> Obj.t buffer) =
  fun t -> fun p -> _singleton_buffer_of_pointer t p
let (buffer_of_array_pointer :
  typ -> array_length_t -> Obj.t pointer -> Obj.t buffer) =
  fun t ->
    fun length ->
      fun p ->
        Buffer ((BufferRootArray (length, p)), Stdint.Uint32.zero, length)
type ('t, 'h, 'b) buffer_live = Obj.t
type ('t, 'b, 'h) buffer_unused_in = Obj.t
let (sub_buffer :
  typ -> Obj.t buffer -> FStar_UInt32.t -> FStar_UInt32.t -> Obj.t buffer) =
  fun t ->
    fun b ->
      fun i ->
        fun len ->
          Buffer
            ((__proj__Buffer__item__broot t b),
              (FStar_UInt32.add (__proj__Buffer__item__bidx t b) i), len)
let (offset_buffer : typ -> Obj.t buffer -> FStar_UInt32.t -> Obj.t buffer) =
  fun t ->
    fun b ->
      fun i ->
        sub_buffer t b i
          (FStar_UInt32.sub (__proj__Buffer__item__blength t b) i)
let (pointer_of_buffer_cell :
  typ -> Obj.t buffer -> FStar_UInt32.t -> Obj.t pointer) =
  fun t ->
    fun b ->
      fun i ->
        match __proj__Buffer__item__broot t b with
        | BufferRootSingleton p -> p
        | BufferRootArray (uu___, p) ->
            _cell uu___ t p
              (FStar_UInt32.add (__proj__Buffer__item__bidx t b) i)
type ('t, 'h, 'b) buffer_readable' = unit
type ('t, 'h, 'b) buffer_readable = unit
type ('value1, 'value2, 'p1, 'p2) disjoint = Obj.t
type loc_aux =
  | LocBuffer of typ * Obj.t buffer 
  | LocPointer of typ * Obj.t pointer 
let (uu___is_LocBuffer : loc_aux -> Prims.bool) =
  fun projectee ->
    match projectee with | LocBuffer (t, b) -> true | uu___ -> false
let (__proj__LocBuffer__item__t : loc_aux -> typ) =
  fun projectee -> match projectee with | LocBuffer (t, b) -> t
let (__proj__LocBuffer__item__b : loc_aux -> Obj.t buffer) =
  fun projectee -> match projectee with | LocBuffer (t, b) -> b
let (uu___is_LocPointer : loc_aux -> Prims.bool) =
  fun projectee ->
    match projectee with | LocPointer (t, p) -> true | uu___ -> false
let (__proj__LocPointer__item__t : loc_aux -> typ) =
  fun projectee -> match projectee with | LocPointer (t, p) -> t
let (__proj__LocPointer__item__p : loc_aux -> Obj.t pointer) =
  fun projectee -> match projectee with | LocPointer (t, p) -> p
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
let (screate : typ -> Obj.t FStar_Pervasives_Native.option -> Obj.t pointer)
  =
  fun value ->
    fun s ->
      let h0 = FStar_HyperStack_ST.get () in
      let s1 =
        match s with
        | FStar_Pervasives_Native.Some s2 -> ovalue_of_value value s2
        | uu___ -> none_ovalue value in
      let content =
        FStar_HyperStack_ST.salloc
          (Fstarcompiler.Prims.Mkdtuple2 (value, s1)) in
      let aref = FStar_Monotonic_HyperStack.aref_of content in
      let p = Pointer (value, aref, PathBase) in
      let h1 = FStar_HyperStack_ST.get () in p
let (ecreate :
  typ -> unit -> Obj.t FStar_Pervasives_Native.option -> Obj.t pointer) =
  fun t ->
    fun r ->
      fun s ->
        let h0 = FStar_HyperStack_ST.get () in
        let s0 = s in
        let s1 =
          match s with
          | FStar_Pervasives_Native.Some s2 -> ovalue_of_value t s2
          | uu___ -> none_ovalue t in
        let content =
          FStar_HyperStack_ST.ralloc ()
            (Fstarcompiler.Prims.Mkdtuple2 (t, s1)) in
        let aref = FStar_Monotonic_HyperStack.aref_of content in
        let p = Pointer (t, aref, PathBase) in
        let h1 = FStar_HyperStack_ST.get () in p
let (field :
  struct_typ -> Obj.t pointer -> Obj.t struct_field -> Obj.t pointer) =
  fun l -> fun p -> fun fd -> _field l p fd
let (ufield :
  union_typ -> Obj.t pointer -> Obj.t struct_field -> Obj.t pointer) =
  fun l -> fun p -> fun fd -> _ufield l p fd
let (cell :
  array_length_t -> typ -> Obj.t pointer -> FStar_UInt32.t -> Obj.t pointer)
  = fun length -> fun value -> fun p -> fun i -> _cell length value p i
let (reference_of :
  typ ->
    FStar_Monotonic_HyperStack.mem ->
      Obj.t pointer -> pointer_ref_contents FStar_HyperStack.reference)
  =
  fun value ->
    fun h ->
      fun p ->
        let x =
          Obj.magic
            (FStar_Monotonic_HyperStack.reference_of h
               (__proj__Pointer__item__contents value p) () ()) in
        x
let (read : typ -> Obj.t pointer -> Obj.t) =
  fun value ->
    fun p ->
      let h = FStar_HyperStack_ST.get () in
      let r = reference_of value h p in
      FStar_HyperStack_ST.witness_region ();
      FStar_HyperStack_ST.witness_hsref r;
      (let uu___2 = FStar_HyperStack_ST.op_Bang r in
       match uu___2 with
       | Fstarcompiler.Prims.Mkdtuple2 (uu___3, c) ->
           value_of_ovalue value
             (path_sel uu___3 value c (__proj__Pointer__item__p value p)))
let (is_null : typ -> Obj.t npointer -> Prims.bool) =
  fun t -> fun p -> match p with | NullPtr -> true | uu___ -> false
let (owrite : typ -> Obj.t pointer -> Obj.t -> unit) =
  fun a ->
    fun b ->
      fun z ->
        let h0 = FStar_HyperStack_ST.get () in
        let r = reference_of a h0 b in
        FStar_HyperStack_ST.witness_region ();
        FStar_HyperStack_ST.witness_hsref r;
        (let v0 = FStar_HyperStack_ST.op_Bang r in
         let uu___2 = v0 in
         match uu___2 with
         | Fstarcompiler.Prims.Mkdtuple2 (t, c0) ->
             let c1 = path_upd t a c0 (__proj__Pointer__item__p a b) z in
             let v1 = Fstarcompiler.Prims.Mkdtuple2 (t, c1) in
             (FStar_HyperStack_ST.op_Colon_Equals r v1;
              (let h1 = FStar_HyperStack_ST.get () in ())))
let (write : typ -> Obj.t pointer -> Obj.t -> unit) =
  fun a -> fun b -> fun z -> owrite a b (ovalue_of_value a z)
let (write_union_field :
  union_typ -> Obj.t pointer -> Obj.t struct_field -> unit) =
  fun l ->
    fun p ->
      fun fd ->
        let field_t = typ_of_struct_field l fd in
        let vu =
          FStar_Pervasives_Native.Some
            (gtdata_create fd (none_ovalue field_t)) in
        let vu1 = Obj.magic vu in owrite (TUnion l) p vu1
let (read_buffer : typ -> Obj.t buffer -> FStar_UInt32.t -> Obj.t) =
  fun t ->
    fun b ->
      fun i -> let uu___ = pointer_of_buffer_cell t b i in read t uu___
let (write_buffer : typ -> Obj.t buffer -> FStar_UInt32.t -> Obj.t -> unit) =
  fun t ->
    fun b ->
      fun i ->
        fun v -> let uu___ = pointer_of_buffer_cell t b i in write t uu___ v
type ('t, 'blarge, 'bsmall) buffer_includes = unit
type ('uuuuu, 'uuuuu1) cloc_aloc = ('uuuuu, 'uuuuu1) aloc


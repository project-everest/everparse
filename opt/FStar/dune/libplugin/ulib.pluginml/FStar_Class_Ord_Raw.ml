open Fstarcompiler
open Prims
type 'a ord =
  {
  super: 'a FStar_Class_Eq_Raw.deq ;
  cmp: 'a -> 'a -> FStar_Order.order }
let __proj__Mkord__item__super : 'a . 'a ord -> 'a FStar_Class_Eq_Raw.deq =
  fun projectee -> match projectee with | { super; cmp;_} -> super
let __proj__Mkord__item__cmp : 'a . 'a ord -> 'a -> 'a -> FStar_Order.order =
  fun projectee -> match projectee with | { super; cmp;_} -> cmp
let super : 'a . 'a ord -> 'a FStar_Class_Eq_Raw.deq =
  fun projectee -> match projectee with | { super = super1; cmp;_} -> super1
let cmp : 'a . 'a ord -> 'a -> 'a -> FStar_Order.order =
  fun projectee ->
    match projectee with | { super = super1; cmp = cmp1;_} -> cmp1
let ord_eq : 'a . 'a ord -> 'a FStar_Class_Eq_Raw.deq = fun d -> d.super
let op_Less_Question : 'a . 'a ord -> 'a -> 'a -> Prims.bool =
  fun uu___ -> fun x -> fun y -> FStar_Order.uu___is_Lt (cmp uu___ x y)
let op_Greater_Question : 'a . 'a ord -> 'a -> 'a -> Prims.bool =
  fun uu___ -> fun x -> fun y -> FStar_Order.uu___is_Gt (cmp uu___ x y)
let op_Less_Equals_Question : 'a . 'a ord -> 'a -> 'a -> Prims.bool =
  fun uu___ ->
    fun x -> fun y -> Prims.op_Negation (op_Greater_Question uu___ x y)
let op_Greater_Equals_Question : 'a . 'a ord -> 'a -> 'a -> Prims.bool =
  fun uu___ ->
    fun x -> fun y -> Prims.op_Negation (op_Less_Question uu___ x y)
let min : 'a . 'a ord -> 'a -> 'a -> 'a =
  fun uu___ ->
    fun x -> fun y -> if op_Less_Equals_Question uu___ x y then x else y
let max : 'a . 'a ord -> 'a -> 'a -> 'a =
  fun uu___ ->
    fun x -> fun y -> if op_Greater_Equals_Question uu___ x y then x else y
let rec sort : 'a . 'a ord -> 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    fun xs ->
      let rec insert x =
        fun xs1 ->
          match xs1 with
          | [] -> [x]
          | y::ys ->
              if op_Less_Equals_Question uu___ x y
              then x :: y :: ys
              else y :: (insert x ys) in
      match xs with | [] -> [] | x::xs1 -> insert x (sort uu___ xs1)
let sort_by :
  'a . ('a -> 'a -> FStar_Order.order) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun xs ->
      let d =
        {
          super =
            {
              FStar_Class_Eq_Raw.eq =
                (fun a1 -> fun b -> (f a1 b) = FStar_Order.Eq)
            };
          cmp = f
        } in
      sort d xs
let dedup : 'a . 'a ord -> 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    fun xs ->
      let out =
        FStar_List_Tot_Base.fold_left
          (fun out1 ->
             fun x ->
               if
                 FStar_List_Tot_Base.existsb
                   (fun y -> FStar_Class_Eq_Raw.op_Equals (ord_eq uu___) x y)
                   out1
               then out1
               else x :: out1) [] xs in
      FStar_List_Tot_Base.rev out
let rec insert_nodup : 'a . 'a ord -> 'a -> 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    fun x ->
      fun xs ->
        match xs with
        | [] -> [x]
        | y::ys ->
            (match cmp uu___ x y with
             | FStar_Order.Eq -> xs
             | FStar_Order.Lt -> x :: xs
             | FStar_Order.Gt -> y :: (insert_nodup uu___ x ys))
let rec sort_dedup : 'a . 'a ord -> 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    fun xs ->
      match xs with
      | [] -> []
      | x::xs1 -> insert_nodup uu___ x (sort_dedup uu___ xs1)
let ord_list_diff :
  'a .
    'a ord ->
      'a Prims.list -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun uu___ ->
    fun xs ->
      fun ys ->
        let xs1 = sort_dedup uu___ xs in
        let ys1 = sort_dedup uu___ ys in
        let rec go xd =
          fun yd ->
            fun xs2 ->
              fun ys2 ->
                match (xs2, ys2) with
                | (x::xs3, y::ys3) ->
                    (match cmp uu___ x y with
                     | FStar_Order.Lt -> go (x :: xd) yd xs3 (y :: ys3)
                     | FStar_Order.Eq -> go xd yd xs3 ys3
                     | FStar_Order.Gt -> go xd (y :: yd) (x :: xs3) ys3)
                | (xs3, ys3) ->
                    ((FStar_List_Tot_Base.rev_acc xd xs3),
                      (FStar_List_Tot_Base.rev_acc yd ys3)) in
        go [] [] xs1 ys1
let (ord_int : Prims.int ord) =
  { super = FStar_Class_Eq_Raw.int_has_eq; cmp = FStar_Order.compare_int }
let (ord_unit : unit ord) =
  {
    super = FStar_Class_Eq_Raw.unit_has_eq;
    cmp = (fun uu___ -> fun uu___1 -> FStar_Order.Eq)
  }
let (ord_string : Prims.string ord) =
  {
    super = FStar_Class_Eq_Raw.string_has_eq;
    cmp =
      (fun x ->
         fun y -> FStar_Order.order_from_int (FStar_String.compare x y))
  }
let ord_option : 'a . 'a ord -> 'a FStar_Pervasives_Native.option ord =
  fun d ->
    {
      super = (FStar_Class_Eq_Raw.eq_option (ord_eq d));
      cmp =
        (fun x ->
           fun y ->
             match (x, y) with
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                 -> FStar_Order.Eq
             | (FStar_Pervasives_Native.Some uu___,
                FStar_Pervasives_Native.None) -> FStar_Order.Gt
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
                uu___) -> FStar_Order.Lt
             | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some
                y1) -> cmp d x1 y1)
    }
let ord_list : 'a . 'a ord -> 'a Prims.list ord =
  fun d ->
    {
      super = (FStar_Class_Eq_Raw.eq_list (ord_eq d));
      cmp = (fun l1 -> fun l2 -> FStar_Order.compare_list l1 l2 (cmp d))
    }
let ord_either :
  'a 'b .
    'a ord -> 'b ord -> ('a, 'b) Fstarcompiler.FStar_Pervasives.either ord
  =
  fun d1 ->
    fun d2 ->
      {
        super = (FStar_Class_Eq_Raw.eq_either (ord_eq d1) (ord_eq d2));
        cmp =
          (fun x ->
             fun y ->
               match (x, y) with
               | (Fstarcompiler.FStar_Pervasives.Inl uu___,
                  Fstarcompiler.FStar_Pervasives.Inr uu___1) ->
                   FStar_Order.Lt
               | (Fstarcompiler.FStar_Pervasives.Inr uu___,
                  Fstarcompiler.FStar_Pervasives.Inl uu___1) ->
                   FStar_Order.Gt
               | (Fstarcompiler.FStar_Pervasives.Inl x1,
                  Fstarcompiler.FStar_Pervasives.Inl y1) -> cmp d1 x1 y1
               | (Fstarcompiler.FStar_Pervasives.Inr x1,
                  Fstarcompiler.FStar_Pervasives.Inr y1) -> cmp d2 x1 y1)
      }
let ord_tuple2 : 'a 'b . 'a ord -> 'b ord -> ('a * 'b) ord =
  fun d1 ->
    fun d2 ->
      {
        super = (FStar_Class_Eq_Raw.eq_pair (ord_eq d1) (ord_eq d2));
        cmp =
          (fun uu___ ->
             fun uu___1 ->
               match (uu___, uu___1) with
               | ((x1, x2), (y1, y2)) ->
                   FStar_Order.lex (cmp d1 x1 y1)
                     (fun uu___2 -> cmp d2 x2 y2))
      }

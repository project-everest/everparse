open Fstarcompiler
open Prims
type color =
  | R 
  | B 
let (uu___is_R : color -> Prims.bool) =
  fun projectee -> match projectee with | R -> true | uu___ -> false
let (uu___is_B : color -> Prims.bool) =
  fun projectee -> match projectee with | B -> true | uu___ -> false
type 'a t =
  | L 
  | N of (color * 'a t * 'a * 'a t) 
let uu___is_L : 'a . 'a t -> Prims.bool =
  fun projectee -> match projectee with | L -> true | uu___ -> false
let uu___is_N : 'a . 'a t -> Prims.bool =
  fun projectee -> match projectee with | N _0 -> true | uu___ -> false
let __proj__N__item___0 : 'a . 'a t -> (color * 'a t * 'a * 'a t) =
  fun projectee -> match projectee with | N _0 -> _0
let empty : 'a . unit -> 'a t = fun uu___ -> L
let singleton : 'a . 'a -> 'a t = fun x -> N (R, L, x, L)
let is_empty : 'a . 'a t -> Prims.bool = uu___is_L
let balance : 'uuuuu . color -> 'uuuuu t -> 'uuuuu -> 'uuuuu t -> 'uuuuu t =
  fun c ->
    fun l ->
      fun x ->
        fun r ->
          match (c, l, x, r) with
          | (B, N (R, N (R, a, x1, b), y, c1), z, d) ->
              N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
          | (B, a, x1, N (R, N (R, b, y, c1), z, d)) ->
              N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
          | (B, N (R, a, x1, N (R, b, y, c1)), z, d) ->
              N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
          | (B, a, x1, N (R, b, y, N (R, c1, z, d))) ->
              N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
          | (c1, l1, x1, r1) -> N (c1, l1, x1, r1)
let blackroot : 'a . 'a t -> 'a t =
  fun s -> match s with | N (uu___, l, x, r) -> N (B, l, x, r)
let add : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a -> 'a t -> 'a t =
  fun uu___ ->
    fun x ->
      fun s ->
        let rec add' s1 =
          match s1 with
          | L -> N (R, L, x, L)
          | N (c, a1, y, b) ->
              if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
              then balance c (add' a1) y b
              else
                if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
                then balance c a1 y (add' b)
                else s1 in
        blackroot (add' s)
let filter :
  'a . 'a FStar_Class_Ord_Raw.ord -> ('a -> Prims.bool) -> 'a t -> 'a t =
  fun uu___ ->
    fun predicate ->
      fun set ->
        let rec aux acc =
          fun s ->
            match s with
            | L -> acc
            | N (uu___1, l, v, r) ->
                aux (aux (if predicate v then add uu___ v acc else acc) l) r in
        aux (empty ()) set
let rec extract_min : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> ('a t * 'a)
  =
  fun uu___ ->
    fun s ->
      match s with
      | N (uu___1, L, x, r) -> (r, x)
      | N (c, a1, x, b) ->
          let uu___1 = extract_min uu___ a1 in
          (match uu___1 with | (a', y) -> ((balance c a' x b), y))
let rec remove : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a -> 'a t -> 'a t =
  fun uu___ ->
    fun x ->
      fun s ->
        match s with
        | L -> L
        | N (c, l, y, r) ->
            if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
            then balance c (remove uu___ x l) y r
            else
              if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
              then balance c l y (remove uu___ x r)
              else
                if uu___is_L r
                then l
                else
                  (let uu___4 = extract_min uu___ r in
                   match uu___4 with | (r', y') -> balance c l y' r')
let rec mem : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a -> 'a t -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun s ->
        match s with
        | L -> false
        | N (uu___1, a1, y, b) ->
            if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
            then mem uu___ x a1
            else
              if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
              then mem uu___ x b
              else true
let rec elems : 'a . 'a t -> 'a Prims.list =
  fun s ->
    match s with
    | L -> []
    | N (uu___, a1, x, b) ->
        FStar_List_Tot_Base.op_At (elems a1)
          (FStar_List_Tot_Base.op_At [x] (elems b))
let equal : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> 'a t -> Prims.bool =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        FStar_Class_Eq_Raw.op_Equals
          (FStar_Class_Ord_Raw.ord_eq (FStar_Class_Ord_Raw.ord_list uu___))
          (elems s1) (elems s2)
let rec union : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> 'a t -> 'a t =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | L -> s2
        | N (c, a1, x, b) -> union uu___ a1 (union uu___ b (add uu___ x s2))
let inter : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> 'a t -> 'a t =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        let rec aux s11 =
          fun acc ->
            match s11 with
            | L -> acc
            | N (uu___1, a1, x, b) ->
                if mem uu___ x s2
                then add uu___ x (aux a1 (aux b acc))
                else aux a1 (aux b acc) in
        aux s1 L
let rec diff : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> 'a t -> 'a t =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        match s2 with
        | L -> s1
        | N (uu___1, a1, x, b) ->
            diff uu___ (diff uu___ (remove uu___ x s1) a1) b
let rec subset :
  'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> 'a t -> Prims.bool =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | L -> true
        | N (uu___1, a1, x, b) ->
            ((mem uu___ x s2) && (subset uu___ a1 s2)) && (subset uu___ b s2)
let rec for_all : 'a . ('a -> Prims.bool) -> 'a t -> Prims.bool =
  fun p ->
    fun s ->
      match s with
      | L -> true
      | N (uu___, a1, x, b) -> ((p x) && (for_all p a1)) && (for_all p b)
let rec for_any : 'a . ('a -> Prims.bool) -> 'a t -> Prims.bool =
  fun p ->
    fun s ->
      match s with
      | L -> false
      | N (uu___, a1, x, b) -> ((p x) || (for_any p a1)) || (for_any p b)
let from_list : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a Prims.list -> 'a t =
  fun uu___ ->
    fun xs ->
      FStar_List_Tot_Base.fold_left (fun s -> fun e -> add uu___ e s) L xs
let addn : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a Prims.list -> 'a t -> 'a t =
  fun uu___ ->
    fun xs ->
      fun s ->
        FStar_List_Tot_Base.fold_left (fun s1 -> fun e -> add uu___ e s1) s
          xs
let collect :
  'a . 'a FStar_Class_Ord_Raw.ord -> ('a -> 'a t) -> 'a Prims.list -> 'a t =
  fun uu___ ->
    fun f ->
      fun l ->
        FStar_List_Tot_Base.fold_left (fun s -> fun e -> union uu___ (f e) s)
          L l

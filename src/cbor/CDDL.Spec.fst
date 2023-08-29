module CDDL.Spec
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Concise Data Definition Language (RFC 8610)

let typ = (Cbor.raw_data_item -> GTot bool) // GTot needed because of the .cbor control (staged serialization)
let t_choice (t1 t2: typ) : typ = (fun x -> t1 x || t2 x)

// Recursive type (needed by COSE Section 5.1 "Recipient")
let rec rec_typ' (f: (typ -> typ)) (t: Cbor.raw_data_item) : GTot bool (decreases t) =
  f (fun t' -> if FStar.StrongExcludedMiddle.strong_excluded_middle (t' << t) then rec_typ' f t' else false) t

let rec_typ : (typ -> typ) -> typ = rec_typ'

// Appendix D
let any : typ = (fun _ -> true)

let uint : typ = (fun x -> Cbor.Int64? x && Cbor.Int64?.typ x = Cbor.major_type_uint64)
let nint : typ = (fun x -> Cbor.Int64? x && Cbor.Int64?.typ x = Cbor.major_type_neg_int64)
let t_int : typ = uint `t_choice` nint

let bstr : typ = (fun x -> Cbor.String? x && Cbor.String?.typ x = Cbor.major_type_byte_string)
let bytes = bstr
let tstr : typ = (fun x -> Cbor.String? x && Cbor.String?.typ x = Cbor.major_type_text_string)
let text = tstr

let t_false : typ = (fun x -> Cbor.Simple? x && Cbor.Simple?.v x = 20uy)
let t_true : typ = (fun x -> Cbor.Simple? x && Cbor.Simple?.v x = 21uy)
let t_bool : typ = t_choice t_false t_true
let t_nil : typ = (fun x -> Cbor.Simple? x && Cbor.Simple?.v x = 22uy)
let t_null : typ = t_nil
let t_undefined : typ = (fun x -> Cbor.Simple? x && Cbor.Simple?.v x = 23uy)

let t_uint_literal (v: U64.t) : typ = (fun x ->
  uint x &&
  Cbor.Int64?.v x = v
)

// Section 2.1: Groups 

// Groups in array context (Section 3.4)
// General semantics, which would imply backtracking

let array_group1 = ((list Cbor.raw_data_item -> GTot bool) -> list Cbor.raw_data_item -> GTot bool)
let array_group1_empty : array_group1 = fun k -> k
let array_group1_concat (a1 a2: array_group1) : array_group1 = fun k -> a1 (a2 k)
let array_group1_choice (a1 a2: array_group1) : array_group1 = fun k l -> a1 k l || a2 k l

let rec array_group1_zero_or_more' (a: array_group1) (k: (list Cbor.raw_data_item -> GTot bool)) (l: list Cbor.raw_data_item) : GTot bool (decreases (List.Tot.length l)) =
  k l ||
  a (fun l' -> if List.Tot.length l' >= List.Tot.length l then false else array_group1_zero_or_more' a k l') l

let array_group1_zero_or_more : array_group1 -> array_group1 = array_group1_zero_or_more'

let array_group1_item (t: typ) : array_group1 = fun k l -> match l with
  | [] -> false
  | a :: q -> t a && k q

let t_array1 (a: array_group1) : typ = fun x ->
  Cbor.Array? x &&
  a Nil? (Cbor.Array?.v x) 

let nat_up_to (n: nat) : eqtype = (i: nat { i <= n })

let array_group2 = ((l: Seq.seq Cbor.raw_data_item) -> (i: nat_up_to (Seq.length l)) -> list (nat_up_to (Seq.length l)))
let array_group2_empty : array_group2 = (fun _ i -> [i])
let array_group2_concat (a1 a2: array_group2) : array_group2 =
  (fun l i1 ->
    let res1 = a1 l i1 in
    List.Tot.concatMap (fun (i2: nat_up_to (Seq.length l)) -> a2 l i2) res1
  )

let array_group2_choice (a1 a2: array_group2) : array_group2 =
  fun l i -> a1 l i `List.Tot.append` a2 l i

let rec array_group2_zero_or_more' (a: array_group2) (l: Seq.seq Cbor.raw_data_item) (i: nat_up_to (Seq.length l)) : Tot (list (nat_up_to (Seq.length l))) (decreases (Seq.length l - i)) =
  i :: begin
    let r1 = a l i in
    List.Tot.concatMap (fun (i2: nat_up_to (Seq.length l)) ->
      if i2 <= i
      then []
      else array_group2_zero_or_more' a l i2
    )
    r1
  end

(*
let array_group2_item (t: typ) : array_group2 = fun l i ->
  if i = Seq.length l then [] else
  if t (Seq.index l i) then [i + 1] else
  []
*)

let t_array2 (a: array_group2) : typ = fun x ->
  Cbor.Array? x &&
  begin let l = Cbor.Array?.v x in
    List.Tot.length l `List.Tot.mem` a (Seq.seq_of_list l) 0
  end

// Greedy semantics (Appendix A?)

let array_group3 = list Cbor.raw_data_item -> GTot (option (list Cbor.raw_data_item))
let array_group3_empty : array_group3 = Some
let array_group3_concat (a1 a3: array_group3) : array_group3 =
  (fun l ->
    match a1 l with
    | None -> None
    | Some l3 -> a3 l3
  )

let array_group3_choice (a1 a3: array_group3) : array_group3 =
  fun l -> match a1 l with
    | None -> a3 l
    | Some l3 -> Some l3

let rec array_group3_zero_or_more' (a: array_group3) (l: list Cbor.raw_data_item) : GTot (option (list Cbor.raw_data_item)) (decreases (List.Tot.length l)) =
  match a l with
  | None -> Some l
  | Some l' ->
    if List.Tot.length l' >= List.Tot.length l
    then Some l
    else array_group3_zero_or_more' a l'

let array_group3_zero_or_more : array_group3 -> array_group3 = array_group3_zero_or_more'

let array_group3_one_or_more (a: array_group3) : array_group3 =
  a `array_group3_concat` array_group3_zero_or_more a

let array_group3_zero_or_one (a: array_group3) : Tot array_group3 = fun l ->
  match a l with
  | None -> Some l
  | Some l' -> Some l'

let array_group3_item (t: typ) : array_group3 = fun l ->
  match l with
  | [] -> None
  | a :: q -> if t a then Some q else None

let t_array3 (a: array_group3) : typ = fun x ->
  Cbor.Array? x &&
  begin match a (Cbor.Array?.v x) with
  | Some l -> Nil? l
  | _ -> false
  end

// Groups in map context (Section 3.5)

let map_group_entry = (typ & typ)

let matches_map_group_entry
  (ge: map_group_entry)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
: GTot bool
= (fst ge) (fst x) && (snd ge) (snd x)

noeq
type map_group = {
  one: list map_group_entry;
  zero_or_one: list map_group_entry;
  zero_or_more: list map_group_entry;
}

let map_group_empty : map_group = {
  one = [];
  zero_or_one = [];
  zero_or_more = [];
}

// Section 3.5.4: Cut
let cut_map_group_entry (key: typ) (ge: map_group_entry) : map_group_entry =
  (fun x -> fst ge x && not (key x)), snd ge

let cut_map_group (key: typ) (g: map_group) : map_group = {
  one = List.Tot.map (cut_map_group_entry key) g.one;
  zero_or_one = List.Tot.map (cut_map_group_entry key) g.zero_or_one;
  zero_or_more = List.Tot.map (cut_map_group_entry key) g.zero_or_more;
}

let maybe_cut_map_group (ge: map_group_entry) (cut: bool) (g: map_group) : map_group =
  if cut
  then cut_map_group (fst ge) g
  else g

let map_group_cons_one (ge: map_group_entry) (cut: bool) (g: map_group) : map_group =
  let g = maybe_cut_map_group ge cut g in {
    g with
    one = ge :: g.one;
  }

let map_group_cons_zero_or_one (ge: map_group_entry) (cut: bool) (g: map_group) : map_group =
  let g = maybe_cut_map_group ge cut g in {
    g with
    zero_or_one = ge :: g.zero_or_one;
  }

let map_group_cons_zero_or_more (ge: map_group_entry) (cut: bool) (g: map_group) : map_group =
  let g = maybe_cut_map_group ge cut g in {
    g with
    zero_or_more = ge :: g.zero_or_more;
}

let rec matches_list_map_group_entry'
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
  (unmatched: list map_group_entry)
  (l: list map_group_entry)
: GTot (option (list map_group_entry))
  (decreases l)
= match l with
  | [] -> None
  | a :: q ->
    if matches_map_group_entry a x
    then Some (List.Tot.rev_acc unmatched q)
    else matches_list_map_group_entry' x (a :: unmatched) q

let matches_list_map_group_entry
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
  (l: list map_group_entry)
: GTot (option (list map_group_entry))
= matches_list_map_group_entry' x [] l

let rec ghost_list_exists (#a: Type) (f: (a -> GTot bool)) (l: list a): GTot bool = match l with
 | [] -> false
 | hd::tl -> if f hd then true else ghost_list_exists f tl

let rec matches_map_group
  (m: map_group)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item))
: GTot bool
  (decreases x)
= match x with
  | [] -> Nil? m.one
  | a :: q ->
    begin match matches_list_map_group_entry a m.one with
      | None -> false
      | Some one' -> matches_map_group ({m with one = one'}) q
    end ||
    begin match matches_list_map_group_entry a m.zero_or_one with
      | None -> false
      | Some one' -> matches_map_group ({m with zero_or_one = one'}) q
    end || (
      ghost_list_exists (fun x -> matches_map_group_entry x a) m.zero_or_more &&
      matches_map_group m q
    )

// 2.1 specifies "names that turn into the map key text string"
let name_as_text_string (s: Seq.seq U8.t) : typ = (fun x -> tstr x && Cbor.String?.v x = s)

let t_map (m: map_group) : typ = fun x ->
  Cbor.Map? x &&
  matches_map_group m (Cbor.Map?.v x)

// Section 3.6: Tags

let t_tag (tag: U64.t) (t: typ) : typ = fun x ->
  Cbor.Tagged? x &&
  Cbor.Tagged?.tag x = tag &&
  t (Cbor.Tagged?.v x)

// Section 3.7.1: Control .size

let str_size (ty: Cbor.major_type_byte_string_or_text_string) (sz: nat) : typ = fun x ->
  Cbor.String? x &&
  Cbor.String?.typ x = ty &&
  Seq.length (Cbor.String?.v x) = sz

let uint_size (sz: nat) : typ = fun x ->
  Cbor.Int64? x &&
  Cbor.Int64?.typ x = Cbor.major_type_uint64 &&
  U64.v (Cbor.Int64?.v x) < pow2 sz

// Section 3.7.2: Control .cbor
// We parameterize over the CBOR order on which the CBOR parser depends

module LP = LowParse.Spec.Base

let bstr_cbor
  (data_item_order: (Cbor.raw_data_item -> Cbor.raw_data_item -> bool))
  (ty: typ)
: typ = fun x ->
  Cbor.String? x &&
  Cbor.String?.typ x = Cbor.major_type_byte_string &&
  begin match LP.parse (Cbor.parse_data_item data_item_order) (Cbor.String?.v x) with
  | None -> false
  | Some (x', _) -> ty x'
  end

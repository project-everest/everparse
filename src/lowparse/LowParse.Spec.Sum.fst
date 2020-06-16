module LowParse.Spec.Sum
include LowParse.Spec.Enum

module Seq = FStar.Seq

let synth_case_recip'
    (#key: eqtype)
    (#repr: eqtype)
    (e: enum key repr)
    (#data: Type)
    (tag_of_data: (data -> Tot (enum_key e)))
    (type_of_tag: (enum_key e -> Tot Type))
    (synth_case_recip: ((k: enum_key e) -> (x: refine_with_tag tag_of_data k) -> Tot (type_of_tag k)))
    (x: data)
: GTot (type_of_tag (tag_of_data x))
= synth_case_recip (tag_of_data x) x

noeq
type sum =
| Sum:
    (key: eqtype) ->
    (repr: eqtype) ->
    (e: enum key repr) ->
    (data: Type) ->
    (tag_of_data: (data -> Tot (enum_key e))) ->
    (type_of_tag: (enum_key e -> Tot Type)) ->
    (synth_case: ((x: enum_key e) -> (y: type_of_tag x) -> Tot (refine_with_tag tag_of_data x))) ->
    (synth_case_recip: ((k: enum_key e) -> (x: refine_with_tag tag_of_data k) -> Tot (type_of_tag k))) ->
    (synth_case_recip_synth_case: (
      (x: enum_key e) ->
      (y: type_of_tag x) ->
      Lemma
      (synth_case_recip' e tag_of_data type_of_tag synth_case_recip (synth_case x y) == y)
    )) ->
    (synth_case_synth_case_recip: (
      (x: data) ->
      Lemma
      (synth_case (tag_of_data x) (synth_case_recip' e tag_of_data type_of_tag synth_case_recip x) == x)
    )) ->
    sum

inline_for_extraction
let sum_key_type (t: sum) : Tot eqtype =
  match t with (Sum key _ _ _ _ _ _ _ _ _) -> key

inline_for_extraction
let sum_repr_type (t: sum) : Tot eqtype =
  match t with (Sum _ repr _ _ _ _ _ _ _ _) -> repr

inline_for_extraction
let sum_enum (t: sum) : Tot (enum (sum_key_type t) (sum_repr_type t)) =
  match t with (Sum _ _ e _ _ _ _ _ _ _) -> e

inline_for_extraction
let sum_key (t: sum) : Tot Type =
  enum_key (sum_enum t)

inline_for_extraction
let sum_key_type_of_sum_key (t: sum) (k: sum_key t) : Pure (sum_key_type t)
  (requires True)
  (ensures (fun k' -> k' == (k <: sum_key_type t)))
= k

inline_for_extraction
let sum_type (t: sum) : Tot Type =
  match t with
  | Sum _ _ _ data _ _ _ _ _ _ -> data

inline_for_extraction
let sum_tag_of_data (t: sum) : Tot ((x: sum_type t) -> Tot (sum_key t)) =
  match t with
  | Sum _ _ _ _ tag_of_data _ _ _ _ _ -> tag_of_data

inline_for_extraction
let sum_cases (t: sum) (x: sum_key t) : Type =
  refine_with_tag #(sum_key t) #(sum_type t) (sum_tag_of_data t) x

inline_for_extraction
let sum_type_of_tag (t: sum) : (x: sum_key t) -> Type =
  match t with
  | Sum _ _ _ _ _ type_of_tag _ _ _ _ -> type_of_tag

let weaken_parse_cases_kind
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
: Tot parser_kind
= let keys : list (sum_key_type s) = List.Tot.map fst (sum_enum s) in
  glb_list_of #(sum_key_type s) (fun (x: sum_key_type s) ->
    if List.Tot.mem x keys
    then let (| k, _ |) = f x in k
    else default_parser_kind
  ) (List.Tot.map fst (sum_enum s))

inline_for_extraction
let synth_sum_case (s: sum) : (k: sum_key s) -> (x: sum_type_of_tag s k) -> Tot (sum_cases s k) =
  match s with
  | Sum _ _ _ _ _ _ synth_case _ _ _ -> synth_case

let synth_sum_case_injective (s: sum) (k: sum_key s) : Lemma
  (synth_injective (synth_sum_case s k))
= Classical.forall_intro (Sum?.synth_case_recip_synth_case s k)

let parse_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
  (x: sum_key s)
: Tot (parser (weaken_parse_cases_kind s f) (sum_cases s x))
= synth_sum_case_injective s x;
  weaken (weaken_parse_cases_kind s f) (dsnd (f x)) `parse_synth` (synth_sum_case s x)

let parse_sum_cases_eq
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
  (x: sum_key s)
  (input: bytes)
: Lemma
  (parse (parse_sum_cases s f x) input == (match parse (dsnd (f x)) input with
  | None -> None
  | Some (y, consumed) -> Some (synth_sum_case s x y, consumed)
  ))
= synth_sum_case_injective s x;
  parse_synth_eq (weaken (weaken_parse_cases_kind s f) (dsnd (f x))) (synth_sum_case s x) input

let parse_sum_cases'
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
  (x: sum_key s)
: Tot (parser (dfst (f x)) (sum_cases s x))
=
  synth_sum_case_injective s x;
  dsnd (f x) `parse_synth` synth_sum_case s x

let parse_sum_cases_eq'
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
  (x: sum_key s)
  (input: bytes)
: Lemma
  (parse (parse_sum_cases s f x) input == parse (parse_sum_cases' s f x) input)
= synth_sum_case_injective s x;
  parse_synth_eq (weaken (weaken_parse_cases_kind s f) (dsnd (f x))) (synth_sum_case s x) input;
  parse_synth_eq (dsnd (f x)) (synth_sum_case s x) input

let parse_sum'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: Tot (parser (and_then_kind (parse_filter_kind kt) k) (sum_type t))
= parse_tagged_union
    #(parse_filter_kind kt)
    #(sum_key t)
    (parse_enum_key p (sum_enum t))
    #(sum_type t)
    (sum_tag_of_data t)
    #k
    pc

inline_for_extraction
let parse_sum_kind
  (kt: parser_kind)
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
: Tot parser_kind
= and_then_kind (parse_filter_kind kt) (weaken_parse_cases_kind t pc)

let parse_sum
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
: Tot (parser (parse_sum_kind kt t pc) (sum_type t))
= parse_sum' t p (parse_sum_cases t pc)

let parse_sum_eq'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (input: bytes)
: Lemma
  (parse (parse_sum t p pc) input == (match parse (parse_enum_key p (sum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match
//      parse (synth_sum_case_injective t k; parse_synth (dsnd (pc k)) (synth_sum_case t k)) input_k
      parse (parse_sum_cases' t pc k) input_k
    with
    | None -> None
    | Some (x, consumed_x) -> Some ((x <: sum_type t), consumed_k + consumed_x)
    end
  ))
= parse_tagged_union_eq_gen
    #(parse_filter_kind kt)
    #(sum_key t)
    (parse_enum_key p (sum_enum t))
    #(sum_type t)
    (sum_tag_of_data t)
    (parse_sum_cases t pc)
    (parse_enum_key p (sum_enum t))
    (fun input -> ())
    (fun k -> dfst (pc k))
    (parse_sum_cases' t pc)
    (fun k input -> parse_sum_cases_eq' t pc k input)
    input

let parse_sum_eq
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (input: bytes)
: Lemma
  (parse (parse_sum t p pc) input == (match parse (parse_enum_key p (sum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match parse (dsnd (pc k)) input_k with
    | None -> None
    | Some (x, consumed_x) -> Some ((synth_sum_case t k x <: sum_type t), consumed_k + consumed_x)
    end
  ))
= parse_sum_eq' t p pc input;
  match parse (parse_enum_key p (sum_enum t)) input with
  | None -> ()
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    synth_sum_case_injective t k;
    parse_synth_eq (dsnd (pc k)) (synth_sum_case t k) input_k

let parse_sum_eq''
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (input: bytes)
: Lemma
  (parse (parse_sum t p pc) input == (match parse p input with
  | None -> None
  | Some (k', consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    let k = maybe_enum_key_of_repr (sum_enum t) k' in
    begin match k with
    | Known k ->
      begin match parse (dsnd (pc k)) input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((synth_sum_case t k x <: sum_type t), consumed_k + consumed_x)
      end
    | _ -> None
    end
  ))
= parse_sum_eq t p pc input;
  parse_enum_key_eq p (sum_enum t) input

inline_for_extraction
let synth_sum_case_recip (s: sum) (k: sum_key s) (x: sum_cases s k) : Tot (sum_type_of_tag s k) =
  match s with (Sum _ _ _ _ _ _ _ synth_case_recip _ _) ->
  synth_case_recip k x

let synth_sum_case_inverse (s: sum) (k: sum_key s) : Lemma
  (synth_inverse (synth_sum_case s k) (synth_sum_case_recip s k))
= Classical.forall_intro (Sum?.synth_case_synth_case_recip s)

let serialize_sum_cases'
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
  (sr: (x: sum_key s) -> Tot (serializer (dsnd (f x))))
  (x: sum_key s)
: Tot (serializer (parse_sum_cases' s f x))
= synth_sum_case_injective s x;
  synth_sum_case_inverse s x;
    (serialize_synth
      _
      (synth_sum_case s x)
      (sr x)
      (synth_sum_case_recip s x)
      ()
    )

let serialize_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
  (sr: (x: sum_key s) -> Tot (serializer (dsnd (f x))))
  (x: sum_key s)
: Tot (serializer (parse_sum_cases s f x))
= Classical.forall_intro (parse_sum_cases_eq' s f x);
  serialize_ext
    (parse_sum_cases' s f x)
    (serialize_sum_cases' s f sr x)
    (parse_sum_cases s f x)

let serialize_sum'
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (pc x))))
: Pure (serializer (parse_sum' t p pc))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_tagged_union
    #(parse_filter_kind kt)
    #(sum_key t)
    #(parse_enum_key p (sum_enum t))
    (serialize_enum_key p s (sum_enum t))
    #(sum_type t)
    (sum_tag_of_data t)
    #k
    #pc
    sc

let serialize_sum
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
: Pure (serializer (parse_sum t p pc))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= // FIXME: WHY WHY WHY is implicit argument inference failing here? (i.e. introducing an eta-expansion)
  serialize_sum' t s #_ #(parse_sum_cases t pc) (serialize_sum_cases t pc sc)

let serialize_sum_eq
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (x: sum_type t)
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (
    serialize (serialize_sum t s sc) x == (
    let tg = sum_tag_of_data t x in
    serialize (serialize_enum_key _ s (sum_enum t)) tg `Seq.append`
    serialize (sc tg) (synth_sum_case_recip t tg x)
  )))
= let tg = sum_tag_of_data t x in
  synth_sum_case_injective t tg;
  synth_sum_case_inverse t tg;
  serialize_synth_eq (dsnd (pc tg)) (synth_sum_case t tg) (sc tg)  (synth_sum_case_recip t tg) () x

inline_for_extraction
let make_sum
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> Tot (enum_key e)))
: Tot (
    (type_of_tag: (enum_key e -> Tot Type)) ->
    (synth_case: ((x: enum_key e) -> (y: type_of_tag x) -> Tot (refine_with_tag tag_of_data x))) ->
    (synth_case_recip: ((k: enum_key e) -> (x: refine_with_tag tag_of_data k) -> Tot (type_of_tag k))) ->
    (synth_case_recip_synth_case: (
      (x: enum_key e) ->
      (y: type_of_tag x) ->
      Lemma
      (synth_case_recip' e tag_of_data type_of_tag synth_case_recip (synth_case x y) == y)
    )) ->
    (synth_case_synth_case_recip: (
      (x: data) ->
      Lemma
      (synth_case (tag_of_data x) (synth_case_recip' e tag_of_data type_of_tag synth_case_recip x) == x)
    )) ->
  Tot sum)
= Sum key repr e data tag_of_data

let synth_case_recip_synth_case_post
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> Tot (enum_key e)))
  (type_of_tag: (enum_key e -> Tot Type))
  (synth_case: ((x: enum_key e) -> (y: type_of_tag x) -> Tot (refine_with_tag tag_of_data x)))
  (synth_case_recip: ((k: enum_key e) -> (x: refine_with_tag tag_of_data k) -> Tot (type_of_tag k)))
  (x: key)
: GTot Type0
= 
  list_mem x (list_map fst e) ==> (
    forall (y: type_of_tag x) . {:pattern (synth_case_recip' e tag_of_data type_of_tag synth_case_recip (synth_case x y))}
    synth_case_recip' e tag_of_data type_of_tag synth_case_recip (synth_case x y) == y
  )

inline_for_extraction
let make_sum'
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> Tot (enum_key e)))
  (type_of_tag: (enum_key e -> Tot Type))
  (synth_case: ((x: enum_key e) -> (y: type_of_tag x) -> Tot (refine_with_tag tag_of_data x)))
  (synth_case_recip: ((k: enum_key e) -> (x: refine_with_tag tag_of_data k) -> Tot (type_of_tag k)))
  (synth_case_recip_synth_case: (
    (x: key) ->
    Tot (squash (synth_case_recip_synth_case_post e tag_of_data type_of_tag synth_case synth_case_recip x))
  ))
  (synth_case_synth_case_recip: (
      (x: data) ->
      Tot (squash
      (synth_case (tag_of_data x) (synth_case_recip' e tag_of_data type_of_tag synth_case_recip x) == x))
  ))
: Tot sum
= make_sum e tag_of_data type_of_tag synth_case synth_case_recip (fun x y ->
  let sq : squash (synth_case_recip_synth_case_post e tag_of_data type_of_tag synth_case synth_case_recip x) =
  synth_case_recip_synth_case x in
  assert (synth_case_recip'  e tag_of_data type_of_tag synth_case_recip (synth_case x y) == y))
  (fun x -> let _ = synth_case_synth_case_recip x in assert (synth_case (tag_of_data x) (synth_case_recip' e tag_of_data type_of_tag synth_case_recip x) == x))

(* Sum with default case *)

inline_for_extraction
let dsum_type_of_tag'
  (#key: eqtype)
  (#repr: eqtype)
  (e: enum key repr)
  (type_of_known_tag: (enum_key e -> Tot Type))
  (type_of_unknown_tag: Type)
  (k: maybe_enum_key e)
: Type
= match k with
  | Unknown _ -> type_of_unknown_tag
  | Known k -> type_of_known_tag k

let synth_dsum_case'
  (#key: eqtype)
  (#repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> GTot (maybe_enum_key e)))
  (type_of_known_tag: (enum_key e -> Tot Type))
  (type_of_unknown_tag: Type)
  (synth_known_case: ((x: enum_key e) -> (y: type_of_known_tag x) -> Tot (refine_with_tag tag_of_data (Known x))))
  (synth_unknown_case: ((x: unknown_enum_repr e) -> type_of_unknown_tag -> Tot (refine_with_tag tag_of_data (Unknown x))))
  (xy: (x: maybe_enum_key e & dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x))
: GTot data
= let (| x, y |) = xy in
  match x with
  | Unknown x -> synth_unknown_case x y
  | Known x -> synth_known_case x y

let synth_dsum_case_recip'
  (#key: eqtype)
  (#repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> GTot (maybe_enum_key e)))
  (type_of_known_tag: (enum_key e -> Tot Type))
  (type_of_unknown_tag: Type)
  (synth_case_recip: ((k: maybe_enum_key e) -> (refine_with_tag tag_of_data k) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag k)))
  (y: data)
: GTot (x: maybe_enum_key e & dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x)
= let tg = tag_of_data y in
  (| tg, synth_case_recip tg y |)

noeq
type dsum =
| DSum:
    (key: eqtype) ->
    (repr: eqtype) ->
    (e: enum key repr) ->
    (data: Type) ->
    (tag_of_data: (data -> Tot (maybe_enum_key e))) ->
    (type_of_known_tag: (enum_key e -> Tot Type)) ->
    (type_of_unknown_tag: Type) ->
    (synth_case: ((x: maybe_enum_key e) -> (y: dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x) -> Tot (refine_with_tag tag_of_data x))) ->
    (synth_case_recip: ((k: maybe_enum_key e) -> (refine_with_tag tag_of_data k) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag k))) ->
    (synth_case_recip_synth_case: (
      (x: maybe_enum_key e) ->
      (y: dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x) ->
      Tot (squash
        (synth_case_recip x (synth_case x y) == y)
      )
    )) ->
    (synth_case_synth_case_recip: (
      (x: data) ->
      Tot (squash
        (synth_case (tag_of_data x) (synth_case_recip (tag_of_data x) x) == x)
      )
    )) ->
    dsum

inline_for_extraction
let dsum_key_type (t: dsum) : Tot eqtype =
  match t with (DSum key _ _ _ _ _ _ _ _ _ _) -> key

inline_for_extraction
let dsum_repr_type (t: dsum) : Tot eqtype =
  match t with (DSum _ repr _ _ _ _ _ _ _ _ _) -> repr

inline_for_extraction
let dsum_enum (t: dsum) : Tot (enum (dsum_key_type t) (dsum_repr_type t)) =
  match t with (DSum _ _ e _ _ _ _ _ _ _ _) -> e

inline_for_extraction
let dsum_key (t: dsum) : Tot Type =
  maybe_enum_key (dsum_enum t)

inline_for_extraction
let dsum_known_key (t: dsum) : Tot Type =
  enum_key (dsum_enum t)

inline_for_extraction
let dsum_unknown_key (t: dsum) : Tot Type =
  unknown_enum_repr (dsum_enum t)

inline_for_extraction
let dsum_type (t: dsum) : Tot Type =
  //NS: this was rewritten from `let DSum ... data .. = t in data`
  //to workaround a glitch in desugaring the above, which introduces
  //an additional, unreduced let binding for extraction
  match t with 
  | DSum _ _ _ data _ _ _ _ _ _ _ -> data

inline_for_extraction
let dsum_tag_of_data (t: dsum) : Tot ((x: dsum_type t) -> Tot (dsum_key t)) =
  match t with (DSum _ _ _ _ tag_of_data _ _ _ _ _ _) -> tag_of_data

inline_for_extraction
let dsum_cases (t: dsum) (x: dsum_key t) : Type =
  refine_with_tag #(dsum_key t) #(dsum_type t) (dsum_tag_of_data t) x

inline_for_extraction
let dsum_type_of_known_tag (t: dsum) : Tot ((k: dsum_known_key t) -> Tot Type) =
  match t with (DSum _ _ _ _ _ type_of_known_tag _ _ _ _ _) ->
  type_of_known_tag

inline_for_extraction
let dsum_type_of_unknown_tag (t: dsum) : Tot Type =
  match t with (DSum _ _ _ _ _ _ type_of_unknown_tag _ _ _ _) ->
  type_of_unknown_tag

inline_for_extraction
let dsum_type_of_tag (t: dsum) =
  dsum_type_of_tag' (dsum_enum t) (dsum_type_of_known_tag t) (dsum_type_of_unknown_tag t)

let weaken_parse_dsum_cases_kind
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (k' : parser_kind)
: Tot parser_kind
= let keys : list (dsum_key_type s) = List.Tot.map fst (dsum_enum s) in
  glb_list_of #(dsum_key_type s) (fun (x: dsum_key_type s) ->
    if List.Tot.mem x keys
    then let (| k, _ |) = f x in k
    else k'
  ) (List.Tot.map fst (dsum_enum s)) `glb` k'

let weaken_parse_dsum_cases_kind'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k' : parser_kind)
  (p: parser k' (dsum_type_of_unknown_tag s))
: Tot parser_kind
= weaken_parse_dsum_cases_kind s f k'

inline_for_extraction
let synth_dsum_case
  (s: dsum)
: Tot ((x: dsum_key s) -> dsum_type_of_tag s x -> Tot (refine_with_tag (dsum_tag_of_data s) x))
= match s with DSum _ _ _ _ _ _ _ synth_case _ _ _ -> synth_case

inline_for_extraction
let synth_dsum_case_recip
  (s: dsum)
: Tot ((x: dsum_key s) -> refine_with_tag (dsum_tag_of_data s) x -> Tot (dsum_type_of_tag s x))
= match s with DSum _ _ _ _ _ _ _ _ synth_case_recip _ _ -> synth_case_recip

let synth_dsum_case_injective
  (s: dsum)
  (x: dsum_key s)
: Lemma
  (synth_injective (synth_dsum_case s x))
= let f
    (y1: dsum_type_of_tag s x)
    (y2: dsum_type_of_tag s x)
  : Lemma
    (requires (synth_dsum_case s x y1 == synth_dsum_case s x y2))
    (ensures (y1 == y2))
  = let k1 : squash (synth_dsum_case_recip s x (synth_dsum_case s x y1) == y1) =
      DSum?.synth_case_recip_synth_case s x y1
    in
    let k2 : squash (synth_dsum_case_recip s x (synth_dsum_case s x y2) == y2) =
      DSum?.synth_case_recip_synth_case s x y2
    in
    // FIXME: WHY WHY WHY is this assert necessary?
    assert (synth_dsum_case_recip s x (synth_dsum_case s x y2) == y2);
    ()
  in
  let g
    (y1: dsum_type_of_tag s x)
    (y2: dsum_type_of_tag s x)
  : Lemma
    (synth_dsum_case s x y1 == synth_dsum_case s x y2 ==> y1 == y2)
  = Classical.move_requires (f y1) y2
  in
  Classical.forall_intro_2 g

let parse_dsum_type_of_tag
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (parser (weaken_parse_dsum_cases_kind s f k) (dsum_type_of_tag s x))
= match x with
    | Known x' -> coerce (parser (weaken_parse_dsum_cases_kind s f k) (dsum_type_of_tag s x)) (weaken (weaken_parse_dsum_cases_kind s f k) (dsnd (f x')))
    | Unknown x' -> weaken (weaken_parse_dsum_cases_kind s f k) g <: parser (weaken_parse_dsum_cases_kind s f k) (dsum_type_of_tag s x)

let parse_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (parser (weaken_parse_dsum_cases_kind s f k) (dsum_cases s x))
= synth_dsum_case_injective s x;
  parse_dsum_type_of_tag s f g x `parse_synth` synth_dsum_case s x

let parse_dsum_cases_kind
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot parser_kind
= match x with
  | Known k -> dfst (f k)
  | _ -> k

let parse_dsum_type_of_tag'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (parser (parse_dsum_cases_kind s f g x) (dsum_type_of_tag s x))
= match x with
    | Known x' -> coerce (parser (parse_dsum_cases_kind s f g x) (dsum_type_of_tag s x)) (dsnd (f x'))
    | Unknown x' -> g <: parser (parse_dsum_cases_kind s f g x) (dsum_type_of_tag s x)

let parse_dsum_cases'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (parser (parse_dsum_cases_kind s f g x) (dsum_cases s x))
= synth_dsum_case_injective s x;
  match x with
  | Known x' -> (dsnd (f x') `parse_synth` synth_dsum_case s (Known x')) <: parser (parse_dsum_cases_kind s f g x) (dsum_cases s x)
  | Unknown x' -> g `parse_synth`  synth_dsum_case s (Unknown x') <: parser (parse_dsum_cases_kind s f g x) (dsum_cases s x)

let parse_dsum_cases_eq'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
  (input: bytes)
: Lemma
  (parse (parse_dsum_cases s f g x) input == parse (parse_dsum_cases' s f g x) input)
= synth_dsum_case_injective s x;
  match x with
  | Known x' ->
    parse_synth_eq (weaken (weaken_parse_dsum_cases_kind s f k) (dsnd (f x'))) (synth_dsum_case s x) input;
    parse_synth_eq (dsnd (f x')) (synth_dsum_case s (Known x')) input
  | Unknown x' ->
    parse_synth_eq (weaken (weaken_parse_dsum_cases_kind s f k) g) (synth_dsum_case s x) input;
    parse_synth_eq g (synth_dsum_case s (Unknown x')) input

let parse_dsum'
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
: Tot (parser (and_then_kind kt k) (dsum_type t))
= parse_tagged_union
    #kt
    #(dsum_key t)
    (parse_maybe_enum_key p (dsum_enum t))
    #(dsum_type t)
    (dsum_tag_of_data t)
    #k
    pc

inline_for_extraction
let parse_dsum_kind
  (kt: parser_kind)
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (k: parser_kind)
: Tot parser_kind
= and_then_kind kt (weaken_parse_dsum_cases_kind s f k)

let parse_dsum
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag t))
: Tot (parser (parse_dsum_kind kt t f k) (dsum_type t))
= parse_dsum' t p (parse_dsum_cases t f g)

let parse_dsum_eq''
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (input: bytes)
: Lemma
  (parse (parse_dsum t p f g) input == (match parse p input with
  | None -> None
  | Some (k', consumed_k) ->
    let k = maybe_enum_key_of_repr (dsum_enum t) k' in
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match parse (parse_dsum_cases t f g k) input_k with
    | None -> None
    | Some (x, consumed_x) -> Some ((x <: dsum_type t), consumed_k + consumed_x)
    end
  ))
= parse_tagged_union_eq #(kt) #(dsum_key t) (parse_maybe_enum_key p (dsum_enum t)) #(dsum_type t) (dsum_tag_of_data t) (parse_dsum_cases t f g) input;
  parse_synth_eq p (maybe_enum_key_of_repr (dsum_enum t)) input

let parse_dsum_eq_
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (input: bytes)
: Lemma
  (parse (parse_dsum t p f g) input == (match parse (parse_maybe_enum_key p (dsum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match parse (parse_dsum_cases' t f g k) input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((x <: dsum_type t), consumed_k + consumed_x)
    end
  ))
= parse_tagged_union_eq_gen (parse_maybe_enum_key p (dsum_enum t)) (dsum_tag_of_data t) (parse_dsum_cases t f g) (parse_maybe_enum_key p (dsum_enum t)) (fun input -> ()) (parse_dsum_cases_kind t f g) (parse_dsum_cases' t f g) (fun tg input -> parse_dsum_cases_eq' t f g tg input) input

let parse_dsum_eq'
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (input: bytes)
: Lemma
  (parse (parse_dsum t p f g) input == (match parse p input with
  | None -> None
  | Some (k', consumed_k) ->
    let k = maybe_enum_key_of_repr (dsum_enum t) k' in
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match parse (parse_dsum_cases' t f g k) input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((x <: dsum_type t), consumed_k + consumed_x)
    end
  ))
= parse_dsum_eq_ t p f g input;
  parse_maybe_enum_key_eq p (dsum_enum t) input

let parse_dsum_eq
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (input: bytes)
: Lemma
  (parse (parse_dsum t p f g) input == (match parse (parse_maybe_enum_key p (dsum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match k with
    | Known k' ->
      begin match parse (dsnd (f k')) input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((synth_dsum_case t k x <: dsum_type t), consumed_k + consumed_x)
      end
    | Unknown k' ->
      begin match parse g input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((synth_dsum_case t k x <: dsum_type t), consumed_k + consumed_x)
      end
    end
  ))
= parse_dsum_eq_ t p f g input;
  let j = parse (parse_maybe_enum_key p (dsum_enum t)) input in
  match j with
  | None -> ()
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    synth_dsum_case_injective t k;
    begin match k with
    | Known k_ ->
      parse_synth_eq (dsnd (f k_)) (synth_dsum_case t k) input_k;
      parse_synth_eq (weaken (weaken_parse_dsum_cases_kind t f k') (dsnd (f k_))) (synth_dsum_case t k) input_k
    | Unknown k_ ->
      parse_synth_eq g (synth_dsum_case t k) input_k;
      parse_synth_eq (weaken (weaken_parse_dsum_cases_kind t f k') g) (synth_dsum_case t k) input_k
    end

let parse_dsum_eq3
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (input: bytes)
: Lemma
  (parse (parse_dsum t p f g) input == (match parse p input with
  | None -> None
  | Some (r, consumed_k) ->
    let k = maybe_enum_key_of_repr (dsum_enum t) r in
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match parse (parse_dsum_type_of_tag' t f g k) input_k with
    | None -> None
    | Some (x, consumed_x) -> Some ((synth_dsum_case t k x <: dsum_type t), consumed_k + consumed_x)
    end
  ))
= parse_dsum_eq t p f g input;
  parse_maybe_enum_key_eq p (dsum_enum t) input

let synth_dsum_case_inverse
  (s: dsum)
  (x: dsum_key s)
: Lemma
  (synth_inverse (synth_dsum_case s x) (synth_dsum_case_recip s x))
= let f
    (y: refine_with_tag (dsum_tag_of_data s) (x))
  : Lemma
    (synth_dsum_case s x (synth_dsum_case_recip s x y) == y)
  = DSum?.synth_case_synth_case_recip s y
  in
  Classical.forall_intro f

let serialize_dsum_type_of_tag
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (sg: serializer g)
  (x: dsum_key s)
: Tot (serializer (parse_dsum_type_of_tag s f g x))
= match x with
  | Known x' ->
    serialize_ext (dsnd (f x')) (sr x') (parse_dsum_type_of_tag s f g x)
  | Unknown x' ->
    serialize_ext g sg (parse_dsum_type_of_tag s f g x)

let serialize_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (sg: serializer g)
  (x: dsum_key s)
: Tot (serializer (parse_dsum_cases s f g x))
= synth_dsum_case_injective s x;
  synth_dsum_case_inverse s x;
  serialize_synth
    _
    (synth_dsum_case s x)
    (serialize_dsum_type_of_tag s f sr g sg x)
    (synth_dsum_case_recip s x)
    ()

let serialize_dsum'
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
: Pure (serializer (parse_dsum' t p pc))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_tagged_union
    #(kt)
    #(dsum_key t)
    #(parse_maybe_enum_key p (dsum_enum t))
    (serialize_maybe_enum_key p s (dsum_enum t))
    #(dsum_type t)
    (dsum_tag_of_data t)
    #k
    #pc
    sc

let serialize_dsum
  (#kt: parser_kind)  
  (s: dsum)
  (#pt: parser kt (dsum_repr_type s))
  (st: serializer pt)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (sg: serializer g)
: Pure (serializer (parse_dsum s pt f g))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_dsum' s st #_ #(parse_dsum_cases s f g) (serialize_dsum_cases s f sr g sg)

let synth_dsum_case_recip_synth_case_known_post
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> Tot (maybe_enum_key e)))
  (type_of_known_tag: (enum_key e -> Tot Type))
  (type_of_unknown_tag: Type)
  (synth_case: ((x: maybe_enum_key e) -> (y: dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x) -> Tot (refine_with_tag tag_of_data x)))
  (synth_case_recip: ((k: maybe_enum_key e) -> (refine_with_tag tag_of_data k) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag k)))
  (x: key)
: GTot Type0
= 
  list_mem x (list_map fst e) ==> (
    forall (y: type_of_known_tag x) . {:pattern (synth_case_recip (Known x) (synth_case (Known x) y))}
    synth_case_recip (Known x) (synth_case (Known x) y) == y
  )

let synth_dsum_case_recip_synth_case_unknown_post
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> Tot (maybe_enum_key e)))
  (type_of_known_tag: (enum_key e -> Tot Type))
  (type_of_unknown_tag: Type)
  (synth_case: ((x: maybe_enum_key e) -> (y: dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x) -> Tot (refine_with_tag tag_of_data x)))
  (synth_case_recip: ((k: maybe_enum_key e) -> (refine_with_tag tag_of_data k) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag k)))
  (x: repr)
: GTot Type0
= 
  list_mem x (list_map snd e) == false ==> (
    forall (y: type_of_unknown_tag) . {:pattern (synth_case_recip (Unknown x) (synth_case (Unknown x) y))}
    synth_case_recip (Unknown x) (synth_case (Unknown x) y) == y
  )

inline_for_extraction
let make_dsum
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> Tot (maybe_enum_key e)))
: Tot (
    (type_of_known_tag: (enum_key e -> Tot Type)) ->
    (type_of_unknown_tag: Type) ->
    (synth_case: ((x: maybe_enum_key e) -> (y: dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x) -> Tot (refine_with_tag tag_of_data x))) ->
    (synth_case_recip: ((k: maybe_enum_key e) -> (refine_with_tag tag_of_data k) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag k))) ->
    (synth_case_recip_synth_case: (
      (x: maybe_enum_key e) ->
      (y: dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x) ->
      Tot (squash
        (synth_case_recip x (synth_case x y) == y)
      )
    )) ->
    (synth_case_synth_case_recip: (
      (x: data) ->
      Tot (squash
        (synth_case (tag_of_data x) (synth_case_recip (tag_of_data x) x) == x)
      )
    )) ->
    dsum
  )
= DSum key repr e data tag_of_data

inline_for_extraction
let make_dsum'
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type)
  (tag_of_data: (data -> Tot (maybe_enum_key e)))
  (type_of_known_tag: (enum_key e -> Tot Type))
  (type_of_unknown_tag: Type)
  (synth_case: ((x: maybe_enum_key e) -> (y: dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x) -> Tot (refine_with_tag tag_of_data x)))
  (synth_case_recip: ((k: maybe_enum_key e) -> (refine_with_tag tag_of_data k) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag k)))
  (synth_case_recip_synth_case_known: (
    (x: key) ->
    Tot (squash (synth_dsum_case_recip_synth_case_known_post e tag_of_data type_of_known_tag type_of_unknown_tag synth_case synth_case_recip x))
  ))
  (synth_case_recip_synth_case_unknown: (
    (x: repr) ->
    Tot (squash (synth_dsum_case_recip_synth_case_unknown_post e tag_of_data type_of_known_tag type_of_unknown_tag synth_case synth_case_recip x))
  ))
: Tot (
    (synth_case_synth_case_recip: (
      (x: data) ->
      Tot (squash
        (synth_case (tag_of_data x) (synth_case_recip (tag_of_data x) x) == x)
      )
    )) ->
    dsum
  )
= make_dsum e tag_of_data type_of_known_tag type_of_unknown_tag synth_case synth_case_recip
    (fun x y ->
      match x with
      | Known x' ->
        synth_case_recip_synth_case_known x'
      | Unknown x' ->
        synth_case_recip_synth_case_unknown x'
    )

let serialize_dsum_eq'
  (#kt: parser_kind)  
  (s: dsum)
  (#pt: parser kt (dsum_repr_type s))
  (st: serializer pt)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (sg: serializer g)
  (x: dsum_type s)
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (
    serialize (serialize_dsum s st f sr g sg) x == (
    let tg = dsum_tag_of_data s x in
    serialize (serialize_maybe_enum_key _ st (dsum_enum s)) tg `Seq.append`
    serialize (serialize_dsum_cases s f sr g sg tg) x
  )))
= ()

let serialize_dsum_eq
  (#kt: parser_kind)  
  (s: dsum)
  (#pt: parser kt (dsum_repr_type s))
  (st: serializer pt)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (sg: serializer g)
  (x: dsum_type s)
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (
    serialize (serialize_dsum s st f sr g sg) x == (
    let tg = dsum_tag_of_data s x in
    serialize (serialize_maybe_enum_key _ st (dsum_enum s)) tg `Seq.append` (
    match tg with
    | Known k -> serialize (sr k) (synth_dsum_case_recip s tg x)
    | Unknown k -> serialize sg (synth_dsum_case_recip s tg x)
  ))))
= serialize_dsum_eq' s st f sr g sg x;
  let tg = dsum_tag_of_data s x in
  synth_dsum_case_injective s tg;
  synth_dsum_case_inverse s tg;
    serialize_synth_eq
    _
    (synth_dsum_case s tg)
    (serialize_dsum_type_of_tag s f sr g sg tg)
    (synth_dsum_case_recip s tg)
    ()
    x

(*
let serialize_dsum_upd
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (x: dsum_type t)
  (y: dsum_type t)
: Lemma
  (requires (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    kt.parser_kind_subkind == Some ParserStrong /\
    ty == tx /\
    Seq.length (serialize (sc ty) y) == Seq.length (serialize (sc tx) x)
  ))
  (ensures (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
    let sx' = serialize (serialize_dsum t s sc) x in
    let sy = serialize (sc ty) y in
    tlen + Seq.length sy == Seq.length sx' /\
    serialize (serialize_dsum t s sc) y == seq_upd_seq sx' tlen sy
  ))
=   let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let st = serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx in
    let tlen = Seq.length st in
    let sx' = serialize (serialize_dsum t s sc) x in
    let sx = serialize (sc tx) x in
    let sy = serialize (sc ty) y in 
    let sy' = serialize (serialize_dsum t s sc) y in
    assert (tlen + Seq.length sy == Seq.length sx');
    seq_upd_seq_right sx' sy;
    Seq.lemma_split sx' tlen;
    Seq.lemma_split sy' tlen;
    Seq.lemma_append_inj (Seq.slice sx' 0 tlen) (Seq.slice sx' tlen (Seq.length sx')) st sx;
    Seq.lemma_append_inj (Seq.slice sy' 0 tlen) (Seq.slice sy' tlen (Seq.length sy')) st sy;
    assert (sy' `Seq.equal` seq_upd_seq sx' tlen sy)

#reset-options "--z3refresh --z3rlimit 32 --z3cliopt smt.arith.nl=false"

let serialize_dsum_upd_bw
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (x: dsum_type t)
  (y: dsum_type t)
: Lemma
  (requires (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    kt.parser_kind_subkind == Some ParserStrong /\
    ty == tx /\
    Seq.length (serialize (sc ty) y) == Seq.length (serialize (sc tx) x)
  ))
  (ensures (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
    let sx' = serialize (serialize_dsum t s sc) x in
    let sy = serialize (sc ty) y in
    tlen + Seq.length sy == Seq.length sx' /\
    serialize (serialize_dsum t s sc) y == seq_upd_bw_seq sx' 0 sy
  ))
= serialize_dsum_upd t s sc x y;
  let tx = dsum_tag_of_data t x in
  let ty = dsum_tag_of_data t y in
  let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
  let sx' = serialize (serialize_dsum t s sc) x in
  let sy = serialize (sc ty) y in
  assert (Seq.length sx' - Seq.length sy == tlen)

let serialize_dsum_upd_chain
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (x: dsum_type t)
  (y: dsum_type t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let sx = serialize (sc tx) x in
    kt.parser_kind_subkind == Some ParserStrong /\
    ty == tx /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize (sc ty) y == seq_upd_seq sx i' s'
  ))
  (ensures (
    let tx = dsum_tag_of_data t x in
    let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
    let sx' = serialize (serialize_dsum t s sc) x in
    tlen + Seq.length (serialize (sc tx) x) == Seq.length sx' /\
    tlen + i' + Seq.length s' <= Seq.length sx' /\
    serialize (serialize_dsum t s sc) y == seq_upd_seq sx' (tlen + i') s'
  ))
= serialize_dsum_upd t s sc x y;
  let tx = dsum_tag_of_data t x in
  let sx = serialize (sc tx) x in
  let sx' = serialize (serialize_dsum t s sc) x in
  let st = serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx in
  let tlen = Seq.length st in
  seq_upd_seq_right_to_left sx' tlen sx i' s';
  Seq.lemma_split sx' tlen;
  Seq.lemma_append_inj (Seq.slice sx' 0 tlen) (Seq.slice sx' tlen (Seq.length sx')) st sx;
  seq_upd_seq_seq_upd_seq_slice sx' tlen (Seq.length sx') i' s'

let serialize_dsum_upd_bw_chain
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (x: dsum_type t)
  (y: dsum_type t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let sx = serialize (sc tx) x in
    kt.parser_kind_subkind == Some ParserStrong /\
    ty == tx /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize (sc ty) y == seq_upd_bw_seq sx i' s'
  ))
  (ensures (
    let tx = dsum_tag_of_data t x in
    let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
    let sx' = serialize (serialize_dsum t s sc) x in
    tlen + Seq.length (serialize (sc tx) x) == Seq.length sx' /\
    i' + Seq.length s' <= Seq.length sx' /\
    serialize (serialize_dsum t s sc) y == seq_upd_bw_seq sx' (i') s'
  ))
= let tx = dsum_tag_of_data t x in
  let j' = Seq.length (serialize (sc tx) x) - i' - Seq.length s' in
  serialize_dsum_upd_chain t s sc x y j' s';
  let sx' = serialize (serialize_dsum t s sc) x in
  let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
  assert (tlen + j' == Seq.length sx' - i' - Seq.length s');
  assert (seq_upd_bw_seq sx' i' s' == seq_upd_seq sx' (tlen + j') s');
  ()

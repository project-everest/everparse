module CDDL.Spec.AST.Base
include CDDL.Spec.Attr
include CDDL.Spec.EqTest
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Cbor = CBOR.Spec.API.Type
module Map = CDDL.Spec.Map
module U8 = FStar.UInt8
module Util = CBOR.Spec.Util
module U32 = FStar.UInt32

irreducible let base_attr : unit = ()
irreducible let sem_attr : unit = ()

[@@base_attr]
let u32_of_char (x: FStar.Char.char) : Tot U32.t = FStar.Char.u32_of_char x

[@@base_attr]
let char_is_ascii (c: FStar.Char.char) : Tot bool =
  FStar.UInt32.lt (u32_of_char c) 127ul // because 7F is forbidden

[@@base_attr]
let string_is_ascii (s: string) : Tot bool =
  List.Tot.for_all char_is_ascii (FStar.String.list_of_string s)

let ascii_string : eqtype = (s: string { string_is_ascii s })

unfold
let mk_ascii_string (s: string) (prf: squash (string_is_ascii s)) : Tot ascii_string = s

let test_ascii_string: ascii_string = mk_ascii_string "hello" (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ()))

(* An abstract syntax tree for CDDL. I define it as an OCaml type with
  no constraints, and I move all constraints to `bounded` or `wf`
  Boolean functions. I do that for 2 reasons:
  
  1. so that I can use PpxDeriving.Show (to this end, I had to replace
  all integer types with int, since U8.t and U64.t do not support
  PpxDeriving.Show)
  
  2. as a defensive practice wrt. ill-formed source input. *)

[@@base_attr; PpxDerivingShow; plugin]
type literal =
| LSimple of int
| LInt: (v: int) -> literal // I deduce the integer type from the sign
| LTextString: string -> literal

[@@base_attr]
let cddl_major_type_uint64 : Cbor.major_type_uint64_or_neg_int64 =
  (_ by (FStar.Tactics.exact (FStar.Tactics.norm_term [delta] (`Cbor.cbor_major_type_uint64))))

[@@base_attr]
let cddl_major_type_neg_int64 : Cbor.major_type_uint64_or_neg_int64 =
  (_ by (FStar.Tactics.exact (FStar.Tactics.norm_term [delta] (`Cbor.cbor_major_type_neg_int64))))

[@@base_attr]
let cddl_major_type_byte_string : Cbor.major_type_byte_string_or_text_string =
  (_ by (FStar.Tactics.exact (FStar.Tactics.norm_term [delta] (`Cbor.cbor_major_type_byte_string))))

[@@base_attr]
let cddl_major_type_text_string : Cbor.major_type_byte_string_or_text_string =
  (_ by (FStar.Tactics.exact (FStar.Tactics.norm_term [delta] (`Cbor.cbor_major_type_text_string))))

[@@base_attr; PpxDerivingShow; plugin]
type elem_typ =
| ELiteral of literal
| EBool
| ESimple
| EByteString // TODO: add length constraints, etc.
| ETextString
| EUInt // TODO: add range constraints, etc.
| ENInt
| EAlwaysFalse
| EAny

[@@base_attr]
type name_env_elem =
| NType
| NGroup

[@@base_attr; PpxDerivingShow; plugin]
type group =
| GDef: string -> group
| GElem: (cut: bool) -> (key: typ) -> (value: typ) -> group
| GAlwaysFalse
| GNop
| GZeroOrOne of group
| GZeroOrMore of group
| GOneOrMore of group
| GConcat: group -> group -> group
| GChoice: group -> group -> group

and typ =
| TElem of elem_typ
| TDef of string
| TArray of group
| TMap of group
| TNamed: (name: string) -> (body: typ) -> typ
| TTagged: (tag: option int) -> (body: typ) -> typ
| TChoice: typ -> typ -> typ
| TRange: typ -> inclusive: bool -> typ -> typ
(* Controls: their semantics will use `andp` *)
| TSize: typ -> typ -> typ
| TDetCbor: typ -> typ -> typ

[@@plugin; base_attr; PpxDerivingShow]
type decl =
| DType of typ
| DGroup of group

[@@PpxDerivingShow]
type program = list (string & decl)

(* Environments and well-formedness constraints *)

[@@  base_attr]
let tint = TChoice (TElem EUInt) (TElem ENInt)

type name_env = (string -> Tot (option name_env_elem))


let name_mem (s: string) (e: name_env) : Tot bool = Some? (e s)

let name (e: name_env) : eqtype = (s: string { name_mem s e })

let typ_name (e: name_env) : eqtype = (s: string { e s == Some NType })
let group_name (e: name_env) : eqtype = (s: string { e s == Some NGroup })

[@@  base_attr]
let name_intro (s: string) (e: name_env) (sq: squash (name_mem s e)) : Tot (name e) =
  s


[@@base_attr]
let empty_name_env (_: string) : Tot (option name_env_elem) = None

[@@"opaque_to_smt"] irreducible
let name_empty_elim (t: Type) (x: name empty_name_env) : Tot t = false_elim ()


[@@base_attr]
let extend_name_env (e: name_env) (new_name: string) (elem: name_env_elem) (s: string) : Tot (option name_env_elem) =
  if s = new_name then Some elem else e s

let name_env_included (s1 s2: name_env) : GTot prop =
  (forall (i: name s1) . s2 i == s1 i)

[@@ base_attr ]
let wf_literal
  (l: literal)
: Tot bool
= match l with
| LSimple x -> x >= 0 && x < pow2 8 && Cbor.simple_value_wf (U8.uint_to_t x)
| LInt v -> v >= - pow2 64 && v < pow2 64
| LTextString s -> String.length s < pow2 64 && string_is_ascii s // FIXME: support utf8

[@@base_attr]
let wf_elem_typ
  (t: elem_typ)
: Tot bool
= match t with
  | ELiteral l -> wf_literal l
  | _ -> true

[@@ base_attr]
let rec group_bounded
  (env: name_env)
  (g: group)
: Tot bool
  (decreases g)
= match g with
  | GDef d -> Some? (env d)
  | GElem _ key value -> typ_bounded env key && typ_bounded env value
  | GZeroOrMore g'
  | GZeroOrOne g'
  | GOneOrMore g'
  -> group_bounded env g'
  | GConcat g1 g2
  | GChoice g1 g2
  -> group_bounded env g1 &&
    group_bounded env g2
  | GAlwaysFalse
  | GNop -> true

and typ_bounded
  (env: name_env)
  (t: typ)
: Tot bool
  (decreases t)
= match t with
  | TElem t -> wf_elem_typ t
  | TDef s -> env s = Some NType
  | TArray g -> group_bounded env g
  | TMap g -> group_bounded env g
  | TNamed _ t' -> typ_bounded env t'
  | TTagged v t' ->
    begin match v with
    | None -> true
    | Some v -> 0 <= v && v < pow2 64
    end && typ_bounded env t'
  | TRange t1 _ t2
  | TChoice t1 t2 ->
    typ_bounded env t1 &&
    typ_bounded env t2
  | TSize base range ->
    typ_bounded env base &&
    typ_bounded env range
  | TDetCbor base ctl ->
    typ_bounded env base && // base should be #2 (byte string) but since it can be an alias, such as `bstr` defined in postlude.cddl, this condition cannot be checked without an ast_env
    typ_bounded env ctl

let rec group_bounded_incr
  (env env': name_env)
  (g: group)
: Lemma
  (requires (
    name_env_included env env' /\
    group_bounded env g
  ))
  (ensures (
    group_bounded env' g
  ))
  (decreases g)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (group_bounded env g)];
    [SMTPat (name_env_included env env'); SMTPat (group_bounded env' g)];
  ]]
= match g with
  | GDef _ -> ()
  | GElem _ key value -> typ_bounded_incr env env' key; typ_bounded_incr env env' value
  | GZeroOrMore g'
  | GZeroOrOne g'
  | GOneOrMore g'
  -> group_bounded_incr env env' g'
  | GConcat g1 g2
  | GChoice g1 g2
  -> group_bounded_incr env env' g1; group_bounded_incr env env' g2
  | GAlwaysFalse
  | GNop -> ()

and typ_bounded_incr
  (env env': name_env)
  (t: typ)
: Lemma
  (requires (
    name_env_included env env' /\
    typ_bounded env t
  ))
  (ensures (
    typ_bounded env' t
  ))
  (decreases t)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (typ_bounded env t)];
    [SMTPat (name_env_included env env'); SMTPat (typ_bounded env' t)];
  ]]
= match t with
  | TElem _
  | TDef _
  -> ()
  | TNamed _ t'
  | TTagged _ t' -> typ_bounded_incr env env' t'
  | TArray g -> group_bounded_incr env env' g
  | TMap g -> group_bounded_incr env env' g
  | TSize t1 t2
  | TRange t1 _ t2
  | TDetCbor t1 t2
  | TChoice t1 t2 -> typ_bounded_incr env env' t1; typ_bounded_incr env env' t2

[@@sem_attr]
type int_value =
| SUInt of U64.t
| SNegInt of U64.t

[@@sem_attr]
let eval_int_value
  (x: int_value)
: Tot int
= match x with
  | SUInt v -> U64.v v
  | SNegInt v -> -1 - U64.v v

[@@sem_attr]
let int_value_minus_one
  (x: int_value)
: Pure int_value
    (requires (eval_int_value x > - pow2 64))
    (ensures (fun y ->
      eval_int_value y == eval_int_value x - 1
    ))
= match x with
  | SUInt v -> if v = 0uL then SNegInt (U64.uint_to_t ((-1) - (-1))) else SUInt (U64.sub v 1uL)
  | SNegInt v -> SNegInt (U64.add v 1uL)

[@@  sem_attr]
noeq
type type_sem
= | Sem of Ghost.erased Spec.typ
  | SInt of int_value
  | SIntRange: a: int_value -> b: int_value { eval_int_value a <= eval_int_value b } -> type_sem
// TODO: floats

[@@ sem_attr]
let sem_env_elem
  (kind: name_env_elem)
: Tot Type
= match kind with
  | NType -> type_sem
  | NGroup -> Ghost.erased (Spec.array_group None & Spec.map_group)

[@@  sem_attr]
noeq
type sem_env = {
  se_bound: name_env;
  se_env: ((n: name se_bound) -> Tot (sem_env_elem (Some?.v (se_bound n))));
}

[@@"opaque_to_smt"] irreducible // because of false_elim
let se_env_empty
  (n: name empty_name_env)
: Tot (sem_env_elem (Some?.v (empty_name_env n)))
= false_elim ()

[@@  sem_attr]
let empty_sem_env = {
  se_bound = empty_name_env;
  se_env = se_env_empty;
}

let sem_env_included (s1 s2: sem_env) : GTot prop =
  name_env_included s1.se_bound s2.se_bound /\
  (forall (i: name s1.se_bound) . s1.se_env i == s2.se_env i)

let sem_env_included_trans (s1 s2 s3: sem_env) : Lemma
  (requires (sem_env_included s1 s2 /\ sem_env_included s2 s3))
  (ensures (sem_env_included s1 s3))
  [SMTPat (sem_env_included s1 s3); SMTPat (sem_env_included s1 s2)]
= ()

[@@"opaque_to_smt";  sem_attr]
let sem_env_extend_gen
  (se: sem_env)
  (new_name: string)
  (nelem: name_env_elem)
  (a: sem_env_elem nelem)
: Pure sem_env
    (requires
      (~ (name_mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == extend_name_env se.se_bound new_name nelem /\
      sem_env_included se se' /\
      se'.se_env new_name == a
    )
= let se_bound' = extend_name_env se.se_bound new_name nelem in
  {
    se_bound = se_bound';
    se_env = (fun (i: name se_bound') -> if i = new_name then a else se.se_env i);
  }

(* Semantics *)

[@@base_attr]
let uint32_to_uint8 (x: U32.t) : Tot U8.t =
  FStar.Int.Cast.uint32_to_uint8 x

let byte_list_of_char_list
  (l: list FStar.Char.char)
: Tot (list U8.t)
= List.Tot.map uint32_to_uint8 (List.Tot.map u32_of_char l)

let char_list_of_byte_list
  (l: list U8.t)
: Tot (list FStar.Char.char)
= List.Tot.map FStar.Char.char_of_u32 (List.Tot.map FStar.Int.Cast.uint8_to_uint32 l)

let rec char_list_of_byte_list_of_char_list
  (l: list FStar.Char.char)
: Lemma
  (requires List.Tot.for_all char_is_ascii l)
  (ensures char_list_of_byte_list (byte_list_of_char_list l) == l)
  [SMTPat (byte_list_of_char_list l)]
= match l with
  | [] -> ()
  | a :: q ->
    let a' = u32_of_char a in
    FStar.Math.Lemmas.small_mod (FStar.UInt32.v a') 256;
    assert (FStar.Int.Cast.uint8_to_uint32 (uint32_to_uint8 a') == a');
    char_list_of_byte_list_of_char_list q

let byte_seq_of_ascii_string
  (s: string)
: Tot (Seq.seq U8.t)
= Seq.seq_of_list (byte_list_of_char_list (FStar.String.list_of_string s))

let byte_seq_of_ascii_string_diff
  (s1 s2: ascii_string)
: Lemma
  (ensures (byte_seq_of_ascii_string s1 == byte_seq_of_ascii_string s2 ==> s1 == s2))
= Seq.lemma_seq_to_seq_of_list (byte_list_of_char_list (FStar.String.list_of_string s1));
  Seq.lemma_seq_to_seq_of_list (byte_list_of_char_list (FStar.String.list_of_string s2));
  char_list_of_byte_list_of_char_list (FStar.String.list_of_string s1);
  char_list_of_byte_list_of_char_list (FStar.String.list_of_string s2);
  FStar.String.string_of_list_of_string s1;
  FStar.String.string_of_list_of_string s2

module U8 = FStar.UInt8

let rec byte_seq_of_ascii_string_is_utf8'
  (l: list FStar.Char.char)
: Lemma
  (requires (List.Tot.for_all char_is_ascii l))
  (ensures (
    let s = Seq.seq_of_list (byte_list_of_char_list l) in
    forall i . i < Seq.length s ==> U8.v (Seq.index s i) < 128
  ))
= match l with
  | [] -> ()
  | a :: q ->
    Seq.lemma_seq_of_list_cons a q;
    byte_seq_of_ascii_string_is_utf8' q;
    let c = uint32_to_uint8 (u32_of_char a) in
    assert (U8.v c < 128);
    let s = Seq.seq_of_list (byte_list_of_char_list l) in
    assert (forall i . i < Seq.length s ==>
      Seq.index s i == (if i = 0 then c else Seq.index (Seq.seq_of_list (byte_list_of_char_list q)) (i - 1))
    )

let byte_seq_of_ascii_string_is_utf8
  (s: ascii_string)
: Lemma
  (ensures (CBOR.Spec.API.UTF8.correct (byte_seq_of_ascii_string s)))
  [SMTPat (byte_seq_of_ascii_string s)]
= byte_seq_of_ascii_string_is_utf8' (FStar.String.list_of_string s);
  CBOR.Spec.API.UTF8.ascii_is_utf8 (byte_seq_of_ascii_string s)

[@@ sem_attr ]
let eval_literal
  (l: literal)
: Ghost Cbor.cbor
  (requires wf_literal l)
  (ensures (fun _ -> True))
= match l with
  | LSimple v -> Cbor.pack (Cbor.CSimple (U8.uint_to_t v))
  | LInt v -> Cbor.pack (Cbor.CInt64 (if v < 0 then cddl_major_type_neg_int64 else cddl_major_type_uint64) (U64.uint_to_t (if v < 0 then -1 - v else v)))
  | LTextString s -> Cbor.pack (Cbor.CString (cddl_major_type_text_string) (byte_seq_of_ascii_string s))

[@@ sem_attr ]
let spec_type_of_literal
  (l: literal)
: Ghost Spec.typ
    (requires wf_literal l)
    (ensures fun _ -> True)
= Spec.t_literal (eval_literal l)

[@@ sem_attr ]
let elem_typ_sem
  (t: elem_typ)
: Ghost Spec.typ
    (requires wf_elem_typ t)
    (ensures fun _ -> True)
= match t with
  | ELiteral l -> spec_type_of_literal l
  | EBool -> Spec.t_bool
  | ESimple -> Spec.t_simple
  | EByteString -> Spec.bstr
  | ETextString -> Spec.tstr
  | EUInt -> Spec.uint
  | ENInt -> Spec.nint
  | EAlwaysFalse -> Spec.t_always_false
  | EAny -> Spec.any

[@@ sem_attr ]
let sem_of_type_sem
  (x: type_sem)
: GTot Spec.typ
= match x with
  | Sem v -> v
  | SInt v -> Spec.t_literal (eval_literal (LInt (eval_int_value v)))
  | SIntRange lo hi -> Spec.t_int_range (eval_int_value lo) (eval_int_value hi)

noextract
let t_size
  (ty: Spec.typ)
  (range: option (int_value & int_value))
  (v: option int_value)
: Tot Spec.typ
=
    Util.andp
      ty
      (Spec.t_choice
        (match range with
        | Some (lo, hi) ->
          let lo = eval_int_value lo in
          let hi = eval_int_value hi in
          if hi < 0
          then Spec.t_always_false
          else let lo = if lo < 0 then 0 else lo in
          Spec.t_choice
            (Spec.str_size Cbor.cbor_major_type_byte_string lo hi)
            (Spec.str_size Cbor.cbor_major_type_text_string lo hi)
        | _ -> Spec.t_always_false
        )
        (match v with
        | Some v ->
          let v = eval_int_value v in
          if v < 0
          then Spec.t_always_false
          else Spec.uint_size v
        | _ -> Spec.t_always_false // uint .size is not defined for ranges
        )
      )

[@@sem_attr]
let rec extract_int_value
  (env: sem_env)
  (x: typ)
: Pure (option int_value)
    (requires (typ_bounded env.se_bound x))
    (ensures (fun _ -> True))
= match x with
  | TDef n ->
    let s : type_sem = env.se_env n in
    begin match s with
    | SInt v -> Some v
    | _ -> None
    end
  | TElem (ELiteral (LInt x)) ->
    if x < 0
    then Some (SNegInt (U64.uint_to_t (-1 - x)))
    else Some (SUInt (U64.uint_to_t x))
  | TNamed _ t -> extract_int_value env t
  | _ -> None

[@@sem_attr]
let rec extract_range_value
  (env: sem_env)
  (x: typ)
: Pure (option (int_value & int_value))
    (requires (typ_bounded env.se_bound x))
    (ensures (fun _ -> True))
= match extract_int_value env x with
  | Some v -> Some (v, v)
  | _ ->
  begin match x with
  | TDef n ->
    let s : type_sem = env.se_env n in
    begin match s with
    | SIntRange a b -> Some (a, b)
    | _ -> None
    end
  | TRange tlow inclusive thigh ->
    begin match extract_int_value env tlow with
    | Some low ->
      begin match extract_int_value env thigh with
      | Some high ->
        if inclusive
        then Some (low, high)
        else if eval_int_value high > - pow2 64
        then Some (low, int_value_minus_one high)
        else None
      | _ -> None
      end
    | _ -> None
    end
  | TNamed _ t -> extract_range_value env t
  | _ -> None
  end

[@@ sem_attr ]
let rec array_group_sem
  (env: sem_env)
  (g: group)
: Ghost (Spec.array_group None)
    (requires group_bounded env.se_bound g)
    (ensures fun _ -> True)
= match g with
  | GDef d ->
    begin match env.se_bound d with
    | Some NGroup -> fst (Ghost.reveal (env.se_env d) <: (Spec.array_group None & Spec.map_group))
    | Some NType -> Spec.array_group_item (sem_of_type_sem (env.se_env d))
    end
  | GElem _ _ t -> Spec.array_group_item (typ_sem env t)
  | GAlwaysFalse -> Spec.array_group_always_false
  | GNop -> Spec.array_group_empty
  | GZeroOrOne g -> Spec.array_group_zero_or_one (array_group_sem env g)
  | GZeroOrMore g -> Spec.array_group_zero_or_more (array_group_sem env g)
  | GOneOrMore g -> Spec.array_group_one_or_more (array_group_sem env g)
  | GConcat g1 g2 -> Spec.array_group_concat (array_group_sem env g1) (array_group_sem env g2)
  | GChoice g1 g2 -> Spec.array_group_choice (array_group_sem env g1) (array_group_sem env g2)

and map_group_sem
  (env: sem_env)
  (g: group)
: Ghost (Spec.map_group)
    (requires group_bounded env.se_bound g)
    (ensures fun _ -> True)
= match g with
  | GDef d ->
    begin match env.se_bound d with
    | Some NGroup -> snd (Ghost.reveal (env.se_env d) <: (Spec.array_group None & Spec.map_group))
    | Some NType -> Spec.map_group_match_item false Spec.any (sem_of_type_sem (env.se_env d))
    end
  | GElem cut key value -> Spec.map_group_match_item cut (typ_sem env key) (typ_sem env value)
  | GAlwaysFalse -> Spec.map_group_always_false
  | GNop -> Spec.map_group_nop
  | GZeroOrOne g -> Spec.map_group_zero_or_one (map_group_sem env g)
  | GZeroOrMore g -> Spec.map_group_zero_or_more (map_group_sem env g)
  | GOneOrMore g -> Spec.map_group_one_or_more (map_group_sem env g)
  | GConcat g1 g2 -> Spec.map_group_concat (map_group_sem env g1) (map_group_sem env g2)
  | GChoice g1 g2 -> Spec.map_group_choice (map_group_sem env g1) (map_group_sem env g2)

and typ_sem
  (env: sem_env)
  (x: typ)
: Ghost Spec.typ
    (requires typ_bounded env.se_bound x)
    (ensures (fun _ -> True))
= match x with
  | TElem t -> elem_typ_sem t
  | TDef s -> sem_of_type_sem (env.se_env s)
  | TTagged tg t' ->
    Spec.t_tag
      begin match tg with
      | None -> None
      | Some tg -> Some (U64.uint_to_t tg)
      end
      (typ_sem env t')
  | TArray g ->
    Spec.t_array (array_group_sem env g)
  | TMap g ->
    Spec.t_map (map_group_sem env g)
  | TNamed _ t -> typ_sem env t
  | TChoice t1 t2 ->
    Spec.t_choice
      (typ_sem env t1)
      (typ_sem env t2)
  | TSize base range ->
    t_size (typ_sem env base) (extract_range_value env range) (extract_int_value env range)
  | TDetCbor base dest ->
    Util.andp
      (typ_sem env base)
      (Spec.bstr_cbor_det (typ_sem env dest))
  | TRange _ _ _ ->
    begin match extract_range_value env x with
    | Some (low, high) ->
      Spec.t_int_range (eval_int_value low) (eval_int_value high)
    | _ -> Spec.t_always_false
    end

let rec extract_int_value_incr
  (env env': sem_env)
  (x: typ)
: Lemma
  (requires typ_bounded env.se_bound x /\
    sem_env_included env env'
  )
  (ensures typ_bounded env'.se_bound x /\
    extract_int_value env' x == extract_int_value env x
  )
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (extract_int_value env x);];
    [SMTPat (sem_env_included env env'); SMTPat (extract_int_value env' x);];
  ]]
= match x with
  | TNamed _ x' -> extract_int_value_incr env env' x'
  | _ -> ()

let rec extract_range_value_incr
  (env env': sem_env)
  (x: typ)
: Lemma
  (requires typ_bounded env.se_bound x /\
    sem_env_included env env'
  )
  (ensures typ_bounded env'.se_bound x /\
    extract_range_value env' x == extract_range_value env x
  )
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (extract_range_value env x);];
    [SMTPat (sem_env_included env env'); SMTPat (extract_range_value env' x);];
  ]]
= match x with
  | TNamed _ x' -> extract_range_value_incr env env' x'
  | _ -> ()

let rec array_group_sem_incr
  (env env': sem_env)
  (g: group)
: Lemma
  (requires (
    sem_env_included env env' /\
    group_bounded env.se_bound g
  ))
  (ensures (
    group_bounded env.se_bound g /\
    group_bounded env'.se_bound g /\
    array_group_sem env g == array_group_sem env' g
  ))
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (array_group_sem env g)];
    [SMTPat (sem_env_included env env'); SMTPat (array_group_sem env' g)];
  ]]
= match g with
  | GAlwaysFalse
  | GNop
  | GDef _ -> ()
  | GElem _ _ t -> typ_sem_incr env env' t
  | GZeroOrOne g
  | GZeroOrMore g
  | GOneOrMore g
  -> array_group_sem_incr env env' g
  | GConcat g1 g2
  | GChoice g1 g2
  -> array_group_sem_incr env env' g1;
  array_group_sem_incr env env' g2

and map_group_sem_incr
  (env env': sem_env)
  (g: group)
: Lemma
  (requires (
    sem_env_included env env' /\
    group_bounded env.se_bound g
  ))
  (ensures (
    group_bounded env.se_bound g /\
    group_bounded env'.se_bound g /\
    map_group_sem env g == map_group_sem env' g
  ))
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (map_group_sem env g)];
    [SMTPat (sem_env_included env env'); SMTPat (map_group_sem env' g)];
  ]]
= match g with
  | GDef _
  | GAlwaysFalse
  | GNop -> ()
  | GElem _ key value ->
    typ_sem_incr env env' key;
    typ_sem_incr env env' value
  | GZeroOrOne g
  | GZeroOrMore g
  | GOneOrMore g
  -> map_group_sem_incr env env' g
  | GConcat g1 g2
  | GChoice g1 g2
  -> map_group_sem_incr env env' g1;
    map_group_sem_incr env env' g2

and typ_sem_incr
  (env env': sem_env)
  (x: typ)
: Lemma
  (requires (
    sem_env_included env env' /\
    typ_bounded env.se_bound x
  ))
  (ensures (
    typ_bounded env.se_bound x /\
    typ_bounded env'.se_bound x /\
    typ_sem env x == typ_sem env' x
  ))
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (typ_sem env x)];
    [SMTPat (sem_env_included env env'); SMTPat (typ_sem env' x)];
  ]]
= match x with
  | TElem _
  | TDef _
  -> ()
  | TTagged _ t' -> typ_sem_incr env env' t'
  | TArray g ->
    array_group_sem_incr env env' g
  | TMap g ->
    map_group_sem_incr env env' g
  | TNamed _ t -> typ_sem_incr env env' t
  | TSize t1 t2
  | TRange t1 _ t2
  | TDetCbor t1 t2
  | TChoice t1 t2 ->
    typ_sem_incr env env' t1;
    typ_sem_incr env env' t2

[@@ sem_attr ]
let rec typ_sem_elem
  (env: sem_env)
  (x: typ)
: Pure type_sem
  (requires (typ_bounded env.se_bound x))
  (ensures (fun y ->
    typ_bounded env.se_bound x /\
    sem_of_type_sem y == typ_sem env x
  ))
= match x with
  | TDef n -> env.se_env n
  | TElem (ELiteral (LInt x)) ->
    if x < 0
    then SInt (SNegInt (U64.uint_to_t (-1 - x)))
    else SInt (SUInt (U64.uint_to_t x))
(* TODO: range *)
  | TNamed _ t -> typ_sem_elem env t
  | _ -> Sem (typ_sem env x)

let rec typ_sem_elem_incr
  (env env': sem_env)
  (x: typ)
: Lemma
  (requires (typ_bounded env.se_bound x /\
    sem_env_included env env'
  ))
  (ensures (
    typ_bounded env.se_bound x /\
    typ_bounded env'.se_bound x /\
    typ_sem_elem env' x == typ_sem_elem env x
  ))
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (typ_sem_elem env x);];
    [SMTPat (sem_env_included env env'); SMTPat (typ_sem_elem env' x);];
  ]]
= match x with
  | TNamed _ x' -> typ_sem_elem_incr env env' x'
  | _ -> ()

(* Annotated AST and their semantics *)

[@@base_attr; PpxDerivingShow]
type map_constraint =
| MCFalse
| MCKeyValue: typ -> typ -> map_constraint
| MCNot: map_constraint -> map_constraint
| MCAnd: map_constraint -> map_constraint -> map_constraint
| MCOr: map_constraint -> map_constraint -> map_constraint

[@@ base_attr]
let rec bounded_map_constraint
  (env: name_env)
  (g: map_constraint)
: Tot bool
= match g with
  | MCFalse -> true
  | MCKeyValue t1 t2 ->
    typ_bounded env t1 && typ_bounded env t2
  | MCNot g' ->
    bounded_map_constraint env g'
  | MCAnd g1 g2
  | MCOr g1 g2 ->
    bounded_map_constraint env g1 &&
    bounded_map_constraint env g2

let rec bounded_map_constraint_incr
  (env env': name_env)
  (g: map_constraint)
: Lemma
  (requires (
    name_env_included env env' /\
    bounded_map_constraint env g
  ))
  (ensures (
    bounded_map_constraint env' g
  ))
  (decreases g)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (bounded_map_constraint env g)];
    [SMTPat (name_env_included env env'); SMTPat (bounded_map_constraint env' g)];
  ]]
= match g with
  | MCAnd g1 g2
  | MCOr g1 g2
    -> bounded_map_constraint_incr env env' g1;
    bounded_map_constraint_incr env env' g2
  | MCNot g1
    -> bounded_map_constraint_incr env env' g1
  | _ -> ()

[@@ sem_attr ]
let rec map_constraint_sem
  (env: sem_env)
  (g: map_constraint)
: Ghost Spec.map_constraint
    (requires bounded_map_constraint env.se_bound g)
    (ensures fun _ -> True)
= match g with
  | MCFalse -> Spec.map_constraint_empty
  | MCKeyValue t1 t2 ->
    Spec.matches_map_group_entry (typ_sem env t1) (typ_sem env t2)
  | MCNot g' ->
    Util.notp (map_constraint_sem env g')
  | MCAnd g1 g2 ->
    Util.andp (map_constraint_sem env g1) (map_constraint_sem env g2)
  | MCOr g1 g2 ->
    Spec.map_constraint_choice (map_constraint_sem env g1) (map_constraint_sem env g2)

let rec map_constraint_sem_incr
  (env env': sem_env)
  (g: map_constraint)
: Lemma
    (requires bounded_map_constraint env.se_bound g /\
      sem_env_included env env'
    )
    (ensures bounded_map_constraint env'.se_bound g /\
      map_constraint_sem env' g == map_constraint_sem env g
    )
    (decreases g)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (map_constraint_sem env g)];
    [SMTPat (sem_env_included env env'); SMTPat (map_constraint_sem env' g)];
  ]]
= bounded_map_constraint_incr env.se_bound env'.se_bound g;
  match g with
  | MCAnd g1 g2
  | MCOr g1 g2
    -> map_constraint_sem_incr env env' g1;
    map_constraint_sem_incr env env' g2
  | MCNot g1
    -> map_constraint_sem_incr env env' g1
  | _ -> ()

[@@base_attr; PpxDerivingShow]
type elab_map_group =
| MGNop
| MGAlwaysFalse
| MGMatch:
  cut: bool ->
  name: option string ->
  key: literal ->
  value: typ ->
  elab_map_group
| MGMatchWithCut:
  key: typ ->
  value: typ ->
  elab_map_group
| MGCut:
  key: typ ->
  elab_map_group
| MGTable:
  key: typ ->
  value: typ ->
  except: map_constraint ->
  elab_map_group
| MGConcat:
  g1: elab_map_group ->
  g2: elab_map_group ->
  elab_map_group
| MGChoice:
  g1: elab_map_group ->
  g2: elab_map_group ->
  elab_map_group

[@@ base_attr]
let rec bounded_elab_map_group
  (env: name_env)
  (g: elab_map_group)
: Tot bool
= match g with
  | MGNop
  | MGAlwaysFalse -> true
  | MGMatch _ _ key value ->
    wf_literal key &&
    typ_bounded env value
  | MGMatchWithCut key value ->
    typ_bounded env key &&
    typ_bounded env value
  | MGCut key ->
    typ_bounded env key
  | MGTable key value except ->
    typ_bounded env key &&
    bounded_map_constraint env except &&
    typ_bounded env value
  | MGConcat g1 g2
  | MGChoice g1 g2
    -> bounded_elab_map_group env g1 && bounded_elab_map_group env g2

let rec bounded_elab_map_group_incr
  (env env': name_env)
  (g: elab_map_group)
: Lemma
  (requires (
    name_env_included env env' /\
    bounded_elab_map_group env g
  ))
  (ensures (
    bounded_elab_map_group env' g
  ))
  (decreases g)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (bounded_elab_map_group env g)];
    [SMTPat (name_env_included env env'); SMTPat (bounded_elab_map_group env' g)];
  ]]
= match g with
  | MGConcat g1 g2
  | MGChoice g1 g2
    -> bounded_elab_map_group_incr env env' g1;
    bounded_elab_map_group_incr env env' g2
  | _ -> ()

[@@ sem_attr ]
let rec elab_map_group_sem
  (env: sem_env)
  (g: elab_map_group)
: Ghost Spec.det_map_group
    (requires bounded_elab_map_group env.se_bound g)
    (ensures fun _ -> True)
= match g with
  | MGNop -> Spec.map_group_nop
  | MGAlwaysFalse -> Spec.map_group_always_false
  | MGMatch cut _ key value ->
    Spec.map_group_match_item_for cut (eval_literal key) (typ_sem env value)
  | MGMatchWithCut key value ->
    Spec.map_group_match_item true (typ_sem env key) (typ_sem env value)
  | MGCut key ->
    Spec.map_group_cut (typ_sem env key)
  | MGTable key value except ->
    Spec.map_group_filtered_table (typ_sem env key) (typ_sem env value) (map_constraint_sem env except)
  | MGConcat g1 g2 ->
    Spec.map_group_concat (elab_map_group_sem env g1) (elab_map_group_sem env g2)
  | MGChoice g1 g2 ->
    Spec.map_group_choice (elab_map_group_sem env g1) (elab_map_group_sem env g2)

let elab_map_group_sem_concat
  (env: sem_env)
  (g1l g1r: elab_map_group)
: Lemma
  (requires
    bounded_elab_map_group env.se_bound g1l /\
    bounded_elab_map_group env.se_bound g1r
  )
  (ensures
    bounded_elab_map_group env.se_bound g1l /\
    bounded_elab_map_group env.se_bound g1r /\
    bounded_elab_map_group env.se_bound (MGConcat g1l g1r) /\
    (elab_map_group_sem env (MGConcat g1l g1r) == Spec.map_group_concat (elab_map_group_sem env g1l) (elab_map_group_sem env g1r))
  )
//  [SMTPat (elab_map_group_sem env (MGConcat g1l g1r))]
=
  assert_norm (elab_map_group_sem env (MGConcat g1l g1r) == Spec.map_group_concat (elab_map_group_sem env g1l) (elab_map_group_sem env g1r)) // FIXME: WHY WHY WHY?

let elab_map_group_sem_choice
  (env: sem_env)
  (g1l g1r: elab_map_group)
: Lemma
  (requires bounded_elab_map_group env.se_bound g1l /\
    bounded_elab_map_group env.se_bound g1r
  )
  (ensures
    (elab_map_group_sem env (MGChoice g1l g1r) == Spec.map_group_choice (elab_map_group_sem env g1l) (elab_map_group_sem env g1r))
  )
//  [SMTPat (elab_map_group_sem env (MGChoice g1l g1r))]
=
  assert_norm (elab_map_group_sem env (MGChoice g1l g1r) == Spec.map_group_choice (elab_map_group_sem env g1l) (elab_map_group_sem env g1r)) // FIXME: WHY WHY WHY?

let rec elab_map_group_sem_incr
  (env env': sem_env)
  (g: elab_map_group)
: Lemma
    (requires bounded_elab_map_group env.se_bound g /\
      sem_env_included env env'
    )
    (ensures bounded_elab_map_group env'.se_bound g /\
      elab_map_group_sem env' g == elab_map_group_sem env g
    )
    (decreases g)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (elab_map_group_sem env g)];
    [SMTPat (sem_env_included env env'); SMTPat (elab_map_group_sem env' g)];
  ]]
= bounded_elab_map_group_incr env.se_bound env'.se_bound g;
  match g with
  | MGConcat g1 g2
  | MGChoice g1 g2
    ->
    elab_map_group_sem_incr env env' g1;
    elab_map_group_sem_incr env env' g2
  | _ -> ()

#push-options "--z3rlimit 32"

#restart-solver
[@@ sem_attr ]
let rec spec_map_group_footprint
  (env: sem_env)
  (g: elab_map_group)
: Pure (Ghost.erased Spec.map_constraint)
    (requires bounded_elab_map_group env.se_bound g)
    (ensures fun  ty ->
      let s = elab_map_group_sem env g in
      Spec.map_group_footprint s ty /\
      Spec.map_group_is_det s
    )
= match g with
  | MGMatch cut _ key value
  -> Spec.map_group_footprint_match_item_for cut (eval_literal key) (typ_sem env value);
    Ghost.hide (Spec.map_group_match_item_for_footprint cut (eval_literal key) (typ_sem env value))
  | MGTable key value except // TODO: extend to GOneOrMore
  -> Ghost.hide (Util.andp (Spec.matches_map_group_entry (typ_sem env key) (typ_sem env value)) (Util.notp (map_constraint_sem env except)))
  | MGChoice g1 g2
  | MGConcat g1 g2 ->
    let ty1 = spec_map_group_footprint env g1 in
    let ty2 = spec_map_group_footprint env g2 in
    (Ghost.hide (Ghost.reveal ty1 `Spec.map_constraint_choice` Ghost.reveal ty2))
  | MGNop
  | MGAlwaysFalse -> (Ghost.hide Spec.map_constraint_empty)
  | MGCut key
  | MGMatchWithCut key _ ->
    (Ghost.hide (Spec.matches_map_group_entry (typ_sem env key) Spec.any))

#pop-options

let spec_map_group_footprint_concat
  (env: sem_env)
  (g1 g2: elab_map_group)
: Lemma
  (requires (
    bounded_elab_map_group env.se_bound g1 /\
    bounded_elab_map_group env.se_bound g2
  ))
  (ensures (
    bounded_elab_map_group env.se_bound (MGConcat g1 g2) /\
    bounded_elab_map_group env.se_bound g1 /\
    bounded_elab_map_group env.se_bound g2 /\
    spec_map_group_footprint env (MGConcat g1 g2) == Ghost.hide (
      spec_map_group_footprint env g1 `Spec.map_constraint_choice`
      spec_map_group_footprint env g2
  )))
= assert_norm (
    spec_map_group_footprint env (MGConcat g1 g2) == Ghost.hide (
      spec_map_group_footprint env g1 `Spec.map_constraint_choice`
      spec_map_group_footprint env g2
  ))

let rec spec_map_group_footprint_incr
  (env env': sem_env)
  (g: elab_map_group)
: Lemma
  (requires
    sem_env_included env env' /\
    bounded_elab_map_group env.se_bound g
  )
  (ensures
    bounded_elab_map_group env'.se_bound g /\
    spec_map_group_footprint env' g == spec_map_group_footprint env g
  )
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_map_group_footprint env g)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_map_group_footprint env' g)];
  ]]
= match g with
  | MGChoice g1 g2
  | MGConcat g1 g2 ->
    spec_map_group_footprint_incr env env' g1;
    spec_map_group_footprint_incr env env' g2
  | _ -> ()

[@@base_attr]
type ast0_wf_typ
: typ -> Type
= 
| WfTRewrite:
  (t: typ) ->
  (t' : typ) ->
  ast0_wf_typ t' ->
  ast0_wf_typ t
  
| WfTArray:
  (g: group) ->
  (s: ast0_wf_array_group g) ->
  ast0_wf_typ (TArray g)
| WfTMap:
  (g: group) ->
//  (ty1: Spec.typ) ->
//  (ty2: Spec.typ) ->
//  (s: ast0_wf_validate_map_group Spec.t_always_false Spec.t_always_false g ty1 ty2) ->
  (g2: elab_map_group) ->
//  (s2: ast0_wf_parse_map_group g2) ->
  (s2: ast0_wf_parse_map_group g2) ->
  ast0_wf_typ (TMap g)
| WfTTagged:
  (tag: option int) ->
  (t': typ) ->
  (s': ast0_wf_typ t') ->
  ast0_wf_typ (TTagged tag t')
| WfTChoice:
  (t1: typ) ->
  (t2: typ) ->
  (s1: ast0_wf_typ t1) ->
  (s2: ast0_wf_typ t2) ->
  ast0_wf_typ (TChoice t1 t2)
| WfTElem:
  (e: elem_typ) ->
  ast0_wf_typ (TElem e)
| WfTDetCbor:
  (base: typ) ->
  (dest: typ) ->
  (wfdest: ast0_wf_typ dest) ->
  ast0_wf_typ (TDetCbor base dest)
| WfTStrSize:
  (k: int) ->
  (base: typ) ->
  (range: typ) ->
  (lo: int) ->
  (hi: int) ->
  ast0_wf_typ (TSize base range)
| WfTIntRange:
  (base_from: typ) ->
  (base_inclusive: bool) ->
  (base_to: typ) ->
  (from: int) ->
  (to: int) ->
  ast0_wf_typ (TRange base_from base_inclusive base_to)
| WfTDef:
  (n: string) ->
  ast0_wf_typ (TDef n)

and ast0_wf_array_group
: group -> Type
= 
| WfAElem:
  _cut: bool ->
  key: typ ->
  ty: typ ->
  prf: ast0_wf_typ ty ->
  ast0_wf_array_group (GElem _cut key ty)
| WfAZeroOrOne:
  g: group ->
  s: ast0_wf_array_group g ->
  ast0_wf_array_group (GZeroOrOne g)
| WfAZeroOrOneOrMore:
  g: group ->
  s: ast0_wf_array_group g ->
  g': group { g' == GZeroOrMore g \/ g' == GOneOrMore g } ->
  ast0_wf_array_group g'
| WfAConcat:
  g1: group ->
  g2: group ->
  s1: ast0_wf_array_group g1 ->
  s2: ast0_wf_array_group g2 ->
  ast0_wf_array_group (GConcat g1 g2)
| WfAChoice:
  g1: group ->
  g2: group ->
  s1: ast0_wf_array_group g1 ->
  s2: ast0_wf_array_group g2 ->
  ast0_wf_array_group (GChoice g1 g2)
| WfARewrite:
  g1: group ->
  g2: group ->
  s2: ast0_wf_array_group g2 ->
  ast0_wf_array_group g1
(*  
| WfADef:
  n: string ->
  ast0_wf_array_group (GDef n) // will be taken into account by the syntax environment
*)

and ast0_wf_parse_map_group
: elab_map_group -> Type
=
| WfMNop:
    unit ->
    ast0_wf_parse_map_group MGNop
| WfMChoice:
    g1': elab_map_group ->
    s1: ast0_wf_parse_map_group g1' ->
    g2': elab_map_group ->
    s2: ast0_wf_parse_map_group g2' ->
    ast0_wf_parse_map_group (MGChoice g1' g2')
| WfMConcat:
    g1: elab_map_group ->
    s1: ast0_wf_parse_map_group g1 ->
    g2: elab_map_group ->
    s2: ast0_wf_parse_map_group g2 ->
    ast0_wf_parse_map_group (MGConcat g1 g2)
| WfMZeroOrOne:
    g: elab_map_group ->
    s: ast0_wf_parse_map_group g ->
    ast0_wf_parse_map_group (MGChoice g MGNop)
| WfMLiteral:
    cut: bool ->
    name: option string ->
    key: literal ->
    value: typ ->
    s: ast0_wf_typ value ->
    ast0_wf_parse_map_group (MGMatch cut name key value)
| WfMZeroOrMore:
    key: typ ->
    value: typ ->
    except: map_constraint ->
    s_key: ast0_wf_typ key ->
    s_value: ast0_wf_typ value ->
    s_map_constraint: ast0_wf_map_constraint except ->
    ast0_wf_parse_map_group (MGTable key value except)

and ast0_wf_map_constraint
: map_constraint -> Type
= | WfMCFalse: ast0_wf_map_constraint MCFalse
  | WfMCKeyValue:
    key: typ ->
    s_key: ast0_wf_typ key ->
    value: typ ->
    s_value: ast0_wf_typ value ->
    ast0_wf_map_constraint (MCKeyValue key value)
  | WfMCNot:
    mc: map_constraint ->
    s_mc: ast0_wf_map_constraint mc ->
    ast0_wf_map_constraint (MCNot mc)
  | WfMCAnd:
    mc1: map_constraint ->
    s_mc1: ast0_wf_map_constraint mc1 ->
    mc2: map_constraint ->
    s_mc2: ast0_wf_map_constraint mc2 ->
    ast0_wf_map_constraint (MCAnd mc1 mc2)
  | WfMCOr:
    mc1: map_constraint ->
    s_mc1: ast0_wf_map_constraint mc1 ->
    mc2: map_constraint ->
    s_mc2: ast0_wf_map_constraint mc2 ->
    ast0_wf_map_constraint (MCOr mc1 mc2)

(*
and ast0_wf_validate_map_group
: Spec.typ -> Spec.typ -> group -> Spec.typ -> Spec.typ -> Type
=
| RMChoice:
    left_elems: Spec.typ ->
    left_tables: Spec.typ ->
    g1: group ->
    left_elems1: Spec.typ ->
    left_tables1: Spec.typ ->
    s1: ast0_wf_validate_map_group left_elems left_tables g1 left_elems1 left_tables1 ->
    g2: group ->
    left_elems2: Spec.typ ->
    left_tables2: Spec.typ ->
    s2: ast0_wf_validate_map_group left_elems left_tables g2 left_elems2 left_tables2 ->
    ast0_wf_validate_map_group left_elems left_tables (GChoice g1 g2) (left_elems1 `Spec.t_choice` left_elems2) (left_tables1 `Spec.t_choice` left_tables2)
| RMConcat:
    left_elems: Spec.typ ->
    left_tables: Spec.typ ->
    g1: group ->
    left_elems1: Spec.typ ->
    left_tables1: Spec.typ ->
    s1: ast0_wf_validate_map_group left_elems left_tables g1 left_elems1 left_tables1 ->
    g2: group ->
    left_elems2: Spec.typ ->
    left_tables2: Spec.typ ->
    s2: ast0_wf_validate_map_group left_elems1 left_tables1 g2 left_elems2 left_tables2 ->
    ast0_wf_validate_map_group left_elems left_tables (GConcat g1 g2) left_elems2 left_tables2
| RMZeroOrOne:
    left_elems: Spec.typ ->
    left_tables: Spec.typ ->
    g: group ->
    left_elems': Spec.typ ->
    left_tables': Spec.typ ->
    s: ast0_wf_validate_map_group left_elems left_tables g left_elems' left_tables' ->
    ast0_wf_validate_map_group left_elems left_tables (GZeroOrOne g) left_elems' left_tables'
| RMElemLiteral:
    left_elems: Spec.typ ->
    left_tables: Spec.typ ->
    cut: bool ->
    key: literal ->
    value: typ ->
    s: ast0_wf_typ value ->
    ast0_wf_validate_map_group left_elems left_tables (GMapElem () cut (TElem (ELiteral key)) value) (left_elems `Spec.t_choice` Spec.t_literal (eval_literal key)) left_tables
| RMZeroOrMore:
    left_elems: Spec.typ ->
    left_tables: Spec.typ ->
    key: typ ->
    value: typ ->
    s_key: ast0_wf_typ key ->
    s_value: ast0_wf_typ value ->
    v_key: Spec.typ ->
    ast0_wf_validate_map_group left_elems left_tables (GZeroOrMore (GMapElem () false key value)) left_elems (left_tables `Spec.t_choice` v_key)
*)

[@@base_attr]
let rec bounded_wf_typ
  (env: name_env)
  (t: typ)
  (wf: ast0_wf_typ t)
: Tot bool
  (decreases wf)
= match wf with
| WfTRewrite t t' s' ->
  typ_bounded env t &&
  typ_bounded env t' &&
  bounded_wf_typ env _ s'
| WfTArray g s ->
  bounded_wf_array_group env g s
| WfTTagged tag t' s' ->
  begin match tag with
  | None -> true
  | Some tag ->
    0 <= tag && tag < pow2 64
  end &&
  bounded_wf_typ env t' s'
| WfTMap g1 (* ty1 ty2 s1 *) g2 s2 ->
    group_bounded env g1 &&
    bounded_elab_map_group env g2 &&
//    bounded_wf_validate_map_group env Spec.t_always_false Spec.t_always_false g1 ty1 ty2 s1 /\
    bounded_wf_parse_map_group env _ s2
| WfTChoice t1 t2 s1 s2 ->
  typ_bounded env t1 &&
  typ_bounded env t2 &&
  bounded_wf_typ env t1 s1 &&
  bounded_wf_typ env t2 s2
| WfTElem e -> wf_elem_typ e
| WfTDetCbor base dest wfdest ->
  typ_bounded env base &&
  typ_bounded env dest &&
  bounded_wf_typ env _ wfdest
| WfTStrSize k base range lo hi ->
  (k = U8.v Cbor.cbor_major_type_byte_string || k = U8.v Cbor.cbor_major_type_text_string) &&
  typ_bounded env base &&
  typ_bounded env range &&
  0 <= lo && lo <= hi && hi < pow2 64
| WfTIntRange base_from base_inclusive base_to from to ->
  typ_bounded env base_from &&
  typ_bounded env base_to &&
  from <= to &&
  begin if from >= 0
  then to < pow2 64
  else if to < 0
  then from >= - pow2 64
  else (from >= - pow2 63 && to < pow2 63)
  end
| WfTDef n ->
  env n = Some NType

and bounded_wf_array_group
  (env: name_env)
  (g: group)
  (wf: ast0_wf_array_group g)
: Tot bool
  (decreases wf)
= match wf with
| WfAElem _ key ty prf ->
  typ_bounded env key &&
  bounded_wf_typ env ty prf
| WfAZeroOrOne g s ->
  group_bounded env g &&
  bounded_wf_array_group env g s
| WfAZeroOrOneOrMore g s g' ->
  group_bounded env g &&
  bounded_wf_array_group env g s
| WfAConcat g1 g2 s1 s2 ->
  group_bounded env g1 &&
  group_bounded env g2 &&
  bounded_wf_array_group env g1 s1 &&
  bounded_wf_array_group env g2 s2
| WfAChoice g1 g2 s1 s2 ->
  group_bounded env g1 &&
  group_bounded env g2 &&
  bounded_wf_array_group env g1 s1 &&
  bounded_wf_array_group env g2 s2
| WfARewrite g1 g2 s2 ->
  group_bounded env g1 &&
  group_bounded env g2 &&
  bounded_wf_array_group env g2 s2
(*  
| WfADef n ->
  env n == Some NGroup
*)

and bounded_wf_parse_map_group
  (env: name_env)
  (g: elab_map_group)
  (wf: ast0_wf_parse_map_group g)
: Tot bool
  (decreases wf)
= match wf with
| WfMChoice g1' s1 g2' s2 ->
    bounded_elab_map_group env g1' &&
    bounded_wf_parse_map_group env g1' s1 &&
    bounded_elab_map_group env g2' &&
    bounded_wf_parse_map_group env g2' s2
| WfMConcat g1 s1 g2 s2 ->
    bounded_elab_map_group env g1 &&
    bounded_wf_parse_map_group env g1 s1 &&
    bounded_elab_map_group env g2 &&
    bounded_wf_parse_map_group env g2 s2
| WfMZeroOrOne g s ->
    bounded_elab_map_group env g &&
    bounded_wf_parse_map_group env g s
| WfMLiteral cut _ key value s ->
    wf_literal key &&
    bounded_wf_typ env value s
| WfMZeroOrMore key value except s_key s_value s_except ->
    bounded_wf_typ env key s_key &&
    bounded_wf_map_constraint env except s_except &&
    bounded_wf_typ env value s_value
| WfMNop _ -> true

and bounded_wf_map_constraint
  (env: name_env)
  (g: map_constraint)
  (wf: ast0_wf_map_constraint g)
: Tot bool
  (decreases wf)
= match wf with
  | WfMCFalse -> true
  | WfMCKeyValue key s_key value s_value ->
    bounded_wf_typ env key s_key &&
    bounded_wf_typ env value s_value
  | WfMCNot g1 wf1 ->
    bounded_wf_map_constraint env g1 wf1
  | WfMCOr g1 wf1 g2 wf2
  | WfMCAnd g1 wf1 g2 wf2 ->
    bounded_wf_map_constraint env g1 wf1 &&
    bounded_wf_map_constraint env g2 wf2

// TODO: recover named map groups

(*
and bounded_wf_validate_map_group
  (env: name_env)
  (left_elems: Spec.typ)
  (left_tables: Spec.typ)
  (g: group)
  (left_elems': Spec.typ)
  (left_tables': Spec.typ)
  (s: ast0_wf_validate_map_group left_elems left_tables g left_elems' left_tables')
: Tot prop
  (decreases s)
= match s with
| RMChoice left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    bounded_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 s1 /\
    bounded_wf_validate_map_group env left_elems left_tables g2 left_elems2 left_tables2 s2
| RMConcat left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    bounded_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 s1 /\
    bounded_wf_validate_map_group env left_elems1 left_tables1 g2 left_elems2 left_tables2 s2
| RMZeroOrOne left_elems left_tables g left_elems' left_tables' s ->
    bounded_wf_validate_map_group env left_elems left_tables g left_elems' left_tables' s
| RMElemLiteral left_elems left_tables cut key value s' ->
    bounded_wf_typ env value s'
| RMZeroOrMore left_elems left_tables key value s_key s_value v_key ->
    typ_bounded env key /\
    bounded_wf_typ env key s_key /\
    bounded_wf_typ env value s_value
*)

let rec bounded_wf_typ_incr
  (env env': name_env)
  (g: typ)
  (wf: ast0_wf_typ g)
: Lemma
  (requires name_env_included env env' /\
    bounded_wf_typ env g wf
  )
  (ensures
      bounded_wf_typ env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_typ env g wf)];
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_typ env' g wf)];
  ]]
= match wf with
  | WfTDetCbor _ _ s'
  | WfTRewrite _ _ s' ->
    bounded_wf_typ_incr env env' _ s'
  | WfTArray g s ->
    bounded_wf_array_group_incr env env' g s
  | WfTTagged _ t' s' ->
    bounded_wf_typ_incr env env' t' s'
  | WfTMap g1 (* ty1 ty2 s1 *) g2 s2 ->
//    bounded_wf_validate_map_group_incr env env' Spec.t_always_false Spec.t_always_false g1 ty1 ty2 s1;
    bounded_wf_parse_map_group_incr env env' _ s2
  | WfTChoice t1 t2 s1 s2 ->
    bounded_wf_typ_incr env env' t1 s1;
    bounded_wf_typ_incr env env' t2 s2
  | WfTStrSize _ _ _ _ _
  | WfTIntRange _ _ _ _ _
  | WfTElem _
  | WfTDef _ -> ()

and bounded_wf_array_group_incr
  (env env': name_env)
  (g: group)
  (wf: ast0_wf_array_group g)
: Lemma
  (requires name_env_included env env' /\
    bounded_wf_array_group env g wf
  )
  (ensures
      bounded_wf_array_group env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_array_group env g wf)];
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_array_group env' g wf)];
  ]]
= match wf with
  | WfAElem _ _ ty prf ->
    bounded_wf_typ_incr env env' ty prf
  | WfAZeroOrOne g s ->
    bounded_wf_array_group_incr env env' g s
  | WfAZeroOrOneOrMore g s g' ->
    bounded_wf_array_group_incr env env' g s
  | WfAConcat g1 g2 s1 s2
  | WfAChoice g1 g2 s1 s2 ->
    bounded_wf_array_group_incr env env' g1 s1;
    bounded_wf_array_group_incr env env' g2 s2
  | WfARewrite _ g2 s2 ->
    bounded_wf_array_group_incr env env' g2 s2
(*    
  | WfADef _ -> ()
*)

(*
and bounded_wf_validate_map_group_incr
  (env env': name_env)
  (left_elems: Spec.typ)
  (left_tables: Spec.typ)
  (g1: group)
  (left_elems1: Spec.typ)
  (left_tables1: Spec.typ)
  (wf: ast0_wf_validate_map_group left_elems left_tables g1 left_elems1 left_tables1)
: Lemma
  (requires name_env_included env env' /\
    bounded_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 wf
  )
  (ensures
    bounded_wf_validate_map_group env' left_elems left_tables g1 left_elems1 left_tables1 wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 wf)];
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_validate_map_group env' left_elems left_tables g1 left_elems1 left_tables1 wf)];
  ]]
= match wf with
| RMChoice left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    bounded_wf_validate_map_group_incr env env' left_elems left_tables g1 left_elems1 left_tables1 s1;
    bounded_wf_validate_map_group_incr env env'  left_elems left_tables g2 left_elems2 left_tables2 s2
| RMConcat left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    bounded_wf_validate_map_group_incr env env' left_elems left_tables g1 left_elems1 left_tables1 s1;
    bounded_wf_validate_map_group_incr env env' left_elems1 left_tables1 g2 left_elems2 left_tables2 s2
| RMZeroOrOne left_elems left_tables g left_elems' left_tables' s ->
    bounded_wf_validate_map_group_incr env env'  left_elems left_tables g left_elems' left_tables' s
| RMElemLiteral left_elems left_tables cut key value s' ->
    bounded_wf_typ_incr env env' value s'
| RMZeroOrMore left_elems left_tables key value s_key s_value v_key ->
    bounded_wf_typ_incr env env' key s_key;
    bounded_wf_typ_incr env env' value s_value
*)

and bounded_wf_parse_map_group_incr
  (env env': name_env)
  (g: elab_map_group)
  (wf: ast0_wf_parse_map_group g)
: Lemma
  (requires name_env_included env env' /\
    bounded_wf_parse_map_group env g wf
  )
  (ensures
      bounded_wf_parse_map_group env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_parse_map_group env g wf)];
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_parse_map_group env' g wf)];
  ]]
= match wf with
  | WfMNop _ -> ()
  | WfMConcat g1' s1 g2' s2
  | WfMChoice g1' s1 g2' s2 ->
    bounded_wf_parse_map_group_incr env env' g1' s1;
    bounded_wf_parse_map_group_incr env env' g2' s2
  | WfMZeroOrOne g s ->
    bounded_wf_parse_map_group_incr env env' g s
  | WfMLiteral cut _ key value s ->
    bounded_wf_typ_incr env env' value s
  | WfMZeroOrMore key value except s_key s_value s_except ->
    bounded_wf_typ_incr env env' key s_key;
    bounded_wf_map_constraint_incr env env' except s_except;
    bounded_wf_typ_incr env env' value s_value

and bounded_wf_map_constraint_incr
  (env env': name_env)
  (g: map_constraint)
  (wf: ast0_wf_map_constraint g)
: Lemma
  (requires name_env_included env env' /\
    bounded_wf_map_constraint env g wf
  )
  (ensures
      bounded_wf_map_constraint env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_map_constraint env g wf)];
    [SMTPat (name_env_included env env'); SMTPat (bounded_wf_map_constraint env' g wf)];
  ]]
= match wf with
  | WfMCFalse -> ()
  | WfMCKeyValue key s_key value s_value ->
    bounded_wf_typ_incr env env' key s_key;
    bounded_wf_typ_incr env env' value s_value
  | WfMCNot g1 wf1 ->
    bounded_wf_map_constraint_incr env env' g1 wf1
  | WfMCOr g1 wf1 g2 wf2
  | WfMCAnd g1 wf1 g2 wf2 ->
    bounded_wf_map_constraint_incr env env' g1 wf1;
    bounded_wf_map_constraint_incr env env' g2 wf2

let rec bounded_wf_typ_bounded
  (env: name_env)
  (g: typ)
  (wf: ast0_wf_typ g)
: Lemma
  (requires
    bounded_wf_typ env g wf
  )
  (ensures
    typ_bounded env g
  )
  (decreases wf)
  [SMTPat (bounded_wf_typ env g wf)]
= match wf with
  | WfTRewrite _ _ s' ->
    bounded_wf_typ_bounded env _ s'
  | WfTArray g s ->
    bounded_wf_array_group_bounded env g s
  | WfTTagged _ t' s' ->
    bounded_wf_typ_bounded env t' s'
  | WfTMap g1 (* ty1 ty2 s1 *) g2 s2 ->
//    bounded_wf_validate_map_group_bounded env Spec.t_always_false Spec.t_always_false g1 ty1 ty2 s1;
    bounded_wf_parse_map_group_bounded env _ s2
  | WfTChoice t1 t2 s1 s2 ->
    bounded_wf_typ_bounded env t1 s1;
    bounded_wf_typ_bounded env t2 s2
  | WfTIntRange _ _ _ _ _
  | WfTDetCbor _ _ _ 
  | WfTStrSize _ _ _ _ _
  | WfTElem _
  | WfTDef _ -> ()

and bounded_wf_array_group_bounded
  (env: name_env)
  (g: group)
  (wf: ast0_wf_array_group g)
: Lemma
  (requires
    bounded_wf_array_group env g wf
  )
  (ensures
      group_bounded env g
  )
  (decreases wf)
  [SMTPat (bounded_wf_array_group env g wf)]
= match wf with
  | WfAElem _ key ty prf ->
    bounded_wf_typ_bounded env ty prf
  | WfAConcat _ _ _ _
  | WfAChoice _ _ _ _
  | WfAZeroOrOneOrMore _ _ _
  | WfAZeroOrOne _ _
  | WfARewrite _ _ _
(*  
  | WfADef _
*)  
    -> ()

(*
and bounded_wf_validate_map_group_bounded
  (env: name_env)
  (left_elems: Spec.typ)
  (left_tables: Spec.typ)
  (g1: group)
  (left_elems1: Spec.typ)
  (left_tables1: Spec.typ)
  (wf: ast0_wf_validate_map_group left_elems left_tables g1 left_elems1 left_tables1)
: Lemma
  (requires
    bounded_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 wf
  )
  (ensures
    group_bounded env g1
  )
  (decreases wf)
  [SMTPat (bounded_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 wf)]
= match wf with
| RMChoice left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    bounded_wf_validate_map_group_bounded env left_elems left_tables g1 left_elems1 left_tables1 s1;
    bounded_wf_validate_map_group_bounded env  left_elems left_tables g2 left_elems2 left_tables2 s2
| RMConcat left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    bounded_wf_validate_map_group_bounded env left_elems left_tables g1 left_elems1 left_tables1 s1;
    bounded_wf_validate_map_group_bounded env left_elems1 left_tables1 g2 left_elems2 left_tables2 s2
| RMZeroOrOne left_elems left_tables g left_elems' left_tables' s ->
    bounded_wf_validate_map_group_bounded env left_elems left_tables g left_elems' left_tables' s
| RMElemLiteral left_elems left_tables cut key value s' ->
    bounded_wf_typ_bounded env value s'
| RMZeroOrMore left_elems left_tables key value s_key s_value v_key ->
    bounded_wf_typ_bounded env key s_key;
    bounded_wf_typ_bounded env value s_value
*)

and bounded_wf_parse_map_group_bounded
  (env: name_env)
  (g: elab_map_group)
  (wf: ast0_wf_parse_map_group g)
: Lemma
  (requires
    bounded_wf_parse_map_group env g wf
  )
  (ensures
      bounded_elab_map_group env g
  )
  (decreases wf)
  [SMTPat (bounded_wf_parse_map_group env g wf)]
= match wf with
  | WfMZeroOrMore key value except s_key s_value s_except ->
    bounded_wf_typ_bounded env key s_key;
    bounded_wf_map_constraint_bounded env except s_except;
    bounded_wf_typ_bounded env value s_value
  | WfMLiteral cut _ key value s ->
    bounded_wf_typ_bounded env value s
  | WfMZeroOrOne _ _
  | WfMConcat _ _ _ _
  | WfMChoice _ _ _ _
  | WfMNop _
  -> ()

and bounded_wf_map_constraint_bounded
  (env: name_env)
  (g: map_constraint)
  (wf: ast0_wf_map_constraint g)
: Lemma
  (requires
    bounded_wf_map_constraint env g wf
  )
  (ensures
    bounded_map_constraint env g
  )
  (decreases wf)
  [SMTPat (bounded_wf_map_constraint env g wf)]
= match wf with
  | WfMCFalse -> ()
  | WfMCKeyValue key s_key value s_value ->
    bounded_wf_typ_bounded env key s_key;
    bounded_wf_typ_bounded env value s_value
  | WfMCNot g1 wf1 ->
    bounded_wf_map_constraint_bounded env g1 wf1
  | WfMCOr g1 wf1 g2 wf2
  | WfMCAnd g1 wf1 g2 wf2 ->
    bounded_wf_map_constraint_bounded env g1 wf1;
    bounded_wf_map_constraint_bounded env g2 wf2

let spec_true : prop = True

[@@ sem_attr ]
let rec spec_wf_typ
  (env: sem_env)
  (guard_choices: bool)
  (t: typ)
  (wf: ast0_wf_typ t)
: GTot prop
  (decreases wf)
= bounded_wf_typ env.se_bound t wf /\ begin match wf with
| WfTRewrite t t' s' ->
  spec_wf_typ env guard_choices _ s' /\
  Spec.typ_equiv (typ_sem env t) (typ_sem env t')
| WfTArray g s ->
  spec_wf_array_group env g s
| WfTTagged _ t' s' ->
  spec_wf_typ env true t' s'
| WfTMap g1 (* ty1 ty2 s1 *) g2 s2 ->
//    Spec.restrict_map_group (map_group_sem env g1) (map_group_sem env g2) /\
//    spec_wf_validate_map_group env Spec.t_always_false Spec.t_always_false g1 ty1 ty2 s1 /\
    map_group_sem env g1 == elab_map_group_sem env g2 /\
    spec_wf_parse_map_group env _ s2
| WfTChoice t1 t2 s1 s2 ->
  spec_wf_typ env guard_choices t1 s1 /\
  spec_wf_typ env guard_choices t2 s2 /\
  (guard_choices ==> Spec.typ_disjoint (typ_sem env t1) (typ_sem env t2))
| WfTDetCbor base _ wfdest ->
  Spec.typ_equiv (typ_sem env base) Spec.bstr /\
  spec_wf_typ env true _ wfdest
| WfTStrSize k base range lo hi ->
  Spec.typ_equiv (typ_sem env base) (Spec.str_gen (U8.uint_to_t k)) // TODO: support chaining of controls, e.g. bstr .size x..y .cbor ty, with `Spec.typ_included`
  /\ begin match extract_range_value env range with
  | Some (ilo, ihi) -> lo == eval_int_value ilo /\ hi == eval_int_value ihi
  | _ -> False
  end
| WfTIntRange base_from base_inclusive base_to from to ->
  begin match extract_int_value env base_from with
  | None -> False
  | Some v -> eval_int_value v == from
  end /\
  begin match extract_int_value env base_to with
  | None -> False
  | Some v -> eval_int_value v == (if base_inclusive then to else to + 1)
  end
| WfTDef _
| WfTElem _ -> True
end

and spec_wf_array_group
  (env: sem_env)
  (g: group)
  (wf: ast0_wf_array_group g)
: GTot prop
  (decreases wf)
= bounded_wf_array_group env.se_bound g wf /\ begin match wf with
| WfAElem _ _ ty prf ->
  spec_wf_typ env true ty prf
| WfAZeroOrOne g s ->
  spec_wf_array_group env g s /\
  Spec.array_group_is_nonempty (array_group_sem env g)
| WfAZeroOrOneOrMore g s g' ->
  spec_wf_array_group env g s /\
  (
      let a = array_group_sem env g in
      Spec.array_group_is_nonempty a /\
      Spec.array_group_concat_unique_strong a a
  )
| WfAConcat g1 g2 s1 s2 ->
  spec_wf_array_group env g1 s1 /\
  spec_wf_array_group env g2 s2 /\
  Spec.array_group_concat_unique_weak (array_group_sem env g1) (array_group_sem env g2)
| WfAChoice g1 g2 s1 s2 ->
  spec_wf_array_group env g1 s1 /\
  spec_wf_array_group env g2 s2 /\
  Spec.array_group_disjoint (array_group_sem env g1) (Spec.close_array_group (array_group_sem env g2))
| WfARewrite g1 g2 s2 ->
  Spec.array_group_equiv (array_group_sem env g1) (array_group_sem env g2) /\
  spec_wf_array_group env g2 s2
(*
| WfADef n -> True
*)
end

and spec_wf_parse_map_group
  (env: sem_env)
  (g: elab_map_group)
  (wf: ast0_wf_parse_map_group g)
: GTot prop
  (decreases wf)
= bounded_wf_parse_map_group env.se_bound g wf /\ begin match wf with
| WfMChoice g1' s1 g2' s2 ->
    spec_wf_parse_map_group env g1' s1 /\
    spec_wf_parse_map_group env g2' s2 /\
    Spec.map_group_choice_compatible
      (elab_map_group_sem env g1')
      (elab_map_group_sem env g2')
| WfMConcat g1 s1 g2 s2 ->
    spec_wf_parse_map_group env g1 s1 /\
    spec_wf_parse_map_group env g2 s2 /\
    (
      Spec.map_constraint_disjoint (spec_map_group_footprint env g1) (spec_map_group_footprint env g2)
    )
| WfMZeroOrOne g s ->
    spec_wf_parse_map_group env g s /\
    Spec.MapGroupFail? (Spec.apply_map_group_det (elab_map_group_sem env g) Cbor.cbor_map_empty)
| WfMLiteral cut _ key value s ->
    spec_wf_typ env true value s
| WfMZeroOrMore key value except s_key s_value s_except ->
    spec_wf_typ env true key s_key /\
    spec_wf_map_constraint env except s_except /\
    spec_wf_typ env true value s_value
| WfMNop _ -> spec_true
end

and spec_wf_map_constraint
  (env: sem_env)
  (g: map_constraint)
  (wf: ast0_wf_map_constraint g)
: GTot prop
  (decreases wf)
= bounded_wf_map_constraint env.se_bound g wf /\ begin match wf with
  | WfMCFalse -> True
  | WfMCKeyValue key s_key value s_value ->
    spec_wf_typ env false key s_key /\
    spec_wf_typ env false value s_value
  | WfMCNot mc1 s_mc1 ->
    spec_wf_map_constraint env mc1 s_mc1
  | WfMCAnd mc1 s_mc1 mc2 s_mc2
  | WfMCOr mc1 s_mc1 mc2 s_mc2 ->
    spec_wf_map_constraint env mc1 s_mc1 /\
    spec_wf_map_constraint env mc2 s_mc2
end

(*
and spec_wf_validate_map_group
  (env: sem_env)
  (left_elems: Spec.typ)
  (left_tables: Spec.typ)
  (g: group)
  (left_elems': Spec.typ)
  (left_tables': Spec.typ)
  (s: ast0_wf_validate_map_group left_elems left_tables g left_elems' left_tables')
: Tot prop
  (decreases s)
= bounded_wf_validate_map_group env.se_bound left_elems left_tables g left_elems' left_tables' s /\ begin match s with
| RMChoice left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    spec_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 s1 /\
    spec_wf_validate_map_group env left_elems left_tables g2 left_elems2 left_tables2 s2
| RMConcat left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    spec_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 s1 /\
    spec_wf_validate_map_group env left_elems1 left_tables1 g2 left_elems2 left_tables2 s2
| RMZeroOrOne left_elems left_tables g left_elems' left_tables' s ->
    spec_wf_validate_map_group env left_elems left_tables g left_elems' left_tables' s
| RMElemLiteral left_elems left_tables cut key value s' ->
    spec_wf_typ env value s' /\
    Spec.typ_disjoint (left_elems `Spec.t_choice` left_tables) (Spec.t_literal (eval_literal key))
| RMZeroOrMore left_elems left_tables key value s_key s_value v_key ->
    spec_wf_typ env key s_key /\
    spec_wf_typ env value s_value /\
    v_key == (typ_sem env key) /\
    Spec.typ_disjoint left_tables v_key
end
*)

let spec_wf_parse_map_group_concat
  (env: sem_env)
  (g1: elab_map_group)
  (s1: ast0_wf_parse_map_group g1)
  (g2: elab_map_group)
  (s2: ast0_wf_parse_map_group g2)
: Lemma
  (spec_wf_parse_map_group env (MGConcat g1 g2) (WfMConcat g1 s1 g2 s2) <==> (
    bounded_wf_parse_map_group env.se_bound (g1) (s1) /\
    bounded_wf_parse_map_group env.se_bound (g2) (s2) /\ (
    spec_wf_parse_map_group env g1 s1 /\
    spec_wf_parse_map_group env g2 s2 /\
    (
      Spec.map_constraint_disjoint (spec_map_group_footprint env g1) (spec_map_group_footprint env g2)
    )
  )))
= ()

let spec_wf_parse_map_group_choice
  (env: sem_env)
  (g1: elab_map_group)
  (s1: ast0_wf_parse_map_group g1)
  (g2: elab_map_group)
  (s2: ast0_wf_parse_map_group g2)
: Lemma
  (spec_wf_parse_map_group env (MGChoice g1 g2) (WfMChoice g1 s1 g2 s2) <==> (
    bounded_wf_parse_map_group env.se_bound (MGChoice g1 g2) (WfMChoice g1 s1 g2 s2) /\ (
    spec_wf_parse_map_group env g1 s1 /\
    spec_wf_parse_map_group env g2 s2 /\
    (
      Spec.map_group_choice_compatible (elab_map_group_sem env g1) (elab_map_group_sem env g2)
    )
  )))
= ()

#restart-solver
let rec spec_wf_typ_incr
  (env env': sem_env)
  (guard_choices: bool)
  (g: typ)
  (wf: ast0_wf_typ g)
: Lemma
  (requires sem_env_included env env' /\
    bounded_wf_typ env.se_bound g wf
  )
  (ensures
    spec_wf_typ env guard_choices g wf <==>
      spec_wf_typ env' guard_choices g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_typ env guard_choices g wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_typ env' guard_choices g wf)];
  ]]
= match wf with
  | WfTRewrite _ _ s' ->
    spec_wf_typ_incr env env' guard_choices _ s'
  | WfTArray g s ->
    spec_wf_array_group_incr env env' g s
  | WfTDetCbor _ t' s'
  | WfTTagged _ t' s' ->
    spec_wf_typ_incr env env' true t' s'
  | WfTMap g1 (* ty1 ty2 s1 *) g2 s2 ->
//    spec_wf_validate_map_group_incr env env' Spec.t_always_false Spec.t_always_false g1 ty1 ty2 s1;
    spec_wf_parse_map_group_incr env env' _ s2
  | WfTChoice t1 t2 s1 s2 ->
    spec_wf_typ_incr env env' guard_choices t1 s1;
    spec_wf_typ_incr env env' guard_choices t2 s2
  | WfTIntRange _ _ _ _ _
  | WfTStrSize _ _ _ _ _
  | WfTElem _
  | WfTDef _ -> ()

and spec_wf_array_group_incr
  (env env': sem_env)
  (g: group)
  (wf: ast0_wf_array_group g)
: Lemma
  (requires sem_env_included env env' /\
    bounded_wf_array_group env.se_bound g wf
  )
  (ensures
    spec_wf_array_group env g wf <==>
      spec_wf_array_group env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_array_group env g wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_array_group env' g wf)];
  ]]
= match wf with
  | WfAElem _ _ ty prf ->
    spec_wf_typ_incr env env' true ty prf
  | WfAZeroOrOne g s ->
    spec_wf_array_group_incr env env' g s
  | WfAZeroOrOneOrMore g s g' ->
    spec_wf_array_group_incr env env' g s
  | WfAConcat g1 g2 s1 s2
  | WfAChoice g1 g2 s1 s2 ->
    spec_wf_array_group_incr env env' g1 s1;
    spec_wf_array_group_incr env env' g2 s2
  | WfARewrite g1 g2 s2 ->
    spec_wf_array_group_incr env env' g2 s2

and spec_wf_map_constraint_incr
  (env env': sem_env)
  (g: map_constraint)
  (wf: ast0_wf_map_constraint g)
: Lemma
  (requires sem_env_included env env' /\
    bounded_wf_map_constraint env.se_bound g wf
  )
  (ensures
      spec_wf_map_constraint env g wf <==> spec_wf_map_constraint env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_map_constraint env g wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_map_constraint env' g wf)];
  ]]
= match wf with
  | WfMCFalse -> ()
  | WfMCKeyValue key s_key value s_value ->
    spec_wf_typ_incr env env' false key s_key;
    spec_wf_typ_incr env env' false value s_value
  | WfMCNot g1 wf1 ->
    spec_wf_map_constraint_incr env env' g1 wf1
  | WfMCOr g1 wf1 g2 wf2
  | WfMCAnd g1 wf1 g2 wf2 ->
    spec_wf_map_constraint_incr env env' g1 wf1;
    spec_wf_map_constraint_incr env env' g2 wf2

(*    
  | WfADef _ -> ()
*)

(*
and spec_wf_validate_map_group_incr
  (env env': sem_env)
  (left_elems: Spec.typ)
  (left_tables: Spec.typ)
  (g1: group)
  (left_elems1: Spec.typ)
  (left_tables1: Spec.typ)
  (wf: ast0_wf_validate_map_group left_elems left_tables g1 left_elems1 left_tables1)
: Lemma
  (requires sem_env_included env env' /\
    spec_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 wf
  )
  (ensures
    spec_wf_validate_map_group env' left_elems left_tables g1 left_elems1 left_tables1 wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_validate_map_group env left_elems left_tables g1 left_elems1 left_tables1 wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_validate_map_group env' left_elems left_tables g1 left_elems1 left_tables1 wf)];
  ]]
= match wf with
| RMChoice left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    spec_wf_validate_map_group_incr env env' left_elems left_tables g1 left_elems1 left_tables1 s1;
    spec_wf_validate_map_group_incr env env'  left_elems left_tables g2 left_elems2 left_tables2 s2
| RMConcat left_elems left_tables g1 left_elems1 left_tables1 s1 g2 left_elems2 left_tables2 s2 ->
    spec_wf_validate_map_group_incr env env' left_elems left_tables g1 left_elems1 left_tables1 s1;
    spec_wf_validate_map_group_incr env env' left_elems1 left_tables1 g2 left_elems2 left_tables2 s2
| RMZeroOrOne left_elems left_tables g left_elems' left_tables' s ->
    spec_wf_validate_map_group_incr env env'  left_elems left_tables g left_elems' left_tables' s
| RMElemLiteral left_elems left_tables cut key value s' ->
    spec_wf_typ_incr env env' value s'
| RMZeroOrMore left_elems left_tables key value s_key s_value v_key ->
    spec_wf_typ_incr env env' key s_key;
    spec_wf_typ_incr env env' value s_value
*)

and spec_wf_parse_map_group_incr
  (env env': sem_env)
  (g: elab_map_group)
  (wf: ast0_wf_parse_map_group g)
: Lemma
  (requires sem_env_included env env' /\
    bounded_wf_parse_map_group env.se_bound g wf
  )
  (ensures
    spec_wf_parse_map_group env g wf <==>
      spec_wf_parse_map_group env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_parse_map_group env g wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_parse_map_group env' g wf)];
  ]]
= match wf with
  | WfMNop _ -> ()
  | WfMConcat g1' s1 g2' s2
  | WfMChoice g1' s1 g2' s2 ->
    spec_wf_parse_map_group_incr env env' g1' s1;
    spec_wf_parse_map_group_incr env env' g2' s2
  | WfMZeroOrOne g s ->
    spec_wf_parse_map_group_incr env env' g s
  | WfMLiteral cut _ key value s ->
    spec_wf_typ_incr env env' true value s
  | WfMZeroOrMore key value except s_key s_value s_except ->
    spec_wf_typ_incr env env' true key s_key;
    spec_wf_map_constraint_incr env env' except s_except;
    spec_wf_typ_incr env env' true value s_value

[@@  sem_attr]
inline_for_extraction
let ast_env_elem0 (s: name_env_elem) : Tot Type0 =
  match s with
  | NType -> typ
  | NGroup -> group

[@@  sem_attr]
let ast_env_elem0_bounded (env: name_env) (#s: name_env_elem) (x: ast_env_elem0 s) : Tot bool =
  match s with
  | NType ->
    typ_bounded env x
  | NGroup ->
    group_bounded env x

[@@ sem_attr]
let ast_env_elem0_sem (e_sem_env: sem_env) (#s: name_env_elem) (x: ast_env_elem0 s) : Pure (sem_env_elem s)
  (requires ast_env_elem0_bounded e_sem_env.se_bound x)
  (ensures fun _ -> True)
= match s with
  | NType -> typ_sem_elem e_sem_env x
  | NGroup -> Ghost.hide (array_group_sem e_sem_env x, map_group_sem e_sem_env x)
  
let ast_env_elem_prop (e_sem_env: sem_env) (s: name_env_elem) (phi: sem_env_elem s) (x: ast_env_elem0 s) : GTot prop =
  ast_env_elem0_bounded e_sem_env.se_bound x /\
  begin
    let sem = ast_env_elem0_sem e_sem_env x in
    match s with
    | NType ->
      Spec.typ_equiv #None (sem_of_type_sem sem) (sem_of_type_sem phi)
    | NGroup ->
      let sem : Spec.array_group None & Spec.map_group = Ghost.reveal sem in
      let phi : Spec.array_group None & Spec.map_group = Ghost.reveal phi in
      Spec.array_group_equiv #None (fst sem) (fst phi) /\ snd sem == snd phi
  end

let ast_env_elem_prop_included (e1 e2: sem_env) (s: name_env_elem) (phi: sem_env_elem s) (x: ast_env_elem0 s) : Lemma
  (requires sem_env_included e1 e2 /\
    ast_env_elem_prop e1 s phi x
  )
  (ensures ast_env_elem_prop e2 s phi x)
  [SMTPat (ast_env_elem_prop e1 s phi x); SMTPat (ast_env_elem_prop e2 s phi x)]
= ()

[@@ sem_attr]
let ast_env_elem (e_sem_env: sem_env) (s: name_env_elem) (phi: sem_env_elem s) : Type0 =
  (x: ast_env_elem0 s { ast_env_elem_prop e_sem_env s phi x })

[@@ sem_attr]
noeq
type wf_ast_env_elem0 (s: name_env_elem) (x: ast_env_elem0 s) : Type0 =
{
  wf_typ: option (_: squash (s == NType) & ast0_wf_typ x);
//  wf_array: option (_: squash (s == NGroup) & ast0_wf_array_group x);
  // TODO: wf_map
}

let wf_ast_env_elem_prop (e_sem_env: sem_env) (s: name_env_elem) (x: ast_env_elem0 s) (y: (wf_ast_env_elem0 s x)) : GTot prop =
  begin match y.wf_typ with
  | None -> True
  | Some (| _, y |) -> spec_wf_typ e_sem_env true x y
  end
  /\ True (* begin match y.wf_array with
  | None -> True
  | Some (| _, y |) -> spec_wf_array_group e_sem_env x y
  end
*)
  // TODO: wf_map

let wf_ast_env_elem_prop_included (e1 e2: sem_env) (s: name_env_elem) (x: ast_env_elem0 s) (y: (wf_ast_env_elem0 s x)) : Lemma
  (requires sem_env_included e1 e2 /\
    wf_ast_env_elem_prop e1 s x y
  )
  (ensures wf_ast_env_elem_prop e2 s x y)
  [SMTPat (ast_env_elem_prop e1 s x y); SMTPat (ast_env_elem_prop e2 s x y)]
= ()

[@@ sem_attr]
let wf_ast_env_elem (e_sem_env: sem_env) (s: name_env_elem) (x: ast_env_elem0 s) =
  (y: (wf_ast_env_elem0 s x) { wf_ast_env_elem_prop e_sem_env s x y })

[@@  sem_attr]
noeq
type ast_env = {
  e_sem_env: sem_env;
  e_env: (i: name e_sem_env.se_bound) -> (ast_env_elem e_sem_env (Some?.v (e_sem_env.se_bound i)) (e_sem_env.se_env i));
  e_wf: (i: name e_sem_env.se_bound) -> wf_ast_env_elem e_sem_env (Some?.v (e_sem_env.se_bound i)) (e_env i);
}

[@@"opaque_to_smt"] irreducible // because of false_elim
let e_env_empty (i: name empty_name_env) : Tot (ast_env_elem empty_sem_env (Some?.v (empty_name_env i)) (empty_sem_env.se_env i)) = false_elim ()

[@@"opaque_to_smt"] irreducible // because of false_elim
let e_wf_empty (i: name empty_name_env) : Tot (wf_ast_env_elem empty_sem_env (Some?.v (empty_name_env i)) (e_env_empty i)) = false_elim ()

[@@"opaque_to_smt";  sem_attr]
let empty_ast_env : (e: ast_env {
  e.e_sem_env.se_bound == empty_name_env
}) = {
  e_sem_env = empty_sem_env;
  e_env = e_env_empty;
  e_wf = e_wf_empty;
}

let ast_env_included
  (e1 e2: ast_env)
: Tot prop
= sem_env_included e1.e_sem_env e2.e_sem_env /\
  (forall (i: name e1.e_sem_env.se_bound) . e2.e_env i == e1.e_env i) /\
  (forall (i: name e1.e_sem_env.se_bound) . Some? (e1.e_wf i).wf_typ ==> ((e1.e_wf i).wf_typ == (e2.e_wf i).wf_typ)) /\
  True // (forall (i: name e1.e_sem_env.se_bound) . Some? (e1.e_wf i).wf_array ==> ((e1.e_wf i).wf_array == (e2.e_wf i).wf_array))
// TODO: wf_map

let ast_env_included_trans (s1 s2 s3: ast_env) : Lemma
  (requires (ast_env_included s1 s2 /\ ast_env_included s2 s3))
  (ensures (ast_env_included s1 s3))
  [SMTPat (ast_env_included s1 s3); SMTPat (ast_env_included s1 s2)]
= ()

[@@"opaque_to_smt";  sem_attr]
let ast_env_extend_gen
  (e: ast_env)
  (new_name: string)
  (kind: name_env_elem)
  (x: ast_env_elem0 kind)
: Pure ast_env
    (requires
      ast_env_elem0_bounded e.e_sem_env.se_bound x /\
      (~ (new_name `name_mem` e.e_sem_env.se_bound))
    )
    (ensures fun e' ->
      let s = ast_env_elem0_sem e.e_sem_env x in
      e'.e_sem_env == sem_env_extend_gen e.e_sem_env new_name kind s /\
      ast_env_included e e' /\
      e'.e_env new_name == x /\
      None? (e'.e_wf new_name).wf_typ /\
      True // None? (e'.e_wf new_name).wf_array
    )
= let s = ast_env_elem0_sem e.e_sem_env x in
  let se' = sem_env_extend_gen e.e_sem_env new_name kind s in
  {
    e_sem_env = se';
    e_env = (fun (i: name se'.se_bound) ->
      if i = new_name
      then x
      else e.e_env i
    );
    e_wf = (fun (i: name se'.se_bound) ->
      if i = new_name
      then { wf_typ = None; (* wf_array = None *) }
      else e.e_wf i
    );
  }

[@@ sem_attr]
let ast_env_extend_gen'
  (e: ast_env)
  (new_name: string)
  (new_name_fresh: squash (~ (new_name `name_mem` e.e_sem_env.se_bound)))
  (kind: name_env_elem)
  (x: ast_env_elem0 kind)
  (x_bounded: squash (ast_env_elem0_bounded e.e_sem_env.se_bound x))
: Tot (e' : ast_env {
      let s = ast_env_elem0_sem e.e_sem_env x in
      e'.e_sem_env == sem_env_extend_gen e.e_sem_env new_name kind s /\
      ast_env_included e e' /\
      e'.e_env new_name == x
  })
= ast_env_extend_gen e new_name kind x

[@@"opaque_to_smt";  sem_attr]
let ast_env_set_wf
  (e: ast_env)
  (new_name: name e.e_sem_env.se_bound)
  (wf: wf_ast_env_elem e.e_sem_env (Some?.v (e.e_sem_env.se_bound new_name)) (e.e_env new_name))
: Pure ast_env
    (requires
      (Some? (e.e_wf new_name).wf_typ ==> (e.e_wf new_name).wf_typ == wf.wf_typ) /\
True //      (Some? (e.e_wf new_name).wf_array ==> (e.e_wf new_name).wf_array == wf.wf_array)
    )
    (ensures fun e' ->
      e'.e_sem_env == e.e_sem_env /\
      ast_env_included e e' /\
      e'.e_wf new_name == wf
    )
=
  {
    e with
    e_wf = (fun (i: name e.e_sem_env.se_bound) ->
      if i = new_name
      then wf
      else e.e_wf i
    );
  }

let ast_env_extend_typ_with_pre
  (e: ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t)
: GTot prop
=
    e.e_sem_env.se_bound new_name == None /\
    typ_bounded e.e_sem_env.se_bound t /\
    bounded_wf_typ (extend_name_env e.e_sem_env.se_bound new_name NType) t t_wf /\
    spec_wf_typ (ast_env_extend_gen e new_name NType t).e_sem_env true t t_wf

[@@sem_attr]
let ast_env_extend_typ_with
  (e: ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    ast_env_extend_typ_with_pre e new_name t t_wf  
  })
: Tot (e': ast_env {
      ast_env_included e e' /\
      e'.e_sem_env.se_bound new_name == Some NType /\
      t == e'.e_env new_name
  })
= ast_env_set_wf (ast_env_extend_gen e new_name NType t) new_name { wf_typ = Some (| (), t_wf |) ; (* wf_array = None *) }

let wf_ast_env = (e: ast_env { forall (i: typ_name e.e_sem_env.se_bound) . Some? (e.e_wf i).wf_typ })

[@@ sem_attr]
let empty_wf_ast_env : wf_ast_env = empty_ast_env

let wf_ast_env_extend_typ_with_pre
  (e: ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t)
: GTot prop
=
    e.e_sem_env.se_bound new_name == None /\
    typ_bounded e.e_sem_env.se_bound t /\
    bounded_wf_typ (extend_name_env e.e_sem_env.se_bound new_name NType) t t_wf /\
    spec_wf_typ (ast_env_extend_gen e new_name NType t).e_sem_env true t t_wf

[@@sem_attr]
let wf_ast_env_extend_typ_with
  (e: wf_ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    wf_ast_env_extend_typ_with_pre e new_name t t_wf
  })
: Tot (e': wf_ast_env {
      ast_env_included e e' /\
      e'.e_sem_env.se_bound == extend_name_env e.e_sem_env.se_bound new_name NType /\
      e'.e_sem_env.se_bound new_name == Some NType /\
      sem_of_type_sem (e'.e_sem_env.se_env new_name) == typ_sem e.e_sem_env t /\
      (e'.e_env new_name <: typ) == t
  })
= ast_env_set_wf (ast_env_extend_gen e new_name NType t) new_name { wf_typ = (Some (| (), t_wf |)) }

let wf_ast_env_extend_typ_with_weak_pre
  (e: ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t)
: GTot prop
=
    e.e_sem_env.se_bound new_name == None /\
    typ_bounded e.e_sem_env.se_bound t /\
    bounded_wf_typ e.e_sem_env.se_bound t t_wf /\
    spec_wf_typ e.e_sem_env true t t_wf

let wf_ast_env_extend_typ_with_weak_pre_correct
  (e: wf_ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t)
: Lemma
  (requires wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf)
  (ensures wf_ast_env_extend_typ_with_pre e new_name t t_wf)
  [SMTPat (wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf)]
= bounded_wf_typ_incr e.e_sem_env.se_bound (ast_env_extend_gen e new_name NType t).e_sem_env.se_bound t t_wf

[@@sem_attr]
let wf_ast_env_extend_typ_with_weak
  (e: wf_ast_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    wf_ast_env_extend_typ_with_weak_pre e new_name t t_wf
  })
: Tot (e': wf_ast_env {
      ast_env_included e e' /\
      e'.e_sem_env.se_bound == extend_name_env e.e_sem_env.se_bound new_name NType /\
      e'.e_sem_env.se_bound new_name == Some NType /\
      sem_of_type_sem (e'.e_sem_env.se_env new_name) == typ_sem e.e_sem_env t /\
      (e'.e_env new_name <: typ) == t
  })
= wf_ast_env_extend_typ_with e new_name t t_wf

[@@sem_attr]
let wf_ast_env_extend_group
  (e: wf_ast_env)
  (new_name: string)
  (t: group)
  (sq1: squash (e.e_sem_env.se_bound new_name == None))
  (sq2: squash (group_bounded e.e_sem_env.se_bound t))
: Tot (e': wf_ast_env {
      ast_env_included e e' /\
      e'.e_sem_env.se_bound new_name == Some NGroup /\
      (e'.e_env new_name <: group) == t
  })
= ast_env_extend_gen e new_name NGroup t

[@@ base_attr ]
noeq
type target_elem_type =
| TTUnit
| TTUInt8
| TTUInt64
| TTInt64
| TTString
| TTBool
| TTAny
| TTAlwaysFalse

[@@ base_attr ]
noeq
type target_type =
| TTElem of target_elem_type
| TTDef of string
| TTOption of target_type
| TTPair: target_type -> target_type -> target_type
| TTUnion: target_type -> target_type -> target_type
| TTArray of target_type
| TTTable: target_type -> target_type -> target_type

[@@ base_attr ]
let rec target_type_bounded
  (bound: name_env)
  (t: target_type)
: Tot bool
= match t with
  | TTDef s -> bound s = Some NType
  | TTPair t1 t2
  | TTTable t1 t2
  | TTUnion t1 t2 ->
    target_type_bounded bound t1 &&
    target_type_bounded bound t2
  | TTArray a
  | TTOption a ->
    target_type_bounded bound a
  | TTElem _ -> true

let rec target_type_bounded_incr
  (bound bound': name_env)
  (t: target_type)
: Lemma
  (requires
    name_env_included bound bound' /\
    target_type_bounded bound t
  )
  (ensures
    target_type_bounded bound' t
  )
  [SMTPatOr [
    [SMTPat (name_env_included bound bound'); SMTPat (target_type_bounded bound t)];
    [SMTPat (name_env_included bound bound'); SMTPat (target_type_bounded bound' t)];
  ]]
= match t with
  | TTPair t1 t2
  | TTTable t1 t2
  | TTUnion t1 t2 ->
    target_type_bounded_incr bound bound' t1;
    target_type_bounded_incr bound bound' t2
  | TTArray a
  | TTOption a ->
    target_type_bounded_incr bound bound' a
  | TTElem _
  | TTDef _ -> ()

[@@ sem_attr ]
type target_spec_env (bound: name_env) =
  (typ_name bound -> GTot Type0)

irreducible [@@"opaque_to_smt"]
let empty_target_spec_env : target_spec_env empty_name_env =
  fun _ -> false_elim ()

let target_spec_env_included (#bound1: name_env) (t1: target_spec_env bound1) (#bound2: name_env) (t2: target_spec_env bound2) : GTot prop =
  name_env_included bound1 bound2 /\
  (forall (x: typ_name bound1) . t1 x == t2 x)

noextract [@@noextract_to "krml"; sem_attr]
let target_spec_env_extend
  (bound: name_env)
  (env: target_spec_env bound)
  (n: string { ~ (name_mem n bound) })
  (s: name_env_elem)
  ([@@@strictly_positive] t: Type0)
: Pure (target_spec_env (extend_name_env bound n s))
    (requires True)
    (ensures fun env' -> target_spec_env_included env env')
= fun n' -> if n' = n then t else env n'

module U8 = FStar.UInt8
module U64 = FStar.UInt64

noextract
let table
  (key: Type0)
  ([@@@strictly_positive] value: Type0)
: GTot Type0
= Map.t key (list value) // that the list be a singleton is a serialization constraint, see below

module I64 = FStar.Int64

[@@ sem_attr ]
let target_elem_type_sem
  (t: target_elem_type)
: GTot eqtype
= match t with
  | TTUInt8 -> U8.t
  | TTUInt64 -> U64.t
  | TTInt64 -> I64.t
  | TTUnit -> unit
  | TTBool -> bool
  | TTString -> Seq.seq U8.t
  | TTAny -> Cbor.cbor
  | TTAlwaysFalse -> squash False

[@@ sem_attr ]
let rec target_type_sem
  (#bound: name_env)
  (env: target_spec_env bound)
  (t: target_type)
: Ghost Type0
  (requires target_type_bounded bound t)
  (ensures fun _ -> True)
= match t with
  | TTDef s -> env s
  | TTPair t1 t2 -> target_type_sem env t1 & target_type_sem env t2
  | TTUnion t1 t2 -> target_type_sem env t1 `either` target_type_sem env t2
  | TTArray a -> list (target_type_sem env a)
  | TTTable t1 t2 -> table (target_type_sem env t1) (target_type_sem env t2)
  | TTOption a -> option (target_type_sem env a)
  | TTElem e -> target_elem_type_sem e

let rec target_type_sem_incr
  (#bound #bound': name_env)
  (env: target_spec_env bound)
  (env': target_spec_env bound')
  (t: target_type)
: Lemma
  (requires target_type_bounded bound t /\
    target_spec_env_included env env'
  )
  (ensures target_type_sem env t == target_type_sem env' t)
  [SMTPatOr [
    [SMTPat (target_spec_env_included env env'); SMTPat (target_type_sem env t)];
    [SMTPat (target_spec_env_included env env'); SMTPat (target_type_sem env' t)];
  ]]
= match t with
  | TTPair t1 t2
  | TTTable t1 t2
  | TTUnion t1 t2 ->
    target_type_sem_incr env env' t1;
    target_type_sem_incr env env' t2
  | TTArray a
  | TTOption a ->
    target_type_sem_incr env env' a
  | TTElem _
  | TTDef _ -> ()

noextract
noeq
type rectype (f: [@@@strictly_positive] Type -> Type) =
| Y of f (rectype f)

let rec target_type_positively_bounded
  (bound: name_env)
  (kbound: name_env)
  (t: target_type)
: Tot bool
= match t with
  | TTDef s -> bound s = Some NType // s `name_mem` bound
  | TTPair t1 t2
  | TTUnion t1 t2 ->
    target_type_positively_bounded bound kbound t1 &&
    target_type_positively_bounded bound kbound t2
  | TTTable t1 t2 ->
    target_type_bounded kbound t1 &&
    target_type_positively_bounded bound kbound t2
  | TTArray a
  | TTOption a ->
    target_type_positively_bounded bound kbound a
  | TTElem _ -> true

let rec target_type_positively_bounded_incr
  (bound bound': name_env)
  (kbound kbound': name_env)
  (t: target_type)
: Lemma
  (requires
    name_env_included bound bound' /\
    name_env_included kbound kbound' /\
    target_type_positively_bounded bound kbound t
  )
  (ensures
    target_type_positively_bounded bound' kbound' t
  )
  [SMTPatOr [
    [SMTPat (name_env_included bound bound'); SMTPat (name_env_included kbound kbound'); SMTPat (target_type_positively_bounded bound kbound t)];
    [SMTPat (name_env_included bound bound'); SMTPat (name_env_included kbound kbound'); SMTPat (target_type_positively_bounded bound' kbound' t)];
  ]]
= match t with
  | TTPair t1 t2
  | TTUnion t1 t2 ->
    target_type_positively_bounded_incr bound bound' kbound kbound' t1;
    target_type_positively_bounded_incr bound bound' kbound kbound' t2
  | TTTable t1 t2 ->
    target_type_positively_bounded_incr bound bound' kbound kbound' t2  
  | TTArray a
  | TTOption a ->
    target_type_positively_bounded_incr bound bound' kbound kbound' a
  | TTElem _
  | TTDef _ -> ()

let rec target_type_sem'
  (#bound: name_env)
  ([@@@strictly_positive] env: target_spec_env bound)
  (#kbound: name_env)
  (kenv: target_spec_env kbound)
  (t: target_type)
: Ghost Type0
  (requires
    target_type_positively_bounded bound kbound t
  )
  (ensures fun _ -> True)
= match t with
  | TTDef s -> env s
  | TTPair t1 t2 -> target_type_sem' env kenv t1 & target_type_sem' env kenv t2
  | TTUnion t1 t2 -> target_type_sem' env kenv t1 `either` target_type_sem' env kenv t2
  | TTArray a -> list (target_type_sem' env kenv a)
  | TTTable t1 t2 -> table (target_type_sem kenv t1) (target_type_sem' env kenv t2)
  | TTOption a -> option (target_type_sem' env kenv a)
  | TTElem e -> target_elem_type_sem e

let rec target_type_sem'_correct
  (#bound: name_env)
  (env: target_spec_env bound)
  (#kbound: name_env)
  (kenv: target_spec_env kbound)
  (t: target_type)
: Lemma
  (requires
    target_type_positively_bounded bound kbound t /\
    target_spec_env_included kenv env
  )
  (ensures
    target_type_bounded bound t /\
    target_type_sem' env kenv t == target_type_sem env t
  )
  [SMTPat (target_type_sem' env kenv t)]
= match t with
  | TTPair t1 t2
  | TTUnion t1 t2 -> target_type_sem'_correct env kenv t1; target_type_sem'_correct env kenv t2
  | TTTable t1 t2 ->
    target_type_sem'_correct env kenv t2
  | TTOption a
  | TTArray a -> target_type_sem'_correct env kenv a
  | TTElem _
  | TTDef _ -> ()

noextract [@@noextract_to "krml"]
let target_type_sem_rec_body
  (bound: name_env)
  (env: target_spec_env bound)
  (new_name: string { ~ (name_mem new_name bound) })
  (s: name_env_elem)
  (t: target_type { target_type_positively_bounded (extend_name_env bound new_name NType) bound t })
  ([@@@strictly_positive] t': Type0)
: GTot Type0
= target_type_sem' (target_spec_env_extend bound env new_name NType t') env t

let target_type_sem_rec
  (bound: name_env)
  (env: target_spec_env bound)
  (new_name: string { ~ (name_mem new_name bound) })
  (s: name_env_elem)
  (t: target_type { target_type_positively_bounded (extend_name_env bound new_name NType) bound t })
: GTot Type0
= rectype (target_type_sem_rec_body bound env new_name s t)

[@@ sem_attr ]
noextract
noeq type target_type_env
  (bound: name_env)
= {
  te_type: target_spec_env bound;
  te_eq: (n: typ_name bound) -> eq_test (te_type n);
}

[@@ sem_attr ]
noextract
let empty_target_type_env : target_type_env empty_name_env = {
  te_type = empty_target_spec_env;
  te_eq = (fun _ -> mk_eq_test (fun _ _ -> true)); // dummy
}

noextract [@@noextract_to "krml"; sem_attr]
let target_type_env_extend
  (bound: name_env)
  (env: target_type_env bound)
  (n: string { ~ (name_mem n bound) })
  (s: name_env_elem)
  (t: Type0)
  (eq: eq_test t)
: Pure (target_type_env (extend_name_env bound n s))
    (requires True)
    (ensures fun env' -> target_spec_env_included env.te_type env'.te_type)
= {
  te_type = target_spec_env_extend bound env.te_type n s t;
  te_eq = (fun n' -> if n' = n then coerce_eq () eq else coerce_eq () (env.te_eq n'));
}

[@@ sem_attr ]
noextract
let rec target_type_eq
  (#bound: name_env)
  (env: target_type_env bound)
  (t: target_type { target_type_bounded bound t })
: Tot (eq_test (target_type_sem env.te_type t))
  (decreases t)
= match t returns eq_test (target_type_sem env.te_type t) with
  | TTElem e -> eqtype_eq (target_elem_type_sem e)
  | TTDef s -> env.te_eq s
  | TTOption t' -> option_eq (target_type_eq env t')
  | TTPair t1 t2 -> pair_eq (target_type_eq env t1) (target_type_eq env t2)
  | TTArray a -> list_eq (target_type_eq env a)
  | TTUnion t1 t2 -> either_eq (target_type_eq env t1) (target_type_eq env t2)
  | TTTable tk tv -> map_eq (target_type_sem env.te_type tk) (list_eq (target_type_eq env tv))

type pair_kind =
| PEraseLeft
| PEraseRight
| PKeep

let pair_kind_wf
  (k: pair_kind)
  (t1 t2: Type0)
: GTot prop
= match k with
  | PEraseLeft -> t1 == unit
  | PEraseRight -> t2 == unit
  | _ -> True

inline_for_extraction
let pair (k: pair_kind) (t1 t2: Type0) : Pure Type0
  (requires (pair_kind_wf k t1 t2))
  (ensures (fun _ -> True))
= match k with
  | PEraseLeft -> t2
  | PEraseRight -> t1
  | _ -> t1 & t2

[@base_attr]
let target_type_of_elem_typ
  (x: elem_typ)
: Tot target_elem_type
= match x with
  | ELiteral _ -> TTUnit
  | EBool -> TTBool
  | ESimple -> TTUInt8
  | EByteString
  | ETextString -> TTString
  | EUInt
  | ENInt -> TTUInt64
  | EAny -> TTAny
  | EAlwaysFalse -> TTAlwaysFalse

[@sem_attr]
let rec target_type_of_wf_typ
  (#x: typ)
  (wf: ast0_wf_typ x)
: Tot target_type
  (decreases wf)
= match wf with
  | WfTDetCbor _ _ s
  | WfTRewrite _ _ s -> target_type_of_wf_typ s
  | WfTArray _ s -> target_type_of_wf_array_group s
  | WfTTagged None _ s -> TTPair (TTElem TTUInt64) (target_type_of_wf_typ s)
  | WfTTagged _ _ s -> target_type_of_wf_typ s
  | WfTMap _ (* _ _ _ *) _ s -> target_type_of_wf_map_group s
  | WfTChoice _ _ s1 s2 -> TTUnion (target_type_of_wf_typ s1) (target_type_of_wf_typ s2)
  | WfTElem e -> TTElem (target_type_of_elem_typ e)
  | WfTDef e -> TTDef e
  | WfTStrSize _ _ _ _ _ -> TTElem TTString
  | WfTIntRange _ _ _ from to ->
    if to < 0 || from >= 0
    then TTElem TTUInt64
    else TTElem TTInt64

and target_type_of_wf_array_group
  (#x: group)
  (wf: ast0_wf_array_group x)
: Tot target_type
  (decreases wf)
= match wf with
  | WfAElem _ _ _ s -> target_type_of_wf_typ s
  | WfAZeroOrOne _ s -> TTOption (target_type_of_wf_array_group s)
  | WfAZeroOrOneOrMore _ s g' ->
    let t' = target_type_of_wf_array_group s in
    TTArray t'
  | WfAConcat _ _ s1 s2 -> TTPair (target_type_of_wf_array_group s1) (target_type_of_wf_array_group s2)
  | WfAChoice _ _ s1 s2 -> TTUnion (target_type_of_wf_array_group s1) (target_type_of_wf_array_group s2)
  | WfARewrite _ _ s2 -> target_type_of_wf_array_group s2
(*  
  | WfADef n -> TTDef n
*)

and target_type_of_wf_map_group
  (#x: elab_map_group)
  (wf: ast0_wf_parse_map_group x)
: Tot target_type
  (decreases wf)
= match wf with
  | WfMNop _ -> TTElem TTUnit
  | WfMChoice _ s1 _ s2 -> TTUnion (target_type_of_wf_map_group s1) (target_type_of_wf_map_group s2)
  | WfMConcat _ s1 _ s2 -> TTPair (target_type_of_wf_map_group s1) (target_type_of_wf_map_group s2)
  | WfMZeroOrOne _ s -> TTOption (target_type_of_wf_map_group s)
  | WfMLiteral _ _ _ _ s -> target_type_of_wf_typ s
  | WfMZeroOrMore _ _ _ s_key s_value _ -> TTTable (target_type_of_wf_typ s_key) (target_type_of_wf_typ s_value)

(*
let target_type_of_wf_ast_elem
  (#s: name_env_elem)
  (x: ast_env_elem0 s)
  (y: wf_ast_env_elem0 s x)
: Tot target_type
= match s with
  | NType -> target_type_of_wf_typ #x y
  | -> target_type_of_wf_array_group #x y
  | -> target_type_of_wf_map_group #x y
*)

let rec target_type_of_wf_typ_bounded
  (env: name_env)
  (#x: typ)
  (wf: ast0_wf_typ x)
: Lemma
  (requires bounded_wf_typ env x wf)
  (ensures target_type_bounded env (target_type_of_wf_typ wf))
  (decreases wf)
  [SMTPat (target_type_bounded env (target_type_of_wf_typ wf))]
= match wf with
  | WfTDetCbor _ _ s
  | WfTRewrite _ _ s -> target_type_of_wf_typ_bounded env s
  | WfTArray _ s -> target_type_of_wf_array_group_bounded env s
  | WfTTagged _ _ s -> target_type_of_wf_typ_bounded env s
  | WfTMap _ (* _ _ _ *) _ s -> target_type_of_wf_map_group_bounded env s
  | WfTChoice _ _ s1 s2 ->
    target_type_of_wf_typ_bounded env s1;
    target_type_of_wf_typ_bounded env s2
  | WfTIntRange _ _ _ _ _
  | WfTStrSize _ _ _ _ _
  | WfTElem _
  | WfTDef _ -> ()

and target_type_of_wf_array_group_bounded
  (env: name_env)
  (#x: group)
  (wf: ast0_wf_array_group x)
: Lemma
  (requires bounded_wf_array_group env x wf)
  (ensures target_type_bounded env (target_type_of_wf_array_group wf))
  (decreases wf)
  [SMTPat (target_type_bounded env (target_type_of_wf_array_group wf))]
= match wf with
  | WfAElem _ _ _ s -> target_type_of_wf_typ_bounded env s
  | WfAZeroOrOne _ s -> target_type_of_wf_array_group_bounded env s
  | WfAZeroOrOneOrMore _ s g' ->
    target_type_of_wf_array_group_bounded env s
  | WfAChoice _ _ s1 s2
  | WfAConcat _ _ s1 s2 -> 
    target_type_of_wf_array_group_bounded env s1;
    target_type_of_wf_array_group_bounded env s2
  | WfARewrite _ _ s2 ->
    target_type_of_wf_array_group_bounded env s2
(*    
  | WfADef _ -> ()
*)

and target_type_of_wf_map_group_bounded
  (env: name_env)
  (#x: elab_map_group)
  (wf: ast0_wf_parse_map_group x)
: Lemma
  (requires bounded_wf_parse_map_group env x wf)
  (ensures target_type_bounded env (target_type_of_wf_map_group wf))
  (decreases wf)
  [SMTPat (target_type_bounded env (target_type_of_wf_map_group wf))]
= match wf with
  | WfMNop _ -> ()
  | WfMConcat _ s1 _ s2
  | WfMChoice _ s1 _ s2 ->
    target_type_of_wf_map_group_bounded env s1;
    target_type_of_wf_map_group_bounded env s2
  | WfMZeroOrOne _ s -> target_type_of_wf_map_group_bounded env s
  | WfMLiteral _ _ _ _ s -> target_type_of_wf_typ_bounded env s
  | WfMZeroOrMore _ _ _ s_key s_value _ ->
    target_type_of_wf_typ_bounded env s_key;
    target_type_of_wf_typ_bounded env s_value

let bounded_target_type (env: name_env) =
  (t: target_type { target_type_bounded env t })

[@@ sem_attr ]
noeq
type spec_env (tp_sem: sem_env) (tp_tgt: target_spec_env (tp_sem.se_bound)) = {
  tp_spec_typ: (n: typ_name tp_sem.se_bound) -> GTot (Spec.spec (sem_of_type_sem (tp_sem.se_env n)) (tp_tgt n) true);
//  tp_spec_array_group: (n: group_name tp_sem.se_bound) -> GTot (Spec.ag_spec (fst (Ghost.reveal (tp_sem.se_env n) <: (Spec.array_group None & Spec.map_group))) (tp_tgt n) true); // FIXME: may not be always defined
}

[@@"opaque_to_smt"] irreducible
let empty_spec_env (e: target_spec_env empty_name_env) : spec_env empty_sem_env e = {
  tp_spec_typ = (fun _ -> false_elim ());
//  tp_spec_array_group = (fun _ -> false_elim ());
}

let spec_env_included
  (#tp_sem1: sem_env)
  (#tp_tgt1: target_spec_env (tp_sem1.se_bound))
  (se1: spec_env tp_sem1 tp_tgt1)
  (#tp_sem2: sem_env)
  (#tp_tgt2: target_spec_env (tp_sem2.se_bound))
  (se2: spec_env tp_sem2 tp_tgt2)
: Tot prop
= sem_env_included tp_sem1 tp_sem2 /\
  target_spec_env_included tp_tgt1 tp_tgt2 /\
  (forall (n: typ_name tp_sem1.se_bound) . se1.tp_spec_typ n == se2.tp_spec_typ n)

let seq_is_bounded64 (s: Seq.seq U8.t) : Tot bool = Seq.length s < pow2 64

[@@ sem_attr ]
let spec_of_elem_typ
  (e: elem_typ)
  (sq: squash (wf_elem_typ e))
: GTot (Spec.spec (elem_typ_sem e) (target_elem_type_sem (target_type_of_elem_typ e)) true)
= match e with
  | ELiteral l -> Spec.spec_literal (eval_literal l)
  | EBool -> Spec.spec_bool
  | ESimple -> Spec.spec_simple
  | EByteString -> Spec.spec_bstr
  | ETextString -> Spec.spec_tstr
  | EUInt -> Spec.spec_uint
  | ENInt -> Spec.spec_nint
  | EAlwaysFalse -> Spec.spec_always_false (fun _ -> true)
  | EAny -> Spec.spec_any

let pair_sum
  (#t1 #t2: Type)
  (f1: t1 -> GTot nat)
  (f2: t2 -> GTot nat)
  (x: (t1 & t2))
: GTot nat
= f1 (fst x) + f2 (snd x)

let array_group_zero_or_one_maybe_close_equiv
  (g: Spec.array_group None)
  (close: bool)
: Lemma
  (Spec.array_group_equiv (Spec.maybe_close_array_group (Spec.array_group_zero_or_one g) close) (Spec.maybe_close_array_group (Spec.array_group_zero_or_one (Spec.maybe_close_array_group g close)) close))
= ()

let array_group_choice_maybe_close_equiv
  (g1 g2: Spec.array_group None)
  (close: bool)
: Lemma
  (Spec.array_group_equiv
    (Spec.maybe_close_array_group
      (Spec.array_group_choice g1 g2)
      close
    )
    (Spec.maybe_close_array_group
      (Spec.array_group_choice
        g1 // alas, I cannot close the LHS part of a choice. This is why array group choices should have longer groups (in terms of concat) on their LHS. This is also why array group choices should be written in right-associative form (a // (b // c)), to make disjointness checks more powerful (indeed, if (b // c) is closed, a and b can still be checked for disjointness with b closed, which would not have been possible with ((a // b) // c))
        (Spec.maybe_close_array_group g2 close)
      )
      close
    )
  )
= ()

let array_group_concat_maybe_close_equiv
  (g1 g2: Spec.array_group None)
  (close: bool)
: Lemma
  (Spec.array_group_equiv
    (Spec.maybe_close_array_group
      (Spec.array_group_concat g1 g2)
      close
    )
    (Spec.maybe_close_array_group
      (Spec.array_group_concat
        g1
        (Spec.maybe_close_array_group g2 close)
      )
      close
    )
  )
= ()

[@@bundle_attr]
let name_from_literal (l : literal) : option string =
  match l with
  | LTextString s -> Some s
  | LSimple i
  | LInt i ->
    Some (if i >= 0
          then "intkey" ^ string_of_int i
          else "intkeyneg" ^ string_of_int (-i))

[@@bundle_attr]
let rec extract_name_map_group (t : ast0_wf_parse_map_group 'a) : option string =
  match t with
  | WfMLiteral _ (Some name) _ _ _ -> Some name
  | WfMLiteral _ None l _ _ -> name_from_literal l
  | WfMZeroOrOne _g sub -> extract_name_map_group sub
  | _ -> None

[@@bundle_attr]
let name_from_array_key (key : typ) : option string =
  match key with
  | TNamed n _ -> Some n
  | TElem (ELiteral l) -> name_from_literal l
  | _ -> None

[@@bundle_attr]
let rec extract_name_array_group (t : ast0_wf_array_group 'a) : option string =
  match t with
  | WfAElem _ key _ _ -> name_from_array_key key
  | WfAZeroOrOne _g sub -> extract_name_array_group sub
  | _ -> None

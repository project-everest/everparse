module LowParse.SteelST.List.Base
include LowParse.Spec.List
include LowParse.SteelST.Validate
include LowParse.SteelST.Access

module AP = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt
module U32 = FStar.UInt32
module R = Steel.ST.Reference
module GR = Steel.ST.GhostReference

open Steel.ST.Util

val intro_nil
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (AP.arrayptr a va)
    (fun va' -> aparse (parse_list p) a va')
    (AP.length (AP.array_of va) == 0)
    (fun va' ->
      array_of va' == AP.array_of va /\
      va'.contents == []
    )

val intro_cons
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: _)
  (#va2: _)
  (a1 a2: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse p a1 va1 `star` aparse (parse_list p) a2 va2)
    (fun va -> aparse (parse_list p) a1 va)
    (k.parser_kind_subkind == Some ParserStrong /\
      AP.length (array_of va1) > 0 /\
      AP.adjacent (array_of va1) (array_of va2))
    (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents :: va2.contents
    )

val elim_nil
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (AP.v byte) opened
    (aparse (parse_list p) a va)
    (fun va' -> AP.arrayptr a va')
    (Nil? va.contents)
    (fun va' ->
      array_of va == AP.array_of va' /\
      AP.length (AP.array_of va') == 0
    )

val ghost_elim_cons
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse (parse_list p) a va)
    (fun a2 -> exists_ (fun va1 -> exists_ (fun va2 ->
      aparse p a va1 `star`
      aparse (parse_list p) a2 va2 `star` pure (
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents :: va2.contents /\
      AP.length (array_of va1) > 0
    ))))
    (Cons? va.contents /\ k.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)

inline_for_extraction
val elim_cons
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#va: _)
  (a: byte_array)
: ST byte_array
    (aparse (parse_list p) a va)
    (fun a2 -> exists_ (fun va1 -> exists_ (fun va2 ->
      aparse p a va1 `star`
      aparse (parse_list p) a2 va2 `star` pure (
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents :: va2.contents /\
      AP.length (array_of va1) > 0
    ))))
    (Cons? va.contents /\ k.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)

val ghost_is_cons
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (Ghost.erased bool) opened
    (aparse (parse_list p) a va)
    (fun _ -> aparse (parse_list p) a va)
    True
    (fun res ->
      (Ghost.reveal res == (AP.length (array_of va) > 0)) /\
      (Ghost.reveal res == Cons? va.contents)
    )

val list_append_nil_l
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1 #va2: _)
  (a1 a2: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_list p) a1 va1 `star` aparse (parse_list p) a2 va2)
    (fun va -> aparse (parse_list p) a1 va)
    (AP.adjacent (array_of va1) (array_of va2) /\
      Nil? va1.contents)
    (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va2.contents
    )

val list_append
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (#va1 #va2: _)
  (a1 a2: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_list p) a1 va1 `star` aparse (parse_list p) a2 va2)
    (fun va -> aparse (parse_list p) a1 va)
    (AP.adjacent (array_of va1) (array_of va2) /\
      k.parser_kind_subkind == Some ParserStrong)
    (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents `List.Tot.append` va2.contents
    )

val valid_list_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma
  (requires (
    k.parser_kind_low > 0 /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
      Seq.length b % k.parser_kind_low == 0 <==> Some? (parse (parse_list p) b)
  ))

inline_for_extraction
val validate_list_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.size_t)
: Pure (validator (parse_list p))
    (requires (
      k.parser_kind_low > 0 /\
      k.parser_kind_low == SZ.size_v sz /\
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_metadata == Some ParserKindMetadataTotal
    ))
    (ensures (fun _ -> True))

inline_for_extraction
val with_local
  (#t: Type)
  (init: t)
  (#pre: vprop)
  (#ret_t: Type)
  (#post: ret_t -> vprop)
  (body: (r: R.ref t) ->
    STT ret_t
    (R.pts_to r full_perm init `star` pre)
    (fun v -> exists_ (R.pts_to r full_perm) `star` post v)
  )
: STF ret_t pre post True (fun _ -> True)

inline_for_extraction // this one is fine
val with_ghost_local
  (#t: Type)
  (init: Ghost.erased t)
  (#pre: vprop)
  (#ret_t: Type)
  (#post: ret_t -> vprop)
  (body: (r: GR.ref t) ->
    STT ret_t
    (GR.pts_to r full_perm init `star` pre)
    (fun v -> exists_ (GR.pts_to r full_perm) `star` post v)
  )
: STF ret_t pre post True (fun _ -> True)

inline_for_extraction
val validate_list
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
: Tot (validator (parse_list p))

val intro_singleton
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse p a va)
    (fun va' -> aparse (parse_list p) a va')
    (AP.length (array_of va) > 0)
    (fun va' ->
      array_of' va' == array_of' va /\
      va'.contents == [va.contents]
    )

inline_for_extraction
val read_replace
  (#t: _)
  (#p: _)
  (#v: Ghost.erased t)
  (r: R.ref t)
: ST t
    (R.pts_to r p v)
    (fun res -> R.pts_to r p res)
    True
    (fun res -> Ghost.reveal v == res)

val list_fold_left_snoc
  (#a #b: Type)
  (f: a -> b -> Tot a)
  (init: a)
  (l1: list b)
  (x: b)
: Lemma
  (List.Tot.fold_left f init (l1 `List.Tot.append` [x]) == f (List.Tot.fold_left f init l1) x)

val list_append_cons_r
  (#a: Type)
  (l1: list a)
  (x: a)
  (l2: list a)
: Lemma
  (l1 `List.Tot.append` (x :: l2) == (l1 `List.Tot.append` [x]) `List.Tot.append` l2)

let array_opt = Ghost.erased (option (AP.array byte))

let length_opt (a: array_opt) : GTot nat =
  match Ghost.reveal a with
  | None -> 0
  | Some a' -> AP.length a'

let adjacent_opt (a1: AP.array byte) (a2: array_opt) : Tot prop =
  match Ghost.reveal a2 with
  | None -> True
  | Some a2' -> AP.adjacent a1 a2'

let merge_opt (a1: AP.array byte) (a2: array_opt) : Pure (AP.array byte)
  (requires (adjacent_opt a1 a2))
  (ensures (fun res -> AP.length res == AP.length a1 + length_opt a2))
= match Ghost.reveal a2 with
  | None -> a1
  | Some a2' -> AP.merge a1 a2'

let merge_opt_into (a1: AP.array byte) (a2: array_opt) (a3: AP.array byte) : Tot prop =
  adjacent_opt a1 a2 /\
  merge_opt a1 a2 == a3

let merge_opt_assoc (a1 a2: AP.array byte) (a3: array_opt) : Lemma
  (requires (
    (AP.adjacent a1 a2 /\ adjacent_opt a2 a3) \/
    (AP.adjacent a1 a2 /\ adjacent_opt (AP.merge a1 a2) a3) \/
    (adjacent_opt a2 a3 /\ AP.adjacent a1 (merge_opt a2 a3))
  ))
  (ensures (
    AP.adjacent a1 a2 /\ adjacent_opt (AP.merge a1 a2) a3 /\
    adjacent_opt a2 a3 /\ AP.adjacent a1 (merge_opt a2 a3) /\
    merge_opt (AP.merge a1 a2) a3 == AP.merge a1 (merge_opt a2 a3)
  ))
= ()

[@@erasable]
noeq
type vl (t: Type0) = {
  array: array_opt;
  contents: list t;
  prf: squash (None? array == Nil? contents);
}

let v_of_vl (#t: Type) (w: vl t { Some? w.array }) : Tot (v parse_list_kind (list t)) = {
  array_perm = Some?.v w.array;
  contents = w.contents;
  array_perm_prf = ();
}

let aparse_list (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array) (v: vl t) : Tot vprop =
  if None? v.array
  then emp
  else aparse (parse_list p) a (v_of_vl v)


val intro_aparse_list_nil (#opened: _) (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array)
: STGhost (vl t) opened
    emp
    (fun res -> aparse_list p a res)
    True
    (fun res -> res.contents == [])

val intro_aparse_list_cons (#opened: _) (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array) (w: v parse_list_kind (list t))
: STGhost (vl t) opened
    (aparse (parse_list p) a w)
    (fun res -> aparse_list p a res)
    (Cons? w.contents)
    (fun res ->
      Ghost.reveal res.array == Some (array_of' w) /\
      w == v_of_vl res /\
      res.contents == w.contents
    )

val elim_aparse_list_nil (#opened: _) (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array) (w: vl t)
: STGhost unit opened
    (aparse_list p a w)
    (fun _ -> emp)
    (Nil? w.contents)
    (fun _ -> None? w.array)

val elim_aparse_list_cons (#opened: _) (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array) (w: vl t)
: STGhost (v parse_list_kind (list t)) opened
    (aparse_list p a w)
    (fun res -> aparse (parse_list p) a res)
    (Cons? w.contents)
    (fun res ->
      Ghost.reveal w.array == Some (array_of' res) /\
      res == v_of_vl w /\
      res.contents == w.contents
    )

let intro_aparse_list_post
  (#t: Type)
  (wl: AP.v byte)
  (wr: v parse_list_kind (list t))
  (wl': AP.v byte)
  (wr': vl t)
: Tot prop
=
      AP.adjacent (AP.array_of wl) (array_of' wr) /\
      merge_opt_into (AP.array_of wl') wr'.array (AP.merge (AP.array_of wl) (array_of' wr)) /\
      AP.contents_of' wl' == AP.contents_of' wl /\
      AP.length (AP.array_of wl') == AP.length (AP.array_of wl) /\
      wr'.contents == wr.contents /\
      length_opt wr'.array == AP.length (array_of' wr)

val intro_aparse_list
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#wl: AP.v byte)
  (#wr: v parse_list_kind (list t))
  (al ar: byte_array)
: STGhost unit opened
    (AP.arrayptr al wl `star` aparse (parse_list p) ar wr)
    (fun _ -> exists_ (fun (wl': AP.v byte) -> exists_ (fun (wr': vl t) ->
      AP.arrayptr al wl' `star`
      aparse_list p ar wr' `star` pure (
      intro_aparse_list_post wl wr wl' wr'
    ))))
    (AP.adjacent (AP.array_of wl) (array_of' wr))
    (fun _ -> True)

let list_split_nil_post
  (#t: Type)
  (va: v parse_list_kind (list t))
  (va1: v parse_list_kind (list t))
  (va2: vl t)
: Tot prop
=
      merge_opt_into (array_of va1) va2.array (array_of va) /\
      length_opt va2.array == AP.length (array_of va) /\
      va1.contents == [] /\
      va2.contents == va.contents

val list_split_nil_l
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: v parse_list_kind (list t))
  (a: byte_array)
: STGhostT unit opened
    (aparse (parse_list p) a va)
    (fun _ -> exists_ (fun (va1: v parse_list_kind (list t)) -> exists_ (fun (va2: vl t) ->
      aparse (parse_list p) a va1 `star`
      aparse_list p a va2 `star` pure (
      list_split_nil_post va va1 va2
    ))))

val ghost_is_cons_opt
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (Ghost.erased bool) opened
    (aparse_list p a va)
    (fun _ -> aparse_list p a va)
    True
    (fun res ->
      (Ghost.reveal res == (length_opt va.array > 0)) /\
      (Ghost.reveal res == Cons? va.contents)
    )

val elim_aparse_list
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#wl: v parse_list_kind (list t))
  (#wr: _)
  (al ar: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_list p) al wl `star` aparse_list p ar wr)
    (fun w -> aparse (parse_list p) al w)
    (adjacent_opt (array_of' wl) wr.array /\
      k.parser_kind_subkind == Some ParserStrong)
    (fun w ->
      merge_opt_into (array_of' wl) wr.array (array_of' w) /\
      w.contents == wl.contents `List.Tot.append` wr.contents
    )

inline_for_extraction
val elim_cons_opt_with_length
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: v k t)
  (#va2: v _ _)
  (a: byte_array)
  (len1: SZ.size_t)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (aparse p a va1 `star` aparse (parse_list p) a2 va2)
    (fun a2' -> exists_ (fun (va1': v k t) -> exists_ (fun va2' ->
      aparse p a va1' `star`
      aparse_list p a2' va2' `star` pure (
      AP.adjacent (array_of' va1) (array_of' va2) /\
      merge_opt_into (array_of va1') va2'.array (AP.merge (array_of' va1) (array_of' va2)) /\
      va1'.contents == va1.contents /\
      va2'.contents == va2.contents /\
      AP.length (array_of' va1) == AP.length (array_of' va1') /\
      AP.length (array_of' va2) == length_opt va2'.array
    ))))
    (k.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of' va1) (array_of' va2) /\
      SZ.size_v len1 == AP.length (array_of va1)
    )
    (fun _ -> True)

let merge_opt_into_r
  (a1: AP.array byte)
  (a2: option (AP.array byte))
  (a3: AP.array byte)
  (a2': AP.array byte)
  (a21: AP.array byte)
  (a22: option (AP.array byte))
: Lemma
  (requires (
    merge_opt_into a1 a2 a3 /\
    a2 == Some a2' /\
    merge_opt_into a21 a22 a2'
  ))
  (ensures (
    AP.adjacent a1 a21 /\
    merge_opt_into (AP.merge a1 a21) a22 a3 
  ))
= ()

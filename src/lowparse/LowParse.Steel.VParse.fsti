module LowParse.Steel.VParse
include LowParse.Spec.Base

module S = Steel.Memory
module SP = Steel.FractionalPermission
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.C.Array
module AP = LowParse.Steel.ArrayPtr

(* For now, we only support parsers with ParserStrong or ParserConsumesAll subkind. *)

let byte_array (base: Type0) : Type0 = AP.t base byte

let valid
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Tot prop
=
  begin match parse p b with
  | None -> False
  | Some (_, consumed) ->
    consumed == Seq.length b
  end

let is_byte_repr
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: t)
  (b: bytes)
: Tot prop
= match parse p b with
  | None -> False
  | Some (v', consumed) ->
    x == v' /\
    consumed == Seq.length b

val is_byte_repr_injective
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: t)
  (b1 b2: bytes)
: Lemma
  (requires (is_byte_repr p x b1 /\ is_byte_repr p x b2))
  (ensures (b1 == b2))

let array_prop (#base: Type) (k: parser_kind) (a: A.array base byte) : Tot prop =
  let l = A.length a in
  k.parser_kind_low <= l /\
  (Some? k.parser_kind_high ==> l <= Some?.v k.parser_kind_high)

let array_t (base: Type) (k: parser_kind) : Tot Type =
  (array: A.array base byte { array_prop k array })

[@@erasable]
noeq
type v (base: Type) (k: parser_kind) (t: Type) = {
  array_perm : (A.array base byte); // & SP.perm);
  contents : t;
  array_perm_prf: squash (array_prop k ((* fst *) array_perm));
}

let array_of (#base: Type) (#k: parser_kind) (#t: Type) (w: v base k t) : GTot (array_t base k) =
//  fst
  w.array_perm

// let perm_of (#base: Type) (#k: parser_kind) (#t: Type) (w: v base k t) : Tot SP.perm =
//  snd w.array_perm

let adjacent
  (#base: Type)
  (#t1 #t2: Type)
  (#k1 #k2: parser_kind)
  (v1: v base k1 t1)
  (v2: v base k2 t2)
: Tot prop
= A.adjacent (array_of v1) (array_of v2) /\
  True //  perm_of v1 == perm_of v2

let merge_into
  (#base: Type)
  (#k1 #k2 #k: parser_kind)
  (#t1 #t2 #t: Type)
  (v1: v base k1 t1)
  (v2: v base k2 t2)
  (v: v base k t)
: Tot prop
= A.merge_into (array_of v1) (array_of v2) (array_of v) /\
True //  perm_of v1 == perm_of v /\
//  perm_of v2 == perm_of v

val vparse_slprop
  (#base: Type)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (a: byte_array base)
: Tot (S.slprop u#1)

val vparse_sel
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: GTot (SE.selector (v base k t) (vparse_slprop p a))

[@SE.__steel_reduce__]
let vparse'
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: Tot SE.vprop'
= {
  SE.hp = vparse_slprop p a;
  SE.t = v base k t;
  SE.sel = vparse_sel p a;
}

[@SE.__steel_reduce__]
let vparse
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: Tot SE.vprop
= SE.VUnit (vparse' p a)

val intro_vparse
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: SEA.SteelGhost unit opened
    (AP.varrayptr a)
    (fun _ -> vparse p a)
    (fun h ->
      valid p (h (AP.varrayptr a)).AP.contents
    )
    (fun h _ h' ->
      let s' = h' (vparse p a) in
      let s = h (AP.varrayptr a) in
      valid p s.AP.contents /\
      array_of s' == s.AP.array /\
//      perm_of s' == s.AP.perm /\
      is_byte_repr p s'.contents s.AP.contents
    )

val elim_vparse
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: SEA.SteelGhost unit opened
    (vparse p a)
    (fun _ -> AP.varrayptr a)
    (fun _ -> True)
    (fun h _ h' ->
      let s' = h' (AP.varrayptr a) in
      let s = h (vparse p a) in
      valid p s'.AP.contents /\
//      s'.AP.perm == perm_of s /\
      s'.AP.array == array_of s /\
      is_byte_repr p s.contents s'.AP.contents
    )

(*
val share
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
: SEA.SteelAtomic (byte_array base) opened
    (vparse p a)
    (fun res -> vparse p a `SE.star` vparse p res)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (vparse p a) in
      let s' = h' (vparse p a) in
      let d = h' (vparse p res) in
      array_of s' == array_of s /\
//      perm_of s' == SP.half_perm (perm_of s) /\
      s'.contents == s.contents /\
      array_of d == array_of s /\
//      perm_of d == SP.half_perm (perm_of s) /\
      d.contents == s.contents
    )

val gather
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a1 a2: byte_array base)
: SEA.SteelGhost unit opened
    (vparse p a1 `SE.star` vparse p a2)
    (fun res -> vparse p a1)
    (fun h ->
      (h (vparse p a1)).array_perm == (h (vparse p a2)).array_perm
    )
    (fun h res h' ->
      let s1 = h (vparse p a1) in
      let s2 = h (vparse p a2) in
      let d = h' (vparse p a1) in
      array_of d == array_of s1 /\
      array_of d == array_of s2 /\
//      perm_of d == perm_of s1 `SP.sum_perm` perm_of s2 /\
      d.contents == s1.contents /\
      d.contents == s2.contents
    )
*)

module LowParse.SteelSel.VParse
include LowParse.Spec.Base

module S = Steel.Memory
module SE = Steel.SelEffect
module A = Steel.SelArray

(* For now, we only support parsers with ParserStrong or ParserConsumesAll subkind. *)

let byte_array : Type0 = A.array byte

let supported_kind
  (k: parser_kind)
: Tot bool
= match k.parser_kind_subkind with
  | Some ParserStrong
  | Some ParserConsumesAll
    -> true
  | _ -> false

let valid
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Tot prop
= supported_kind k /\
  begin match parse p b with
  | None -> False
  | Some (_, consumed) ->
    consumed == n
  end

let is_byte_repr
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: t)
  (b: Seq.lseq byte n)
: Tot prop
= match parse p b with
  | None -> False
  | Some (v', consumed) ->
    x == v' /\
    consumed == n

val has_byte_repr
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (x: t)
: Tot prop

let select_t
  (n: Ghost.erased nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type0
= (y: t { has_byte_repr n p y })

val vparse_slprop
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (a: byte_array)
: Tot (S.slprop u#1)

val vparse_sel
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: Tot (SE.selector (select_t (A.length a) p) (vparse_slprop p a))

[@SE.__steel_reduce__]
let vparse'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: Tot SE.vprop'
= {
  SE.hp = vparse_slprop p a;
  SE.t = select_t (A.length a) p;
  SE.sel = vparse_sel p a;
}

[@SE.__steel_reduce__]
let vparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: Tot SE.vprop
= SE.VUnit (vparse' p a)

val intro_vparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: SE.SteelSel unit
    (A.varray a)
    (fun _ -> vparse p a)
    (fun h ->
      valid (A.length a) p (h (A.varray a))
    )
    (fun h _ h' ->
      valid (A.length a) p (h (A.varray a)) /\
      is_byte_repr (A.length a) p (h' (vparse p a)) (h (A.varray a))
    )

val elim_vparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: SE.SteelSel unit
    (vparse p a)
    (fun _ -> A.varray a)
    (fun _ -> True)
    (fun h _ h' ->
      valid (A.length a) p (h' (A.varray a)) /\
      is_byte_repr (A.length a) p (h (vparse p a)) (h' (A.varray a))
    )

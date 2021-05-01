module LowParse.SteelSel.VParse
include LowParse.Spec.Base

module S = Steel.Memory
module SE = Steel.SelEffect
module A = Steel.SelArray
module AP = Steel.SelArrayPtr

(* For now, we only support parsers with ParserStrong or ParserConsumesAll subkind. *)

let byte_array : Type0 = AP.t byte

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

noeq
type v (t: Type) = {
  array : A.array byte;
  contents : t;
}

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
: Tot (SE.selector (v t) (vparse_slprop p a))

[@SE.__steel_reduce__]
let vparse'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: Tot SE.vprop'
= {
  SE.hp = vparse_slprop p a;
  SE.t = v t;
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
    (AP.varrayptr a)
    (fun _ -> vparse p a)
    (fun h ->
      valid p (h (AP.varrayptr a)).AP.contents
    )
    (fun h _ h' ->
      valid p (h (AP.varrayptr a)).AP.contents /\
      (h' (vparse p a)).array == (h (AP.varrayptr a)).AP.array /\
      is_byte_repr p (h' (vparse p a)).contents (h (AP.varrayptr a)).AP.contents
    )

val elim_vparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: SE.SteelSel unit
    (vparse p a)
    (fun _ -> AP.varrayptr a)
    (fun _ -> True)
    (fun h _ h' ->
      valid p (h' (AP.varrayptr a)).AP.contents /\
      (h' (AP.varrayptr a)).AP.array == (h (vparse p a)).array /\
      is_byte_repr p (h (vparse p a)).contents (h' (AP.varrayptr a)).AP.contents
    )

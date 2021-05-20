module LowParse.Steel.VParse
include LowParse.Spec.Base

module S = Steel.Memory
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.Array
module AP = Steel.ArrayPtr

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

let array_prop (k: parser_kind) (a: A.array byte) : Tot prop =
  let l = A.length a in
  k.parser_kind_low <= l /\
  (Some? k.parser_kind_high ==> l <= Some?.v k.parser_kind_high)

let array_t (k: parser_kind) : Tot Type =
  (array: A.array byte { array_prop k array })

noeq
type v (k: parser_kind) (t: Type) = {
  array : array_t k;
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
: Tot (SE.selector (v k t) (vparse_slprop p a))

[@SE.__steel_reduce__]
let vparse'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: Tot SE.vprop'
= {
  SE.hp = vparse_slprop p a;
  SE.t = v k t;
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
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: SEA.SteelGhost unit opened
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
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
: SEA.SteelGhost unit opened
    (vparse p a)
    (fun _ -> AP.varrayptr a)
    (fun _ -> True)
    (fun h _ h' ->
      valid p (h' (AP.varrayptr a)).AP.contents /\
      (h' (AP.varrayptr a)).AP.array == (h (vparse p a)).array /\
      is_byte_repr p (h (vparse p a)).contents (h' (AP.varrayptr a)).AP.contents
    )

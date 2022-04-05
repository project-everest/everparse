module LowParse.SteelST.Parse
module AP = LowParse.SteelST.ArrayPtr

open Steel.ST.Util
include LowParse.Spec.Base

(* For now, we only support parsers with ParserStrong or ParserConsumesAll subkind. *)

let byte_array (base: Type0) : Type0 = AP.t base byte

let array_prop (#base: Type) (k: parser_kind) (a: AP.array base byte) : Tot prop =
  let l = AP.length a in
  k.parser_kind_low <= l /\
  (Some? k.parser_kind_high ==> l <= Some?.v k.parser_kind_high)

[@@erasable]
noeq
type v (base: Type) (k: parser_kind) (t: Type) = {
  array_perm : (AP.array base byte); // & SP.perm);
  contents : t;
  array_perm_prf: squash (array_prop k ((* fst *) array_perm));
}

let array_t (base: Type) (k: parser_kind) : Tot Type =
  (array: AP.array base byte { array_prop k array })

let array_of (#base: Type) (#k: parser_kind) (#t: Type) (w: v base k t) : GTot (array_t base k) =
  w.array_perm

let arrayptr_parse
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va: AP.v base byte)
: GTot (option (v base k t))
=
  let s = AP.contents_of' va in
  match parse p s with
  | None -> None
  | Some (vt, consumed) ->
    if consumed = Seq.length s
    then
      Some ({
        array_perm = AP.array_of va;
        contents = vt;
        array_perm_prf =
          begin
            parser_kind_prop_equiv k p
          end;
      })
    else
      None

let arrayptr_parse_injective
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va1 va2: AP.v base byte)
: Lemma
  (requires (
    let pa1 = arrayptr_parse p va1 in
    let pa2 = arrayptr_parse p va2 in
    pa1 == pa2 /\ (Some? pa1 \/ Some? pa2)
  ))
  (ensures (
    va1 == va2
  ))
= match arrayptr_parse p va1, arrayptr_parse p va2 with
  | Some _, Some _ ->
    parse_injective p (AP.contents_of va1) (AP.contents_of va2)
  | _ -> ()

[@@ __reduce__]
let aparse0
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
  (vp: v base k t)
: Tot vprop
= exists_ (fun va ->
    AP.arrayptr a va `star` pure (arrayptr_parse p va == Some vp)
  )

let aparse
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array base)
  ([@@@ smt_fallback] vp: v base k t)
: Tot vprop
= aparse0 p a vp

let intro_aparse
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (#va: AP.v base byte)
  (p: parser k t)
  (a: byte_array base)
: STGhost (v base k t) opened
    (AP.arrayptr a va)
    (fun vp -> aparse p a vp)
    (Some? (arrayptr_parse p va))
    (fun vp -> arrayptr_parse p va == Some vp)
= let vp = Some?.v (arrayptr_parse p va) in
  noop ();
  rewrite (aparse0 p a vp) (aparse p a vp); 
  vp

let elim_aparse
  (#opened: _)
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (#vp: v base k t)
  (p: parser k t)
  (a: byte_array base)
: STGhost (AP.v base byte) opened
    (aparse p a vp)
    (fun va -> AP.arrayptr a va)
    True
    (fun va -> arrayptr_parse p va == Some vp)
= let gva = elim_exists () in
  elim_pure _;
  let va = Ghost.reveal gva in
  noop ();
  va

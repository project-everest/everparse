module LowParse.SteelST.Parse
module AP = LowParse.SteelST.ArrayPtr

open Steel.ST.GenElim
include LowParse.Spec.Base

(* For now, we only support parsers with ParserStrong or ParserConsumesAll subkind. *)

inline_for_extraction
let byte_array : Type0 = AP.t byte

let array_prop (k: parser_kind) (a: AP.array byte) : Tot prop =
  let l = AP.length a in
  k.parser_kind_low <= l /\
  (Some? k.parser_kind_high ==> l <= Some?.v k.parser_kind_high)

[@@erasable]
noeq
type v (k: parser_kind) (t: Type) = {
  array_perm : (AP.array byte); // & SP.perm);
  contents : t;
  array_perm_prf: squash (array_prop k ((* fst *) array_perm));
}

let array_t (k: parser_kind) : Tot Type =
  (array: AP.array byte { array_prop k array })

let array_of (#k: parser_kind) (#t: Type) (w: v k t) : GTot (array_t k) =
  w.array_perm

let array_of' (#k: parser_kind) (#t: Type) (w: v k t) : GTot (AP.array byte) =
  array_of w

let arrayptr_parse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va: AP.v byte)
: GTot (option (v k t))
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
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va1 va2: AP.v byte)
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
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
  (vp: v k t)
: Tot vprop
= exists_ (fun va ->
    AP.arrayptr a va `star` pure (arrayptr_parse p va == Some vp)
  )

let aparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a: byte_array)
  ([@@@ smt_fallback] vp: v k t)
: Tot vprop
= aparse0 p a vp

let intro_aparse
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#va: AP.v byte)
  (p: parser k t)
  (a: byte_array)
: STGhost (v k t) opened
    (AP.arrayptr a va)
    (fun vp -> aparse p a vp)
    (Some? (arrayptr_parse p va))
    (fun vp ->
      AP.array_of va == array_of vp /\
      arrayptr_parse p va == Some vp
    )
= let vp = Some?.v (arrayptr_parse p va) in
  noop ();
  rewrite (aparse0 p a vp) (aparse p a vp); 
  vp

#set-options "--ide_id_info_off"

let elim_aparse
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#vp: v k t)
  (p: parser k t)
  (a: byte_array)
: STGhost (AP.v byte) opened
    (aparse p a vp)
    (fun va -> AP.arrayptr a va)
    True
    (fun va ->
      AP.array_of va == array_of vp /\
      arrayptr_parse p va == Some vp
    )
= rewrite (aparse p a vp) (aparse0 p a vp);
  let _ = gen_elim () in
  let va = vpattern (fun va -> AP.arrayptr a va) in
  noop (); // FIXME: WHY WHY WHY?
  va

let rewrite_aparse
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#y1: v k1 t1)
  (a: byte_array)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: STGhost (v k2 t2) opened
    (aparse p1 a y1)
    (fun y2 -> aparse p2 a y2)
    (t1 == t2 /\ (forall bytes . parse p1 bytes == parse p2 bytes))
    (fun y2 ->
      t1 == t2 /\
      array_of' y1 == array_of' y2 /\
      y1.contents == y2.contents
    )
= let _ = elim_aparse p1 a in
  intro_aparse p2 a

let share_aparse
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#va: v k t)
  (p: parser k t)
  (a: byte_array)
  (p1 p2: perm)
: STGhost (Ghost.erased (v k t & v k t)) opened
    (aparse p a va)
    (fun res -> aparse p a (fstp res) `star` aparse p a (sndp res))
    (AP.array_perm (array_of va) == p1 `Steel.FractionalPermission.sum_perm` p2)
    (fun res ->
      (fst res).contents == va.contents /\
      (snd res).contents == va.contents /\
      array_of (fst res) == AP.set_array_perm (array_of va) p1 /\
      array_of (snd res) == AP.set_array_perm (array_of va) p2
    )
= let _ = elim_aparse p a in
  let ares = AP.share a p1 p2 in
  let va1 = intro_aparse #_ #_ #_ #(fst ares) p a in
  let va2 = intro_aparse p a in
  let res = Ghost.hide (va1, va2) in
  rewrite (aparse p a va1) (aparse p a (fstp res));
  rewrite (aparse p a va2) (aparse p a (sndp res));
  res

let gather_aparse
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#x1 #x2: v k t)
  (a: byte_array)
: STGhost (v k t) opened
    (aparse p a x1 `star` aparse p a x2)
    (fun res -> aparse p a res)
    (array_of x1 == AP.set_array_perm (array_of x2) (AP.array_perm (array_of x1)))
    (fun res ->
      res.contents == x1.contents /\
      res.contents == x2.contents /\
      array_of res == AP.set_array_perm (array_of x1) (AP.array_perm (array_of x1) `Steel.FractionalPermission.sum_perm` AP.array_perm (array_of x2))
    )
= let y1 = elim_aparse #_ #_ #_ #x1 p a in
  let y2 = elim_aparse p a in
  let y = AP.gather #_ #_ #y1 #y2 a in
  intro_aparse p a
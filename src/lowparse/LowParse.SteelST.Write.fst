module LowParse.SteelST.Write
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

open Steel.ST.GenElim

include LowParse.SteelST.Parse

inline_for_extraction
let writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
=
  (#va: _) ->
  (x: t) ->
  (a: byte_array) ->
  ST SZ.t
    (AP.arrayptr a va)
    (fun sz -> exists_ (fun vl -> aparse p a vl `star` exists_ (fun ar -> exists_ (fun vr -> AP.arrayptr ar vr `star` pure (
      AP.merge_into (array_of' vl) (AP.array_of vr) (AP.array_of va) /\
      vl.contents == x /\
      SZ.v sz == AP.length (array_of' vl)
    )))))
    (Seq.length (serialize s x) <= AP.length (AP.array_of va) /\
      AP.array_perm (AP.array_of va) == full_perm)
    (fun _ -> True)

inline_for_extraction
let exact_writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
=
  (#va: _) ->
  (x: t) ->
  (a: byte_array) ->
  ST (v k t)
    (AP.arrayptr a va)
    (fun va' -> aparse p a va')
    (Seq.length (serialize s x) == AP.length (AP.array_of va) /\
      AP.array_perm (AP.array_of va) == full_perm)
    (fun va' ->
      array_of' va' == AP.array_of va /\
      va'.contents == x
    )

inline_for_extraction
let exact_write
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: writer s)
: Tot (exact_writer s)
= fun x a ->
  let _ = w x a in
  let _ = gen_elim () in
  let va0 = elim_aparse _ a in
  parse_injective p (AP.contents_of va0) (serialize s x);
  let va1 = AP.join a _ in
  assert (AP.contents_of va1 `Seq.equal` AP.contents_of va0);
  let va' = intro_aparse p a in
  return va'

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
let write_constant_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: exact_writer s)
  (sz: SZ.t)
: Pure (writer s)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.v sz
    ))
    (ensures (fun _ -> True))
= fun x a ->
  let _ = AP.gsplit a sz in
  let _ = gen_elim () in
  let _ = w x a in
  return sz

#pop-options

module LowParse.SteelST.Swap
include LowParse.SteelST.Parse

module AP = LowParse.SteelST.ArrayPtr
module APSwap = LowParse.SteelST.ArrayPtrSwap
module SZ = FStar.SizeT

open Steel.ST.GenElim

inline_for_extraction
let swap_parsed_with_sizes
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#v1: v k1 t1)
  (al: byte_array)
  (sz1: SZ.t)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#v2: v k2 t2)
  (ar: Ghost.erased byte_array)
  (sz2: SZ.t)
: ST byte_array
    (aparse p1 al v1 `star` aparse p2 ar v2)
    (fun ar' -> exists_ (fun v1' -> exists_ (fun v2' ->
      aparse p2 al v2' `star`
      aparse p1 ar' v1' `star`
      pure (
        AP.adjacent (array_of v2') (array_of v1') /\
        AP.merge_into (array_of v1) (array_of v2) (AP.merge (array_of v2') (array_of v1')) /\
        AP.length (array_of v1') == AP.length (array_of v1) /\
        v1'.contents == v1.contents /\
        AP.length (array_of v2') == AP.length (array_of v2) /\
        v2'.contents == v2.contents
    ))))
    (AP.adjacent (array_of v1) (array_of v2) /\
      SZ.v sz1 == AP.length (array_of v1) /\
      SZ.v sz2 == AP.length (array_of v2) /\
      AP.array_perm (array_of v1) == full_perm
    )
    (fun _ -> True)
= let vb1 = elim_aparse _ al in
  let vb2 = elim_aparse _ ar in
  let _ = AP.join al ar in
  let _ = APSwap.arrayptr_swap al (sz1 `SZ.add` sz2) sz1 in
  let ar' = AP.split al sz2 in
  let _ = gen_elim () in
  let vb2' : AP.v byte = vpattern_replace (AP.arrayptr al) in
  let vb1' : AP.v byte = vpattern_replace (AP.arrayptr ar') in
  Seq.append_slices (AP.contents_of vb1) (AP.contents_of vb2);
  assert (AP.contents_of vb1' `Seq.equal` AP.contents_of vb1);
  assert (AP.contents_of vb2' `Seq.equal` AP.contents_of vb2);
  noop ();
  let _ = intro_aparse p2 al in
  let _ = intro_aparse p1 ar' in
  return ar'

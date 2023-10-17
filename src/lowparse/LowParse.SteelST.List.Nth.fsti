module LowParse.SteelST.List.Nth

include LowParse.SteelST.List.Base

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

open Steel.ST.GenElim

/// Placeholder for a pattern to record the tail of a list_nth to restore the list
let list_nth_tail
  (b0: byte_array)
  (i: SZ.t)
  (e: byte_array)
  (b: byte_array)
: GTot byte_array
= b

let list_nth_post
  (k: parser_kind)
  (#t: Type)
  (va0: v parse_list_kind (list t))
  (i: SZ.t)
  (vl: v parse_list_kind (list t))
  (ve: v k t)
  (vr: v parse_list_kind (list t))
: Tot prop
=
  k.parser_kind_subkind == Some ParserStrong /\
  AP.length (array_of' ve) > 0 /\
  va0.contents == vl.contents `List.Tot.append` (ve.contents :: vr.contents) /\
  List.Tot.length vl.contents == SZ.v i /\
  SZ.v i < List.Tot.length va0.contents /\
  List.Tot.index va0.contents (SZ.v i) == ve.contents /\
  AP.adjacent (array_of' ve) (array_of' vr) /\
  AP.merge_into (array_of' vl) (AP.merge (array_of' ve) (array_of' vr)) (array_of' va0)

inline_for_extraction
val list_nth
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#va0: v _ _)
  (a0: byte_array)
  (i: SZ.t)
: ST byte_array
    (aparse (parse_list p) a0 va0)
    (fun e -> exists_ (fun a -> exists_ (fun (vl: v _ _) -> exists_ (fun (ve: v _ _) -> exists_ (fun (vr: v _ _) ->
      aparse (parse_list p) a0 vl `star`
      aparse p e ve `star`
      aparse (parse_list p) (list_nth_tail a0 i e a) vr `star`
      pure (
        list_nth_post k va0 i vl ve vr
    ))))))
    (
      k.parser_kind_subkind == Some ParserStrong /\
      SZ.v i < List.Tot.length va0.contents
    )
    (fun _ -> True)

val list_nth_restore
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (#vl: v parse_list_kind (list t))
  (#ve: v k t)
  (#vr: v parse_list_kind (list t))
  (#p: parser k t)
  (a0: byte_array)
  (va0: v _ _)
  (i: SZ.t)
  (e: byte_array)
  (a: byte_array)
: STGhost unit opened
    (
      aparse (parse_list p) a0 vl `star`
      aparse p e ve `star`
      aparse (parse_list p) (list_nth_tail a0 i e a) vr
    )
    (fun _ -> aparse (parse_list p) a0 va0)
    (list_nth_post k va0 i vl ve vr)
    (fun _ -> True)

inline_for_extraction
let list_nth_with_implies
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#va0: v _ _)
  (a0: byte_array)
  (i: SZ.t {
    k.parser_kind_subkind == Some ParserStrong /\
    SZ.v i < List.Tot.length va0.contents
  })
: STT byte_array
    (aparse (parse_list p) a0 va0)
    (fun e -> exists_ (fun (ve: v _ _) ->
      aparse p e ve `star`
      (aparse p e ve `implies_` aparse (parse_list p) a0 va0) `star`
      pure (ve.contents == List.Tot.index va0.contents (SZ.v i))
    ))
= let res = list_nth j a0 i in
  let _ = gen_elim () in
  intro_implies
    (aparse p res _)
    (aparse (parse_list p) a0 va0)
    (aparse (parse_list p) a0 _ `star` aparse (parse_list p) _ _)
    (fun _ ->
      list_nth_restore a0 va0 i res _
    );
  return res

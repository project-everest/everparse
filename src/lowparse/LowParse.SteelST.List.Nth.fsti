module LowParse.SteelST.List.Nth

include LowParse.SteelST.List.Base

module AP = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt

open Steel.ST.Util

/// Placeholder for a pattern to record the tail of a list_nth to restore the list
let list_nth_tail
  (b0: byte_array)
  (i: SZ.size_t)
  (e: byte_array)
  (b: byte_array)
: GTot byte_array
= b

let list_nth_post
  (k: parser_kind)
  (#t: Type)
  (va0: v parse_list_kind (list t))
  (i: SZ.size_t)
  (vl: v parse_list_kind (list t))
  (ve: v k t)
  (vr: v parse_list_kind (list t))
: Tot prop
=
  k.parser_kind_subkind == Some ParserStrong /\
  AP.length (array_of' ve) > 0 /\
  va0.contents == vl.contents `List.Tot.append` (ve.contents :: vr.contents) /\
  List.Tot.length vl.contents == SZ.size_v i /\
  AP.adjacent (array_of' ve) (array_of' vr) /\
  AP.merge_into (array_of' vl) (AP.merge (array_of' ve) (array_of' vr)) (array_of' va0)

inline_for_extraction
val list_nth
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#va0: v _ _)
  (a0: byte_array)
  (i: SZ.size_t)
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
      SZ.size_v i < List.Tot.length va0.contents
    )
    (fun _ -> True)

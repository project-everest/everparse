module LowParse.SteelST.List.Length
include LowParse.SteelST.List.Base

module AP = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt

open Steel.ST.Util

inline_for_extraction
val list_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#va0: v _ _)
  (a0: byte_array)
  (len: SZ.size_t)
: ST SZ.size_t
    (aparse (parse_list p) a0 va0)
    (fun _ -> aparse (parse_list p) a0 va0)
    (SZ.size_v len == AP.length (array_of' va0) /\
      k.parser_kind_subkind == Some ParserStrong)
    (fun res -> SZ.size_v res == List.Tot.length va0.contents)

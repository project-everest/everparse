module LowParse.SteelST.List.Length
include LowParse.SteelST.List.Base

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

open Steel.ST.Util

inline_for_extraction
val list_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#va0: v _ _)
  (a0: byte_array)
  (len: SZ.t)
: ST SZ.t
    (aparse (parse_list p) a0 va0)
    (fun _ -> aparse (parse_list p) a0 va0)
    (SZ.v len == AP.length (array_of' va0) /\
      k.parser_kind_subkind == Some ParserStrong)
    (fun res -> SZ.v res == List.Tot.length va0.contents)

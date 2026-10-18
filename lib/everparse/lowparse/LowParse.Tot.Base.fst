module LowParse.Tot.Base
include LowParse.Spec.Base

inline_for_extraction
let bare_parser = tot_bare_parser

inline_for_extraction
let parser = tot_parser

inline_for_extraction
let serializer
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= serializer #k p

inline_for_extraction
let weaken = tot_weaken

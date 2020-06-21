module LowParseWriters.Parsers
friend LowParseWriters.LowParse

let get_parser_kind
  p
= (dsnd p).kind

let get_parser
  p
= (dsnd p).parser

let make_parser'
  #t #k p s j
= {
  kind = k;
  parser = p;
  serializer = s;
  jumper = j;
}

let make_parser_correct
  #t #k p s j
= ()

let size_correct
  p s x
= LP.serializer_unique (get_parser p) (dsnd p).serializer s x

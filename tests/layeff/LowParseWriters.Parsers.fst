module LowParseWriters.Parsers
friend LowParseWriters.LowParse

module B = LowStar.Buffer

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

let valid_synth_parser_eq
  p1 p2
= {
  valid_synth_valid = (fun h b pos pos' -> ());
  valid_synth_size = (fun x ->
    LP.serializer_unique (get_parser p1) (dsnd p1).serializer (dsnd p2).serializer x
  );
}

let parse_synth
  p1 #t2 f2 f1
= make_parser
    ((dsnd p1).parser `LP.parse_synth` f2)
    (LP.serialize_synth (dsnd p1).parser f2 (dsnd p1).serializer f1 ())
    (LP.jump_synth (dsnd p1).jumper f2 ())

let valid_synth_parse_synth
  p1 #t2 f2 f1 sq
= {
  valid_synth_valid = (fun h b pos pos' ->
    LP.valid_synth h (get_parser p1) f2 (LP.make_slice b (B.len b)) pos
  );
  valid_synth_size = (fun x ->
    LP.synth_injective_synth_inverse_synth_inverse_recip f2 f1 ();
    LP.serialize_synth_eq (get_parser p1) f2 (dsnd p1).serializer f1 () (f2 x)
  );
}

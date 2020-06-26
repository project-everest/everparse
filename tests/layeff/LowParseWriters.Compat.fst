module LowParseWriters.Compat

friend LowParseWriters.LowParse
friend LowParseWriters.Parsers

module B = LowStar.Buffer

let star_correct
  p1 p2
= ()

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

let valid_synth_parse_synth_recip
  p1 #t2 f2 f1 sq
= {
  valid_synth_valid = (fun h b pos pos' ->
    LP.synth_injective_synth_inverse_synth_inverse_recip f2 f1 ();
    LP.valid_synth h (get_parser p1) f2 (LP.make_slice b (B.len b)) pos
  );
  valid_synth_size = (fun x ->
    LP.serialize_synth_eq (get_parser p1) f2 (dsnd p1).serializer f1 () (x)
  );
}

let parse_vldata_correct
  p min max
= ()

let list_size_correct
  p x
= ()

let parse_vllist_correct
  p min max
= ()

let parse_vlbytes_correct
  min max
= ()

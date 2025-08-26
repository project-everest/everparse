module LowParse.Spec.SeqBytes.Base
include LowParse.Spec.FLData

let parse_seq_flbytes_gen
  (sz: nat)
  (s: bytes { Seq.length s == sz } )
: Tot (Seq.lseq byte sz)
= s

let tot_parse_seq_flbytes
  (sz: nat)
: Tot (tot_parser (total_constant_size_parser_kind sz) (Seq.lseq byte sz))
= tot_make_total_constant_size_parser sz (Seq.lseq byte sz) (parse_seq_flbytes_gen sz)

let parse_seq_flbytes
  (sz: nat)
: Tot (parser (total_constant_size_parser_kind sz) (Seq.lseq byte sz))
= tot_parse_seq_flbytes sz

let serialize_seq_flbytes'
  (sz: nat)
  (x: Seq.lseq byte sz)
: Tot bytes
= x

let serialize_seq_flbytes_correct
  (sz: nat)
: Lemma
  (serializer_correct (parse_seq_flbytes sz) (serialize_seq_flbytes' sz))
= let prf
    (input: Seq.lseq byte sz)
  : Lemma
    (
      let ser = serialize_seq_flbytes' sz input in
      Seq.length ser == sz /\
      parse (parse_seq_flbytes sz) ser == Some (input, sz)
    )
  = ()
  in
  Classical.forall_intro prf

let serialize_seq_flbytes
  (sz: nat)
: Tot (serializer (parse_seq_flbytes sz))
= serialize_seq_flbytes_correct sz;
  serialize_seq_flbytes' sz

let tot_serialize_seq_flbytes
  (sz: nat)
: Tot (tot_serializer (tot_parse_seq_flbytes sz))
= serialize_seq_flbytes_correct sz;
  serialize_seq_flbytes' sz

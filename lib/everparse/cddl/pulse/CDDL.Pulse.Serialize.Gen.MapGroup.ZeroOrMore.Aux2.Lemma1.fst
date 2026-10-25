module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma1
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT

#push-options "--z3rlimit 32"

let cbor_serialize_map_insert_pre_intro
  (pe: bare_cbor_parser)
  (p: bare_cbor_map_parser)
  (m: cbor_map)
  (size0 size1 size1' size2 size2': SZ.t)
  (vk vv: cbor)
  (w_ w0 w_key w_value w_suffix: Seq.seq U8.t)
: Lemma
  (requires
    SZ.v size0 <= Seq.length w0 /\
    SZ.v size1' == SZ.v size0 + SZ.v size1 /\
    SZ.v size2' == SZ.v size1' + SZ.v size2 /\
    Seq.length w_key == SZ.v size1 /\
    Seq.length w_value == SZ.v size2 /\
    Seq.length w_ == SZ.v size2' /\
    w_ == Seq.slice
      (Seq.append (Seq.slice w0 0 (SZ.v size0))
        (Seq.append w_key (Seq.append w_value w_suffix)))
      0 (SZ.v size2') /\
    p (cbor_map_length m) (Seq.slice w0 0 (SZ.v size0)) == Some (m, SZ.v size0) /\
    pe w_key == Some (vk, SZ.v size1) /\
    pe w_value == Some (vv, SZ.v size2)
  )
  (ensures cbor_serialize_map_insert_pre p pe m size0 vk size1' vv w_)
=
  let prefix = Seq.slice w0 0 (SZ.v size0) in
  let rest = Seq.append w_key (Seq.append w_value w_suffix) in
  let full = Seq.append prefix rest in
  // Establish key lengths
  assert (Seq.length prefix == SZ.v size0);
  Seq.lemma_len_append prefix rest;
  Seq.lemma_len_append w_key (Seq.append w_value w_suffix);
  Seq.lemma_len_append w_value w_suffix;
  // w_ is a prefix slice of full
  assert (w_ == Seq.slice full 0 (SZ.v size2'));
  assert (SZ.v size2' <= Seq.length full);
  // Show: Seq.slice w_ 0 (SZ.v size0) == prefix
  // Using slice_slice: Seq.slice (Seq.slice s i j) k l == Seq.slice s (i+k) (i+l)
  Seq.slice_slice full 0 (SZ.v size2') 0 (SZ.v size0);
  assert (Seq.slice w_ 0 (SZ.v size0) == Seq.slice full 0 (SZ.v size0));
  // Seq.slice (append prefix rest) 0 |prefix| == prefix
  Seq.lemma_eq_intro (Seq.slice full 0 (SZ.v size0)) prefix;
  assert (Seq.slice w_ 0 (SZ.v size0) == prefix);
  // Show: Seq.slice w_ size0 size1' == w_key
  Seq.slice_slice full 0 (SZ.v size2') (SZ.v size0) (SZ.v size1');
  assert (Seq.slice w_ (SZ.v size0) (SZ.v size1') == Seq.slice full (SZ.v size0) (SZ.v size1'));
  Seq.lemma_eq_intro (Seq.slice full (SZ.v size0) (SZ.v size1')) w_key;
  assert (Seq.slice w_ (SZ.v size0) (SZ.v size1') == w_key);
  // Show: Seq.slice w_ size1' (length w_) == w_value
  Seq.slice_slice full 0 (SZ.v size2') (SZ.v size1') (SZ.v size2');
  assert (Seq.slice w_ (SZ.v size1') (Seq.length w_) == Seq.slice full (SZ.v size1') (SZ.v size2'));
  Seq.lemma_eq_intro (Seq.slice full (SZ.v size1') (SZ.v size2')) w_value;
  assert (Seq.slice w_ (SZ.v size1') (Seq.length w_) == w_value);
  // Now the conclusion follows
  ()

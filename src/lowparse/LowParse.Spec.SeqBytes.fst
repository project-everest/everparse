module LowParse.Spec.SeqBytes
include LowParse.Spec.SeqBytes.Base
include LowParse.Spec.VLData

module Seq = FStar.Seq
module U32 = FStar.UInt32

(* VLBytes *)

(* For the payload: since the input buffer is truncated at the time of
reading the length header, "parsing" the payload will always succeed,
by just returning it unchanged (unless the length of the input
is greater than 2^32) *)

let parse_seq_all_bytes_kind =
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_metadata = None;
    parser_kind_subkind = Some ParserConsumesAll;
  }

let parse_seq_all_bytes'
  (input: bytes)
: GTot (option (bytes * consumed_length input))
= let len = Seq.length input in
    Some (input, len)

#set-options "--z3rlimit 16"

let parse_seq_all_bytes_injective () : Lemma
  (injective parse_seq_all_bytes')
= let prf
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond parse_seq_all_bytes' b1 b2))
    (ensures (injective_postcond parse_seq_all_bytes' b1 b2))
  = ()
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x))

#reset-options

let parse_seq_all_bytes_correct () : Lemma
  (parser_kind_prop parse_seq_all_bytes_kind parse_seq_all_bytes')
= parser_kind_prop_equiv parse_seq_all_bytes_kind parse_seq_all_bytes';
  parse_seq_all_bytes_injective ()

let parse_seq_all_bytes : parser parse_seq_all_bytes_kind bytes =
  parse_seq_all_bytes_correct ();
  parse_seq_all_bytes'

let serialize_seq_all_bytes'
  (input: bytes)
: GTot bytes
= input

#set-options "--z3rlimit 32"

let serialize_seq_all_bytes_correct () : Lemma (serializer_correct parse_seq_all_bytes serialize_seq_all_bytes') =
  let prf
    (input: bytes)
  : Lemma
    (
      let ser = serialize_seq_all_bytes' input in
      let len : consumed_length ser = Seq.length ser in
      parse parse_seq_all_bytes ser == Some (input, len)
    )
  = assert (Seq.length (serialize_seq_all_bytes' input) == Seq.length input)
  in
  Classical.forall_intro prf

#reset-options

let serialize_seq_all_bytes : serializer parse_seq_all_bytes =
  serialize_seq_all_bytes_correct ();
  serialize_seq_all_bytes'

let parse_bounded_seq_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
: Tot (parser (parse_bounded_vldata_strong_kind min max (log256' max) parse_seq_all_bytes_kind) (parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes))
= parse_bounded_vldata_strong min max serialize_seq_all_bytes

let parse_bounded_seq_vlbytes_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: bytes)
: GTot Type0
= let reslen = Seq.length x in
  min <= reslen /\ reslen <= max

let parse_bounded_seq_vlbytes_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot Type
= (x: bytes { parse_bounded_seq_vlbytes_pred min max x } )

let synth_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (x: parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes)
: Tot (parse_bounded_seq_vlbytes_t min max)
= x

let parse_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (parser (parse_bounded_vldata_strong_kind min max (log256' max) parse_seq_all_bytes_kind) (parse_bounded_seq_vlbytes_t min max))
= parse_synth (parse_bounded_seq_vlbytes' min max) (synth_bounded_seq_vlbytes min max)

let serialize_bounded_seq_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (serializer (parse_bounded_seq_vlbytes' min max))
= serialize_bounded_vldata_strong min max serialize_seq_all_bytes

let serialize_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (serializer (parse_bounded_seq_vlbytes min max))
= serialize_synth
    (parse_bounded_seq_vlbytes' min max)
    (synth_bounded_seq_vlbytes min max)
    (serialize_bounded_seq_vlbytes' min max)
    (fun (x: parse_bounded_seq_vlbytes_t min max) ->
      (x <: parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes)
    )
    ()


let parse_lseq_bytes_gen
  (sz: nat)
  (s: bytes { Seq.length s == sz } )
: GTot (Seq.lseq byte sz)
= s

let parse_lseq_bytes
  (sz: nat)
: Tot (parser (total_constant_size_parser_kind sz) (Seq.lseq byte sz))
= make_total_constant_size_parser sz (Seq.lseq byte sz) (parse_lseq_bytes_gen sz)

let serialize_lseq_bytes'
  (sz: nat)
: Tot (bare_serializer (Seq.lseq byte sz))
= fun x -> x

let serialize_lseq_bytes_correct
  (sz: nat)
: Lemma
  (serializer_correct (parse_lseq_bytes sz) (serialize_lseq_bytes' sz))
= ()

let serialize_lseq_bytes
  (sz: nat)
: Tot (serializer (parse_lseq_bytes sz))
= serialize_lseq_bytes_correct sz;
  serialize_lseq_bytes' sz

module S = LowParse.Spec.Sorted

let byte_compare (x y: byte) : Tot int =
  if x = y
  then 0
  else if x `FStar.UInt8.lt` y
  then -1
  else 1

let bytes_lex_compare (x y: bytes) : Tot int =
  S.lex_compare byte_compare (Seq.seq_to_list x) (Seq.seq_to_list y)

let bytes_lex_order (x y: bytes) : Tot bool =
  S.lex_order byte_compare (Seq.seq_to_list x) (Seq.seq_to_list y)

let bytes_lex_order_irrefl
  (x y: bytes)
: Lemma
  (requires (bytes_lex_order x y))
  (ensures (~ (x == y)))
= S.lex_order_irrefl byte_compare (fun _ _ -> ()) (Seq.seq_to_list x) (Seq.seq_to_list y)

let bytes_lex_order_trans
  (x y z: bytes)
: Lemma
  (requires (bytes_lex_order x y /\ bytes_lex_order y z))
  (ensures (bytes_lex_order x z))
= S.lex_order_trans byte_compare (fun _ _ -> ()) (fun _ _ _ -> ()) (Seq.seq_to_list x) (Seq.seq_to_list y) (Seq.seq_to_list z)

let bytes_lex_order_total
  (x y: bytes)
: Lemma
  (ensures (x == y \/ bytes_lex_order x y \/ bytes_lex_order y x))
= Seq.lemma_seq_list_bij x;
  Seq.lemma_seq_list_bij y;
  S.lex_order_total byte_compare (fun _ _ -> ()) (fun _ _ -> ()) (Seq.seq_to_list x) (Seq.seq_to_list y)

let bytes_lex_compare_append
  (l1 l2: bytes)
  (l1' l2': bytes)
: Lemma
  (requires (
    bytes_lex_compare l1 l2 < 0 /\
    Seq.length l1 == Seq.length l2
  ))
  (ensures (
    bytes_lex_compare (Seq.append l1 l1') (Seq.append l2 l2') < 0
  ))
= S.seq_to_list_append l1 l1';
  S.seq_to_list_append l2 l2';
  S.lex_compare_append byte_compare (Seq.seq_to_list l1) (Seq.seq_to_list l2) (Seq.seq_to_list l1') (Seq.seq_to_list l2')

let seq_to_list_length_one (#t: Type) (s: Seq.seq t) : Lemma
  (requires (Seq.length s == 1))
  (ensures (
    Seq.length s == 1 /\
    Seq.seq_to_list s == [Seq.index s 0]
  ))
= assert (s `Seq.equal` (Seq.index s 0 `Seq.cons` Seq.empty))

#push-options "--z3rlimit 16"
#restart-solver

let rec bytes_lex_order_prefix_or_append
  (l1 l2: bytes)
  (suff1 suff2: bytes)
: Lemma
  (requires (bytes_lex_order l1 l2 == true))
  (ensures (
    (Seq.length l1 <= Seq.length l2 /\ Seq.slice l2 0 (Seq.length l1) `Seq.equal` l1) \/
    bytes_lex_order (l1 `Seq.append` suff1) (l2 `Seq.append` suff2) == true
  ))
  (decreases (Seq.length l1))
= if Seq.length l1 = 0
  then ()
  else begin
    Seq.lemma_split l1 1;
    Seq.lemma_split l2 1;
    let h1 = Seq.slice l1 0 1 in
    let t1 = Seq.slice l1 1 (Seq.length l1) in
    let x1 = Seq.index h1 0 in
    assert (l1 == Seq.cons x1 t1);
    Seq.append_assoc h1 t1 suff1;
    let h2 = Seq.slice l2 0 1 in
    let t2 = Seq.slice l2 1 (Seq.length l2) in
    let x2 = Seq.index h2 0 in
    assert (l2 == Seq.cons x2 t2);
    Seq.append_assoc h2 t2 suff2;
    if Seq.index l1 0 `FStar.UInt8.lt` Seq.index l2 0
    then begin
      seq_to_list_length_one h1;
      seq_to_list_length_one h2;
      bytes_lex_compare_append h1 h2 (t1 `Seq.append` suff1) (t2 `Seq.append` suff2)
    end else begin
      assert (Seq.index l1 0 = Seq.index l2 0);
      S.seq_to_list_append l1 suff1;
      S.seq_to_list_append l2 suff2;
      S.seq_to_list_append t1 suff1;
      S.seq_to_list_append t2 suff2;
      bytes_lex_order_prefix_or_append t1 t2 suff1 suff2;
      ()
    end
  end

#pop-options

let bytes_lex_order_serialize_strong_prefix
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (l1 l2: t)
  (suff1 suff2: bytes)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    bytes_lex_order (serialize s l1) (serialize s l2) == true
  ))
  (ensures (
    bytes_lex_order (serialize s l1 `Seq.append` suff1) (serialize s l2 `Seq.append` suff2) == true
  ))
= let s1 = serialize s l1 in
  let s2 = serialize s l2 in
  bytes_lex_order_prefix_or_append s1 s2 suff1 suff2;
  if Seq.length s1 <= Seq.length s2 && Seq.slice s2 0 (Seq.length s1) = s1
  then begin
    Seq.lemma_split s2 (Seq.length s1);
    Seq.append_empty_r s2;
    serialize_strong_prefix s l1 l2 (Seq.slice s2 (Seq.length s1) (Seq.length s2)) Seq.empty;
    bytes_lex_order_irrefl (serialize s l1) (serialize s l2)
  end else
    ()

let bytes_length_first_lex_order (x y: bytes) : Tot bool =
  S.length_first_lex_order byte_compare (Seq.seq_to_list x) (Seq.seq_to_list y)

let bytes_length_first_lex_order_irrefl
  (x y: bytes)
: Lemma
  (requires (bytes_length_first_lex_order x y))
  (ensures (~ (x == y)))
= S.length_first_lex_order_irrefl byte_compare (fun _ _ -> ()) (Seq.seq_to_list x) (Seq.seq_to_list y)

let bytes_length_first_lex_order_trans
  (x y z: bytes)
: Lemma
  (requires (bytes_length_first_lex_order x y /\ bytes_length_first_lex_order y z))
  (ensures (bytes_length_first_lex_order x z))
= S.length_first_lex_order_trans byte_compare (fun _ _ -> ()) (fun _ _ _ -> ()) (Seq.seq_to_list x) (Seq.seq_to_list y) (Seq.seq_to_list z)

let bytes_length_first_lex_order_total
  (x y: bytes)
: Lemma
  (ensures (x == y \/ bytes_length_first_lex_order x y \/ bytes_length_first_lex_order y x))
= Seq.lemma_seq_list_bij x;
  Seq.lemma_seq_list_bij y;
  S.length_first_lex_order_total byte_compare (fun _ _ -> ()) (fun _ _ -> ()) (Seq.seq_to_list x) (Seq.seq_to_list y)

(*

let serialize_bounded_seq_vlbytes_upd
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: parse_bounded_seq_vlbytes_t min max)
  (y: bytes)
: Lemma
  (requires (Seq.length y == Seq.length x))
  (ensures (
    let sy = y in
    let y : parse_bounded_seq_vlbytes_t min max = y in
    let sx = serialize (serialize_bounded_seq_vlbytes min max) x in
    let lm = log256' max in
    lm + Seq.length y == Seq.length sx /\
    serialize (serialize_bounded_seq_vlbytes min max) y == seq_upd_seq sx lm sy
  ))
= serialize_bounded_vldata_strong_upd min max serialize_seq_all_bytes x y

let serialize_bounded_seq_vlbytes_upd_bw
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: parse_bounded_seq_vlbytes_t min max)
  (y: bytes)
: Lemma
  (requires (Seq.length y == Seq.length x))
  (ensures (
    let sy = y in
    let y : parse_bounded_seq_vlbytes_t min max = y in
    let sx = serialize (serialize_bounded_seq_vlbytes min max) x in
    let lm = log256' max in
    lm + Seq.length y == Seq.length sx /\
    serialize (serialize_bounded_seq_vlbytes min max) y == seq_upd_bw_seq sx 0 sy
  ))
= serialize_bounded_vldata_strong_upd_bw min max serialize_seq_all_bytes x y

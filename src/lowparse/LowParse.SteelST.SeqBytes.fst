module LowParse.SteelST.SeqBytes
include LowParse.Spec.SeqBytes
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
open Steel.ST.GenElim

module SZ = FStar.SizeT
module AP = LowParse.SteelST.ArrayPtr

inline_for_extraction
let validate_seq_all_bytes
: validator parse_seq_all_bytes
= fun _ len _ -> noop (); return len

let intro_seq_all_bytes
  (#opened: _)
  (#va: AP.v byte)
  (a: byte_array)
: STGhost (v parse_seq_all_bytes_kind bytes) opened
    (AP.arrayptr a va)
    (fun va' -> aparse parse_seq_all_bytes a va')
    True
    (fun va' ->
      array_of va' == AP.array_of va /\
      va'.contents == AP.contents_of va
    )
= intro_aparse _ a

let elim_seq_all_bytes
  (#opened: _)
  (#va: v parse_seq_all_bytes_kind bytes)
  (a: byte_array)
: STGhost (AP.v byte) opened
    (aparse parse_seq_all_bytes a va)
    (fun va' -> AP.arrayptr a va')
    True
    (fun va' ->
      AP.array_of va' == array_of va /\
      va.contents == AP.contents_of va'
    )
= elim_aparse _ a

let seq_all_bytes_length
  (#opened: _)
  (#va: v parse_seq_all_bytes_kind bytes)
  (a: byte_array)
: STGhost unit opened
    (aparse parse_seq_all_bytes a va)
    (fun _ -> aparse parse_seq_all_bytes a va)
    True
    (fun _ ->
      Seq.length va.contents == AP.length (array_of va)
    )
= let _ = elim_seq_all_bytes a in
  let _ = intro_seq_all_bytes a in
  vpattern_rewrite (aparse _ a) va

inline_for_extraction
let validate_lseq_bytes
  (sz: SZ.t)
: Tot (validator (parse_lseq_bytes (SZ.v sz)))
= validate_total_constant_size _ sz

inline_for_extraction
let jump_lseq_bytes
  (sz: SZ.t)
: Tot (jumper (parse_lseq_bytes (SZ.v sz)))
= jump_constant_size _ sz

let intro_lseq_bytes
  (#opened: _)
  (n: nat)
  (#va: _)
  (a: byte_array)
: STGhost (v (total_constant_size_parser_kind n) (Seq.lseq byte n)) opened
    (AP.arrayptr a va)
    (fun va' -> aparse (parse_lseq_bytes n) a va')
    (n == AP.length (AP.array_of va))
    (fun va' ->
      array_of' va' == AP.array_of va /\
      va'.contents == AP.contents_of va
    )
= intro_aparse (parse_lseq_bytes n) a

let elim_lseq_bytes
  (#opened: _)
  (n: nat)
  (#va': v (total_constant_size_parser_kind n) (Seq.lseq byte n))
  (a: byte_array)
: STGhost (AP.v byte) opened
    (aparse (parse_lseq_bytes n) a va')
    (fun va -> AP.arrayptr a va)
    True
    (fun va ->
      array_of' va' == AP.array_of va /\
      va'.contents == AP.contents_of va
    )
= elim_aparse (parse_lseq_bytes n) a

(* Sequences as lists *)

module I = LowParse.SteelST.Int
module NL = LowParse.SteelST.VCList.Sorted

#push-options "--z3rlimit 16 --fuel 1 --ifuel 6"

#restart-solver
let rec seq_all_bytes_to_nlist_byte
  (#opened: _)
  (#va: v parse_seq_all_bytes_kind bytes)
  (n: nat)
  (a: byte_array)
: STGhost (v (NL.parse_nlist_kind n I.parse_u8_kind) (NL.nlist n byte)) opened
    (aparse parse_seq_all_bytes a va)
    (fun va' -> aparse (NL.parse_nlist n I.parse_u8) a va')
    (n == Seq.length va.contents \/ n == AP.length (array_of va))
    (fun va' ->
      n == Seq.length va.contents /\
      n == AP.length (array_of va) /\
      array_of' va' == array_of' va /\
      va'.contents == Seq.seq_to_list va.contents
    )
    (decreases n)
= seq_all_bytes_length a;
  let _ = elim_seq_all_bytes a in
  noop ();
  if n = 0
  then begin
    NL.intro_nlist_nil n I.parse_u8 a
  end else begin
    let n' : nat = n - 1 in
    let a' = AP.gsplit a 1sz in
    let _ = gen_elim () in
    let vl = vpattern_replace (AP.arrayptr a) in
    I.parse_u8_spec' (AP.contents_of vl);
    parser_kind_prop_equiv I.parse_u8_kind I.parse_u8;
    noop ();
    let _ = intro_aparse I.parse_u8 a in
    let _ = intro_seq_all_bytes a' in
    let _ = seq_all_bytes_to_nlist_byte n' a' in
    NL.intro_nlist_cons n I.parse_u8 n' a a'
  end

#restart-solver
let rec seq_all_bytes_from_nlist_byte
  (#opened: _)
  (n: nat)
  (#va: v (NL.parse_nlist_kind n I.parse_u8_kind) (NL.nlist n byte))
  (a: byte_array)
: STGhost (v parse_seq_all_bytes_kind bytes) opened
    (aparse (NL.parse_nlist n I.parse_u8) a va)
    (fun va' -> aparse parse_seq_all_bytes a va')
    True
    (fun va' ->
      array_of' va' == array_of' va /\
      va'.contents `Seq.equal` Seq.seq_of_list va.contents
    )
    (decreases n)
= if n = 0
  then begin
    let _ = NL.elim_nlist_nil n I.parse_u8 a in
    intro_seq_all_bytes a
  end else begin
    let n' : nat = n - 1 in
    let a' = NL.elim_nlist_cons I.parse_u8 n n' a in
    let _ = gen_elim () in
    let vl = elim_aparse I.parse_u8 a in
    I.parse_u8_spec' (AP.contents_of vl);
    Seq.lemma_seq_of_list_induction va.contents;
    let _ = seq_all_bytes_from_nlist_byte n' a' in
    let _ = elim_seq_all_bytes a' in
    let _ = AP.join a a' in
    intro_seq_all_bytes a
  end

#pop-options

module I16 = FStar.Int16

inline_for_extraction
let byte_compare_impl : NL.compare_impl I.parse_u8 byte_compare =
  fun a1 _ a2 _ ->
    let x1 = I.read_u8 a1 in
    let x2 = I.read_u8 a2 in
    if x1 = x2
    then return 0s
    else if x1 `FStar.UInt8.lt` x2
    then return (-1s)
    else return 1s

inline_for_extraction
let byte_array_lex_compare
  (na0: SZ.t)
  (#va0: AP.v byte)
  (a0: byte_array)
  (nb0: SZ.t)
  (#vb0: AP.v byte)
  (b0: byte_array)
: ST I16.t
    (AP.arrayptr a0 va0 `star` AP.arrayptr b0 vb0)
    (fun _ -> AP.arrayptr a0 va0 `star` AP.arrayptr b0 vb0)
    (SZ.v na0 == AP.length (AP.array_of va0) /\ SZ.v nb0 == AP.length (AP.array_of vb0))
    (fun res -> I16.v res `NL.same_sign` bytes_lex_compare (AP.contents_of va0) (AP.contents_of vb0))
= Seq.lemma_seq_list_bij (AP.contents_of va0);
  Seq.lemma_seq_list_bij (AP.contents_of vb0);
  let _ = intro_seq_all_bytes a0 in
  let _ = seq_all_bytes_to_nlist_byte (SZ.v na0) a0 in
  let _ = intro_seq_all_bytes b0 in
  let _ = seq_all_bytes_to_nlist_byte (SZ.v nb0) b0 in
  let res = NL.nlist_lex_compare I.jump_u8 byte_compare byte_compare_impl na0 a0 nb0 b0 in
  let _ = seq_all_bytes_from_nlist_byte (SZ.v nb0) b0 in
  let _ = elim_seq_all_bytes b0 in
  vpattern_rewrite (AP.arrayptr b0) vb0;
  let _ = seq_all_bytes_from_nlist_byte (SZ.v na0) a0 in
  let _ = elim_seq_all_bytes a0 in
  vpattern_rewrite (AP.arrayptr a0) va0;
  return res

inline_for_extraction
let byte_array_lex_order
  (na0: SZ.t)
  (#va0: AP.v byte)
  (a0: byte_array)
  (nb0: SZ.t)
  (#vb0: AP.v byte)
  (b0: byte_array)
: ST bool
    (AP.arrayptr a0 va0 `star` AP.arrayptr b0 vb0)
    (fun _ -> AP.arrayptr a0 va0 `star` AP.arrayptr b0 vb0)
    (SZ.v na0 == AP.length (AP.array_of va0) /\ SZ.v nb0 == AP.length (AP.array_of vb0))
    (fun res -> res == bytes_lex_order (AP.contents_of va0) (AP.contents_of vb0))
= let comp = byte_array_lex_compare na0 a0 nb0 b0 in
  return (comp `I16.lt` 0s)

inline_for_extraction
let byte_array_length_first_lex_order
  (na0: SZ.t)
  (#va0: AP.v byte)
  (a0: byte_array)
  (nb0: SZ.t)
  (#vb0: AP.v byte)
  (b0: byte_array)
: ST bool
    (AP.arrayptr a0 va0 `star` AP.arrayptr b0 vb0)
    (fun _ -> AP.arrayptr a0 va0 `star` AP.arrayptr b0 vb0)
    (SZ.v na0 == AP.length (AP.array_of va0) /\ SZ.v nb0 == AP.length (AP.array_of vb0))
    (fun res -> res == bytes_length_first_lex_order (AP.contents_of va0) (AP.contents_of vb0))
= Seq.lemma_seq_list_bij (AP.contents_of va0);
  Seq.lemma_seq_list_bij (AP.contents_of vb0);
  let _ = intro_seq_all_bytes a0 in
  let _ = seq_all_bytes_to_nlist_byte (SZ.v na0) a0 in
  let _ = intro_seq_all_bytes b0 in
  let _ = seq_all_bytes_to_nlist_byte (SZ.v nb0) b0 in
  let res = NL.nlist_length_first_lex_order I.jump_u8 byte_compare byte_compare_impl na0 a0 nb0 b0 in
  let _ = seq_all_bytes_from_nlist_byte (SZ.v nb0) b0 in
  let _ = elim_seq_all_bytes b0 in
  vpattern_rewrite (AP.arrayptr b0) vb0;
  let _ = seq_all_bytes_from_nlist_byte (SZ.v na0) a0 in
  let _ = elim_seq_all_bytes a0 in
  vpattern_rewrite (AP.arrayptr a0) va0;
  return res

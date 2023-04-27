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

(* Sequences as lists *)

module I = LowParse.SteelST.Int
module NL = LowParse.SteelST.VCList

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

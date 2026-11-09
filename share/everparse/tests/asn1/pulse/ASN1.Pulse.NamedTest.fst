module ASN1.Pulse.NamedTest
#lang-pulse

(* Named C types through impl descriptors (ASN1.Pulse.Rel): a SEQUENCE
   parsed into and written from a C struct, an OPTIONAL component as a named
   case type, and a CHOICE as a named case type, instead of nested pairs,
   `option` and `either`.

     Ch  ::= CHOICE { i INTEGER (small), o OCTET STRING }
     Rec ::= SEQUENCE { a INTEGER (small), b BOOLEAN OPTIONAL, c Ch }

   Extraction roots: `validate_rec`, `parse_rec`, `jit_rec` (JIT writer of
   raw bytes), `jit_raw_rec` (the same, as a writer of raw values),
   `jit_typed_rec` (the same, as a writer of typed values, taking the
   relation returned by `parse_rec`, weakened by
   `ASN1.Pulse.RelKeep.to_writer`) and `roundtrip_rec` (parse then write,
   verified to write back the input bytes.) A KEEP-BYTES test (`Outer`)
   follows at the end. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.Interpreter
open ASN1.Pulse.Parser
open ASN1.Pulse.RawRel
open ASN1.Pulse.JitWriter
open ASN1.Pulse.RawJitWriter
open ASN1.Pulse.TypedWriter
open ASN1.Syntax
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module I64 = FStar.Int64
module LPS = LowParse.Pulse.Base
module RW = ASN1.Pulse.RawWriter
module SZ = FStar.SizeT
module SB = LowParse.Spec.Base
module W = LowParse.Pulse.R2L
module Trade = Pulse.Lib.Trade

(* The schema *)

noextract
let ch_lc : list (asn1_id_t & asn1_content_k) =
  [(integer_id, ASN1_TERMINAL (ASN1_INTEGER 8)); (octetstring_id, ASN1_TERMINAL ASN1_OCTETSTRING)]

noextract
let ch_pf : squash (List.Tot.noRepeats (List.Tot.map fst ch_lc)) = _ by (choice_tac ())

noextract
let ch_k = ASN1_CHOICE_ILC ch_lc ch_pf

noextract
let rec_items =
  ASN1_GEN_ITEMS_CONS _ _ (ASN1_PLAIN_ILC (asn1_bounded_integer 8)) _
  (ASN1_GEN_ITEMS_CONS _ _ (ASN1_OPTION_ILC asn1_boolean) _
  (ASN1_GEN_ITEMS_CONS _ _ (ASN1_PLAIN_ILC ch_k) _ ASN1_GEN_ITEMS_NIL))

noextract
let rec_gitems : asn1_gen_items_lk = (| _, rec_items |)

noextract
let rec_k = ASN1_ILC sequence_id (ASN1_SEQUENCE rec_gitems)

(* The C types *)

[@@FStar.Attributes.rename_let "Ch"]
noeq
type ch_t =
| Ch_i : i: I64.t -> ch_t
| Ch_o : o: S.slice U8.t -> ch_t

[@@FStar.Attributes.rename_let "Rec_b"]
type rec_b_t =
| Rec_b_absent : rec_b_t
| Rec_b_present : b: bool -> rec_b_t

[@@FStar.Attributes.rename_let "Rec"]
noeq
type rec_t = {
  a: I64.t;
  b: rec_b_t;
  c: ch_t;
}

(* The descriptor: shallow views onto the canonical shapes *)

inline_for_extraction noextract
let ch_view (x: ch_t) : either I64.t (S.slice U8.t) =
  match x with
  | Ch_i i -> Inl i
  | Ch_o o -> Inr o

inline_for_extraction noextract
let ch_mk (x: either I64.t (S.slice U8.t)) : ch_t =
  match x with
  | Inl i -> Ch_i i
  | Inr o -> Ch_o o

noextract
let ch_desc : adesc ch_k ch_t =
  D_VIEW (D_CHOICE ch_lc ch_pf (LC_CONS integer_id (CD_TERMINAL (ASN1_INTEGER 8)) (LC_SINGLE octetstring_id (CD_TERMINAL ASN1_OCTETSTRING))))
    ch_t ch_view ch_mk ()

inline_for_extraction noextract
let rec_b_view (x: rec_b_t) : option bool =
  match x with
  | Rec_b_absent -> None
  | Rec_b_present b -> Some b

inline_for_extraction noextract
let rec_b_mk (x: option bool) : rec_b_t =
  match x with
  | None -> Rec_b_absent
  | Some b -> Rec_b_present b

inline_for_extraction noextract
let rec_view (x: rec_t) : I64.t & (rec_b_t & ch_t) = (x.a, (x.b, x.c))

inline_for_extraction noextract
let rec_mk (x: I64.t & (rec_b_t & ch_t)) : rec_t =
  let (a, (b, c)) = x in { a = a; b = b; c = c }

noextract
let rec_desc : adesc rec_k rec_t =
  D_ILC sequence_id (CD_VIEW
    (CD_SEQUENCE rec_gitems
      (ID_CONS (DD_PLAIN (D_ILC integer_id (CD_TERMINAL (ASN1_INTEGER 8))))
      (ID_CONS (DD_VIEW (DD_OPTION (D_ILC boolean_id (CD_TERMINAL ASN1_BOOLEAN))) rec_b_t rec_b_view rec_b_mk ())
      (ID_SINGLE (DD_PLAIN ch_desc)))))
    rec_t rec_view rec_mk ())

noextract
let rec_supported : squash (supported_k rec_k) =
  _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

noextract
let rec_psupported : squash (psupported_k rec_k) =
  _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

noextract
let rec_ok : squash (RW.raw_ok rec_k) =
  _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

let half_perm : perm = 1.0R /. 2.0R

(* Extraction roots *)

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.NamedTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_rec : LPS.validator #(asn1_t rec_k) #asn1_strong_parser_kind (asn1_as_parser rec_k) =
  validate_k rec_k rec_supported

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.NamedTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_rec : aparser #rec_t #(asn1_t rec_k) (arel true rec_desc) #asn1_strong_parser_kind (asn1_as_parser rec_k) =
  fun input #pm #w #v -> parse_d rec_desc rec_psupported input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.NamedTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%jit_writer_d];
  zeta; iota; primops]]
let jit_rec : jwx (raw_arel rec_desc) (kacc rec_k) 1.0R =
  fun x' #y out pos #v #p -> jit_writer_d rec_desc rec_ok 1.0R x' #y out pos #v #p

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.NamedTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%jit_writer_d];
  zeta; iota; primops]]
let jit_raw_rec : raw_jit_writer_d_t rec_desc rec_ok 1.0R =
  fun x' #y out pos #v #p -> jit_write_raw_d rec_desc rec_ok 1.0R (jit_writer_d rec_desc rec_ok (1.0R /. 2.0R)) x' #y out pos #v #p

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.NamedTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%jit_writer_d];
  zeta; iota; primops]]
let jit_typed_rec : typed_jit_writer_d_t rec_desc 1.0R =
  fun x' #v out pos #b #p -> write_typed_d rec_desc rec_ok 1.0R (jit_write_raw_d rec_desc rec_ok 1.0R (jit_writer_d rec_desc rec_ok (1.0R /. 2.0R))) x' #v out pos #b #p

(* Parse then write: if the output fits, the bytes written are exactly the
   parsed input. *)
fn roundtrip_rec (input: S.slice U8.t) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_t rec_k))
  (out: S.slice U8.t) (pos: ref SZ.t) (#b: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
requires S.pts_to input w ** pts_to out b ** pts_to pos p **
  pure (parsed #asn1_strong_parser_kind (asn1_as_parser rec_k) w v /\ SZ.v p <= Seq.length b)
returns res: jit_result
ensures exists* b' p' . S.pts_to input w ** pts_to out b' ** pts_to pos p' **
  pure ((res == JIT_OK \/ res == JIT_NO_SPACE) /\
    (res == JIT_OK ==> W.r2l_post w (SZ.v p) b true (SZ.v p') b'))
{
  let x = parse_rec input #1.0R #w #v;
  parsed_encodable_d rec_k w v;
  ASN1.Pulse.RelKeep.to_writer rec_desc 1.0R x v;
  let res = jit_typed_rec x #v out pos;
  Trade.elim_trade (arel false rec_desc 1.0R x v) _;
  Trade.elim_trade _ _;
  res
}

(* KEEP-BYTES: a component that keeps its bytes when parsed

     Outer ::= SEQUENCE { x INTEGER (small), r Rec } -- r: KEEP-BYTES

   `parse_outer` returns `r` with its bytes (`kraw`), the writer
   `jit_typed_outer` ignores them, and `roundtrip_outer` hands the parsed
   value to the writer through `ASN1.Pulse.RelKeep.to_writer`. *)

noextract
let outer_items =
  ASN1_GEN_ITEMS_CONS _ _ (ASN1_PLAIN_ILC (asn1_bounded_integer 8)) _
  (ASN1_GEN_ITEMS_CONS _ _ (ASN1_PLAIN_ILC rec_k) _ ASN1_GEN_ITEMS_NIL)

noextract
let outer_gitems : asn1_gen_items_lk = (| _, outer_items |)

noextract
let outer_k = ASN1_ILC sequence_id (ASN1_SEQUENCE outer_gitems)

[@@FStar.Attributes.rename_let "Outer"]
noeq
type outer_t = {
  x: I64.t;
  r: kept rec_t;
}

inline_for_extraction noextract
let outer_view (o: outer_t) : I64.t & kept rec_t = (o.x, o.r)

inline_for_extraction noextract
let outer_mk (o: I64.t & kept rec_t) : outer_t =
  let (x, r) = o in { x = x; r = r }

noextract
let rec_wf : squash (ASN1.Spec.Conformance.wf rec_k) =
  _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

noextract
let outer_desc : adesc outer_k outer_t =
  D_ILC sequence_id (CD_VIEW
    (CD_SEQUENCE outer_gitems
      (ID_CONS (DD_PLAIN (D_ILC integer_id (CD_TERMINAL (ASN1_INTEGER 8))))
      (ID_SINGLE (DD_PLAIN (D_KEEP rec_desc rec_wf)))))
    outer_t outer_view outer_mk ())

noextract
let outer_supported : squash (supported_k outer_k) =
  _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

noextract
let outer_psupported : squash (psupported_k outer_k) =
  _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

noextract
let outer_ok : squash (RW.raw_ok outer_k) =
  _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.NamedTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_outer : LPS.validator #(asn1_t outer_k) #asn1_strong_parser_kind (asn1_as_parser outer_k) =
  validate_k outer_k outer_supported

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.NamedTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_outer : aparser #outer_t #(asn1_t outer_k) (arel true outer_desc) #asn1_strong_parser_kind (asn1_as_parser outer_k) =
  fun input #pm #w #v -> parse_d outer_desc outer_psupported input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.NamedTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%jit_writer_d];
  zeta; iota; primops]]
let jit_typed_outer : typed_jit_writer_d_t outer_desc 1.0R =
  fun x' #v out pos #b #p -> write_typed_d outer_desc outer_ok 1.0R (jit_write_raw_d outer_desc outer_ok 1.0R (jit_writer_d outer_desc outer_ok (1.0R /. 2.0R))) x' #v out pos #b #p

(* Parse then write: the parsed value, with its kept bytes, is handed to the
   writer (which only needs `arel false`) and the relation of the parser is
   restored afterwards. *)
fn roundtrip_outer (input: S.slice U8.t) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_t outer_k))
  (out: S.slice U8.t) (pos: ref SZ.t) (#b: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
requires S.pts_to input w ** pts_to out b ** pts_to pos p **
  pure (parsed #asn1_strong_parser_kind (asn1_as_parser outer_k) w v /\ SZ.v p <= Seq.length b)
returns res: jit_result
ensures exists* b' p' . S.pts_to input w ** pts_to out b' ** pts_to pos p' **
  pure ((res == JIT_OK \/ res == JIT_NO_SPACE) /\
    (res == JIT_OK ==> W.r2l_post w (SZ.v p) b true (SZ.v p') b'))
{
  let x = parse_outer input #1.0R #w #v;
  parsed_encodable_d outer_k w v;
  ASN1.Pulse.RelKeep.to_writer outer_desc 1.0R x v;
  let res = jit_typed_outer x #v out pos;
  Trade.elim_trade (arel false outer_desc 1.0R x v) _;
  Trade.elim_trade _ _;
  res
}

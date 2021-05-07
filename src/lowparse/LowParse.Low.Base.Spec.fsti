module LowParse.Low.Base.Spec
include LowParse.Spec.Base
include LowParse.Slice

module M = LowParse.Math
module B = LowStar.Monotonic.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

let valid'
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: GTot Type0
= U32.v pos <= U32.v s.len /\
  live_slice h s /\
  Some? (parse p (bytes_of_slice_from h s pos))

val valid
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: GTot Type0

val valid_equiv
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (valid p h s pos <==> valid' p h s pos)

val valid_dec
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Ghost bool
  (requires (live_slice h s))
  (ensures (fun b ->
    b == true <==> valid p h s pos
  ))

let valid_elim
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos))
  (ensures (valid' p h s pos))
//  [SMTPat (valid p h s pos)]
= valid_equiv p h s pos

let valid_elim'
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos))
  (ensures (U32.v pos + k.parser_kind_low <= U32.v s.len /\
  live_slice h s))
  [SMTPat (valid p h s pos)]
= parser_kind_prop_equiv k p;
  valid_equiv p h s pos

let contents'
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Ghost t
  (requires (valid' p h s pos))
  (ensures (fun _ -> True))
= let Some (v, _) = parse p (bytes_of_slice_from h s pos) in
  v

val contents
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Ghost t
  (requires (valid p h s pos))
  (ensures (fun _ -> True))

val contents_eq
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos))
  (ensures (valid p h s pos /\ valid' p h s pos /\ contents p h s pos == contents' p h s pos))

let content_length'
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Ghost nat
  (requires (valid' p h sl pos))
  (ensures (fun res ->
    U32.v pos + res <= U32.v sl.len /\
    k.parser_kind_low <= res /\ (
    match k.parser_kind_high with
    | None -> True
    | Some max -> res <= max
  )))
= let Some (_, consumed) = parse p (bytes_of_slice_from h sl pos) in
  parser_kind_prop_equiv k p;
  consumed

val content_length
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Ghost nat
  (requires (valid p h sl pos))
  (ensures (fun res -> True))

val serialized_length
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Ghost nat
  (requires True)
  (ensures (fun res ->
    k.parser_kind_low <= res /\ (
    match k.parser_kind_high with
    | None -> True
    | Some max -> res <= max
  )))

val serialized_length_eq
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (serialized_length s x == Seq.length (serialize s x))

val content_length_eq_gen
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p h sl pos))
  (ensures (valid p h sl pos /\ valid' p h sl pos /\ content_length p h sl pos == content_length' p h sl pos))

let content_length_post
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p h sl pos))
  (ensures (
    let res = content_length p h sl pos in
    U32.v pos + res <= U32.v sl.len /\
    k.parser_kind_low <= res /\ (
    match k.parser_kind_high with
    | None -> True
    | Some max -> res <= max
  )))
  [SMTPat (content_length p h sl pos)]
= content_length_eq_gen p h sl pos

let valid_facts
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  ((valid p h sl pos <==> valid' p h sl pos) /\
   (valid p h sl pos ==> (
     contents p h sl pos == contents' p h sl pos /\
     content_length p h sl pos == content_length' p h sl pos
  )))
= valid_equiv p h sl pos;
  Classical.move_requires (contents_eq p h sl) pos;
  Classical.move_requires (content_length_eq_gen p h sl) pos

val content_length_eq
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p h sl pos))
  (ensures (content_length p h sl pos == serialized_length s (contents p h sl pos)))
  [SMTPat (serialized_length s (contents p h sl pos))]

let valid_pos
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
= valid p h sl pos /\
  U32.v pos + content_length p h sl pos == U32.v pos'

val get_valid_pos
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Ghost U32.t
  (requires (valid p h sl pos))
  (ensures (fun pos' -> True))

val get_valid_pos_post
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p h sl pos))
  (ensures (
    let pos' = get_valid_pos p h sl pos in
    valid_pos p h sl pos pos'
  ))
  [SMTPat (get_valid_pos p h sl pos)]

let valid_pos_get_valid_pos
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_pos p h sl pos pos'))
  (ensures (get_valid_pos p h sl pos == pos'))
  [SMTPat (valid_pos p h sl pos pos'); SMTPat (get_valid_pos p h sl pos)]
= ()


let valid_pos_consumes_all
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid p h sl pos /\
    k.parser_kind_subkind == Some ParserConsumesAll
  ))
  (ensures (
    valid_pos p h sl pos sl.len
  ))
= parser_kind_prop_equiv k p;
  valid_facts p h sl pos

let valid_content
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (x: t)
= valid p h sl pos /\
  contents p h sl pos == x

let valid_content_pos
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (x: t)
  (pos' : U32.t)
= valid_pos p h sl pos pos' /\
  valid_content p h sl pos x

let valid_frame
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (l: B.loc)
  (h': HS.mem)
: Lemma
  (requires (live_slice h sl /\ B.modifies l h h' /\ B.loc_disjoint (loc_slice_from sl pos) l))
  (ensures (
    (valid p h sl pos \/ valid p h' sl pos) ==> (
    valid p h sl pos /\
    valid_content_pos p h' sl pos (contents p h sl pos) (get_valid_pos p h sl pos)
  )))
  [SMTPatOr [
    [SMTPat (valid p h sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (valid p h' sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (contents p h sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (contents p h' sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (content_length p h sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (content_length p h' sl pos); SMTPat (B.modifies l h h')];
  ]]
= let f () : Lemma
    (requires (U32.v pos <= U32.v sl.len /\ (valid p h sl pos \/ valid p h' sl pos)))
    (ensures (
    valid p h sl pos /\
    valid_content_pos p h' sl pos (contents p h sl pos) (get_valid_pos p h sl pos)
    ))
  =
    B.modifies_buffer_from_to_elim sl.base pos sl.len l h h';
    valid_facts p h sl pos;
    valid_facts p h' sl pos
  in
  Classical.move_requires f ()

(* Case where we do not have the strong prefix property (e.g. lists): we need an extra length *)

let bytes_of_slice_from_to  (#rrel #rel: _)
  (h: HS.mem) (s: slice rrel rel) (pos pos': U32.t) : Ghost bytes (requires  (U32.v pos <= U32.v pos' /\ U32.v pos' <= U32.v s.len)) (ensures (fun _ -> True)) =
  Seq.slice (B.as_seq h s.base) (U32.v pos) (U32.v pos')

let valid_exact'
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0
= U32.v pos <= U32.v pos' /\
  U32.v pos' <= U32.v s.len /\
  live_slice h s /\ (
  let len' = pos' `U32.sub` pos in
  match parse p (bytes_of_slice_from_to h s pos pos') with
  | None -> False
  | Some (_, consumed) -> (consumed <: nat) == U32.v len'
  )

val valid_exact
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0

val valid_exact_equiv
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (valid_exact p h s pos pos' <==> valid_exact' p h s pos pos')

let valid_exact_elim
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos'))
  (ensures (valid_exact' p h s pos pos'))
//  [SMTPat (valid_exact p h s pos pos')]
= valid_exact_equiv p h s pos pos'

let valid_exact_elim'
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos'))
  (ensures (
    live_slice h s /\
    U32.v pos <= U32.v pos' /\
    U32.v pos' <= U32.v s.len /\ (
    let length = U32.v pos' - U32.v pos in
    k.parser_kind_low <= length /\ (
    match k.parser_kind_high with
    | Some high -> length <= high
    | _ -> True
  ))))
  [SMTPat (valid_exact p h s pos pos')]
= parser_kind_prop_equiv k p;
  valid_exact_equiv p h s pos pos'

let contents_exact'
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost t
  (requires (valid_exact' p h s pos pos'))
  (ensures (fun _ -> True))
= let (Some (v, _)) = parse p (bytes_of_slice_from_to h s pos pos') in
  v

val contents_exact
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost t
  (requires (valid_exact p h s pos pos'))
  (ensures (fun _ -> True))

val contents_exact_eq
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos'))
  (ensures (valid_exact p h s pos pos' /\ valid_exact' p h s pos pos' /\ contents_exact p h s pos pos' == contents_exact' p h s pos pos'))

let valid_exact_serialize
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h sl pos pos'))
  (ensures (
    serialize s (contents_exact p h sl pos pos') == bytes_of_slice_from_to h sl pos pos'
  ))
= valid_exact_equiv p h sl pos pos' ;
  contents_exact_eq p h sl pos pos' ;
  serializer_correct_implies_complete p s;
  ()

let serialize_valid_exact
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (sl: slice rrel rel)
  (x: t)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    live_slice h sl /\
    U32.v pos + Seq.length (serialize s x) == U32.v pos' /\
    U32.v pos' <= U32.v sl.len /\
    bytes_of_slice_from_to h sl pos pos' `Seq.equal` serialize s x
  ))
  (ensures (
    valid_exact p h sl pos pos' /\
    contents_exact p h sl pos pos' == x
  ))
= serializer_correct_implies_complete p s;
  valid_exact_equiv p h sl pos pos' ;
  contents_exact_eq p h sl pos pos'

let valid_exact_frame
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (live_slice h s /\ B.modifies l h h' /\ B.loc_disjoint l (loc_slice_from_to s pos pos')))
  (ensures (
    (valid_exact p h s pos pos' \/ valid_exact p h' s pos pos') ==> (
    valid_exact p h s pos pos' /\
    valid_exact p h' s pos pos' /\ contents_exact p h' s pos pos' == contents_exact p h s pos pos'
  )))
  [SMTPatOr [
    [SMTPat (valid_exact p h s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (valid_exact p h' s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (contents_exact p h s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (contents_exact p h' s pos pos'); SMTPat (B.modifies l h h')];
  ]]
= let f () : Lemma
    (requires (
      U32.v pos <= U32.v pos' /\ U32.v pos' <= U32.v s.len /\ (valid_exact p h s pos pos' \/ valid_exact p h' s pos pos')
    ))
    (ensures (
      valid_exact p h s pos pos' /\
      valid_exact p h' s pos pos' /\ contents_exact p h' s pos pos' == contents_exact p h s pos pos'
    ))
  =
    valid_exact_equiv p h s pos pos' ;
    valid_exact_equiv p h' s pos pos' ;
    Classical.move_requires (contents_exact_eq p h s pos) pos' ;
    Classical.move_requires (contents_exact_eq p h' s pos) pos' ;
    B.modifies_buffer_from_to_elim s.base pos pos' l h h'
  in
  Classical.move_requires f ()

let valid_valid_exact_consumes_all
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserConsumesAll))
  (ensures (
    (valid p h s pos \/ valid_exact p h s pos s.len) ==>
    (valid_exact p h s pos s.len /\
    valid_content_pos p h s pos (contents_exact p h s pos s.len) s.len)
  ))
= parser_kind_prop_equiv k p;
  valid_facts p h s pos;
  valid_exact_equiv p h s pos s.len;
  Classical.move_requires (contents_exact_eq p h s pos) s.len

let valid_valid_exact
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    let npos' = U32.v pos + content_length p h s pos in
    npos' <= U32.v s.len /\ (
    let pos' = U32.uint_to_t npos' in
    valid_exact p h s pos pos' /\
    contents_exact p h s pos pos' == contents p h s pos
  )))
= valid_facts p h s pos;
  let npos' = U32.v pos + content_length p h s pos in
  let pos' = U32.uint_to_t npos' in
  valid_exact_equiv p h s pos pos' ;
  Classical.move_requires (contents_exact_eq p h s pos) pos' ;
  parse_strong_prefix p (bytes_of_slice_from h s pos) (bytes_of_slice_from_to h s pos pos')

let valid_pos_valid_exact
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_pos p h s pos pos' /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_exact p h s pos pos' /\
    contents_exact p h s pos pos' == contents p h s pos
  ))
= valid_valid_exact p h s pos

let valid_pos_valid_exact_pat
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_pos p h s pos pos' /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_exact p h s pos pos' /\
    contents_exact p h s pos pos' == contents p h s pos
  ))
  [SMTPat (valid_exact p h s pos pos'); SMTPat (valid p h s pos)]
= valid_pos_valid_exact p h s pos pos'

let valid_exact_valid
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos' /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_content_pos p h s pos (contents_exact p h s pos pos') pos'
  ))
= valid_exact_equiv p h s pos pos' ;
  contents_exact_eq p h s pos pos' ;
  valid_facts p h s pos;
  parse_strong_prefix p (bytes_of_slice_from_to h s pos pos') (bytes_of_slice_from h s pos)

let valid_exact_valid_pat
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos' /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_content_pos p h s pos (contents_exact p h s pos pos') pos'
  ))
  [SMTPat (valid_exact p h s pos pos'); SMTPat (valid p h s pos)]
= valid_exact_valid p h s pos pos'

let valid_pos_frame_strong_1
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h': HS.mem)
: Lemma
  (requires (
    valid_pos p h sl pos pos' /\
    B.modifies l h h' /\ B.loc_disjoint (loc_slice_from_to sl pos pos') l /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_pos p h sl pos pos' /\
    valid_content_pos p h' sl pos (contents p h sl pos) pos'
  ))
= valid_pos_valid_exact p h sl pos pos';
  valid_exact_valid p h' sl pos pos'

let valid_pos_frame_strong_2
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h': HS.mem)
: Lemma
  (requires (
    live_slice h sl /\
    valid_pos p h' sl pos pos' /\
    B.modifies l h h' /\ B.loc_disjoint (loc_slice_from_to sl pos pos') l /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_pos p h sl pos pos' /\
    valid_pos p h' sl pos pos' /\
    valid_content_pos p h sl pos (contents p h' sl pos) pos'
  ))
= valid_pos_valid_exact p h' sl pos pos';
  valid_exact_valid p h sl pos pos'

let valid_pos_frame_strong
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h': HS.mem)
: Lemma
  (requires (
    live_slice h sl /\
    B.modifies l h h' /\ B.loc_disjoint (loc_slice_from_to sl pos pos') l /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    (valid_pos p h sl pos pos' \/ valid_pos p h' sl pos pos') ==> (
    valid_pos p h sl pos pos' /\
    valid_content_pos p h' sl pos (contents p h sl pos) pos'
  )))
= Classical.move_requires (valid_pos_frame_strong_1 p h sl pos pos' l) h';
  Classical.move_requires (valid_pos_frame_strong_2 p h sl pos pos' l) h'

let valid_frame_strong
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (l: B.loc)
  (h': HS.mem)
: Lemma
  (requires (
    live_slice h sl /\
    valid p h sl pos /\
    B.modifies l h h' /\ B.loc_disjoint (loc_slice_from_to sl pos (get_valid_pos p h sl pos)) l /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_content_pos p h' sl pos (contents p h sl pos) (get_valid_pos p h sl pos)
  ))
  [SMTPatOr [
//    [SMTPat (valid p h sl pos); SMTPat (B.modifies_inert l h h')];
    [SMTPat (valid p h' sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (contents p h' sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (content_length p h' sl pos); SMTPat (B.modifies l h h')];
  ]]
= valid_pos_frame_strong p h sl pos (get_valid_pos p h sl pos) l h'

let valid_exact_ext_intro
  (#rrel1 #rel1: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h1: HS.mem)
  (s1: slice rrel1 rel1)
  (pos1: U32.t)
  (pos1' : U32.t)
  (h2: HS.mem)
  (#rrel2 #rel2: _)
  (s2: slice rrel2 rel2)
  (pos2: U32.t)
  (pos2' : U32.t)
: Lemma
  (requires (
    valid_exact p h1 s1 pos1 pos1' /\
    live_slice h2 s2 /\
    U32.v pos1' - U32.v pos1 == U32.v pos2' - U32.v pos2 /\
    U32.v pos2' <= U32.v s2.len /\
    bytes_of_slice_from_to h1 s1 pos1 pos1' `Seq.equal` bytes_of_slice_from_to h2 s2 pos2 pos2'
  ))
  (ensures (
    valid_exact p h2 s2 pos2 pos2' /\
    contents_exact p h2 s2 pos2 pos2' == contents_exact p h1 s1 pos1 pos1'
  ))
= valid_exact_equiv p h1 s1 pos1 pos1' ;
  valid_exact_equiv p h2 s2 pos2 pos2' ;
  contents_exact_eq p h1 s1 pos1 pos1' ;
  contents_exact_eq p h2 s2 pos2 pos2'

let valid_exact_ext_elim
  (#rrel1 #rel1: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h1: HS.mem)
  (s1: slice rrel1 rel1)
  (pos1: U32.t)
  (pos1' : U32.t)
  (h2: HS.mem)
  (#rrel2 #rel2: _)
  (s2: slice rrel2 rel2)
  (pos2: U32.t)
  (pos2' : U32.t)
: Lemma
  (requires (
    valid_exact p h1 s1 pos1 pos1' /\
    valid_exact p h2 s2 pos2 pos2' /\
    contents_exact p h1 s1 pos1 pos1' == contents_exact p h2 s2 pos2 pos2'
  ))
  (ensures (
    U32.v pos2' - U32.v pos2 == U32.v pos1' - U32.v pos1 /\
    bytes_of_slice_from_to h1 s1 pos1 pos1' == bytes_of_slice_from_to h2 s2 pos2 pos2'
  ))
= valid_exact_equiv p h1 s1 pos1 pos1' ;
  valid_exact_equiv p h2 s2 pos2 pos2' ;
  contents_exact_eq p h1 s1 pos1 pos1' ;
  contents_exact_eq p h2 s2 pos2 pos2' ;
  parser_kind_prop_equiv k p;
  assert (injective_precond p (bytes_of_slice_from_to h1 s1 pos1 pos1') (bytes_of_slice_from_to h2 s2 pos2 pos2'));
  assert (injective_postcond p (bytes_of_slice_from_to h1 s1 pos1 pos1') (bytes_of_slice_from_to h2 s2 pos2 pos2'))

let valid_ext_intro
  (#rrel1 #rel1: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h1: HS.mem)
  (s1: slice rrel1 rel1)
  (pos1: U32.t)
  (h2: HS.mem)
  (#rrel2 #rel2: _)
  (s2: slice rrel2 rel2)
  (pos2: U32.t)
: Lemma
  (requires (
    valid p h1 s1 pos1 /\
    k.parser_kind_subkind == Some ParserStrong /\ (
    let pos1' = get_valid_pos p h1 s1 pos1 in
    live_slice h2 s2 /\
    U32.v pos2 + (U32.v pos1' - U32.v pos1) <= U32.v s2.len /\ (
    let pos2' = pos2 `U32.add` (pos1' `U32.sub` pos1) in
    bytes_of_slice_from_to h1 s1 pos1 pos1' `Seq.equal` bytes_of_slice_from_to h2 s2 pos2 pos2'
  ))))
  (ensures (
    valid_content_pos p h2 s2 pos2 (contents p h1 s1 pos1) (pos2 `U32.add` (get_valid_pos p h1 s1 pos1 `U32.sub` pos1))
  ))
= let pos1' = get_valid_pos p h1 s1 pos1 in
  let pos2' = pos2 `U32.add` (pos1' `U32.sub` pos1) in
  valid_pos_valid_exact p h1 s1 pos1 pos1' ;
  valid_exact_ext_intro p h1 s1 pos1 pos1' h2 s2 pos2 pos2' ;
  valid_exact_valid p h2 s2 pos2 pos2'

let valid_ext_elim
  (#rrel1 #rel1: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h1: HS.mem)
  (s1: slice rrel1 rel1)
  (pos1: U32.t)
  (h2: HS.mem)
  (#rrel2 #rel2: _)
  (s2: slice rrel2 rel2)
  (pos2: U32.t)
: Lemma
  (requires (
    valid p h1 s1 pos1 /\
    valid p h2 s2 pos2 /\
    k.parser_kind_subkind == Some ParserStrong /\
    contents p h1 s1 pos1 == contents p h2 s2 pos2
  ))
  (ensures (
    let pos1' = get_valid_pos p h1 s1 pos1 in
    let pos2' = get_valid_pos p h2 s2 pos2 in
    U32.v pos2' - U32.v pos2 == U32.v pos1' - U32.v pos1 /\
    bytes_of_slice_from_to h1 s1 pos1 pos1' == bytes_of_slice_from_to h2 s2 pos2 pos2'
  ))
= let pos1' = get_valid_pos p h1 s1 pos1 in
  let pos2' = get_valid_pos p h2 s2 pos2 in
  valid_valid_exact p h1 s1 pos1;
  valid_valid_exact p h2 s2 pos2;
  valid_exact_ext_elim p h1 s1 pos1 pos1' h2 s2 pos2 pos2'


(* Accessors for reading only (no in-place serialization yet) *)

noeq
type clens (t1: Type) (t2: Type) = {
  clens_cond: t1 -> GTot Type0;
  clens_get: (x1: t1) -> Ghost t2 (requires (clens_cond x1)) (ensures (fun _ -> True));
(*  
  clens_put: (x1: t1) -> t2 -> Ghost t1 (requires (clens_cond x1)) (ensures (fun x1' -> clens_cond x1'));
  clens_get_put: (x1: t1) -> (x2: t2) -> Lemma (requires (clens_cond x1)) (ensures (clens_get (clens_put x1 x2) == x2));
  clens_put_put: (x1: t1) -> (x2: t2) -> (x2' : t2) -> Lemma (requires (clens_cond x1)) (ensures (clens_put (clens_put x1 x2) x2' == clens_put x1 x2'));
  clens_put_get: (x1: t1) -> Lemma (requires (clens_cond x1)) (ensures (clens_put x1 (clens_get x1) == x1));
*)
}

let clens_id (t: Type) : Tot (clens t t) = {
  clens_cond = (fun _ -> True);
  clens_get = (fun x -> x);
}

let clens_eq (#t: Type) (#t': Type) (cl1: clens t t') (cl2: clens t t') : GTot Type0 =
  (forall (x: t) . {:pattern (cl1.clens_cond x) \/ (cl2.clens_cond x)} cl1.clens_cond x <==> cl2.clens_cond x) /\
  (forall (x: t) . {:pattern (cl1.clens_get x) \/ (cl2.clens_get x)} (cl1.clens_cond x \/ cl2.clens_cond x) ==> (cl1.clens_get x == cl2.clens_get x))

let clens_eq_intro
  (#t: Type) (#t': Type) (cl1: clens t t') (cl2: clens t t')
  (cond: (
    (x: t) ->
    Lemma
    (cl1.clens_cond x <==> cl2.clens_cond x)
  ))
  (get: (
    (x: t) ->
    Lemma
    (requires (cl1.clens_cond x /\ cl2.clens_cond x))
    (ensures (cl1.clens_cond x /\ cl2.clens_cond x /\ cl1.clens_get x == cl2.clens_get x))
  ))
: Lemma
  (clens_eq cl1 cl2)
= Classical.forall_intro cond;
  Classical.forall_intro (Classical.move_requires get)

let clens_eq_intro'
  (#t: Type) (#t': Type) (cl1: clens t t') (cl2: clens t t')
  (cond: (
    (x: t) ->
    Tot (squash (cl1.clens_cond x <==> cl2.clens_cond x))
  ))
  (get: (
    (x: t) ->
    (sq: squash (cl1.clens_cond x /\ cl2.clens_cond x)) ->
    Tot (squash (cl1.clens_cond x /\ cl2.clens_cond x /\ cl1.clens_get x == cl2.clens_get x))
  ))
: Tot (squash (clens_eq cl1 cl2))
= clens_eq_intro cl1 cl2 (fun x -> cond x) (fun x -> get x ())
 

(*
let clens_get_put'
  (#t1: Type) (#clens_cond: t1 -> GTot Type0) (#t2: Type) (l: clens clens_cond t2)
  (x1: t1) (x2: t2)
: Lemma
  (requires (clens_cond x1))
  (ensures (l.clens_get (l.clens_put x1 x2) == x2))
  [SMTPat (l.clens_get (l.clens_put x1 x2))]
= l.clens_get_put x1 x2

let clens_put_put'
  (#t1: Type) (#clens_cond: t1 -> GTot Type0) (#t2: Type) (l: clens clens_cond t2)
  (x1: t1) (x2: t2) (x2' : t2)
: Lemma
  (requires (clens_cond x1))
  (ensures (l.clens_put (l.clens_put x1 x2) x2' == l.clens_put x1 x2'))
  [SMTPat (l.clens_put (l.clens_put x1 x2) x2')]
= l.clens_put_put x1 x2 x2'

let clens_put_get'
  (#t1: Type) (#clens_cond: t1 -> GTot Type0) (#t2: Type) (l: clens clens_cond t2)
  (x1: t1)
: Lemma
  (requires (clens_cond x1))
  (ensures (l.clens_put x1 (l.clens_get x1) == x1))
  [SMTPat (l.clens_put x1 (l.clens_get x1))]
= l.clens_put_get x1

abstract
let clens_disjoint_l
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
: GTot Type0
= (forall (x0: t0) (x2: t2) . (clens_cond2 x0 /\ clens_cond3 x0) ==> 
  (let x0' = l2.clens_put x0 x2 in clens_cond3 x0' /\ l3.clens_get x0' == l3.clens_get x0))

abstract
let clens_disjoint_l_elim
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
  (x0: t0) (x2: t2)
: Lemma
  (requires (clens_disjoint_l l2 l3 /\ clens_cond2 x0 /\ clens_cond3 x0))
  (ensures (let x0' = l2.clens_put x0 x2 in clens_cond3 x0' /\ l3.clens_get x0' == l3.clens_get x0))
  [SMTPat (l3.clens_get (l2.clens_put x0 x2))]
= ()

abstract
let clens_disjoint_l_intro
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
  (lem: (
    (x0: t0) ->
    (x2: t2) ->
    Lemma
    (requires (clens_cond2 x0 /\ clens_cond3 x0))
    (ensures (clens_cond2 x0 /\ clens_cond3 x0 /\ (let x0' = l2.clens_put x0 x2 in clens_cond3 x0' /\ l3.clens_get x0' == l3.clens_get x0)))
  ))
: Lemma
  (clens_disjoint_l l2 l3)
= let lem'
    (x0: t0)
    (x2: t2)
  : Lemma
    ((clens_cond2 x0 /\ clens_cond3 x0) ==>
    (ensures (clens_cond2 x0 /\ clens_cond3 x0 /\ (let x0' = l2.clens_put x0 x2 in clens_cond3 x0' /\ l3.clens_get x0' == l3.clens_get x0))))
  = Classical.move_requires (lem x0) x2
  in
  Classical.forall_intro_2 lem'

let clens_disjoint
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
: GTot Type0
= clens_disjoint_l l2 l3 /\ clens_disjoint_l l3 l2

let clens_disjoint_sym
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
: Lemma
  (clens_disjoint l2 l3 <==> clens_disjoint l3 l2)
  [SMTPat (clens_disjoint l2 l3)]
= ()
*)

let clens_compose_cond
  (#t1: Type)
  (#t2: Type)
  (l12: clens t1 t2)
  (clens_cond2: t2 -> GTot Type0)
  (x1: t1)
: GTot Type0
= l12.clens_cond x1 /\
  clens_cond2 (l12.clens_get x1)

let clens_compose
  (#t1: Type)
  (#t2: Type)
  (#t3: Type)
  (l12: clens t1 t2)
  (l23: clens t2 t3)
: Tot (clens t1 t3)
= {
  clens_cond = (clens_compose_cond l12 l23.clens_cond);
  clens_get = (fun x1 -> l23.clens_get (l12.clens_get x1));
(*  
  clens_put = (fun x1 x3 ->
    let x2' = l23.clens_put (l12.clens_get x1) x3 in
    let x1' = l12.clens_put x1 x2' in
    x1'
  );
  clens_get_put = (fun x1 x3 -> ());
  clens_put_put = (fun x1 x3 x3' -> ());
  clens_put_get = (fun x1 -> ());
*)
}

let clens_compose_strong_pre
  (#t1: Type)
  (#t2: Type)
  (#t3: Type)
  (l12: clens t1 t2)
  (l23: clens t2 t3)
: GTot Type0
= forall (x: t1) . {:pattern (l12.clens_cond x) \/ (l23.clens_cond (l12.clens_get x))} l12.clens_cond x ==> l23.clens_cond (l12.clens_get x)

let clens_compose_strong
  (#t1: Type)
  (#t2: Type)
  (#t3: Type)
  (l12: clens t1 t2)
  (l23: clens t2 t3 { clens_compose_strong_pre l12 l23 })
: Tot (clens t1 t3)
= {
  clens_cond = l12.clens_cond;
  clens_get = (fun x1 -> l23.clens_get (l12.clens_get x1));
}

(*
abstract
let clens_disjoint_compose
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
  (#clens_cond3': t3 -> GTot Type0)
  (#t3' : Type)
  (l3' : clens clens_cond3' t3')
: Lemma
  (requires (clens_disjoint l2 l3))
  (ensures (clens_disjoint l2 (clens_compose l3 l3')))
  [SMTPat (clens_disjoint l2 (clens_compose l3 l3'))]
= ()
*)

let gaccessor_pre
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (cl: clens t1 t2)
  (sl: bytes)
: GTot Type0
= match parse p1 sl with
  | Some (x1, _) -> cl.clens_cond x1
  | _ -> False

let gaccessor_post
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (cl: clens t1 t2)
  (sl: bytes)
  (res : nat)
: GTot Type0
= res <= Seq.length sl /\
  begin match parse p1 sl with
  | Some (x1, consumed1) ->
    begin match parse p2 (Seq.slice sl res (Seq.length sl)) with
    | Some (x2, consumed2) ->
      cl.clens_cond x1 /\
      x2 == cl.clens_get x1 /\
      res + consumed2 <= consumed1
    | _ -> False
    end
  | _ -> False
  end

let gaccessor_post' 
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (cl: clens t1 t2)
  (sl : bytes)
  (res: nat)
: GTot Type0
= 
    res <= Seq.length sl /\
    (gaccessor_pre p1 p2 cl sl ==> gaccessor_post p1 p2 cl sl res)

let gaccessor'
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (cl: clens t1 t2)
: Tot Type
= (sl: bytes) ->
  Ghost (nat)
  (requires True)
  (ensures (fun res ->
    gaccessor_post' p1 p2 cl sl res
  ))

let gaccessor_no_lookahead
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (f: gaccessor' p1 p2 cl)
= (k1.parser_kind_subkind == Some ParserStrong ==> (forall (sl sl' : bytes) . {:pattern (f sl); (f sl')} (gaccessor_pre p1 p2 cl sl /\ gaccessor_pre p1 p2 cl sl' /\ no_lookahead_on_precond p1 sl sl') ==> f sl == f sl'))

let gaccessor_no_lookahead_weaken
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (f: gaccessor' p1 p2 cl)
  (sl sl' : bytes)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    gaccessor_pre p1 p2 cl sl /\
    no_lookahead_on_precond p1 sl sl'
  ))
  (ensures (gaccessor_pre p1 p2 cl sl'))
= parse_strong_prefix p1 sl sl'

let gaccessor_injective
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (f: gaccessor' p1 p2 cl)
= (forall (sl sl' : bytes) . {:pattern (f sl); (f sl')} (gaccessor_pre p1 p2 cl sl /\ gaccessor_pre p1 p2 cl sl' /\ injective_precond p1 sl sl') ==> f sl == f sl')

let gaccessor_prop'
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (f: gaccessor' p1 p2 cl)
: GTot Type0
= gaccessor_no_lookahead f /\ gaccessor_injective f

val gaccessor_prop
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (f: gaccessor' p1 p2 cl)
: GTot Type0

val gaccessor_prop_equiv
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (cl: clens t1 t2)
  (f: gaccessor' p1 p2 cl)
: Lemma
  (gaccessor_prop f <==> gaccessor_prop' f)

[@unifier_hint_injective]
let gaccessor
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (cl: clens t1 t2)
: Tot Type
= (f: gaccessor' p1 p2 cl { gaccessor_prop f })

let get_gaccessor_clens
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
: Tot (clens t1 t2)
= cl

(*
abstract
let gaccessors_disjoint
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl2: clens t1 t2)
  (g2: gaccessor p1 p2 cl2)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl3: clens t1 t3)
  (g3: gaccessor p1 p3 cl3)
: GTot Type0
= // clens_disjoint cl2 cl3 /\
  (forall (sl: bytes) . (
     match parse p1 sl with
     | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
     | _ -> False
   ) ==> (
   let (pos2, consumed2) = g2 sl in
   let (pos3, consumed3) = g3 sl in
   pos2 + consumed2 <= pos3 \/ pos3 + consumed3 <= pos2
  ))
*)

(*
abstract
let gaccessors_disjoint_clens_disjoint
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#pre2: t1 -> GTot Type0)
  (#cl2: clens pre2 t2)
  (g2: gaccessor p1 p2 cl2)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#pre3: t1 -> GTot Type0)
  (#cl3: clens pre3 t3)
  (g3: gaccessor p1 p3 cl3)
: Lemma
  (requires (gaccessors_disjoint g2 g3))
  (ensures (clens_disjoint cl2 cl3))
  [SMTPat (gaccessors_disjoint g2 g3)]
= ()
*)

(*
abstract
let gaccessors_disjoint_elim
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl2: clens t1 t2)
  (g2: gaccessor p1 p2 cl2)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl3: clens t1 t3)
  (g3: gaccessor p1 p3 cl3)
  (sl: bytes)
: Lemma
  (requires (gaccessors_disjoint g2 g3 /\ (
     match parse p1 sl with
     | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
     | _ -> False
  )))
  (ensures (
    let (pos2, consumed2) = g2 sl in
    let (pos3, consumed3) = g3 sl in
    pos2 + consumed2 <= pos3 \/ pos3 + consumed3 <= pos2
  ))
= ()

abstract
let gaccessors_disjoint_intro
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl2: clens t1 t2)
  (g2: gaccessor p1 p2 cl2)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl3: clens t1 t3)
  (g3: gaccessor p1 p3 cl3)
//  (clens_disj: squash (clens_disjoint cl2 cl3))
  (lem: (
    (sl: bytes) ->
    Lemma
    (requires (
      match parse p1 sl with
      | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
      | _ -> False
    ))
    (ensures ((
      match parse p1 sl with
      | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
      | _ -> False) /\ (
      let (pos2, consumed2) = g2 sl in
      let (pos3, consumed3) = g3 sl in
      pos2 + consumed2 <= pos3 \/ pos3 + consumed3 <= pos2
    )))
  ))
: Lemma
  (gaccessors_disjoint g2 g3)
= let lem'
   (sl: bytes)
 : Lemma
   ((
     match parse p1 sl with
     | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
     | _ -> False
   ) ==> (
   let (pos2, consumed2) = g2 sl in
   let (pos3, consumed3) = g3 sl in
   pos2 + consumed2 <= pos3 \/ pos3 + consumed3 <= pos2
   ))
 = Classical.move_requires lem sl
 in
 Classical.forall_intro lem'
*)

let gaccessor_id'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Ghost (nat)
  (requires True)
  (ensures (fun res -> gaccessor_post' p p (clens_id _) input res))
= 0

val gaccessor_id
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (gaccessor p p (clens_id _))

val gaccessor_id_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Lemma
  (gaccessor_id p input == gaccessor_id' p input)

let gaccessor_ext'
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
  (input: bytes)
: Ghost (nat) (requires True) (ensures (fun res -> gaccessor_post' p1 p2 cl' input res))
= g input

val gaccessor_ext
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
: Tot (gaccessor p1 p2 cl')

val gaccessor_ext_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
  (input: bytes)
: Lemma
  (gaccessor_ext g cl' sq input == gaccessor_ext' g cl' sq input)

let gaccessor_compose'
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (a12: gaccessor p1 p2 cl12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (a23: gaccessor p2 p3 cl23)
  (input: bytes)
: Ghost (nat) (requires True) (ensures (fun res -> gaccessor_post' p1 p3 (clens_compose cl12 cl23) input res))
= let pos2 = a12 input in
  let input2 = Seq.slice input pos2 (Seq.length input) in
  let pos3 = a23 input2 in
  pos2 + pos3

val gaccessor_compose_injective
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (a12: gaccessor p1 p2 cl12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (a23: gaccessor p2 p3 cl23)
  (sl sl': bytes)
: Lemma
  (requires (gaccessor_pre p1 p3 (clens_compose cl12 cl23) sl /\ gaccessor_pre p1 p3 (clens_compose cl12 cl23) sl' /\ injective_precond p1 sl sl'))
  (ensures (gaccessor_compose' a12 a23 sl == gaccessor_compose' a12 a23 sl'))

val gaccessor_compose_no_lookahead
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (a12: gaccessor p1 p2 cl12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (a23: gaccessor p2 p3 cl23)
  (sl sl': bytes)
: Lemma
  (requires (k1.parser_kind_subkind == Some ParserStrong /\ gaccessor_pre p1 p3 (clens_compose cl12 cl23) sl /\ gaccessor_pre p1 p3 (clens_compose cl12 cl23) sl' /\ no_lookahead_on_precond p1 sl sl'))
  (ensures (gaccessor_compose' a12 a23 sl == gaccessor_compose' a12 a23 sl'))

val gaccessor_compose
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (a12: gaccessor p1 p2 cl12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (a23: gaccessor p2 p3 cl23)
: Tot (gaccessor p1 p3 (clens_compose cl12 cl23))

val gaccessor_compose_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (a12: gaccessor p1 p2 cl12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (a23: gaccessor p2 p3 cl23)
  (input: bytes)
: Lemma
  (gaccessor_compose a12 a23 input == gaccessor_compose' a12 a23 input)

(*
abstract
let gaccessor_compose_strong
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (a12: gaccessor p1 p2 cl12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (a23: gaccessor p2 p3 cl23 { clens_compose_strong_pre cl12 cl23 } )
: Tot (gaccessor p1 p3 (clens_compose_strong cl12 cl23))
= gaccessor_compose' a12 a23

abstract
let gaccessor_compose_strong_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (a12: gaccessor p1 p2 cl12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (a23: gaccessor p2 p3 cl23 { clens_compose_strong_pre cl12 cl23 } )
  (input: bytes)
: Lemma
  (gaccessor_compose_strong a12 a23 input == gaccessor_compose' a12 a23 input)
= ()
*)

let slice_access'
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice rrel rel)
  (pos: U32.t)
: Ghost U32.t
  (requires (
    valid p1 h sl pos
  ))
  (ensures (fun pos' -> True))
=
  let small = bytes_of_slice_from h sl pos in
  pos `U32.add` U32.uint_to_t (g small)

val slice_access
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice rrel rel)
  (pos: U32.t)
: Ghost U32.t
  (requires (
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos)
  ))
  (ensures (fun pos' -> True))

val slice_access_eq
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos)
  ))
  (ensures (
    valid' p1 h sl pos /\
    cl.clens_cond (contents' p1 h sl pos) /\
    slice_access h g sl pos == slice_access' h g sl pos
  ))

let slice_access_post
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos)
  ))
  (ensures (
    let pos' = slice_access h g sl pos in
    valid p2 h sl pos' /\
    contents p2 h sl pos' == cl.clens_get (contents p1 h sl pos) /\
    // useful for framing
    U32.v pos <= U32.v pos' /\
    U32.v pos' + content_length p2 h sl pos' <= U32.v pos + content_length p1 h sl pos
  ))
  [SMTPat (slice_access h g sl pos)]
= slice_access_eq h g sl pos;
  valid_facts p1 h sl pos;
  assert_norm (pow2 32 == 4294967296);
  let res = slice_access' h g sl pos in
  valid_facts p2 h sl res

let slice_access_frame_weak
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice rrel rel)
  (pos: U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos) /\
    B.modifies l h h' /\
    B.loc_disjoint l (loc_slice_from sl pos)
  ))
  (ensures (
    valid p1 h' sl pos /\
    cl.clens_cond (contents p1 h' sl pos) /\
    slice_access h' g sl pos == slice_access h g sl pos
  ))
  [SMTPatOr [
    [SMTPat (slice_access h g sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (slice_access h' g sl pos); SMTPat (B.modifies l h h')];
  ]]
= valid_facts p1 h sl pos;
  valid_facts p1 h' sl pos;
  slice_access_eq h g sl pos;
  slice_access_eq h' g sl pos;
  B.modifies_buffer_from_to_elim sl.base pos sl.len l h h'

val slice_access_frame_strong
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice rrel rel)
  (pos: U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos) /\
    B.modifies l h h' /\
    B.loc_disjoint l (loc_slice_from_to sl pos (get_valid_pos p1 h sl pos))
  ))
  (ensures (
    valid p1 h' sl pos /\
    cl.clens_cond (contents p1 h' sl pos) /\
    slice_access h' g sl pos == slice_access h g sl pos
  ))
  [SMTPatOr [
    [SMTPat (slice_access h g sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (slice_access h' g sl pos); SMTPat (B.modifies l h h')];
  ]]


(* lists, to avoid putting LowParse.*.List into the user context *)

val valid_list
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0
  (decreases (U32.v pos' - U32.v pos))

val valid_list_equiv
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (valid_list p h sl pos pos' <==> (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    live_slice h sl /\
    U32.v pos' <= U32.v sl.len /\ (
    if pos = pos'
    then True
    else
      valid p h sl pos /\ (
      let pos1 = get_valid_pos p h sl pos in
      U32.v pos1 <= U32.v pos' /\
      valid_list p h sl pos1 pos'
  ))))

let valid_list_elim
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_list p h sl pos pos'))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    live_slice h sl /\
    U32.v pos <= U32.v pos' /\
    U32.v pos' <= U32.v sl.len
  ))
  [SMTPat (valid_list p h sl pos pos')]
= valid_list_equiv p h sl pos pos'

val contents_list
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost (list t)
  (requires (valid_list p h sl pos pos'))
  (ensures (fun _ -> True))
  (decreases (U32.v pos' - U32.v pos))

val contents_list_eq
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_list p h sl pos pos'))
  (ensures (contents_list p h sl pos pos' == (
    valid_list_equiv p h sl pos pos';
    if pos = pos'
    then []
    else
      contents p h sl pos :: contents_list p h sl (get_valid_pos p h sl pos) pos'
  )))

let valid_list_nil
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos : U32.t)
: Lemma
  (requires (U32.v pos <= U32.v sl.len /\ live_slice h sl /\ k.parser_kind_low > 0 /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_list p h sl pos pos /\
    contents_list p h sl pos pos == []
  ))
= valid_list_equiv p h sl pos pos;
  contents_list_eq p h sl pos pos

let valid_list_cons
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    valid p h sl pos /\
    valid_list p h sl (get_valid_pos p h sl pos) pos'
  ))
  (ensures (
    valid p h sl pos /\
    valid_list p h sl (get_valid_pos p h sl pos) pos' /\
    valid_list p h sl pos pos' /\
    contents_list p h sl pos pos' == contents p h sl pos :: contents_list p h sl (get_valid_pos p h sl pos) pos'
  ))
= valid_list_equiv p h sl pos pos' ;
  contents_list_eq p h sl pos pos'

module L = FStar.List.Tot

let valid_list_cons_recip
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    pos <> pos' /\
    valid_list p h sl pos pos'
  ))
  (ensures (
    pos <> pos' /\
    valid_list p h sl pos pos' /\
    valid p h sl pos /\ (
    let pos1 = get_valid_pos p h sl pos in
    valid_list p h sl pos1 pos' /\
    contents_list p h sl pos pos' == contents p h sl pos :: contents_list p h sl pos1 pos'
  )))
= valid_list_equiv p h sl pos pos' ;
  contents_list_eq p h sl pos pos'

let rec valid_list_frame_1
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (B.modifies l h h' /\ B.loc_disjoint l (loc_slice_from_to s pos pos') /\ valid_list p h s pos pos'))
  (ensures (
    valid_list p h s pos pos' /\ valid_list p h' s pos pos' /\ contents_list p h' s pos pos' == contents_list p h s pos pos'
  ))
  (decreases (U32.v pos' - U32.v pos))
= valid_list_equiv p h s pos pos';
  contents_list_eq p h s pos pos' ;
  valid_list_equiv p h' s pos pos' ;
  begin if pos = pos'
  then ()
  else begin
    let pos1 = get_valid_pos p h s pos in
    valid_list_frame_1 p h s pos1 pos' l h'
  end end;
  B.modifies_buffer_from_to_elim s.base pos pos' l h h';
  contents_list_eq p h' s pos pos'

let rec valid_list_frame_2
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (live_slice h s /\ B.modifies l h h' /\ B.loc_disjoint l (loc_slice_from_to s pos pos') /\ valid_list p h' s pos pos'))
  (ensures (
    valid_list p h' s pos pos' /\ valid_list p h s pos pos' /\ contents_list p h' s pos pos' == contents_list p h s pos pos'
  ))
  (decreases (U32.v pos' - U32.v pos))
= valid_list_equiv p h' s pos pos' ;
  contents_list_eq p h' s pos pos' ;
  valid_list_equiv p h s pos pos' ;
  if pos = pos'
  then ()
  else begin
    let pos1 = get_valid_pos p h' s pos in
    valid_valid_exact p h' s pos;
    valid_exact_valid p h s pos pos1;
    valid_list_frame_2 p h s pos1 pos' l h'
  end;
  B.modifies_buffer_from_to_elim s.base pos pos' l h h';
  contents_list_eq p h s pos pos'

let valid_list_frame
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (live_slice h s /\ B.modifies l h h' /\ B.loc_disjoint l (loc_slice_from_to s pos pos')))
  (ensures (
    (valid_list p h s pos pos' \/ valid_list p h' s pos pos') ==> (
    valid_list p h s pos pos' /\
    valid_list p h' s pos pos' /\ contents_list p h' s pos pos' == contents_list p h s pos pos'
  )))
  [SMTPatOr [
    [SMTPat (valid_list p h s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (valid_list p h' s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (contents_list p h s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (contents_list p h' s pos pos'); SMTPat (B.modifies l h h')];
  ]]
= Classical.move_requires (valid_list_frame_1 p h s pos pos' l) h';
  Classical.move_requires (valid_list_frame_2 p h s pos pos' l) h'

let rec valid_list_append
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos1 pos2 pos3 : U32.t)
: Lemma
  (requires (
    valid_list p h sl pos1 pos2 /\
    valid_list p h sl pos2 pos3
  ))
  (ensures (
    valid_list p h sl pos1 pos3 /\
    contents_list p h sl pos1 pos3 == contents_list p h sl pos1 pos2 `L.append` contents_list p h sl pos2 pos3
  ))
  (decreases (U32.v pos2 - U32.v pos1))
= if pos1 = pos2
  then
    valid_list_nil p h sl pos1
  else begin
    valid_list_cons_recip p h sl pos1 pos2;
    let pos15 = get_valid_pos p h sl pos1 in
    valid_list_append p h sl pos15 pos2 pos3;
    valid_list_cons p h sl pos1 pos3
  end

let valid_list_snoc
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice rrel rel)
  (pos1 pos2 : U32.t)
: Lemma
  (requires (
    valid_list p h sl pos1 pos2 /\
    valid p h sl pos2
  ))
  (ensures (
    let pos3 = get_valid_pos p h sl pos2 in
    valid_list p h sl pos1 pos3 /\
    contents_list p h sl pos1 pos3 == contents_list p h sl pos1 pos2 `L.append` [contents p h sl pos2]
  ))
= let pos3 = get_valid_pos p h sl pos2 in
  valid_list_nil p h sl pos3;
  valid_list_cons p h sl pos2 pos3;
  valid_list_append p h sl pos1 pos2 pos3

(* size of a list of serialized data (should be taken from serialize_list) *)

val serialized_list_length (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (l: list t) : GTot nat

val serialized_list_length_nil (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) : Lemma
  (serialized_list_length s [] == 0)

val serialized_list_length_cons (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (x: t) (q: list t) : Lemma
  (serialized_list_length s (x :: q) == serialized_length s x + serialized_list_length s q)

val serialized_list_length_append (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (l1 l2: list t) : Lemma
  (serialized_list_length s (List.Tot.append l1 l2) == serialized_list_length s l1 + serialized_list_length s l2)

val valid_list_serialized_list_length (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (h: HS.mem) (#rrel #rel: _) (input: slice rrel rel) (pos pos' : U32.t) : Lemma
  (requires (
    valid_list p h input pos pos'
  ))
  (ensures (
    serialized_list_length s (contents_list p h input pos pos') == U32.v pos' - U32.v pos
  ))
  (decreases (U32.v pos' - U32.v pos))

val serialized_list_length_constant_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_high == Some k.parser_kind_low})
  (l: list t)
: Lemma
  (ensures (
    serialized_list_length s l == L.length l `Prims.op_Multiply` k.parser_kind_low
  ))

let list_length_append (#t: Type) (l1 l2: list t) : Lemma (L.length (l1 `L.append` l2) == L.length l1 + L.length l2) = L.append_length l1 l2

val list_flatten_append
  (#a: Type)
  (l1 l2: list (list a))
: Lemma
  (L.flatten (l1 `L.append` l2) == L.flatten l1 `L.append` L.flatten l2)

val list_filter_append
  (#t: Type)
  (f: (t -> Tot bool))
  (l1 l2: list t)
: Lemma
  (L.filter f (l1 `L.append` l2) == L.filter f l1 `L.append` L.filter f l2)

val list_index_append (#t: Type) (l1 l2: list t) (i: int) : Lemma
  (requires (L.length l1 <= i /\ i < L.length l1 + L.length l2))
  (ensures (
    L.length (L.append l1 l2) == L.length l1 + L.length l2 /\
    L.index (L.append l1 l2) i == L.index l2 (i - L.length l1)
  ))

val list_flatten_map_append
  (#a #b: Type)
  (f: a -> Tot (list b))
  (l1 l2: list a)
: Lemma
  (L.flatten (L.map f (l1 `L.append` l2)) == L.flatten (L.map f l1) `L.append` L.flatten (L.map f l2))

val list_map_list_flatten_map
  (#a #b: Type)
  (f: a -> Tot b)
  (l: list a)
: Lemma
  (L.map f l == L.flatten (L.map (fun x -> [f x]) l))

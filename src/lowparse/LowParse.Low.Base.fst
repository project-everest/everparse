module LowParse.Low.Base
include LowParse.Spec.Base

module B = LowStar.Buffer
module M = LowStar.ModifiesPat
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

inline_for_extraction
type buffer8 = B.buffer FStar.UInt8.t

noeq
type slice = {
  base: buffer8;
  len: (len: U32.t { len == B.len base } );
}

let live_slice (h: HS.mem) (s: slice) : GTot Type0 = B.live h s.base

let buffer_of_slice_from (s: slice) (pos: U32.t) : Ghost buffer8 (requires (U32.v pos <= U32.v s.len)) (ensures (fun _ -> True)) =
  B.gsub s.base pos (s.len `U32.sub` pos)

let bytes_of_slice_from (h: HS.mem) (s: slice) (pos: U32.t) : Ghost bytes (requires  (U32.v pos <= U32.v s.len)) (ensures (fun _ -> True)) =
  B.as_seq h (buffer_of_slice_from s pos)

private
let loc_slice_from' (s: slice) (pos: U32.t) : GTot B.loc =
  if U32.v pos <= U32.v s.len
  then B.loc_buffer (B.gsub s.base pos (s.len `U32.sub` pos))
  else B.loc_none

[@"opaque_to_smt"]
abstract
let loc_slice_from (s: slice) (pos: U32.t) : GTot B.loc =
  loc_slice_from' s pos

abstract
private
let loc_slice_from_eq_gen (s: slice) (pos: U32.t) : Lemma
  (loc_slice_from s pos == loc_slice_from' s pos)
= assert_norm (loc_slice_from s pos == loc_slice_from' s pos)

abstract
let loc_slice_from_includes_intro (s: slice) (pos: U32.t) : Lemma
  (B.loc_includes (B.loc_buffer s.base) (loc_slice_from s pos))
  [SMTPat (loc_slice_from s pos)]
= loc_slice_from_eq_gen s pos

abstract
let loc_includes_union_l_loc_slice_from (l1 l2: B.loc) (s: slice) (pos: U32.t) : Lemma
  (requires (B.loc_includes l1 (loc_slice_from s pos) \/ B.loc_includes l2 (loc_slice_from s pos)))
  (ensures (B.loc_includes (B.loc_union l1 l2) (loc_slice_from s pos)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (loc_slice_from s pos))]
= loc_slice_from_eq_gen s pos

abstract
let loc_slice_from_includes_buffer (b: buffer8) (s: slice) (pos: U32.t) : Lemma
  (requires (b == s.base))
  (ensures (B.loc_includes (B.loc_buffer b) (loc_slice_from s pos)))
  [SMTPat (B.loc_includes (B.loc_buffer b) (loc_slice_from s pos))]
= loc_slice_from_eq_gen s pos

abstract
let loc_slice_from_includes_gsub (s: slice) (pos: U32.t) (b: buffer8) (pos' len: U32.t) : Lemma
  (requires (b == s.base /\ U32.v pos <= U32.v pos' /\ U32.v pos' + U32.v len <= B.length b))
  (ensures (B.loc_includes (loc_slice_from s pos) (B.loc_buffer (B.gsub b pos' len))))
  [SMTPat (B.loc_includes (loc_slice_from s pos) (B.loc_buffer (B.gsub b pos' len)))]
= loc_slice_from_eq_gen s pos

abstract
let loc_slice_from_includes_addresses (r: HS.rid) (addrs: Set.set nat) (tg: bool) (s: slice) (pos: U32.t) : Lemma
  (requires (B.frameOf s.base == r /\ B.as_addr s.base `Set.mem` addrs))
  (ensures (B.loc_includes (B.loc_addresses tg r addrs) (loc_slice_from s pos)))
  [SMTPat (B.loc_includes (B.loc_addresses tg r addrs) (loc_slice_from s pos))]
= loc_slice_from_eq_gen s pos

abstract
let loc_slice_from_includes_regions (rs: Set.set HS.rid) (tg: bool) (s: slice) (pos: U32.t) : Lemma
  (requires (B.frameOf s.base `Set.mem` rs))
  (ensures (B.loc_includes (B.loc_regions tg rs) (loc_slice_from s pos)))
  [SMTPat (B.loc_includes (B.loc_regions tg rs) (loc_slice_from s pos))]
= loc_slice_from_eq_gen s pos

abstract
let loc_slice_from_eq
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (U32.v pos <= U32.v s.len))
  (ensures (loc_slice_from s pos == B.loc_buffer (B.gsub s.base pos (s.len `U32.sub` pos))))
= loc_slice_from_eq_gen s pos

abstract
let loc_slice_from_includes_l
  (s: slice)
  (pos1 pos2: U32.t)
: Lemma
  (requires (U32.v pos1 <= U32.v pos2))
  (ensures (B.loc_includes (loc_slice_from s pos1) (loc_slice_from s pos2)))
  [SMTPat (B.loc_includes (loc_slice_from s pos1) (loc_slice_from s pos2))]
= loc_slice_from_eq_gen s pos1;
  loc_slice_from_eq_gen s pos2

abstract
let loc_slice_from_gsub_disjoint
  (sl: slice)
  (b: buffer8)
  (pos pos' len: U32.t)
: Lemma
  (requires (b == sl.base /\ U32.v pos' + U32.v len <= B.length b /\ U32.v pos' + U32.v len <= U32.v pos))
  (ensures (B.loc_disjoint (loc_slice_from sl pos) (B.loc_buffer (B.gsub b pos' len))))
  [SMTPat (B.loc_disjoint (loc_slice_from sl pos) (B.loc_buffer (B.gsub b pos' len)))]
= loc_slice_from_eq_gen sl pos

let valid'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: GTot Type0
= U32.v pos <= U32.v s.len /\
  live_slice h s /\
  Some? (parse p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))))

[@"opaque_to_smt"]
abstract
let valid
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: GTot Type0
= valid' p h s pos

abstract
let valid_equiv
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Lemma
  (valid p h s pos <==> valid' p h s pos)
= assert_norm (valid p h s pos <==> valid' p h s pos)

abstract
let valid_dec
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Ghost bool
  (requires (live_slice h s))
  (ensures (fun b ->
    b == true <==> valid p h s pos
  ))
= valid_equiv p h s pos;
  (not (pos `U32.gt` s.len)) && Some? (parse p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))))

abstract
let valid_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos))
  (ensures (valid' p h s pos))
//  [SMTPat (valid p h s pos)]
= valid_equiv p h s pos

abstract
let valid_elim'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos))
  (ensures (U32.v pos + k.parser_kind_low <= U32.v s.len /\
  live_slice h s))
  [SMTPat (valid p h s pos)]
= parser_kind_prop_equiv k p;
  valid_equiv p h s pos

let contents'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Ghost t
  (requires (valid' p h s pos))
  (ensures (fun _ -> True))
= let Some (v, _) = parse p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))) in
  v

[@"opaque_to_smt"]
abstract
let contents
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Ghost t
  (requires (valid p h s pos))
  (ensures (fun _ -> True))
= valid_equiv p h s pos;
  contents' p h s pos

abstract
let contents_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos))
  (ensures (valid p h s pos /\ valid' p h s pos /\ contents p h s pos == contents' p h s pos))
= valid_equiv p h s pos;
  assert_norm (contents p h s pos == contents' p h s pos)

let content_length'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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
= let Some (_, consumed) = parse p (B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos))) in
  parser_kind_prop_equiv k p;
  consumed

[@"opaque_to_smt"]
abstract
let content_length
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
: Ghost nat
  (requires (valid p h sl pos))
  (ensures (fun res ->
    U32.v pos + res <= U32.v sl.len /\
    k.parser_kind_low <= res /\ (
    match k.parser_kind_high with
    | None -> True
    | Some max -> res <= max
  )))
= valid_equiv p h sl pos;
  content_length' p h sl pos

abstract
let serialized_length
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
= Seq.length (serialize s x)

abstract
let serialized_length_eq
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (serialized_length s x == Seq.length (serialize s x))
= ()

abstract
let content_length_eq_gen
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h sl pos))
  (ensures (valid p h sl pos /\ valid' p h sl pos /\ content_length p h sl pos == content_length' p h sl pos))
= valid_equiv p h sl pos;
  assert_norm (content_length p h sl pos == content_length' p h sl pos)

abstract
let valid_facts
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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

abstract
let content_length_eq
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h sl pos))
  (ensures (content_length p h sl pos == serialized_length s (contents p h sl pos)))
  [SMTPat (serialized_length s (contents p h sl pos))]
= parser_kind_prop_equiv k p;
  content_length_eq_gen p h sl pos;
  contents_eq p h sl pos;
  let b = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
  let Some (x, consumed) = parse p b in
  assert (x == contents p h sl pos);
  let ps' = parse p (serialize s x) in
  assert (serializer_correct p s);
  assert (Some? ps');
  assert (injective_precond p b (serialize s x))

let valid_pos
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (pos' : U32.t)
= valid p h sl pos /\
  U32.v pos + content_length p h sl pos == U32.v pos'

abstract
let get_valid_pos
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
: Ghost U32.t
  (requires (valid p h sl pos))
  (ensures (fun pos' -> valid_pos p h sl pos pos'))
= pos `U32.add` U32.uint_to_t (content_length p h sl pos)

abstract
let valid_pos_get_valid_pos
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_pos p h sl pos pos'))
  (ensures (get_valid_pos p h sl pos == pos'))
  [SMTPat (valid_pos p h sl pos pos'); SMTPat (get_valid_pos p h sl pos)]
= ()

let valid_content
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (x: t)
= valid p h sl pos /\
  contents p h sl pos == x

let valid_content_pos
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (x: t)
  (pos' : U32.t)
= valid_pos p h sl pos pos' /\
  valid_content p h sl pos x

abstract
let valid_frame
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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
= loc_slice_from_eq_gen sl pos;
  valid_facts p h sl pos;
  valid_facts p h' sl pos

(* Case where we do not have the strong prefix property (e.g. lists): we need an extra length *)

private
let loc_slice_from_to'
  (sl: slice)
  (pos pos' : U32.t)
: GTot B.loc
= if U32.v pos' > U32.v sl.len
  then loc_slice_from' sl pos
  else if U32.v pos > U32.v pos'
  then B.loc_none
  else B.loc_buffer (B.gsub sl.base pos (pos' `U32.sub` pos))

[@"opaque_to_smt"]
abstract
let loc_slice_from_to
  (sl: slice)
  (pos pos' : U32.t)
: GTot B.loc
= loc_slice_from_to' sl pos pos'

abstract
private
let loc_slice_from_to_eq_gen
  (sl: slice)
  (pos pos' : U32.t)
: Lemma
  (loc_slice_from_to sl pos pos' == loc_slice_from_to' sl pos pos')
= assert_norm (loc_slice_from_to sl pos pos' == loc_slice_from_to' sl pos pos')

abstract
let loc_slice_from_to_includes_intro (s: slice) (pos pos': U32.t) : Lemma
  (B.loc_includes (loc_slice_from s pos) (loc_slice_from_to s pos pos'))
  [SMTPat (loc_slice_from_to s pos pos')]
= loc_slice_from_eq_gen s pos;
  loc_slice_from_to_eq_gen s pos pos'

abstract
let loc_includes_union_l_loc_slice_from_to (l1 l2: B.loc) (s: slice) (pos pos' : U32.t) : Lemma
  (requires (B.loc_includes l1 (loc_slice_from_to s pos pos') \/ B.loc_includes l2 (loc_slice_from_to s pos pos')))
  (ensures (B.loc_includes (B.loc_union l1 l2) (loc_slice_from_to s pos pos')))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (loc_slice_from_to s pos pos'))]
= loc_slice_from_to_eq_gen s pos pos'

abstract
let loc_slice_from_to_includes_buffer (b: buffer8) (s: slice) (pos pos' : U32.t) : Lemma
  (requires (b == s.base))
  (ensures (B.loc_includes (B.loc_buffer b) (loc_slice_from_to s pos pos')))
  [SMTPat (B.loc_includes (B.loc_buffer b) (loc_slice_from_to s pos pos'))]
= loc_slice_from_to_eq_gen s pos pos'

abstract
let loc_slice_from_to_includes_addresses (r: HS.rid) (addrs: Set.set nat) (tg: bool) (s: slice) (pos pos' : U32.t) : Lemma
  (requires (B.frameOf s.base == r /\ B.as_addr s.base `Set.mem` addrs))
  (ensures (B.loc_includes (B.loc_addresses tg r addrs) (loc_slice_from_to s pos pos')))
  [SMTPat (B.loc_includes (B.loc_addresses tg r addrs) (loc_slice_from_to s pos pos'))]
= loc_slice_from_to_eq_gen s pos pos'

abstract
let loc_slice_from_to_includes_regions (rs: Set.set HS.rid) (tg: bool) (s: slice) (pos pos' : U32.t) : Lemma
  (requires (B.frameOf s.base `Set.mem` rs))
  (ensures (B.loc_includes (B.loc_regions tg rs) (loc_slice_from_to s pos pos')))
  [SMTPat (B.loc_includes (B.loc_regions tg rs) (loc_slice_from_to s pos pos'))]
= loc_slice_from_to_eq_gen s pos pos'

abstract
let loc_slice_from_to_includes_r
  (sl: slice)
  (pos0 pos pos' : U32.t)
: Lemma
  (requires (U32.v pos0 <= U32.v pos))
  (ensures (B.loc_includes (loc_slice_from sl pos0) (loc_slice_from_to sl pos pos')))
  [SMTPat (B.loc_includes (loc_slice_from sl pos0) (loc_slice_from_to sl pos pos'))]
= loc_slice_from_eq_gen sl pos0;
  loc_slice_from_to_eq_gen sl pos pos'

abstract
let loc_slice_from_to_eq
  (sl: slice)
  (pos pos' : U32.t)
: Lemma
  (requires (U32.v pos <= U32.v pos' /\ U32.v pos' <= U32.v sl.len))
  (ensures (loc_slice_from_to sl pos pos' == B.loc_buffer (B.gsub sl.base pos (pos' `U32.sub` pos))))
= loc_slice_from_to_eq_gen sl pos pos'

abstract
let loc_slice_from_to_includes_l
  (sl: slice)
  (posl posr posl' posr' : U32.t)
: Lemma
  (requires (U32.v posl <= U32.v posl' /\ U32.v posr' <= U32.v posr))
  (ensures (loc_slice_from_to sl posl posr `B.loc_includes` loc_slice_from_to sl posl' posr'))
  [SMTPat (loc_slice_from_to sl posl posr `B.loc_includes` loc_slice_from_to sl posl' posr')]
= loc_slice_from_to_eq_gen sl posl posr;
  loc_slice_from_to_eq_gen sl posl' posr'

abstract
let loc_slice_from_to_disjoint
  (sl: slice)
  (posl1 posr1 posl2 posr2 : U32.t)
: Lemma
  (requires (U32.v posr1 <= U32.v posl2))
  (ensures (B.loc_disjoint (loc_slice_from_to sl posl1 posr1) (loc_slice_from_to sl posl2 posr2)))
  [SMTPat (B.loc_disjoint (loc_slice_from_to sl posl1 posr1) (loc_slice_from_to sl posl2 posr2))]
= loc_slice_from_to_eq_gen sl posl1 posr1;
  loc_slice_from_to_eq_gen sl posl2 posr2

abstract
let loc_slice_from_to_gsub_disjoint
  (sl: slice)
  (b: buffer8)
  (pos1 pos2 pos' len: U32.t)
: Lemma
  (requires (b == sl.base /\ U32.v pos' + U32.v len <= B.length b /\ (U32.v pos' + U32.v len <= U32.v pos1 \/ U32.v pos2 <= U32.v pos')))
  (ensures (B.loc_disjoint (loc_slice_from_to sl pos1 pos2) (B.loc_buffer (B.gsub b pos' len))))
  [SMTPat (B.loc_disjoint (loc_slice_from_to sl pos1 pos2) (B.loc_buffer (B.gsub b pos' len)))]
= loc_slice_from_to_eq_gen sl pos1 pos2

abstract
let loc_slice_from_loc_slice_from_to_disjoint
  (sl: slice)
  (pos1 pos2 pos' : U32.t)
: Lemma
  (requires (U32.v pos2 <= U32.v pos'))
  (ensures (B.loc_disjoint (loc_slice_from_to sl pos1 pos2) (loc_slice_from sl pos')))
  [SMTPat (B.loc_disjoint (loc_slice_from_to sl pos1 pos2) (loc_slice_from sl pos'))]
= loc_slice_from_to_eq_gen sl pos1 pos2;
  loc_slice_from_eq_gen sl pos'

let valid_exact'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0
= U32.v pos <= U32.v pos' /\
  U32.v pos' <= U32.v s.len /\
  live_slice h s /\ (
  let len' = pos' `U32.sub` pos in
  match parse p (B.as_seq h (B.gsub s.base pos len')) with
  | None -> False
  | Some (_, consumed) -> (consumed <: nat) == U32.v len'
  )

[@"opaque_to_smt"]
abstract
let valid_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0
= valid_exact' p h s pos pos'

abstract
let valid_exact_equiv
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (valid_exact p h s pos pos' <==> valid_exact' p h s pos pos')
= assert_norm (valid_exact p h s pos pos' <==> valid_exact' p h s pos pos')

abstract
let valid_exact_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos'))
  (ensures (valid_exact' p h s pos pos'))
//  [SMTPat (valid_exact p h s pos pos')]
= valid_exact_equiv p h s pos pos'

abstract
let valid_exact_elim'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost t
  (requires (valid_exact' p h s pos pos'))
  (ensures (fun _ -> True))
= let (Some (v, _)) = parse p (B.as_seq h (B.gsub s.base pos (pos' `U32.sub` pos))) in
  v

[@"opaque_to_smt"]
abstract
let contents_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost t
  (requires (valid_exact p h s pos pos'))
  (ensures (fun _ -> True))
= valid_exact_equiv p h s pos pos' ;
  contents_exact' p h s pos pos'

abstract
let contents_exact_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos'))
  (ensures (valid_exact p h s pos pos' /\ valid_exact' p h s pos pos' /\ contents_exact p h s pos pos' == contents_exact' p h s pos pos'))
= valid_exact_equiv p h s pos pos' ;
  assert_norm (contents_exact p h s pos pos' == contents_exact' p h s pos pos')

abstract
let valid_exact_serialize
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h sl pos pos'))
  (ensures (
    serialize s (contents_exact p h sl pos pos') == B.as_seq h (B.gsub sl.base pos (pos' `U32.sub` pos)
  )))
= valid_exact_equiv p h sl pos pos' ;
  contents_exact_eq p h sl pos pos' ;
  serializer_correct_implies_complete p s;
  ()

abstract
let valid_exact_frame
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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
= valid_exact_equiv p h s pos pos' ;
  valid_exact_equiv p h' s pos pos' ;
  Classical.move_requires (contents_exact_eq p h s pos) pos' ;
  Classical.move_requires (contents_exact_eq p h' s pos) pos' ;
  loc_slice_from_to_eq_gen s pos pos'

abstract
let valid_valid_exact_consumes_all
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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

abstract
let valid_valid_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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
  parse_strong_prefix p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))) (B.as_seq h (B.gsub s.base pos (pos' `U32.sub` pos)))

abstract
let valid_pos_valid_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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

abstract
let valid_exact_valid
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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
  parse_strong_prefix p (B.as_seq h (B.gsub s.base pos (pos' `U32.sub`pos))) (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos)))

let valid_exact_valid_pat
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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

abstract
let valid_exact_ext_intro
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s1: slice)
  (pos1: U32.t)
  (pos1' : U32.t)
  (s2: slice)
  (pos2: U32.t)
  (pos2' : U32.t)
: Lemma
  (requires (
    valid_exact p h s1 pos1 pos1' /\
    live_slice h s2 /\
    U32.v pos1' - U32.v pos1 == U32.v pos2' - U32.v pos2 /\
    U32.v pos2' <= U32.v s2.len /\
    B.as_seq h (B.gsub s1.base pos1 (pos1' `U32.sub` pos1)) `Seq.equal` B.as_seq h (B.gsub s2.base pos2 (pos2' `U32.sub` pos2))
  ))
  (ensures (
    valid_exact p h s2 pos2 pos2' /\
    contents_exact p h s2 pos2 pos2' == contents_exact p h s1 pos1 pos1'
  ))
= valid_exact_equiv p h s1 pos1 pos1' ;
  valid_exact_equiv p h s2 pos2 pos2' ;
  contents_exact_eq p h s1 pos1 pos1' ;
  contents_exact_eq p h s2 pos2 pos2'

abstract
let valid_exact_ext_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s1: slice)
  (pos1: U32.t)
  (pos1' : U32.t)
  (s2: slice)
  (pos2: U32.t)
  (pos2' : U32.t)
: Lemma
  (requires (
    valid_exact p h s1 pos1 pos1' /\
    valid_exact p h s2 pos2 pos2' /\
    contents_exact p h s1 pos1 pos1' == contents_exact p h s2 pos2 pos2'
  ))
  (ensures (
    U32.v pos2' - U32.v pos2 == U32.v pos1' - U32.v pos1 /\
    B.as_seq h (B.gsub s1.base pos1 (pos1' `U32.sub` pos1)) == B.as_seq h (B.gsub s2.base pos2 (pos2' `U32.sub` pos2))
  ))
= valid_exact_equiv p h s1 pos1 pos1' ;
  valid_exact_equiv p h s2 pos2 pos2' ;
  contents_exact_eq p h s1 pos1 pos1' ;
  contents_exact_eq p h s2 pos2 pos2' ;
  parser_kind_prop_equiv k p;
  assert (injective_precond p (B.as_seq h (B.gsub s1.base pos1 (pos1' `U32.sub` pos1))) (B.as_seq h (B.gsub s2.base pos2 (pos2' `U32.sub` pos2))));
  assert (injective_postcond p (B.as_seq h (B.gsub s1.base pos1 (pos1' `U32.sub` pos1))) (B.as_seq h (B.gsub s2.base pos2 (pos2' `U32.sub` pos2))))

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
  | Some (x1, consumed) -> (consumed <: nat) == Seq.length sl /\ cl.clens_cond x1
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
  (res : nat & nat)
: GTot Type0
= let (pos', len) = res in
  pos' + len <= Seq.length sl /\
  begin match parse p1 sl with
  | Some (x1, consumed1) ->
    begin match parse p2 (Seq.slice sl pos' (pos' + len)) with
    | Some (x2, consumed2) ->
      cl.clens_cond x1 /\
      x2 == cl.clens_get x1 /\
      pos' + consumed2 <= consumed1 /\
      consumed2 == len
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
  (res: nat & nat)
: GTot Type0
= 
    let (pos', len') = res in pos' + len' <= Seq.length sl /\
    (gaccessor_pre p1 p2 cl sl ==> gaccessor_post p1 p2 cl sl res)

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
= (sl: bytes) ->
  Ghost (nat & nat)
  (requires True)
  (ensures (fun res ->
    gaccessor_post' p1 p2 cl sl res
  ))

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

let gaccessor_id'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Ghost (nat & nat)
  (requires True)
  (ensures (fun res -> gaccessor_post' p p (clens_id _) input res))
= (0, Seq.length input)

abstract
let gaccessor_id
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (gaccessor p p (clens_id _))
= gaccessor_id' p

abstract
let gaccessor_id_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Lemma
  (gaccessor_id p input == gaccessor_id' p input)
= ()

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
: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' p1 p2 cl' input res))
= g input

abstract
let gaccessor_ext
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
= gaccessor_ext' g cl' sq

abstract
let gaccessor_ext_eq
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
  (gaccessor_ext g cl sq input == gaccessor_ext' g cl sq input)
= ()

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
: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' p1 p3 (clens_compose cl12 cl23) input res))
= let (pos2, consumed2) = a12 input in
  let input2 = Seq.slice input pos2 (pos2 + consumed2) in
  let (pos3, consumed3) = a23 input2 in
  (pos2 + pos3, consumed3)

abstract
let gaccessor_compose
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
= gaccessor_compose' a12 a23

abstract
let gaccessor_compose_eq
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
= ()

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

let slice_access'
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice)
  (pos: U32.t)
: Ghost U32.t
  (requires (
    valid' p1 h sl pos
  ))
  (ensures (fun pos' -> True))
= 
  let small = B.as_seq h (B.gsub sl.base pos (U32.uint_to_t (content_length' p1 h sl pos))) in
  pos `U32.add` U32.uint_to_t (fst (g small))

#push-options "--z3rlimit 16"

[@"opaque_to_smt"]
abstract
let slice_access
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice)
  (pos: U32.t)
: Ghost U32.t
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos)
  ))
  (ensures (fun pos' ->
    valid p2 h sl pos' /\
    contents p2 h sl pos' == cl.clens_get (contents p1 h sl pos) /\
    // useful for framing
    U32.v pos <= U32.v pos' /\
    U32.v pos' + content_length p2 h sl pos' <= U32.v pos + content_length p1 h sl pos
  ))
= valid_facts p1 h sl pos;
  let res = slice_access' h g sl pos in
  valid_facts p2 h sl res;
  let _ =
    let input_large = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
    let input_small = B.as_seq h (B.gsub sl.base pos (U32.uint_to_t (content_length' p1 h sl pos))) in
    parse_strong_prefix p1 input_large input_small;
    let output_small = B.as_seq h (B.gsub sl.base res (U32.uint_to_t (snd (g input_small)))) in
    let output_large = B.as_seq h (B.gsub sl.base res (sl.len `U32.sub` res)) in
    parse_strong_prefix p2 output_small output_large
  in
  res

#pop-options

abstract
let slice_access_eq
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice)
  (pos: U32.t)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos)
  ))
  (ensures (
    valid' p1 h sl pos /\
    cl.clens_cond (contents' p1 h sl pos) /\
    slice_access h g sl pos == slice_access' h g sl pos
  ))
= valid_facts p1 h sl pos;
  assert_norm (slice_access h g sl pos == slice_access' h g sl pos)

#push-options "--z3rlimit 16"

abstract
let slice_access_eq_inv
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice)
  (pos: U32.t)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl.clens_cond (contents p1 h sl pos)
  ))
  (ensures (
    let pos2 = slice_access h g sl pos in
    g (B.as_seq h (B.gsub sl.base pos (U32.uint_to_t (content_length p1 h sl pos)))) ==
      (U32.v pos2 - U32.v pos, content_length p2 h sl pos2)
  ))
= valid_facts p1 h sl pos;
  slice_access_eq h g sl pos;
  let res = slice_access' h g sl pos in
  valid_facts p2 h sl res;
    let input_large = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
    let input_small = B.as_seq h (B.gsub sl.base pos (U32.uint_to_t (content_length' p1 h sl pos))) in
    parse_strong_prefix p1 input_large input_small;
    let output_small = B.as_seq h (B.gsub sl.base res (U32.uint_to_t (snd (g input_small)))) in
    let output_large = B.as_seq h (B.gsub sl.base res (sl.len `U32.sub` res)) in
    parse_strong_prefix p2 output_small output_large

#pop-options

abstract
let slice_access_frame
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (g: gaccessor p1 p2 cl)
  (sl: slice)
  (pos: U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
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
= valid_facts p1 h sl pos;
  valid_facts p1 h' sl pos;
  slice_access_eq h g sl pos;
  slice_access_eq h' g sl pos;
  loc_slice_from_to_eq_gen sl pos (get_valid_pos p1 h sl pos)

[@unifier_hint_injective]
inline_for_extraction
let accessor
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  ($g: gaccessor p1 p2 cl)
: Tot Type
= (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> k1.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_subkind == Some ParserStrong /\ valid p1 h sl pos /\ cl.clens_cond (contents p1 h sl pos))) 
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    pos' == slice_access h g sl pos
  ))

[@unifier_hint_injective]
inline_for_extraction
let make_accessor_from_pure
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  ($g: gaccessor p1 p2 cl)
  (f: (
    (input: Ghost.erased bytes) ->
    Pure U32.t
    (requires (Seq.length (Ghost.reveal input) < 4294967296 /\ gaccessor_pre p1 p2 cl (Ghost.reveal input)))
    (ensures (fun y -> U32.v y == fst (g (Ghost.reveal input))))
  ))
: Tot (accessor g)
= fun (sl: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ =
    slice_access_eq_inv h g sl pos;
    valid_facts p1 h sl pos;
    parse_strong_prefix p1 (B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos))) (B.as_seq h (B.gsub sl.base pos (get_valid_pos p1 h sl pos `U32.sub` pos)))
  in
  pos `U32.add` f (Ghost.hide (B.as_seq h (B.gsub sl.base pos (get_valid_pos p1 h sl pos `U32.sub` pos))))

inline_for_extraction
let accessor_id
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (accessor (gaccessor_id p))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_id p) input pos in
  pos

inline_for_extraction
let accessor_ext
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (#g: gaccessor p1 p2 cl)
  (a: accessor g)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
: Tot (accessor (gaccessor_ext g cl' sq))
= fun input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq h (gaccessor_ext g cl' sq) input pos;
    gaccessor_ext_eq g cl' sq (B.as_seq h (B.gsub input.base pos (U32.uint_to_t (content_length' p1 h input pos))));
    slice_access_eq h g input pos
  in
  a input pos

#push-options "--z3rlimit 32"

inline_for_extraction
let accessor_compose
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (#a12: gaccessor p1 p2 cl12)
  (a12' : accessor a12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (#a23: gaccessor p2 p3 cl23)
  (a23' : accessor a23)
  (sq: squash (k2.parser_kind_subkind == Some ParserStrong))
: Tot (accessor (gaccessor_compose a12 a23))
= fun input pos ->
  let h = HST.get () in
  let pos2 = a12' input pos in
  let pos3 = a23' input pos2 in
  slice_access_eq_inv h a12 input pos;
  slice_access_eq_inv h a23 input pos2;
  slice_access_eq_inv h (gaccessor_compose a12 a23) input pos;
  pos3

#pop-options

inline_for_extraction
let accessor_compose_strong
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (#a12: gaccessor p1 p2 cl12)
  (a12' : accessor a12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (#a23: gaccessor p2 p3 cl23)
  (a23' : accessor a23 { clens_compose_strong_pre cl12 cl23 } )
  (sq: squash (k2.parser_kind_subkind == Some ParserStrong))
: Tot (accessor (gaccessor_compose_strong a12 a23))
= fun input pos -> 
  let h = HST.get () in
  slice_access_eq h (gaccessor_compose_strong a12 a23) input pos;
  slice_access_eq h (gaccessor_compose a12 a23) input pos;
  accessor_compose a12' a23' () input pos

(* Validators *)

inline_for_extraction
let max_uint32 : U32.t = 4294967295ul

let max_uint32_correct
  (x: U32.t)
: Lemma
  (U32.v x <= U32.v max_uint32)
= ()

(*

Error codes for validators

TODO: replace with type classes

inline_for_extraction
let default_validator_cls : validator_cls = {
  validator_max_length = 4294967279ul;
}

*)

inline_for_extraction
let validator_max_length : (u: U32.t { 4 <= U32.v u /\ U32.v u < U32.v max_uint32 } ) = 4294967279ul

inline_for_extraction
type validator_error = (u: U32.t { U32.v u > U32.v validator_max_length } )

inline_for_extraction
let validator_error_generic : validator_error = validator_max_length `U32.add` 1ul

inline_for_extraction
let validator_error_not_enough_data : validator_error = validator_max_length `U32.add` 2ul

[@unifier_hint_injective]
inline_for_extraction
let validator (#k: parser_kind) (#t: Type) (p: parser k t) : Tot Type =
  (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> live_slice h sl /\ U32.v pos <= U32.v sl.len /\ U32.v sl.len <= U32.v validator_max_length))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    if U32.v res <= U32.v validator_max_length
    then
      valid_pos p h sl pos res
    else
      (~ (valid p h sl pos))
  )))

let valid_total_constant_size
  (h: HS.mem)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: U32.t)
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
    (valid p h input pos <==> (live_slice h input /\ U32.v input.len - U32.v pos >= k.parser_kind_low)) /\
    (valid p h input pos ==> content_length p h input pos == k.parser_kind_low)
  ))
= parser_kind_prop_equiv k p;
  valid_facts p h input pos

inline_for_extraction
let validate_total_constant_size
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    U32.v sz <= U32.v validator_max_length /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  })
: Tot (validator p)
= fun (input: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_total_constant_size h p sz input pos in
  if U32.lt (input.len `U32.sub` pos) sz
  then validator_error_not_enough_data
  else
    pos `U32.add` sz

[@unifier_hint_injective]
inline_for_extraction
let jumper
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> valid p h sl pos))
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + content_length p h sl pos == U32.v pos'
  ))

inline_for_extraction
let jump_constant_size
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz
  })
: Tot (jumper p)
= fun (input: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts p h input pos in
  pos `U32.add` sz

[@unifier_hint_injective]
inline_for_extraction
let leaf_reader
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack t
  (requires (fun h -> valid p h sl pos))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == contents p h sl pos
  ))

[@unifier_hint_injective]
inline_for_extraction
let leaf_reader_ext
  (#k1: parser_kind)
  (#t: Type)
  (#p1: parser k1 t)
  (p32: leaf_reader p1)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (lem: (
    (x: bytes) ->
    Lemma
    (parse p2 x == parse p1 x)
  ))
: Tot (leaf_reader p2)
= fun sl pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts p1 h sl pos;
    valid_facts p2 h sl pos;
    lem (B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)))
  in
  p32 sl pos

[@unifier_hint_injective]
inline_for_extraction
let leaf_writer_weak
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> live_slice h sl /\ U32.v pos <= U32.v sl.len /\ U32.v sl.len < U32.v max_uint32))
  (ensures (fun h pos' h' ->
    B.modifies (loc_slice_from sl pos) h h' /\ (
    if pos' = max_uint32
    then U32.v pos + serialized_length s x > U32.v sl.len
    else valid_content_pos p h' sl pos x pos'
  )))

[@unifier_hint_injective]
inline_for_extraction
let leaf_writer_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> live_slice h sl /\ U32.v pos + serialized_length s x <= U32.v sl.len))
  (ensures (fun h pos' h' ->
    B.modifies (loc_slice_from_to sl pos pos') h h' /\
    valid_content_pos p h' sl pos x pos'
  ))

[@unifier_hint_injective]
inline_for_extraction
let serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (b: buffer8) ->
  HST.Stack U32.t
  (requires (fun h -> B.live h b /\ Seq.length (serialize s x) <= B.length b))
  (ensures (fun h len h' ->
    Seq.length (serialize s x) == U32.v len /\ (
    let b' = B.gsub b 0ul len in
    B.modifies (B.loc_buffer b') h h' /\
    B.live h b /\
    B.as_seq h' b' `Seq.equal` serialize s x
  )))

inline_for_extraction
let leaf_writer_strong_of_serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (u: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (leaf_writer_strong s)
= fun x input pos ->
  let b = B.sub input.base pos (input.len `U32.sub` pos) in
  let len = s32 x b in
  let h = HST.get () in
  [@inline_let] let pos' = pos `U32.add` len in
  [@inline_let] let _ : squash (valid_content_pos p h input pos x pos') =
    let small = B.as_seq h (B.gsub b 0ul len) in
    let large = B.as_seq h b in
    parse_strong_prefix p small large;
    valid_facts p h input pos
  in
  [@inline_let] let _ = loc_slice_from_to_eq_gen input pos pos' in
  pos'

inline_for_extraction
let leaf_writer_weak_of_strong_constant_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: leaf_writer_strong s)
  (sz: U32.t)
  (u: squash (
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz /\
    k.parser_kind_low < U32.v max_uint32
  ))
: Tot (leaf_writer_weak s)
= fun x input pos ->
  if (input.len `U32.sub` pos) `U32.lt` sz
  then max_uint32
  else s32 x input pos

#push-options "--z3rlimit 16"

inline_for_extraction
let copy_strong
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: slice) // FIXME: length is useless here
  (spos spos' : U32.t)
  (dst: slice)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h src spos spos' /\
    U32.v dpos + U32.v spos' - U32.v spos <= U32.v dst.len /\
    live_slice h dst /\
    B.loc_disjoint (loc_slice_from_to src spos spos') (loc_slice_from_to dst dpos (dpos `U32.add` (spos' `U32.sub` spos))
  )))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from_to dst dpos dpos') h h' /\
    valid_content_pos p h' dst dpos (contents p h src spos) dpos' /\
    dpos' `U32.sub` dpos == spos' `U32.sub` spos
  ))
= let h0 = HST.get () in
  let len = spos' `U32.sub` spos in
  let src' = B.sub src.base spos len in
  let dst' = B.sub dst.base dpos len in
  valid_facts p h0 src spos;
  loc_slice_from_to_eq_gen src spos spos';
  loc_slice_from_to_eq_gen dst dpos (dpos `U32.add` (spos' `U32.sub` spos));
  B.blit src' 0ul dst' 0ul len;
  let h = HST.get () in
  [@inline_let] let dpos' = dpos `U32.add` len in
  loc_slice_from_to_eq_gen dst dpos dpos';
  parse_strong_prefix p (B.as_seq h0 (B.gsub src.base spos (src.len `U32.sub` spos))) (B.as_seq h (B.gsub dst.base dpos (dst.len `U32.sub` dpos)));
  valid_facts p h dst dpos;
  dpos'

#pop-options

inline_for_extraction
let copy_strong'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (src: slice) // FIXME: length is useless here
  (spos : U32.t)
  (dst: slice)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid p h src spos /\ (
    let clen = content_length p h src spos in
    U32.v dpos + clen <= U32.v dst.len /\
    live_slice h dst /\
    B.loc_disjoint (loc_slice_from src spos) (loc_slice_from_to dst dpos (dpos `U32.add` (U32.uint_to_t clen)))
  )))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from_to dst dpos dpos') h h' /\
    valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  ))
= let spos' = j src spos in
  copy_strong p src spos spos' dst dpos

inline_for_extraction
let copy_weak_with_length
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: slice) // FIXME: length is useless here
  (spos spos' : U32.t)
  (dst: slice)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h src spos spos' /\
    live_slice h dst /\
    U32.v dpos <= U32.v dst.len /\
    U32.v dst.len < U32.v max_uint32 /\
    B.loc_disjoint (loc_slice_from_to src spos spos') (loc_slice_from dst dpos)
  ))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from dst dpos) h h' /\ (
    if dpos' = max_uint32
    then
      U32.v dpos + content_length p h src spos > U32.v dst.len
    else
      valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  )))
= if (dst.len `U32.sub` dpos) `U32.lt` (spos' `U32.sub` spos)
  then max_uint32
  else copy_strong p src spos spos' dst dpos

inline_for_extraction
let copy_weak
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (jmp: jumper p)
  (src: slice)
  (spos : U32.t)
  (dst: slice)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid p h src spos /\
    live_slice h dst /\
    U32.v dpos <= U32.v dst.len /\
    U32.v dst.len < U32.v max_uint32 /\
    B.loc_disjoint (loc_slice_from src spos) (loc_slice_from dst dpos)
  ))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from dst dpos) h h' /\ (
    if dpos' = max_uint32
    then
      U32.v dpos + content_length p h src spos > U32.v dst.len
    else
      valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  )))
= let spos' = jmp src spos in
  copy_weak_with_length p src spos spos' dst dpos

let loc_includes_loc_slice_from_loc_slice_from_to
  (s: slice)
  (pos pos1 pos2: U32.t)
: Lemma
  (requires (U32.v pos <= U32.v pos1))
  (ensures (B.loc_includes (loc_slice_from s pos) (loc_slice_from_to s pos1 pos2)))
  [SMTPat (B.loc_includes (loc_slice_from s pos) (loc_slice_from_to s pos1 pos2))]
= assert (B.loc_includes (loc_slice_from s pos) (loc_slice_from s pos1))

let loc_disjoint_loc_slice_from_loc_disjoint_loc_slice_from_to
  (l: B.loc)
  (s: slice)
  (pos pos1 pos2: U32.t)
: Lemma
  (requires (B.loc_disjoint l (loc_slice_from s pos) /\ U32.v pos <= U32.v pos1))
  (ensures (B.loc_disjoint l (loc_slice_from_to s pos1 pos2)))
  [SMTPat (B.loc_disjoint l (loc_slice_from_to s pos1 pos2)); SMTPat (B.loc_disjoint l (loc_slice_from s pos))]
= assert (B.loc_includes (loc_slice_from s pos) (loc_slice_from s pos1))

let loc_disjoint_loc_slice_from_to_loc_disjoint_loc_slice_from_to
  (l: B.loc)
  (s: slice)
  (pos1 pos2 pos1' pos2': U32.t)
: Lemma
  (requires (B.loc_disjoint l (loc_slice_from_to s pos1 pos2) /\ U32.v pos1 <= U32.v pos1' /\ U32.v pos2' <= U32.v pos2))
  (ensures (B.loc_disjoint l (loc_slice_from_to s pos1' pos2')))
  [SMTPat (B.loc_disjoint l (loc_slice_from_to s pos1 pos2)); SMTPat (B.loc_disjoint l (loc_slice_from_to s pos1' pos2'))]
= assert (B.loc_includes (loc_slice_from_to s pos1 pos2) (loc_slice_from_to s pos1' pos2'))


(* lists, to avoid putting LowParse.*.List into the user context *)

[@"opaque_to_smt"]
abstract
let rec valid_list
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0
  (decreases (U32.v pos' - U32.v pos))
= k.parser_kind_subkind == Some ParserStrong /\
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
  ))

abstract
let rec valid_list_equiv
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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
= assert_norm (valid_list p h sl pos pos' <==> (
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

abstract
let valid_list_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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

[@"opaque_to_smt"]
abstract
let rec contents_list
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost (list t)
  (requires (valid_list p h sl pos pos'))
  (ensures (fun _ -> True))
  (decreases (U32.v pos' - U32.v pos))
= valid_list_equiv p h sl pos pos';
  if pos = pos'
  then []
  else
    contents p h sl pos :: contents_list p h sl (get_valid_pos p h sl pos) pos'

abstract
let contents_list_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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
= assert_norm (contents_list p h sl pos pos' == (
    valid_list_equiv p h sl pos pos';
    if pos = pos'
    then []
    else
      contents p h sl pos :: contents_list p h sl (get_valid_pos p h sl pos) pos'
  ))

abstract
let valid_list_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
: Lemma
  (requires (U32.v pos <= U32.v sl.len /\ live_slice h sl /\ k.parser_kind_low > 0 /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_list p h sl pos pos /\
    contents_list p h sl pos pos == []
  ))
= valid_list_equiv p h sl pos pos;
  contents_list_eq p h sl pos pos

abstract
let valid_list_cons
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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

abstract
let valid_list_cons_recip
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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

[@"opaque_to_smt"]
abstract
let rec valid_list_frame_1
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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
  loc_slice_from_to_eq_gen s pos pos' ;
  begin if pos = pos'
  then ()
  else begin
    let pos1 = get_valid_pos p h s pos in
    valid_list_frame_1 p h s pos1 pos' l h'
  end end;
  contents_list_eq p h' s pos pos'

[@"opaque_to_smt"]
abstract
let rec valid_list_frame_2
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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
  loc_slice_from_to_eq_gen s pos pos' ;
  if pos = pos'
  then ()
  else begin
    let pos1 = get_valid_pos p h' s pos in
    valid_valid_exact p h' s pos;
    valid_exact_valid p h s pos pos1;
    valid_list_frame_2 p h s pos1 pos' l h'
  end;
  contents_list_eq p h s pos pos'

abstract
let valid_list_frame
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
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

abstract
let rec valid_list_append
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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

abstract
let valid_list_snoc
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
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

(* fold_left on lists *)

#push-options "--z3rlimit 20"
inline_for_extraction
private
let list_fold_left_gen
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (j: jumper p)
  (sl: slice)
  (pos pos' : U32.t)
  (h0: HS.mem)
  (l: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal l) (loc_slice_from_to sl pos pos') } )
  (inv: (HS.mem -> list t -> list t -> U32.t -> GTot Type0))
  (inv_frame: (h: HS.mem) -> (l1: list t) -> (l2: list t) -> (pos1: U32.t) -> (h' : HS.mem) -> Lemma (requires (
    B.modifies (B.loc_unused_in h0) h h' /\
    inv h l1 l2 pos1
  )) (ensures (inv h' l1 l2 pos1)))
  (body: (
    (pos1: U32.t) ->
    (pos2: U32.t) ->
    HST.Stack unit
    (requires (fun h ->
      valid_list p h sl pos pos1 /\
      valid_pos p h sl pos1 pos2 /\
      valid_list p h sl pos2 pos' /\
      inv h (contents_list p h sl pos pos1) (contents p h sl pos1 :: contents_list p h sl pos2 pos') pos1
    ))
    (ensures (fun h _ h' ->
      B.modifies (Ghost.reveal l) h h' /\
      inv h' (contents_list p h sl pos pos1 `L.append` [contents p h sl pos1]) (contents_list p h sl pos2 pos') pos2
    ))
  ))
: HST.Stack unit
  (requires (fun h ->
    h == h0 /\
    valid_list p h sl pos pos' /\
    inv h [] (contents_list p h sl pos pos') pos
  ))
  (ensures (fun h _ h' ->
    B.modifies (Ghost.reveal l) h h' /\
    inv h' (contents_list p h sl pos pos') [] pos'
  ))
= HST.push_frame ();
  let h1 = HST.get () in
  //B.fresh_frame_modifies h0 h1;
  let bpos : B.pointer U32.t = B.alloca pos 1ul in
  let h2 = HST.get () in
  let test_pre (h: HS.mem) : GTot Type0 =
    B.live h bpos /\ (
    let pos1 = Seq.index (B.as_seq h bpos) 0 in
    valid_list p h0 sl pos pos1 /\
    valid_list p h0 sl pos1 pos' /\
    B.modifies (Ghost.reveal l `B.loc_union` B.loc_buffer bpos) h2 h /\
    inv h (contents_list p h0 sl pos pos1) (contents_list p h0 sl pos1 pos') pos1
  )
  in
  let test_post (cond: bool) (h: HS.mem) : GTot Type0 =
    test_pre h /\
    cond == (U32.v (Seq.index (B.as_seq h bpos) 0) < U32.v pos')
  in
  valid_list_nil p h0 sl pos;
  inv_frame h0 [] (contents_list p h0 sl pos pos') pos h1;
  inv_frame h1 [] (contents_list p h0 sl pos pos') pos h2;
  [@inline_let]
  let while_body () : HST.Stack unit
    (requires (fun h -> test_post true h))
    (ensures (fun _ _ h1 -> test_pre h1))
  =
      let h51 = HST.get () in
      let pos1 = B.index bpos 0ul in
      valid_list_cons_recip p h0 sl pos1 pos';
      //assert (B.modifies (Ghost.reveal l `B.loc_union` B.loc_buffer bpos) h0 h51);
      //assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos'));
      //assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos pos1));
      valid_list_cons_recip p h51 sl pos1 pos';
      let pos2 = j sl pos1 in
      let h52 = HST.get () in
      inv_frame h51 (contents_list p h0 sl pos pos1) (contents_list p h1 sl pos1 pos') pos1 h52;
      body pos1 pos2;
      let h53 = HST.get () in
      //assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos2));
      //assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos2 pos'));
      valid_pos_frame_strong p h0 sl pos1 pos2 (Ghost.reveal l `B.loc_union` B.loc_buffer bpos) h53;
      valid_list_snoc p h0 sl pos pos1;
      B.upd bpos 0ul pos2;
      let h54 = HST.get () in
      inv_frame h53 (contents_list p h0 sl pos pos2) (contents_list p h0 sl pos2 pos') pos2 h54
  in
  C.Loops.while
    #test_pre
    #test_post
    (fun (_: unit) -> B.index bpos 0ul `U32.lt` pos' <: HST.Stack bool (requires (fun h -> test_pre h)) (ensures (fun h x h1 -> test_post x h1)))
    while_body
    ;
  valid_list_nil p h0 sl pos';
  let h3 = HST.get () in
  HST.pop_frame ();
  let h4 = HST.get () in
  //B.popped_modifies h3 h4;
  B.loc_regions_unused_in h0 (Set.singleton (HS.get_tip h3));  
  inv_frame h3 (contents_list p h0 sl pos pos') [] pos' h4
  //B.loc_includes_union_l (B.loc_all_regions_from false (HS.get_tip h1)) (Ghost.reveal l) (Ghost.reveal l)
  //B.modifies_fresh_frame_popped h0 h1 (Ghost.reveal l) h3 h4
#pop-options

module G = FStar.Ghost

inline_for_extraction
let list_fold_left
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (j: jumper p)
  (sl: slice)
  (pos pos' : U32.t)
  (h0: HS.mem)
  (l: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal l) (loc_slice_from_to sl pos pos') } )
  (inv: (HS.mem -> list t -> list t -> U32.t -> GTot Type0))
  (inv_frame: (h: HS.mem) -> (l1: list t) -> (l2: list t) -> (pos1: U32.t) -> (h' : HS.mem) -> Lemma (requires (
    B.modifies (B.loc_unused_in h0) h h' /\
    inv h l1 l2 pos1
  )) (ensures (inv h' l1 l2 pos1)))
  (body: (
    (pos1: U32.t) ->
    (pos2: U32.t) ->
    (l1: Ghost.erased (list t)) ->
    (x: Ghost.erased t) ->
    (l2: Ghost.erased (list t)) ->
    HST.Stack unit
    (requires (fun h ->
      valid_list p h sl pos pos' /\
      valid_content_pos p h sl pos1 (G.reveal x) pos2 /\
      U32.v pos <= U32.v pos1 /\ U32.v pos2 <= U32.v pos' /\
      B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos2) /\
      inv h (Ghost.reveal l1) (Ghost.reveal x :: Ghost.reveal l2) pos1 /\
      contents_list p h sl pos pos' == Ghost.reveal l1 `L.append` (Ghost.reveal x :: Ghost.reveal l2)
    ))
    (ensures (fun h _ h' ->
      B.modifies (Ghost.reveal l) h h' /\
      inv h' (Ghost.reveal l1 `L.append` [contents p h sl pos1]) (Ghost.reveal l2) pos2
    ))
  ))
: HST.Stack unit
  (requires (fun h ->
    h == h0 /\
    valid_list p h sl pos pos' /\
    inv h [] (contents_list p h sl pos pos') pos
  ))
  (ensures (fun h _ h' ->
    B.modifies (Ghost.reveal l) h h' /\
    inv h' (contents_list p h sl pos pos') [] pos'
  ))
= list_fold_left_gen
    p
    j
    sl
    pos pos'
    h0
    l
    inv
    inv_frame
    (fun pos1 pos2 ->
      let h = HST.get () in
      valid_list_cons p h sl pos1 pos';
      valid_list_append p h sl pos pos1 pos';
      body
        pos1
        pos2
        (Ghost.hide (contents_list p h sl pos pos1))
        (Ghost.hide (contents p h sl pos1))
        (Ghost.hide (contents_list p h sl pos2 pos'))
    )

let list_length_append (#t: Type) (l1 l2: list t) : Lemma (L.length (l1 `L.append` l2) == L.length l1 + L.length l2) = L.append_length l1 l2

inline_for_extraction
let list_length
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (j: jumper p)
  (sl: slice)
  (pos pos' : U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid_list p h sl pos pos'
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v res == L.length (contents_list p h sl pos pos')
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  B.fresh_frame_modifies h0 h1;
  let blen : B.pointer U32.t = B.alloca 0ul 1ul in
  let h2 = HST.get () in
  list_fold_left
    p
    j
    sl
    pos
    pos'
    h2
    (Ghost.hide (B.loc_buffer blen))
    (fun h l1 l2 pos1 ->
      B.modifies (B.loc_buffer blen) h2 h /\
      B.live h blen /\ (
      let len = U32.v (Seq.index (B.as_seq h blen) 0) in
      len <= U32.v pos1 /\ // necessary to prove that length computations do not overflow
      len == L.length l1
    ))
    (fun h l1 l2 pos1 h' ->
      B.modifies_only_not_unused_in (B.loc_buffer blen) h2 h';
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun pos1 pos2 l1 x l2 ->
      B.upd blen 0ul (B.index blen 0ul `U32.add` 1ul);
      Classical.forall_intro_2 (list_length_append #t)
    )
    ;
  let len = B.index blen 0ul in
  HST.pop_frame ();
  len

abstract
let rec list_filter_append
  (#t: Type)
  (f: (t -> Tot bool))
  (l1 l2: list t)
: Lemma
  (L.filter f (l1 `L.append` l2) == L.filter f l1 `L.append` L.filter f l2)
= match l1 with
  | [] -> ()
  | a :: q ->
    list_filter_append f q l2

#push-options "--z3rlimit 16"

inline_for_extraction
let list_filter
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (j: jumper p)
  (f: (t -> Tot bool))
  (f' : (
    (sl: slice) ->
    (pos: U32.t) ->
    (x: Ghost.erased t) ->
    HST.Stack bool
    (requires (fun h -> valid_content p h sl pos (G.reveal x)))
    (ensures (fun h res h' -> B.modifies B.loc_none h h' /\ res == f (G.reveal x)))
  ))
  (sl: slice)
  (pos pos' : U32.t)
  (sl_out : slice)
  (pos_out : U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v pos_out + U32.v pos' - U32.v pos <= U32.v sl_out.len /\
    valid_list p h sl pos pos' /\
    B.loc_disjoint (loc_slice_from_to sl pos pos') (loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))) /\
    live_slice h sl_out
  ))
  (ensures (fun h pos_out' h' ->
    B.modifies (loc_slice_from_to sl_out pos_out pos_out') h h' /\
    U32.v pos_out' - U32.v pos_out <= U32.v pos' - U32.v pos /\
    valid_list p h' sl_out pos_out pos_out' /\
    contents_list p h' sl_out pos_out pos_out' == L.filter f (contents_list p h sl pos pos')
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  //B.fresh_frame_modifies h0 h1;
  let bpos_out' : B.pointer U32.t = B.alloca pos_out 1ul in
  let h2 = HST.get () in
  let inv (h: HS.mem) (l1 l2: list t) (pos1: U32.t) : GTot Type0 =
    B.live h bpos_out' /\ (
      let pos_out' = Seq.index (B.as_seq h bpos_out') 0 in
      B.modifies (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out pos_out') h2 h /\
      valid_list p h sl_out pos_out pos_out' /\
      contents_list p h sl_out pos_out pos_out' == L.filter f l1 /\
      U32.v pos_out' - U32.v pos1 <= U32.v pos_out - U32.v pos // necessary to prove that length computations do not overflow
    )
  in
  valid_list_nil p h2 sl_out pos_out;
  list_fold_left
    p
    j
    sl
    pos
    pos'
    h2
    (Ghost.hide (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))))
    inv
    (fun h l1 l2 pos1 h' ->
      let pos_out' = Seq.index (B.as_seq h bpos_out') 0 in
      B.modifies_only_not_unused_in (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out pos_out') h2 h';
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun pos1 pos2 l1 x l2 ->
      let pos_out1 = B.index bpos_out' 0ul in
      list_filter_append f (G.reveal l1) [G.reveal x];
      if f' sl pos1 x
      then begin
        assert (B.loc_includes (loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))) (loc_slice_from_to sl_out pos_out1 (pos_out1 `U32.add` (pos2 `U32.sub` pos1))));
        let pos_out2 = copy_strong p sl pos1 pos2 sl_out pos_out1 in
        B.upd bpos_out' 0ul pos_out2;
        let h' = HST.get () in
        valid_list_nil p h' sl_out pos_out2;
        valid_list_cons p h' sl_out pos_out1 pos_out2;
        valid_list_append p h' sl_out pos_out pos_out1 pos_out2
      end else
        L.append_l_nil (L.filter f (G.reveal l1))
    )
    ;
  let pos_out' = B.index bpos_out' 0ul in
  HST.pop_frame ();
  pos_out'

#pop-options

#push-options "--z3rlimit 16"

inline_for_extraction
let list_nth
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (j: jumper p)
  (sl: slice)
  (pos pos' : U32.t)
  (i: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid_list p h sl pos pos' /\
    U32.v i < L.length (contents_list p h sl pos pos')
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    valid_list p h sl pos res /\
    valid p h sl res /\
    valid_list p h sl (get_valid_pos p h sl res) pos' /\
    L.length (contents_list p h sl pos res) == U32.v i /\
    contents p h sl res == L.index (contents_list p h sl pos pos') (U32.v i)
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let bpos1 = B.alloca pos 1ul in
  let bi1 = B.alloca 0ul 1ul in
  let h1 = HST.get () in
  valid_list_nil p h0 sl pos;
  C.Loops.do_while
    (fun h b ->
      B.modifies (B.loc_union (B.loc_buffer bpos1) (B.loc_buffer bi1)) h1 h /\ (
      let pos1 = B.get h bpos1 0 in
      let i1 = B.get h bi1 0 in
      U32.v i1 <= U32.v i /\
      valid_list p h0 sl pos pos1 /\
      valid_list p h0 sl pos1 pos' /\
      L.length (contents_list p h0 sl pos pos1) == U32.v i1 /\ (
      let tl = contents_list p h0 sl pos1 pos' in
      U32.v i - U32.v i1 < L.length tl /\
      L.index (contents_list p h0 sl pos pos') (U32.v i) == L.index tl (U32.v i - U32.v i1) /\
      (b == true ==> i == i1)
    )))
    (fun _ ->
      let i1 = B.index bi1 0ul in
      if i1 = i
      then true
      else
        let pos1 = B.index bpos1 0ul in
        let _ = valid_list_cons_recip p h0 sl pos1 pos' in
        let _ = valid_list_snoc p h0 sl pos pos1 in
        let pos2 = j sl pos1 in
        let _ = assert (pos2 == get_valid_pos p h0 sl pos1) in
        let _ = list_length_append (contents_list p h0 sl pos pos1) [contents p h0 sl pos1] in
        let i2 = i1 `U32.add` 1ul in
        let _ = B.upd bpos1 0ul pos2 in
        let _ = B.upd bi1 0ul i2 in
        i2 = i
    );
  let res = B.index bpos1 0ul in
  let _ = valid_list_cons_recip p h0 sl res pos' in
  HST.pop_frame ();
  res

#pop-options

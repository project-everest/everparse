module LowParse.Low.Base.Spec

module M = LowParse.Math
module B = LowStar.Monotonic.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

let valid
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: GTot Type0
= valid' p h s pos

let valid_equiv
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
: Lemma
  (valid p h s pos <==> valid' p h s pos)
= assert_norm (valid p h s pos <==> valid' p h s pos)

let valid_dec
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
= valid_equiv p h s pos;
  (not (pos `U32.gt` s.len)) && Some? (parse p (bytes_of_slice_from h s pos))

let contents
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
= valid_equiv p h s pos;
  contents' p h s pos

let contents_eq
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
= valid_equiv p h s pos;
  assert_norm (contents p h s pos == contents' p h s pos)

let content_length
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
= valid_equiv p h sl pos;
  content_length' p h sl pos

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

let serialized_length_eq
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (serialized_length s x == Seq.length (serialize s x))
= ()

let content_length_eq_gen
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
= valid_equiv p h sl pos;
  assert_norm (content_length p h sl pos == content_length' p h sl pos)

let content_length_eq
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
= parser_kind_prop_equiv k p;
  content_length_eq_gen p h sl pos;
  contents_eq p h sl pos;
  let b = bytes_of_slice_from h sl pos in
  let Some (x, consumed) = parse p b in
  assert (x == contents p h sl pos);
  let ps' = parse p (serialize s x) in
  assert (serializer_correct p s);
  assert (Some? ps');
  assert (injective_precond p b (serialize s x))

let get_valid_pos
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
= pos `U32.add` U32.uint_to_t (content_length p h sl pos)

let get_valid_pos_post
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
= ()

let valid_exact
  (#rrel #rel: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0
= valid_exact' p h s pos pos'

let valid_exact_equiv
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
= assert_norm (valid_exact p h s pos pos' <==> valid_exact' p h s pos pos')

let contents_exact
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
= valid_exact_equiv p h s pos pos' ;
  contents_exact' p h s pos pos'

let contents_exact_eq
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
= valid_exact_equiv p h s pos pos' ;
  assert_norm (contents_exact p h s pos pos' == contents_exact' p h s pos pos')

let gaccessor_prop
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (f: gaccessor' p1 p2 cl)
: GTot Type0
= gaccessor_prop' f

let gaccessor_prop_equiv
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
= ()

let gaccessor_id
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (gaccessor p p (clens_id _))
= gaccessor_id' p

let gaccessor_id_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Lemma
  (gaccessor_id p input == gaccessor_id' p input)
= ()


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

let gaccessor_compose_injective
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
= let sl_ = Seq.slice sl (a12 sl) (Seq.length sl) in
  let sl'_ = Seq.slice sl' (a12 sl') (Seq.length sl') in
  assert (injective_precond p2 sl_ sl'_)

let gaccessor_compose_no_lookahead
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
= let sl_ = Seq.slice sl (a12 sl) (Seq.length sl) in
  let sl'_ = Seq.slice sl' (a12 sl') (Seq.length sl') in
  parse_strong_prefix p1 sl sl';
  assert (injective_precond p1 sl sl');
  assert (injective_precond p2 sl_ sl'_)

[@"opaque_to_smt"]
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
= Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_compose_injective a12 a23 x));
  Classical.forall_intro_2 (fun x -> Classical.move_requires (gaccessor_compose_no_lookahead a12 a23 x));
  gaccessor_compose' a12 a23

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
= assert_norm (gaccessor_compose a12 a23 input == gaccessor_compose' a12 a23 input)

[@"opaque_to_smt"]
let slice_access
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
= valid_facts p1 h sl pos;
  slice_access' h g sl pos

let slice_access_eq
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
= valid_facts p1 h sl pos;
  assert_norm (slice_access h g sl pos == slice_access' h g sl pos)

let slice_access_frame_strong
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
= valid_facts p1 h sl pos;
  valid_facts p1 h' sl pos;
  slice_access_eq h g sl pos;
  slice_access_eq h' g sl pos;
  let pos2 = get_valid_pos p1 h sl pos in
  parse_strong_prefix p1 (bytes_of_slice_from h sl pos) (bytes_of_slice_from_to h sl pos pos2);
  B.modifies_buffer_from_to_elim sl.base pos (get_valid_pos p1 h sl pos) l h h' ;
  parse_strong_prefix p1 (bytes_of_slice_from_to h' sl pos pos2) (bytes_of_slice_from h' sl pos)

let rec valid_list
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

let rec valid_list_equiv
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

let rec contents_list
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
= valid_list_equiv p h sl pos pos';
  if pos = pos'
  then []
  else
    contents p h sl pos :: contents_list p h sl (get_valid_pos p h sl pos) pos'

let contents_list_eq
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
= assert_norm (contents_list p h sl pos pos' == (
    valid_list_equiv p h sl pos pos';
    if pos = pos'
    then []
    else
      contents p h sl pos :: contents_list p h sl (get_valid_pos p h sl pos) pos'
  ))

let rec serialized_list_length (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (l: list t) : GTot nat =
  match l with
  | [] -> 0
  | x :: q -> serialized_length s x + serialized_list_length s q

let serialized_list_length_nil (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) : Lemma
  (serialized_list_length s [] == 0)
= ()

let serialized_list_length_cons (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (x: t) (q: list t) : Lemma
  (serialized_list_length s (x :: q) == serialized_length s x + serialized_list_length s q)
= ()

let rec serialized_list_length_append (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (l1 l2: list t) : Lemma
  (serialized_list_length s (List.Tot.append l1 l2) == serialized_list_length s l1 + serialized_list_length s l2)
= match l1 with
  | [] -> ()
  | _ :: q -> serialized_list_length_append s q l2

let rec valid_list_serialized_list_length (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (h: HS.mem) (#rrel #rel: _) (input: slice rrel rel) (pos pos' : U32.t) : Lemma
  (requires (
    valid_list p h input pos pos'
  ))
  (ensures (
    serialized_list_length s (contents_list p h input pos pos') == U32.v pos' - U32.v pos
  ))
  (decreases (U32.v pos' - U32.v pos))
= if pos = pos'
  then valid_list_nil p h input pos
  else begin
    valid_list_cons_recip p h input pos pos' ;
    let pos1 = get_valid_pos p h input pos in
    valid_list_serialized_list_length s h input pos1 pos'
  end

#restart-solver
#set-options "--fuel 2 --ifuel 2 --z3rlimit 100"

let rec serialized_list_length_constant_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_high == Some k.parser_kind_low})
  (l: list t)
: Lemma
  (ensures (
    serialized_list_length s l == L.length l `Prims.op_Multiply` k.parser_kind_low
  ))
= match l with
  | [] ->
    assert (serialized_list_length s l == 0);
    assert (L.length l == 0)
  | a :: q ->
    serialized_list_length_constant_size s q;
    serialized_length_eq s a;
    assert (serialized_length s a == k.parser_kind_low);
    M.distributivity_add_left 1 (L.length q) k.parser_kind_low

#set-options "--fuel 2 --ifuel 1 --z3rlimit 100"

let rec list_flatten_append
  (#a: Type)
  (l1 l2: list (list a))
: Lemma
  (L.flatten (l1 `L.append` l2) == L.flatten l1 `L.append` L.flatten l2)
= match l1 with
  | [] -> ()
  | a :: q ->
    list_flatten_append q l2;
    L.append_assoc a (L.flatten q) (L.flatten l2)

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

let rec list_index_append (#t: Type) (l1 l2: list t) (i: int) : Lemma
  (requires (L.length l1 <= i /\ i < L.length l1 + L.length l2))
  (ensures (
    L.length (L.append l1 l2) == L.length l1 + L.length l2 /\
    L.index (L.append l1 l2) i == L.index l2 (i - L.length l1)
  ))
= list_length_append l1 l2;
  match l1 with
  | [] -> ()
  | a :: q -> list_index_append q l2 (i - 1)

#set-options "--fuel 2 --ifuel 0 --z3rlimit 500"
#restart-solver

let list_flatten_map_append
  (#a #b: Type)
  (f: a -> Tot (list b))
  (l1 l2: list a)
: Lemma
  (L.flatten (L.map f (l1 `L.append` l2)) == L.flatten (L.map f l1) `L.append` L.flatten (L.map f l2))
= L.map_append f l1 l2;
  list_flatten_append (L.map f l1) (L.map f l2)

#set-options "--fuel 2 --ifuel 1 --z3rlimit 100"

let rec list_map_list_flatten_map
  (#a #b: Type)
  (f: a -> Tot b)
  (l: list a)
: Lemma
  (L.map f l == L.flatten (L.map (fun x -> [f x]) l))
= match l with
  | [] -> ()
  | a :: q -> list_map_list_flatten_map f q


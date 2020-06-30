module LowParseWriters.Sealed
include LowParseWriters.Parsers

inline_for_extraction
let read_repr
  (t: Type)
  (inv: memory_invariant)
: Tot Type
= read_repr t True (fun _ -> True) (fun _ -> True) inv

inline_for_extraction
let read_reify_trivial
  (#a: Type)
  (#l: memory_invariant)
  (f: (unit -> ERead a True (fun _ -> True) (fun _ -> True) l))
: Tot (read_repr a l)
= reify (f ())

inline_for_extraction
let read_return_conv
  (t: Type)
  (x: t)
  (inv: memory_invariant)
  ()
: ERead t True (fun _ -> True) (fun _ -> True) inv
= x

inline_for_extraction
let read_return
  (t: Type)
  (x: t)
  (inv: memory_invariant)
: Tot (read_repr t inv)
=
  read_reify_trivial (read_return_conv t x inv)

inline_for_extraction
let read_bind_conv
  (a:Type) (b:Type)
  (l: memory_invariant)
  (f_bind : read_repr a l)
  (g : (x: a -> read_repr b l))
  ()
: ERead b True (fun _ -> True) (fun _ -> True) l
= let x = ERead?.reflect f_bind in
  ERead?.reflect (g x)

inline_for_extraction
let read_bind
  (a:Type) (b:Type)
  (l: memory_invariant)
  (f_bind : read_repr a l)
  (g : (x: a -> read_repr b l))
: Tot (read_repr b l)
= read_reify_trivial (read_bind_conv a b l f_bind g)

inline_for_extraction
let read_subcomp_conv (a:Type)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:read_repr a l)
  (sq: squash (l `memory_invariant_includes` l'))
  ()
: ERead a True (fun _ -> True) (fun _ -> True) l'
= let x = ERead?.reflect f_subcomp in
  x

inline_for_extraction
let read_subcomp (a:Type)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:read_repr a l)
: Pure (read_repr a l')
  (requires (l `memory_invariant_includes` l'))
  (ensures (fun _ -> True))
= read_reify_trivial (read_subcomp_conv a l l' f_subcomp ())

inline_for_extraction
let read_if_then_else (a:Type)
  (l:memory_invariant)
  (f_ifthenelse:read_repr a l)
  (g:read_repr a l)
  (p:Type0)
: Tot Type
= read_repr a l

// NOT smt_reifiable_layered_effect because no logical contents
reifiable reflectable total
layered_effect {
  TRead : a:Type -> (memory_invariant) -> Effect
  with
  repr = read_repr;
  return = read_return;
  bind = read_bind;
  subcomp = read_subcomp;
  if_then_else = read_if_then_else
}

inline_for_extraction
let lift_pure_read_conv (a:Type) (wp:pure_wp a { pure_wp_mono a wp })
  (l: memory_invariant)
  (f_pure:unit -> PURE a wp)
  (sq: squash (wp (fun _ -> True)))
  ()
: ERead a True (fun _ -> True) (fun _ -> True) l
= f_pure ()

inline_for_extraction
let lift_pure_read (a:Type) (wp:pure_wp a { pure_wp_mono a wp })
  (l: memory_invariant)
  (f_pure:unit -> PURE a wp)
: Pure (read_repr a l)
  (requires (wp (fun _ -> True)))
  (ensures (fun _ -> True))
= read_reify_trivial (lift_pure_read_conv a wp l f_pure ())

sub_effect PURE ~> TRead = lift_pure_read

inline_for_extraction
let tread_of_eread // NOTE: I could define it as a lift (sub_effect), but I prefer to do it explicitly to avoid F* generating pre and postconditions
  (#a: Type)
  (#l: memory_invariant)
  (f: unit -> ERead a True (fun _ -> True) (fun _ -> True) l)
: TRead a l
= TRead?.reflect (read_reify_trivial f)

inline_for_extraction
let failwith
  (#a: Type)
  (#inv: memory_invariant)
  (s: string)
: TRead a inv
= tread_of_eread (fun _ -> failwith s)

module B = LowStar.Buffer
module U32 = FStar.UInt32

inline_for_extraction
let buffer_index
  (#t: Type)
  (#inv: memory_invariant)
  (b: B.buffer t)
  (i: U32.t {
      B.live inv.h0 b /\
      B.loc_buffer b `B.loc_disjoint` inv.lwrite /\
      U32.v i < B.length b
  })
: TRead t inv
= tread_of_eread (fun _ -> buffer_index b i)

inline_for_extraction
let buffer_sub
  (#t: Type)
  (#inv: memory_invariant)
  (b: B.buffer t)
  (i: U32.t)
  (len: Ghost.erased U32.t {
      B.live inv.h0 b /\
      B.loc_buffer b `B.loc_disjoint` inv.lwrite /\
      U32.v i + U32.v len <= B.length b
  })
: TRead (B.buffer t) inv
= tread_of_eread (fun _ -> buffer_sub b i len)

module LP = LowParse.Low.Base

inline_for_extraction
let deref
  (#p: parser)
  (#inv: memory_invariant)
  (r: LP.leaf_reader (get_parser p))
  (x: ptr p inv)
: TRead (dfst p) inv
= tread_of_eread (fun _ -> deref r x)

inline_for_extraction
let access_t
  (p1 p2: parser)
  (#lens: LP.clens (dfst p1) (dfst p2))
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
: Tot Type
=
  (#inv: memory_invariant) ->
  (x: ptr p1 inv {
    lens.LP.clens_cond (deref_spec x)
  }) ->
  TRead (ptr p2 inv) inv

inline_for_extraction
let access
  (p1 p2: parser)
  (#lens: LP.clens (dfst p1) (dfst p2))
  (#g: LP.gaccessor (get_parser p1) (get_parser p2) lens)
  (a: LP.accessor g)
: Tot (access_t p1 p2 a)
= fun #inv x ->
  tread_of_eread (fun _ -> access p1 p2 a x)


inline_for_extraction
let repr
  (a: Type u#x)
  (r_in: parser) (r_out: parser)
  (l: memory_invariant)
: Tot Type
=
  repr a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l

inline_for_extraction
let reify_trivial
  (#a: Type)
  (#l: memory_invariant)
  (#p1 #p2: parser)
  (f: (unit -> EWrite a p1 p2 (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l))
: Tot (repr a p1 p2 l)
= reify (f ())

inline_for_extraction
let return_conv
  (t: Type)
  (x: t)
  (r: parser)
  (inv: memory_invariant)
  ()
: EWrite t r r (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv
= x

inline_for_extraction
let returnc
  (t: Type)
  (x: t)
  (r: parser)
  (inv: memory_invariant)
: Tot (repr t r r inv)
= reify_trivial (return_conv t x r inv)

inline_for_extraction
let bind_conv (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f: parser)
  (r_out_g: parser)
  (l: memory_invariant)
  (f_bind : repr a r_in_f r_out_f l)
  (g : (x: a -> repr b (r_out_f) r_out_g l))
  ()
: EWrite b r_in_f r_out_g (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l
= let x = EWrite?.reflect f_bind in
  EWrite?.reflect (g x)

inline_for_extraction
let bind (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f: parser)
  (r_out_g: parser)
  (l: memory_invariant)
  (f_bind : repr a r_in_f r_out_f l)
  (g : (x: a -> repr b (r_out_f) r_out_g l))
: Tot (repr b r_in_f r_out_g l)
= reify_trivial (bind_conv a b r_in_f r_out_f r_out_g l f_bind g)

inline_for_extraction
let subcomp_conv
  (a:Type)
  (r_in:parser) (r_out: parser)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:repr a r_in r_out l)
  (sq: squash (
    l `memory_invariant_includes` l'
  ))
  ()
: EWrite a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l'
= let x = EWrite?.reflect f_subcomp in
  x

inline_for_extraction
let subcomp
  (a:Type)
  (r_in:parser) (r_out: parser)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:repr a r_in r_out l)
: Pure (repr a r_in r_out l')
  (requires (
    l `memory_invariant_includes` l'
  ))
  (ensures (fun _ -> True))
=
  reify_trivial (subcomp_conv a r_in r_out l l' f_subcomp ())

let if_then_else (a:Type)
  (r_in:parser) (r_out: parser)
  (l:memory_invariant)
  (f_ifthenelse:repr a r_in r_out l)
  (g:repr a r_in r_out l)
  (p:Type0)
: Tot Type
= repr a r_in r_out
    l

// NOT smt_reifiable_layered_effect because no logical contents
reifiable reflectable total
layered_effect {
  TWrite : a:Type -> (pin: parser) -> (pout: (parser)) -> (memory_invariant) -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

inline_for_extraction
let lift_read_conv
  (a: Type)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a inv)
  ()
: EWrite a r r (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv
= let x = ERead?.reflect f_read_spec in
  x

inline_for_extraction
let lift_read
  (a: Type)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a inv)
: Tot (repr a r r inv)
= reify_trivial (lift_read_conv a inv r f_read_spec)

sub_effect TRead ~> TWrite = lift_read

let destr_repr_spec
  (#a:Type u#x)
  (#r_in: parser)
  (#r_out: parser)
  (#l: memory_invariant)
  (f_destr_spec: unit -> TWrite a r_in r_out l)
: Tot (repr_spec a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True))
= dfst (reify (f_destr_spec ()))

inline_for_extraction
let destr_repr_impl
  (#a:Type u#x)
  (#r_in: parser)
  (#r_out: parser)
  (#l: memory_invariant)
  (f_destr_spec: unit -> TWrite a r_in r_out l)
: Tot (repr_impl a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l (destr_repr_spec f_destr_spec))
= dsnd (reify (f_destr_spec ()))

inline_for_extraction
let twrite_of_ewrite // NOTE: I could define it as a lift (sub_effect), but I prefer to do it explicitly to avoid F* generating pre and postconditions
  (#a: Type)
  (#l: memory_invariant)
  (#p1 #p2: parser)
  (f: unit -> EWrite a p1 p2 (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l)
: TWrite a p1 p2 l
= TWrite?.reflect (reify_trivial f)

inline_for_extraction
let wfailwith
  (#a: Type)
  (#inv: memory_invariant)
  (#rin #rout: parser)  
  (s: string)
: TWrite a rin rout inv
= twrite_of_ewrite (fun _ -> wfailwith s)

inline_for_extraction
let ewrite_of_twrite
  (#a: Type)
  (#l: memory_invariant)
  (#p1 #p2: parser)
  (f: unit -> TWrite a p1 p2 l)
: EWrite a p1 p2 (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l
= EWrite?.reflect (reify (f ()))

inline_for_extraction
let frame
  (#a: Type)
  (#fr: parser)
  (#p: parser)
  (#l: memory_invariant)
  (f: unit ->
    TWrite a emp p l
  )
: TWrite a fr (fr `star` p)
    l
=
  twrite_of_ewrite (fun _ -> frame' _ _ _ _ (fun _ -> ewrite_of_twrite f))

noeq
[@erasable] // very important, otherwise KReMLin will fail with argument typing
type valid_synth_t
  (p1: parser)
  (p2: parser)
=
| ValidSynth:
  (f: (dfst p1 -> GTot (dfst p2))) ->
  (v: LowParseWriters.valid_synth_t p1 p2 (fun _ -> True) f) ->
  valid_synth_t p1 p2

let tvalid_synth_of_evalid_synth
  (#p1: parser)
  (#p2: parser)
  (#precond: pre_t p1)
  (#f: (x: dfst p1 { precond x }) -> GTot (dfst p2))
  (v: LowParseWriters.valid_synth_t p1 p2 precond f)
: Pure (valid_synth_t p1 p2)
  (requires (forall (x: dfst p1) . precond x))
  (ensures (fun _ -> True))
= ValidSynth
    f
    (valid_synth_implies _ _ _ _ v _ _)

let evalid_synth_of_tvalid_synth_f
  (#p1: parser)
  (#p2: parser)
  (v: valid_synth_t p1 p2)
  (x: dfst p1)
: GTot (dfst p2)
=
  ValidSynth?.f v x

let evalid_synth_of_tvalid_synth
  (#p1: parser)
  (#p2: parser)
  (v: valid_synth_t p1 p2)
: Tot (LowParseWriters.valid_synth_t p1 p2 (fun _ -> True) (evalid_synth_of_tvalid_synth_f v))
= valid_synth_implies _ _ _ _ (ValidSynth?.v v) _ _

let valid_synth_compose
  (#p1: parser)
  (#p2: parser)
  (v12: valid_synth_t p1 p2)
  (#p3: parser)
  (v23: valid_synth_t p2 p3)
: Tot (valid_synth_t p1 p3)
= tvalid_synth_of_evalid_synth (valid_synth_compose _ _ _ _ (evalid_synth_of_tvalid_synth v12) _ _ _ (evalid_synth_of_tvalid_synth v23))

inline_for_extraction
let valid_synth
  (#p1: parser)
  (#p2: parser)
  (#inv: memory_invariant)
  (v: valid_synth_t p1 p2)
: TWrite unit p1 p2 inv
= twrite_of_ewrite (fun _ -> valid_synth _ _ _ _ _ (evalid_synth_of_tvalid_synth v))

inline_for_extraction
let cast
  (#p1: parser)
  (#p2: parser)
  (#inv: memory_invariant)
  (v: valid_synth_t p1 p2)
  (x1: ptr p1 inv)
: Tot (x2: ptr p2 inv {
    deref_spec x2 == ValidSynth?.f v (deref_spec x1)
  })
= cast _ _ _ _ (evalid_synth_of_tvalid_synth v) _ x1

let valid_synth_star_assoc_1
  (p1 p2 p3: parser)
: Tot (valid_synth_t ((p1 `star` p2) `star` p3) (p1 `star` (p2 `star` p3)))
= tvalid_synth_of_evalid_synth (valid_synth_star_assoc_1 p1 p2 p3)

let valid_synth_star_assoc_2
  (p1 p2 p3: parser)
: Tot (valid_synth_t (p1 `star` (p2 `star` p3)) ((p1 `star` p2) `star` p3))
= tvalid_synth_of_evalid_synth (valid_synth_star_assoc_2 p1 p2 p3)

let valid_synth_star_compat_l
  (p: parser)
  (#p1 #p2: parser)
  (v: valid_synth_t p1 p2)
: Tot (valid_synth_t (p `star` p1) (p `star` p2))
= tvalid_synth_of_evalid_synth (valid_synth_star_compat_l p _ _ _ _ (evalid_synth_of_tvalid_synth v))

let valid_synth_star_compat_r
  (p: parser)
  (#p1 #p2: parser)
  (v: valid_synth_t p1 p2)
: Tot (valid_synth_t (p1 `star` p) (p2 `star` p))
=
  tvalid_synth_of_evalid_synth (valid_synth_star_compat_r p _ _ _ _ (evalid_synth_of_tvalid_synth v))

inline_for_extraction
let cat
  (#inv: memory_invariant)
  (#p: parser)
  (x: ptr p inv)
: TWrite unit emp p inv
= twrite_of_ewrite (fun _ -> cat x)

inline_for_extraction
let start
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: dfst p)
: TWrite unit emp (p) l
= twrite_of_ewrite (fun _ -> start p w x)

inline_for_extraction
let append
  (#fr: parser)
  (p: parser)
  (w: LP.leaf_writer_strong (get_serializer p) {
    (get_parser_kind p).LP.parser_kind_high == Some (get_parser_kind p).LP.parser_kind_low
  })
  (#l: memory_invariant)
  (x: dfst p)
: TWrite unit fr (fr `star` p) l
= twrite_of_ewrite (fun _ -> append p w x)

let valid_synth_parser_eq'
  (p1: parser)
  (p2: parser {
    dfst p1 == dfst p2 /\
    get_parser_kind p1 == get_parser_kind p2 /\
    get_parser p1 == LP.coerce (LP.parser (get_parser_kind p1) (dfst p1)) (get_parser p2)
  })
: Tot (valid_synth_t p1 p2)
= tvalid_synth_of_evalid_synth (valid_synth_parser_eq p1 p2)

inline_for_extraction
let parse_vldata_intro_weak_ho'
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (f: (unit -> TWrite unit emp p inv))
: TWrite unit emp (parse_vldata p min max)
    inv
=
  twrite_of_ewrite (fun _ -> parse_vldata_intro_weak_ho' p min max (fun _ -> ewrite_of_twrite f))

inline_for_extraction
let parse_vldata_recast
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 (max')})
: TWrite unit (parse_vldata p min max) (parse_vldata p min' max') inv
= twrite_of_ewrite (fun _ -> parse_vldata_recast p min max min' max')

inline_for_extraction
let destr_list
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
: TRead (option (ptr p inv & lptr p inv)) inv
= tread_of_eread (fun _ -> destr_list x)

let list_exists
  (#p: parser1)
  (#inv: memory_invariant)
  (f_spec: Ghost.erased (dfst p -> Tot bool)) // reifying f below is not enough because of the ptr
  (f: ((x: ptr p inv) -> Read bool (True) (fun res -> res == Ghost.reveal f_spec (deref_spec x)) inv))
  (l: lptr p inv)
: TRead bool inv
= tread_of_eread (fun _ -> list_exists f_spec f l)

inline_for_extraction
let parse_vllist_nil
  (#inv: memory_invariant)
  (p: parser1)
  (max: U32.t { U32.v max > 0 })
: TWrite unit emp (parse_vllist p 0ul max) inv
= twrite_of_ewrite (fun _ -> parse_vllist_nil p max)

inline_for_extraction
let parse_vllist_snoc_weak
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: TWrite unit (parse_vllist p min max `star` p) (parse_vllist p min max)
    inv
=
  twrite_of_ewrite (fun _ -> parse_vllist_snoc_weak p min max)

inline_for_extraction
let parse_vllist_snoc_weak_ho'
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (f: (unit -> TWrite unit emp p inv))
: TWrite unit (parse_vllist p min max) (parse_vllist p min max) inv
=
  twrite_of_ewrite (fun _ -> parse_vllist_snoc_weak_ho' p min max (fun _ -> ewrite_of_twrite f))

let parse_vllist_recast
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (min': U32.t)
  (max': U32.t { U32.v min' <= U32.v max' /\ U32.v max' > 0 /\ log256 (max) == log256 (max')})
: TWrite unit (parse_vllist p min max) (parse_vllist p min' max') inv
=
  twrite_of_ewrite (fun _ -> parse_vllist_recast p min max min' max')

inline_for_extraction
let get_vlbytes
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (p: ptr (parse_vlbytes min max) inv)
: TRead
    (B.buffer LP.byte & U32.t)
    inv
= 
  tread_of_eread (fun _ -> get_vlbytes min max p)

inline_for_extraction
let put_vlbytes
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (len: U32.t { U32.v min <= U32.v len /\ U32.v len <= U32.v max })
  (l: Ghost.erased (Seq.seq LP.byte) { Seq.length l == U32.v len })
  (f: put_vlbytes_impl_t inv min max len l)
: TWrite unit emp (parse_vlbytes min max) inv
= twrite_of_ewrite (fun _ -> put_vlbytes min max len l f)

let list_map
  (p1 p2: parser1)
  (#inv: memory_invariant)
  (f: Ghost.erased (dfst p1 -> Tot (dfst p2)))
  (f' : (
    (x: ptr p1 inv) ->
    Write unit emp p2 (fun _ -> True) (fun _ _ out -> out == Ghost.reveal f (deref_spec x)) inv
  ))
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (l: lptr p1 inv)
: TWrite unit emp (parse_vllist p2 min max) inv
= twrite_of_ewrite (fun _ -> list_map p1 p2 f f' min max l)

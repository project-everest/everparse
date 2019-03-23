module LowParse.Low.Array

include LowParse.Spec.Array
include LowParse.Low.List
include LowParse.Low.VLData

module L = FStar.List.Tot
module M = LowParse.Math
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 16"

val list_nth_constant_size_parser_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
  (i: nat)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    Some? (parse (parse_list p) b) /\ (
    let (Some (l, _)) = parse (parse_list p) b in
    i < L.length l
  )))
  (ensures (
    let j = i `Prims.op_Multiply` k.parser_kind_low in
    0 <= j /\
    j + k.parser_kind_low <= Seq.length b /\ (
    let b' = Seq.slice b j (Seq.length b) in
    Some? (parse p b') /\ (
    let (Some (l, _)) = parse (parse_list p) b in
    let (Some (x, _)) = parse p b' in
    x == L.index l i
  ))))
  (decreases i)

let rec list_nth_constant_size_parser_correct #k #t p b i =
  parser_kind_prop_equiv k p;
  parse_list_eq p b;
  if i = 0
  then ()
  else begin
    M.mult_decomp i k.parser_kind_low;
    list_nth_constant_size_parser_correct p (Seq.slice b k.parser_kind_low (Seq.length b)) (i - 1)
  end

let clens_array_nth
  (t: Type)
  (elem_count: nat)
  (i: nat { i < elem_count } )
: Tot (clens (array t elem_count) t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (l: array t elem_count) -> L.index l i);
}

#reset-options // re-enable non-linear arith to prove that multiplying two nats yields a nat

abstract
let array_nth_ghost'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: nat {
    fldata_array_precond p array_byte_size elem_count == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    i < elem_count
  })
  (input: bytes)
: GTot (nat * nat)
= if (i `Prims.op_Multiply` k.parser_kind_low) + k.parser_kind_low <= Seq.length input
  then (i `Prims.op_Multiply` k.parser_kind_low, k.parser_kind_low)
  else (0, 0) // dummy

#reset-options "--z3cliopt smt.arith.nl=false"

abstract
let array_nth_ghost_correct'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: nat {
    fldata_array_precond p array_byte_size elem_count == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    i < elem_count
  })
  (input: bytes)
: Lemma
  (requires (gaccessor_pre (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i) input))
  (ensures (gaccessor_post' (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i) input (array_nth_ghost' s array_byte_size elem_count i input)))
= parser_kind_prop_equiv k p;
  fldata_to_array_inj s array_byte_size elem_count ();
  parse_synth_eq (parse_fldata_strong (serialize_list _ s) array_byte_size) (fldata_to_array s array_byte_size elem_count ()) input;
  list_nth_constant_size_parser_correct p input i;
  let off = i `Prims.op_Multiply` k.parser_kind_low in
  parse_strong_prefix p (Seq.slice input off (Seq.length input)) (Seq.slice input off (off + k.parser_kind_low))

abstract
let array_nth_ghost_correct
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: nat {
    fldata_array_precond p array_byte_size elem_count == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    i < elem_count
  })
  (input: bytes)
: Lemma
  (gaccessor_post' (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i) input (array_nth_ghost' s array_byte_size elem_count i input))
= Classical.move_requires (array_nth_ghost_correct' s array_byte_size elem_count i) input

abstract
let array_nth_ghost
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: nat {
    fldata_array_precond p array_byte_size elem_count == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    i < elem_count
  })
: Tot (gaccessor (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i))
= fun input -> ((
  array_nth_ghost_correct s array_byte_size elem_count i input;
  array_nth_ghost' s array_byte_size elem_count i input) <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i) input res)))

module B = LowStar.Buffer

inline_for_extraction
let array_nth
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: U32.t {
    fldata_array_precond p (array_byte_size) (elem_count) == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    U32.v i < elem_count
  })
: Tot (accessor (array_nth_ghost s (array_byte_size) (elem_count) (U32.v i)))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    parser_kind_prop_equiv k p;
    valid_facts (parse_array s (array_byte_size) (elem_count)) h input pos;
    slice_access_eq h (array_nth_ghost s (array_byte_size) (elem_count) (U32.v i)) input pos;
    fldata_to_array_inj s (array_byte_size) (elem_count) ();
    parse_synth_eq (parse_fldata_strong (serialize_list _ s) (array_byte_size)) (fldata_to_array s array_byte_size elem_count ()) (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
    list_nth_constant_size_parser_correct p (B.as_seq h (B.gsub (B.gsub input.base pos (input.len `U32.sub` pos)) 0ul (U32.uint_to_t array_byte_size))) (U32.v i)
  in
  pos `U32.add` (i `U32.mul` U32.uint_to_t k.parser_kind_low)

module HS = FStar.HyperStack

let valid_list_valid_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true /\
    U32.v array_byte_size32 == array_byte_size
  })
  (h: HS.mem)
  (input: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_list p h input pos pos' /\ (L.length (contents_list p h input pos pos') == elem_count \/ U32.v pos' - U32.v pos == array_byte_size)))
  (ensures (
    let x = contents_list p h input pos pos' in
    L.length x == elem_count /\
    U32.v pos' - U32.v pos == array_byte_size /\    
    valid_content_pos (parse_array s array_byte_size elem_count) h input pos x pos'
  ))
= valid_list_valid_exact_list p h input pos pos' ;
  valid_exact_equiv (parse_list p) h input pos pos' ;
  let len32 = pos' `U32.sub` pos in
  list_length_constant_size_parser_correct p (B.as_seq h (B.gsub (B.gsub input.base pos (input.len `U32.sub` pos)) 0ul len32));
  contents_exact_eq (parse_list p) h input pos pos';
  valid_facts (parse_fldata_strong (serialize_list _ s) array_byte_size) h input pos;
  valid_synth h (parse_fldata_strong (serialize_list _ s) array_byte_size) (fldata_to_array s array_byte_size elem_count ()) input pos

let valid_array_valid_list
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true /\
    U32.v array_byte_size32 == array_byte_size
  })
  (h: HS.mem)
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_array s array_byte_size elem_count) h input pos
  ))
  (ensures (
    let pos' = get_valid_pos (parse_array s array_byte_size elem_count) h input pos in
    let x = contents (parse_array s array_byte_size elem_count) h input pos in
    U32.v pos' - U32.v pos == array_byte_size /\
    valid_list p h input pos pos' /\
    contents_list p h input pos pos' == x
  ))
= 
    let pos' = get_valid_pos (parse_array s array_byte_size elem_count) h input pos in
    let x = contents (parse_array s array_byte_size elem_count) h input pos in
    valid_synth h (parse_fldata_strong (serialize_list _ s) array_byte_size) (fldata_to_array s array_byte_size elem_count ()) input pos;
    valid_facts (parse_fldata_strong (serialize_list _ s) array_byte_size) h input pos;
    valid_exact_equiv (parse_list p) h input pos pos' ;
    contents_exact_eq (parse_list p) h input pos pos' ;
    valid_exact_list_valid_list p h input pos pos'

inline_for_extraction
let validate_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true /\
    U32.v array_byte_size32 == array_byte_size
  })
: Tot (validator (parse_array s array_byte_size elem_count))
= validate_synth
    (validate_fldata_strong (serialize_list _ s) (validate_list v ()) array_byte_size array_byte_size32)
    (fldata_to_array s array_byte_size elem_count ())
    ()

inline_for_extraction
let jump_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true /\
    U32.v array_byte_size32 == array_byte_size
  })
: Tot (jumper (parse_array s array_byte_size elem_count))
= jump_constant_size (parse_array s array_byte_size elem_count) array_byte_size32 ()

inline_for_extraction
let validate_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (sz32: U32.t { U32.v sz32 == log256' array_byte_size_max /\ array_byte_size_max <= U32.v validator_max_length } )
: Tot (validator (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u))
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  validate_synth
    (validate_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) (validate_list v ()) ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())
    ()

inline_for_extraction
let jump_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (sz32: U32.t { U32.v sz32 == log256' array_byte_size_max } )
: Tot (jumper (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u))
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  jump_synth
    (jump_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())
    ()

inline_for_extraction
let finalize_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (sl: slice)
  (pos pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true /\ (
    let vpos1 = U32.v pos + log256' array_byte_size_max in
    vpos1 < 4294967296 /\ (
    let pos1 = U32.uint_to_t vpos1 in
    let len = U32.v pos' - vpos1 in
    valid_list p h sl pos1 pos' /\ (
    let count = L.length (contents_list p h sl pos1 pos') in
    ((array_byte_size_min <= len /\ len <= array_byte_size_max) \/ (elem_count_min <= count /\ count <= elem_count_max))
  )))))
  (ensures (fun h _ h' ->
    let pos1 = (U32.uint_to_t (U32.v pos + log256' array_byte_size_max)) in
    let l = contents_list p h sl pos1 pos' in
    B.modifies (loc_slice_from_to sl pos pos1) h h' /\
    elem_count_min <= L.length l /\ L.length l <= elem_count_max /\
    valid_content_pos (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) h' sl pos l pos'
  ))
= let h = HST.get () in
  let pos1 = pos `U32.add` U32.uint_to_t (log256' array_byte_size_max) in
  valid_list_valid_exact_list p h sl pos1 pos';
  let l = Ghost.hide (contents_list p h sl pos1 pos') in
  let _ : squash (let count = L.length (Ghost.reveal l) in elem_count_min <= count /\ count <= elem_count_max) =
    valid_exact_serialize (serialize_list _ s) h sl pos1 pos' ;
    Classical.move_requires (vldata_to_vlarray_correct array_byte_size_min array_byte_size_max s elem_count_min elem_count_max) (Ghost.reveal l) 
  in
  vlarray_to_vldata_correct array_byte_size_min array_byte_size_max s elem_count_min elem_count_max (Ghost.reveal l);
  finalize_bounded_vldata_strong_exact array_byte_size_min array_byte_size_max (serialize_list _ s) sl pos pos' ;
  let h = HST.get () in
  valid_synth h (parse_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s)) (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())  sl pos

let clens_vlarray_nth
  (t: Type)
  (min max: nat)
  (i: nat)
: Tot (clens (vlarray t min max) t)
= {
  clens_cond = (fun (l: vlarray t min max) -> i < L.length l);
  clens_get = (fun (l: vlarray t min max) -> L.index l i);
}

#reset-options // we need non-linear arithmetic here

#push-options "--z3rlimit 512"

inline_for_extraction
let vlarray_list_length
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (sl: slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true /\
    valid (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) h sl pos
  ))
  (ensures (fun h res h' ->
    let x = (contents (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) h sl pos) in
    let pos' = get_valid_pos (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) h sl pos in
    B.modifies B.loc_none h h' /\
    U32.v res == L.length x /\
    U32.v pos' == U32.v pos + (log256' array_byte_size_max) + (U32.v res `FStar.Mul.op_Star` k.parser_kind_low) /\
    valid_list p h sl (pos `U32.add` U32.uint_to_t (log256' array_byte_size_max)) pos' /\
    contents_list p h sl (pos `U32.add` U32.uint_to_t (log256' array_byte_size_max)) pos' == x
  ))
= let h = HST.get () in
  [@inline_let]
  let _ : unit =
    let l = contents (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) h sl pos in
    let sq = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
    valid_facts (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) h sl pos;
    valid_facts (parse_bounded_integer (log256' array_byte_size_max)) h sl pos;
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ();
    parse_synth_eq
      (parse_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s))
      (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())
      sq;
    parse_vldata_gen_eq (log256' array_byte_size_max) (in_bounds array_byte_size_min array_byte_size_max) (parse_list p) sq;
    let psq = parse (parse_bounded_integer (log256' array_byte_size_max)) sq in
    let Some (ln, _) = psq in
    list_length_constant_size_parser_correct p (Seq.slice sq (log256' array_byte_size_max) (log256' array_byte_size_max + U32.v ln));
    LowParse.Math.multiple_division_lemma (L.length l) k.parser_kind_low;
    let pos_payload = pos `U32.add` U32.uint_to_t (log256' array_byte_size_max) in
    let pos' = pos_payload `U32.add` ln in
    valid_exact_equiv (parse_list p) h sl pos_payload pos';
    contents_exact_eq (parse_list p) h sl pos_payload pos';
    valid_exact_list_valid_list p h sl pos_payload pos'
  in
  let blen = read_bounded_integer (log256' array_byte_size_max) sl pos in
  blen `U32.div` U32.uint_to_t k.parser_kind_low

#pop-options

#push-options "--z3rlimit 16"

abstract
let vlarray_nth_ghost'
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (i: nat {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (input: bytes)
: GTot (nat * nat)
= if (log256' array_byte_size_max + (i `Prims.op_Multiply` k.parser_kind_low) + k.parser_kind_low) <= Seq.length input
  then (log256' array_byte_size_max + (i `Prims.op_Multiply` k.parser_kind_low), k.parser_kind_low)
  else (0, 0) // dummy

#pop-options

#reset-options "--z3cliopt smt.arith.nl=false --z3refresh"

#push-options "--z3rlimit 16"

abstract
let vlarray_nth_ghost_correct'
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (i: nat {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (input: bytes)
: Lemma
  (requires (gaccessor_pre (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) p (clens_vlarray_nth t elem_count_min elem_count_max i) input))
  (ensures (gaccessor_post' (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) p (clens_vlarray_nth t elem_count_min elem_count_max i) input (vlarray_nth_ghost' array_byte_size_min array_byte_size_max s elem_count_min elem_count_max i input)))
= parse_vlarray_eq_some array_byte_size_min array_byte_size_max s elem_count_min elem_count_max () input;
  let input' = Seq.slice input (log256' array_byte_size_max) (Seq.length input) in
  assert (Some? (parse (parse_list p) input'));
  list_nth_constant_size_parser_correct p input' i;
  let off = i `Prims.op_Multiply` k.parser_kind_low in
  let ps = parse p (Seq.slice input' off (Seq.length input')) in
  assert (Some? ps);
  let Some (x, consumed) = ps in
  let f () : Lemma (consumed == k.parser_kind_low) =
    parser_kind_prop_equiv k p;
    M.le_antisym consumed k.parser_kind_low
  in
  f ();
  let s2 = Seq.slice input' off (off + k.parser_kind_low) in
  M.plus_minus_l off k.parser_kind_low;
  assert (Seq.length s2 == k.parser_kind_low);
  assert (Seq.slice (Seq.slice input' off (Seq.length input')) 0 consumed `Seq.equal` Seq.slice (Seq.slice input' off (off + k.parser_kind_low)) 0 consumed);
  parse_strong_prefix p (Seq.slice input' off (Seq.length input')) (Seq.slice input' off (off + k.parser_kind_low));
  let (pos, len) = vlarray_nth_ghost' array_byte_size_min array_byte_size_max s elem_count_min elem_count_max i input in
  assert (pos == log256' array_byte_size_max + off);
  assert (len == k.parser_kind_low);
  Seq.slice_slice input (log256' array_byte_size_max) (Seq.length input) off (off + k.parser_kind_low);
  M.addition_is_associative (log256' array_byte_size_max) off k.parser_kind_low;
  assert (log256' array_byte_size_max + (off + k.parser_kind_low) == pos + len);
  assert ((Seq.slice input pos (pos + len)) == (Seq.slice input' off (off + k.parser_kind_low)));
  assert (
    gaccessor_post' (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) p (clens_vlarray_nth t elem_count_min elem_count_max i) input (vlarray_nth_ghost' array_byte_size_min array_byte_size_max s elem_count_min elem_count_max i input)
  )

#pop-options

abstract
let vlarray_nth_ghost_correct
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (i: nat {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (input: bytes)
: Lemma
  (gaccessor_post' (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) p (clens_vlarray_nth t elem_count_min elem_count_max i) input (vlarray_nth_ghost' array_byte_size_min array_byte_size_max s elem_count_min elem_count_max i input))
= Classical.move_requires (vlarray_nth_ghost_correct' array_byte_size_min array_byte_size_max s elem_count_min elem_count_max i) input

abstract
let vlarray_nth_ghost
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (i: nat {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
: Tot (gaccessor (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) p (clens_vlarray_nth t elem_count_min elem_count_max i))
= fun input -> ((
  vlarray_nth_ghost_correct array_byte_size_min array_byte_size_max s elem_count_min elem_count_max i input;
  vlarray_nth_ghost' array_byte_size_min array_byte_size_max s elem_count_min elem_count_max i input) <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) p (clens_vlarray_nth t elem_count_min elem_count_max i) input res)))

module B = LowStar.Buffer

#push-options "--z3rlimit 16"

inline_for_extraction
let vlarray_nth
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (i: U32.t {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
: Tot (accessor (vlarray_nth_ghost array_byte_size_min array_byte_size_max s elem_count_min elem_count_max (U32.v i)))
= make_accessor_from_pure 
    (vlarray_nth_ghost array_byte_size_min array_byte_size_max s elem_count_min elem_count_max (U32.v i))
    (fun input ->
      [@inline_let] let _ =
        parse_vlarray_eq_some array_byte_size_min array_byte_size_max s elem_count_min elem_count_max () (Ghost.reveal input);
        let pi = parse (parse_bounded_integer (log256' array_byte_size_max)) (Ghost.reveal input) in
        let lc = Some?.v pi in
        let len = fst lc in
        let c_len = snd lc in
        list_nth_constant_size_parser_correct p (Seq.slice (Ghost.reveal input) (log256' array_byte_size_max) (Seq.length (Ghost.reveal input))) (U32.v i)
      in
      [@inline_let]
      let res = U32.uint_to_t (log256' array_byte_size_max) `U32.add` (i `U32.mul` U32.uint_to_t k.parser_kind_low) in
      res
    )

#pop-options

module HS = FStar.HyperStack

let valid_bounded_vldata_strong_list_valid_list
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (input: slice)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    valid (parse_bounded_vldata_strong min max (serialize_list _ s)) h input pos
  ))
  (ensures (
    let pos' = get_valid_pos (parse_bounded_vldata_strong min max (serialize_list _ s)) h input pos in
    U32.v pos + log256' max <= U32.v pos' /\ (
    let pos1 = pos `U32.add` U32.uint_to_t (log256' max) in
    valid_list p h input pos1 pos' /\
    contents_list p h input pos1 pos' == contents (parse_bounded_vldata_strong min max (serialize_list _ s)) h input pos /\
    True
  )))
= valid_bounded_vldata_strong_elim h min max (serialize_list _ s) input pos;
  let pos1 = pos `U32.add` U32.uint_to_t (log256' max) in
  let pos' = get_valid_pos (parse_bounded_vldata_strong min max (serialize_list _ s)) h input pos in
  valid_exact_list_valid_list p h input pos1 pos'

inline_for_extraction
let bounded_vldata_strong_list_payload_size
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (input: slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid (parse_bounded_vldata_strong min max (serialize_list _ s)) h input pos
  ))
  (ensures (fun h res h' ->
    let pos' = get_valid_pos (parse_bounded_vldata_strong min max (serialize_list _ s)) h input pos in
    B.modifies B.loc_none h h' /\
    U32.v pos + log256' max <= U32.v pos' /\ (
    let pos1 = pos `U32.add` U32.uint_to_t (log256' max) in
    res == pos' `U32.sub` pos1 /\
    valid_list p h input pos1 pos' /\
    contents_list p h input pos1 pos' == contents (parse_bounded_vldata_strong min max (serialize_list _ s)) h input pos /\
    True
  )))
= let h = HST.get () in
  let pos' = jump_bounded_vldata_strong min max (serialize_list _ s) () input pos in
  [@inline_let]
  let _ =
    assert (valid_pos (parse_bounded_vldata_strong min max (serialize_list _ s)) h input pos pos')
  in
  [@inline_let] let _ = valid_bounded_vldata_strong_list_valid_list min max p s input pos h in
  [@inline_let] let pos1 = pos `U32.add` U32.uint_to_t (log256' max) in
  [@inline_let] let res = pos' `U32.sub` pos1 in
  res

inline_for_extraction
let finalize_bounded_vldata_strong_list
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: slice)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_list p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    let len_ser = Seq.length (serialize (serialize_list _ s) (contents_list p h input pos_payload pos')) in
    ((min <= U32.v len_payload /\ U32.v len_payload <= max) \/ (min <= len_ser /\ len_ser <= max))
  ))))
  (ensures (fun h _ h' ->
    let sz = log256' max in
    let x = contents_list p h input (pos `U32.add` U32.uint_to_t sz) pos' in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    Seq.length (serialize (serialize_list _ s) x) == U32.v pos' - (U32.v pos + sz) /\
    parse_bounded_vldata_strong_pred min max (serialize_list _ s) x /\
    valid_content_pos (parse_bounded_vldata_strong min max (serialize_list _ s)) h' input pos x pos'
  ))
= let h = HST.get () in
  [@inline_let] let _ = valid_list_valid_exact_list p h input (pos `U32.add` U32.uint_to_t (log256' max)) pos' in
  finalize_bounded_vldata_strong_exact min max (serialize_list _ s) input pos pos'

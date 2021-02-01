module LowParse.Low.BitSum
include LowParse.Low.Combinators
include LowParse.Spec.BitSum

module U32 = FStar.UInt32
module HS = FStar.HyperStack

#push-options "--z3rlimit 16"

inline_for_extraction
let validate_bitsum'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#k: parser_kind)
  (#p: parser k t)
  (v: validator p)
  (r: leaf_reader p)
  (phi: filter_bitsum'_t b)
: Tot (validator (parse_bitsum' b p))
= synth_bitsum'_injective b;
  validate_synth
    (validate_filter
      v
      r
      (filter_bitsum' b)
      (fun x -> phi x))
    (synth_bitsum' b)
    ()

module HST = FStar.HyperStack.ST

inline_for_extraction
noextract
let validate_bitsum_cases_t
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#from: nat)
  (b: bitsum' cl from)
: Tot (Type u#(r+1))
= (u: (bitsum'_key_type b -> Tot (Type u#r))) ->
  (f: ((x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (u x)))) ->
  (v: ((x: bitsum'_key_type b) -> Tot (validator (dsnd (f x))))) ->
  (x: parse_filter_refine (filter_bitsum' b)) ->
  Tot (validator (dsnd (f (bitsum'_key_of_t b (synth_bitsum' b x)))))

inline_for_extraction
let validate_bitsum_cases_bitstop
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
: Tot (validate_bitsum_cases_t u#r #tot #t #cl #0 (BitStop ()))
= fun u f v x #rrel #rel sl pos ->
  v () sl pos

inline_for_extraction
let validate_bitsum_cases_bitfield
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (phi: validate_bitsum_cases_t u#r rest)
: Tot (validate_bitsum_cases_t u#r (BitField sz rest))
= fun u f v x #rrel #rel sl pos ->
  phi
    (fun x -> u (coerce (bitsum'_key_type (BitField sz rest)) x))
    (fun x -> f (coerce (bitsum'_key_type (BitField sz rest)) x))
    (fun x -> v (coerce (bitsum'_key_type (BitField sz rest)) x))
    x
    sl
    pos

inline_for_extraction
let validate_bitsum_cases_bitsum_gen
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (key_of: ((x: enum_repr e) -> Tot (y: enum_key e { y == enum_key_of_repr e x })))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (destr_payload: ((k: enum_key e) -> Tot (validate_bitsum_cases_t u#r (payload k))))
: Tot (validate_bitsum_cases_t u#r (BitSum' key key_size e payload))
= fun u f v x_ #rrel #rel sl pos ->
      [@inline_let]
      let r = cl.get_bitfield x_ (bitsum'_size - key_size) bitsum'_size in
      [@inline_let]
      let k = key_of r in
      destr_payload 
        k
        (fun x -> u (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        (fun x -> f (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        (fun x -> v (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        x_ sl pos

module L = FStar.List.Tot

inline_for_extraction
noextract
let validate_bitsum_cases_bitsum'_t
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
: Tot (Type u#(r+1))
= (u: (bitsum'_key_type (BitSum' key key_size e payload) -> Tot (Type u#r))) ->
  (f: ((x: bitsum'_key_type (BitSum' key key_size e payload)) -> Tot (k: parser_kind & parser k (u x)))) ->
  (v: ((x: bitsum'_key_type (BitSum' key key_size e payload)) -> Tot (validator (dsnd (f x))))) ->
  (x: parse_filter_refine (filter_bitsum' (BitSum' key key_size e payload)) { ~ (list_mem (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) (list_map snd l1)) }) ->
  (xr: t { xr == cl.bitfield_eq_lhs x (bitsum'_size - key_size) bitsum'_size }) ->
  Tot (validator (dsnd (f (bitsum'_key_of_t (BitSum' key key_size e payload) (synth_bitsum' (BitSum' key key_size e payload) x)))))

inline_for_extraction
let validate_bitsum_cases_bitsum'_intro
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (phi: validate_bitsum_cases_bitsum'_t u#r cl bitsum'_size key key_size e payload [] e)
: Tot (validate_bitsum_cases_t u#r (BitSum' key key_size e payload))
= fun u f v x #rrel #rel sl pos ->
    let xr = cl.bitfield_eq_lhs x (bitsum'_size - key_size) bitsum'_size in
    phi u f v x xr sl pos

inline_for_extraction
let validate_bitsum_cases_bitsum'_nil
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (h: squash (e == e `L.append` []))
: Tot (validate_bitsum_cases_bitsum'_t u#r cl bitsum'_size key key_size e payload e [])
= (fun u f v x xr #rrel #rel sl pos ->
    assert False;
    validator_error_generic (* dummy *))

#push-options "--z3rlimit 32"

inline_for_extraction
let validate_bitsum_cases_bitsum'_cons
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (k: key)
  (r: bitfield cl key_size)
  (l2: list (key & bitfield cl key_size) { 
    e == l1 `L.append` ((k, r) :: l2) /\
    list_mem k (list_map fst e) /\
    enum_repr_of_key e k == r /\
    e == (l1 `L.append` [(k, r)]) `L.append` l2
  })
  (destr_payload: validate_bitsum_cases_t u#r (payload k))
  (destr_tail: validate_bitsum_cases_bitsum'_t u#r cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) l2)
: Tot (validate_bitsum_cases_bitsum'_t u#r cl bitsum'_size key key_size e payload l1 ((k, r) :: l2))
= fun u f v x xr #rrel #rel sl pos ->
    // [@inline_let]
    let _ =
      enum_repr_of_key_append_cons e l1 (k, r) l2
    in
    [@inline_let] let yr = cl.bitfield_eq_rhs x (bitsum'_size - key_size) bitsum'_size r in
    [@inline_let] let cond = (xr <: t) = yr in
    [@inline_let] let _ = 
      assert (cond == true <==> (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) == r)
    in
    if cond
    then
      destr_payload 
        (fun x -> u (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        (fun x -> f (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        (fun x -> v (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        x sl pos
    else
      [@inline_let] let _ =
        L.append_assoc l1 [(k, r)] l2;
        L.map_append snd l1 [(k, r)];
        L.append_mem (L.map snd l1) (L.map snd [(k, r)]) (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size)
      in
      destr_tail u f v (x <: t) xr sl pos

[@filter_bitsum'_t_attr]
noextract
let rec mk_validate_bitsum_cases_bitsum'_t'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
  (mk_validate_bitsum_cases_t':
    (* universe-polymorphic mutually recursive functions must be "split off"
       cf. https://github.com/FStarLang/FStar/issues/1480#issuecomment-623260544
     *)
    (b: bitsum' cl (bitsum'_size - key_size) { b << BitSum' key key_size e payload }) ->
    Tot (validate_bitsum_cases_t u#r b)
  )
: Tot (validate_bitsum_cases_bitsum'_t u#r cl bitsum'_size key key_size e payload l1 l2)
      (decreases %[BitSum' key key_size e payload; l2])
= bitsum_wellfoundedness (BitSum' key key_size e payload);
  match l2 with
  | [] ->
    [@inline_let] let _ =
      L.append_l_nil l1
    in
    validate_bitsum_cases_bitsum'_nil cl bitsum'_size key key_size e payload ()
  | (k, r) :: q ->
    [@inline_let] let _ =
      enum_repr_of_key_append_cons e l1 (k, r) q;
      L.append_assoc l1 [(k, r)] q
    in  
    validate_bitsum_cases_bitsum'_cons cl bitsum'_size key key_size e payload l1 k r q
      (mk_validate_bitsum_cases_t' (payload k))
      (mk_validate_bitsum_cases_bitsum'_t' cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) q mk_validate_bitsum_cases_t')

[@filter_bitsum'_t_attr]
noextract
let rec mk_validate_bitsum_cases_t'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot (validate_bitsum_cases_t u#r b)
  (decreases b)
= match b with
  | BitStop _ -> validate_bitsum_cases_bitstop cl
  | BitField sz rest -> validate_bitsum_cases_bitfield cl bitsum'_size sz rest (mk_validate_bitsum_cases_t' rest)
  | BitSum' key key_size e payload ->
    validate_bitsum_cases_bitsum'_intro cl bitsum'_size key key_size e payload (mk_validate_bitsum_cases_bitsum'_t' cl bitsum'_size key key_size e payload [] e (mk_validate_bitsum_cases_t' #tot #t #cl #(bitsum'_size - key_size)))

#push-options "--z3rlimit 64"
#restart-solver

inline_for_extraction
let validate_bitsum
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (v: validator p)
  (r: leaf_reader p)
  (phi: filter_bitsum'_t b)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (vf: (x: bitsum'_key_type b) -> Tot (validator (dsnd (f x))))
  (vs: validate_bitsum_cases_t b)
: Tot (validator (parse_bitsum b tag_of_data type_of_tag synth_case p f))
= fun #rrel #rel sl pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    valid_facts (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl (uint64_to_uint32 pos);
    parse_bitsum_eq b tag_of_data type_of_tag synth_case p f (bytes_of_slice_from h sl (uint64_to_uint32 pos));
    valid_facts (parse_bitsum' b p) h sl (uint64_to_uint32 pos)
  in
  let pos1 = validate_bitsum' b v r phi sl pos in
  if is_error pos1
  then pos1
  else
    [@inline_let] let _ =
      synth_bitsum'_injective b;
      parse_synth_eq (p `parse_filter` filter_bitsum' b) (synth_bitsum' b) (bytes_of_slice_from h sl (uint64_to_uint32 pos));
      parse_filter_eq p (filter_bitsum' b) (bytes_of_slice_from h sl (uint64_to_uint32 pos));
      valid_facts p h sl (uint64_to_uint32 pos)
    in
    let x = r sl (uint64_to_uint32 pos) in
    [@inline_let]
    let _ =
      let y = synth_bitsum' b x in
      let tg = bitsum'_key_of_t b y in 
      parse_synth_eq (dsnd (f tg)) (synth_case.f y) (bytes_of_slice_from h sl (uint64_to_uint32 pos1));
      valid_facts (dsnd (f tg)) h sl (uint64_to_uint32 pos1)
    in
    vs (type_of_tag) f vf x sl pos1

#pop-options

let valid_bitsum_intro
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (p: parser kt t)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (h: HS.mem)
  (#rrel: _)
  (#rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bitsum' b p) h sl pos /\ (
    let tg = contents (parse_bitsum' b p) h sl pos in
    let k = bitsum'_key_of_t b tg in
    valid (dsnd (f k)) h sl (get_valid_pos (parse_bitsum' b p) h sl pos)
  )))
  (ensures (
    let tg = contents (parse_bitsum' b p) h sl pos in
    let k = bitsum'_key_of_t b tg in
    let pos1 = get_valid_pos (parse_bitsum' b p) h sl pos in
    let y = contents (dsnd (f k)) h sl pos1 in
    valid_content_pos (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos (synth_case.f tg y) (get_valid_pos (dsnd (f k)) h sl pos1)
  ))
= valid_facts (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos;
  parse_bitsum_eq b tag_of_data type_of_tag synth_case p f (bytes_of_slice_from h sl pos);
  valid_facts (parse_bitsum' b p) h sl pos;
  let tg = contents (parse_bitsum' b p) h sl pos in
  let k = bitsum'_key_of_t b tg in
  let pos1 = get_valid_pos (parse_bitsum' b p) h sl pos in
  valid_facts (dsnd (f k)) h sl pos1

#pop-options

let valid_bitsum_elim'
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (p: parser kt t)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (h: HS.mem)
  (#rrel: _)
  (#rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos
  ))
  (ensures (
    valid (parse_bitsum' b p) h sl pos /\ (
    let tg = contents (parse_bitsum' b p) h sl pos in
    let k = bitsum'_key_of_t b tg in
    let pos1 = get_valid_pos (parse_bitsum' b p) h sl pos in
    valid (dsnd (f k)) h sl pos1 /\ (
    let y = contents (dsnd (f k)) h sl pos1 in
    valid_content_pos (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos (synth_case.f tg y) (get_valid_pos (dsnd (f k)) h sl pos1)
  ))))
= valid_facts (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos;
  parse_bitsum_eq b tag_of_data type_of_tag synth_case p f (bytes_of_slice_from h sl pos);
  valid_facts (parse_bitsum' b p) h sl pos;
  let tg = contents (parse_bitsum' b p) h sl pos in
  let k = bitsum'_key_of_t b tg in
  let pos1 = get_valid_pos (parse_bitsum' b p) h sl pos in
  valid_facts (dsnd (f k)) h sl pos1;
  valid_bitsum_intro b tag_of_data type_of_tag synth_case p f h sl pos

let valid_bitsum_elim
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (p: parser kt t)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (h: HS.mem)
  (#rrel: _)
  (#rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos
  ))
  (ensures (
    valid p h sl pos /\ (
    let x = contents p h sl pos in
    filter_bitsum' b x == true /\ (
    let tg = synth_bitsum' b x in
    let k = bitsum'_key_of_t b tg in
    let pos1 = get_valid_pos p h sl pos in
    valid (dsnd (f k)) h sl pos1 /\
    valid_pos (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos (get_valid_pos (dsnd (f k)) h sl pos1) /\ (
    let x = contents (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos in
    let y = contents (dsnd (f k)) h sl pos1 in
    tg == tag_of_data x /\
    x == synth_case.f tg y /\
    y == synth_case.g tg x
  )))))
= valid_bitsum_elim' b tag_of_data type_of_tag synth_case p f h sl pos;
  synth_bitsum'_injective b;
  assert (valid ((p `parse_filter` filter_bitsum' b) `parse_synth` synth_bitsum' b) h sl pos);
  valid_synth h (p `parse_filter` filter_bitsum' b) (synth_bitsum' b) sl pos;
  valid_filter h p (filter_bitsum' b) sl pos;
  let tg = synth_bitsum' b (contents p h sl pos) in  
  let tg = contents (parse_bitsum' b p) h sl pos in
  let k = bitsum'_key_of_t b tg in
  let pos1 = get_valid_pos (parse_bitsum' b p) h sl pos in
  let x = contents (parse_bitsum b tag_of_data type_of_tag synth_case p f) h sl pos in
  let y = contents (dsnd (f k)) h sl pos1 in
  assert (tg == tag_of_data x);
  assert (x == synth_case.f tg y);
  synth_case.f_g_eq tg x;
  synth_case.f_inj tg (synth_case.g tg x) y

#pop-options

module LowParseExample7.Aux

module LP = LowParse.Spec
module B32 = FStar.Bytes
module U32 = FStar.UInt32

#reset-options "--using_facts_from '* -FStar.Reflection.* -FStar.Tactics.* -FStar.UInt32 -FStar.UInt8 -LowParse.*'"

module L = FStar.List.Tot

(*
let rec list_init_last (#t: Type) (l: list t) : Lemma
  (requires (Cons? l))
  (ensures (l == L.append (L.init l) [L.last l]))
= match l with
  | [_] -> ()
  | a :: b :: q ->
    list_init_last (b :: q);
    assert (a :: b :: q == [a] `L.append` (b :: q));
    assert (L.init (a :: b :: q) == [a] `L.append` L.init (b :: q));
    assert (L.last (a :: b :: q) == L.last (b :: q));
    L.append_assoc [a] (L.init (b :: q)) [L.last (b :: q)]

#reset-options

let list_init_last_recip (#t: Type) (init: list t) (last: t) : Lemma
  (let l = L.append init [last] in
  Cons? l /\
  L.init l == init /\ L.last l == last
  )
= let l = L.append init [last] in
  assert (L.length l > 0);
  list_init_last l;
  L.append_length_inv_tail (L.init l) [L.last l] init [last]

// NOTE: parse_bounded_vlbytes_t is only the vlbytes payload, it does not include its length
type binders = LP.parse_bounded_vlbytes_t 0 65535
let parse_binders : LP.parser _ binders = LP.parse_bounded_vlbytes 0 65535
let serialize_binders: LP.serializer parse_binders = LP.serialize_bounded_vlbytes 0 65535

type pre_shared_key_extension = (U32.t * binders)
let parse_pre_shared_key_extension : LP.parser _ pre_shared_key_extension = LP.nondep_then LP.parse_u32 parse_binders
let serialize_pre_shared_key_extension : LP.serializer parse_pre_shared_key_extension = LP.serialize_nondep_then _ LP.serialize_u32 () _ serialize_binders

type extension_type = | PreSharedKeyExtension_t

inline_for_extraction
let extension_enum : LP.enum extension_type U32.t =
  let l : list (extension_type * U32.t) = [
    PreSharedKeyExtension_t, 18ul;
  ]
  in
  assert_norm (L.noRepeats (LP.list_map fst l) /\ L.noRepeats (LP.list_map snd l));
  l

noeq
type extension =
| PreSharedKeyExtension of LP.parse_bounded_vldata_strong_t 2 65535 serialize_pre_shared_key_extension
| UnknownExtension of (LP.unknown_enum_repr extension_enum * LP.parse_bounded_vlbytes_t 2 65535)

let type_of_extension (e: extension) : GTot (LP.maybe_enum_key extension_enum) =
  match e with
  | PreSharedKeyExtension _ -> LP.Known PreSharedKeyExtension_t
  | UnknownExtension (u, _) -> LP.Unknown u

inline_for_extraction
let extension_sum : LP.dsum =
  LP.make_dsum extension_enum type_of_extension

inline_for_extraction
let synth_pre_shared_extension (z: LP.parse_bounded_vldata_strong_t 2 65535 serialize_pre_shared_key_extension) : Tot (LP.dsum_cases extension_sum (LP.Known PreSharedKeyExtension_t)) =
  PreSharedKeyExtension z

let synth_pre_shared_extension_inj () : Lemma
  (LP.synth_injective synth_pre_shared_extension)
= ()

let parse_known_extension (x: LP.dsum_known_key extension_sum) : Tot (k: LP.parser_kind & LP.parser k (LP.dsum_cases extension_sum (LP.Known x))) =
  match x with
  | PreSharedKeyExtension_t ->
    (| _, LP.parse_bounded_vldata_strong 2 65535 serialize_pre_shared_key_extension `LP.parse_synth` synth_pre_shared_extension |)

inline_for_extraction
let synth_unknown_extension (u: LP.dsum_unknown_key extension_sum) (z: LP.parse_bounded_vlbytes_t 2 65535) : Tot (LP.dsum_cases extension_sum (LP.Unknown u)) =
  UnknownExtension (u, z)

let synth_unknown_extension_inj (u: LP.dsum_unknown_key extension_sum) : Lemma
  (LP.synth_injective (synth_unknown_extension u))
= ()

let parse_unknown_extension (x: LP.dsum_unknown_key extension_sum) : Tot (LP.parser _ (LP.dsum_cases extension_sum (LP.Unknown x))) =
  LP.parse_bounded_vlbytes 2 65535 `LP.parse_synth` (synth_unknown_extension x)

let parse_extension_cases (x: LP.dsum_key extension_sum) : Tot (LP.parser _ (LP.dsum_cases extension_sum x)) =
  LP.parse_dsum_cases extension_sum parse_known_extension parse_unknown_extension x

let parse_extension : LP.parser _ extension = LP.parse_dsum extension_sum LP.parse_u32 parse_extension_cases

inline_for_extraction
let synth_pre_shared_extension_recip (z: LP.dsum_cases extension_sum (LP.Known PreSharedKeyExtension_t)) : Tot (LP.parse_bounded_vldata_strong_t 2 65535 serialize_pre_shared_key_extension) =
  match z with
  | PreSharedKeyExtension x -> x

let synth_pre_shared_extension_inv () : Lemma (LP.synth_inverse synth_pre_shared_extension synth_pre_shared_extension_recip) =
  let f
    (x: LP.dsum_cases extension_sum (LP.Known PreSharedKeyExtension_t))
  : Lemma
    (synth_pre_shared_extension (synth_pre_shared_extension_recip x) == x)
  = assert_norm (synth_pre_shared_extension (synth_pre_shared_extension_recip x) == x)
  in
  Classical.forall_intro f

let serialize_known_extension (x: LP.dsum_known_key extension_sum) : Tot (LP.serializer (dsnd (parse_known_extension x))) =
  match x with
  | PreSharedKeyExtension_t ->
    synth_pre_shared_extension_inj ();
    synth_pre_shared_extension_inv ();
    LP.serialize_synth
      _
      synth_pre_shared_extension
      (LP.serialize_bounded_vldata_strong 2 65535 serialize_pre_shared_key_extension)
      synth_pre_shared_extension_recip
      ()

inline_for_extraction
let synth_unknown_extension_recip (x: LP.dsum_unknown_key extension_sum) (z: LP.dsum_cases extension_sum (LP.Unknown x)) : Tot (LP.parse_bounded_vlbytes_t 2 65535) =
  match z with
  | UnknownExtension (_, y) -> y

let synth_inverse_intro'
  (#t1: Type0)
  (#t2: Type0)
  (f2: (t1 -> GTot t2))
  (g1: (t2 -> GTot t1))
  (f: ((x: t2) -> Lemma (f2 (g1 x) == x)))
: Lemma
  (LP.synth_inverse f2 g1)
= Classical.forall_intro f

#set-options "--z3rlimit 32"

let synth_unknown_extension_inv (x: LP.dsum_unknown_key extension_sum) : Lemma
  (LP.synth_inverse (synth_unknown_extension x) (synth_unknown_extension_recip x))
= let f
    (z: LP.dsum_cases extension_sum (LP.Unknown x))
  : Lemma
    (synth_unknown_extension x (synth_unknown_extension_recip x z) == z)
  = match z with
    | UnknownExtension (x', y) ->
      assert (type_of_extension z == LP.Unknown x);
      assert (type_of_extension z == LP.Unknown x'); // Z3 chokes on this one
      assert (x' == x);
      assert (synth_unknown_extension x (synth_unknown_extension_recip x z) == z)
  in
  synth_inverse_intro' (synth_unknown_extension x) (synth_unknown_extension_recip x) f

#reset-options

let serialize_unknown_extension (x: LP.dsum_unknown_key extension_sum) : Tot (LP.serializer (parse_unknown_extension x)) =
  synth_unknown_extension_inv x;
  LP.serialize_synth
    _
    (synth_unknown_extension x)
    (LP.serialize_bounded_vlbytes 2 65535)
    (synth_unknown_extension_recip x)
    ()

let serialize_extension_cases (x: LP.dsum_key extension_sum) : Tot (LP.serializer (parse_extension_cases x)) =
  LP.serialize_dsum_cases
    extension_sum
    parse_known_extension
    serialize_known_extension
    parse_unknown_extension
    serialize_unknown_extension
    x

let serialize_extension : LP.serializer parse_extension =
  LP.serialize_dsum extension_sum LP.serialize_u32 serialize_extension_cases

type extensions = LP.parse_bounded_vldata_strong_t 0 65535 (LP.serialize_list _ serialize_extension)
let parse_extensions : LP.parser _ extensions = LP.parse_bounded_vldata_strong 0 65535 (LP.serialize_list _ serialize_extension)
let serialize_extensions : LP.serializer parse_extensions = LP.serialize_bounded_vldata_strong 0 65535 (LP.serialize_list _ serialize_extension)

type cipher_suites = LP.parse_bounded_vldata_strong_t 0 65535 (LP.serialize_list _ (LP.serialize_flbytes 2))
let parse_cipher_suites : LP.parser _ cipher_suites = LP.parse_bounded_vldata_strong 0 65535 (LP.serialize_list _ (LP.serialize_flbytes 2))
let serialize_cipher_suites : LP.serializer parse_cipher_suites = LP.serialize_bounded_vldata_strong 0 65535 (LP.serialize_list _ (LP.serialize_flbytes 2))

type client_hello = (cipher_suites * extensions)
let parse_client_hello : LP.parser _ client_hello = parse_cipher_suites `LP.nondep_then` parse_extensions
let serialize_client_hello : LP.serializer parse_client_hello =
  LP.serialize_nondep_then
    _
    serialize_cipher_suites
    ()
    _
    serialize_extensions

let with_psk
  (ch: client_hello)
: GTot Type0
= let (_, exts) = ch in
  Cons? exts /\
  PreSharedKeyExtension? (L.last exts)

let get_binders
  (ch: client_hello { with_psk ch } )
: GTot binders
= let (_, exts) = ch in
  let (PreSharedKeyExtension (_, b)) = L.last exts in
  b

let get_psk_id
  (ch: client_hello { with_psk ch } )
: GTot U32.t
= let (_, exts) = ch in
  let (PreSharedKeyExtension (i, _)) = L.last exts in
  i

#reset-options "--z3rlimit 16"

let set_binders
  (ch: client_hello { with_psk ch } )
  (b' : B32.bytes { B32.length b' == B32.length (get_binders ch) } )
: Ghost client_hello
  (requires True)
  (ensures (fun ch' ->
    let s = LP.serialize serialize_client_hello ch in
    with_psk ch' /\
    fst ch' == fst ch /\
    L.init (snd ch') == L.init (snd ch) /\
    get_psk_id ch' == get_psk_id ch /\
    get_binders ch' == b' /\
    B32.length b' <= Seq.length s /\
    LP.serialize serialize_client_hello ch' == LP.seq_upd_bw_seq s 0 (B32.reveal b')
  ))
= let (cs, exts) = ch in
  let last : extension = L.last exts in
  let last : LP.dsum_cases extension_sum (LP.Known PreSharedKeyExtension_t) = last in
  let (PreSharedKeyExtension ps) = last in
  let (i, b) = ps in
  LP.serialize_bounded_vlbytes_upd_bw 0 65535 b b';
  let rb' = B32.reveal b' in
  let b' : binders = b' in
  LP.serialize_nondep_then_upd_bw_right_chain _ LP.serialize_u32 () _ serialize_binders ps b' 0 rb';
  let ps' : pre_shared_key_extension = (i, b') in
  LP.serialize_bounded_vldata_strong_upd_bw_chain 2 65535 serialize_pre_shared_key_extension ps ps' 0 rb';
  let ps' : LP.parse_bounded_vldata_strong_t 2 65535 serialize_pre_shared_key_extension = ps' in
  let last' : extension = PreSharedKeyExtension ps' in
  assert_norm (LP.dsum_tag_of_data extension_sum last' == LP.Known PreSharedKeyExtension_t);
  let last' : LP.dsum_cases extension_sum (LP.Known PreSharedKeyExtension_t) = last' in
  synth_pre_shared_extension_inj ();
  synth_pre_shared_extension_inv ();
  assert_norm (synth_pre_shared_extension ps == last);
  assert_norm (synth_pre_shared_extension ps' == last');
  LP.serialize_synth_upd_bw_chain _ synth_pre_shared_extension (LP.serialize_bounded_vldata_strong 2 65535 serialize_pre_shared_key_extension) synth_pre_shared_extension_recip () ps  last ps' last' 0 rb';
  assert_norm (LP.serialize (serialize_extension_cases (LP.Known PreSharedKeyExtension_t)) last == LP.serialize (LP.serialize_synth _ synth_pre_shared_extension (LP.serialize_bounded_vldata_strong 2 65535 serialize_pre_shared_key_extension) synth_pre_shared_extension_recip ()) last);
  assert_norm (LP.serialize (serialize_extension_cases (LP.Known PreSharedKeyExtension_t)) last' == LP.serialize (LP.serialize_synth _ synth_pre_shared_extension (LP.serialize_bounded_vldata_strong 2 65535 serialize_pre_shared_key_extension) synth_pre_shared_extension_recip ()) last');
  LP.serialize_dsum_upd_bw_chain extension_sum LP.serialize_u32 serialize_extension_cases last last' 0 rb';
  let init = L.init exts in
  assert_norm (LP.serialize_list_precond (LP.get_parser_kind parse_extension));
  LP.serialize_list_snoc_upd_bw_chain serialize_extension init last last' 0 rb';
  list_init_last exts;
  let exts' = L.append init [last'] in
  LP.serialize_bounded_vldata_strong_upd_bw_chain 0 65535 (LP.serialize_list _ serialize_extension) exts exts' 0 rb';
  let exts' : extensions = exts' in
  LP.serialize_nondep_then_upd_bw_right_chain _ serialize_cipher_suites () _ serialize_extensions ch exts' 0 rb';
  let ch' : client_hello = (cs, exts') in
  assert (LP.serialize serialize_client_hello ch' == LP.seq_upd_bw_seq (LP.serialize serialize_client_hello ch) 0 (B32.reveal b'));
  list_init_last_recip init last';
  assert (
    with_psk ch' /\
    fst ch' == fst ch /\
    L.init (snd ch') == L.init (snd ch) /\
    get_psk_id ch' == get_psk_id ch /\
    get_binders ch' == b' /\
    B32.length b' <= Seq.length (LP.serialize serialize_client_hello ch) /\
    True
  );
  ch'

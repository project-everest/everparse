module CBOR.Pulse.API.Nondet.C
#lang-pulse
module Rust = CBOR.Pulse.API.Nondet.Rust

[@@pulse_unfold]
let cbor_nondet_match = Rust.cbor_nondet_match

let cbor_nondet_reset_perm () = Rust.cbor_nondet_reset_perm ()

let cbor_nondet_share = Rust.cbor_nondet_share

let cbor_nondet_gather = Rust.cbor_nondet_gather

let cbor_nondet_parse () = cbor_nondet_parse_from_arrayptr (Rust.cbor_nondet_validate ()) (Rust.cbor_nondet_parse_valid ())

let cbor_nondet_match_with_size = Rust.cbor_nondet_match_with_size

let cbor_nondet_match_with_size_intro () = Rust.cbor_nondet_match_with_size_intro ()

let cbor_nondet_size () x bound #p #x' #v = Rust.cbor_nondet_size () x bound #p #x' #v

let cbor_nondet_serialize () = cbor_nondet_serialize_to_arrayptr (Rust.cbor_nondet_serialize ())

let cbor_nondet_major_type () x #p #y = Rust.cbor_nondet_major_type () x #p #y

let cbor_nondet_read_simple_value () = read_simple_value_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_simple_value ())

let cbor_nondet_elim_simple () = Rust.cbor_nondet_elim_simple ()

let cbor_nondet_read_uint64 () = read_uint64_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_uint64 ())

let cbor_nondet_read_int64 () = read_int64_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_read_uint64 ())

let cbor_nondet_elim_int64 () = Rust.cbor_nondet_elim_int64 ()

let cbor_nondet_get_string () = get_string_as_arrayptr_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_string_length ()) (get_string_as_arrayptr (Rust.cbor_nondet_get_string ()))

let cbor_nondet_get_byte_string () = get_string_as_arrayptr_safe_gen (cbor_nondet_major_type ()) (cbor_nondet_get_string ()) _

let cbor_nondet_get_text_string () = get_string_as_arrayptr_safe_gen (cbor_nondet_major_type ()) (cbor_nondet_get_string ()) _

let cbor_nondet_get_tagged () = get_tagged_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_tagged_tag ()) (Rust.cbor_nondet_get_tagged_payload ())

let cbor_nondet_get_array_length () = get_array_length_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_array_length ())

let cbor_nondet_array_iterator_match = Rust.cbor_nondet_array_iterator_match

let cbor_nondet_array_iterator_start () = array_iterator_start_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_array_iterator_start ())

let cbor_nondet_array_iterator_is_empty () x #p #y = Rust.cbor_nondet_array_iterator_is_empty () x #p #y

let cbor_nondet_array_iterator_length () x #p #y = Rust.cbor_nondet_array_iterator_length () x #p #y

let cbor_nondet_array_iterator_next () = array_iterator_next_safe (cbor_nondet_array_iterator_is_empty ()) (Rust.cbor_nondet_array_iterator_next ())

let cbor_nondet_array_iterator_truncate () x len #p #y = Rust.cbor_nondet_array_iterator_truncate () x len #p #y

let cbor_nondet_array_iterator_share () = Rust.cbor_nondet_array_iterator_share ()

let cbor_nondet_array_iterator_gather () = Rust.cbor_nondet_array_iterator_gather ()

let cbor_nondet_get_array_item () = get_array_item_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_array_length ()) (Rust.cbor_nondet_get_array_item ())

let cbor_nondet_get_map_length () = get_map_length_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_get_map_length ())

let cbor_nondet_map_iterator_match = Rust.cbor_nondet_map_iterator_match

let cbor_nondet_map_iterator_start () = map_iterator_start_safe (cbor_nondet_major_type ()) (Rust.cbor_nondet_map_iterator_start ())

let cbor_nondet_map_iterator_is_empty () x #p #y = Rust.cbor_nondet_map_iterator_is_empty () x #p #y

let cbor_nondet_map_entry_match = Rust.cbor_nondet_map_entry_match

let cbor_nondet_map_entry_key () x #p #y = Rust.cbor_nondet_map_entry_key () x #p #y

let cbor_nondet_map_entry_value () x #p #y = Rust.cbor_nondet_map_entry_value () x #p #y

let cbor_nondet_map_iterator_next () = map_iterator_next_safe (cbor_nondet_map_iterator_is_empty ()) (Rust.cbor_nondet_map_iterator_next ()) (Rust.cbor_nondet_map_entry_share ()) (Rust.cbor_nondet_map_entry_gather ()) (cbor_nondet_map_entry_key ()) (cbor_nondet_map_entry_value ())

let cbor_nondet_map_iterator_share () = Rust.cbor_nondet_map_iterator_share ()

let cbor_nondet_map_iterator_gather () = Rust.cbor_nondet_map_iterator_gather ()

let cbor_nondet_map_entry_share () = Rust.cbor_nondet_map_entry_share ()

let cbor_nondet_map_entry_gather () = Rust.cbor_nondet_map_entry_gather ()

let cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2 = Rust.cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2

let cbor_nondet_map_get () = map_get_by_ref_safe (cbor_nondet_major_type ()) (map_get_as_ref (Rust.cbor_nondet_map_get ()))

let cbor_nondet_mk_simple_value () = mk_simple_safe (Rust.cbor_nondet_mk_simple_value ())

let cbor_nondet_mk_uint64 () v = Rust.cbor_nondet_mk_uint64 () v

let cbor_nondet_mk_neg_int64 () v = Rust.cbor_nondet_mk_neg_int64 () v

let cbor_nondet_mk_int64 () v = Rust.cbor_nondet_mk_int64 () v

let cbor_nondet_mk_byte_string () = mk_string_from_arrayptr (Rust.cbor_nondet_mk_string ()) cbor_major_type_byte_string

let cbor_nondet_mk_text_string () = mk_string_from_arrayptr (Rust.cbor_nondet_mk_string ()) cbor_major_type_text_string

let cbor_nondet_mk_tagged () = mk_tagged_safe (Rust.cbor_nondet_mk_tagged ())

let cbor_nondet_mk_array () = mk_array_from_arrayptr (Rust.cbor_nondet_mk_array ())

let cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv = Rust.cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv

let cbor_nondet_mk_map () = cbor_mk_map_from_arrayptr_safe (mk_map_gen_by_ref (Rust.cbor_nondet_mk_map ()))


noextract [@noextract_to "krml"]
let set_snd_None
  (t1 t2: Type)
  (x: (t1 & option t2))
: Tot (t1 & option t2)
= (fst x, None)

module PM = Pulse.Lib.SeqMatch.Util

ghost fn trade_assoc_hyp_r2l
  (a b c d: slprop)
requires
  Trade.trade (a ** (b ** c)) d
ensures
  Trade.trade ((a ** b) ** c) d
{
  slprop_equivs ();
  rewrite Trade.trade (a ** (b ** c)) d as Trade.trade ((a ** b) ** c) d
}

ghost fn trade_assoc_hyp_l2r
  (a b c d: slprop)
requires
  Trade.trade ((a ** b) ** c) d
ensures
  Trade.trade (a ** (b ** c)) d
{
  slprop_equivs ();
  rewrite Trade.trade ((a ** b) ** c) d as Trade.trade (a ** (b ** c)) d
}

ghost fn trade_assoc_concl_r2l
  (a b c d: slprop)
requires
  Trade.trade a (b ** (c ** d))
ensures
  Trade.trade a ((b ** c) ** d)
{
  slprop_equivs ();
  rewrite Trade.trade a (b ** (c ** d)) as Trade.trade a ((b ** c) ** d)
}

ghost fn trade_assoc_concl_l2r
  (a b c d: slprop)
requires
  Trade.trade a ((b ** c) ** d)
ensures
  Trade.trade a (b ** (c ** d))
{
  slprop_equivs ();
  rewrite Trade.trade a ((b ** c) ** d) as Trade.trade a (b ** (c ** d))
}

let list_memP_map_intro_forall
  (#a #b: Type)
  (f: a -> Tot b)
  (l: list a)
: Lemma
  (requires True)
  (ensures (forall x . List.Tot.memP x l ==> List.Tot.memP (f x) (List.Tot.map f l)))
= let prf
    (x: a)
  : Lemma
    (ensures List.Tot.memP x l ==> List.Tot.memP (f x) (List.Tot.map f l))
  = List.Tot.memP_map_intro f x l
  in
  Classical.forall_intro prf

ghost fn lemma_trade_ab_cd_e
  (a b1 b2 c d1 d2 e: slprop)
requires
  Trade.trade (b1 ** d1) (b2 ** d2) **
  Trade.trade ((a ** b2) ** (c ** d2)) e
ensures
  Trade.trade ((a ** b1) ** (c ** d1)) e
{
  slprop_equivs ();
  rewrite (Trade.trade ((a ** b2) ** (c ** d2)) e) as Trade.trade ((a ** c) ** (b2 ** d2)) e;
  Trade.trans_hyp_r (a ** c) _ _ _;
  rewrite Trade.trade ((a ** c) ** (b1 ** d1)) e as (Trade.trade ((a ** b1) ** (c ** d1)) e)
}

ghost fn trade_prod_cancel_hyp_r_concl_l
  (#a b #c #d #e: slprop)
requires
  Trade.trade (a ** b) c ** Trade.trade d (b ** e)
ensures
  Trade.trade (a ** d) (c ** e)
{
  intro
    (Trade.trade (a ** d) (c ** e))
    #(Trade.trade (a ** b) c ** Trade.trade d (b ** e))
    fn _ {
      Trade.elim d _;
      Trade.elim (a ** b) _
    }
}

ghost fn trade_prod_cancel_hyp_l_concl_l
  (b #a #c #d #e: slprop)
requires
  Trade.trade (b ** a) c ** Trade.trade d (b ** e)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (b ** a) c as Trade.trade (a ** b) c;
  trade_prod_cancel_hyp_r_concl_l b
}

ghost fn trade_prod_cancel_hyp_r_concl_r
  (#a b #c #d #e: slprop)
requires
  Trade.trade (a ** b) c ** Trade.trade d (e ** b)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade d (e ** b) as Trade.trade d (b ** e);
  trade_prod_cancel_hyp_r_concl_l b
}

ghost fn trade_prod_cancel_hyp_l_concl_r
  (b #a #c #d #e: slprop)
requires
  Trade.trade (b ** a) c ** Trade.trade d (e ** b)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (b ** a) c as Trade.trade (a ** b) c;
  trade_prod_cancel_hyp_r_concl_r b;
}

ghost fn trade_prod_cancel_concl_r_hyp_l
  (#a #b c #d #e: slprop)
requires
  Trade.trade a (b ** c) ** Trade.trade (c ** d) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (c ** d) e as Trade.trade (d ** c) e;
  trade_prod_cancel_hyp_r_concl_r c;
  rewrite Trade.trade (d ** a) (e ** b) as Trade.trade (a ** d) (b ** e)
}

ghost fn trade_prod_cancel_concl_l_hyp_l
  (#a c #b #d #e: slprop)
requires
  Trade.trade a (c ** b) ** Trade.trade (c ** d) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade a (c ** b) as Trade.trade a (b ** c);
  trade_prod_cancel_concl_r_hyp_l c;
}

ghost fn trade_prod_cancel_concl_r_hyp_r
  (#a #b c #d #e: slprop)
requires
  Trade.trade a (b ** c) ** Trade.trade (d ** c) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (d ** c) e as Trade.trade (c ** d) e;
  trade_prod_cancel_concl_r_hyp_l c
}

ghost fn trade_prod_cancel_concl_l_hyp_r
  (#a c #b #d #e: slprop)
requires
  Trade.trade a (c ** b) ** Trade.trade (d ** c) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade a (c ** b) as Trade.trade a (b ** c);
  trade_prod_cancel_concl_r_hyp_r c
}

ghost fn trade_comm_concl
  (a b c: slprop)
requires Trade.trade a (b ** c)
ensures Trade.trade a (c ** b)
{
  slprop_equivs();
  rewrite Trade.trade a (b ** c) as Trade.trade a (c ** b)
}

let lemma_seq_assoc_cons
  (#t: Type)
  (a: Seq.seq t)
  (b: t)
  (c: Seq.seq t)
: Lemma
  (Seq.equal (Seq.append a (Seq.cons b c)) (Seq.append (Seq.append a (Seq.cons b Seq.empty)) c))
= ()

let lemma_seq_assoc_cons_upd
  (#t: Type)
  (a: Seq.seq t)
  (c: Seq.seq t)
  (b': t)
: Lemma
  (requires Seq.length c > 0)
  (ensures Seq.equal
    (Seq.upd (Seq.append a c) (Seq.length a) b')
    (Seq.append (Seq.append a (Seq.cons b' Seq.empty)) (Seq.tail c))
  )
= ()

ghost fn lemma_trade_rewrite5
  (a b c d ef: slprop)
requires
   Trade.trade (((a **
        b) **
        c) **
        d)
      (ef)
ensures
   Trade.trade (a ** (d ** b ** c))
      (ef)
{
  slprop_equivs ();
  rewrite
   Trade.trade (((a **
        b) **
        c) **
        d)
      (ef)
  as Trade.trade (a ** (d ** b ** c))
      (ef)
}

ghost fn cbor_map_get_multiple_entry_match_snd_prop
  (#t: Type0)
  (vmatch: perm -> t -> Spec.cbor -> slprop)
  (x: cbor_map_get_multiple_entry_t t)
  (y: option Spec.cbor)
requires
  cbor_map_get_multiple_entry_match_snd vmatch true x y
ensures
  cbor_map_get_multiple_entry_match_snd vmatch true x y **
  pure (x.found == Some? y)
{
  if (x.found <> Some? y) {
    rewrite cbor_map_get_multiple_entry_match_snd vmatch true x y as pure False;
    rewrite emp as cbor_map_get_multiple_entry_match_snd vmatch true x y
  }
}

module S = Pulse.Lib.Slice.Util

let cbor_nondet_map_get_multiple () = cbor_map_get_multiple_as_arrayptr cbor_nondet_map_get_multiple_entry_t (cbor_nondet_major_type ()) (Rust.cbor_nondet_map_get_multiple ())

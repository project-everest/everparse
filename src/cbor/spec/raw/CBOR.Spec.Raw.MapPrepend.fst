module CBOR.Spec.Raw.MapPrepend

(* Pure spec lemma supporting a nondeterministic CBOR map-entry "prepend"
   operation.  Given a valid map (Map len entries) and a fresh entry (rk, rv)
   whose key rk is absent (up to raw_equiv) from the existing keys, prepending
   (rk, rv) corresponds, at the abstract `cbor_map` level, to a left-biased
   union of the existing map with the singleton {mk_cbor rk -> mk_cbor rv}.

   NOTE on the signature shape: to make the raw term `R.Map len' ((rk,rv)::entries)`
   type-check, the length header `len'` must witness that the prepended list has
   the right length.  We therefore refine `len'` with
   `U64.v l.value == 1 + U64.v len.value`, and bind `entries` as an `nlist` of
   length `U64.v len.value`.  Validity of the prepended map is DERIVED (see
   `mk_cbor_map_prepend_valid`), not assumed. *)

open CBOR.Spec.Raw

module R = CBOR.Spec.Raw.Base
module U = CBOR.Spec.Util
module U64 = FStar.UInt64

(* assoc returns None when the key is absent from the list of keys. *)
let rec assoc_none_of_not_memP
  (#t1: eqtype)
  (#t2: Type)
  (x: t1)
  (l: list (t1 & t2))
: Lemma
  (requires (~ (List.Tot.memP x (List.Tot.map fst l))))
  (ensures (List.Tot.assoc x l == None))
  (decreases l)
= match l with
  | [] -> ()
  | (k, _) :: q -> assoc_none_of_not_memP x q

(* Validity of the prepended map is derivable from the hypotheses. *)
let mk_cbor_map_prepend_valid
  (len: R.raw_uint64)
  (entries: R.nlist (R.raw_data_item & R.raw_data_item) (U64.v len.value))
  (rk rv: R.raw_data_item)
  (len': (l: R.raw_uint64 { U64.v l.value == 1 + U64.v len.value }))
: Lemma
  (requires (
    valid_raw_data_item (R.Map len entries) == true /\
    valid_raw_data_item rk == true /\
    valid_raw_data_item rv == true /\
    (~ (List.Tot.existsb (raw_equiv rk) (List.Tot.map fst entries)))
  ))
  (ensures (valid_raw_data_item (R.Map len' ((rk, rv) :: entries)) == true))
= valid_eq basic_data_model (R.Map len entries);
  valid_eq basic_data_model (R.Map len' ((rk, rv) :: entries))

let mk_cbor_map_prepend
  (len: R.raw_uint64)
  (entries: R.nlist (R.raw_data_item & R.raw_data_item) (U64.v len.value))
  (rk rv: R.raw_data_item)
  (len': (l: R.raw_uint64 { U64.v l.value == 1 + U64.v len.value }))
: Lemma
  (requires (
    valid_raw_data_item (R.Map len entries) == true /\
    valid_raw_data_item rk == true /\
    valid_raw_data_item rv == true /\
    (~ (List.Tot.existsb (raw_equiv rk) (List.Tot.map fst entries)))
  ))
  (ensures (
    CMap? (unpack (mk_cbor (R.Map len entries))) /\
    CMap? (unpack (mk_cbor (R.Map len' ((rk, rv) :: entries)))) /\
    (CMap?.c (unpack (mk_cbor (R.Map len' ((rk, rv) :: entries)))) <: cbor_map) ==
      cbor_map_union
        (CMap?.c (unpack (mk_cbor (R.Map len entries))))
        (cbor_map_singleton (mk_cbor rk) (mk_cbor rv))
  ))
= mk_cbor_map_prepend_valid len entries rk rv len';
  mk_cbor_eq (R.Map len entries);
  mk_cbor_eq (R.Map len' ((rk, rv) :: entries));
  valid_eq basic_data_model (R.Map len entries);
  valid_eq basic_data_model (R.Map len' ((rk, rv) :: entries));
  let m_old = CMap?.c (unpack (mk_cbor (R.Map len entries))) in
  let m_new = CMap?.c (unpack (mk_cbor (R.Map len' ((rk, rv) :: entries)))) in
  let sing = cbor_map_singleton (mk_cbor rk) (mk_cbor rv) in
  let target = cbor_map_union m_old sing in
  let aux (k: cbor) : Lemma (cbor_map_get m_new k == cbor_map_get target k) =
    list_assoc_map_mk_cbor_map_entry m_old entries () k;
    list_assoc_map_mk_cbor_map_entry m_new ((rk, rv) :: entries) () k;
    list_mem_map_fst_mk_cbor_map_entry entries rk;
    assoc_none_of_not_memP (mk_cbor rk) (List.Tot.map mk_cbor_map_entry entries)
  in
  Classical.forall_intro aux;
  assert (cbor_map_equal m_new target);
  cbor_map_ext m_new target

(* Presence direction: if the fresh key [rk] is equivalent (raw_equiv) to some
   existing key, then the abstract key [mk_cbor rk] is defined in the abstract
   map.  This is the dual of the absence reasoning in [mk_cbor_map_prepend], and
   bridges the raw-level [existsb raw_equiv] dup-check result to the spec-level
   [cbor_map_defined] used in the None branch of the map-insert specification. *)
let mk_cbor_map_defined_of_existsb
  (len: R.raw_uint64)
  (entries: R.nlist (R.raw_data_item & R.raw_data_item) (U64.v len.value))
  (rk: R.raw_data_item)
: Lemma
  (requires (
    valid_raw_data_item (R.Map len entries) == true /\
    valid_raw_data_item rk == true /\
    List.Tot.existsb (raw_equiv rk) (List.Tot.map fst entries)
  ))
  (ensures (
    CMap? (unpack (mk_cbor (R.Map len entries))) /\
    cbor_map_defined (mk_cbor rk) (CMap?.c (unpack (mk_cbor (R.Map len entries))))
  ))
= mk_cbor_eq (R.Map len entries);
  valid_eq basic_data_model (R.Map len entries);
  let m_old = CMap?.c (unpack (mk_cbor (R.Map len entries))) in
  list_mem_map_fst_mk_cbor_map_entry entries rk;
  list_assoc_map_mk_cbor_map_entry m_old entries () (mk_cbor rk);
  List.Tot.mem_memP (mk_cbor rk) (List.Tot.map fst (List.Tot.map mk_cbor_map_entry entries));
  List.Tot.assoc_mem (mk_cbor rk) (List.Tot.map mk_cbor_map_entry entries)

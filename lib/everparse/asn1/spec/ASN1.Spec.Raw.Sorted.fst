module ASN1.Spec.Raw.Sorted

(* Generic values of raw values sorted on the fly, as the raw writer
   (`ASN1.Pulse.RawWriter`) does: the components of a SET and the elements of
   a SET OF are inserted one by one, each one being inserted after the
   leading values that are smaller than it and whose header is a DER header
   (`vins`), as `ASN1.Pulse.SortedInsert.ins` does on bytes.

   `svalue k y` is `rvalue k y` (`ASN1.Spec.Raw.Value`) except for this
   order. If either of them conforms to `k`, then they are equal
   (`svalue_rvalue`.) *)

open LowParse.Tot.Base
open ASN1.Bytes
open ASN1.Base
open ASN1.Spec.Value
open ASN1.Spec.Value.Enc
open ASN1.Spec.Content.Enc
open ASN1.Spec.Interpreter
open ASN1.Spec.Conformance
open ASN1.Spec.ToValue
open ASN1.Spec.Raw
open ASN1.Spec.Raw.Props
open ASN1.Spec.Raw.Value

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module List = FStar.List.Tot
module Set = FStar.Set
module LPC = LowParse.Spec.Combinators
module Inj = ASN1.Spec.ToValue.Inj
module TVS = ASN1.Spec.ToValue.Set
module Set_ = ASN1.Spec.Set
module Str = ASN1.Spec.Conformance.Struct
module Snd = ASN1.Spec.ToValue.Sound

(* On-the-fly insertion *)

let vlt_t = asn1_value -> list asn1_value -> Tot bool

(* SET: by tag *)
let vlt_tag : vlt_t = fun w e ->
  match e with
  | [] -> false
  | a :: _ -> asn1_tag_lt (value_id w) (value_id a)

(* SET OF: by encoding *)
let vlt_lex : vlt_t = fun w e ->
  not (Set_.lex_byte_order (asn1_value_list_enc e) (asn1_value_enc w))

(* Insert the values `e` after the leading values `w` of `l` with a DER
   header and such that `lt w e` *)
let rec vins (lt: vlt_t) (e: list asn1_value) (l: list asn1_value) : Tot (list asn1_value) (decreases l) =
  match l with
  | [] -> e
  | w :: q -> if Str.hdr_ok w && lt w e then w :: vins lt e q else e `List.append` l

let rec vsort_tag (l: list asn1_value) : Tot (list asn1_value) (decreases l) =
  match l with
  | [] -> []
  | v :: q -> vins vlt_tag [v] (vsort_tag q)

(* Inserting the elements first to last *)
let rec vsacc (acc: list asn1_value) (l: list asn1_value) : Tot (list asn1_value) (decreases l) =
  match l with
  | [] -> acc
  | v :: q -> vsacc (vins vlt_lex [v] acc) q

let vsort_lex (l: list asn1_value) : Tot (list asn1_value) = vsacc [] l

(* Generic values *)

let rec scontent (b: bool) (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k) : Tot asn1_value (decreases %[k; 0]) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> rterm id k' y
  | ASN1_TERMINAL k' -> rterm id k' y
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    mk_cons id (sitems b items y)
  | ASN1_SET _ items _ -> mk_cons id (let l = sitems b items y in if b then vsort_tag l else sort_by_tag l)
  | ASN1_SEQUENCE_OF _ k' -> mk_cons id (slist b k' y)
  | ASN1_SET_OF _ k' -> mk_cons id (let l = slist b k' y in if b then vsort_lex l else vsort l)
  | ASN1_PREFIXED k' -> mk_encap id (svalue b k' y)
  | ASN1_ANY_DEFINED_BY _ prefix kid key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      let sfx (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key :: sls b key_k ls key y
      in
      mk_cons id (sitems_any b prefix sfx y)
    | Some fb ->
      let (| _, fbitems |) = fb in
      let sfx (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key ::
        sls_fb b key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> sitems b fbitems z) key y
      in
      mk_cons id (sitems_any b prefix sfx y)
    end

and slist (b: bool) (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k)) : Tot (list asn1_value) (decreases %[k; l]) =
  match l with
  | [] -> []
  | a :: q -> svalue b k a :: slist b k q

and svalue (b: bool) (#s: _) (k: asn1_k s) (y: asn1_raw_t k) : Tot asn1_value (decreases %[k; y]) =
  match k with
  | ASN1_ILC id k' -> scontent b id k' y
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    schoice b lc id z
  | ASN1_ANY_ILC -> y

and schoice (b: bool) (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc)) : Tot asn1_value (decreases %[lc; 0]) =
  match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then scontent b id c y
    else schoice b tl id y

and sls (b: bool) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_raw_terminal_t key_k) (y: idlookup_t key (raw_any_t_core key_k ls)) : Tot (list asn1_value) (decreases %[ls; 0]) =
  match ls with
  | [] -> false_elim ()
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then sitems b items y
    else sls b key_k tl key y

and sls_fb (b: bool) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: Type) (fbf: fb -> Tot (list asn1_value)) (key: asn1_raw_terminal_t key_k) (y: idlookup_with_fallback_t key (raw_any_t_core key_k ls) fb) : Tot (list asn1_value) (decreases %[ls; 0]) =
  match ls with
  | [] -> fbf y
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then sitems b items y
    else sls_fb b key_k tl fb fbf key y

and sdec (b: bool) (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk) : Tot (list asn1_value) (decreases %[dk; 0]) =
  match dk with
  | ASN1_PLAIN_ILC k -> [svalue b k y]
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    (match y' with None -> [] | Some z -> [svalue b k z])
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with
     | None -> []
     | Some z -> if z = raw_key_of_lit k defv_l then [] else [rterm id k z])
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with
     | None -> []
     | Some z -> if z = raw_key_of_lit k defv_l then [] else [rterm id k z])

and sitems (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items) : Tot (list asn1_value) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> []
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> sdec b dk y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    sdec b dk a `List.append` sitems b tl c

and sitems_any (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items sfx_t) : Tot (list asn1_value) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> sfx y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, c) = y' in
    sdec b dk a `List.append` sfx c
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, c) = y' in
    sdec b dk a `List.append` sitems_any b tl sfx c

(* Insertion of values with DER headers *)

let rec vins_memP (lt: vlt_t) (e l: list asn1_value) (v: asn1_value)
: Lemma (ensures (List.memP v (vins lt e l) <==> (List.memP v e \/ List.memP v l))) (decreases l)
= match l with
  | [] -> ()
  | w :: q ->
    List.append_memP e l v;
    if Str.hdr_ok w && lt w e then vins_memP lt e q v else ()

let rec vins_count (lt: vlt_t) (e l: list asn1_value) (v: asn1_value)
: Lemma (ensures (TVS.count v (vins lt e l) == TVS.count v e + TVS.count v l)) (decreases l)
= match l with
  | [] -> ()
  | w :: q ->
    TVS.count_append v e l;
    if Str.hdr_ok w && lt w e then vins_count lt e q v else ()

let vins_nil (l: list asn1_value)
: Lemma (vins vlt_tag [] l == l)
= match l with
  | [] -> ()
  | _ -> ()

let all_hdr_ok (l: list asn1_value) : prop = forall v . List.memP v l ==> Str.hdr_ok v == true

let rec vins_tag (v: asn1_value) (l: list asn1_value)
: Lemma (requires (all_hdr_ok l)) (ensures (vins vlt_tag [v] l == insert_by_tag v l)) (decreases l)
= match l with
  | [] -> ()
  | w :: q -> vins_tag v q

let rec vsort_tag_memP (l: list asn1_value) (v: asn1_value)
: Lemma (ensures (List.memP v (vsort_tag l) <==> List.memP v l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q -> vsort_tag_memP q v; vins_memP vlt_tag [a] (vsort_tag q) v

let rec vsort_tag_count (l: list asn1_value) (v: asn1_value)
: Lemma (ensures (TVS.count v (vsort_tag l) == TVS.count v l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q -> vsort_tag_count q v; vins_count vlt_tag [a] (vsort_tag q) v

let rec vsort_tag_eq (l: list asn1_value)
: Lemma (requires (all_hdr_ok l)) (ensures (vsort_tag l == sort_by_tag l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    vsort_tag_eq q;
    let prf (x: asn1_value) : Lemma (List.memP x (sort_by_tag q) ==> Str.hdr_ok x == true) =
      TVS.count_sort q x; TVS.count_mem x q; TVS.count_mem x (sort_by_tag q)
    in
    FStar.Classical.forall_intro prf;
    vins_tag a (sort_by_tag q)

(* SET OF *)

let rec vins_lex (v: asn1_value) (l: list asn1_value)
: Lemma (requires (all_hdr_ok l)) (ensures (vins vlt_lex [v] l == insert_enc asn1_value_enc v l)) (decreases l)
= match l with
  | [] -> ()
  | w :: q ->
    assert (asn1_value_list_enc [v] == asn1_value_enc v `Seq.append` Seq.empty);
    Seq.append_empty_r (asn1_value_enc v);
    vins_lex v q

let rec vsacc_memP (acc l: list asn1_value) (v: asn1_value)
: Lemma (ensures (List.memP v (vsacc acc l) <==> (List.memP v acc \/ List.memP v l))) (decreases l)
= match l with
  | [] -> ()
  | a :: q -> vins_memP vlt_lex [a] acc v; vsacc_memP (vins vlt_lex [a] acc) q v

let rec vsacc_eq (acc l: list asn1_value)
: Lemma (requires (all_hdr_ok acc /\ all_hdr_ok l)) (ensures (vsacc acc l == sort_fold asn1_value_enc acc l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    vins_lex a acc;
    FStar.Classical.forall_intro (vins_memP vlt_lex [a] acc);
    vsacc_eq (vins vlt_lex [a] acc) q

let vsort_lex_memP (l: list asn1_value) (v: asn1_value)
: Lemma (List.memP v (vsort_lex l) <==> List.memP v l)
= vsacc_memP [] l v

let vsort_lex_eq (l: list asn1_value)
: Lemma (requires (all_hdr_ok l)) (ensures (vsort_lex l == vsort l))
= vsacc_eq [] l;
  FStar.Classical.forall_intro_2 (fun v1 v2 -> FStar.Classical.move_requires (asn1_value_enc_inj v1) v2);
  sort_fold_eq asn1_value_enc l

(* Without sorting on the fly, `svalue` is `rvalue` *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec f_content (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k)
: Lemma (ensures (scontent false id k y == rcontent id k y)) (decreases %[k; 3])
= match k with
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    f_items items y
  | ASN1_SET _ items _ -> f_items items y
  | ASN1_SEQUENCE_OF _ k' -> f_list k' y
  | ASN1_SET_OF _ k' -> f_list k' y
  | ASN1_PREFIXED k' -> f_value k' y
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      let k = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf' in
      let ssfx (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key :: sls false key_k ls key y
      in
      let rsfx (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key :: rls key_k ls key y
      in
      assert (scontent false id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == mk_cons id (sitems_any false prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, y |) = s in rterm kid key_k key :: sls false key_k ls key y) <: list asn1_value) y))
        by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
      assert (rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == mk_cons id (ritems_any prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, y |) = s in rterm kid key_k key :: rls key_k ls key y) <: list asn1_value) y))
        by (FStar.Tactics.norm [delta_only [`%rcontent]; zeta; iota]; FStar.Tactics.trefl ());
      let prf (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Lemma (ssfx s == rsfx s) =
        let (| key, z |) = s in
        f_ls key_k ls key z
      in
      FStar.Classical.forall_intro prf;
      f_items_any prefix ssfx rsfx y
    | Some (| fbids, fbitems |) ->
      let k = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf' in
      fb_precedes k;
      let ssfx (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key ::
        sls_fb false key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> sitems false fbitems z) key y
      in
      let rsfx (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
        let (| key, y |) = s in
        rterm kid key_k key ::
        rls_fb key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> ritems fbitems z) key y
      in
      assert (scontent false id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == mk_cons id (sitems_any false prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, y |) = s in rterm kid key_k key :: sls_fb false key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> sitems false fbitems z) key y) <: list asn1_value) y))
        by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
      assert (rcontent id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == mk_cons id (ritems_any prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, y |) = s in rterm kid key_k key :: rls_fb key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> ritems fbitems z) key y) <: list asn1_value) y))
        by (FStar.Tactics.norm [delta_only [`%rcontent]; zeta; iota]; FStar.Tactics.trefl ());
      let prf (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Lemma (ssfx s == rsfx s) =
        let (| key, z |) = s in
        f_ls_fb k key_k ls fbitems key z
      in
      FStar.Classical.forall_intro prf;
      f_items_any prefix ssfx rsfx y
    end
  | _ -> ()

and f_list (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k))
: Lemma (ensures (slist false k l == rlist k l)) (decreases %[k; 3; l])
= match l with
  | [] -> ()
  | a :: q -> f_value k a; f_list k q

and f_value (#s: _) (k: asn1_k s) (y: asn1_raw_t k)
: Lemma (ensures (svalue false k y == rvalue k y)) (decreases %[k; 2])
= match k with
  | ASN1_ILC id k' -> f_content id k' y
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    f_choice lc id z
  | ASN1_ANY_ILC -> ()

and f_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc))
: Lemma (ensures (schoice false lc id y == rchoice lc id y)) (decreases %[lc; 0])
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then f_content id c y
    else f_choice tl id y

and f_ls (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_raw_terminal_t key_k) (y: idlookup_t key (raw_any_t_core key_k ls))
: Lemma (ensures (sls false key_k ls key y == rls key_k ls key y)) (decreases %[ls; 0])
= match ls with
  | [] -> false_elim ()
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then f_items items y
    else f_ls key_k tl key y

and f_ls_fb (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_raw_terminal_t key_k) (y: idlookup_with_fallback_t key (raw_any_t_core key_k ls) (raw_items_t fbitems))
: Lemma
  (ensures (
    sls_fb false key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> sitems false fbitems z) key y ==
    rls_fb key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> ritems fbitems z) key y))
  (decreases %[k0; 1; ls])
= match ls with
  | [] -> f_items fbitems y
  | (key', it) :: tl ->
    let (| _, items |) = it in
    if key = raw_key_of_lit key_k key'
    then f_items items y
    else f_ls_fb k0 key_k tl fbitems key y

and f_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk)
: Lemma (ensures (sdec false dk y == rdec dk y)) (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k -> f_value k y
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    (match y' with None -> () | Some z -> f_value k z)
  | _ -> ()

and f_items (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items)
: Lemma (ensures (sitems false items y == ritems items y)) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> f_dec dk y
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    f_dec dk a; f_items tl c

and f_items_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (ssfx rsfx: sfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items sfx_t)
: Lemma
  (requires (forall z . ssfx z == rsfx z))
  (ensures (sitems_any false items ssfx y == ritems_any items rsfx y)) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, c) = y' in
    f_dec dk a
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, c) = y' in
    f_dec dk a; f_items_any tl ssfx rsfx c
#pop-options

(* Identifiers *)

let scontent_id (b: bool) (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k)
: Lemma (value_id (scontent b id k y) == any_id id)
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> rterm_id id k' y
  | ASN1_TERMINAL k' -> rterm_id id k' y
  | ASN1_ANY_DEFINED_BY _ _ _ _ _ ofb _ _ ->
    begin match ofb with
    | None -> ()
    | Some _ -> ()
    end
  | _ -> ()

let rec schoice_id (b: bool) (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc))
: Lemma
  (ensures (
    value_id (schoice b lc id y) == any_id id /\
    List.mem id (List.map fst lc) /\
    (wf_lc lc ==> asn1_any_id_valid id)))
  (decreases lc)
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then scontent_id b id c y
    else schoice_id b tl id y

let svalue_mem (b: bool) (#s: _) (k: asn1_k s) (y: asn1_raw_t k)
: Lemma
  (requires (wf k))
  (ensures (Set.mem (value_id (svalue b k y)) s))
= match k with
  | ASN1_ILC id k' -> scontent_id b id k' y
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    schoice_id b lc id z;
    Inj.mem_as_set' id (List.map fst lc)
  | ASN1_ANY_ILC -> ()

let sdec_values (b: bool) (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk)
: Lemma
  (requires (wf_dec dk))
  (ensures (Inj.dec_values_ok s d (sdec b dk y)))
= match dk with
  | ASN1_PLAIN_ILC k -> svalue_mem b k y
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    (match y' with None -> () | Some z -> svalue_mem b k z)
  | ASN1_DEFAULT_TERMINAL id #k defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with None -> () | Some z -> rterm_id id k z)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
    let y' : option (asn1_raw_terminal_t k) = y in
    (match y' with None -> () | Some z -> rterm_id id k z)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec sitems_head (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (y: raw_items_t items) (r: list asn1_value)
: Lemma
  (requires (wf_items items /\ Inj.wf_tail ids s r))
  (ensures (Inj.head_not_in (sitems b items y `List.append` r) s))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    sdec_values b dk y;
    Inj.dec_head_not_in s s' d (sdec b dk y) r
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    sdec_values b dk a;
    List.append_assoc (sdec b dk a) (sitems b tl c) r;
    if Nil? (sdec b dk a) then sitems_head b tl (Set.union s s') c r;
    Inj.dec_head_not_in s s' d (sdec b dk a) (sitems b tl c `List.append` r)

let rec sitems_any_head (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items sfx_t)
: Lemma
  (requires (wf_items items /\ (forall (z: sfx_t) . Inj.wf_tail ids s (sfx z))))
  (ensures (Inj.head_not_in (sitems_any b items sfx y) s))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, c) = y' in
    sdec_values b dk a;
    Inj.dec_head_not_in s s' d (sdec b dk a) (sfx c)
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, c) = y' in
    assert (Inj.wf_tail ids s (sfx (raw_items_any_sfx tl c)));
    sdec_values b dk a;
    if Nil? (sdec b dk a) then sitems_any_head b tl (Set.union s s') sfx c;
    Inj.dec_head_not_in s s' d (sdec b dk a) (sitems_any b tl sfx c)

let rec sset_items_not_in (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (s0: Set.set asn1_id_t) (y: raw_items_t items)
: Lemma
  (requires (wf_items items /\ asn1_set_k_wf' s0 ids))
  (ensures (forall v . List.memP v (sitems b items y) ==> ~ (Set.mem (value_id v) s0)))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    sdec_values b dk y;
    assert (forall (i: asn1_id_t) . asn1_same_tag i i)
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    sdec_values b dk a;
    sset_items_not_in b tl s0 c;
    assert (forall (i: asn1_id_t) . asn1_same_tag i i);
    FStar.Classical.forall_intro (List.append_memP (sdec b dk a) (sitems b tl c))
#pop-options

(* The prefix of ANY DEFINED BY *)

let nil_sfx (#sfx_t: Type) (z: sfx_t) : Tot (list asn1_value) = []

let rec sitems_any_split (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items sfx_t)
: Lemma
  (ensures (sitems_any b items sfx y == sitems_any b items (nil_sfx #sfx_t) y `List.append` sfx (raw_items_any_sfx items y)))
  (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, c) = y' in
    List.append_l_nil (sdec b dk a)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, c) = y' in
    sitems_any_split b tl sfx c;
    List.append_assoc (sdec b dk a) (sitems_any b tl (nil_sfx #sfx_t) c) (sfx (raw_items_any_sfx tl c))

(* Q: if `svalue b k y` conforms to `k`, then sorting on the fly does not
   change anything *)

let aid (v: asn1_value) : Lemma (asn1_value_id v == value_id v) = ()

let vconf_hdr_ok (#s: _) (k: asn1_k s) (v: asn1_value)
: Lemma (requires (Str.vconf k v)) (ensures (Str.hdr_ok v))
= match k with
  | ASN1_ANY_ILC -> ()
  | _ -> ()

let rec vconf_list_memP (#s: _) (k: asn1_k s) (l: list asn1_value) (v: asn1_value)
: Lemma (requires (Str.vconf_list k l /\ List.memP v l)) (ensures (Str.vconf k v)) (decreases l)
= match l with
  | a :: q -> FStar.Classical.move_requires (vconf_list_memP k q) v

let rec vconf_list_intro (#s: _) (k: asn1_k s) (l: list asn1_value)
: Lemma (requires (forall v . List.memP v l ==> Str.vconf k v)) (ensures (Str.vconf_list k l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q -> vconf_list_intro k q

let rec count_filter (f: asn1_value -> Tot bool) (l: list asn1_value) (v: asn1_value)
: Lemma (ensures (TVS.count v (List.filter f l) == (if f v then TVS.count v l else 0))) (decreases l)
= match l with
  | [] -> ()
  | a :: q -> count_filter f q v

let all_hdr_ok_append (l1 l2: list asn1_value)
: Lemma (requires (all_hdr_ok l1 /\ all_hdr_ok l2)) (ensures (all_hdr_ok (l1 `List.append` l2)))
= FStar.Classical.forall_intro (List.append_memP l1 l2)

(* PREFIXED, primitive *)
let encap_parse (w w': asn1_value)
: Lemma
  (requires (Str.tparse parse_asn1_value (asn1_value_enc w) == Some w'))
  (ensures (w' == w))
= let c = asn1_value_enc w in
  Str.tparse_exact parse_asn1_value c;
  parse_asn1_value_consumed' c;
  match parse parse_asn1_value c with
  | Some (w2, n) ->
    Seq.lemma_eq_elim (Seq.slice c 0 n) c;
    asn1_value_enc_inj w2 w
  | None -> ()

(* ANY DEFINED BY: the key *)
let adb_key (kid: asn1_id_t) (key_k: asn1_terminal_k) (key: asn1_raw_terminal_t key_k) (x: asn1_terminal_t key_k)
: Lemma
  (requires (
    wf_terminal kid key_k /\
    Str.tparse (asn1_terminal_as_parser key_k) (Str.vcont (rterm kid key_k key)) == Some x))
  (ensures (key == forget_terminal key_k x))
= let c = Str.vcont (rterm kid key_k key) in
  Snd.terminal_esound kid key_k;
  Str.tparse_exact (asn1_terminal_as_parser key_k) c;
  assert (Some? (parse (asn1_terminal_as_parser key_k) c));
  Seq.lemma_eq_elim (Seq.slice c 0 (Seq.length c)) c;
  assert (c == Snd.value_contents (terminal_to_value kid key_k x));
  begin match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_t k2);
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_raw_terminal_t k2);
    let y' : asn1_raw_terminal_t k2 = coerce_eq #(asn1_raw_terminal_t key_k) #(asn1_raw_terminal_t k2) () key in
    let x' : asn1_terminal_t k2 = coerce_eq #(asn1_terminal_t key_k) #(asn1_terminal_t k2) () x in
    let a1 = rterm id2 k2 y' in
    let a2 = terminal_to_value id2 k2 x' in
    assert (rterm kid key_k key == mk_encap kid a1);
    assert (terminal_to_value kid key_k x == mk_encap kid a2);
    Seq.append_empty_r (asn1_value_enc a1);
    Seq.append_empty_r (asn1_value_enc a2);
    asn1_value_enc_inj a1 a2
  | _ -> ()
  end;
  rterm_mixed kid key_k key x

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec q_value (b: bool) (#s: _) (k: asn1_k s) (y: asn1_raw_t k)
: Lemma
  (requires (wf k /\ Str.vconf k (svalue b k y)))
  (ensures (svalue true k y == svalue false k y))
  (decreases %[k; 2])
= match k with
  | ASN1_ILC id k' -> q_content b id k' y
  | ASN1_CHOICE_ILC lc _ ->
    let y' : make_gen_choice_type (raw_lc_t lc) = y in
    let (| id, z |) = y' in
    q_choice b lc id z
  | ASN1_ANY_ILC -> ()

and q_content (b: bool) (id: asn1_id_t) (k: asn1_content_k) (y: asn1_raw_content_t k)
: Lemma
  (requires (wf_content id k /\ Str.cconf k (scontent b id k y)))
  (ensures (scontent true id k y == scontent false id k y))
  (decreases %[k; 3])
= match k with
  | ASN1_RESTRICTED_TERMINAL _ _ -> ()
  | ASN1_TERMINAL _ -> ()
  | ASN1_SEQUENCE gitems ->
    let (| ids, items |) = gitems in
    Inj.seq_wf_tail ids;
    q_seq b items Set.empty y
  | ASN1_SET ids items _ ->
    let l = sitems b items y in
    let l' = if b then vsort_tag l else sort_by_tag l in
    let prf (v: asn1_value) : Lemma (TVS.count v l' == TVS.count v l) =
      if b then vsort_tag_count l v else TVS.count_sort l v
    in
    FStar.Classical.forall_intro prf;
    q_set b items y l';
    vsort_tag_eq (sitems true items y)
  | ASN1_SEQUENCE_OF _ k' ->
    q_list b k' y
  | ASN1_SET_OF _ k' ->
    let l = slist b k' y in
    let l' = if b then vsort_lex l else vsort l in
    let prf (v: asn1_value) : Lemma (List.memP v l ==> Str.vconf k' v) =
      vsort_lex_memP l v;
      sort_memP asn1_value_enc l v;
      FStar.Classical.move_requires (vconf_list_memP k' l') v
    in
    FStar.Classical.forall_intro prf;
    vconf_list_intro k' l;
    q_list b k' y;
    vsort_lex_eq (slist true k' y)
  | ASN1_PREFIXED k' ->
    let w = svalue b k' y in
    begin match Str.tparse parse_asn1_value (asn1_value_enc w) with
    | Some w' -> encap_parse w w'
    | None -> ()
    end;
    q_value b k' y
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None -> q_adb b id idp prefix kid key_k ls pf pf' y
    | Some fb ->
      let (| fbids, fbitems |) = fb in
      q_adb_fb b id idp prefix kid key_k ls fbids fbitems pf pf' y
    end

and q_adb (b: bool) (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))
: Lemma
  (requires (
    wf_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') /\
    Str.cconf (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') (scontent b id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y)))
  (ensures (scontent true id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y == scontent false id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y))
  (decreases %[ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'; 2])
= let sclo (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key :: sls b key_k ls key z
  in
  let sclo_t (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key :: sls true key_k ls key z
  in
  let sclo_f (s: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key :: sls false key_k ls key z
  in
  assert (scontent b id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y ==
    mk_cons id (sitems_any b prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, z |) = s in rterm kid key_k key :: sls b key_k ls key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
  assert (scontent true id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y ==
    mk_cons id (sitems_any true prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, z |) = s in rterm kid key_k key :: sls true key_k ls key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
  assert (scontent false id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf') y ==
    mk_cons id (sitems_any false prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, z |) = s in rterm kid key_k key :: sls false key_k ls key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
  let rtail (z: make_gen_choice_type (raw_any_t_core key_k ls)) : Lemma (Inj.wf_tail idp Set.empty (sclo z)) =
    let (| key, _ |) = z in
    rterm_id kid key_k key;
    Inj.any_prefix_wf_tail (Set.singleton kid) idp (sclo z)
  in
  FStar.Classical.forall_intro rtail;
  q_items_any b prefix Set.empty sclo y;
  sitems_any_split b prefix sclo y;
  sitems_any_split true prefix sclo_t y;
  sitems_any_split false prefix sclo_f y;
  let rs = raw_items_any_sfx prefix #(make_gen_choice_type (raw_any_t_core key_k ls)) y in
  let (| key, z |) = rs in
  match Str.tparse (asn1_terminal_as_parser key_k) (Str.vcont (rterm kid key_k key)) with
  | Some x -> adb_key kid key_k key x; q_ls b key_k ls key x z
  | None -> ()

and q_adb_fb (b: bool) (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbids: id_decs {asn1_sequence_k_wf fbids}) (fbitems: asn1_gen_items_l fbids)
  (pf: squash (asn1_any_prefix_k_wf (Set.singleton kid) idp))
  (pf': squash (List.noRepeats (List.map fst ls)))
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
: Lemma
  (requires (
    wf_content id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') /\
    Str.cconf (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') (scontent b id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y)))
  (ensures (scontent true id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == scontent false id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y))
  (decreases %[ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'; 2])
= let k0 = ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf' in
  fb_precedes k0;
  let sclo (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key ::
    sls_fb b key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems b fbitems w) key z
  in
  let sclo_t (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key ::
    sls_fb true key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems true fbitems w) key z
  in
  let sclo_f (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (list asn1_value) =
    let (| key, z |) = s in
    rterm kid key_k key ::
    sls_fb false key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems false fbitems w) key z
  in
  assert (scontent b id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y ==
    mk_cons id (sitems_any b prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, z |) = s in rterm kid key_k key :: sls_fb b key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems b fbitems w) key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
  assert (scontent true id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y ==
    mk_cons id (sitems_any true prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, z |) = s in rterm kid key_k key :: sls_fb true key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems true fbitems w) key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
  assert (scontent false id (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y ==
    mk_cons id (sitems_any false prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, z |) = s in rterm kid key_k key :: sls_fb false key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems false fbitems w) key z) <: list asn1_value) y))
    by (FStar.Tactics.norm [delta_only [`%scontent]; zeta; iota]; FStar.Tactics.trefl ());
  let rtail (z: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Lemma (Inj.wf_tail idp Set.empty (sclo z)) =
    let (| key, _ |) = z in
    rterm_id kid key_k key;
    Inj.any_prefix_wf_tail (Set.singleton kid) idp (sclo z)
  in
  FStar.Classical.forall_intro rtail;
  q_items_any b prefix Set.empty sclo y;
  sitems_any_split b prefix sclo y;
  sitems_any_split true prefix sclo_t y;
  sitems_any_split false prefix sclo_f y;
  let rs = raw_items_any_sfx prefix #(make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) y in
  let (| key, z |) = rs in
  match Str.tparse (asn1_terminal_as_parser key_k) (Str.vcont (rterm kid key_k key)) with
  | Some x -> adb_key kid key_k key x; q_ls_fb b k0 key_k ls fbitems key x z
  | None -> ()

and q_list (b: bool) (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k))
: Lemma
  (requires (wf k /\ Str.vconf_list k (slist b k l)))
  (ensures (slist true k l == slist false k l /\ all_hdr_ok (slist b k l)))
  (decreases %[k; 3; l])
= match l with
  | [] -> ()
  | a :: q ->
    q_value b k a;
    vconf_hdr_ok k (svalue b k a);
    q_list b k q

and q_choice (b: bool) (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc))
: Lemma
  (requires (wf_lc lc /\ Str.choice_conf lc (schoice b lc id y)))
  (ensures (schoice true lc id y == schoice false lc id y))
  (decreases %[lc; 0])
= match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    schoice_id b lc id y;
    aid (schoice b lc id y);
    if id = id'
    then q_content b id c y
    else q_choice b tl id y

and q_ls (b: bool) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_raw_terminal_t key_k) (x: asn1_terminal_t key_k) (y: idlookup_t key (raw_any_t_core key_k ls))
: Lemma
  (requires (wf_ls ls /\ key == forget_terminal key_k x /\ Str.lsm key_k ls x (sls b key_k ls key y)))
  (ensures (sls true key_k ls key y == sls false key_k ls key y))
  (decreases %[ls; 0])
= match ls with
  | [] -> false_elim ()
  | (l, it) :: tl ->
    let (| ids, items |) = it in
    if x = key_of_lit key_k l
    then begin
      Inj.seq_wf_tail ids;
      q_seq b items Set.empty y
    end
    else begin
      forget_key_ne key_k x l;
      q_ls b key_k tl key x y
    end

and q_ls_fb (b: bool) (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_raw_terminal_t key_k) (x: asn1_terminal_t key_k) (y: idlookup_with_fallback_t key (raw_any_t_core key_k ls) (raw_items_t fbitems))
: Lemma
  (requires (
    wf_ls ls /\ wf_items fbitems /\ asn1_sequence_k_wf fbids /\ key == forget_terminal key_k x /\
    Str.lsm_fb k0 key_k ls fbitems x (sls_fb b key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems b fbitems w) key y)))
  (ensures (
    sls_fb true key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems true fbitems w) key y ==
    sls_fb false key_k ls (raw_items_t fbitems) (fun (w: raw_items_t fbitems) -> sitems false fbitems w) key y))
  (decreases %[k0; 1; ls])
= match ls with
  | [] ->
    Inj.seq_wf_tail fbids;
    q_seq b fbitems Set.empty y
  | (l, it) :: tl ->
    let (| ids, items |) = it in
    if x = key_of_lit key_k l
    then begin
      Inj.seq_wf_tail ids;
      q_seq b items Set.empty y
    end
    else begin
      forget_key_ne key_k x l;
      q_ls_fb b k0 key_k tl fbitems key x y
    end

and q_dec (b: bool) (#s: _) (#d: _) (dk: asn1_decorated_k s d) (y: raw_dec_t dk)
: Lemma
  (requires (wf_dec dk /\ (forall v . List.memP v (sdec b dk y) ==> Str.itemconf dk v)))
  (ensures (sdec true dk y == sdec false dk y /\ all_hdr_ok (sdec b dk y)))
  (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k ->
    assert (List.memP (svalue b k y) (sdec b dk y));
    q_value b k y;
    vconf_hdr_ok k (svalue b k y)
  | ASN1_OPTION_ILC k ->
    let y' : option (asn1_raw_t k) = y in
    begin match y' with
    | None -> ()
    | Some z ->
      assert (List.memP (svalue b k z) (sdec b dk y));
      q_value b k z;
      vconf_hdr_ok k (svalue b k z)
    end
  | ASN1_DEFAULT_TERMINAL id #k defv_l -> ()
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l -> ()

and q_seq (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (y: raw_items_t items)
: Lemma
  (requires (wf_items items /\ Inj.wf_tail ids s [] /\ Str.seqm items (sitems b items y)))
  (ensures (sitems true items y == sitems false items y /\ all_hdr_ok (sitems b items y)))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    sdec_values b dk y;
    FStar.Classical.forall_intro aid;
    q_dec b dk y
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    sdec_values b dk a;
    FStar.Classical.forall_intro aid;
    if Nil? (sdec b dk a) then begin
      sitems_head b tl (Set.union s s') c [];
      List.append_l_nil (sitems b tl c)
    end;
    q_dec b dk a;
    let s1 : Set.set asn1_id_t = if PLAIN? d then Set.empty else Set.union s s' in
    q_seq b tl s1 c;
    all_hdr_ok_append (sdec b dk a) (sitems b tl c)

and q_items_any (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (s: Set.set asn1_id_t) (#sfx_t: Type) (sfx: sfx_t -> Tot (list asn1_value)) (y: raw_items_any_t items sfx_t)
: Lemma
  (requires (
    wf_items items /\
    (forall (z: sfx_t) . Inj.wf_tail ids s (sfx z)) /\
    Some? (Str.pfxm items (sitems_any b items sfx y))))
  (ensures (
    Str.pfxm items (sitems_any b items sfx y) == Some (sfx (raw_items_any_sfx items y)) /\
    sitems_any true items (nil_sfx #sfx_t) y == sitems_any false items (nil_sfx #sfx_t) y))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    let y' : raw_dec_t dk & sfx_t = y in
    let (a, c) = y' in
    assert (Inj.wf_tail ids s (sfx c));
    sdec_values b dk a;
    FStar.Classical.forall_intro aid;
    q_dec b dk a
  | ASN1_GEN_ITEMS_CONS s' d dk tids tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, c) = y' in
    assert (Inj.wf_tail ids s (sfx (raw_items_any_sfx tl c)));
    sdec_values b dk a;
    FStar.Classical.forall_intro aid;
    let s1 : Set.set asn1_id_t = if PLAIN? d then Set.empty else Set.union s s' in
    assert (forall (z: sfx_t) . Inj.wf_tail tids s1 (sfx z));
    if Nil? (sdec b dk a) then sitems_any_head b tl (Set.union s s') sfx c;
    q_dec b dk a;
    q_items_any b tl s1 sfx c

and q_set (b: bool) (#ids: _) (items: asn1_gen_items_l ids) (y: raw_items_t items) (l: list asn1_value)
: Lemma
  (requires (
    wf_items items /\ asn1_set_k_wf ids /\
    (forall v . TVS.count v l == TVS.count v (sitems b items y)) /\
    Str.setm items l))
  (ensures (sitems true items y == sitems false items y /\ all_hdr_ok (sitems b items y)))
  (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' d dk _ ASN1_GEN_ITEMS_NIL ->
    let d1 = sdec b dk y in
    sdec_values b dk y;
    FStar.Classical.forall_intro aid;
    let h = List.filter (Str.in_s s') l in
    let t = List.filter (Str.out_s s') l in
    let prf (v: asn1_value) : Lemma (TVS.count v h == TVS.count v d1) =
      count_filter (Str.in_s s') l v;
      count_filter (Str.out_s s') l v;
      if Set.mem (value_id v) s' then () else Inj.count_not_mem v d1 (fun w -> Set.mem (value_id w) s')
    in
    FStar.Classical.forall_intro prf;
    Inj.short_count_eq h d1;
    q_dec b dk y
  | ASN1_GEN_ITEMS_CONS s' d dk _ tl ->
    let y' : raw_dec_t dk & raw_items_t tl = y in
    let (a, c) = y' in
    let d1 = sdec b dk a in
    let t1 = sitems b tl c in
    sdec_values b dk a;
    sset_items_not_in b tl s' c;
    FStar.Classical.forall_intro aid;
    let h = List.filter (Str.in_s s') l in
    let t = List.filter (Str.out_s s') l in
    let in_s' (w: asn1_value) : GTot prop = Set.mem (value_id w) s' in
    let not_in_s' (w: asn1_value) : GTot prop = ~ (Set.mem (value_id w) s') in
    let prf (v: asn1_value) : Lemma (TVS.count v h == TVS.count v d1 /\ TVS.count v t == TVS.count v t1) =
      count_filter (Str.in_s s') l v;
      count_filter (Str.out_s s') l v;
      TVS.count_append v d1 t1;
      if Set.mem (value_id v) s'
      then Inj.count_not_mem v t1 not_in_s'
      else Inj.count_not_mem v d1 in_s'
    in
    FStar.Classical.forall_intro prf;
    Inj.short_count_eq h d1;
    q_dec b dk a;
    q_set b tl c t;
    all_hdr_ok_append d1 t1
#pop-options

let svalue_rvalue (b: bool) (#s: _) (k: asn1_k s) (y: asn1_raw_t k)
: Lemma
  (requires (wf k /\ Str.vconf k (svalue b k y)))
  (ensures (svalue true k y == rvalue k y))
= q_value b k y;
  f_value k y

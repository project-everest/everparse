module CDDL.SteelST
include CDDL.Spec
open LowParse.SteelST.Combinators
module Cbor = CBOR.SteelST
module SZ = FStar.SizeT
open Steel.ST.GenElim

inline_for_extraction [@@noextract_to "krml"]
let impl_typ (t: typ) =
  (#va: v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) ->
  (a: byte_array) ->
  ST bool
    (aparse Cbor.parse_raw_data_item a va)
    (fun _ -> aparse Cbor.parse_raw_data_item a va)
    True
    (fun res -> res == t va.contents)

inline_for_extraction [@@noextract_to "krml"]
let impl_typ_with_size (t: typ) =
  (#va: v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) ->
  (a: byte_array) ->
  (sz: SZ.t) ->
  ST bool
    (aparse Cbor.parse_raw_data_item a va)
    (fun _ -> aparse Cbor.parse_raw_data_item a va)
    (SZ.v sz == Seq.length (Cbor.serialize_raw_data_item va.contents))
    (fun res -> res == t va.contents)

inline_for_extraction [@@noextract_to "krml"]
let impl_typ_with_size_of_impl_typ
  (#t: typ)
  (i: impl_typ t)
: Tot (impl_typ_with_size t)
= fun a _ -> i a

module AP = LowParse.SteelST.ArrayPtr

inline_for_extraction [@@noextract_to "krml"]
let get_serialized_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#vp: v k t)
  (s: serializer p)
  (j: jumper p)
  (a: byte_array)
: ST SZ.t
    (aparse p a vp)
    (fun res -> aparse p a vp)
    True
    (fun res ->
      SZ.v res == AP.length (array_of vp) /\
      SZ.v res == Seq.length (serialize s vp.contents)
    )
=
  let vb = elim_aparse p a in
  parsed_data_is_serialize s (AP.contents_of vb);
  let res = j a in
  let _ = intro_aparse p a in
  return res

inline_for_extraction [@@noextract_to "krml"]
let impl_typ_of_impl_typ_with_size
  (#t: typ)
  (i: impl_typ_with_size t)
: Tot (impl_typ t)
= fun a ->
    let sz = get_serialized_size Cbor.serialize_raw_data_item CBOR.SteelST.Validate.jump_raw_data_item a in
    i a sz

inline_for_extraction [@@noextract_to "krml"]
let impl_t_choice
  (#t1 #t2: typ)
  (i1: impl_typ t1)
  (i2: impl_typ t2)
: Tot (impl_typ (t1 `t_choice` t2))
= fun a ->
    if i1 a
    then return true
    else i2 a

inline_for_extraction [@@noextract_to "krml"]
let impl_t_always_false : impl_typ t_always_false
= fun _ -> return false

inline_for_extraction [@@noextract_to "krml"]
let impl_rec_typ_body
  (f: (typ -> typ))
  (impl_f: (t: typ) -> impl_typ_with_size t -> impl_typ_with_size (f t))
  (impl_rec_typ: impl_typ_with_size (rec_typ f))
: Tot (impl_typ_with_size (rec_typ f))
= fun #va a sz ->
    [@@inline_let]
    let _ = assert (rec_typ f va.contents == f (rec_typ'_rec f va.contents (rec_typ f)) va.contents) by (FStar.Tactics.trefl ()) in
    impl_f
      (rec_typ'_rec f va.contents (rec_typ f))
      (fun #va' a' sz' -> if sz' `SZ.lt` sz then impl_rec_typ a' sz' else return false)
      #va a sz

[@@noextract_to "krml"] let rec impl_rec_typ_template // this cannot extract because I cannot use inline_for_extraction on recursive functions. This function only provides a template to create implementations for recursive types.
  (f: (typ -> typ))
  (impl_f: (t: typ) -> impl_typ_with_size t -> impl_typ_with_size (f t))
: Tot (impl_typ_with_size (rec_typ f))
= fun a sz -> impl_rec_typ_body f impl_f (impl_rec_typ_template f impl_f) a sz

inline_for_extraction [@@noextract_to "krml"]
let impl_any: impl_typ any = (fun _ -> return true)

inline_for_extraction [@@noextract_to "krml"]
let impl_uint : impl_typ uint
= fun a ->
    let mt = CBOR.SteelST.Validate.read_major_type a in
    return (mt = Cbor.major_type_uint64)

inline_for_extraction [@@noextract_to "krml"]
let impl_nint : impl_typ nint
= fun a ->
    let mt = CBOR.SteelST.Validate.read_major_type a in
    return (mt = Cbor.major_type_neg_int64)

inline_for_extraction [@@noextract_to "krml"]
let impl_t_int : impl_typ t_int
= impl_uint `impl_t_choice` impl_nint

inline_for_extraction [@@noextract_to "krml"]
let impl_bstr : impl_typ bstr
= fun a ->
    let mt = CBOR.SteelST.Validate.read_major_type a in
    return (mt = Cbor.major_type_byte_string)

inline_for_extraction [@@noextract_to "krml"]
let impl_bytes : impl_typ CDDL.Spec.bytes = impl_bstr

inline_for_extraction [@@noextract_to "krml"]
let impl_tstr : impl_typ tstr
= fun a ->
    let mt = CBOR.SteelST.Validate.read_major_type a in
    return (mt = Cbor.major_type_text_string)

inline_for_extraction [@@noextract_to "krml"]
let impl_text : impl_typ text = impl_tstr

inline_for_extraction [@@noextract_to "krml"]
let impl_t_simple_value_literal (s: Cbor.simple_value) : impl_typ (t_simple_value_literal s)
= fun a ->
    let mt = CBOR.SteelST.Validate.read_major_type a in
    if mt = Cbor.major_type_simple_value
    then begin
      let sv = CBOR.SteelST.Read.read_simple_value a in
      return (sv = s)
    end else begin
      return false
    end

inline_for_extraction [@@noextract_to "krml"]
let impl_t_false : impl_typ t_false
= impl_t_simple_value_literal simple_value_false

inline_for_extraction [@@noextract_to "krml"]
let impl_t_true : impl_typ t_true
= impl_t_simple_value_literal simple_value_true

inline_for_extraction [@@noextract_to "krml"]
let impl_t_bool : impl_typ t_bool
= impl_t_false `impl_t_choice` impl_t_true

inline_for_extraction [@@noextract_to "krml"]
let impl_t_nil : impl_typ t_nil
= impl_t_simple_value_literal simple_value_nil

inline_for_extraction [@@noextract_to "krml"]
let impl_t_null : impl_typ t_null
= impl_t_nil

inline_for_extraction [@@noextract_to "krml"]
let impl_t_undefined : impl_typ t_undefined
= impl_t_simple_value_literal simple_value_undefined

module U64 = FStar.UInt64

inline_for_extraction [@@noextract_to "krml"]
let impl_t_uint_literal (s: U64.t) : impl_typ (t_uint_literal s)
= fun a ->
    let mt = CBOR.SteelST.Validate.read_major_type a in
    if mt = Cbor.major_type_uint64
    then begin
      let sv = CBOR.SteelST.Read.read_int64 a in
      return (sv = s)
    end else begin
      return false
    end

module VC = LowParse.SteelST.VCList
module R = Steel.ST.Reference

[@@noextract_to "krml"]
let impl_array_group3_post
  (g: array_group3)
  (l l': list Cbor.raw_data_item)
  (res: bool)
: Tot prop
= res == Some? (g l) /\
  (res == true ==> g l == Some l')

[@@erasable]
noeq
type impl_array_group3_res
= {
    n: U64.t;
    al: byte_array;
    l: v (VC.parse_nlist_kind (U64.v n) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v n) Cbor.raw_data_item);
    res: bool;
  }

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3
  (g: array_group3)
: Tot Type
= (#n: Ghost.erased U64.t) ->
  (#al: Ghost.erased byte_array) ->
  (#l: v (VC.parse_nlist_kind (U64.v n) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v n) Cbor.raw_data_item)) ->
  (#res: Ghost.erased bool) ->
  (pn: R.ref U64.t) ->
  (pl: R.ref byte_array) ->
  (pres: R.ref bool) ->
  ST impl_array_group3_res
    (
      R.pts_to pn full_perm n `star`
      R.pts_to pl full_perm al `star`
      R.pts_to pres full_perm res `star`
      aparse (VC.parse_nlist (U64.v n) Cbor.parse_raw_data_item) al l
    )
    (fun res ->
      R.pts_to pn full_perm res.n `star`
      R.pts_to pl full_perm res.al `star`
      R.pts_to pres full_perm res.res `star`
      aparse (VC.parse_nlist (U64.v res.n) Cbor.parse_raw_data_item) res.al res.l `star`
      (aparse (VC.parse_nlist (U64.v res.n) Cbor.parse_raw_data_item) res.al res.l `implies_`
        aparse (VC.parse_nlist (U64.v n) Cbor.parse_raw_data_item) al l
      )
    )
    True
    (fun res ->
        impl_array_group3_post g l.contents res.l.contents res.res
    )

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3_always_false : impl_array_group3 array_group3_always_false
= fun #gn #ga #gl pn pl pres ->
    let w = {
      n = gn;
      al = ga;
      l = gl;
      res = false;
    }
    in
    R.write pres false;
    rewrite_with_implies
      (aparse (VC.parse_nlist (U64.v gn) Cbor.parse_raw_data_item) ga gl)
      (aparse (VC.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.al w.l);
    return w

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3_empty : impl_array_group3 array_group3_empty
= fun #gn #ga #gl pn pl pres ->
    let w = {
      n = gn;
      al = ga;
      l = gl;
      res = true;
    }
    in
    R.write pres true;
    rewrite_with_implies
      (aparse (VC.parse_nlist (U64.v gn) Cbor.parse_raw_data_item) ga gl)
      (aparse (VC.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.al w.l);
    return w

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3_concat
  (#g1 #g2: array_group3)
  (i1: impl_array_group3 g1)
  (i2: impl_array_group3 g2)
: impl_array_group3 (array_group3_concat g1 g2)
= fun #gn #ga #gl pn pl pres ->
    let w1 = i1 pn pl pres in
    let res1 = R.read pres in
    if res1
    then begin
      let w2 = i2 pn pl pres in
      implies_trans
        (aparse (VC.parse_nlist (U64.v w2.n) Cbor.parse_raw_data_item) w2.al w2.l)
        (aparse (VC.parse_nlist (U64.v w1.n) Cbor.parse_raw_data_item) w1.al w1.l)
        (aparse (VC.parse_nlist (U64.v gn) Cbor.parse_raw_data_item) ga gl);
      return w2
    end else begin
      noop ();
      return w1
    end

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3_choice
  (#g1 #g2: array_group3)
  (i1: impl_array_group3 g1)
  (i2: impl_array_group3 g2)
: Tot (impl_array_group3 (array_group3_choice g1 g2))
= fun #gn #ga #gl pn pl pres ->
    let n = R.read pn in
    let a = R.read pl in
    let w1 = i1 pn pl pres in
    let res1 = R.read pres in
    if res1
    then begin
      noop ();
      return w1
    end else begin
      R.write pn n;
      R.write pl a;
      elim_implies
        (aparse (VC.parse_nlist (U64.v w1.n) Cbor.parse_raw_data_item) w1.al w1.l)
        (aparse (VC.parse_nlist (U64.v gn) Cbor.parse_raw_data_item) ga gl);
      i2 #gn #ga #gl pn pl pres
    end

let impl_array_group3_res_strong
  (g: array_group3)
  (l: list Cbor.raw_data_item)
: Tot Type0
= (res: impl_array_group3_res { impl_array_group3_post g l res.l.contents res.res })

module GR = Steel.ST.GhostReference

unfold
let impl_array_group3_zero_or_more_inv_prop_gen
  (g: array_group3)
  (gn: Ghost.erased U64.t)
  (gl: list Cbor.raw_data_item)
  (wres: bool)
  (wl: list Cbor.raw_data_item)
  (cont: bool)
: Tot prop
= cont = not wres /\
  begin if cont
  then array_group3_zero_or_more g gl == array_group3_zero_or_more' g wl 
  else impl_array_group3_post (array_group3_zero_or_more g) gl wl wres
  end

let impl_array_group3_zero_or_more_inv_prop
  (g: array_group3)
  (gn: Ghost.erased U64.t)
  (gl: v (VC.parse_nlist_kind (U64.v gn) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v gn) Cbor.raw_data_item))
  (w: impl_array_group3_res)
  (cont: bool)
: Tot prop
= impl_array_group3_zero_or_more_inv_prop_gen g gn gl.contents w.res w.l.contents cont

[@@__reduce__]
let impl_array_group3_zero_or_more_inv_body
  (g: array_group3)
  (gn: Ghost.erased U64.t)
  (ga: Ghost.erased byte_array)
  (gl: v (VC.parse_nlist_kind (U64.v gn) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v gn) Cbor.raw_data_item))
  (pn: R.ref U64.t)
  (pl: R.ref byte_array)
  (pres: R.ref bool)
  (wn: U64.t)
  (wal: byte_array)
  (wl: v (VC.parse_nlist_kind (U64.v wn) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v wn) Cbor.raw_data_item))
  (wres: bool)
: Tot vprop
= 
  R.pts_to pn full_perm wn `star`
  R.pts_to pl full_perm wal `star`
  R.pts_to pres full_perm wres `star`
  aparse (VC.parse_nlist (U64.v wn) Cbor.parse_raw_data_item) wal wl `star`
  (aparse (VC.parse_nlist (U64.v wn) Cbor.parse_raw_data_item) wal wl `implies_`
    aparse (VC.parse_nlist (U64.v gn) Cbor.parse_raw_data_item) ga gl
  )

[@@__reduce__]
let impl_array_group3_zero_or_more_inv0
  (g: array_group3)
  (gn: Ghost.erased U64.t)
  (ga: Ghost.erased byte_array)
  (gl: v (VC.parse_nlist_kind (U64.v gn) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v gn) Cbor.raw_data_item))
  (pn: R.ref U64.t)
  (pl: R.ref byte_array)
  (pres: R.ref bool)
  (pw: GR.ref impl_array_group3_res)
  (cont: bool)
: Tot vprop
= exists_ (fun w ->
    GR.pts_to pw full_perm w `star`
    impl_array_group3_zero_or_more_inv_body g gn ga gl pn pl pres w.n w.al w.l w.res `star`
    pure (impl_array_group3_zero_or_more_inv_prop g gn gl w cont)
  )

let impl_array_group3_zero_or_more_inv
  (g: array_group3)
  (gn: Ghost.erased U64.t)
  (ga: Ghost.erased byte_array)
  (gl: v (VC.parse_nlist_kind (U64.v gn) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v gn) Cbor.raw_data_item))
  (pn: R.ref U64.t)
  (pl: R.ref byte_array)
  (pres: R.ref bool)
  (pw: GR.ref impl_array_group3_res)
  (cont: bool)
: Tot vprop
= impl_array_group3_zero_or_more_inv0 g gn ga gl pn pl pres pw cont

let intro_impl_array_group3_zero_or_more_inv
  (#opened: _)
  (#w': impl_array_group3_res)
  (g: array_group3)
  (gn: Ghost.erased U64.t)
  (ga: Ghost.erased byte_array)
  (gl: v (VC.parse_nlist_kind (U64.v gn) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v gn) Cbor.raw_data_item))
  (pn: R.ref U64.t)
  (pl: R.ref byte_array)
  (pres: R.ref bool)
  (pw: GR.ref impl_array_group3_res)
  (wn: U64.t)
  (wal: byte_array)
  (wl: v (VC.parse_nlist_kind (U64.v wn) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v wn) Cbor.raw_data_item))
  (wres: bool)
  (cont: bool)
: STGhost unit opened
    (impl_array_group3_zero_or_more_inv_body g gn ga gl pn pl pres wn wal wl wres `star`
      GR.pts_to pw full_perm w'
    )
    (fun _ -> impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw cont)
    (impl_array_group3_zero_or_more_inv_prop_gen g gn gl.contents wres wl.contents cont)
    (fun _ -> True)
= let w = {
    al = wal;
    n = wn;
    l = wl;
    res = wres;
  }
  in
  rewrite
    (impl_array_group3_zero_or_more_inv_body g gn ga gl pn pl pres wn wal wl wres)
    (impl_array_group3_zero_or_more_inv_body g gn ga gl pn pl pres w.n w.al w.l w.res);
  GR.write pw w;
  rewrite
    (impl_array_group3_zero_or_more_inv0 g gn ga gl pn pl pres pw cont)
    (impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw cont)

let elim_impl_array_group3_zero_or_more_inv
  (#opened: _)
  (g: array_group3)
  (gn: Ghost.erased U64.t)
  (ga: Ghost.erased byte_array)
  (gl: v (VC.parse_nlist_kind (U64.v gn) Cbor.parse_raw_data_item_kind) (VC.nlist (U64.v gn) Cbor.raw_data_item))
  (pn: R.ref U64.t)
  (pl: R.ref byte_array)
  (pres: R.ref bool)
  (pw: GR.ref impl_array_group3_res)
  (cont: bool)
: STGhost impl_array_group3_res opened
    (impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw cont)
    (fun w -> impl_array_group3_zero_or_more_inv_body g gn ga gl pn pl pres w.n w.al w.l w.res `star`
      GR.pts_to pw full_perm w
    )
    True
    (fun w -> impl_array_group3_zero_or_more_inv_prop g gn gl w cont)
= rewrite
    (impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw cont)
    (impl_array_group3_zero_or_more_inv0 g gn ga gl pn pl pres pw cont);
  let _ = gen_elim () in
  let w = vpattern_replace (GR.pts_to pw full_perm) in
  rewrite
    (impl_array_group3_zero_or_more_inv_body g gn ga gl pn pl pres _ _ _ _)
    (impl_array_group3_zero_or_more_inv_body g gn ga gl pn pl pres w.n w.al w.l w.res);
  w

#pop-options

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3_zero_or_more
  (#g: array_group3)
  (i: impl_array_group3 g)
: Tot (impl_array_group3 (array_group3_zero_or_more g))
= fun #gn #ga #gl pn pl pres ->
    R.write pres false;
    implies_refl (aparse (VC.parse_nlist (U64.v gn) Cbor.parse_raw_data_item) ga gl);
    let w0 = {
      n = gn;
      al = ga;
      l = gl;
      res = false;
    }
    in
    let pw = GR.alloc w0 in
    intro_impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw _ _ _ _ true;
    Steel.ST.Loops.while_loop
      (impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw)
      (fun _ ->
        let gcont = elim_exists #_ #_ #(impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw) () in
        let _ = elim_impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw gcont in
        let res = R.read pres in
        [@@inline_let]
        let cont = not res in
        intro_impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw _ _ _ _ cont;
        return cont
      )
      (fun _ ->
        let w0 = elim_impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw true in
        let al = R.read pl in
        let n = R.read pn in
        let w = i pn pl pres in
        let res = R.read pres in
        let n' = R.read pn in
        let res = res && (n' `U64.lt` n) in
        R.write pres (not res);
        if res
        then begin
          implies_trans
            (aparse (VC.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.al w.l)
            (aparse (VC.parse_nlist (U64.v w0.n) Cbor.parse_raw_data_item) w0.al w0.l)
            (aparse (VC.parse_nlist (U64.v gn) Cbor.parse_raw_data_item) ga gl);
          intro_impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw _ _ _ _ true;
          noop ()
        end else begin
          elim_implies
            (aparse (VC.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.al w.l)
            (aparse (VC.parse_nlist (U64.v w0.n) Cbor.parse_raw_data_item) w0.al w0.l);
          R.write pn n;
          R.write pl al;
          vpattern_rewrite (R.pts_to pn full_perm) w0.n;
          vpattern_rewrite (R.pts_to pl full_perm) w0.al;
          intro_impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw _ _ _ _ false;
          noop ()
        end
      );
    let w = elim_impl_array_group3_zero_or_more_inv g gn ga gl pn pl pres pw false in
    GR.free pw;
    return w

#pop-options

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3_one_or_more
  (#g: array_group3)
  (i: impl_array_group3 g)
: Tot (impl_array_group3 (array_group3_one_or_more g))
= i `impl_array_group3_concat` impl_array_group3_zero_or_more i

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3_zero_or_one
  (#g: array_group3)
  (i: impl_array_group3 g)
: Tot (impl_array_group3 (array_group3_zero_or_one g))
= i `impl_array_group3_choice` impl_array_group3_empty

[@@erasable]
noeq
type ghost_focus_nlist_res (k: parser_kind) (t: Type0) = {
  n: nat;
  a2: byte_array;
  va1: v k t;
  va2: v (VC.parse_nlist_kind n k) (VC.nlist n t);
}

#push-options "--z3rlimit 32"
#restart-solver

let ghost_focus_nlist
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (n: nat)
  (#va: v _ _)
  (a: byte_array)
: STGhost (ghost_focus_nlist_res k t) opened
    (aparse (VC.parse_nlist n p) a va)
    (fun w ->
      aparse p a w.va1 `star`
      aparse (VC.parse_nlist w.n p) w.a2 w.va2 `star`
      ((aparse p a w.va1 `star`
        aparse (VC.parse_nlist w.n p) w.a2 w.va2) `implies_`
        aparse (VC.parse_nlist n p) a va
    ))
    (Cons? va.contents /\
      n > 0 /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun w ->
      n == w.n + 1 /\
      va.contents == w.va1.contents :: w.va2.contents /\
      AP.merge_into (array_of w.va1) (array_of w.va2) (array_of va)
    )
= let n_pred : nat = n - 1 in
  let a2 = VC.elim_nlist_cons p n n_pred a in
  let _ = gen_elim () in
  let va1 = vpattern_replace (aparse p a) in
  let va2 = vpattern_replace (aparse (VC.parse_nlist n_pred p) a2) in
  let w = {
    n = n_pred;
    a2 = Ghost.reveal a2;
    va1 = va1;
    va2 = va2;
  }
  in
  vpattern_rewrite (aparse p a) w.va1;
  rewrite (aparse _ a2 _) (aparse (VC.parse_nlist w.n p) w.a2 w.va2);
  intro_implies
    (aparse p a w.va1 `star`
      aparse (VC.parse_nlist w.n p) w.a2 w.va2)
    (aparse (VC.parse_nlist n p) a va)
    emp
    (fun _ ->
      let _ = VC.intro_nlist_cons n p w.n a w.a2 in
      vpattern_rewrite (aparse _ a) va
    );
  w

#pop-options

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction [@@noextract_to "krml"]
let impl_array_group3_item
  (#t: typ)
  (i: impl_typ t)
: Tot (impl_array_group3 (array_group3_item t))
= fun #gn #ga #gl pn pl pres ->
    let n = R.read pn in
    if n = 0uL
    then begin
      noop ();
      impl_array_group3_always_false pn pl pres
    end else begin
      let wcons = ghost_focus_nlist Cbor.parse_raw_data_item _ ga in
      let a = R.read pl in
      vpattern_rewrite_with_implies #_ #_ #(Ghost.reveal ga) (fun a -> aparse _ a _) a;
      if i a
      then begin
        let a2 = hop_aparse_aparse_with_implies Cbor.jump_raw_data_item _ a _ in
        [@@inline_let]
        let n' : U64.t = n `U64.sub` 1uL in
        let gl' = rewrite_aparse_with_implies a2 (VC.parse_nlist (U64.v n') Cbor.parse_raw_data_item) in
        R.write pn n';
        R.write pl a2;
        R.write pres true;
        let w : impl_array_group3_res = {
          al = a2; 
          n = n `U64.sub` 1uL;
          l = gl';
          res = true;
        }
        in
        rewrite_with_implies (aparse _ a2 _) (aparse (VC.parse_nlist (U64.v w.n) Cbor.parse_raw_data_item) w.al w.l);
        implies_trans (aparse _ w.al _) (aparse _ a2 _) (aparse _ a2 _);
        implies_trans (aparse _ w.al _) (aparse _ a2 _) (aparse _ wcons.a2 _);
        implies_join
          (aparse _ a _) (aparse _ ga _)
          (aparse _ w.al _) (aparse _ wcons.a2 _);
        implies_trans
          (aparse _ a _ `star` aparse _ w.al _)
          (aparse _ ga _ `star` aparse _ wcons.a2 _)
          (aparse _ ga _);
        implies_curry (aparse _ a _) (aparse _ w.al _) (aparse _ ga _);
        elim_implies (aparse _ a _) (aparse _ w.al _ `implies_` aparse _ ga _);
        return w
      end else begin
        elim_implies (aparse _ a _) (aparse _ ga _);
        elim_implies (aparse _ ga _ `star` aparse _ _ _) (aparse _ ga _);
        impl_array_group3_always_false pn pl pres
      end
    end

#pop-options

inline_for_extraction [@@noextract_to "krml"]
let impl_t_array3_res
  (g: array_group3)
  (va: v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
: Tot Type0
= (res: bool { res == t_array3 g va.contents })

inline_for_extraction [@@noextract_to "krml"]
let impl_t_array3
  (#g: array_group3)
  (i: impl_array_group3 g)
: Tot (impl_typ (t_array3 g))
= fun #va a ->
    let mt = CBOR.SteelST.Validate.read_major_type a in
    if mt = Cbor.major_type_array
    then begin
      noop ();
      let res : impl_t_array3_res g va =
        R.with_local 0uL (fun pn ->
        R.with_local a (fun pa ->
        R.with_local false (fun pres ->
          let wl = CBOR.SteelST.Array.focus_array pn pa a in
          let wi = i pn pa pres in
          let res0 = R.read pres in
          let n = R.read pn in
          let res : impl_t_array3_res g va = res0 && (n = 0uL) in
          elim_implies
            (aparse (VC.parse_nlist (U64.v wi.n) Cbor.parse_raw_data_item) wi.al wi.l)
            (aparse (VC.parse_nlist (U64.v wl.n) Cbor.parse_raw_data_item) wl.a wl.l);
          elim_implies
            (aparse (VC.parse_nlist (U64.v wl.n) Cbor.parse_raw_data_item) wl.a wl.l)
            (aparse Cbor.parse_raw_data_item a va);
          return res
        )))
      in
      return (res <: bool)
    end else begin
      return false
    end

let rec sieve_list
  (l: list map_group_entry)
  (l': list bool { List.Tot.length l' == List.Tot.length l })
: Tot (list map_group_entry)
  (decreases l)
= match l, l' with
  | a :: q, true :: q' -> a :: sieve_list q q'
  | _ :: q, false :: q' -> sieve_list q q'
  | _ -> []

let rec sieve_list_append
  (l1: list map_group_entry)
  (l1': list bool { List.Tot.length l1' == List.Tot.length l1 })
  (l2: list map_group_entry)
  (l2': list bool { List.Tot.length l2' == List.Tot.length l2 })
: Lemma
  (ensures (
    List.Tot.length (l1 `List.Tot.append` l2) == List.Tot.length (l1' `List.Tot.append` l2') /\
    sieve_list (l1 `List.Tot.append` l2) (l1' `List.Tot.append` l2') == sieve_list l1 l1' `List.Tot.append` sieve_list l2 l2'
  ))
  (decreases l1)
= List.Tot.append_length l1 l2;
  List.Tot.append_length l1' l2';
  match l1, l1' with
  | _ :: q, _ :: q' -> sieve_list_append q q' l2 l2'
  | _ -> ()

let list_rev_eq
  (#t: Type)
  (a: t)
  (q: list t)
: Lemma
  (List.Tot.rev (a :: q) == List.Tot.rev q `List.Tot.append` [a])
= List.Tot.rev_rev' (a :: q);
  List.Tot.rev_rev' q

let rec sieve_list_rev
  (l1: list map_group_entry)
  (l1': list bool { List.Tot.length l1' == List.Tot.length l1 })
: Lemma
  (ensures (
    List.Tot.length (List.Tot.rev l1) == List.Tot.length (List.Tot.rev l1') /\
    sieve_list (List.Tot.rev l1) (List.Tot.rev l1') == List.Tot.rev (sieve_list l1 l1')
  ))
  (decreases (List.Tot.length l1))
= List.Tot.rev_length l1;
  List.Tot.rev_length l1';
  match l1, l1' with
  | a :: q, a' :: q' ->
    list_rev_eq a q;
    list_rev_eq a' q';
    sieve_list_rev q q';
    sieve_list_append (List.Tot.rev q) (List.Tot.rev q') [a] [a'];
    List.Tot.rev_append (sieve_list [a] [a']) (sieve_list q q')
  | _ -> ()

let rec matches_list_map_group_entry2'
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
  (unmatched: list bool)
  (l: list map_group_entry)
  (l': list bool { List.Tot.length l' == List.Tot.length l })
: GTot (option (list bool))
    (decreases l)
= match l, l' with
  | a :: q, true :: q' ->
    if matches_map_group_entry a x
    then Some (List.Tot.rev_acc (false :: unmatched) q')
    else matches_list_map_group_entry2' x (true :: unmatched) q q'
  | a :: q, false :: q' ->
    matches_list_map_group_entry2' x (false :: unmatched) q q'
  | _ -> None

let rec matches_list_map_group_entry2'_correct
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
  (unmatched0: list map_group_entry)
  (unmatched: list map_group_entry)
  (unmatched': list bool)
  (l0: list map_group_entry)
  (l: list map_group_entry)
  (l': list bool)
: Lemma
  (requires (
    List.Tot.length unmatched' == List.Tot.length unmatched0 /\
    unmatched == sieve_list unmatched0 unmatched' /\
    List.Tot.length l' == List.Tot.length l0 /\
    l == sieve_list l0 l'
  ))
  (ensures (
    match matches_list_map_group_entry' x unmatched l, matches_list_map_group_entry2' x unmatched' l0 l' with
    | None, None -> True
    | Some q, Some q' ->
      List.Tot.length q' == List.Tot.length (List.Tot.rev_acc unmatched0 l0) /\
      q == sieve_list (List.Tot.rev_acc unmatched0 l0) q'
    | _ -> False
  ))
  (decreases l0)
= admit ()

let matches_list_map_group_entry2
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
  (l: list map_group_entry)
  (l': list bool { List.Tot.length l' == List.Tot.length l })
: GTot (option (list bool))
= matches_list_map_group_entry2' x [] l l'

let matches_list_map_group_entry2_correct
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
  (l0: list map_group_entry)
  (l: list map_group_entry)
  (l': list bool)
: Lemma
  (requires (
    List.Tot.length l' == List.Tot.length l0 /\
    l == sieve_list l0 l'
  ))
  (ensures (
    match matches_list_map_group_entry x l, matches_list_map_group_entry2 x l0 l' with
    | None, None -> True
    | Some q, Some q' ->
      List.Tot.length q' == List.Tot.length l0 /\
      q == sieve_list l0 q'
    | _ -> False
  ))
= matches_list_map_group_entry2'_correct x [] [] [] l0 l l'

let rec pts_to_list
  (#t: Type)
  (lr: list (R.ref t))
  (lv: list t)
: Tot vprop
= match lr, lv with
  | [], [] -> emp
  | r :: lr', v :: lv' -> R.pts_to r full_perm v `star` pts_to_list lr' lv'
  | _ -> pure (squash False)

let rec pts_to_list_length
  (#opened: _)
  (#t: Type)
  (lr: list (R.ref t))
  (lv: list t)
: STGhost unit opened
    (pts_to_list lr lv)
    (fun _ -> pts_to_list lr lv)
    True
    (fun _ -> List.Tot.length lr == List.Tot.length lv)
    (decreases lr)
= match lr, lv with
  | [], [] -> noop ()
  | r :: lr', v :: lv' ->
    rewrite (pts_to_list lr lv) (R.pts_to r full_perm v `star` pts_to_list lr' lv');
    pts_to_list_length lr' lv';
    rewrite (R.pts_to r full_perm v `star` pts_to_list lr' lv') (pts_to_list lr lv)
  | _ ->
    rewrite (pts_to_list lr lv) (pure (squash False));
    elim_pure (squash False);
    rewrite emp (pts_to_list lr lv) // by contradiction

let rec intro_pts_to_list_append
  (#opened: _)
  (#t: Type)
  (lr1: list (R.ref t))
  (lv1: list t)
  (lr2: list (R.ref t))
  (lv2: list t)
: STGhostT unit opened
    (pts_to_list lr1 lv1 `star` pts_to_list lr2 lv2)
    (fun _ -> pts_to_list (lr1 `List.Tot.append` lr2) (lv1 `List.Tot.append` lv2))
    (decreases lr1)
= match lr1, lv1 with
  | [], [] ->
    rewrite (pts_to_list lr1 lv1) emp;
    rewrite (pts_to_list lr2 lv2) (pts_to_list (lr1 `List.Tot.append` lr2) (lv1 `List.Tot.append` lv2))
  | r :: lr', v :: lv' ->
    rewrite (pts_to_list lr1 lv1) (R.pts_to r full_perm v `star` pts_to_list lr' lv');
    intro_pts_to_list_append lr' lv' lr2 lv2;
    rewrite
      (R.pts_to r full_perm v `star` pts_to_list (lr' `List.Tot.append` lr2) (lv' `List.Tot.append` lv2))
      (pts_to_list (lr1 `List.Tot.append` lr2) (lv1 `List.Tot.append` lv2))
  | _ ->
    rewrite (pts_to_list lr1 lv1) (pure (squash False));
    elim_pure (squash False);
    rewrite (pts_to_list lr2 lv2) (pts_to_list (lr1 `List.Tot.append` lr2) (lv1 `List.Tot.append` lv2)) // by contradiction

let rec intro_pts_to_list_rev
  (#opened: _)
  (#t: Type)
  (lr: list (R.ref t))
  (lv: list t)
: STGhostT unit opened
    (pts_to_list lr lv)
    (fun _ -> pts_to_list (List.Tot.rev lr) (List.Tot.rev lv))
    (decreases lr)
= match lr, lv with
  | [], [] ->
    rewrite (pts_to_list lr lv) (pts_to_list (List.Tot.rev lr) (List.Tot.rev lv))
  | r :: lr', v :: lv' ->
    rewrite (pts_to_list lr lv) (R.pts_to r full_perm v `star` pts_to_list lr' lv');
    intro_pts_to_list_rev lr' lv';
    List.Tot.rev_append [r] lr';
    List.Tot.rev_append [v] lv';
    rewrite (R.pts_to r full_perm v `star` emp) (pts_to_list (List.Tot.rev [r]) (List.Tot.rev [v]));
    intro_pts_to_list_append (List.Tot.rev lr') (List.Tot.rev lv') (List.Tot.rev [r]) (List.Tot.rev [v]);
    rewrite (pts_to_list _ _) (pts_to_list (List.Tot.rev lr) (List.Tot.rev lv))
  | _ ->
    rewrite (pts_to_list lr lv) (pure (squash False));
    elim_pure (squash False);
    rewrite emp (pts_to_list (List.Tot.rev lr) (List.Tot.rev lv)) // by contradiction

let rec elim_pts_to_list_append
  (#opened: _)
  (#t: Type)
  (lr1: list (R.ref t))
  (lv1: list t)
  (lr2: list (R.ref t))
  (lv2: list t)
: STGhost unit opened
    (pts_to_list (lr1 `List.Tot.append` lr2) (lv1 `List.Tot.append` lv2))
    (fun _ -> pts_to_list lr1 lv1 `star` pts_to_list lr2 lv2)
    (List.Tot.length lr1 == List.Tot.length lv1)
    (fun _ -> True)
    (decreases lr1)
= match lr1, lv1 with
  | [], [] ->
    rewrite (pts_to_list (lr1 `List.Tot.append` lr2) (lv1 `List.Tot.append` lv2)) (pts_to_list lr2 lv2);
    rewrite emp (pts_to_list lr1 lv1)
  | r :: lr', v :: lv' ->
    rewrite (pts_to_list (lr1 `List.Tot.append` lr2) (lv1 `List.Tot.append` lv2))
      (R.pts_to r full_perm v `star` pts_to_list (lr' `List.Tot.append` lr2) (lv' `List.Tot.append` lv2));
    elim_pts_to_list_append lr' lv' lr2 lv2;
    rewrite
      (R.pts_to r full_perm v `star` pts_to_list lr' lv')
      (pts_to_list lr1 lv1)

inline_for_extraction [@@noextract_to "krml"]
let impl_matches_list_map_group_entry2'_t
  (l: list map_group_entry)
  (lr: list (R.ref bool))
: Tot Type
= (gx1: v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) ->
  (gx2: v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) ->
  (x1: byte_array) ->
  (x2: byte_array) ->
  (unmatched_r: Ghost.erased (list (R.ref bool))) ->
  (unmatched: Ghost.erased (list bool)) ->
  (l': Ghost.erased (list bool) { List.Tot.length l' == List.Tot.length l }) ->
  STT (option (R.ref bool))
    (pts_to_list unmatched_r unmatched `star`
      pts_to_list lr l' `star`
      aparse Cbor.parse_raw_data_item x1 gx1 `star`
      aparse Cbor.parse_raw_data_item x2 gx2
    )
    (fun res ->
      aparse Cbor.parse_raw_data_item x1 gx1 `star`
      aparse Cbor.parse_raw_data_item x2 gx2 `star`
      begin match res with
      | None ->
        pts_to_list unmatched_r unmatched `star`
        pts_to_list lr l' `star`
        pure (matches_list_map_group_entry2' (gx1.contents, gx2.contents) unmatched l l' == None)
      | Some r' ->
        exists_ (fun lrl -> exists_ (fun lrr -> exists_ (fun lvl -> exists_ (fun lvr ->
          pts_to_list lrl lvl `star`
          pts_to_list lrr lvr `star`
          R.pts_to r' full_perm false `star`
          pure (
            matches_list_map_group_entry2' (gx1.contents, gx2.contents) unmatched l l' == Some (lvl `List.Tot.append` (false :: lvr)) /\
            Ghost.reveal unmatched `List.Tot.append` Ghost.reveal l' == lvl `List.Tot.append` (true :: lvr)
          )
        ))))
      end
    )


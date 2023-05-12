module Test

open Steel.ST.GenElim

module A = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference

open LowParse.SteelST.Int
open LowParse.SteelST.BoundedInt
open LowParse.SteelST.VLData
open LowParse.SteelST.List

module U16 = FStar.UInt16
module U32 = FStar.UInt32

module C = C // for dependencies only (_zero_for_deref)

let test_accessor
  (#vb: v _ _)
  (b: byte_array)
: STT U16.t
    (aparse (parse_u16 `nondep_then` parse_u16) b vb)
    (fun r -> aparse (parse_u16 `nondep_then` parse_u16) b vb `star`
      pure (U16.v r == U16.v (fstp vb.contents) \/ U16.v r == U16.v (sndp vb.contents)))
= with_pair_fst parse_u16 parse_u16 b (fun bf ->
    with_pair_snd jump_u16 parse_u16 b (fun bs ->
      let f = read_u16 bf in
      let s = read_u16 bs in
      let res = 
        if f `U16.lt` s
        then s
        else f
      in
      noop ();
      return res
  ))

inline_for_extraction noextract
let u16_max (x1 x2: U16.t) : Tot U16.t
= if x1 `U16.lte` x2 then x2 else x1

[@@__reduce__]
let p = parse_vldata 1 (parse_list parse_u16)

let q = p

// let validate_p : validator q = validate_vldata_gen 1 (unconstrained_bounded_integer 1) (fun _ -> true) (validate_list_total_constant_size parse_u16 (SZ.mk_size_t 2ul))
let validate_p : validator q = validate_vldata_gen 1 (unconstrained_bounded_integer 1) (fun _ -> true) (validate_list validate_u16)

let state (_: U16.t) (_: list U16.t) : Tot vprop = emp

inline_for_extraction
noextract
let iter_max
  (#va: _)
  (a: byte_array)
  (len: SZ.t)
: ST U16.t
    (aparse (parse_list parse_u16) a va)
    (fun _ -> aparse (parse_list parse_u16) a va)
    (SZ.v len == A.length (array_of' va))
    (fun _ -> True)
=
    rewrite emp (state _ _);
    let res = list_iter jump_u16 u16_max state
      (fun va a accu l ->
        rewrite (state _ _) emp;
        let wa = read_u16 a in
        let res = u16_max accu wa in
        rewrite emp (state _ _);
        return res
      )
      a len 0us
    in
    rewrite (state _ _) emp;
    return res

inline_for_extraction
noextract
let mk_size_t (sq: squash SZ.fits_u32) (x: U32.t) : Tot SZ.t = SZ.uint32_to_sizet x

#push-options "--z3rlimit 64"
#restart-solver

let test (a: byte_array) (#va: _) (len: SZ.t)
: ST U16.t
  (A.arrayptr a va)
  (fun _ -> A.arrayptr a va)
  (SZ.v len == A.length (A.array_of va))
  (fun _ -> True)
= let sq = Steel.ST.Array.intro_fits_u32 () in
  with_local 0ul (fun perr ->
  let sz = validate_p a len perr in
  let _ = gen_elim () in
  let err = R.read perr in
  if err = 0ul
  then begin
    let ar = ghost_peek_strong p a in
    let _ = gen_elim () in
    let gac = ghost_elim_vldata_gen _ _ _ a in
    let _ = gen_elim () in
    let acsz = read_bounded_integer _ a in
    let ac = hop_aparse_aparse (jump_bounded_integer 1) _ a gac in
    let res = iter_max ac (mk_size_t sq acsz) in
    let _ = intro_vldata_gen 1 (unconstrained_bounded_integer 1) _ a ac in
    unpeek_strong a va ar;
    return res
  end
  else begin
    noop ();
    return 0us
  end
  )

#pop-options

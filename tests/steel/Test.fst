module Test

open Steel.ST.GenElim

module A = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt
module R = Steel.ST.Reference

open LowParse.SteelST.Int
open LowParse.SteelST.BoundedInt
open LowParse.SteelST.VLData
open LowParse.SteelST.List

module U16 = FStar.UInt16
module U32 = FStar.UInt32

module F = LowParse.SteelST.Fold

let test_prog_1 = F.run_prog
  (F.impl_bind
    _
    (F.impl_u8 (F.initial_ser_index F.TU8))
    _
    (fun w ->
      F.impl_action
        _
        (F.impl_ser_u8 w ())
        _
    )
  )

let test_prog_2 = F.run_prog
      (F.impl_bind
        _
        (F.impl_action _ (F.impl_ser_u8 #_ #(F.initial_ser_index F.TU8) 42uy ()) _)
        _
        (fun _ -> F.impl_list
          _
          (F.impl_ret #_ #_ #_ #F.TU8 ())
          (jump_weaken F.pkind (jump_constant_size parse_u8  SZ.one_size) ())
        )
      )

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
  (len: SZ.size_t)
: ST U16.t
    (aparse (parse_list parse_u16) a va)
    (fun _ -> aparse (parse_list parse_u16) a va)
    (SZ.size_v len == A.length (array_of' va))
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

#push-options "--z3rlimit 128"

let test (a: byte_array) (#va: _) (len: SZ.size_t) (perr: R.ref U32.t)
: ST U16.t
  (A.arrayptr a va `star` exists_ (fun v -> R.pts_to perr full_perm v))
  (fun _ -> A.arrayptr a va `star` exists_ (fun v -> R.pts_to perr full_perm v))
  (SZ.size_v len == A.length (A.array_of va))
  (fun _ -> True)
= let _ = gen_elim () in
  R.write perr 0ul;
  let sz = validate_p a len perr in
  let _ = gen_elim () in
  let err = R.read perr in
  if err = 0ul
  then begin
    let ar = peek_strong_with_size p a sz in
    let _ = gen_elim () in
    let gac = ghost_elim_vldata_gen _ _ _ a in
    let _ = gen_elim () in
    let acsz = read_bounded_integer _ a in
    let ac = hop_aparse_aparse (jump_bounded_integer 1) _ a gac in
    let res = iter_max ac (SZ.mk_size_t acsz) in
    let _ = intro_vldata_gen _ _ _ a ac in
    let va' = elim_aparse p a in
    parse_injective p (Seq.slice (A.contents_of' va) 0 (SZ.size_v sz)) (A.contents_of' va');
    Seq.lemma_split (A.contents_of' va) (SZ.size_v sz);
    let _ = A.join a ar in
    return res
  end
  else begin
    noop ();
    return 0us
  end

#pop-options

let main () = C.EXIT_SUCCESS

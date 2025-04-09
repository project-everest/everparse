module Sign
#lang-pulse
open Pulse
open COSE.Format

let specnint_of_int (i: int { - pow2 64 <= i /\ i < 0 }) : GTot spect_evercddl_nint_pretty =
  Mkspect_evercddl_nint_pretty0 (UInt64.uint_to_t (-i-1))

let specuint_of_int (i: int { 0 <= i /\ i < pow2 64 }) : GTot spect_evercddl_uint_pretty =
  Mkspect_evercddl_uint_pretty0 (UInt64.uint_to_t i)

let specint_of_int (i: int { -pow2 64 <= i /\ i < pow2 64 }) : GTot spect_evercddl_int_pretty =
  if i >= 0 then
    Mkspect_evercddl_int_pretty0 (specuint_of_int i)
  else
    Mkspect_evercddl_int_pretty1 (specnint_of_int i)

inline_for_extraction
let i32_to_u64_safe (i: Int32.t { Int32.v i >= 0 }) : j:UInt64.t { UInt64.v j == Int32.v i } =
  Math.Lemmas.pow2_lt_compat 64 31;
  Math.Lemmas.small_mod (Int32.v i) (pow2 64);
  Int.Cast.int32_to_uint64 i

let specint_of_i32 (i: Int32.t) : GTot spect_evercddl_int_pretty =
  Math.Lemmas.pow2_lt_compat 64 31;
  specint_of_int (Int32.v i)

let rel_evercddl_uint_eq a b : squash (rel_evercddl_uint a b == pure (Mkevercddl_uint_pretty0?._x0 a == Mkspect_evercddl_uint_pretty0?._x0 b)) = ()
let rel_evercddl_nint_eq a b : squash (rel_evercddl_nint a b == pure (Mkevercddl_nint_pretty0?._x0 a == Mkspect_evercddl_nint_pretty0?._x0 b)) = ()

let rel_evercddl_int_eq a b : squash (rel_evercddl_int a b ==
  (match a, b with
   | Mkevercddl_int_pretty0 a, Mkspect_evercddl_int_pretty0 b -> rel_evercddl_uint a b
   | Mkevercddl_int_pretty1 a, Mkspect_evercddl_int_pretty1 b -> rel_evercddl_nint a b
   | _ -> pure False)) =
  ()

ghost fn rw_r #a #b (h: squash (a == b)) requires a ensures b { rewrite a as b }
ghost fn rw_l #a #b (h: squash (a == b)) requires b ensures a { rewrite b as a }

let i32_lt_iff a b : squash (Int32.lt a b <==> Int32.v a < Int32.v b) = ()

fn mk_int (i: Int32.t)
  returns j: evercddl_int_pretty
  ensures rel_evercddl_int j (specint_of_i32 i)
{
  if Int32.lt i 0l {
    i32_lt_iff i 0l; assert pure (Int32.v i < Int32.v 0l);
    let k = Int32.sub (-1l) i;
    let j = i32_to_u64_safe k;
    Math.Lemmas.pow2_lt_compat 64 31;
    rw_l (rel_evercddl_nint_eq (Mkevercddl_nint_pretty0 j) (specnint_of_int (Int32.v i)));
    rw_l (rel_evercddl_int_eq (Mkevercddl_int_pretty1 (Mkevercddl_nint_pretty0 j)) (Mkspect_evercddl_int_pretty1 (specnint_of_int (Int32.v i))));
    rewrite each Mkspect_evercddl_int_pretty1 (specnint_of_int (Int32.v i)) as specint_of_i32 i;
    Mkevercddl_int_pretty1 (Mkevercddl_nint_pretty0 j)
  } else {
    let j = i32_to_u64_safe i;
    rw_l (rel_evercddl_uint_eq (Mkevercddl_uint_pretty0 j) (specuint_of_int (UInt64.v j)));
    rw_l (rel_evercddl_int_eq (Mkevercddl_int_pretty0 (Mkevercddl_uint_pretty0 j)) (Mkspect_evercddl_int_pretty0 (specuint_of_int (UInt64.v j))));
    rewrite each Mkspect_evercddl_int_pretty0 (specuint_of_int (UInt64.v j)) as specint_of_i32 i;
    Mkevercddl_int_pretty0 (Mkevercddl_uint_pretty0 j)
  }
}
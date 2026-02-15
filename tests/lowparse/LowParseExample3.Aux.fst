module LowParseExample3.Aux
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = FStar.Buffer
module M = FStar.Modifies
module HST = FStar.HyperStack.ST

include LowParse.Low

type t = {
  a: U16.t;
  b: U32.t;
  c: U16.t;
}

let synth_t ((x, y), z) = {a=x; b=y; c=z}

let parse_t : parser _ t =
  (parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16)
  `parse_synth` synth_t

inline_for_extraction
let validate_t : validator parse_t =
  validate_total_constant_size parse_t 8uL ()
(*
  validate32_synth
  (validate32_u16 `validate32_nondep_then` validate32_u32 `validate32_nondep_then` validate32_u16)
  synth_t
  ()
*)

let synth_t_recip x = ((x.a, x.b), x.c)

let clens_a : clens t U16.t = {
  clens_cond =  (fun _ -> True);
  clens_get = (fun x -> x.a);
}

let gaccess_a : gaccessor parse_t parse_u16 clens_a =
  gaccessor_ext
    ((gaccessor_synth (parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16) synth_t synth_t_recip ()
     `gaccessor_compose`
     gaccessor_fst (parse_u16 `nondep_then` parse_u32) () parse_u16)
     `gaccessor_compose`
     gaccessor_fst parse_u16 () parse_u32)
    clens_a
    ()

inline_for_extraction
let access_a : accessor gaccess_a =
  accessor_ext
    (accessor_compose
      (accessor_compose
        (accessor_synth (parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16) synth_t synth_t_recip ())
        (accessor_fst (parse_u16 `nondep_then` parse_u32) () parse_u16))
      (accessor_fst parse_u16 () parse_u32))
    clens_a
    ()


let clens_b : clens t U32.t = {
  clens_cond =  (fun _ -> True);
  clens_get = (fun x -> x.b);
}

let gaccess_b : gaccessor parse_t parse_u32 clens_b =
  gaccessor_ext
    ((gaccessor_synth (parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16) synth_t synth_t_recip ()
     `gaccessor_compose`
     gaccessor_fst (parse_u16 `nondep_then` parse_u32) () parse_u16)
     `gaccessor_compose`
     gaccessor_snd parse_u16 parse_u32)
    clens_b
    ()

inline_for_extraction
let access_b : accessor gaccess_b =
  accessor_ext
    (accessor_compose
      (accessor_compose
        (accessor_synth (parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16) synth_t synth_t_recip ())
        (accessor_fst (parse_u16 `nondep_then` parse_u32) () parse_u16))
      (accessor_snd jump_u16 parse_u32))
    clens_b
    ()

let clens_c : clens t U16.t = {
  clens_cond =  (fun _ -> True);
  clens_get = (fun x -> x.c);
}

let gaccess_c : gaccessor parse_t parse_u16 clens_c =
  gaccessor_ext
    (gaccessor_synth (parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16) synth_t synth_t_recip ()
     `gaccessor_compose`
     gaccessor_snd (parse_u16 `nondep_then` parse_u32) parse_u16)
    clens_c
    ()

inline_for_extraction
let access_c : accessor gaccess_c =
  accessor_ext
    (accessor_compose
      (accessor_synth (parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16) synth_t synth_t_recip ())
      (accessor_snd (jump_u16 `jump_nondep_then` jump_u32) parse_u16))
    clens_c
    ()

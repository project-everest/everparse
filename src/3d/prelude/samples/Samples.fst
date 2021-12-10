module Samples
open EverParse3d.Prelude
open EverParse3d.Actions
open EverParse3d.Interpreter
module T = FStar.Tactics
module A = EverParse3d.Actions.All
module P = EverParse3d.Prelude
#push-options "--query_stats"
[@@specialize]
let u8_dtyp = DT_IType UInt8

[@@specialize]
let u8_pair
  : typ _ _ _ _
  = T_pair (T_denoted u8_dtyp) (T_denoted u8_dtyp)

[@@T.postprocess_with specialize_tac]
let validate_u8_pair
  = as_val u8_pair

(* In emacs, C-c C-s C-p shows the definition of validate_u8_pair as:

Actions.validate_pair "" Actions.validate____UINT8 Actions.validate____UINT8
*)

[@@specialize]
let u8_pair_binding
  : global_binding
  = {
      name = "u8_pair";
      param_types = [];
      parser_kind_nz = _;
      parser_weak_kind = _;
      parser_kind = _;
      inv = coerce (_ by (T.trefl())) (A.conj_inv A.true_inv A.true_inv);
      loc = coerce (_ by (T.trefl())) (A.eloc_union A.eloc_none A.eloc_none);
      p_t = as_type u8_pair;
      p_p = as_parser u8_pair;
      p_reader = None;
      p_v = validate_u8_pair;
    }

[@@specialize]
let u8_pair_dtyp = DT_App "u8_pair" u8_pair_binding ()

module U8 = FStar.UInt8

let tt = (T_denoted u8_pair_dtyp)

[@@T.postprocess_with specialize_tac]
let validate_u8_pair_pair
  = as_val (T_pair (T_denoted u8_pair_dtyp)
                   (T_denoted u8_pair_dtyp))

[@@specialize]
let u8_pair_param (i:P.___UINT8)
  : typ _ _ _ _
  = T_pair (T_refine u8_dtyp (fun fst -> U8.(fst <^ i) ))
           (T_refine u8_dtyp (fun snd -> U8.(snd >=^ i)))

[@@T.postprocess_with specialize_tac]
let validate_u8_pair_param (i:P.___UINT8)
  = as_validator (u8_pair_param i)


//let u8_pair_global_binding_alt (i:P.___UINT8) =

[@@specialize]
let u8_pair_global_binding_alt_param
  : arrow [PT_Base UInt8] global_binding_alt
  = coerce (_ by (T.trefl()))
    (fun i ->  mk_global_binding_alt None (validate_u8_pair_param i) ( _ by (T.trefl())))

[@@specialize]
let kind_u8_pair = and_then_kind (filter_kind kind____UINT8) (filter_kind kind____UINT8)
let inv_u8_pair = A.conj_inv A.true_inv A.true_inv
let eloc_u8_pair = A.eloc_union A.eloc_none A.eloc_none
[@@specialize]
let u8_pair_param_dtyp_alt (i:P.___UINT8)
  : dtyp kind_u8_pair false inv_u8_pair eloc_u8_pair
  = coerce (_ by (T.trefl()))
           (DT_App_Alt [PT_Base UInt8] u8_pair_global_binding_alt_param (coerce (_ by (T.trefl())) (i, ())))


[@@specialize]
let param_types = [PT_Base UInt8]

let p_t
  : arrow param_types Type
  = coerce (_ by (T.trefl())) (fun i -> as_type (u8_pair_param i))

let p_k = P.and_then_kind
              (P.filter_kind (parser_kind_of_itype (UInt8)))
              (P.filter_kind (parser_kind_of_itype (UInt8)))

let p_p
 : dep_arrow param_types (fun args -> P.parser p_k (apply_arrow p_t args))
  = coerce (_ by (T.trefl())) (fun i -> as_parser (u8_pair_param i))
module U8 = FStar.UInt8

let p_inv
 : arrow param_types A.slice_inv
 = coerce (_ by (T.trefl())) (fun (i:U8.t) -> A.conj_inv A.true_inv A.true_inv)

let p_loc
 : arrow param_types A.eloc
 = coerce (_ by (T.trefl())) (fun (i:U8.t) -> A.eloc_union A.eloc_none A.eloc_none)

[@@specialize]
let p_v
  : dep_arrow param_types
    (fun args -> A.validate_with_action_t
                 (apply_dep_arrow _ _ p_p args)
                 (apply_arrow p_inv args)
                 (apply_arrow p_loc args)
                 false)
  = coerce (_ by (T.trefl())) validate_u8_pair_param


[@@specialize]
let u8_pair_param_binding
  : global_binding
  = mk_global_binding
       [PT_Base UInt8]
       p_inv
       p_loc
       None
       p_v
       ()


[@@specialize]
let u8_pair_param_dtyp x = DT_App "u8_pair_param" u8_pair_param_binding (x, ())

////////////////////////////////////////////////////////////////////////////////


let u8_line_kind
  : P.parser_kind true P.WeakKindStrongPrefix
  = P.and_then_kind kind_u8_pair kind_u8_pair

[@@specialize]
let u8_line (x:P.___UINT8)
  = T_pair (T_denoted (u8_pair_param_dtyp_alt x))
           (T_denoted (u8_pair_param_dtyp_alt x))

[@@T.postprocess_with specialize_tac]
let validate_u8_line (x:P.___UINT8)
  = as_validator (u8_line x)

let u8_rect_kind
  : P.parser_kind true P.WeakKindStrongPrefix
  = P.and_then_kind u8_line_kind u8_line_kind

[@@specialize]
let u8_rect
  : typ u8_rect_kind _ _ _
  = T_pair u8_line u8_line

[@@T.postprocess_with specialize_tac]
let validate_u8_rect
  = as_validator u8_rect

[@@specialize]
let u8_rect2_raw
  : typ _ _ _ _
  = T_pair
        (T_pair (T_pair (T_pair u8_rect u8_rect)
                        (T_pair u8_rect u8_rect))
                (T_pair (T_pair u8_rect u8_rect)
                        (T_pair u8_rect u8_rect)))
        (T_pair (T_pair (T_pair u8_rect u8_rect)
                        (T_pair u8_rect u8_rect))
                (T_pair (T_pair u8_rect u8_rect)
                        (T_pair u8_rect u8_rect)))

let kind_of #nz #wk #pk #s #l #b (t:typ #nz #wk pk s l b) : P.parser_kind (normalize_term nz) (normalize_term wk) = pk
let inv_of  #nz #wk #pk #s #l #b (t:typ #nz #wk pk s l b) : A.slice_inv = s
let eloc_of  #nz #wk #pk #s #l #b (t:typ #nz #wk pk s l b) : A.eloc = l
let u8_rect2_kind = kind_of (u8_rect2_raw)
let u8_rect2_inv = inv_of (u8_rect2_raw)
let u8_rect2_eloc = eloc_of (u8_rect2_raw)
[@@specialize]
let u8_rect2
  : typ u8_rect2_kind u8_rect2_inv u8_rect2_eloc _
  = u8_rect2_raw
#push-options "--debug Samples --debug_level EraseErasableArgs"

[@@T.postprocess_with specialize_tac]
let validate_u8_rect2
  = as_validator u8_rect2

(* But there are still huge implicit terms in there
   If you #push-options "--print_implicits"
   and try to print the term, emacs will hang *)

(**
// Generates:

//     Actions.validate_pair ""
//     (Actions.validate_pair ""
//         (Actions.validate_pair "" EverParse3d.Interpreter.validate_u8_pair EverParse3d.Interpreter.validate_u8_pair)
//         (Actions.validate_pair "" EverParse3d.Interpreter.validate_u8_pair EverParse3d.Interpreter.validate_u8_pair))
//     (Actions.validate_pair ""
//         (Actions.validate_pair ""
//             (Actions.validate_pair "" EverParse3d.Interpreter.validate_u8_pair EverParse3d.Interpreter.validate_u8_pair)
//             (Actions.validate_pair "" EverParse3d.Interpreter.validate_u8_pair EverParse3d.Interpreter.validate_u8_pair))
//         (Actions.validate_pair ""
//             (Actions.validate_pair ""
//                 (Actions.validate_pair "" EverParse3d.Interpreter.validate_u8_pair EverParse3d.Interpreter.validate_u8_pair)
//                 (Actions.validate_pair "" EverParse3d.Interpreter.validate_u8_pair EverParse3d.Interpreter.validate_u8_pair))
//             (Actions.validate_pair ""
//                 (Actions.validate_pair "" EverParse3d.Interpreter.validate_u8_pair EverParse3d.Interpreter.validate_u8_pair)
//                 (Actions.validate_pair "" EverParse3d.Interpreter.validate_u8_pair EverParse3d.Interpreter.validate_u8_pair)))
//     )

//  **)

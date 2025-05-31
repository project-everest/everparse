(*
   Copyright 2025 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain as copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module CoerceProbes
(*
  This module implements a pass over the source AST,
  elaborating CoerceProbeFunctionStubs into ProbeFunctions, 
  by coercing a 32-bit layout type into a 64-bit layout type 
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module H = Hashtable
module B = Binding
open GlobalEnv
open GeneralizeProbes

let params = list generic_param & list param
noeq
type env = {
  benv:B.env;
  params:params;
}
let probe_fail
: probe_action
= with_dummy_range <|
  Probe_atomic_action <|
  Probe_action_fail

let probe_return_unit 
: probe_action
= with_dummy_range <|
  Probe_atomic_action <|
  Probe_action_return (with_dummy_range (Constant Unit))

let read_and_coerce_pointer (e:env) (fid:expr)
: ML probe_action
= let reader = find_probe_fn e.benv (PQRead UInt32) fid.range in
  let writer = find_probe_fn e.benv (PQWrite UInt64) fid.range in
  let coercion = find_extern_coercion e.benv tuint32 tuint64 fid.range in
  let as_ident x = with_dummy_range <| to_ident' x in
  let as_expr x = with_dummy_range <| Identifier <| as_ident x in
  with_dummy_range <|
  Probe_action_let fid
    (as_ident "ptr32")
    (Probe_action_read reader)
    (with_dummy_range <|
      Probe_action_let fid
          (as_ident "ptr64")
          (Probe_action_call coercion [as_expr "ptr32"])
          (with_dummy_range <| Probe_atomic_action (Probe_action_write writer (as_expr "ptr64"))))


let skip_bytes_read (n:expr)
: ML probe_action
= with_dummy_range <| Probe_atomic_action (Probe_action_skip_read n)

let skip_bytes_write (n:expr)
: ML probe_action
= with_dummy_range <| Probe_atomic_action (Probe_action_skip_write n)

let copy_bytes (e:env) (n:expr)
: ML probe_action
= let probe_and_copy_n = find_probe_fn e.benv PQWithOffsets n.range in
  with_dummy_range <|
  Probe_atomic_action 
        (Probe_action_call probe_and_copy_n [n])

let cstring (s:string) = with_dummy_range <| Constant (String s)
let continue (fn:string) (a:probe_action) (k:probe_action)
: ML probe_action
= with_dummy_range <|
  Probe_action_seq (cstring fn) a k

let read_and_coerce_id = with_dummy_range <| to_ident' "read_and_coerce_pointer"
let copy_bytes_id = with_dummy_range <| to_ident' "copy_bytes"
let skip_bytes_read_id = with_dummy_range <| to_ident' "skip_bytes_read"
let skip_bytes_write_id = with_dummy_range <| to_ident' "skip_bytes_write"
let mk_expr x = with_dummy_range <| Identifier (mk_ident x)
let mk_probe_helpers (e:env)
: ML (list decl)
= let read_and_coerce =
    ProbeFunction
      read_and_coerce_id
      [tstring, mk_ident "fieldname", Immutable]
      (read_and_coerce_pointer e (mk_expr "fieldname"))
      HelperProbeFunction
  in
  let skip_read =
    ProbeFunction
      skip_bytes_read_id
      [tuint64, mk_ident "numbytes", Immutable]
      (skip_bytes_read (mk_expr "numbytes"))
      HelperProbeFunction
  in
  let skip_write =
    ProbeFunction
      skip_bytes_write_id
      [tuint64, mk_ident "numbytes", Immutable]
      (skip_bytes_write (mk_expr "numbytes"))
      HelperProbeFunction
  in
  let copy_bytes =
    ProbeFunction
      copy_bytes_id
      [tuint64, mk_ident "numbytes", Immutable]
      (copy_bytes e (mk_expr "numbytes"))
      HelperProbeFunction
  in
  [mk_decl read_and_coerce dummy_range [] false;
   mk_decl skip_read dummy_range [] false;
   mk_decl skip_write dummy_range [] false;
   mk_decl copy_bytes dummy_range [] false]

let cuint64 (n:int) = with_dummy_range <| Constant <| Int UInt64 n

let iskip_bytes_read (n:int) =
  let hd =
      with_dummy_range <| 
        App (ProbeFunctionName skip_bytes_read_id)
            [cuint64 n]
  in
  with_dummy_range <| Probe_action_var hd

let iskip_bytes_write (n:int) =
  let hd =
      with_dummy_range <| 
        App (ProbeFunctionName skip_bytes_write_id)
            [cuint64 n]
  in
  with_dummy_range <| Probe_action_var hd

let icopy_bytes (n:int) =
  let hd =
      with_dummy_range <| 
        App (ProbeFunctionName copy_bytes_id)
            [cuint64 n]
  in
  with_dummy_range <| Probe_action_var hd

let probe_and_copy_alignment 
    (e:env)
    (n0 n1:int)
    (k:probe_action)
: ML probe_action
= if n0=n1
  then continue "alignment" (icopy_bytes n0) k
  else continue "alignment" (iskip_bytes_read n0)
          (continue "alignment" (iskip_bytes_write n1) k)

let read_and_coerce_pointer_k (e:env) (fid:ident) (k:probe_action)
: ML probe_action
= 
  let read_and_coerce = 
    let hd =
      with_dummy_range <| 
        App (ProbeFunctionName read_and_coerce_id) 
            [cstring <| print_ident fid]
    in
    with_dummy_range <| Probe_action_var hd
  in
  continue (print_ident fid) read_and_coerce k
  // continue 
  //   (print_ident fid)
  //   (read_and_coerce_pointer e (cstring <| print_ident fid)) k

let integer_type_of_type t
: option integer_type
= if eq_typ t tuint8 then Some UInt8
  else if eq_typ t tuint16 then Some UInt16
  else if eq_typ t tuint32 then Some UInt32
  else if eq_typ t tuint64 then Some UInt64
  else None 

let rec head_type (e:env) (t:typ) : ML ident =
  match (Binding.unfold_typ_abbrev_only e.benv t).v with
  | Type_app hd _ _ _ -> hd
  | Pointer t _ -> head_type e t
  | _ -> error "Cannot find head type of an arrow" t.range

let is_pointer_or_integer (e:env) (t:typ) : ML (option integer_type) =
  match (Binding.unfold_typ_abbrev_only e.benv t).v with
  | Pointer _ (PQ sz _ _) -> Some sz
  | _ -> integer_type_of_type t

let find_probe_fn_for_type (e:env) (id:ident) (r:range)
: ML (option ident)
= match GlobalEnv.find_probe_fn (B.global_env_of_env e.benv) r (SimpleProbeFunction id) with
  | None ->
    GlobalEnv.find_probe_fn (B.global_env_of_env e.benv) r (CoerceProbeFunction(id,id))
  | p -> p
let probe_and_copy_type (e:env) (fn:ident) (t0:typ) (k:probe_action)
: ML probe_action
= let probe_and_copy_n = find_probe_fn e.benv PQWithOffsets fn.range in
  let t = B.unfold_typ_abbrev_and_enum e.benv t0 in
  match is_pointer_or_integer e t with
  | None -> (
      if eq_typ t tunit then k else
      let id = head_type e t in
      match find_probe_fn_for_type e id t.range with
      | None ->
        error 
          (Printf.sprintf "Cannot find probe function for type %s" (print_typ t))
          t.range
      | Some id -> (
        let insts, _ = GeneralizeProbes.generic_instantiations_for_type e.benv t in
        Options.debug_print_string <|
          Printf.sprintf "****Instantiating probe function for type %s unfolded to %s with %s\n" 
            (print_typ t0)
            (print_typ t)
            (String.concat ", " (List.map print_expr insts));
        let hd =
          match insts with
          | [] ->
            with_dummy_range <| Identifier id
          | _ ->
            with_dummy_range <| App (ProbeFunctionName id) insts
        in
        let hd = with_dummy_range <| Probe_action_var hd in
        with_dummy_range <|
        Probe_action_seq (cstring <| print_ident fn) hd k
      )
  )
  | Some i -> 
    let size =
      match i with
      | UInt8 -> 1
      | UInt16 -> 2
      | UInt32 -> 4
      | UInt64 -> 8
    in
    with_dummy_range <|
    Probe_action_seq
      (cstring <| print_ident fn)
      (icopy_bytes size)
      k
  

let alignment_bytes (af:atomic_field)
: ML int
= match af.v.field_array_opt with
  | FieldArrayQualified ({v=Constant (Int _ n)}, ByteArrayByteSize) -> n                  
  | _ -> failwith "Not an alignment field"

let check_scope (env:env) (e:expr)
: ML unit
= let fvs = free_vars_of_expr e in
  List.iter (fun i -> 
    if not (List.existsb (fun (_, j, _) -> eq_idents i j) (snd env.params))
    then (
      error 
        (Printf.sprintf
          "Cannot coerce a type with a data-dependent length; \
           the length of this type may depend on the field `%s`"
           (print_ident i))
        i.range
    ))
  fvs

let check_scope_type (env:env) (field_name:ident) (t:typ)
: ML unit
= let fvs = free_vars_of_typ t in
  List.iter (fun i -> 
    if not (List.existsb (fun (_, j, _) -> eq_idents i j) (snd env.params))
    then (
      error 
        (Printf.sprintf
          "Cannot coerce a type with data-dependency; \
           field %s of type %s may depend on the field `%s`"
          (print_ident field_name)
          (print_typ t)
          (print_ident i))
        i.range
    ))
  fvs

let rec coerce_fields (e:env) (r0 r1:record)
: ML probe_action
= match r0, r1 with
  | hd0::tl0, hd1::tl1 -> (
    match hd0.v, hd1.v with
    | RecordField r0 i0, RecordField r1 i1 -> (
      if not (eq_idents i0 i1)
      then failwith <|
            Printf.sprintf
              "Unexpected fields: cannot coerce field %s to %s"
              (print_ident i0)
              (print_ident i1);
      with_dummy_range <|
      Probe_action_seq (cstring <| print_ident i0)
        (coerce_fields e r0 r1)
        (coerce_fields e tl0 tl1)
     )
    | SwitchCaseField sw0 i0, SwitchCaseField sw1 i1 -> (
      if not (eq_idents i0 i1)
      then (
        error
            (Printf.sprintf
              "Unexpected fields: cannot coerce field %s to %s"
              (print_ident i0)
              (print_ident i1))
            i0.range
      );
      with_dummy_range <|
      Probe_action_seq (cstring <| print_ident i0)
        (coerce_switch_case e sw0 sw1)
        (coerce_fields e tl0 tl1)
    )
    | AtomicField af0, AtomicField af1 -> (
      match TypeSizes.is_alignment_field af0.v.field_ident,
            TypeSizes.is_alignment_field af1.v.field_ident
      with
      | true, true ->
        let n0 = alignment_bytes af0 in
        let n1 = alignment_bytes af1 in
        probe_and_copy_alignment e n0 n1 (coerce_fields e tl0 tl1)
      | true, false ->
        let n0 = alignment_bytes af0 in
        continue "alignment" (iskip_bytes_read n0) (coerce_fields e tl0 r1)
      | false, true ->
        let n1 = alignment_bytes af1 in
        continue "alignment" (iskip_bytes_write n1) (coerce_fields e r0 tl1)
      | false, false -> (
        let coerce_scalar_part ()
        : ML probe_action
        = let t0_is_u32 =
            match af0.v.field_type.v with
            | Pointer _ pq -> pq_as_integer_type pq = UInt32
            | _ -> eq_typ af0.v.field_type tuint32
          in
          let t1_is_ptr64 =
            match af1.v.field_type.v with
            | Pointer _ pq -> pq_as_integer_type pq = UInt64
            | _ -> false
          in
          if t0_is_u32 && t1_is_ptr64
          then read_and_coerce_pointer_k e af0.v.field_ident (coerce_fields e tl0 tl1)
          else if eq_typ af0.v.field_type af1.v.field_type
          then (
            let _ = check_scope_type e af0.v.field_ident af0.v.field_type in
            probe_and_copy_type e af0.v.field_ident af0.v.field_type (coerce_fields e tl0 tl1)
          )
          else (
            match Generate32BitTypes.has_32bit_coercion e.benv af0.v.field_type af1.v.field_type with
            | Some id -> (
              let insts, _ = GeneralizeProbes.generic_instantiations_for_type e.benv af0.v.field_type in
              Options.debug_print_string <|
                Printf.sprintf "****Instantiating probe function for type %s with %s\n" 
                  (print_typ af0.v.field_type)
                  (String.concat ", " (List.map print_expr insts));
              let hd =
                match insts with
                | [] ->
                  with_dummy_range <| Identifier id
                | _ ->
                  with_dummy_range <| App (ProbeFunctionName id) insts
              in
              with_dummy_range <|
              Probe_action_seq (cstring <| print_ident af0.v.field_ident)
                (with_dummy_range <| Probe_action_var hd)
                (coerce_fields e tl0 tl1)
            )
            | None ->
              error 
                (Printf.sprintf
                  "Unexpected fields: cannot coerce field %s of type %s to %s"
                  (print_ident af0.v.field_ident)
                  (print_typ af0.v.field_type)
                  (print_typ af1.v.field_type))
              af0.v.field_ident.range
          )
        in
        if not (eq_idents af0.v.field_ident af1.v.field_ident)
        then (
          error 
            (Printf.sprintf
                "Unexpected fields: cannot coerce field %s to %s"
                (print_ident af0.v.field_ident)
                (print_ident af1.v.field_ident))
            af0.v.field_ident.range
        )
        else if Some? af0.v.field_bitwidth ||
                Some? af1.v.field_bitwidth
        then (
          error 
            (Printf.sprintf
                "Unexpected fields: cannot coerce bit fields %s to %s"
                (print_ident af0.v.field_ident)
                (print_ident af1.v.field_ident))
            af0.v.field_ident.range
        )
        else (
          match af0.v.field_array_opt, af1.v.field_array_opt with
          | FieldScalar, FieldScalar -> coerce_scalar_part ()
          | FieldArrayQualified (n0, aq0), FieldArrayQualified (n1, aq1) -> (
            let _ =
              match aq0, aq1 with
              | ByteArrayByteSize, ByteArrayByteSize
              | ArrayByteSize, ArrayByteSize -> ()
              | _ ->
                error
                  (Printf.sprintf
                    "Unexpected fields: Unsupported array type, cannot coerce field %s to %s"
                    (print_ident af0.v.field_ident)
                    (print_ident af1.v.field_ident))
                  af0.v.field_ident.range
            in
            let coerce_elt = coerce_scalar_part () in
            let _ = check_scope e n0 in
            with_dummy_range <| Probe_action_array n0 coerce_elt
          )
          | _ ->
            error 
              (Printf.sprintf
                "Unexpected fields: cannot coerce field %s of type %s to %s"
                (print_ident af0.v.field_ident)
                (print_typ af0.v.field_type)
                (print_typ af1.v.field_type))
              af0.v.field_ident.range
        )
      )
    ) 
    | _ -> 
      failwith "Cannot yet coerce structs with non-structurally similar fields"
  )
  | [], [] ->
    probe_return_unit
  | hd::tl, [] -> (
    match hd.v with
    | AtomicField af -> (
      if TypeSizes.is_alignment_field af.v.field_ident
      then (
        let n = alignment_bytes af in
        continue "alignment" (iskip_bytes_read n) (coerce_fields e tl [])
      )
      else error ("Unexpected fields: extra non-alignment field in LHS type") af.v.field_ident.range
    )
    | _ -> 
      error ("Unexpected fields: extra non-alignment field in LHS type") hd.range
  )

  | [], hd::tl-> (
    match hd.v with
    | AtomicField af -> (
      if TypeSizes.is_alignment_field af.v.field_ident
      then (
        let n = alignment_bytes af in
        continue "alignment" (iskip_bytes_write n) (coerce_fields e [] tl)
      ) 
      else error ("Unexpected fields: extra non-alignment field in RHS type") af.v.field_ident.range
    )
    | _ -> 
      error ("Unexpected fields: extra non-alignment field in RHS type") hd.range
  )


and coerce_switch_case (e:env) (sw0 sw1:switch_case)
: ML probe_action
= let scrutinee0, cases0 = sw0 in
  let scrutinee1, cases1 = sw1 in
  if not (eq_expr scrutinee0 scrutinee1)
  then failwith "Cannot coerce switch cases with different scrutinees";
  if List.length cases0 <> List.length cases1
  then failwith "Cannot coerce switch cases with different number of cases";
  let cases = List.zip cases0 cases1 in
  List.fold_right
    (fun (c0, c1) k ->
      Options.debug_print_string <|
        Printf.sprintf "Coercing switch case %s to %s\n" (print_case c0) (print_case c1);
      match c0, c1 with
      | Case e0 f0, Case e1 f1 -> (
        if not (eq_expr e0 e1)
        then failwith "Cannot coerce switch cases with different case expressions";
        with_dummy_range <|
        Probe_action_ite 
          (with_range (App Eq [scrutinee0; e0]) e0.range)
          (coerce_fields e [f0] [f1])
          k
      )
      | DefaultCase f0, DefaultCase f1 -> (
        coerce_fields e [f0] [f1]
      )
      | _ -> failwith "Cannot coerce switch cases with different case types"
    )
    cases
    probe_fail

let rec optimize_coercion (p:probe_action)
: ML probe_action
= let is_copy p = 
    match p.v with
    | Probe_action_var {v=App (ProbeFunctionName id) [{v=Constant (Int UInt64 n)}]} ->
      if eq_idents id copy_bytes_id
      then Some n
      else None
    | Probe_atomic_action (Probe_action_copy g {v=Constant (Int UInt64 n)}) ->
      Some n
    | _ -> None
  in
  match p.v with
  | Probe_action_seq d hd k -> (
    let k = optimize_coercion k in
    let def () = { p with v = Probe_action_seq d hd k } in
    match is_copy hd with
    | None -> def ()
    | Some len -> (
      match k.v with
      | Probe_action_seq d' hd' k -> (
        match is_copy hd' with
        | None -> def ()
        | Some len' -> 
          { p with v = Probe_action_seq d (icopy_bytes (len + len')) k }
      )
      | _ -> (
        match is_copy k with
        | None -> def ()
        | Some len' -> icopy_bytes (len + len')
      )
    )
    | _ -> def ()
  )
  | Probe_action_let d i a k ->
    { p with v = Probe_action_let d i a (optimize_coercion k) }
  | Probe_action_ite e t f ->
    { p with v = Probe_action_ite e (optimize_coercion t) (optimize_coercion f) }
  | Probe_action_array l body ->
    let body = optimize_coercion body in
    { p with v = Probe_action_array l body }
  | _ -> p
  
let replace_stub (e:B.env) (d:decl { CoerceProbeFunctionStub? d.d_decl.v })
: ML decl
= match d.d_decl.v with
  | CoerceProbeFunctionStub i params (CoerceProbeFunction (t0, t1)) ->
    Options.debug_print_string <|
    Printf.sprintf "Replacing stub %s (from %s to %s)\n"
      i.v.name (print_ident t0) (print_ident t1);
    let d0, _ = B.lookup_type_decl e t0 in
    let d1, _ = B.lookup_type_decl e t1 in
    let e = { benv=e; params=B.params_of_decl d } in
    let coercion =
      match d0.d_decl.v, d1.d_decl.v with
      | Record _ _ _ _ r0, Record _ _ _ _ r1 ->
        Options.debug_print_string <|
          Printf.sprintf "Coercing record %s to %s\nfields lhs: %s\nfields rhs: %s" 
            (print_ident t0) (print_ident t1)
            (print_record r0) (print_record r1);
        coerce_fields e r0 r1
      | CaseType _ _ params0 r0, CaseType _ _ params1 r1 ->
        if List.length params0 <> List.length params1
        then failwith "Cannot coerce case types with different number of parameters";
        coerce_switch_case e r0 r1
      | _ ->
        error
          (Printf.sprintf "Type %s is not coercible to %s" (print_ident t0) (print_ident t1))
          d.d_decl.range
    in
    let probe_action = optimize_coercion coercion in
    let probe_fn = { 
        d.d_decl with
        v = ProbeFunction i params probe_action (CoerceProbeFunction(t0, t1)) 
      }
    in
    { d with d_decl = probe_fn }
  | _ -> d


let replace_stubs (e:global_env) (ds:list decl)
: ML (list decl)
= let e = B.mk_env e in
  let probe_helpers =
    if List.existsb (fun d -> CoerceProbeFunctionStub? d.d_decl.v) ds
    then mk_probe_helpers {benv=e;params=([],[])}
    else []
  in
  let decls_rev, _ = 
    List.fold_left
      (fun (acc, added_helpers) (d:decl) ->
        match d.d_decl.v with
        | CoerceProbeFunctionStub _ _ _ ->
          let d = replace_stub e d in
          if added_helpers
          then d::acc, added_helpers
          else d::probe_helpers @ acc, true
        | _ -> d::acc, added_helpers)
      ([], false)
      ds
  in
  List.rev decls_rev 
    
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

let print_probe_qualifier = function
  | PQWithOffsets -> "WithOffsets"
  | PQRead i -> Printf.sprintf "Read %s" (print_integer_type i)
  | PQWrite i -> Printf.sprintf "Write %s" (print_integer_type i)
  | PQInit -> "Init"


let find_probe_fn (e:B.env) (q:probe_qualifier)
: ML ident
= match GlobalEnv.extern_probe_fn_qual (B.global_env_of_env e) (Some q) with
  | None ->
    error (Printf.sprintf "Cannot find probe function for %s" (print_probe_qualifier q))
          dummy_range
  | Some id ->
    id
  
let find_extern_coercion (e:B.env) (t0:typ) (t1:typ)
: ML ident
= match GlobalEnv.resolve_extern_coercion (B.global_env_of_env e) t0 t1 with
  | None ->
    error (Printf.sprintf "Cannot find coercion for %s to %s" (print_typ t0) (print_typ t1))
          dummy_range
  | Some id ->
    id

let read_and_coerce_pointer (e:B.env) (fid:ident) (k:probe_action)
: ML probe_action
= let reader = find_probe_fn e (PQRead UInt32) in
  let writer = find_probe_fn e (PQWrite UInt64) in
  let coercion = find_extern_coercion e tuint32 tuint64 in
  let fid64 = {fid with v = { fid.v with name = fid.v.name ^ "_64" } } in
  let fid_expr = with_dummy_range <| Identifier fid in
  let fid64_expr = with_dummy_range <| Identifier fid64 in
  with_dummy_range <|
  Probe_action_let 
    fid
    (Probe_action_read reader)
    (with_dummy_range <|
      Probe_action_let fid64
        (Probe_action_call coercion [fid_expr])
        (with_dummy_range <| 
          Probe_action_seq (with_dummy_range <| Probe_atomic_action (Probe_action_write writer fid64_expr)) k))

let integer_type_of_type t
: option integer_type
= if eq_typ t tuint8 then Some UInt8
  else if eq_typ t tuint16 then Some UInt16
  else if eq_typ t tuint32 then Some UInt32
  else if eq_typ t tuint64 then Some UInt64
  else None 

let rec head_type (e:B.env) (t:typ) : ML ident =
  match (Binding.unfold_typ_abbrev_only e t).v with
  | Type_app hd _ _ _ -> hd
  | Pointer t _ -> head_type e t
  | _ -> error "Cannot find head type of an arrow" t.range

let probe_and_copy_type (e:B.env) (t0:typ) (k:probe_action)
: ML probe_action
= let probe_and_copy_n = find_probe_fn e PQWithOffsets in
  let t = B.unfold_typ_abbrev_and_enum e t0 in
  match integer_type_of_type t with
  | None -> (
      if eq_typ t tunit then k else
      let id = head_type e t in
      match GlobalEnv.find_probe_fn (B.global_env_of_env e) (SimpleProbeFunction id) with
      | None ->
        error 
          (Printf.sprintf "Cannot find probe function for type %s" (print_typ t))
          t.range
      | Some id -> (
        let insts, _ = GeneralizeProbes.generic_instantiations_for_type e t in
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
        Probe_action_seq hd k
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
      (with_dummy_range <| Probe_atomic_action (Probe_action_copy probe_and_copy_n (with_dummy_range <| Constant (Int UInt64 size))))
      k
  
let skip_bytes_read (n:int) (k:probe_action)
: ML probe_action
= with_dummy_range <|
    Probe_action_seq 
      (with_dummy_range <| Probe_atomic_action (Probe_action_skip_read (with_dummy_range <| Constant (Int UInt64 n))))
      k

let skip_bytes_write (n:int) (k:probe_action)
: ML probe_action
= with_dummy_range <|
    Probe_action_seq 
      (with_dummy_range <| Probe_atomic_action (Probe_action_skip_write (with_dummy_range <| Constant (Int UInt64 n))))
      k

let probe_and_copy_alignment 
    (e:B.env)
    (n0 n1:int)
    (k:probe_action)
: ML probe_action
= if n0=n1
  then (
    let probe_and_copy_n = find_probe_fn e PQWithOffsets in
    with_dummy_range <|
      Probe_action_seq
        (with_dummy_range <| Probe_atomic_action 
          (Probe_action_call probe_and_copy_n [with_dummy_range <| Constant (Int UInt64 n0)]))
        k
  )
  else (
    skip_bytes_read n0 (skip_bytes_write n1 k)
  )

let alignment_bytes (af:atomic_field)
: ML int
= match af.v.field_array_opt with
  | FieldArrayQualified ({v=Constant (Int _ n)}, ByteArrayByteSize) -> n
  | _ -> failwith "Not an alignment field"

let rec coerce_fields (e:B.env) (r0 r1:record)
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
      Probe_action_seq
        (coerce_fields e r0 r1)
        (coerce_fields e tl0 tl1)
     )
    | SwitchCaseField sw0 i0, SwitchCaseField sw1 i1 -> (
      if not (eq_idents i0 i1)
      then failwith <|
            Printf.sprintf
              "Unexpected fields: cannot coerce field %s to %s"
              (print_ident i0)
              (print_ident i1);
      with_dummy_range <|
      Probe_action_seq
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
        skip_bytes_read n0 (coerce_fields e tl0 r1)
      | false, true ->
        let n1 = alignment_bytes af1 in
        skip_bytes_write n1 (coerce_fields e r0 tl1)
      | false, false -> (
        if not (eq_idents af0.v.field_ident af1.v.field_ident)
        then failwith <|
              Printf.sprintf
                "Unexpected fields: cannot coerce field %s to %s"
                (print_ident af0.v.field_ident)
                (print_ident af1.v.field_ident)
        else (
          let t0_is_u32 =
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
          then read_and_coerce_pointer e af0.v.field_ident (coerce_fields e tl0 tl1)
          else if eq_typ af0.v.field_type af1.v.field_type
          then probe_and_copy_type e af0.v.field_type (coerce_fields e tl0 tl1)
          else (
            match Generate32BitTypes.has_32bit_coercion e af0.v.field_type af1.v.field_type with
            | Some id -> (
              let insts, _ = GeneralizeProbes.generic_instantiations_for_type e af0.v.field_type in
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
              Probe_action_seq 
                (with_dummy_range <| Probe_action_var hd)
                (coerce_fields e tl0 tl1)
            )
            | None ->
              failwith <|
                Printf.sprintf
                  "Unexpected fields: cannot coerce field %s of type %s to %s"
                  (print_ident af0.v.field_ident)
                  (print_typ af0.v.field_type)
                  (print_typ af1.v.field_type)
          )
        )
      )
    )
    | _ -> 
      failwith "Cannot yet coerce structs with non-structurally similar fields"
  )
  | [], [] ->
    probe_return_unit
  | _ -> failwith "Unexpected number of fields"

and coerce_switch_case (e:B.env) (sw0 sw1:switch_case)
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
= match p.v with
  | Probe_action_seq {v=Probe_atomic_action (Probe_action_copy f len)} k -> (
    let k = optimize_coercion k in
    let def () = { p with v = Probe_action_seq (with_dummy_range <| Probe_atomic_action (Probe_action_copy f len)) k } in
    match len.v with
    | Constant (Int UInt64 l0) -> (
      match k.v with
      | Probe_action_seq {v=Probe_atomic_action (Probe_action_copy g {v=Constant (Int UInt64 l1)})} k -> 
        if eq_idents f g || true
        then (

          { k with v = 
            Probe_action_seq 
              (with_dummy_range <| Probe_atomic_action (Probe_action_copy g {len with v=Constant (Int UInt64 (l0 + l1))}))
              k }
        )
        else def ()

      | Probe_atomic_action (Probe_action_copy g {v=Constant (Int UInt64 l1)}) -> 
        if eq_idents f g || true
        then { k with v=Probe_atomic_action (Probe_action_copy g {len with v=Constant (Int UInt64 (l0 + l1))}) }
        else def ()
      
      | _ -> def ()
    )
    | _ -> def ()
  )
  | Probe_action_seq a k ->
    { p with v = Probe_action_seq a (optimize_coercion k) }
  | Probe_action_let i a k ->
    { p with v = Probe_action_let i a (optimize_coercion k) }
  | Probe_action_ite e t f ->
    { p with v = Probe_action_ite e (optimize_coercion t) (optimize_coercion f) }
  | _ -> p
  

let replace_stub (e:B.env) (d:decl { CoerceProbeFunctionStub? d.d_decl.v })
: ML decl
= let CoerceProbeFunctionStub i params (CoerceProbeFunction (t0, t1)) = d.d_decl.v in
  Options.debug_print_string <|
    Printf.sprintf "Replacing stub %s (from %s to %s)\n" i.v.name (print_ident t0) (print_ident t1);
  let d0, _ = B.lookup_type_decl e t0 in
  let d1, _ = B.lookup_type_decl e t1 in
  let coercion =
    match d0.d_decl.v, d1.d_decl.v with
    | Record _ _ _ _ r0, Record _ _ _ _ r1 ->
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

let replace_stubs (e:global_env) (ds:list decl)
: ML (list decl)
= let e = B.mk_env e in
  List.map 
    (fun (d:decl) ->
      if CoerceProbeFunctionStub? d.d_decl.v
      then replace_stub e d
      else d)
    ds
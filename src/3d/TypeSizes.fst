(*
   Copyright 2019 Microsoft Research

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
module TypeSizes
open FStar.All
open Ast
open FStar.Mul
module H = Hashtable
module B = Binding

let product_size (base:size) (n:int) =
  match base with
  | Variable
  | WithVariableSuffix _ ->
    Variable
  | Fixed k ->
    Fixed (k * n)

let typename = ident'

type size_env = H.t typename (size & alignment)

//TODO: size of pointer is platform-dependent
let pointer_alignment : alignment = Some 8

let initial_senv () =
  let i = [
       ("unit",     (Fixed 0,  None));
       ("Bool",     (Fixed 1,  Some 1));
       ("UINT8",    (Fixed 1,  Some 1));
       ("UINT16",   (Fixed 2,  Some 2));
       ("UINT32",   (Fixed 4,  Some 4));
       ("UINT64",   (Fixed 8,  Some 8));
       ("UINT8BE",   (Fixed 1,  Some 1));
       ("UINT16BE",   (Fixed 2,  Some 2));
       ("UINT32BE",   (Fixed 4,  Some 4));
       ("UINT64BE",   (Fixed 8,  Some 8));
       ("field_id", (Fixed 4,  Some 4));
       ("all_bytes", (Variable, None));
       ("all_zeros", (Variable, None));
       ("PUINT8",   (Variable, pointer_alignment))
  ]
  in
  let senv = H.create 17 in
  List.iter (fun (i, k) -> H.insert senv (to_ident' i) k) i;
  senv

let size_and_alignment_of_typename (env:env_t) (i:ident)
  : ML (size & alignment)
  = match H.try_find (snd env) i.v with
    | Some s -> s
    | None ->
      failwith (Printf.sprintf "size_of_typename: Identifier %s not found" (ident_to_string i))

let size_of_typename (env:env_t) (i:ident)
  : ML size
  = fst (size_and_alignment_of_typename env i)

let print_size =
  function
  | Fixed n -> Printf.sprintf "(Fixed %d)" n
  | WithVariableSuffix n -> Printf.sprintf "(WithVariableSuffix %d)" n
  | Variable -> "Variable"

let extend_with_size_of_ident (env:env_t) (i:ident) (n:size) (a:alignment)
  : ML unit
  = Options.debug_print_string
     (Printf.sprintf "***** Size of %s = %s\n"
                     (ident_to_string i) (print_size n));
    H.insert (snd env) i.v (n, a)

let extend_with_size_of_typedef_names (env:env_t) (names:typedef_names) (size:size) (a:alignment)
  : ML unit
  = extend_with_size_of_ident env names.typedef_name size a;
    extend_with_size_of_ident env names.typedef_abbrev size a;
    (match names.typedef_ptr_abbrev with
     | None -> ()
     | Some nm -> extend_with_size_of_ident env nm Variable a)

let size_and_alignment_of_typ (env:env_t) (t:typ)
  : ML (size & alignment)
  = match t.v with
    | Type_app i _ _ _ -> size_and_alignment_of_typename env i
    | Pointer _ (PQ UInt64 _ _) -> Fixed 8, Some 8 //pointers are 64 bit and aligned
    | Pointer _ (PQ UInt32 _ _) -> Fixed 4, Some 4 //u32 pointers are 32 bit and aligned
    | Pointer _ _ -> failwith "Pointer sizes should already have been resolved to UInt32 or UInt64"
    | Type_arrow _ _ -> Variable, None 

let size_of_typ (env:env_t) (t:typ)
  : ML size
  = fst (size_and_alignment_of_typ env t)

let rec value_of_const_expr (env:env_t) (e:expr)
  : ML (option (either bool (integer_type & int)))
  =
  match e.v with
  | Constant (Int t n) -> Some (Inr (t, n))
  | Constant (Bool b) -> Some (Inl b)
  | App op [e1; e2] ->
    let v1 = value_of_const_expr env e1 in
    let v2 = value_of_const_expr env e2 in
    begin
    match op, v1, v2 with
    | Plus _,  Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 + n2))
    | Minus _, Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 - n2))
    | Mul _,   Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 * n2))
    | Division _, Some (Inr (t1, n1)), Some (Inr (t2, n2)) ->
      if n2 = 0
      then error ("Division by zero in constant expression") e2.range
      else Some (Inr (integer_type_lub t1 t2, n1 / n2))
    | GT _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 > n2))
    | LT _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 < n2))
    | GE _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 >= n2))
    | LE _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 <= n2))
    | And, Some (Inl b1), Some (Inl b2) -> Some (Inl (b1 && b2))
    | Or, Some (Inl b1), Some (Inl b2) -> Some (Inl (b1 || b2))
    | _ -> None
    end
  | App Not [e] ->
    let v = value_of_const_expr env e in
    begin
    match v with
    | Some (Inl b) -> Some (Inl (not b))
    | _ -> None
    end
  | App SizeOf [{v=Identifier t}] ->
    begin
    try
      match size_of_typ env (with_range (Type_app t KindSpec [] []) t.range) with
      | Fixed n
      | WithVariableSuffix n -> Some (Inr (UInt32, n))
      | _ -> None
    with
      | _ -> None
    end
  | App (Cast _ t) [e] ->
    let v = value_of_const_expr env e in
    begin
    match v with
    | Some (Inr (_, n)) ->
      Some (Inr (t, n))
    | _ -> None
    end
  | Identifier i ->
    begin
    match B.lookup_macro_definition (fst env) i with
    | Some e ->
      value_of_const_expr env e
    | _ -> None
    end
  | _ -> None

let size_and_alignment_of_atomic_field (env:env_t) (f:atomic_field)
  : ML (size & alignment)
  = let base_size, align = size_and_alignment_of_typ env f.v.field_type in
    let size =
      match f.v.field_array_opt with
      | FieldScalar ->
        base_size

      | FieldArrayQualified (n, ByteArrayByteSize) ->
        if base_size <> Fixed 1
        then error "Expected a byte array; if the underlying array elements are larger than a byte, use the '[:byte-size' notation"
                     f.range;
        let n = value_of_const_expr env n in
        begin
        match n with
        | Some (Inr (_, k)) ->
          Fixed k
        | _ ->
          Variable
        end

      | FieldString (Some n)
      | FieldArrayQualified (n, ArrayByteSize)
      | FieldArrayQualified (n, ArrayByteSizeSingleElementArray) ->
        let n = value_of_const_expr env n in
        begin
        match n with
        | Some (Inr (_, k)) -> Fixed k

        | _ ->
          Variable
        end

      | _ -> Variable
    in
    size, align

#push-options "--warn_error -272"
let alignment_prefix = Printf.sprintf "%salignment_padding" Ast.reserved_prefix
let gen_alignment_ident
  : unit -> ML ident
  = let ctr : ref int = alloc 0 in
    fun () ->
      let next = !ctr in
      ctr := next + 1;
      with_range
        (to_ident' (Printf.sprintf "%s_%d" alignment_prefix next))
        dummy_range
#pop-options

let padding_field (env:env_t) (diag_enclosing_type_name:ident (* for diagnostics only *)) (padding_msg:string) (n:int)
  : ML (list field)
  =
  if n <= 0
  then []
  else (
    let field_name = gen_alignment_ident() in
    let n_expr = with_range (Constant (Int UInt32 n)) dummy_range in
    let nm = ident_to_string diag_enclosing_type_name in
    FStar.IO.print_string
      (Printf.sprintf "Adding padding field in %s for %d bytes at %s\n"
                       nm
                       n
                       padding_msg);
    let sf = {
      field_dependence = false;
      field_ident = field_name;
      field_type = tuint8;
      field_array_opt=(if n = 1 then FieldScalar else FieldArrayQualified(n_expr, ByteArrayByteSize));
      field_constraint=None;
      field_bitwidth=None;
      field_action=None;
      field_probe=None
    } in
    let af = with_dummy_range sf in
    let f = with_dummy_range (AtomicField af) in
    [f]
  )

let should_align (td:typedef_names)
  : bool
  = List.Tot.Base.existsb Aligned? td.typedef_attributes

let alignment_padding env (should_align:bool) 
                          (diag_enclosing_type_name:ident (* for diagnostics only *))
                          (msg:string)
                          (offset:size)
                          (a:alignment)
  : ML (int & list field)
  = if not should_align
    then 0, []
    else (
      let pad_size =
          match offset, a with
          | _, None ->
            0 //no alignment for this type
          | Fixed o, Some n ->
            if o % n = 0
            then 0 //already aligned
            else n - (o % n)
          | _ ->
            //variable offset;
            //this is beyond what is expressed in C
            //no alignment needed
            0
      in
      pad_size,
      padding_field env diag_enclosing_type_name msg pad_size
    )

let sum_size (n : size) (m:size)
  = match n with
    | Variable
    | WithVariableSuffix _ -> n
    | Fixed n ->
      match m with
      | Fixed m -> Fixed (n + m)
      | WithVariableSuffix m -> WithVariableSuffix (n + m)
      | Variable -> WithVariableSuffix n

open FStar.List.Tot

let align_t = x:int{x == 1 \/ x == 2 \/ x == 4 \/ x == 8}

let union_padding (env:env_t) (swc:(expr & list case)) (size_and_alignments:list (size & alignment))
: ML ((expr & list case) & size & alignment)
= let scru, cases = swc in
  let max_size, max_alignment =
    List.fold_left #(int & align_t) #(size & alignment)
      (fun (max_sz, max_align) (size, align) ->
        let max_sz =
          match size with
          | Fixed n -> Math.Lib.max n max_sz
          | _ -> max_sz
        in
        let max_align =
          match align with
          | None -> max_align
          | Some a -> Math.Lib.max a max_align
      in
      max_sz, max_align
    ) (0, 1) size_and_alignments
  in
  let pad_case (c:case) (n:nat) : ML case =
    match c with
    | Case p f ->
      let padding_fields = padding_field env (mk_ident "__union_case_") (Printf.sprintf "(case %s)" (print_expr p)) n in
      Case p (with_dummy_range (RecordField (f :: padding_fields) (mk_ident "__union_case_")))
    | DefaultCase f ->
      let padding_fields = padding_field env (mk_ident "__union_case_") "(default case)" n in
      DefaultCase (with_dummy_range (RecordField (f :: padding_fields) (mk_ident "__union_case_")))
  in
  let cases =
    List.map2
      (fun case (size, align) ->
        match size with
        | Fixed sz ->
          if sz < max_size
          then pad_case case (max_size - sz)
          else case
        | _ -> case)
      cases size_and_alignments
  in
  (scru, cases), Fixed max_size, Some max_alignment

let rec size_and_alignment_of_field (env:env_t)
                                    (should_align:bool)
                                    (diag_enclosing_type_name:ident)
                                    (f:field) 
  : ML (res:(field & size & alignment) { let f', _, _ = res in field_tag_equal f f' })
  = match f.v with
    | AtomicField af ->
      let s, a = size_and_alignment_of_atomic_field env af in
      f, s, a

    | RecordField fields field_name ->
      let aligned_field_size
            (offset:size)
            (max_align:alignment)
            (fields:list field)
            (f:field)
        : ML (size & alignment & list field)
        = let field, field_size, field_alignment = size_and_alignment_of_field env should_align diag_enclosing_type_name f in
          let pad_size, padding_field =
            let msg = Printf.sprintf "(preceding field %s)" (print_field' field false) in
            alignment_padding env should_align diag_enclosing_type_name msg offset field_alignment
          in
          let offset =
            (offset `sum_size` (Fixed pad_size)) `sum_size`
            field_size
          in
          let max_align =
            match max_align, field_alignment with
            | None, _ -> field_alignment
            | _, None -> max_align
            | Some n, Some m -> Some (FStar.Math.Lib.max n m)
          in
          let fields =
            f ::
            padding_field @
            fields
          in
          offset, max_align, fields
      in
      let size, max_align, fields_rev =
        List.fold_left
          (fun (o, m, fs) f -> aligned_field_size o m fs f)
          (Fixed 0, None, [])
          fields
      in
      let pad_size, end_padding =
          alignment_padding env should_align diag_enclosing_type_name "(end padding)" size max_align
      in
      let size = size `sum_size` (Fixed pad_size) in
      let fields_rev = end_padding @ fields_rev in
      let fields = List.rev fields_rev in
      { f with v = RecordField fields field_name }, 
      size, 
      max_align

    | SwitchCaseField swc field_name ->
      let case_sizes =
        List.map
          (function
            | Case p f -> 
              let f, s, a = size_and_alignment_of_field env should_align diag_enclosing_type_name f in
              Case p f, (s, a)
            
            | DefaultCase f ->
              let f, s, a = size_and_alignment_of_field env should_align diag_enclosing_type_name f in
              DefaultCase f, (s, a))
          (snd swc)
      in
      let cases, size_and_alignments = List.unzip case_sizes in
      let combine_size_and_alignment
          (accum_size, accum_align)
          (f_size, f_align)
       = let size =
             match accum_size with
             | None -> Some f_size
             | Some s ->
               if s = f_size
               then Some s
               else Some Variable
         in
         let alignment : alignment =
           if None? accum_align then f_align
           else if None? f_align then accum_align
           else let Some n = accum_align in
                let Some m = f_align in
                Some (FStar.Math.Lib.max n m)
         in
         size, alignment
      in
      let size, alignment =
        List.fold_left
          combine_size_and_alignment
          (None, None)
          size_and_alignments
      in
      let size =
        match size with
        | None -> Fixed 0 //empty case type
        | Some s -> s
      in
      let alignment = if Fixed? size then alignment else None in
      let swc = fst swc, cases in
      let swc, size, alignment =
        if should_align
        then (
          let all_cases_fixed =
            List.for_all (function (Fixed _, _) -> true | _ -> false) size_and_alignments
          in
          if not all_cases_fixed
          then (
            let cases = List.zip cases size_and_alignments in
            let non_fixed_cases = List.filter (function (_, (Fixed _, _)) -> false | _ -> true) cases in
            error 
                (Printf.sprintf
                  "Type %s is a union with an 'aligned' qualifier. \
                  All cases of a union must have a fixed size to enable union padding;\n\
                  The following cases do not have a fixed size:\n%s\n"
                (ident_to_string diag_enclosing_type_name)
                (String.concat "\n"
                  (List.map
                    (fun (c, (s, _)) ->
                      Printf.sprintf "  case %s : size %s"
                        (match c with
                         | Case p _ -> print_expr p
                         | DefaultCase _ -> "(default case)")
                        (print_size s))
                    non_fixed_cases)
                ))
                f.range
          );
          if Fixed? size
          then swc, size, alignment
          else union_padding env swc size_and_alignments
       )
        else swc, size, alignment
      in
      let f = { f with v = SwitchCaseField swc field_name } in
      f, size, alignment

let field_size_and_alignment (env:env_t) (enclosing_typ:ident) (field_name:ident)
: ML (option (size & alignment))
= let ge = Binding.global_env_of_env (fst env) in
  match GlobalEnv.fields_of_type ge enclosing_typ with
  | None ->
    None
  | Some fields ->
    let found =
      List.tryFind
        (fun f ->
          match f.v with
          | AtomicField af -> eq_idents af.v.field_ident field_name
          | RecordField _ id
          | SwitchCaseField _ id -> eq_idents id field_name)
        fields  
    in
    match found with
    | None ->
      None
    | Some f ->
      let f, size, alignment = size_and_alignment_of_field env false enclosing_typ f in
      Some (size, alignment)

let should_skip (f:field) : bool =
  match f.v with
  | AtomicField af ->
    eq_typ af.v.field_type tunit
  | _ -> false
  
let field_offsets_of_type (env:env_t) (typ:ident)
: ML (either (list (ident & int)) string)
= let ge = Binding.global_env_of_env (fst env) in
  match GlobalEnv.fields_of_type ge typ with
  | None ->
    Inr <| Printf.sprintf "No fields for type %s" (ident_to_string typ)
  | Some fields ->
    let rec field_offsets (current_offset:int) (acc:list (ident & int)) (fields:list field)
    : ML (either (list (ident & int)) string)
    = match fields with
      | [] -> Inl <| List.rev acc
      | field :: fields ->
        if should_skip field
        then field_offsets current_offset acc fields
        else (
          let _, size, _ = size_and_alignment_of_field env false typ field in
          let id =
            match field.v with
            | AtomicField af -> af.v.field_ident
            | RecordField _ id
            | SwitchCaseField _ id -> id
          in
          match size with
          | Fixed n ->
            let next_offset = n + current_offset in
            field_offsets next_offset ((id, current_offset) :: acc) fields

          | WithVariableSuffix _
          | Variable ->
            Inl <| List.rev ((id, current_offset) :: acc)
        )
    in
    field_offsets 0 [] fields

let is_alignment_field (fieldname:ident) : Tot bool =
  Utils.string_starts_with (ident_to_string fieldname) alignment_prefix

let decl_size_with_alignment (env:env_t) (d:decl)
  : ML decl
  = match d.d_decl.v with
    | ModuleAbbrev _ _ -> d
    | Define _ _ _ -> d

    | TypeAbbrev _ t i _ _
    | Enum t i _ ->
      let s, a = size_and_alignment_of_typ env t in
      extend_with_size_of_ident env i s a;
      d

    | Record names generics params where fields ->
      let dummy_ident = with_dummy_range (to_ident' "_") in
      let { v = RecordField fields _ }, size, max_align = 
        size_and_alignment_of_field env (should_align names) names.typedef_name (with_dummy_range (RecordField fields dummy_ident))
      in
      extend_with_size_of_typedef_names env names size max_align;
      decl_with_v d (Record names generics params where fields)

    | CaseType names generics params cases ->
      let dummy_ident = with_dummy_range (to_ident' "_") in    
      let { v = SwitchCaseField cases _ }, size, alignment = 
        size_and_alignment_of_field env (should_align names) names.typedef_name (with_dummy_range (SwitchCaseField cases dummy_ident))
      in
      extend_with_size_of_typedef_names env names size alignment;
      decl_with_v d (CaseType names generics params cases)

    | Specialize _ _ _
    | ProbeFunction _ _ _ _
    | CoerceProbeFunctionStub _ _ _
    | OutputType _
    | ExternType _
    | ExternFn _ _ _ _
    | ExternProbe _ _ -> d

let size_of_decls (genv:B.global_env) (senv:size_env) (ds:list decl) =
  let env = B.mk_env genv, senv in
  let ds = List.map (decl_size_with_alignment env) ds in
  let ge = B.global_env_of_env (fst env) in
  ds |> List.iter (fun d ->
  idents_of_decl d |> List.iter (fun i ->
  match H.try_find ge.ge_h i.v with
  | None -> ()
  | Some (_, attrs) ->  H.insert ge.ge_h i.v (d, attrs)));
  ds

let finish_module en mname e_and_p =
  e_and_p |> snd |> List.iter (H.remove en)
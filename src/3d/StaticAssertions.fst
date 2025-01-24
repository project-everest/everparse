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
module StaticAssertions
open FStar.All
open Ast
module B = Binding

noeq
type sizeof_assertion = {
  type_name : ident;
  size : int
}

noeq
type offsetof_assertion = {
  type_name : ident;
  field_name : ident;
  offset : int
}

noeq
type static_assert =
| SizeOfAssertion of sizeof_assertion
| OffsetOfAssertion of offsetof_assertion

noeq
type static_asserts = {
  includes : list string;
  assertions : list static_assert
}

let empty_static_asserts = {
  includes = [];
  assertions = []
}

let compute_static_asserts (benv:B.global_env)
                           (senv:TypeSizes.size_env)
                           (r:option type_refinement)
  : ML static_asserts
  = let env = B.mk_env benv, senv in
    match r with
    | None -> empty_static_asserts
    | Some r -> 
      let static_assertions =
        r.type_map
        |> List.collect
          (fun (i, jopt) ->
            let j =
              match jopt with
              | None -> i
              | Some j -> j
            in
            let offsets = TypeSizes.field_offsets_of_type env j in
            let offset_of_assertions =
              match offsets with
              | Inr msg ->
                Ast.warning 
                  (Printf.sprintf
                    "No offsetof assertions for type %s because %s\n"
                    (ident_to_string j)
                    msg)
                  i.range;
                []
              | Inl offsets ->
                offsets |>
                List.collect
                  (fun offset -> 
                    if TypeSizes.is_alignment_field (fst offset)
                    then []
                    else [OffsetOfAssertion { 
                            type_name = i;
                            field_name = fst offset;
                            offset = snd offset }])
            in
            let t_j = with_dummy_range (Type_app j KindSpec []) in
            let sizeof_assertion =
              match TypeSizes.size_of_typ env t_j with
              | TypeSizes.Fixed n
              | TypeSizes.WithVariableSuffix n ->
                SizeOfAssertion {
                  type_name = i;
                  size = n }
              | _ -> 
                Ast.error 
                  (Printf.sprintf
                    "Type %s is variable sized and cannot refine a C type %s"
                    (ident_to_string j) (ident_to_string i))
                  i.range
            in
            sizeof_assertion::offset_of_assertions)
      in
      {
        includes = r.Ast.includes;
        assertions = static_assertions
      }

let no_static_asserts (sas: static_asserts) : Tot bool =
  Nil? sas.includes &&
  Nil? sas.assertions

let has_static_asserts (sas: static_asserts) : Tot bool =
  not (no_static_asserts sas)

let print_static_asserts (sas:static_asserts)
  : ML string
  = let includes =
        sas.includes
        |> List.map (fun i -> Printf.sprintf "#include \"%s\"" i)
        |> String.concat "\n"
    in
    let print_static_assert (sa:static_assert) =
      match sa with
      | SizeOfAssertion sa ->
        Printf.sprintf "EVERPARSE_STATIC_ASSERT(sizeof(%s) == %d);" (ident_to_string sa.type_name) sa.size
      | OffsetOfAssertion oa ->
        Printf.sprintf "EVERPARSE_STATIC_ASSERT(offsetof(%s, %s) == %d);" (ident_to_string oa.type_name) (ident_to_string oa.field_name) oa.offset
    in
    let sizeof_assertions =
        sas.assertions
        |> List.map print_static_assert
        |> String.concat "\n"
    in
    let define_c_assert = 
      "#define EVERPARSE_STATIC_ASSERT(e) typedef char __EVERPARSE_STATIC_ASSERT__[(e)?1:-1];"
    in
    "#include <stddef.h>\n" ^
    Options.make_includes () ^
    includes ^ "\n" ^
    define_c_assert ^ "\n" ^
    sizeof_assertions

(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module JSON

(* JSON for the 3d frontend: the `--json` dump of the source AST, and the
   `--config` file.

   This used to be `[@@ PpxDerivingYoJson]` on the types of Ast and Config
   plus a hand-written OCaml file calling into Yojson. The encoding below is
   the one ppx_deriving_yojson produced, so a `--json` dump and a config file
   still read the same way:

     - a record is an object whose keys are the field names;
     - a constructor is an array whose first element is its name, followed by
       one element per argument, so a nullary constructor is a one-element
       array;
     - a tuple is an array;
     - `None` is `null` and `Some x` is `x` itself;
     - `with_meta_t` is transparent, i.e. it serializes as its `v` field, so
       that ranges and comments do not pollute the output. *)

open FStar.All
open Ast
module Char = FStar.Char
module String = FStar.String
module List = FStar.List.Tot

(* -------------------------------------------------------------------- *)
(* JSON values                                                          *)
(* -------------------------------------------------------------------- *)

noeq
type json =
  | JNull
  | JBool   of bool
  | JInt    of int
  | JString of string
  | JList   of list json
  | JAssoc  of list (string & json)

let hex_digit (i:int) : string =
  match i with
  | 0 -> "0" | 1 -> "1" | 2 -> "2" | 3 -> "3"
  | 4 -> "4" | 5 -> "5" | 6 -> "6" | 7 -> "7"
  | 8 -> "8" | 9 -> "9" | 10 -> "a" | 11 -> "b"
  | 12 -> "c" | 13 -> "d" | 14 -> "e" | _ -> "f"

let escape_char (c:Char.char) : ML string =
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\r' then "\\r"
  else if c = '\t' then "\\t"
  else
    let i = Char.int_of_char c in
    (* Everything below U+0020 has to be escaped; the rest is emitted as it
       stands, which for a code point above U+007F means the UTF-8 that
       [string_of_char] gives back. *)
    if i < 0x20
    then "\\u00" ^ hex_digit (i / 16) ^ hex_digit (i % 16)
    else String.string_of_char c

let escape_string (s:string) : ML string =
  String.concat "" (FStar.List.map escape_char (String.list_of_string s))

let rec json_to_string (j:json) : ML string =
  match j with
  | JNull -> "null"
  | JBool true -> "true"
  | JBool false -> "false"
  | JInt i -> Printf.sprintf "%d" i
  | JString s -> "\"" ^ escape_string s ^ "\""
  | JList js ->
    "[" ^ String.concat "," (FStar.List.map json_to_string js) ^ "]"
  | JAssoc fs ->
    "{" ^
    String.concat ","
      (FStar.List.map
        (fun (f, j) -> "\"" ^ escape_string f ^ "\":" ^ json_to_string j) fs) ^
    "}"

(* -------------------------------------------------------------------- *)
(* Serializing the source AST                                           *)
(* -------------------------------------------------------------------- *)

let jctor (name:string) (args:list json) : json = JList (JString name :: args)

let jopt (f:'a -> ML json) (x:option 'a) : ML json =
  match x with
  | None -> JNull
  | Some v -> f v

let jlist (f:'a -> ML json) (xs:list 'a) : ML json =
  JList (FStar.List.map f xs)

let jstring (s:string) : json = JString s

let pos_to_json (p:pos) : json =
  JAssoc [
    "filename", JString p.filename;
    "line", JInt p.line;
    "col", JInt p.col;
  ]

let range_to_json (r:range) : json =
  let p, q = r in
  JList [pos_to_json p; pos_to_json q]

let ident'_to_json (i:ident') : ML json =
  JAssoc [
    "modul_name", jopt jstring i.modul_name;
    "name", JString i.name;
  ]

let ident_to_json (i:ident) : ML json = ident'_to_json i.v

let integer_type_to_json (t:integer_type) : json =
  jctor (match t with
         | UInt8 -> "UInt8"
         | UInt16 -> "UInt16"
         | UInt32 -> "UInt32"
         | UInt64 -> "UInt64")
        []

let bitfield_bit_order_to_json (o:bitfield_bit_order) : json =
  jctor (match o with
         | LSBFirst -> "LSBFirst"
         | MSBFirst -> "MSBFirst")
        []

let constant_to_json (c:constant) : json =
  match c with
  | Unit -> jctor "Unit" []
  | Int t i -> jctor "Int" [integer_type_to_json t; JInt i]
  | XInt t s -> jctor "XInt" [integer_type_to_json t; JString s]
  | Bool b -> jctor "Bool" [JBool b]
  | String s -> jctor "String" [JString s]

let op_to_json (o:op) : ML json =
  let un (name:string) (t:option integer_type) : ML json =
    jctor name [jopt integer_type_to_json t]
  in
  match o with
  | Eq -> jctor "Eq" []
  | Neq -> jctor "Neq" []
  | And -> jctor "And" []
  | Or -> jctor "Or" []
  | Not -> jctor "Not" []
  | Plus t -> un "Plus" t
  | Minus t -> un "Minus" t
  | Mul t -> un "Mul" t
  | Division t -> un "Division" t
  | Remainder t -> un "Remainder" t
  | BitwiseAnd t -> un "BitwiseAnd" t
  | BitwiseXor t -> un "BitwiseXor" t
  | BitwiseOr t -> un "BitwiseOr" t
  | BitwiseNot t -> un "BitwiseNot" t
  | ShiftRight t -> un "ShiftRight" t
  | ShiftLeft t -> un "ShiftLeft" t
  | LT t -> un "LT" t
  | GT t -> un "GT" t
  | LE t -> un "LE" t
  | GE t -> un "GE" t
  | IfThenElse -> jctor "IfThenElse" []
  | BitFieldOf sz order ->
    jctor "BitFieldOf" [JInt sz; bitfield_bit_order_to_json order]
  | SizeOf -> jctor "SizeOf" []
  | Cast from to -> jctor "Cast" [jopt integer_type_to_json from;
                                  integer_type_to_json to]
  | Ext s -> jctor "Ext" [JString s]
  | ProbeFunctionName i -> jctor "ProbeFunctionName" [ident_to_json i]

let rec expr'_to_json (e:expr') : ML json =
  match e with
  | Constant c -> jctor "Constant" [constant_to_json c]
  | Identifier i -> jctor "Identifier" [ident_to_json i]
  | Static e -> jctor "Static" [expr_to_json e]
  | This -> jctor "This" []
  | App o es -> jctor "App" [op_to_json o; jlist expr_to_json es]

and expr_to_json (e:expr) : ML json = expr'_to_json e.v

let t_kind_to_json (k:t_kind) : json =
  jctor (match k with
         | KindSpec -> "KindSpec"
         | KindOutput -> "KindOutput"
         | KindExtern -> "KindExtern")
        []

let rec out_expr'_to_json (o:out_expr') : ML json =
  match o with
  | OE_id i -> jctor "OE_id" [ident_to_json i]
  | OE_star o -> jctor "OE_star" [out_expr_to_json o]
  | OE_addrof o -> jctor "OE_addrof" [out_expr_to_json o]
  | OE_deref o i -> jctor "OE_deref" [out_expr_to_json o; ident_to_json i]
  | OE_dot o i -> jctor "OE_dot" [out_expr_to_json o; ident_to_json i]

and out_expr_meta_t_to_json (m:out_expr_meta_t) : ML json =
  JAssoc [
    "out_expr_base_t", typ_to_json m.out_expr_base_t;
    "out_expr_t", typ_to_json m.out_expr_t;
    "out_expr_bit_width", jopt (fun (i:int) -> JInt i) m.out_expr_bit_width;
  ]

and out_expr_to_json (o:out_expr) : ML json =
  JAssoc [
    "out_expr_node", out_expr'_to_json o.out_expr_node.v;
    "out_expr_meta", jopt out_expr_meta_t_to_json o.out_expr_meta;
  ]

and typ_param_to_json (p:typ_param) : ML json =
  match p with
  | Inl e -> jctor "Inl" [expr_to_json e]
  | Inr o -> jctor "Inr" [out_expr_to_json o]

and typ'_to_json (t:typ') : ML json =
  match t with
  | Type_app i k gs ps ->
    jctor "Type_app" [ident_to_json i; t_kind_to_json k;
                      jlist expr_to_json gs; jlist typ_param_to_json ps]
  | Pointer t q -> jctor "Pointer" [typ_to_json t; pointer_qualifier_to_json q]
  | Type_arrow args t ->
    jctor "Type_arrow" [jlist typ_to_json args; typ_to_json t]

and pointer_qualifier_to_json (q:pointer_qualifier) : ML json =
  match q with
  | PQ pq explicit nullable ->
    jctor "PQ" [integer_type_to_json pq; JBool explicit; JBool nullable]

and typ_to_json (t:typ) : ML json = typ'_to_json t.v

let atomic_action_to_json (a:atomic_action) : ML json =
  match a with
  | Action_return e -> jctor "Action_return" [expr_to_json e]
  | Action_abort -> jctor "Action_abort" []
  | Action_field_pos_64 -> jctor "Action_field_pos_64" []
  | Action_field_pos_32 -> jctor "Action_field_pos_32" []
  | Action_field_ptr -> jctor "Action_field_ptr" []
  | Action_field_ptr_after sz write_to ->
    jctor "Action_field_ptr_after" [expr_to_json sz; out_expr_to_json write_to]
  | Action_deref i -> jctor "Action_deref" [ident_to_json i]
  | Action_assignment lhs rhs ->
    jctor "Action_assignment" [out_expr_to_json lhs; expr_to_json rhs]
  | Action_call f args ->
    jctor "Action_call" [ident_to_json f; jlist expr_to_json args]

let rec action'_to_json (a:action') : ML json =
  match a with
  | Atomic_action a -> jctor "Atomic_action" [atomic_action_to_json a]
  | Action_seq hd tl ->
    jctor "Action_seq" [atomic_action_to_json hd; action_to_json tl]
  | Action_ite hd then_ else_ ->
    jctor "Action_ite" [expr_to_json hd; action_to_json then_;
                        jopt action_to_json else_]
  | Action_let i a k ->
    jctor "Action_let" [ident_to_json i; atomic_action_to_json a;
                        action_to_json k]
  | Action_act a -> jctor "Action_act" [action_to_json a]

and action_to_json (a:action) : ML json = action'_to_json a.v

let qualifier_to_json (q:qualifier) : json =
  jctor (match q with
         | Immutable -> "Immutable"
         | Mutable -> "Mutable")
        []

let param_to_json (p:param) : ML json =
  let t, i, q = p in
  JList [typ_to_json t; ident_to_json i; qualifier_to_json q]

let bitfield_attr'_to_json (b:bitfield_attr') : ML json =
  JAssoc [
    "bitfield_width", JInt b.bitfield_width;
    "bitfield_identifier", JInt b.bitfield_identifier;
    "bitfield_type", typ_to_json b.bitfield_type;
    "bitfield_from", JInt b.bitfield_from;
    "bitfield_to", JInt b.bitfield_to;
  ]

let bitfield_attr_to_json (b:bitfield_attr) : ML json =
  bitfield_attr'_to_json b.v

let field_bitwidth_t_to_json (f:field_bitwidth_t) : ML json =
  match f with
  | Inl n -> jctor "Inl" [JInt n.v]
  | Inr b -> jctor "Inr" [bitfield_attr_to_json b]

let array_qualifier_to_json (q:array_qualifier) : json =
  jctor (match q with
         | ByteArrayByteSize -> "ByteArrayByteSize"
         | ArrayByteSize -> "ArrayByteSize"
         | ArrayByteSizeAtMost -> "ArrayByteSizeAtMost"
         | ArrayByteSizeSingleElementArray -> "ArrayByteSizeSingleElementArray")
        []

let field_array_t_to_json (f:field_array_t) : ML json =
  match f with
  | FieldScalar -> jctor "FieldScalar" []
  | FieldArrayQualified eq ->
    let e, q = eq in
    jctor "FieldArrayQualified" [JList [expr_to_json e;
                                        array_qualifier_to_json q]]
  | FieldString e -> jctor "FieldString" [jopt expr_to_json e]
  | FieldConsumeAll -> jctor "FieldConsumeAll" []

let probe_field_to_json (p:probe_field) : ML json =
  match p with
  | ProbeLength e -> jctor "ProbeLength" [expr_to_json e]
  | ProbeDest e -> jctor "ProbeDest" [expr_to_json e]

let probe_atomic_action_to_json (p:probe_atomic_action) : ML json =
  match p with
  | Probe_action_return e -> jctor "Probe_action_return" [expr_to_json e]
  | Probe_action_call f args ->
    jctor "Probe_action_call" [ident_to_json f; jlist expr_to_json args]
  | Probe_action_read f -> jctor "Probe_action_read" [ident_to_json f]
  | Probe_action_write f value ->
    jctor "Probe_action_write" [ident_to_json f; expr_to_json value]
  | Probe_action_copy_and_return reader writer ty maybe_warn ->
    jctor "Probe_action_copy_and_return"
      [ident_to_json reader; ident_to_json writer; integer_type_to_json ty;
       jopt (fun (sr:string & range) ->
               let s, r = sr in
               JList [JString s; range_to_json r])
            maybe_warn]
  | Probe_action_copy f len ->
    jctor "Probe_action_copy" [ident_to_json f; expr_to_json len]
  | Probe_action_skip_read len ->
    jctor "Probe_action_skip_read" [expr_to_json len]
  | Probe_action_skip_write len ->
    jctor "Probe_action_skip_write" [expr_to_json len]
  | Probe_action_fail -> jctor "Probe_action_fail" []

let rec probe_action'_to_json (p:probe_action') : ML json =
  match p with
  | Probe_atomic_action a ->
    jctor "Probe_atomic_action" [probe_atomic_action_to_json a]
  | Probe_action_var e -> jctor "Probe_action_var" [expr_to_json e]
  | Probe_action_seq detail hd tl ->
    jctor "Probe_action_seq" [expr_to_json detail; probe_action_to_json hd;
                              probe_action_to_json tl]
  | Probe_action_let detail i a k ->
    jctor "Probe_action_let" [expr_to_json detail; ident_to_json i;
                              probe_atomic_action_to_json a;
                              probe_action_to_json k]
  | Probe_action_ite hd then_ else_ ->
    jctor "Probe_action_ite" [expr_to_json hd; probe_action_to_json then_;
                              probe_action_to_json else_]
  | Probe_action_array len action ->
    jctor "Probe_action_array" [expr_to_json len; probe_action_to_json action]
  | Probe_action_copy_init_sz f ->
    jctor "Probe_action_copy_init_sz" [ident_to_json f]

and probe_action_to_json (p:probe_action) : ML json = probe_action'_to_json p.v

let probe_call_to_json (p:probe_call) : ML json =
  JAssoc [
    "probe_dest", ident_to_json p.probe_dest;
    "probe_block", probe_action_to_json p.probe_block;
    "probe_ptr_as_u64", jopt ident_to_json p.probe_ptr_as_u64;
    "probe_dest_sz", expr_to_json p.probe_dest_sz;
    "probe_init", jopt ident_to_json p.probe_init;
  ]

let rec atomic_field'_to_json (a:atomic_field') : ML json =
  JAssoc [
    "field_dependence", JBool a.field_dependence;
    "field_ident", ident_to_json a.field_ident;
    "field_type", typ_to_json a.field_type;
    "field_array_opt", field_array_t_to_json a.field_array_opt;
    "field_constraint", jopt expr_to_json a.field_constraint;
    "field_bitwidth", jopt field_bitwidth_t_to_json a.field_bitwidth;
    "field_action", jopt (fun (ab:action & bool) ->
                            let a, b = ab in
                            JList [action_to_json a; JBool b])
                         a.field_action;
    "field_probe", jopt probe_call_to_json a.field_probe;
  ]

and atomic_field_to_json (a:atomic_field) : ML json = atomic_field'_to_json a.v

and field'_to_json (f:field') : ML json =
  match f with
  | AtomicField a -> jctor "AtomicField" [atomic_field_to_json a]
  | RecordField r i -> jctor "RecordField" [record_to_json r; ident_to_json i]
  | SwitchCaseField s i ->
    jctor "SwitchCaseField" [switch_case_to_json s; ident_to_json i]

and field_to_json (f:field) : ML json = field'_to_json f.v

and record_to_json (r:record) : ML json = jlist field_to_json r

and case_to_json (c:case) : ML json =
  match c with
  | Case e f -> jctor "Case" [expr_to_json e; field_to_json f]
  | DefaultCase f -> jctor "DefaultCase" [field_to_json f]

and switch_case_to_json (s:switch_case) : ML json =
  let e, cs = s in
  JList [expr_to_json e; jlist case_to_json cs]

let probe_entrypoint_to_json (p:probe_entrypoint) : ML json =
  JAssoc [
    "probe_ep_init", jopt ident_to_json p.probe_ep_init;
    "probe_ep_fn", ident_to_json p.probe_ep_fn;
    "probe_ep_length", expr_to_json p.probe_ep_length;
  ]

let attribute_to_json (a:attribute) : ML json =
  match a with
  | Entrypoint ep_name probe ->
    jctor "Entrypoint" [jopt ident_to_json ep_name;
                        jopt probe_entrypoint_to_json probe]
  | Aligned -> jctor "Aligned" []
  | Noextract -> jctor "Noextract" []

let typedef_names_to_json (t:typedef_names) : ML json =
  JAssoc [
    "typedef_name", ident_to_json t.typedef_name;
    "typedef_abbrev", ident_to_json t.typedef_abbrev;
    "typedef_ptr_abbrev", jopt ident_to_json t.typedef_ptr_abbrev;
    "typedef_attributes", jlist attribute_to_json t.typedef_attributes;
  ]

let enum_case_to_json (e:enum_case) : ML json =
  let i, v = e in
  JList [ident_to_json i;
         jopt (fun (x:either int ident) ->
                 match x with
                 | Inl n -> jctor "Inl" [JInt n]
                 | Inr i -> jctor "Inr" [ident_to_json i])
              v]

let rec out_field_to_json (o:out_field) : ML json =
  match o with
  | Out_field_named i t bit_width ->
    jctor "Out_field_named" [ident_to_json i; typ_to_json t;
                             jopt (fun (n:int) -> JInt n) bit_width]
  | Out_field_anon fs is_union ->
    jctor "Out_field_anon" [jlist out_field_to_json fs; JBool is_union]

let out_typ_to_json (o:out_typ) : ML json =
  JAssoc [
    "out_typ_names", typedef_names_to_json o.out_typ_names;
    "out_typ_fields", jlist out_field_to_json o.out_typ_fields;
    "out_typ_is_union", JBool o.out_typ_is_union;
  ]

let probe_qualifier_to_json (q:probe_qualifier) : json =
  match q with
  | PQWithOffsets -> jctor "PQWithOffsets" []
  | PQInit -> jctor "PQInit" []
  | PQRead t -> jctor "PQRead" [integer_type_to_json t]
  | PQWrite t -> jctor "PQWrite" [integer_type_to_json t]

let generic_param_to_json (g:generic_param) : ML json =
  match g with
  | GenericProbeFunction param_name k probe_for_type ->
    jctor "GenericProbeFunction" [ident_to_json param_name; typ_to_json k;
                                  ident_to_json probe_for_type]

let probe_function_type_to_json (p:probe_function_type) : ML json =
  match p with
  | SimpleProbeFunction i -> jctor "SimpleProbeFunction" [ident_to_json i]
  | CoerceProbeFunctionPlaceholder i ->
    jctor "CoerceProbeFunctionPlaceholder" [ident_to_json i]
  | CoerceProbeFunction ii ->
    let i1, i2 = ii in
    jctor "CoerceProbeFunction" [JList [ident_to_json i1; ident_to_json i2]]
  | HelperProbeFunction -> jctor "HelperProbeFunction" []

let decl'_to_json (d:decl') : ML json =
  match d with
  | ModuleAbbrev i j -> jctor "ModuleAbbrev" [ident_to_json i; ident_to_json j]
  | Define i t c ->
    jctor "Define" [ident_to_json i; jopt typ_to_json t; constant_to_json c]
  | TypeAbbrev attrs t i gs ps ->
    jctor "TypeAbbrev" [jlist attribute_to_json attrs; typ_to_json t;
                        ident_to_json i; jlist generic_param_to_json gs;
                        jlist param_to_json ps]
  | Enum t i cases ->
    jctor "Enum" [typ_to_json t; ident_to_json i; jlist enum_case_to_json cases]
  | Record names generics params where fields ->
    jctor "Record" [typedef_names_to_json names;
                    jlist generic_param_to_json generics;
                    jlist param_to_json params; jopt expr_to_json where;
                    record_to_json fields]
  | CaseType names generics params sc ->
    jctor "CaseType" [typedef_names_to_json names;
                      jlist generic_param_to_json generics;
                      jlist param_to_json params; switch_case_to_json sc]
  | ProbeFunction i params body t ->
    jctor "ProbeFunction" [ident_to_json i; jlist param_to_json params;
                           probe_action_to_json body;
                           probe_function_type_to_json t]
  | Specialize ts i j ->
    jctor "Specialize" [jlist (fun (tt:integer_type & integer_type) ->
                                 let t1, t2 = tt in
                                 JList [integer_type_to_json t1;
                                        integer_type_to_json t2])
                              ts;
                        ident_to_json i; ident_to_json j]
  | CoerceProbeFunctionStub i params p ->
    jctor "CoerceProbeFunctionStub" [ident_to_json i; jlist param_to_json params;
                                     probe_function_type_to_json p]
  | OutputType o -> jctor "OutputType" [out_typ_to_json o]
  | ExternType names -> jctor "ExternType" [typedef_names_to_json names]
  | ExternFn i t params pure ->
    jctor "ExternFn" [ident_to_json i; typ_to_json t; jlist param_to_json params;
                      JBool pure]
  | ExternProbe i q -> jctor "ExternProbe" [ident_to_json i;
                                            probe_qualifier_to_json q]

let decl_to_json (d:decl) : ML json =
  JAssoc [
    "d_decl", decl'_to_json d.d_decl.v;
    "d_exported", JBool d.d_exported;
  ]

let type_refinement_to_json (t:type_refinement) : ML json =
  let map_to_json (m:list (ident & option ident)) : ML json =
    jlist (fun (ii:ident & option ident) ->
             let i, j = ii in
             JList [ident_to_json i; jopt ident_to_json j])
          m
  in
  JAssoc [
    "includes", jlist (fun (s:string) -> JString s) t.includes;
    "type_map", map_to_json t.type_map;
    "auto_type_map", map_to_json t.auto_type_map;
  ]

let prog_to_json (p:Ast.prog) : ML string =
  let decls, refinement = p in
  json_to_string (JList [jlist decl_to_json decls;
                         jopt type_refinement_to_json refinement])

(* -------------------------------------------------------------------- *)
(* The configuration file                                               *)
(* -------------------------------------------------------------------- *)

let compile_time_flags_to_json (f:Config.compile_time_flags) : ML json =
  JAssoc [
    "flags", jlist (fun (s:string) -> JString s) f.flags;
    "include_file", JString f.include_file;
  ]

let config_to_json (c:Config.config) : ML string =
  json_to_string
    (JAssoc ["compile_time_flags",
             compile_time_flags_to_json c.compile_time_flags])

(* -------------------------------------------------------------------- *)
(* Parsing                                                              *)
(* -------------------------------------------------------------------- *)

exception JSONError of string

let fail (#a:Type) (msg:string) : ML a = raise (JSONError msg)

let is_ws (c:Char.char) : bool =
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

let is_digit (c:Char.char) : bool =
  let i = Char.int_of_char c in
  i >= 0x30 && i <= 0x39

let digit_value (c:Char.char) : int = Char.int_of_char c - 0x30

let rec skip_ws (cs:list Char.char) : list Char.char =
  match cs with
  | c :: tl -> if is_ws c then skip_ws tl else cs
  | [] -> []

(* [\uXXXX] is decoded to the code point it names; a surrogate pair is not
   recombined, which is what Yojson did too. *)
let hex_value (c:Char.char) : ML int =
  let i = Char.int_of_char c in
  if i >= 0x30 && i <= 0x39 then i - 0x30
  else if i >= 0x61 && i <= 0x66 then i - 0x61 + 10
  else if i >= 0x41 && i <= 0x46 then i - 0x41 + 10
  else fail "Invalid hexadecimal digit in a \\u escape"

let rec parse_string_chars (acc:list Char.char) (cs:list Char.char)
  : ML (string & list Char.char)
  = match cs with
    | [] -> fail "Unterminated string"
    | '"' :: tl -> String.string_of_list (List.rev acc), tl
    | '\\' :: e :: tl ->
      let c, tl =
        if e = '"' then '"', tl
        else if e = '\\' then '\\', tl
        else if e = '/' then '/', tl
        else if e = 'b' then Char.char_of_int 0x08, tl
        else if e = 'f' then Char.char_of_int 0x0c, tl
        else if e = 'n' then '\n', tl
        else if e = 'r' then '\r', tl
        else if e = 't' then '\t', tl
        else if e = 'u'
        then match tl with
             | a :: b :: c :: d :: tl ->
               let v = ((hex_value a * 16 + hex_value b) * 16 +
                        hex_value c) * 16 + hex_value d in
               (* A lone surrogate has no code point of its own; U+FFFD is
                  what a decoder is expected to put in its place. *)
               (if v >= 0xd800 && v <= 0xdfff
                then Char.char_of_int 0xfffd
                else Char.char_of_int v), tl
             | _ -> fail "Truncated \\u escape"
        else fail "Unknown escape sequence in a string"
      in
      parse_string_chars (c :: acc) tl
    | c :: tl -> parse_string_chars (c :: acc) tl

let parse_string (cs:list Char.char) : ML (string & list Char.char) =
  match cs with
  | '"' :: tl -> parse_string_chars [] tl
  | _ -> fail "Expected a string"

let rec parse_digits (acc:int) (cs:list Char.char) : ML (int & list Char.char) =
  match cs with
  | c :: tl -> if is_digit c
               then parse_digits (acc * 10 + digit_value c) tl
               else acc, cs
  | [] -> acc, cs

let expect (c:Char.char) (cs:list Char.char) : ML (list Char.char) =
  match skip_ws cs with
  | c' :: tl -> if c = c' then tl
                else fail (Printf.sprintf "Expected %s"
                             (String.string_of_char c))
  | [] -> fail (Printf.sprintf "Expected %s, found the end of the input"
                  (String.string_of_char c))

let starts_with (prefix:list Char.char) (cs:list Char.char)
  : option (list Char.char)
  = let rec aux (p:list Char.char) (cs:list Char.char) =
      match p, cs with
      | [], _ -> Some cs
      | pc :: p, c :: cs -> if pc = c then aux p cs else None
      | _, [] -> None
    in
    aux prefix cs

let rec parse_value (cs:list Char.char) : ML (json & list Char.char) =
  let cs = skip_ws cs in
  match cs with
  | [] -> fail "Unexpected end of the input"
  | '"' :: _ -> let s, tl = parse_string cs in JString s, tl
  | '{' :: tl -> parse_object [] (skip_ws tl)
  | '[' :: tl -> parse_array [] (skip_ws tl)
  | '-' :: tl -> let n, tl = parse_digits 0 tl in JInt (0 - n), tl
  | c :: _ ->
    if is_digit c
    then let n, tl = parse_digits 0 cs in JInt n, tl
    else match starts_with (String.list_of_string "true") cs with
         | Some tl -> JBool true, tl
         | None ->
           match starts_with (String.list_of_string "false") cs with
           | Some tl -> JBool false, tl
           | None ->
             match starts_with (String.list_of_string "null") cs with
             | Some tl -> JNull, tl
             | None -> fail "Expected a value"

and parse_object (acc:list (string & json)) (cs:list Char.char)
  : ML (json & list Char.char)
  = match cs with
    | '}' :: tl -> JAssoc (List.rev acc), tl
    | _ ->
      let key, tl = parse_string (skip_ws cs) in
      let tl = expect ':' tl in
      let v, tl = parse_value tl in
      match skip_ws tl with
      | ',' :: tl -> parse_object ((key, v) :: acc) (skip_ws tl)
      | '}' :: tl -> JAssoc (List.rev ((key, v) :: acc)), tl
      | _ -> fail "Expected , or } in an object"

and parse_array (acc:list json) (cs:list Char.char)
  : ML (json & list Char.char)
  = match cs with
    | ']' :: tl -> JList (List.rev acc), tl
    | _ ->
      let v, tl = parse_value cs in
      match skip_ws tl with
      | ',' :: tl -> parse_array (v :: acc) (skip_ws tl)
      | ']' :: tl -> JList (List.rev (v :: acc)), tl
      | _ -> fail "Expected , or ] in an array"

let json_of_string (s:string) : ML json =
  let v, rest = parse_value (String.list_of_string s) in
  match skip_ws rest with
  | [] -> v
  | _ -> fail "Trailing characters after the JSON value"

(* -------------------------------------------------------------------- *)
(* Reading the configuration file                                       *)
(* -------------------------------------------------------------------- *)

let field_of (o:json) (name:string) (what:string) : ML json =
  match o with
  | JAssoc fs ->
    (match List.assoc name fs with
     | Some v -> v
     | None -> fail (Printf.sprintf "%s: missing field %s" what name))
  | _ -> fail (Printf.sprintf "%s: expected an object" what)

let string_of_json (j:json) (what:string) : ML string =
  match j with
  | JString s -> s
  | _ -> fail (Printf.sprintf "%s: expected a string" what)

let compile_time_flags_of_json (j:json) : ML Config.compile_time_flags =
  let what = "Config.compile_time_flags" in
  let flags =
    match field_of j "flags" what with
    | JList js -> FStar.List.map (fun j -> string_of_json j (what ^ ".flags")) js
    | _ -> fail (Printf.sprintf "%s: expected a list of strings" what)
  in
  let include_file =
    string_of_json (field_of j "include_file" what) (what ^ ".include_file")
  in
  { flags; include_file }

let config_of_json (s:string) : ML (FStar.Pervasives.either Config.config string) =
  try
    let j = json_of_string s in
    let flags =
      compile_time_flags_of_json
        (field_of j "compile_time_flags" "Config.config")
    in
    FStar.Pervasives.Inl ({ compile_time_flags = flags } <: Config.config)
  with
  | JSONError msg -> FStar.Pervasives.Inr msg

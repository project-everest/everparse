open Fstar_pluginlib
type name_env = (Prims.string * CDDL_Spec_AST_Base.name_env_elem) list

let cddl_env_of_env (f: name_env) (s: Prims.string) : CDDL_Spec_AST_Base.name_env_elem option =
  try
    FStar_Pervasives_Native.Some (List.assoc s f)
  with Not_found -> FStar_Pervasives_Native.None

let extend_name_env (env: name_env) (name: Prims.string) (k: CDDL_Spec_AST_Base.name_env_elem) : name_env =
  List.sort
    (fun x y -> compare (fst x) (fst y))
    ((name, k) :: env)

let check_name (env : name_env) (name : Prims.string)
  (k : CDDL_Spec_AST_Base.name_env_elem) :
  name_env FStar_Pervasives_Native.option=
  match cddl_env_of_env env name with
  | FStar_Pervasives_Native.None ->
      FStar_Pervasives_Native.Some
        (extend_name_env env name k)
  | FStar_Pervasives_Native.Some k' ->
      if k = k'
      then FStar_Pervasives_Native.Some env
      else FStar_Pervasives_Native.None

let empty_name_env : name_env = []

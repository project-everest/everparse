module CDDL.Interpreter.Pulse
include CDDL.Interpreter.AST

module Spec = CDDL.Spec
module CP = CDDL.Pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick
open Pulse.Lib.SeqMatch

module U8 = FStar.UInt8
module A = Pulse.Lib.Array
module U64 = FStar.UInt64

let impl_elem_type_sem
  (t: target_elem_type)
: Tot Type0
= match t with
  | TTSimple -> CBOR.Spec.simple_value
  | TTUInt64 -> U64.t
  | TTUnit -> unit
  | TTBool -> bool
  | TTString -> A.array U8.t
  | TTAny -> CBOR.Pulse.cbor
  | TTAlwaysFalse -> squash False

let impl_table (key value: Type) = A.array (key & value)

let rec impl_type_sem
  (#bound: name_env)
  (env: target_spec_env bound)
  (t: target_type)
: Pure Type0
  (requires target_type_bounded bound t)
  (ensures fun _ -> True)
= match t with
  | TTDef s -> env s
  | TTPair t1 t2 -> impl_type_sem env t1 & impl_type_sem env t2
  | TTUnion t1 t2 -> impl_type_sem env t1 `either` impl_type_sem env t2
  | TTArray a -> A.array (impl_type_sem env a)
  | TTTable t1 t2 -> impl_table (impl_type_sem env t1) (impl_type_sem env t2)
  | TTOption a -> option (impl_type_sem env a)
  | TTElem e -> impl_elem_type_sem e

let impl_type_sem_incr
  (#bound: name_env)
  (env: target_spec_env bound)
  (#bound': name_env)
  (env': target_spec_env bound')
  (t: target_type)
: Lemma
  (requires target_type_bounded bound t /\
    target_spec_env_included env env'
  )
  (ensures
    target_type_bounded bound' t /\
    impl_type_sem env' t == impl_type_sem env t
  )
  [SMTPatOr [
    [SMTPat (target_spec_env_included env env'); SMTPat (impl_type_sem env t)];
    [SMTPat (target_spec_env_included env env'); SMTPat (impl_type_sem env' t)];
  ]]
= admit ()

let rel (t1 t2: Type) = t1 -> t2 -> vprop

noeq
type impl_env
    (#bound: name_env)
    (high: target_spec_env bound)
=   {
        i_low: target_spec_env bound;
        i_r: (n: name bound) -> rel (i_low n) (high n);
    }

[@@"opaque_to_smt"] irreducible
let empty_impl_env (e: target_spec_env empty_name_env) : impl_env e = {
  i_low = empty_target_spec_env;
  i_r = (fun _ _ _ -> pure False);
}

let impl_env_included
    (#bound: name_env)
    (#high: target_spec_env bound)
    (env: impl_env high)
    (#bound': name_env)
    (#high': target_spec_env bound')
    (env': impl_env high')
: Tot prop
= target_spec_env_included high high' /\
  target_spec_env_included env.i_low env'.i_low /\
  (forall (n: name bound) . env.i_r n == env'.i_r n)

let impl_env_extend
    (#bound: name_env)
    (#high_env: target_spec_env bound)
    (env: impl_env high_env)
    (n: string { ~ (name_mem n bound) })
  (s: name_env_elem)
  (high: Type0)
  (low: Type0)
  (r: rel low high)
: Tot (env' : impl_env (target_spec_env_extend _ high_env n s high) {
  impl_env_included env env' /\
  env'.i_low n == low /\
  env'.i_r n == r
})
= admit ()

let impl_rel_pure
    (t: Type)
    (x y: t)
: vprop
= pure (x == y)

let impl_rel_scalar_array
  (t: Type)
  (r: A.array t)
  (x: Seq.seq t)
: Tot vprop
= A.pts_to r x

let impl_rel_array_of_list
  (#low #high: Type)
  (r: rel low high)
  (x: A.array low)
  (y: list high)
: vprop
= exists* s . A.pts_to x s ** seq_list_match s y r

```pulse
ghost
fn rec seq_list_match_pure_elim
  (#t: Type0)
  (s: Seq.seq t)
  (l: list t)
requires
  seq_list_match s l (impl_rel_pure _)
ensures
  pure (s `Seq.equal` Seq.seq_of_list l)
decreases l
{
  seq_list_match_length  (impl_rel_pure t) s l;
  if (Nil? l) {
    seq_list_match_nil_elim s l (impl_rel_pure _)
  } else {
    let _ = seq_list_match_cons_elim s l (impl_rel_pure _);
    unfold (impl_rel_pure _ (Seq.head s) (List.Tot.hd l));
    seq_list_match_pure_elim (Seq.tail s) (List.Tot.tl l)
  }
}
```

```pulse
ghost
fn rec seq_list_match_pure_intro
  (#t: Type0)
  (s: Seq.seq t)
  (l: list t)
requires
  pure (s `Seq.equal` Seq.seq_of_list l)  
ensures
  seq_list_match s l (impl_rel_pure _)
decreases l
{
  if (Nil? l) {
    seq_list_match_nil_intro s l (impl_rel_pure _)
  } else {
    fold (impl_rel_pure _ (Seq.head s) (List.Tot.hd l));
    seq_list_match_pure_intro (Seq.tail s) (List.Tot.tl l);
    seq_list_match_cons_intro (Seq.head s) (List.Tot.hd l) (Seq.tail s) (List.Tot.tl l) (impl_rel_pure _);
    rewrite (seq_list_match 
      (Seq.head s `Seq.cons` Seq.tail s) (List.Tot.hd l :: List.Tot.tl l) (impl_rel_pure _)
    ) as (seq_list_match s l (impl_rel_pure _))
  }
}
```

let impl_rel_elem
    (t: target_elem_type)
: rel (impl_elem_type_sem t) (target_elem_type_sem t)
= match t with
  | TTSimple
  | TTUInt64
  | TTUnit
  | TTBool
  | TTAlwaysFalse -> impl_rel_pure _
  | TTString -> impl_rel_scalar_array U8.t
  | TTAny -> CP.raw_data_item_match 1.0R

let impl_rel_pair
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (xlow: (low1 & low2)) (xhigh: (high1 & high2))
: vprop
= r1 (fst xlow) (fst xhigh) ** r2 (snd xlow) (snd xhigh)

let impl_rel_either
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (xlow: (low1 `either` low2)) (xhigh: (high1 `either` high2))
: vprop
= match xlow, xhigh with
| Inl xl, Inl xh -> r1 xl xh
| Inr xl, Inr xh -> r2 xl xh
| _ -> pure False

let impl_rel_option
  (#low #high: Type)
  (r: low -> high -> vprop)
  (x: option low)
  (y: option high)
: vprop
= match x, y with
  | Some x', Some y' -> r x' y'
  | None, None -> emp
  | _ -> pure False

let rec impl_rel
    (#bound: name_env)
    (#high: target_spec_env bound)
    (env: impl_env high)
    (t: target_type {target_type_bounded bound t})
: rel (impl_type_sem env.i_low t) (target_type_sem high t)
= match t with
  | TTDef s -> env.i_r s
  | TTElem e -> impl_rel_elem e
  | TTPair t1 t2 -> impl_rel_pair (impl_rel env t1) (impl_rel env t2)
  | TTUnion t1 t2 -> impl_rel_either (impl_rel env t1) (impl_rel env t2)
  | TTArray a -> impl_rel_array_of_list (impl_rel env a)
  | TTTable t1 t2 -> impl_rel_array_of_list (impl_rel_pair (impl_rel env t1) (impl_rel env t2))
  | TTOption a -> impl_rel_option (impl_rel env a)

let impl_rel_incr
    (#bound: name_env)
    (#high: target_spec_env bound)
    (env: impl_env high)
    (#bound': name_env)
    (#high': target_spec_env bound')
    (env': impl_env high')
    (t: target_type {target_type_bounded bound t})
: Lemma
  (requires impl_env_included env env')
  (ensures
    impl_type_sem env.i_low t == impl_type_sem env'.i_low t /\
    target_type_sem  high t == target_type_sem high' t /\
     impl_rel env' t == coerce_eq () (impl_rel env t)
//    impl_rel env' t == impl_rel env t // FIXME: WHY WHY WHY?
  )
  [SMTPatOr [
    [SMTPat (impl_rel env t); SMTPat (impl_env_included env env')];
    [SMTPat (impl_rel env' t); SMTPat (impl_env_included env env')];
  ]]
= admit ()

let impl_rel_bij_l
  (#left #right: Type)
  (r: rel left right)
  (#left': Type)
  (bij: Spec.bijection left left')
: rel left' right
= fun
  (x: left')
  (y: right) ->
   r (bij.bij_to_from x) y

let impl_rel_bij_r
  (#left #right: Type)
  (r: rel left right)
  (#right': Type)
  (bij: Spec.bijection right right')
: rel left right'
= fun
  (x: left)
  (y: right')
->
 r x (bij.bij_to_from y)

inline_for_extraction [@@noextract_to "krml"]
noeq
type total_env = {
  te_ast: target_ast_env;
  te_spec: spec_env (te_ast.ta_ast.e_sem_env) (te_ast.ta_tgt);
  te_impl_typ: impl_env te_ast.ta_tgt;
(*
  te_impl_bij: (n: name te_ast.ta_ast.e_sem_env.se_bound) -> Spec.bijection
    (target_type_sem te_impl_typ.i_low (target_type_of_wf_ast_elem (te_ast.ta_ast.e_env n) (Some?.v (te_ast.ta_ast.e_wf n))))
    (te_impl_typ.i_low n);
*)
  te_impl_validate: (n: typ_name te_ast.ta_ast.e_sem_env.se_bound) ->
    CP.impl_typ #None (te_ast.ta_ast.e_sem_env.se_env n);
  te_impl_parse: (n: typ_name te_ast.ta_ast.e_sem_env.se_bound) ->
    CP.impl_parse
      (te_spec.tp_spec_typ n).parser
      (te_impl_typ.i_r n)
     ;
  te_impl_serialize: (n: typ_name te_ast.ta_ast.e_sem_env.se_bound) ->
    CP.impl_serialize
      (te_spec.tp_spec_typ n).serializer
      (te_impl_typ.i_r n)
     ;
}

[@@"opaque_to_smt"; noextract_to "krml"] irreducible noextract
let empty_impl_validate (n: typ_name empty_name_env) : CP.impl_typ #None (empty_sem_env.se_env n) =
  false_elim ()

[@@"opaque_to_smt"; noextract_to "krml"] irreducible noextract
let empty_impl_parse (env: target_spec_env empty_name_env) (n: typ_name empty_name_env) : CP.impl_parse
  ((empty_spec_env env).tp_spec_typ n).parser
  ((empty_impl_env _).i_r n)
= false_elim ()

[@@"opaque_to_smt"; noextract_to "krml"] irreducible noextract
let empty_impl_serialize (env: target_spec_env empty_name_env) (n: typ_name empty_name_env) : CP.impl_serialize
  ((empty_spec_env env).tp_spec_typ n).serializer
  ((empty_impl_env _).i_r n)
= false_elim ()

let empty_total_env = {
  te_ast = empty_target_ast_env;
  te_spec = empty_spec_env _;
  te_impl_typ = empty_impl_env _;
  te_impl_validate = empty_impl_validate;
  te_impl_parse = empty_impl_parse _;
  te_impl_serialize = empty_impl_serialize _;
}

assume val gen_impl_validate
  (env: total_env)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    spec_wf_typ env.te_ast.ta_ast.e_sem_env t t_wf
  })
: CP.impl_typ #None (typ_sem env.te_ast.ta_ast.e_sem_env t)

assume val gen_impl_parse
  (env: total_env)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    spec_wf_typ env.te_ast.ta_ast.e_sem_env t t_wf
  })
  (high: Type0)
  (bij_high: Spec.bijection (target_type_sem env.te_ast.ta_tgt (target_type_of_wf_typ t_wf)) high)
  (low: Type0)
  (bij_low: Spec.bijection (impl_type_sem env.te_impl_typ.i_low (target_type_of_wf_typ t_wf)) low)
: CP.impl_parse
    (Spec.spec_bij
      (spec_of_wf_typ env.te_spec t_wf)
      bij_high
    ).parser
    (impl_rel_bij_l
      (impl_rel_bij_r
        (impl_rel env.te_impl_typ (target_type_of_wf_typ t_wf))
        bij_high
      )
      bij_low
    )

assume val gen_impl_serialize
  (env: total_env)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    spec_wf_typ env.te_ast.ta_ast.e_sem_env t t_wf
  })
  (high: Type0)
  (bij_high: Spec.bijection (target_type_sem env.te_ast.ta_tgt (target_type_of_wf_typ t_wf)) high)
  (low: Type0)
  (bij_low: Spec.bijection (impl_type_sem env.te_impl_typ.i_low (target_type_of_wf_typ t_wf)) low)
: CP.impl_serialize
    (Spec.spec_bij
      (spec_of_wf_typ env.te_spec t_wf)
      bij_high
    ).serializer
    (impl_rel_bij_l
      (impl_rel_bij_r
        (impl_rel env.te_impl_typ (target_type_of_wf_typ t_wf))
        bij_high
      )
      bij_low
    )

inline_for_extraction
let inline_coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

#push-options "--z3rlimit 16"

#restart-solver
inline_for_extraction
let total_env_extend_typ
  (env: total_env)
  (new_name: string)
  (t: typ)
  (t_wf: ast0_wf_typ t {
    wf_ast_env_extend_typ_with_weak_pre env.te_ast.ta_ast new_name t t_wf
  })
  (high: Type0)
  (bij_high: Spec.bijection (target_type_sem env.te_ast.ta_tgt (target_type_of_wf_typ t_wf)) high)
  (low: Type0)
  (bij_low: Spec.bijection (impl_type_sem env.te_impl_typ.i_low (target_type_of_wf_typ t_wf)) low)
: Tot (env' : total_env {
  env'.te_ast == target_ast_env_extend_typ env.te_ast new_name t t_wf high bij_high /\
  env'.te_spec == spec_env_extend_typ env.te_ast.ta_ast new_name t t_wf env.te_spec high bij_high /\
  env'.te_impl_typ == impl_env_extend env.te_impl_typ new_name NType high low
    (impl_rel_bij_l
      (impl_rel_bij_r
        (impl_rel env.te_impl_typ (target_type_of_wf_typ t_wf))
        bij_high
      )
      bij_low
    )
})
= {
  te_ast = target_ast_env_extend_typ env.te_ast new_name t t_wf high bij_high;
  te_spec = spec_env_extend_typ env.te_ast.ta_ast new_name t t_wf env.te_spec high bij_high;
  te_impl_typ = impl_env_extend env.te_impl_typ new_name NType high low
    (impl_rel_bij_l
      (impl_rel_bij_r
        (impl_rel env.te_impl_typ (target_type_of_wf_typ t_wf))
        bij_high
      )
      bij_low
    );
  te_impl_validate = (fun n -> if n = new_name then gen_impl_validate env t t_wf else inline_coerce_eq () (env.te_impl_validate n));
  te_impl_parse = (fun n -> if n = new_name then gen_impl_parse env t t_wf _ bij_high _ bij_low else inline_coerce_eq () (env.te_impl_parse n));
  te_impl_serialize = (fun n -> if n = new_name then gen_impl_serialize env t t_wf _ bij_high _ bij_low else inline_coerce_eq () (env.te_impl_serialize n));
}

#pop-options

inline_for_extraction
let total_env_replace
  (env: total_env)
  (n: string)
  (_: squash (env.te_ast.ta_ast.e_sem_env.se_bound n == Some NType))
  (validate: CP.impl_typ #None (env.te_ast.ta_ast.e_sem_env.se_env n))
  (parse:
    CP.impl_parse
      (env.te_spec.tp_spec_typ n).parser
      (env.te_impl_typ.i_r n)
  )
  (serialize:
    CP.impl_serialize
      (env.te_spec.tp_spec_typ n).serializer
      (env.te_impl_typ.i_r n)
  )
: Tot total_env
= {
  env with
  te_impl_validate = (fun n' -> if n' = n then inline_coerce_eq () validate else inline_coerce_eq () (env.te_impl_validate n'));
  te_impl_parse = (fun n' -> if n' = n then inline_coerce_eq () parse else inline_coerce_eq () (env.te_impl_parse n'));
  te_impl_serialize = (fun n' -> if n' = n then serialize else inline_coerce_eq () (env.te_impl_serialize n'));
}

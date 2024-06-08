(*
   Copyright 2023 Microsoft Research

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

module CBOR.Spec.Type
include CBOR.Spec.Constants

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* The generic data model *)

let u0 = CBOR.Spec.FiniteMap.UniverseToken u#0

noextract
noeq
type cbor_case (t: Type u#a) : Type u#(max a 1) =
  | CSimple: (v: simple_value) -> cbor_case t
  | CInt64: (typ: major_type_uint64_or_neg_int64) -> (v: U64.t) -> cbor_case t
  | CString: (typ: major_type_byte_string_or_text_string) -> (v: Seq.seq U8.t { FStar.UInt.fits (Seq.length v) U64.n }) -> cbor_case t // Section 3.1: "a string containing an invalid UTF-8 sequence is well-formed but invalid", so we don't care about UTF-8 specifics here.
  | CArray: (v: list t { FStar.UInt.fits (List.Tot.length v) U64.n }) -> cbor_case t
  | CMap: (c: CBOR.Spec.FiniteMap.fmap t t u0 { FStar.UInt.fits (CBOR.Spec.FiniteMap.length c) U64.n }) -> cbor_case t
  | CTagged: (tag: U64.t) -> (v: t) -> cbor_case t

let rec list_eq
  (#t: Type)
  (eq: CBOR.Spec.FiniteMap.eq_test t)
  (l1 l2: list t)
: Tot (CBOR.Spec.FiniteMap.eq_elem_test_codom l1 l2)
  (decreases l1)
= match l1, l2 with
  | [], [] -> true
  | x1 :: l1', x2 :: l2' -> eq x1 x2 && list_eq eq l1' l2'
  | _ -> false

let rec seq_eq
  (#t: Type)
  (eq: CBOR.Spec.FiniteMap.eq_test t)
  (l1 l2: Seq.seq t)
: Tot (CBOR.Spec.FiniteMap.eq_elem_test_codom l1 l2)
  (decreases (Seq.length l1))
= if Seq.length l1 = 0
  then
    if Seq.length l2 = 0
    then begin
      assert (l1 `Seq.equal` l2);
      true
    end
    else false
  else if Seq.length l2 = 0
  then false
  else begin
    Seq.cons_head_tail l1;
    Seq.cons_head_tail l2;
    eq (Seq.head l1) (Seq.head l2) && seq_eq eq (Seq.tail l1) (Seq.tail l2)
  end

let cbor_case_eq
  (#t: Type)
  (eq: CBOR.Spec.FiniteMap.eq_test t)
: Tot (CBOR.Spec.FiniteMap.eq_test (cbor_case t))
= fun c1 c2 -> match c1, c2 with
  | CSimple v1, CSimple v2 -> v1 = v2
  | CInt64 t1 v1, CInt64 t2 v2 -> t1 = t2 && v1 = v2
  | CString t1 s1, CString t2 s2 -> t1 = t2 && seq_eq (fun x y -> x = y) s1 s2
  | CArray l1, CArray l2 -> list_eq eq l1 l2
  | CMap l1, CMap l2 -> CBOR.Spec.FiniteMap.fmap_eq l1 l2
  | CTagged tag1 x1, CTagged tag2 x2 -> tag1 = tag2 && eq x1 x2
  | _ -> false

let rec list_bound
  (#t: Type)
  (bound: t -> Tot nat)
  (l: list t)
: Tot nat
= match l with
  | [] -> 0
  | a :: q ->
    let ba = bound a in
    let bq = list_bound bound q in
    if ba >= bq then ba else bq

let fmap_bound_op
  (#t: Type)
  (s: CBOR.Spec.FiniteMap.fmap t t u0)
  (bound: t -> Tot nat)
  (accu: nat)
  (x: t)
: Tot nat
= let bx = bound x in
  let accu1 = if bx > accu then bx else accu in
  let bw = match CBOR.Spec.FiniteMap.get x s with
  | None -> 0
  | Some w -> bound w
  in
  if bw > accu1 then bw else accu1

let fmap_bound
  (#t: Type)
  (bound: t -> Tot nat)
  (s: CBOR.Spec.FiniteMap.fmap t t u0)
: Tot nat
= CBOR.Spec.FiniteMap.fold (fmap_bound_op s bound) 0 s

let cbor_case_bound
  (#t: Type)
  (bound: t -> nat)
  (x: cbor_case t)
: Tot nat
= match x with
  | CArray l -> 1 + list_bound bound l
  | CMap l -> 1 + fmap_bound bound l
  | CTagged _ x -> 1 + bound x
  | _ -> 0

[@@erasable] noeq type empty_t : Type u#a =

noextract [@@noextract_to "krml"]
let empty_elim (#t: Type u#b) (x: empty_t u#a) : Tot t =
  match empty_t with

let rec cbor1 (b: nat) : Tot (Type u#1)
  (decreases (b + b + 1))
= cbor_case (cbor2 b)

and cbor2 (b: nat) : Tot (Type u#1)
  (decreases (b + b))
= (if b = 0 then empty_t else cbor1 (b - 1))

let rec cbor1_bound (b: nat) : Tot (cbor1 b -> nat) (decreases (b + b + 1))
= cbor_case_bound (cbor2_bound b)

and cbor2_bound (b: nat) : Tot (cbor2 b -> nat) (decreases (b + b))
= if b = 0 then empty_elim #nat else cbor1_bound (b - 1)

noeq
type cbor = {
  b: nat;
  obj: (obj: cbor1 b { cbor1_bound b obj == b });
}

let cbor_bound (x: cbor) : Tot nat = x.b

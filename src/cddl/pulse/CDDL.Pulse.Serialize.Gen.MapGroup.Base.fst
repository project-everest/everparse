module CDDL.Pulse.Serialize.Gen.MapGroup.Base
include CDDL.Pulse.Serialize.Gen.Base
include CDDL.Pulse.Parse.MapGroup
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest

let bare_cbor_map_parser = (n: nat) -> (x: Seq.seq U8.t) -> Pure (option (Cbor.cbor_map & nat))
  (True)
  (fun res -> match res with
  | None -> True
  | Some (m, len) -> Cbor.cbor_map_length m == n /\
    len <= Seq.length x
  )

let cbor_parse_map_prefix_prop'
  (p: bare_cbor_map_parser)
  (count: nat)
  (x y: Seq.seq U8.t)
: Tot prop
= match p count x with
  | Some (_, n) -> (Seq.length y >= n /\ Seq.slice x 0 n == Seq.slice y 0 n) ==> p count x == p count y
  | _ -> True

let cbor_parse_map_prefix_prop
  (p: bare_cbor_map_parser)
: Tot prop
= forall n x y . cbor_parse_map_prefix_prop' p n x y

let cbor_map_min_length_op
  (f: cbor -> nat)
  (m: cbor_map)
  (accu: nat)
  (x: cbor)
: Tot nat
= match cbor_map_get m x with
  | None -> accu
  | Some y -> accu + f x + f y

let cbor_map_min_length
  (f: cbor -> nat)
  (m: cbor_map)
: Tot nat
= cbor_map_fold (cbor_map_min_length_op f m) 0 m

let cbor_map_min_length_empty
  (f: cbor -> nat)
: Lemma
  (cbor_map_min_length f cbor_map_empty == 0)
= cbor_map_fold_empty (cbor_map_min_length_op f cbor_map_empty) 0

let cbor_map_min_length_singleton
  (f: cbor -> nat)
  (x y: cbor)
: Lemma
  (cbor_map_min_length f (cbor_map_singleton x y) == f x + f y)
= cbor_map_fold_singleton (cbor_map_min_length_op f (cbor_map_singleton x y)) 0 x y

let cbor_map_fold_singleton_forall
  (#a: Type)
  (f: a -> cbor -> a {
    CBOR.Spec.Util.op_comm f
  })
  (key value: cbor)
: Lemma
  (forall x . cbor_map_fold f x (cbor_map_singleton key value) == f x key)
= Classical.forall_intro (fun x -> cbor_map_fold_singleton f x key value)

let cbor_map_fold_union_forall
  (#a: Type)
  (f: a -> cbor -> a {
    CBOR.Spec.Util.op_comm f
  })
  (m1: cbor_map)
  (m2: cbor_map {
    cbor_map_disjoint m1 m2
  })
: Lemma
  (ensures (forall x .
    cbor_map_fold f x (cbor_map_union m1 m2) ==
      cbor_map_fold f (cbor_map_fold f x m1) m2
  ))
= Classical.forall_intro (fun x -> Classical.move_requires (cbor_map_fold_union f x m1) m2)

let cbor_map_fold_min_length_accu
  (f: cbor -> nat)
  (m1 m2: cbor_map)
: Lemma
  (forall a . cbor_map_fold (cbor_map_min_length_op f m1) a m2 == a + cbor_map_fold (cbor_map_min_length_op f m1) 0 m2)
= cbor_map_ind
    (fun m -> forall a . cbor_map_fold (cbor_map_min_length_op f m1) a m == a + cbor_map_fold (cbor_map_min_length_op f m1) 0 m)
    (Classical.forall_intro (cbor_map_fold_empty (cbor_map_min_length_op f m1)))
    (fun m' x y ->
      let ms = cbor_map_singleton x y in
      let m = cbor_map_union m' ms in
      let prf
        (a: nat)
      : Lemma
        (cbor_map_fold (cbor_map_min_length_op f m1) a m == a + cbor_map_fold (cbor_map_min_length_op f m1) 0 m)
      =
        cbor_map_fold_union (cbor_map_min_length_op f m1) a m' ms;
        cbor_map_fold_union (cbor_map_min_length_op f m1) 0 m' ms;
        cbor_map_fold_singleton (cbor_map_min_length_op f m1) (cbor_map_fold (cbor_map_min_length_op f m1) a m') x y;
        cbor_map_fold_singleton (cbor_map_min_length_op f m1) (cbor_map_fold (cbor_map_min_length_op f m1) 0 m') x y;
        ()
      in
      Classical.forall_intro prf
    )
    m2

let cbor_map_min_length_union
  (f: cbor -> nat)
  (m1 m2: cbor_map)
: Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures cbor_map_min_length f (cbor_map_union m1 m2) == cbor_map_min_length f m1 + cbor_map_min_length f m2)
= let m = cbor_map_union m1 m2 in
  cbor_map_fold_union (cbor_map_min_length_op f m) 0 m1 m2;
  cbor_map_fold_min_length_accu f m m2;
  cbor_map_fold_ext (cbor_map_min_length_op f m) (cbor_map_min_length_op f m1) 0 m1 m1;
  cbor_map_fold_ext (cbor_map_min_length_op f m) (cbor_map_min_length_op f m2) 0 m2 m2;
  ()

let cbor_map_min_length_prop'
  (p: bare_cbor_map_parser)
  (f: cbor -> nat)
  (n: nat)
  (s: Seq.seq U8.t)
: Tot prop
= match p n s with
  | None -> True
  | Some (res, len) -> len >= cbor_map_min_length f res

let cbor_map_min_length_prop
  (p: bare_cbor_map_parser)
  (f: cbor -> nat)
: Tot prop
= forall n s . cbor_map_min_length_prop' p f n s

let cbor_map_det_min_length_eq
  (m: cbor_map)
: Lemma
  (Seq.length (Cbor.cbor_det_serialize_map m) == cbor_map_min_length cbor_det_min_length m)
= cbor_map_ind
    (fun m -> Seq.length (Cbor.cbor_det_serialize_map m) == cbor_map_min_length cbor_det_min_length m)
    (
      Cbor.cbor_det_serialize_map_empty ();
      cbor_map_min_length_empty cbor_det_min_length;
      ()
    )
    (fun m' x y -> 
      Cbor.cbor_det_serialize_map_singleton x y;
      Cbor.cbor_det_serialize_map_append_length m' (cbor_map_singleton x y);
      cbor_map_min_length_singleton cbor_det_min_length x y;
      cbor_map_min_length_union cbor_det_min_length m' (cbor_map_singleton x y);
      ()
    )
    m

let cbor_map_det_min_length_prop
  (n: nat)
  (s: Seq.seq U8.t)
: Lemma
  (ensures cbor_map_min_length_prop' Cbor.cbor_det_parse_map cbor_det_min_length n s)
  [SMTPat (cbor_map_min_length_prop' Cbor.cbor_det_parse_map cbor_det_min_length n s)]
= match Cbor.cbor_det_parse_map n s with
  | None -> ()
  | Some (m, len) ->
    Cbor.cbor_det_parse_map_equiv n s m len;
    cbor_map_det_min_length_eq m

let cbor_map_max_length_op
  (f: cbor -> option nat)
  (m: cbor_map)
  (accu: option nat)
  (x: cbor)
: Tot (option nat)
= match accu with
  | None -> None
  | Some accu' ->
    match cbor_map_get m x with
    | None -> accu
    | Some y ->
      match f x with
      | None -> None
      | Some fx ->
        match f y with
        | None -> None
        | Some fy -> Some (accu' + fx + fy)

let cbor_map_max_length
  (f: cbor -> option nat)
  (m: cbor_map)
: Tot (option nat)
= cbor_map_fold (cbor_map_max_length_op f m) (Some 0) m

let cbor_map_max_length_empty
  (f: cbor -> option nat)
: Lemma
  (cbor_map_max_length f cbor_map_empty == Some 0)
= cbor_map_fold_empty (cbor_map_max_length_op f cbor_map_empty) (Some 0)

let cbor_map_max_length_singleton
  (f: cbor -> option nat)
  (x y: cbor)
: Lemma
  (cbor_map_max_length f (cbor_map_singleton x y) == begin match f x, f y with
  | Some fx, Some fy -> Some (fx + fy)
  | _ -> None
  end)
= cbor_map_fold_singleton (cbor_map_max_length_op f (cbor_map_singleton x y)) (Some 0) x y

let cbor_map_fold_max_length_accu_prop'
  (f: cbor -> option nat)
  (m1 m2: cbor_map)
  (a: option nat)
: Tot prop
= cbor_map_fold (cbor_map_max_length_op f m1) a m2 ==
    begin match a with
    | None -> None
    | Some a' ->
      match cbor_map_fold (cbor_map_max_length_op f m1) (Some 0) m2 with
      | None -> None
      | Some y -> Some (a' + y)
    end

#restart-solver

let cbor_map_fold_max_length_accu
  (f: cbor -> option nat)
  (m1 m2: cbor_map)
: Lemma
  (forall (a: option nat) . cbor_map_fold_max_length_accu_prop' f m1 m2 a)
= cbor_map_ind
    (fun m ->
      forall (a: option nat) . cbor_map_fold_max_length_accu_prop' f m1 m a
    )
    (
      Classical.forall_intro (cbor_map_fold_empty (cbor_map_max_length_op f m1))
    )
    (fun m' x y ->
      cbor_map_fold_singleton_forall (cbor_map_max_length_op f m1) x y;
      cbor_map_fold_union_forall (cbor_map_max_length_op f m1) m' (cbor_map_singleton x y);
      ()
    )
    m2

let cbor_map_max_length_union
  (f: cbor -> option nat)
  (m1 m2: cbor_map)
: Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures cbor_map_max_length f (cbor_map_union m1 m2) == begin match cbor_map_max_length f m1, cbor_map_max_length f m2 with
  | Some fm1, Some fm2 -> Some (fm1 + fm2)
  | _ -> None
  end)
= let m = cbor_map_union m1 m2 in
  cbor_map_fold_union (cbor_map_max_length_op f m) (Some 0) m1 m2;
  cbor_map_fold_max_length_accu f m m2;
  cbor_map_fold_ext (cbor_map_max_length_op f m) (cbor_map_max_length_op f m1) (Some 0) m1 m1;
  cbor_map_fold_ext (cbor_map_max_length_op f m) (cbor_map_max_length_op f m2) (Some 0) m2 m2;
  ()

let cbor_map_max_length_prop'
  (p: bare_cbor_map_parser)
  (f: cbor -> option nat)
  (n: nat)
  (s: Seq.seq U8.t)
: Tot prop
= match p n s with
  | None -> True
  | Some (res, len) ->
    match cbor_map_max_length f res with
    | None -> True
    | Some maxlen -> len <= maxlen

let cbor_map_max_length_prop
  (p: bare_cbor_map_parser)
  (f: cbor -> option nat)
: Tot prop
= forall n s . cbor_map_max_length_prop' p f n s

let cbor_map_det_max_length_eq
  (m: cbor_map)
: Lemma
  (Some (Seq.length (Cbor.cbor_det_serialize_map m)) == cbor_map_max_length cbor_det_max_length m)
= cbor_map_ind
    (fun m -> Some (Seq.length (Cbor.cbor_det_serialize_map m)) == cbor_map_max_length cbor_det_max_length m)
    (
      Cbor.cbor_det_serialize_map_empty ();
      cbor_map_max_length_empty cbor_det_max_length;
      ()
    )
    (fun m' x y -> 
      Cbor.cbor_det_serialize_map_singleton x y;
      Cbor.cbor_det_serialize_map_append_length m' (cbor_map_singleton x y);
      cbor_map_max_length_singleton cbor_det_max_length x y;
      cbor_map_max_length_union cbor_det_max_length m' (cbor_map_singleton x y);
      ()
    )
    m

let cbor_map_det_max_length_prop
  (n: nat)
  (s: Seq.seq U8.t)
: Lemma
  (ensures cbor_map_max_length_prop' Cbor.cbor_det_parse_map cbor_det_max_length n s)
  [SMTPat (cbor_map_max_length_prop' Cbor.cbor_det_parse_map cbor_det_max_length n s)]
= match Cbor.cbor_det_parse_map n s with
  | None -> ()
  | Some (m, len) ->
    Cbor.cbor_det_parse_map_equiv n s m len;
    cbor_map_det_max_length_eq m

let cbor_map_parser
  (minl: cbor -> nat)
  (maxl: cbor -> option nat)
= (p: bare_cbor_map_parser { 
    cbor_parse_map_prefix_prop p /\
    cbor_map_min_length_prop p minl /\
    cbor_map_max_length_prop p maxl
  })

let cbor_det_parse_map : cbor_map_parser cbor_det_min_length cbor_det_max_length =
  Classical.forall_intro_3 (Cbor.cbor_det_parse_map_prefix);
  Cbor.cbor_det_parse_map

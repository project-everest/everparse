module ASN1.Pulse.RelShare
#lang-pulse

(* Sharing and gathering the permission of `asn1_rel` (`share_t`, `gather_t`),
   as needed by the mixed-list iterator, hence by the SEQUENCE OF / SET OF
   writers. Gathering also proves that the relation is functional, from the
   injectivity of the content encoders (`leaf_enc_inj`, `asn1_value_enc_inj`).
   ANY DEFINED BY keys must be comparable with a literal
   (`adb_key_supported`). *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module I64 = FStar.Int64
module SB = LowParse.Spec.Base
module PB = LowParse.PulseParse.Base
module It = LowParse.PulseParse.Iterator
module PS = ASN1.Pulse.ParseSequence
module PC = ASN1.Pulse.ParseChoice
module PA = ASN1.Pulse.ParseAdb
module AL = ASN1.Pulse.ParseAdb.Lemmas
module T = FStar.Tactics

(* The schemas supported by the writers: those of the parsers *)

[@@ASN1.Pulse.Interpreter.asn1_pulse_attr]
let rec wsupported_content (k: asn1_content_k) : Tot bool (decreases k) =
  match k with
  | ASN1_TERMINAL _ -> true
  | ASN1_RESTRICTED_TERMINAL _ _ -> true
  | ASN1_PREFIXED k' -> wsupported_k k'
  | ASN1_SEQUENCE gitems -> wsupported_items (dsnd gitems)
  | ASN1_SEQUENCE_OF _ k' -> wsupported_k k'
  | ASN1_SET_OF _ k' -> wsupported_k k'
  | ASN1_SET _ items _ -> wsupported_items items && ASN1.Pulse.ParseSet.items_canon items
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    wsupported_items prefix && ASN1.Pulse.Interpreter.adb_key_supported key_k && wsupported_ls ls &&
    (match ofb with None -> true | Some fb -> wsupported_items (dsnd fb))

and wsupported_ls (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : Tot bool (decreases ls) =
  match ls with
  | [] -> true
  | (_, y) :: tl -> wsupported_items (dsnd y) && wsupported_ls tl

and wsupported_items (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> wsupported_dec dk && wsupported_items tl

and wsupported_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot bool (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> wsupported_k k
  | ASN1_OPTION_ILC k -> wsupported_k k
  | _ -> true

and wsupported_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot bool (decreases lc) =
  match lc with
  | [] -> true
  | (_, c) :: tl -> wsupported_content c && wsupported_lc tl

and wsupported_k (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC _ k' -> wsupported_content k'
  | ASN1_CHOICE_ILC lc _ -> wsupported_lc lc
  | ASN1_ANY_ILC -> true

(* Generic combinators *)

inline_for_extraction
let share_t (#t: Type0) (#u: Type0) (r: prel t u) : Type = PB.share_t #t #u r
inline_for_extraction
let gather_t (#t: Type0) (#u: Type0) (r: prel t u) : Type = PB.gather_t #t #u r

let prel_equiv (#t: Type0) (#u: Type0) (r1 r2: prel t u) : prop =
  forall pm x y . r1 pm x y == r2 pm x y

ghost
fn share_ext (#t: Type0) (#u: Type0) (r1: prel t u) (r2: prel t u) (sq: squash (prel_equiv r1 r2)) (sh: share_t r1)
: share_t #t #u r2
= (x: t) (#p: perm) (#y: u)
{
  rewrite (r2 p x y) as (r1 p x y);
  sh x #p #y;
  rewrite (r1 (p /. 2.0R) x y ** r1 (p /. 2.0R) x y) as (r2 (p /. 2.0R) x y ** r2 (p /. 2.0R) x y)
}

ghost
fn gather_ext (#t: Type0) (#u: Type0) (r1: prel t u) (r2: prel t u) (sq: squash (prel_equiv r1 r2)) (g: gather_t r1)
: gather_t #t #u r2
= (x: t) (#p: perm) (#y: u) (#p': perm) (#y': u)
{
  rewrite (r2 p x y ** r2 p' x y') as (r1 p x y ** r1 p' x y');
  g x #p #y #p' #y';
  rewrite (r1 (p +. p') x y) as (r2 (p +. p') x y)
}

ghost
fn share_eq (t: eqtype)
: share_t #t #t (prel_eq t)
= (x: t) (#p: perm) (#y: t)
{
  unfold (prel_eq t p x y);
  fold (prel_eq t (p /. 2.0R) x y);
  fold (prel_eq t (p /. 2.0R) x y)
}

ghost
fn gather_eq (t: eqtype)
: gather_t #t #t (prel_eq t)
= (x: t) (#p: perm) (#y: t) (#p': perm) (#y': t)
{
  unfold (prel_eq t p x y);
  unfold (prel_eq t p' x y');
  fold (prel_eq t (p +. p') x y)
}

ghost
fn share_emp_unit (_: unit)
: share_t #unit #unit (prel_emp unit unit)
= (x: unit) (#p: perm) (#y: unit)
{
  unfold (prel_emp unit unit p x y);
  fold (prel_emp unit unit (p /. 2.0R) x y);
  fold (prel_emp unit unit (p /. 2.0R) x y)
}

ghost
fn gather_emp_unit (_: unit)
: gather_t #unit #unit (prel_emp unit unit)
= (x: unit) (#p: perm) (#y: unit) (#p': perm) (#y': unit)
{
  unfold (prel_emp unit unit p x y);
  unfold (prel_emp unit unit p' x y');
  fold (prel_emp unit unit (p +. p') x y)
}

ghost
fn share_slice_ser (#u: Type0) (enc: u -> GTot SB.bytes)
: share_t #(S.slice U8.t) #u (prel_slice_ser enc)
= (x: S.slice U8.t) (#p: perm) (#y: u)
{
  unfold (prel_slice_ser enc p x y);
  S.share x;
  fold (prel_slice_ser enc (p /. 2.0R) x y);
  fold (prel_slice_ser enc (p /. 2.0R) x y)
}

let enc_injective (#u: Type0) (enc: u -> GTot SB.bytes) : prop =
  forall (y1 y2: u) . enc y1 == enc y2 ==> y1 == y2

ghost
fn gather_slice_ser (#u: Type0) (enc: u -> GTot SB.bytes) (inj: squash (enc_injective enc))
: gather_t #(S.slice U8.t) #u (prel_slice_ser enc)
= (x: S.slice U8.t) (#p: perm) (#y: u) (#p': perm) (#y': u)
{
  unfold (prel_slice_ser enc p x y);
  unfold (prel_slice_ser enc p' x y');
  S.gather x;
  fold (prel_slice_ser enc (p +. p') x y)
}

let leaf_enc_injective (k: leaf_k) : squash (enc_injective (leaf_enc k)) =
  Classical.forall_intro_2 (fun y1 y2 -> Classical.move_requires (leaf_enc_inj k y1) y2)

let value_enc_injective () : squash (enc_injective asn1_value_enc) =
  Classical.forall_intro_2 (fun y1 y2 -> Classical.move_requires (asn1_value_enc_inj y1) y2)

ghost
fn share_small_int (bound: pos)
: share_t #I64.t #(asn1_integer_t bound) (asn1_small_int_rel bound)
= (x: I64.t) (#p: perm) (#y: asn1_integer_t bound)
{
  unfold (asn1_small_int_rel bound p x y);
  fold (asn1_small_int_rel bound (p /. 2.0R) x y);
  fold (asn1_small_int_rel bound (p /. 2.0R) x y)
}

ghost
fn gather_small_int (bound: pos)
: gather_t #I64.t #(asn1_integer_t bound) (asn1_small_int_rel bound)
= (x: I64.t) (#p: perm) (#y: asn1_integer_t bound) (#p': perm) (#y': asn1_integer_t bound)
{
  unfold (asn1_small_int_rel bound p x y);
  unfold (asn1_small_int_rel bound p' x y');
  fold (asn1_small_int_rel bound (p +. p') x y)
}

ghost
fn share_int (bound: pos)
: share_t #asn1_int_impl #(asn1_integer_t bound) (asn1_int_rel bound)
= (x: asn1_int_impl) (#p: perm) (#y: asn1_integer_t bound)
{
  match x {
    Small i -> {
      rewrite (asn1_int_rel bound p x y) as (pure (I64.v i == y));
      rewrite (pure (I64.v i == y)) as (asn1_int_rel bound (p /. 2.0R) x y);
      rewrite (pure (I64.v i == y)) as (asn1_int_rel bound (p /. 2.0R) x y);
      ()
    }
    Big s -> {
      rewrite (asn1_int_rel bound p x y) as (prel_slice_ser (integer_enc bound) p s y ** pure (~ (fits_i64 y)));
      share_slice_ser (integer_enc bound) s #p #y;
      rewrite (prel_slice_ser (integer_enc bound) (p /. 2.0R) s y ** pure (~ (fits_i64 y))) as (asn1_int_rel bound (p /. 2.0R) x y);
      rewrite (prel_slice_ser (integer_enc bound) (p /. 2.0R) s y ** pure (~ (fits_i64 y))) as (asn1_int_rel bound (p /. 2.0R) x y);
      ()
    }
  }
}

ghost
fn gather_int (bound: pos)
: gather_t #asn1_int_impl #(asn1_integer_t bound) (asn1_int_rel bound)
= (x: asn1_int_impl) (#p: perm) (#y: asn1_integer_t bound) (#p': perm) (#y': asn1_integer_t bound)
{
  match x {
    Small i -> {
      rewrite (asn1_int_rel bound p x y) as (pure (I64.v i == y));
      rewrite (asn1_int_rel bound p' x y') as (pure (I64.v i == y'));
      rewrite (pure (I64.v i == y)) as (asn1_int_rel bound (p +. p') x y);
      ()
    }
    Big s -> {
      rewrite (asn1_int_rel bound p x y) as (prel_slice_ser (integer_enc bound) p s y ** pure (~ (fits_i64 y)));
      rewrite (asn1_int_rel bound p' x y') as (prel_slice_ser (integer_enc bound) p' s y' ** pure (~ (fits_i64 y')));
      leaf_enc_injective (ASN1_INTEGER bound);
      gather_slice_ser (integer_enc bound) () s #p #y #p' #y';
      rewrite (prel_slice_ser (integer_enc bound) (p +. p') s y ** pure (~ (fits_i64 y))) as (asn1_int_rel bound (p +. p') x y);
      ()
    }
  }
}

ghost
fn share_bitstring (_: unit)
: share_t #asn1_bitstring_impl #asn1_bitstring_t asn1_bitstring_rel
= (x: asn1_bitstring_impl) (#p: perm) (#y: asn1_bitstring_t)
{
  unfold (asn1_bitstring_rel p x y);
  S.share x.bytes;
  fold (asn1_bitstring_rel (p /. 2.0R) x y);
  fold (asn1_bitstring_rel (p /. 2.0R) x y)
}

ghost
fn gather_bitstring (_: unit)
: gather_t #asn1_bitstring_impl #asn1_bitstring_t asn1_bitstring_rel
= (x: asn1_bitstring_impl) (#p: perm) (#y: asn1_bitstring_t) (#p': perm) (#y': asn1_bitstring_t)
{
  unfold (asn1_bitstring_rel p x y);
  unfold (asn1_bitstring_rel p' x y');
  S.gather x.bytes;
  fold (asn1_bitstring_rel (p +. p') x y)
}

let prel_default (#t: Type0) (#u: eqtype) (r: prel t u) (defv: u) (pm: perm) (x: option t) (y: default_tv defv) : slprop =
  match x, y with
  | None, Default -> emp
  | Some a, Nondefault b -> r pm a b
  | _ -> pure False

ghost
fn share_option (#t: Type0) (#u: Type0) (r: prel t u) (sh: share_t r)
: share_t #(option t) #(option u) (prel_option r)
= (x: option t) (#p: perm) (#y: option u)
{
  match x {
    None -> {
      match y {
        None -> {
          rewrite (prel_option r p x y) as emp;
          rewrite emp as (prel_option r (p /. 2.0R) x y);
          rewrite emp as (prel_option r (p /. 2.0R) x y);
        }
        Some b -> {
          rewrite (prel_option r p x y) as pure False;
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        None -> {
          rewrite (prel_option r p x y) as pure False;
          unreachable ()
        }
        Some b -> {
          rewrite (prel_option r p x y) as (r p a b);
          sh a #p #b;
          rewrite (r (p /. 2.0R) a b) as (prel_option r (p /. 2.0R) x y);
          rewrite (r (p /. 2.0R) a b) as (prel_option r (p /. 2.0R) x y);
        }
      }
    }
  }
}

ghost
fn gather_option (#t: Type0) (#u: Type0) (r: prel t u) (g: gather_t r)
: gather_t #(option t) #(option u) (prel_option r)
= (x: option t) (#p: perm) (#y: option u) (#p': perm) (#y': option u)
{
  match x {
    None -> {
      match y {
        None -> {
          match y' {
            None -> {
              rewrite (prel_option r p x y) as emp;
              rewrite (prel_option r p' x y') as emp;
              rewrite emp as (prel_option r (p +. p') x y);
            }
            Some _ -> {
              rewrite (prel_option r p' x y') as pure False;
              unreachable ()
            }
          }
        }
        Some _ -> {
          rewrite (prel_option r p x y) as pure False;
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        None -> {
          rewrite (prel_option r p x y) as pure False;
          unreachable ()
        }
        Some b -> {
          match y' {
            None -> {
              rewrite (prel_option r p' x y') as pure False;
              unreachable ()
            }
            Some b' -> {
              rewrite (prel_option r p x y) as (r p a b);
              rewrite (prel_option r p' x y') as (r p' a b');
              g a #p #b #p' #b';
              rewrite (r (p +. p') a b) as (prel_option r (p +. p') x y);
            }
          }
        }
      }
    }
  }
}

ghost
fn share_default (#t: Type0) (#u: eqtype) (r: prel t u) (defv: u) (sh: share_t r)
: share_t #(option t) #(default_tv defv) (prel_default r defv)
= (x: option t) (#p: perm) (#y: default_tv defv)
{
  match x {
    None -> {
      match y {
        Default -> {
          rewrite (prel_default r defv p x y) as emp;
          rewrite emp as (prel_default r defv (p /. 2.0R) x y);
          rewrite emp as (prel_default r defv (p /. 2.0R) x y);
        }
        Nondefault b -> {
          rewrite (prel_default r defv p x y) as pure False;
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        Default -> {
          rewrite (prel_default r defv p x y) as pure False;
          unreachable ()
        }
        Nondefault b -> {
          rewrite (prel_default r defv p x y) as (r p a b);
          sh a #p #b;
          rewrite (r (p /. 2.0R) a b) as (prel_default r defv (p /. 2.0R) x y);
          rewrite (r (p /. 2.0R) a b) as (prel_default r defv (p /. 2.0R) x y);
        }
      }
    }
  }
}

ghost
fn gather_default (#t: Type0) (#u: eqtype) (r: prel t u) (defv: u) (g: gather_t r)
: gather_t #(option t) #(default_tv defv) (prel_default r defv)
= (x: option t) (#p: perm) (#y: default_tv defv) (#p': perm) (#y': default_tv defv)
{
  match x {
    None -> {
      match y {
        Default -> {
          match y' {
            Default -> {
              rewrite (prel_default r defv p x y) as emp;
              rewrite (prel_default r defv p' x y') as emp;
              rewrite emp as (prel_default r defv (p +. p') x y);
            }
            Nondefault _ -> {
              rewrite (prel_default r defv p' x y') as pure False;
              unreachable ()
            }
          }
        }
        Nondefault _ -> {
          rewrite (prel_default r defv p x y) as pure False;
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        Default -> {
          rewrite (prel_default r defv p x y) as pure False;
          unreachable ()
        }
        Nondefault b -> {
          match y' {
            Default -> {
              rewrite (prel_default r defv p' x y') as pure False;
              unreachable ()
            }
            Nondefault b' -> {
              rewrite (prel_default r defv p x y) as (r p a b);
              rewrite (prel_default r defv p' x y') as (r p' a b');
              g a #p #b #p' #b';
              rewrite (r (p +. p') a b) as (prel_default r defv (p +. p') x y);
            }
          }
        }
      }
    }
  }
}

ghost
fn share_pair (#t1 #t2: Type0) (#u1 #u2: Type0) (r1: prel t1 u1) (r2: prel t2 u2) (sh1: share_t r1) (sh2: share_t r2)
: share_t #(t1 & t2) #(u1 & u2) (prel_pair r1 r2)
= (x: t1 & t2) (#p: perm) (#y: u1 & u2)
{
  unfold (prel_pair r1 r2 p x y);
  sh1 (fst x) #p #(fst y);
  sh2 (snd x) #p #(snd y);
  fold (prel_pair r1 r2 (p /. 2.0R) x y);
  fold (prel_pair r1 r2 (p /. 2.0R) x y)
}

ghost
fn gather_pair (#t1 #t2: Type0) (#u1 #u2: Type0) (r1: prel t1 u1) (r2: prel t2 u2) (g1: gather_t r1) (g2: gather_t r2)
: gather_t #(t1 & t2) #(u1 & u2) (prel_pair r1 r2)
= (x: t1 & t2) (#p: perm) (#y: u1 & u2) (#p': perm) (#y': u1 & u2)
{
  unfold (prel_pair r1 r2 p x y);
  unfold (prel_pair r1 r2 p' x y');
  g1 (fst x) #p #(fst y) #p' #(fst y');
  g2 (snd x) #p #(snd y) #p' #(snd y');
  fold (prel_pair r1 r2 (p +. p') x y)
}

(* Terminals *)

let terminal_prefixed_eq (id: asn1_id_t) (k': asn1_terminal_k)
: Lemma (share_t (asn1_terminal_rel (ASN1_PREFIXED_TERMINAL id k')) == share_t (asn1_terminal_rel k') /\
    gather_t (asn1_terminal_rel (ASN1_PREFIXED_TERMINAL id k')) == gather_t (asn1_terminal_rel k'))
= assert_norm (asn1_terminal_rel (ASN1_PREFIXED_TERMINAL id k') == asn1_terminal_rel k')

let rec share_terminal (k: asn1_terminal_k) : Tot (share_t (asn1_terminal_rel k)) (decreases k) =
  match k with
  | ASN1_BOOLEAN -> share_eq bool
  | ASN1_NULL -> share_emp_unit ()
  | ASN1_INTEGER bound ->
    if small_integer bound
    then coerce_eq () (share_small_int bound)
    else coerce_eq () (share_int bound)
  | ASN1_BITSTRING -> share_bitstring ()
  | ASN1_PREFIXED_TERMINAL id k' -> terminal_prefixed_eq id k'; coerce_eq () (share_terminal k')
  | ASN1_OCTETSTRING -> share_slice_ser (leaf_enc k)
  | ASN1_PRINTABLESTRING -> share_slice_ser (leaf_enc k)
  | ASN1_UTF8STRING -> share_slice_ser (leaf_enc k)
  | ASN1_IA5STRING -> share_slice_ser (leaf_enc k)
  | ASN1_VISIBLESTRING -> share_slice_ser (leaf_enc k)
  | ASN1_BMPSTRING -> share_slice_ser (leaf_enc k)
  | ASN1_UNIVERSALSTRING -> share_slice_ser (leaf_enc k)
  | ASN1_TELETEXSTRING -> share_slice_ser (leaf_enc k)
  | ASN1_NUMERICSTRING -> share_slice_ser (leaf_enc k)
  | ASN1_VIDEOTEXSTRING -> share_slice_ser (leaf_enc k)
  | ASN1_GRAPHICSTRING -> share_slice_ser (leaf_enc k)
  | ASN1_GENERALSTRING -> share_slice_ser (leaf_enc k)
  | ASN1_OBJECTDESCRIPTOR -> share_slice_ser (leaf_enc k)
  | ASN1_OID -> share_slice_ser (leaf_enc k)
  | ASN1_RELATIVE_OID -> share_slice_ser (leaf_enc k)
  | ASN1_OID_IRI -> share_slice_ser (leaf_enc k)
  | ASN1_RELATIVE_OID_IRI -> share_slice_ser (leaf_enc k)
  | ASN1_UTCTIME -> share_slice_ser (leaf_enc k)
  | ASN1_GENERALIZEDTIME -> share_slice_ser (leaf_enc k)
  | ASN1_DATE -> share_slice_ser (leaf_enc k)
  | ASN1_TIME_OF_DAY -> share_slice_ser (leaf_enc k)
  | ASN1_DATE_TIME -> share_slice_ser (leaf_enc k)

let rec gather_terminal (k: asn1_terminal_k) : Tot (gather_t (asn1_terminal_rel k)) (decreases k) =
  match k with
  | ASN1_BOOLEAN -> gather_eq bool
  | ASN1_NULL -> gather_emp_unit ()
  | ASN1_INTEGER bound ->
    if small_integer bound
    then coerce_eq () (gather_small_int bound)
    else coerce_eq () (gather_int bound)
  | ASN1_BITSTRING -> gather_bitstring ()
  | ASN1_PREFIXED_TERMINAL id k' -> terminal_prefixed_eq id k'; coerce_eq () (gather_terminal k')
  | ASN1_OCTETSTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_PRINTABLESTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_UTF8STRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_IA5STRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_VISIBLESTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_BMPSTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_UNIVERSALSTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_TELETEXSTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_NUMERICSTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_VIDEOTEXSTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_GRAPHICSTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_GENERALSTRING -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_OBJECTDESCRIPTOR -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_OID -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_RELATIVE_OID -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_OID_IRI -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_RELATIVE_OID_IRI -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_UTCTIME -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_GENERALIZEDTIME -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_DATE -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_TIME_OF_DAY -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)
  | ASN1_DATE_TIME -> gather_slice_ser (leaf_enc k) (leaf_enc_injective k)

(* Contents *)

let content_terminal_equiv (k: asn1_terminal_k)
: Lemma (prel_equiv #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) (asn1_content_rel (ASN1_TERMINAL k)))
= assert_norm (prel_equiv #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) (asn1_content_rel (ASN1_TERMINAL k)))

let restricted_t_eq (k: asn1_terminal_k) (r: asn1_restriction k)
: Lemma (asn1_content_t (ASN1_RESTRICTED_TERMINAL k r) == parse_filter_refine (restriction_pred r))
= assert_norm (asn1_content_t (ASN1_RESTRICTED_TERMINAL k r) == parse_filter_refine (restriction_pred r))

let restricted_up (k: asn1_terminal_k) (r: asn1_restriction k) (y: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) : Tot (asn1_terminal_t k) =
  restricted_t_eq k r;
  let y' : parse_filter_refine (restriction_pred r) = coerce_eq () y in
  y'

let content_restricted_eq (k: asn1_terminal_k) (r: asn1_restriction k) (pm: perm) (x: asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) (y: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
: Lemma (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm x y == asn1_terminal_rel k pm x (restricted_up k r y))
= assert_norm (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm x y == asn1_terminal_rel k pm x y)

ghost
fn share_restricted (k: asn1_terminal_k) (r: asn1_restriction k) (sh: share_t (asn1_terminal_rel k))
: share_t #(asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r))
= (x: asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) (#p: perm) (#y: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
{
  content_restricted_eq k r p x y;
  content_restricted_eq k r (p /. 2.0R) x y;
  rewrite (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) p x y) as (asn1_terminal_rel k p x (restricted_up k r y));
  sh x #p #(restricted_up k r y);
  rewrite (asn1_terminal_rel k (p /. 2.0R) x (restricted_up k r y) ** asn1_terminal_rel k (p /. 2.0R) x (restricted_up k r y))
    as (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) (p /. 2.0R) x y ** asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) (p /. 2.0R) x y)
}

ghost
fn gather_restricted (k: asn1_terminal_k) (r: asn1_restriction k) (g: gather_t (asn1_terminal_rel k))
: gather_t #(asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r))
= (x: asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) (#p: perm) (#y: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (#p': perm) (#y': asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
{
  content_restricted_eq k r p x y;
  content_restricted_eq k r p' x y';
  content_restricted_eq k r (p +. p') x y;
  rewrite (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) p x y ** asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) p' x y')
    as (asn1_terminal_rel k p x (restricted_up k r y) ** asn1_terminal_rel k p' x (restricted_up k r y'));
  g x #p #(restricted_up k r y) #p' #(restricted_up k r y');
  rewrite (asn1_terminal_rel k (p +. p') x (restricted_up k r y)) as (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) (p +. p') x y)
}

let content_prefixed_equiv (#s: _) (k: asn1_k s)
: Lemma (prel_equiv #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_content_rel (ASN1_PREFIXED k)))
= assert_norm (prel_equiv #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_content_rel (ASN1_PREFIXED k)))

let content_sequence_equiv (gitems: asn1_gen_items_lk)
: Lemma (prel_equiv #(asn1_items_impl_t (dsnd gitems)) #(asn1_sequence_t_core (dsnd gitems)) (asn1_items_rel (dsnd gitems)) (asn1_content_rel (ASN1_SEQUENCE gitems)))
= assert_norm (prel_equiv #(asn1_items_impl_t (dsnd gitems)) #(asn1_sequence_t_core (dsnd gitems)) (asn1_items_rel (dsnd gitems)) (asn1_content_rel (ASN1_SEQUENCE gitems)))

let content_set_equiv (ids: _) (items: asn1_gen_items_l ids) (pf: _)
: Lemma (prel_equiv #(asn1_items_impl_t items) #(asn1_sequence_t_core items) (asn1_items_rel items) (asn1_content_rel (ASN1_SET ids items pf)))
= assert_norm (prel_equiv #(asn1_items_impl_t items) #(asn1_sequence_t_core items) (asn1_items_rel items) (asn1_content_rel (ASN1_SET ids items pf)))

let seq_of_up (ne: bool) (#s: _) (k: asn1_k s) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k)) : Tot (list (asn1_t k)) =
  assert_norm (asn1_content_t (ASN1_SEQUENCE_OF ne k) == sized_list ne (asn1_t k));
  let y' : sized_list ne (asn1_t k) = coerce_eq () y in
  y'

let set_of_up (ne: bool) (#s: _) (k: asn1_k s) (y: asn1_content_t (ASN1_SET_OF ne k)) : Tot (list (asn1_t k)) =
  assert_norm (asn1_content_t (ASN1_SET_OF ne k) == sized_list ne (asn1_t k));
  let y' : sized_list ne (asn1_t k) = coerce_eq () y in
  y'

let seq_of_eq (ne: bool) (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm x y == It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x (seq_of_up ne k y))
= asn1_content_rel_seq_of_eq ne k pm x y

let set_of_eq (ne: bool) (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_content_impl_t (ASN1_SET_OF ne k)) (y: asn1_content_t (ASN1_SET_OF ne k))
: Lemma (asn1_content_rel (ASN1_SET_OF ne k) pm x y == It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x (set_of_up ne k y))
= asn1_content_rel_set_of_eq ne k pm x y

ghost
fn share_seq_of (ne: bool) (#s: _) (k: asn1_k s) (sh: share_t (asn1_rel k))
: share_t #(asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) #(asn1_content_t (ASN1_SEQUENCE_OF ne k)) (asn1_content_rel (ASN1_SEQUENCE_OF ne k))
= (x: asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) (#p: perm) (#y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
{
  seq_of_eq ne k p x y;
  seq_of_eq ne k (p /. 2.0R) x y;
  rewrite (asn1_content_rel (ASN1_SEQUENCE_OF ne k) p x y) as (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p x (seq_of_up ne k y));
  It.mixed_list_match_share (asn1_rel k) ml_ops (asn1_as_parser k) p x (seq_of_up ne k y) sh;
  rewrite (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p /. 2.0R) x (seq_of_up ne k y) ** It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p /. 2.0R) x (seq_of_up ne k y))
    as (asn1_content_rel (ASN1_SEQUENCE_OF ne k) (p /. 2.0R) x y ** asn1_content_rel (ASN1_SEQUENCE_OF ne k) (p /. 2.0R) x y)
}

ghost
fn gather_seq_of (ne: bool) (#s: _) (k: asn1_k s) (g: gather_t (asn1_rel k))
: gather_t #(asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) #(asn1_content_t (ASN1_SEQUENCE_OF ne k)) (asn1_content_rel (ASN1_SEQUENCE_OF ne k))
= (x: asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) (#p: perm) (#y: asn1_content_t (ASN1_SEQUENCE_OF ne k)) (#p': perm) (#y': asn1_content_t (ASN1_SEQUENCE_OF ne k))
{
  seq_of_eq ne k p x y;
  seq_of_eq ne k p' x y';
  seq_of_eq ne k (p +. p') x y;
  rewrite (asn1_content_rel (ASN1_SEQUENCE_OF ne k) p x y ** asn1_content_rel (ASN1_SEQUENCE_OF ne k) p' x y')
    as (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p x (seq_of_up ne k y) ** It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p' x (seq_of_up ne k y'));
  It.mixed_list_match_gather (asn1_rel k) ml_ops (asn1_as_parser k) p p' x (seq_of_up ne k y) (seq_of_up ne k y') g;
  rewrite (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p +. p') x (seq_of_up ne k y))
    as (asn1_content_rel (ASN1_SEQUENCE_OF ne k) (p +. p') x y)
}

ghost
fn share_set_of (ne: bool) (#s: _) (k: asn1_k s) (sh: share_t (asn1_rel k))
: share_t #(asn1_content_impl_t (ASN1_SET_OF ne k)) #(asn1_content_t (ASN1_SET_OF ne k)) (asn1_content_rel (ASN1_SET_OF ne k))
= (x: asn1_content_impl_t (ASN1_SET_OF ne k)) (#p: perm) (#y: asn1_content_t (ASN1_SET_OF ne k))
{
  set_of_eq ne k p x y;
  set_of_eq ne k (p /. 2.0R) x y;
  rewrite (asn1_content_rel (ASN1_SET_OF ne k) p x y) as (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p x (set_of_up ne k y));
  It.mixed_list_match_share (asn1_rel k) ml_ops (asn1_as_parser k) p x (set_of_up ne k y) sh;
  rewrite (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p /. 2.0R) x (set_of_up ne k y) ** It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p /. 2.0R) x (set_of_up ne k y))
    as (asn1_content_rel (ASN1_SET_OF ne k) (p /. 2.0R) x y ** asn1_content_rel (ASN1_SET_OF ne k) (p /. 2.0R) x y)
}

ghost
fn gather_set_of (ne: bool) (#s: _) (k: asn1_k s) (g: gather_t (asn1_rel k))
: gather_t #(asn1_content_impl_t (ASN1_SET_OF ne k)) #(asn1_content_t (ASN1_SET_OF ne k)) (asn1_content_rel (ASN1_SET_OF ne k))
= (x: asn1_content_impl_t (ASN1_SET_OF ne k)) (#p: perm) (#y: asn1_content_t (ASN1_SET_OF ne k)) (#p': perm) (#y': asn1_content_t (ASN1_SET_OF ne k))
{
  set_of_eq ne k p x y;
  set_of_eq ne k p' x y';
  set_of_eq ne k (p +. p') x y;
  rewrite (asn1_content_rel (ASN1_SET_OF ne k) p x y ** asn1_content_rel (ASN1_SET_OF ne k) p' x y')
    as (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p x (set_of_up ne k y) ** It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p' x (set_of_up ne k y'));
  It.mixed_list_match_gather (asn1_rel k) ml_ops (asn1_as_parser k) p p' x (set_of_up ne k y) (set_of_up ne k y') g;
  rewrite (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p +. p') x (set_of_up ne k y))
    as (asn1_content_rel (ASN1_SET_OF ne k) (p +. p') x y)
}

(* Tags *)

let rel_ilc_equiv (id: asn1_id_t) (k: asn1_content_k)
: Lemma (prel_equiv #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k) (asn1_rel (ASN1_ILC id k)))
= assert_norm (prel_equiv #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k) (asn1_rel (ASN1_ILC id k)))

let rel_any_equiv (_: unit)
: Lemma (prel_equiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (asn1_rel ASN1_ANY_ILC))
= assert_norm (prel_equiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (asn1_rel ASN1_ANY_ILC))

let rel_choice_equiv (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc)))
: Lemma (prel_equiv #(asn1_lc_impl_t lc) #(make_gen_choice_type (asn1_lc_t lc)) (asn1_lc_rel lc) (asn1_rel (ASN1_CHOICE_ILC lc pf)))
= assert_norm (prel_equiv #(asn1_lc_impl_t lc) #(make_gen_choice_type (asn1_lc_t lc)) (asn1_lc_rel lc) (asn1_rel (ASN1_CHOICE_ILC lc pf)))

(* Decorated items *)

let dec_plain_equiv (#s: _) (k: asn1_k s)
: Lemma (prel_equiv #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_decorated_rel (ASN1_PLAIN_ILC k)))
= assert_norm (prel_equiv #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_decorated_rel (ASN1_PLAIN_ILC k)))

let dec_option_equiv (#s: _) (k: asn1_k s)
: Lemma (prel_equiv #(option (asn1_impl_t k)) #(option (asn1_t k)) (prel_option (asn1_rel k)) (asn1_decorated_rel (ASN1_OPTION_ILC k)))
= assert_norm (prel_equiv #(option (asn1_impl_t k)) #(option (asn1_t k)) (prel_option (asn1_rel k)) (asn1_decorated_rel (ASN1_OPTION_ILC k)))

let dec_default_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k)
: Lemma (prel_equiv #(option (asn1_terminal_impl_t k)) #(default_tv (key_of_lit k defv)) (prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)))
= assert_norm (prel_equiv #(option (asn1_terminal_impl_t k)) #(default_tv (key_of_lit k defv)) (prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)))

let dec_default_restricted_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) })
: Lemma (prel_equiv #(option (asn1_terminal_impl_t k)) #(default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv)) (prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)))
= assert_norm (prel_equiv #(option (asn1_terminal_impl_t k)) #(default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv)) (prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)))

(* Items *)

let items_nil_equiv (_: unit)
: Lemma (prel_equiv #unit #unit (prel_emp unit unit) (asn1_items_rel ASN1_GEN_ITEMS_NIL))
= assert_norm (prel_equiv #unit #unit (prel_emp unit unit) (asn1_items_rel ASN1_GEN_ITEMS_NIL))

let items_single_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (prel_equiv #(asn1_decorated_impl_t dk) #(asn1_decorated_t_core dk) (asn1_decorated_rel dk) (asn1_items_rel (PS.single dk)))
= assert_norm (prel_equiv #(asn1_decorated_impl_t dk) #(asn1_decorated_t_core dk) (asn1_decorated_rel dk) (asn1_items_rel (PS.single dk)))

let items_cons_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
: Lemma (prel_equiv
    #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    #(asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    (prel_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
    (asn1_items_rel (PS.cons2 dk dk2 tl2)))
= assert_norm (prel_equiv
    #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    #(asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    (prel_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
    (asn1_items_rel (PS.cons2 dk dk2 tl2)))

(* CHOICE alternatives *)

let lc_head_val (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (asn1_lc_t ((id', c) :: tl))) (sq: squash (dfst v == id'))
: Tot (asn1_content_t c)
= dsnd v

let lc_tail_val (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (asn1_lc_t (hd :: tl))) (sq: squash (dfst v <> fst hd))
: Tot (make_gen_choice_type (asn1_lc_t tl))
= (| dfst v, dsnd v |)

let lc_head_inj (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v v': make_gen_choice_type (asn1_lc_t ((id', c) :: tl)))
: Lemma (requires dfst v == id' /\ dfst v' == id' /\ lc_head_val id' c tl v () == lc_head_val id' c tl v' ())
  (ensures v == v')
= ()

let lc_tail_inj (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v v': make_gen_choice_type (asn1_lc_t (hd :: tl)))
: Lemma (requires dfst v <> fst hd /\ dfst v' <> fst hd /\ lc_tail_val hd tl v () == lc_tail_val hd tl v' ())
  (ensures v == v')
= ()

let lc_single_eq (id': asn1_id_t) (c: asn1_content_k) (pm: perm) (x: asn1_lc_impl_t [(id', c)])
  (v: make_gen_choice_type (asn1_lc_t [(id', c)]))
: Lemma (asn1_lc_rel [(id', c)] pm x v == (if dfst v = id' then asn1_content_rel c pm x (lc_head_val id' c [] v ()) else pure False))
= assert_norm (asn1_lc_rel [(id', c)] pm x v == (let (| id, v |) = v in if id = id' then asn1_content_rel c pm x v else pure False))

let lc_inl (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k)) (a: asn1_content_impl_t c)
: Tot (asn1_lc_impl_t ((id', c) :: hd2 :: tl2))
= Inl #_ #(asn1_lc_impl_t (hd2 :: tl2)) a

let lc_inr (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k)) (b: asn1_lc_impl_t (hd2 :: tl2))
: Tot (asn1_lc_impl_t ((id', c) :: hd2 :: tl2))
= Inr #(asn1_content_impl_t c) b

let lc_cons_inl_eq (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (a: asn1_content_impl_t c) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm (lc_inl id' c hd2 tl2 a) v ==
    (if dfst v = id' then asn1_content_rel c pm a (lc_head_val id' c (hd2 :: tl2) v ()) else pure False))
= let (| id, w |) = v in
  assert_norm (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm (lc_inl id' c hd2 tl2 a) (| id, w |) ==
    (if id = id' then asn1_content_rel c pm a w else pure False))

let lc_cons_inr_eq (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (b: asn1_lc_impl_t (hd2 :: tl2)) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm (lc_inr id' c hd2 tl2 b) v ==
    (if dfst v = id' then pure False else asn1_lc_rel (hd2 :: tl2) pm b (lc_tail_val (id', c) (hd2 :: tl2) v ())))
= let (| id, w |) = v in
  assert_norm (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm (lc_inr id' c hd2 tl2 b) (| id, w |) ==
    (if id = id' then pure False else asn1_lc_rel (hd2 :: tl2) pm b (| id, w |)));
  if id = id' then () else begin
    let t : make_gen_choice_type (asn1_lc_t (hd2 :: tl2)) = lc_tail_val (id', c) (hd2 :: tl2) v () in
    assert_norm (lc_tail_val (id', c) (hd2 :: tl2) v () == (| dfst v, dsnd v |));
    assert (t == (| id, w |))
  end

ghost
fn share_lc_single (id': asn1_id_t) (c: asn1_content_k) (sh: share_t (asn1_content_rel c))
: share_t #(asn1_lc_impl_t [(id', c)]) #(make_gen_choice_type (asn1_lc_t [(id', c)])) (asn1_lc_rel [(id', c)])
= (x: asn1_lc_impl_t [(id', c)]) (#p: perm) (#y: make_gen_choice_type (asn1_lc_t [(id', c)]))
{
  lc_single_eq id' c p x y;
  lc_single_eq id' c (p /. 2.0R) x y;
  if (dfst y = id') {
    rewrite (asn1_lc_rel [(id', c)] p x y) as (asn1_content_rel c p x (lc_head_val id' c [] y ()));
    sh x #p #(lc_head_val id' c [] y ());
    rewrite (asn1_content_rel c (p /. 2.0R) x (lc_head_val id' c [] y ()) ** asn1_content_rel c (p /. 2.0R) x (lc_head_val id' c [] y ()))
      as (asn1_lc_rel [(id', c)] (p /. 2.0R) x y ** asn1_lc_rel [(id', c)] (p /. 2.0R) x y)
  } else {
    rewrite (asn1_lc_rel [(id', c)] p x y) as (pure False);
    unreachable ()
  }
}

ghost
fn gather_lc_single (id': asn1_id_t) (c: asn1_content_k) (g: gather_t (asn1_content_rel c))
: gather_t #(asn1_lc_impl_t [(id', c)]) #(make_gen_choice_type (asn1_lc_t [(id', c)])) (asn1_lc_rel [(id', c)])
= (x: asn1_lc_impl_t [(id', c)]) (#p: perm) (#y: make_gen_choice_type (asn1_lc_t [(id', c)])) (#p': perm) (#y': make_gen_choice_type (asn1_lc_t [(id', c)]))
{
  lc_single_eq id' c p x y;
  lc_single_eq id' c p' x y';
  lc_single_eq id' c (p +. p') x y;
  if (dfst y = id') {
    if (dfst y' = id') {
      rewrite (asn1_lc_rel [(id', c)] p x y ** asn1_lc_rel [(id', c)] p' x y')
        as (asn1_content_rel c p x (lc_head_val id' c [] y ()) ** asn1_content_rel c p' x (lc_head_val id' c [] y' ()));
      g x #p #(lc_head_val id' c [] y ()) #p' #(lc_head_val id' c [] y' ());
      lc_head_inj id' c [] y y';
      rewrite (asn1_content_rel c (p +. p') x (lc_head_val id' c [] y ())) as (asn1_lc_rel [(id', c)] (p +. p') x y)
    } else {
      rewrite (asn1_lc_rel [(id', c)] p' x y') as (pure False);
      unreachable ()
    }
  } else {
    rewrite (asn1_lc_rel [(id', c)] p x y) as (pure False);
    unreachable ()
  }
}

ghost
fn share_lc_cons (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (sh: share_t (asn1_content_rel c)) (sht: share_t (asn1_lc_rel (hd2 :: tl2)))
: share_t #(asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) #(make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) (asn1_lc_rel ((id', c) :: hd2 :: tl2))
= (x: asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) (#p: perm) (#y: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
{
  let x' : either (asn1_content_impl_t c) (asn1_lc_impl_t (hd2 :: tl2)) = x;
  match x' {
    Inl a -> {
      lc_cons_inl_eq id' c hd2 tl2 p a y;
      lc_cons_inl_eq id' c hd2 tl2 (p /. 2.0R) a y;
      assert (pure (x == lc_inl id' c hd2 tl2 a));
      if (dfst y = id') {
        rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p x y) as (asn1_content_rel c p a (lc_head_val id' c (hd2 :: tl2) y ()));
        sh a #p #(lc_head_val id' c (hd2 :: tl2) y ());
        rewrite (asn1_content_rel c (p /. 2.0R) a (lc_head_val id' c (hd2 :: tl2) y ()) ** asn1_content_rel c (p /. 2.0R) a (lc_head_val id' c (hd2 :: tl2) y ()))
          as (asn1_lc_rel ((id', c) :: hd2 :: tl2) (p /. 2.0R) x y ** asn1_lc_rel ((id', c) :: hd2 :: tl2) (p /. 2.0R) x y)
      } else {
        rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p x y) as (pure False);
        unreachable ()
      }
    }
    Inr b -> {
      lc_cons_inr_eq id' c hd2 tl2 p b y;
      lc_cons_inr_eq id' c hd2 tl2 (p /. 2.0R) b y;
      assert (pure (x == lc_inr id' c hd2 tl2 b));
      if (dfst y = id') {
        rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p x y) as (pure False);
        unreachable ()
      } else {
        rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p x y) as (asn1_lc_rel (hd2 :: tl2) p b (lc_tail_val (id', c) (hd2 :: tl2) y ()));
        sht b #p #(lc_tail_val (id', c) (hd2 :: tl2) y ());
        rewrite (asn1_lc_rel (hd2 :: tl2) (p /. 2.0R) b (lc_tail_val (id', c) (hd2 :: tl2) y ()) ** asn1_lc_rel (hd2 :: tl2) (p /. 2.0R) b (lc_tail_val (id', c) (hd2 :: tl2) y ()))
          as (asn1_lc_rel ((id', c) :: hd2 :: tl2) (p /. 2.0R) x y ** asn1_lc_rel ((id', c) :: hd2 :: tl2) (p /. 2.0R) x y)
      }
    }
  }
}

ghost
fn gather_lc_cons (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (g: gather_t (asn1_content_rel c)) (gt: gather_t (asn1_lc_rel (hd2 :: tl2)))
: gather_t #(asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) #(make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) (asn1_lc_rel ((id', c) :: hd2 :: tl2))
= (x: asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) (#p: perm) (#y: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) (#p': perm) (#y': make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
{
  let x' : either (asn1_content_impl_t c) (asn1_lc_impl_t (hd2 :: tl2)) = x;
  match x' {
    Inl a -> {
      lc_cons_inl_eq id' c hd2 tl2 p a y;
      lc_cons_inl_eq id' c hd2 tl2 p' a y';
      lc_cons_inl_eq id' c hd2 tl2 (p +. p') a y;
      assert (pure (x == lc_inl id' c hd2 tl2 a));
      if (dfst y = id') {
        if (dfst y' = id') {
          rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p x y ** asn1_lc_rel ((id', c) :: hd2 :: tl2) p' x y')
            as (asn1_content_rel c p a (lc_head_val id' c (hd2 :: tl2) y ()) ** asn1_content_rel c p' a (lc_head_val id' c (hd2 :: tl2) y' ()));
          g a #p #(lc_head_val id' c (hd2 :: tl2) y ()) #p' #(lc_head_val id' c (hd2 :: tl2) y' ());
          lc_head_inj id' c (hd2 :: tl2) y y';
          rewrite (asn1_content_rel c (p +. p') a (lc_head_val id' c (hd2 :: tl2) y ())) as (asn1_lc_rel ((id', c) :: hd2 :: tl2) (p +. p') x y)
        } else {
          rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p' x y') as (pure False);
          unreachable ()
        }
      } else {
        rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p x y) as (pure False);
        unreachable ()
      }
    }
    Inr b -> {
      lc_cons_inr_eq id' c hd2 tl2 p b y;
      lc_cons_inr_eq id' c hd2 tl2 p' b y';
      lc_cons_inr_eq id' c hd2 tl2 (p +. p') b y;
      assert (pure (x == lc_inr id' c hd2 tl2 b));
      if (dfst y = id') {
        rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p x y) as (pure False);
        unreachable ()
      } else if (dfst y' = id') {
        rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p' x y') as (pure False);
        unreachable ()
      } else {
        rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) p x y ** asn1_lc_rel ((id', c) :: hd2 :: tl2) p' x y')
          as (asn1_lc_rel (hd2 :: tl2) p b (lc_tail_val (id', c) (hd2 :: tl2) y ()) ** asn1_lc_rel (hd2 :: tl2) p' b (lc_tail_val (id', c) (hd2 :: tl2) y' ()));
        gt b #p #(lc_tail_val (id', c) (hd2 :: tl2) y ()) #p' #(lc_tail_val (id', c) (hd2 :: tl2) y' ());
        lc_tail_inj (id', c) (hd2 :: tl2) y y';
        rewrite (asn1_lc_rel (hd2 :: tl2) (p +. p') b (lc_tail_val (id', c) (hd2 :: tl2) y ())) as (asn1_lc_rel ((id', c) :: hd2 :: tl2) (p +. p') x y)
      }
    }
  }
}

ghost
fn share_lc_nil (_: unit)
: share_t #(asn1_lc_impl_t []) #(make_gen_choice_type (asn1_lc_t [])) (asn1_lc_rel [])
= (x: asn1_lc_impl_t []) (#p: perm) (#y: make_gen_choice_type (asn1_lc_t []))
{
  rewrite (asn1_lc_rel [] p x y) as (pure False);
  unreachable ()
}

ghost
fn gather_lc_nil (_: unit)
: gather_t #(asn1_lc_impl_t []) #(make_gen_choice_type (asn1_lc_t [])) (asn1_lc_rel [])
= (x: asn1_lc_impl_t []) (#p: perm) (#y: make_gen_choice_type (asn1_lc_t [])) (#p': perm) (#y': make_gen_choice_type (asn1_lc_t []))
{
  rewrite (asn1_lc_rel [] p x y) as (pure False);
  unreachable ()
}

let share_any (_: unit) : share_t #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) =
  share_slice_ser asn1_value_enc

let gather_any (_: unit) : gather_t #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) =
  gather_slice_ser asn1_value_enc (value_enc_injective ())

(* ANY DEFINED BY *)

let items_any_nil_equiv (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (prel_equiv #sfxi #sfxs sfxr (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr))
= assert_norm (prel_equiv #sfxi #sfxs sfxr (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr))

let items_any_single_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (prel_equiv #(asn1_decorated_impl_t dk & sfxi) #(asn1_decorated_t_core dk & sfxs) (prel_pair (asn1_decorated_rel dk) sfxr) (asn1_items_any_rel (PS.single dk) sfxr))
= assert_norm (prel_equiv #(asn1_decorated_impl_t dk & sfxi) #(asn1_decorated_t_core dk & sfxs) (prel_pair (asn1_decorated_rel dk) sfxr) (asn1_items_any_rel (PS.single dk) sfxr))

let items_any_cons_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (prel_equiv
    #(asn1_decorated_impl_t dk & asn1_items_any_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi)
    #(asn1_decorated_t_core dk & asn1_sequence_any_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs)
    (prel_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr))
    (asn1_items_any_rel (PS.cons2 dk dk2 tl2) sfxr))
= assert_norm (prel_equiv
    #(asn1_decorated_impl_t dk & asn1_items_any_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi)
    #(asn1_decorated_t_core dk & asn1_sequence_any_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs)
    (prel_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr))
    (asn1_items_any_rel (PS.cons2 dk dk2 tl2) sfxr))

let adb_none_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma (prel_equiv
    #(asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls None))
    #(asn1_sequence_any_t_core prefix (AL.ady key_k ls))
    (asn1_items_any_rel prefix (asn1_adb_rel key_k ls))
    (asn1_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf')))
= Classical.forall_intro_3 (PA.adb_rel_none_eq ipd prefix kid key_k ls pf pf')

let adb_some_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma (prel_equiv
    #(asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb))))
    #(asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb))
    (asn1_items_any_rel prefix (PA.afb_rel key_k ls fb))
    (asn1_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf')))
= Classical.forall_intro_3 (PA.adb_rel_some_eq ipd prefix kid key_k ls fb pf pf')

(* Without a fallback *)

let adb_single_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (pm: perm)
  (r: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady key_k [(kx, y)])
: Lemma (asn1_adb_rel key_k [(kx, y)] pm r v ==
    (if dfst v = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm r (AL.ady_head_val kx y [] v ()) else pure False))
= assert_norm (asn1_adb_rel key_k [(kx, y)] pm r v == (let (| key, w |) = v in if key = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm r w else pure False))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let adb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) a) v ==
    (if dfst v = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm a (AL.ady_head_val kx y (hd2 :: tl2) v ()) else pure False))
= ()

let adb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else asn1_adb_rel key_k (hd2 :: tl2) pm b (AL.ady_tail_val kx y (hd2 :: tl2) v ())))
= let (| key, w |) = v in
  PA.adb_rel_cons_inr_aux kx y hd2 tl2 pm b key w
#pop-options

let ady_head_inj (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (v v': AL.ady key_k ((kx, y) :: tl))
: Lemma (requires dfst v == key_of_lit key_k kx /\ dfst v' == key_of_lit key_k kx /\ AL.ady_head_val kx y tl v () == AL.ady_head_val kx y tl v' ())
  (ensures v == v')
= ()

let ady_tail_inj (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (v v': AL.ady key_k ((kx, y) :: tl))
: Lemma (requires dfst v <> key_of_lit key_k kx /\ dfst v' <> key_of_lit key_k kx /\ AL.ady_tail_val kx y tl v () == AL.ady_tail_val kx y tl v' ())
  (ensures v == v')
= ()

ghost
fn share_adb_nil (key_k: asn1_terminal_k)
: share_t #(asn1_adb_suffix_impl_t key_k [] None) #(AL.ady key_k []) (asn1_adb_rel key_k [])
= (x: asn1_adb_suffix_impl_t key_k [] None) (#p: perm) (#y: AL.ady key_k [])
{
  rewrite (asn1_adb_rel key_k [] p x y) as (pure False);
  unreachable ()
}

ghost
fn gather_adb_nil (key_k: asn1_terminal_k)
: gather_t #(asn1_adb_suffix_impl_t key_k [] None) #(AL.ady key_k []) (asn1_adb_rel key_k [])
= (x: asn1_adb_suffix_impl_t key_k [] None) (#p: perm) (#y: AL.ady key_k []) (#p': perm) (#y': AL.ady key_k [])
{
  rewrite (asn1_adb_rel key_k [] p x y) as (pure False);
  unreachable ()
}

ghost
fn share_adb_single (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (sh: share_t (asn1_items_rel (dsnd y)))
: share_t #(asn1_adb_suffix_impl_t key_k [(kx, y)] None) #(AL.ady key_k [(kx, y)]) (asn1_adb_rel key_k [(kx, y)])
= (x: asn1_adb_suffix_impl_t key_k [(kx, y)] None) (#p: perm) (#v: AL.ady key_k [(kx, y)])
{
  adb_single_eq kx y p x v;
  adb_single_eq kx y (p /. 2.0R) x v;
  if (dfst v = key_of_lit key_k kx) {
    rewrite (asn1_adb_rel key_k [(kx, y)] p x v) as (asn1_items_rel (dsnd y) p x (AL.ady_head_val kx y [] v ()));
    sh x #p #(AL.ady_head_val kx y [] v ());
    rewrite (asn1_items_rel (dsnd y) (p /. 2.0R) x (AL.ady_head_val kx y [] v ()) ** asn1_items_rel (dsnd y) (p /. 2.0R) x (AL.ady_head_val kx y [] v ()))
      as (asn1_adb_rel key_k [(kx, y)] (p /. 2.0R) x v ** asn1_adb_rel key_k [(kx, y)] (p /. 2.0R) x v)
  } else {
    rewrite (asn1_adb_rel key_k [(kx, y)] p x v) as (pure False);
    unreachable ()
  }
}

ghost
fn gather_adb_single (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (g: gather_t (asn1_items_rel (dsnd y)))
: gather_t #(asn1_adb_suffix_impl_t key_k [(kx, y)] None) #(AL.ady key_k [(kx, y)]) (asn1_adb_rel key_k [(kx, y)])
= (x: asn1_adb_suffix_impl_t key_k [(kx, y)] None) (#p: perm) (#v: AL.ady key_k [(kx, y)]) (#p': perm) (#v': AL.ady key_k [(kx, y)])
{
  adb_single_eq kx y p x v;
  adb_single_eq kx y p' x v';
  adb_single_eq kx y (p +. p') x v;
  if (dfst v = key_of_lit key_k kx) {
    if (dfst v' = key_of_lit key_k kx) {
      rewrite (asn1_adb_rel key_k [(kx, y)] p x v ** asn1_adb_rel key_k [(kx, y)] p' x v')
        as (asn1_items_rel (dsnd y) p x (AL.ady_head_val kx y [] v ()) ** asn1_items_rel (dsnd y) p' x (AL.ady_head_val kx y [] v' ()));
      g x #p #(AL.ady_head_val kx y [] v ()) #p' #(AL.ady_head_val kx y [] v' ());
      ady_head_inj kx y [] v v';
      rewrite (asn1_items_rel (dsnd y) (p +. p') x (AL.ady_head_val kx y [] v ())) as (asn1_adb_rel key_k [(kx, y)] (p +. p') x v)
    } else {
      rewrite (asn1_adb_rel key_k [(kx, y)] p' x v') as (pure False);
      unreachable ()
    }
  } else {
    rewrite (asn1_adb_rel key_k [(kx, y)] p x v) as (pure False);
    unreachable ()
  }
}

ghost
fn share_adb_cons (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (sh: share_t (asn1_items_rel (dsnd y))) (sht: share_t (asn1_adb_rel key_k (hd2 :: tl2)))
: share_t #(asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) #(AL.ady key_k ((kx, y) :: hd2 :: tl2)) (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2))
= (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) (#p: perm) (#v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
{
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) = x;
  match x' {
    Inl a -> {
      adb_cons_inl_eq kx y hd2 tl2 p a v;
      adb_cons_inl_eq kx y hd2 tl2 (p /. 2.0R) a v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p x v) as (asn1_items_rel (dsnd y) p a (AL.ady_head_val kx y (hd2 :: tl2) v ()));
        sh a #p #(AL.ady_head_val kx y (hd2 :: tl2) v ());
        rewrite (asn1_items_rel (dsnd y) (p /. 2.0R) a (AL.ady_head_val kx y (hd2 :: tl2) v ()) ** asn1_items_rel (dsnd y) (p /. 2.0R) a (AL.ady_head_val kx y (hd2 :: tl2) v ()))
          as (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) (p /. 2.0R) x v ** asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) (p /. 2.0R) x v)
      } else {
        rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p x v) as (pure False);
        unreachable ()
      }
    }
    Inr b -> {
      adb_cons_inr_eq kx y hd2 tl2 p b v;
      adb_cons_inr_eq kx y hd2 tl2 (p /. 2.0R) b v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p x v) as (pure False);
        unreachable ()
      } else {
        rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p x v) as (asn1_adb_rel key_k (hd2 :: tl2) p b (AL.ady_tail_val kx y (hd2 :: tl2) v ()));
        sht b #p #(AL.ady_tail_val kx y (hd2 :: tl2) v ());
        rewrite (asn1_adb_rel key_k (hd2 :: tl2) (p /. 2.0R) b (AL.ady_tail_val kx y (hd2 :: tl2) v ()) ** asn1_adb_rel key_k (hd2 :: tl2) (p /. 2.0R) b (AL.ady_tail_val kx y (hd2 :: tl2) v ()))
          as (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) (p /. 2.0R) x v ** asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) (p /. 2.0R) x v)
      }
    }
  }
}

ghost
fn gather_adb_cons (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (g: gather_t (asn1_items_rel (dsnd y))) (gt: gather_t (asn1_adb_rel key_k (hd2 :: tl2)))
: gather_t #(asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) #(AL.ady key_k ((kx, y) :: hd2 :: tl2)) (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2))
= (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) None) (#p: perm) (#v: AL.ady key_k ((kx, y) :: hd2 :: tl2)) (#p': perm) (#v': AL.ady key_k ((kx, y) :: hd2 :: tl2))
{
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) = x;
  match x' {
    Inl a -> {
      adb_cons_inl_eq kx y hd2 tl2 p a v;
      adb_cons_inl_eq kx y hd2 tl2 p' a v';
      adb_cons_inl_eq kx y hd2 tl2 (p +. p') a v;
      if (dfst v = key_of_lit key_k kx) {
        if (dfst v' = key_of_lit key_k kx) {
          rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p x v ** asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p' x v')
            as (asn1_items_rel (dsnd y) p a (AL.ady_head_val kx y (hd2 :: tl2) v ()) ** asn1_items_rel (dsnd y) p' a (AL.ady_head_val kx y (hd2 :: tl2) v' ()));
          g a #p #(AL.ady_head_val kx y (hd2 :: tl2) v ()) #p' #(AL.ady_head_val kx y (hd2 :: tl2) v' ());
          ady_head_inj kx y (hd2 :: tl2) v v';
          rewrite (asn1_items_rel (dsnd y) (p +. p') a (AL.ady_head_val kx y (hd2 :: tl2) v ())) as (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) (p +. p') x v)
        } else {
          rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p' x v') as (pure False);
          unreachable ()
        }
      } else {
        rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p x v) as (pure False);
        unreachable ()
      }
    }
    Inr b -> {
      adb_cons_inr_eq kx y hd2 tl2 p b v;
      adb_cons_inr_eq kx y hd2 tl2 p' b v';
      adb_cons_inr_eq kx y hd2 tl2 (p +. p') b v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p x v) as (pure False);
        unreachable ()
      } else if (dfst v' = key_of_lit key_k kx) {
        rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p' x v') as (pure False);
        unreachable ()
      } else {
        rewrite (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p x v ** asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) p' x v')
          as (asn1_adb_rel key_k (hd2 :: tl2) p b (AL.ady_tail_val kx y (hd2 :: tl2) v ()) ** asn1_adb_rel key_k (hd2 :: tl2) p' b (AL.ady_tail_val kx y (hd2 :: tl2) v' ()));
        gt b #p #(AL.ady_tail_val kx y (hd2 :: tl2) v ()) #p' #(AL.ady_tail_val kx y (hd2 :: tl2) v' ());
        ady_tail_inj kx y (hd2 :: tl2) v v';
        rewrite (asn1_adb_rel key_k (hd2 :: tl2) (p +. p') b (AL.ady_tail_val kx y (hd2 :: tl2) v ())) as (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) (p +. p') x v)
      }
    }
  }
}

(* With a fallback *)

let fbr_eq (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm) (z: PA.fbt key_k fb) (key: asn1_terminal_t key_k) (v: PA.fbs fb)
: Lemma (PA.fbr key_k fb pm z key v == (asn1_terminal_rel key_k pm (fst z) key ** asn1_items_rel (dsnd fb) pm (snd z) v))
= ()

ghost
fn share_fbr (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (shk: share_t (asn1_terminal_rel key_k)) (shi: share_t (asn1_items_rel (dsnd fb)))
  (z: PA.fbt key_k fb) (#p: perm) (#key: asn1_terminal_t key_k) (#v: PA.fbs fb)
requires PA.fbr key_k fb p z key v
ensures PA.fbr key_k fb (p /. 2.0R) z key v ** PA.fbr key_k fb (p /. 2.0R) z key v
{
  fbr_eq key_k fb p z key v;
  fbr_eq key_k fb (p /. 2.0R) z key v;
  rewrite (PA.fbr key_k fb p z key v) as (asn1_terminal_rel key_k p (fst z) key ** asn1_items_rel (dsnd fb) p (snd z) v);
  shk (fst z) #p #key;
  shi (snd z) #p #v;
  rewrite (asn1_terminal_rel key_k (p /. 2.0R) (fst z) key ** asn1_items_rel (dsnd fb) (p /. 2.0R) (snd z) v) as (PA.fbr key_k fb (p /. 2.0R) z key v);
  rewrite (asn1_terminal_rel key_k (p /. 2.0R) (fst z) key ** asn1_items_rel (dsnd fb) (p /. 2.0R) (snd z) v) as (PA.fbr key_k fb (p /. 2.0R) z key v)
}

ghost
fn gather_fbr (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (gk: gather_t (asn1_terminal_rel key_k)) (gi: gather_t (asn1_items_rel (dsnd fb)))
  (z: PA.fbt key_k fb) (#p: perm) (#key: asn1_terminal_t key_k) (#v: PA.fbs fb) (#p': perm) (#key': asn1_terminal_t key_k) (#v': PA.fbs fb)
requires PA.fbr key_k fb p z key v ** PA.fbr key_k fb p' z key' v'
ensures PA.fbr key_k fb (p +. p') z key v ** pure (key == key' /\ v == v')
{
  fbr_eq key_k fb p z key v;
  fbr_eq key_k fb p' z key' v';
  fbr_eq key_k fb (p +. p') z key v;
  rewrite (PA.fbr key_k fb p z key v) as (asn1_terminal_rel key_k p (fst z) key ** asn1_items_rel (dsnd fb) p (snd z) v);
  rewrite (PA.fbr key_k fb p' z key' v') as (asn1_terminal_rel key_k p' (fst z) key' ** asn1_items_rel (dsnd fb) p' (snd z) v');
  gk (fst z) #p #key #p' #key';
  gi (snd z) #p #v #p' #v';
  rewrite (asn1_terminal_rel key_k (p +. p') (fst z) key ** asn1_items_rel (dsnd fb) (p +. p') (snd z) v) as (PA.fbr key_k fb (p +. p') z key v)
}

let afb_nil_eq (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm) (z: PA.fbt key_k fb) (v: AL.ady_fb key_k [] fb)
: Lemma (PA.afb_rel key_k [] fb pm z v == PA.fbr key_k fb pm z (dfst v) (AL.ady_fb_nil_val fb v))
= PA.afb_rel_nil_eq fb pm (fst z) (snd z) v

let afb_single_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady_fb key_k [(kx, y)] fb)
: Lemma (PA.afb_rel key_k [(kx, y)] fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) a) v ==
    (if dfst v = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val kx y [] fb v ()) else pure False))
= let (| key, w |) = v in
  PA.afb_rel_single_inl_aux kx y fb pm a key w

let afb_single_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (b: PA.fbt key_k fb) (v: AL.ady_fb key_k [(kx, y)] fb)
: Lemma (PA.afb_rel key_k [(kx, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else PA.fbr key_k fb pm b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ()))))
= let (| key, w |) = v in
  PA.afb_rel_single_inr_aux kx y fb pm b key w

let afb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
: Lemma (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) a) v ==
    (if dfst v = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()) else pure False))
= let (| key, w |) = v in
  PA.afb_rel_cons_inl_aux kx y hd2 tl2 fb pm a key w

let afb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
: Lemma (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else PA.afb_rel key_k (hd2 :: tl2) fb pm b (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ())))
= let (| key, w |) = v in
  PA.afb_rel_cons_inr_aux kx y hd2 tl2 fb pm b key w

let ady_fb_nil_inj (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (v v': AL.ady_fb key_k [] fb)
: Lemma (requires dfst v == dfst v' /\ AL.ady_fb_nil_val fb v == AL.ady_fb_nil_val fb v')
  (ensures v == v')
= ()

let ady_fb_head_inj (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v v': AL.ady_fb key_k ((kx, y) :: tl) fb)
: Lemma (requires dfst v == key_of_lit key_k kx /\ dfst v' == key_of_lit key_k kx /\ AL.ady_fb_head_val kx y tl fb v () == AL.ady_fb_head_val kx y tl fb v' ())
  (ensures v == v')
= ()

let ady_fb_tail_inj (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v v': AL.ady_fb key_k ((kx, y) :: tl) fb)
: Lemma (requires dfst v <> key_of_lit key_k kx /\ dfst v' <> key_of_lit key_k kx /\ AL.ady_fb_tail_val kx y tl fb v () == AL.ady_fb_tail_val kx y tl fb v' ())
  (ensures v == v')
= ()

let ady_fb_single_inr_inj (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk)
  (v v': AL.ady_fb key_k [(kx, y)] fb)
: Lemma (requires dfst v <> key_of_lit key_k kx /\ dfst v' <> key_of_lit key_k kx /\ dfst v == dfst v' /\
    AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ()) == AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v' ()))
  (ensures v == v')
= ()

ghost
fn share_afb_nil (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (shk: share_t (asn1_terminal_rel key_k)) (shi: share_t (asn1_items_rel (dsnd fb)))
: share_t #(asn1_adb_suffix_impl_t key_k [] (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k [] fb) (PA.afb_rel key_k [] fb)
= (x: asn1_adb_suffix_impl_t key_k [] (Some (PA.fbt key_k fb))) (#p: perm) (#v: AL.ady_fb key_k [] fb)
{
  let z : PA.fbt key_k fb = x;
  afb_nil_eq fb p z v;
  afb_nil_eq fb (p /. 2.0R) z v;
  rewrite (PA.afb_rel key_k [] fb p x v) as (PA.fbr key_k fb p z (dfst v) (AL.ady_fb_nil_val fb v));
  share_fbr key_k fb shk shi z;
  rewrite (PA.fbr key_k fb (p /. 2.0R) z (dfst v) (AL.ady_fb_nil_val fb v) ** PA.fbr key_k fb (p /. 2.0R) z (dfst v) (AL.ady_fb_nil_val fb v))
    as (PA.afb_rel key_k [] fb (p /. 2.0R) x v ** PA.afb_rel key_k [] fb (p /. 2.0R) x v)
}

ghost
fn gather_afb_nil (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (gk: gather_t (asn1_terminal_rel key_k)) (gi: gather_t (asn1_items_rel (dsnd fb)))
: gather_t #(asn1_adb_suffix_impl_t key_k [] (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k [] fb) (PA.afb_rel key_k [] fb)
= (x: asn1_adb_suffix_impl_t key_k [] (Some (PA.fbt key_k fb))) (#p: perm) (#v: AL.ady_fb key_k [] fb) (#p': perm) (#v': AL.ady_fb key_k [] fb)
{
  let z : PA.fbt key_k fb = x;
  afb_nil_eq fb p z v;
  afb_nil_eq fb p' z v';
  afb_nil_eq fb (p +. p') z v;
  rewrite (PA.afb_rel key_k [] fb p x v ** PA.afb_rel key_k [] fb p' x v')
    as (PA.fbr key_k fb p z (dfst v) (AL.ady_fb_nil_val fb v) ** PA.fbr key_k fb p' z (dfst v') (AL.ady_fb_nil_val fb v'));
  gather_fbr key_k fb gk gi z #p #(dfst v) #(AL.ady_fb_nil_val fb v) #p' #(dfst v') #(AL.ady_fb_nil_val fb v');
  ady_fb_nil_inj fb v v';
  rewrite (PA.fbr key_k fb (p +. p') z (dfst v) (AL.ady_fb_nil_val fb v)) as (PA.afb_rel key_k [] fb (p +. p') x v)
}

ghost
fn share_afb_single (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk)
  (sh: share_t (asn1_items_rel (dsnd y))) (shk: share_t (asn1_terminal_rel key_k)) (shi: share_t (asn1_items_rel (dsnd fb)))
: share_t #(asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k [(kx, y)] fb) (PA.afb_rel key_k [(kx, y)] fb)
= (x: asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) (#p: perm) (#v: AL.ady_fb key_k [(kx, y)] fb)
{
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (PA.fbt key_k fb) = x;
  match x' {
    Inl a -> {
      afb_single_inl_eq kx y fb p a v;
      afb_single_inl_eq kx y fb (p /. 2.0R) a v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (PA.afb_rel key_k [(kx, y)] fb p x v) as (asn1_items_rel (dsnd y) p a (AL.ady_fb_head_val kx y [] fb v ()));
        sh a #p #(AL.ady_fb_head_val kx y [] fb v ());
        rewrite (asn1_items_rel (dsnd y) (p /. 2.0R) a (AL.ady_fb_head_val kx y [] fb v ()) ** asn1_items_rel (dsnd y) (p /. 2.0R) a (AL.ady_fb_head_val kx y [] fb v ()))
          as (PA.afb_rel key_k [(kx, y)] fb (p /. 2.0R) x v ** PA.afb_rel key_k [(kx, y)] fb (p /. 2.0R) x v)
      } else {
        rewrite (PA.afb_rel key_k [(kx, y)] fb p x v) as (pure False);
        unreachable ()
      }
    }
    Inr b -> {
      afb_single_inr_eq kx y fb p b v;
      afb_single_inr_eq kx y fb (p /. 2.0R) b v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (PA.afb_rel key_k [(kx, y)] fb p x v) as (pure False);
        unreachable ()
      } else {
        rewrite (PA.afb_rel key_k [(kx, y)] fb p x v) as (PA.fbr key_k fb p b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ())));
        share_fbr key_k fb shk shi b;
        rewrite (PA.fbr key_k fb (p /. 2.0R) b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ())) ** PA.fbr key_k fb (p /. 2.0R) b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ())))
          as (PA.afb_rel key_k [(kx, y)] fb (p /. 2.0R) x v ** PA.afb_rel key_k [(kx, y)] fb (p /. 2.0R) x v)
      }
    }
  }
}

ghost
fn gather_afb_single (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk)
  (g: gather_t (asn1_items_rel (dsnd y))) (gk: gather_t (asn1_terminal_rel key_k)) (gi: gather_t (asn1_items_rel (dsnd fb)))
: gather_t #(asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k [(kx, y)] fb) (PA.afb_rel key_k [(kx, y)] fb)
= (x: asn1_adb_suffix_impl_t key_k [(kx, y)] (Some (PA.fbt key_k fb))) (#p: perm) (#v: AL.ady_fb key_k [(kx, y)] fb) (#p': perm) (#v': AL.ady_fb key_k [(kx, y)] fb)
{
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (PA.fbt key_k fb) = x;
  match x' {
    Inl a -> {
      afb_single_inl_eq kx y fb p a v;
      afb_single_inl_eq kx y fb p' a v';
      afb_single_inl_eq kx y fb (p +. p') a v;
      if (dfst v = key_of_lit key_k kx) {
        if (dfst v' = key_of_lit key_k kx) {
          rewrite (PA.afb_rel key_k [(kx, y)] fb p x v ** PA.afb_rel key_k [(kx, y)] fb p' x v')
            as (asn1_items_rel (dsnd y) p a (AL.ady_fb_head_val kx y [] fb v ()) ** asn1_items_rel (dsnd y) p' a (AL.ady_fb_head_val kx y [] fb v' ()));
          g a #p #(AL.ady_fb_head_val kx y [] fb v ()) #p' #(AL.ady_fb_head_val kx y [] fb v' ());
          ady_fb_head_inj kx y [] fb v v';
          rewrite (asn1_items_rel (dsnd y) (p +. p') a (AL.ady_fb_head_val kx y [] fb v ())) as (PA.afb_rel key_k [(kx, y)] fb (p +. p') x v)
        } else {
          rewrite (PA.afb_rel key_k [(kx, y)] fb p' x v') as (pure False);
          unreachable ()
        }
      } else {
        rewrite (PA.afb_rel key_k [(kx, y)] fb p x v) as (pure False);
        unreachable ()
      }
    }
    Inr b -> {
      afb_single_inr_eq kx y fb p b v;
      afb_single_inr_eq kx y fb p' b v';
      afb_single_inr_eq kx y fb (p +. p') b v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (PA.afb_rel key_k [(kx, y)] fb p x v) as (pure False);
        unreachable ()
      } else if (dfst v' = key_of_lit key_k kx) {
        rewrite (PA.afb_rel key_k [(kx, y)] fb p' x v') as (pure False);
        unreachable ()
      } else {
        rewrite (PA.afb_rel key_k [(kx, y)] fb p x v ** PA.afb_rel key_k [(kx, y)] fb p' x v')
          as (PA.fbr key_k fb p b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ())) ** PA.fbr key_k fb p' b (dfst v') (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v' ())));
        gather_fbr key_k fb gk gi b #p #(dfst v) #(AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ())) #p' #(dfst v') #(AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v' ()));
        ady_fb_single_inr_inj kx y fb v v';
        rewrite (PA.fbr key_k fb (p +. p') b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ()))) as (PA.afb_rel key_k [(kx, y)] fb (p +. p') x v)
      }
    }
  }
}

#push-options "--z3rlimit 64"
ghost
fn share_afb_cons (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (sh: share_t (asn1_items_rel (dsnd y))) (sht: share_t (PA.afb_rel key_k (hd2 :: tl2) fb))
: share_t #(asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb) (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb)
= (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) (#p: perm) (#v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
{
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) = x;
  match x' {
    Inl a -> {
      afb_cons_inl_eq kx y hd2 tl2 fb p a v;
      afb_cons_inl_eq kx y hd2 tl2 fb (p /. 2.0R) a v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p x v) as (asn1_items_rel (dsnd y) p a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()));
        sh a #p #(AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ());
        rewrite (asn1_items_rel (dsnd y) (p /. 2.0R) a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()) ** asn1_items_rel (dsnd y) (p /. 2.0R) a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()))
          as (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb (p /. 2.0R) x v ** PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb (p /. 2.0R) x v)
      } else {
        rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p x v) as (pure False);
        unreachable ()
      }
    }
    Inr b -> {
      afb_cons_inr_eq kx y hd2 tl2 fb p b v;
      afb_cons_inr_eq kx y hd2 tl2 fb (p /. 2.0R) b v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p x v) as (pure False);
        unreachable ()
      } else {
        rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p x v) as (PA.afb_rel key_k (hd2 :: tl2) fb p b (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ()));
        sht b #p #(AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ());
        rewrite (PA.afb_rel key_k (hd2 :: tl2) fb (p /. 2.0R) b (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ()) ** PA.afb_rel key_k (hd2 :: tl2) fb (p /. 2.0R) b (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ()))
          as (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb (p /. 2.0R) x v ** PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb (p /. 2.0R) x v)
      }
    }
  }
}

ghost
fn gather_afb_cons (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (g: gather_t (asn1_items_rel (dsnd y))) (gt: gather_t (PA.afb_rel key_k (hd2 :: tl2) fb))
: gather_t #(asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) #(AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb) (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb)
= (x: asn1_adb_suffix_impl_t key_k ((kx, y) :: hd2 :: tl2) (Some (PA.fbt key_k fb))) (#p: perm) (#v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb) (#p': perm) (#v': AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
{
  let x' : either (asn1_items_impl_t (Mkdtuple2?._2 y)) (asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) = x;
  match x' {
    Inl a -> {
      afb_cons_inl_eq kx y hd2 tl2 fb p a v;
      afb_cons_inl_eq kx y hd2 tl2 fb p' a v';
      afb_cons_inl_eq kx y hd2 tl2 fb (p +. p') a v;
      if (dfst v = key_of_lit key_k kx) {
        if (dfst v' = key_of_lit key_k kx) {
          rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p x v ** PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p' x v')
            as (asn1_items_rel (dsnd y) p a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()) ** asn1_items_rel (dsnd y) p' a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v' ()));
          g a #p #(AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()) #p' #(AL.ady_fb_head_val kx y (hd2 :: tl2) fb v' ());
          ady_fb_head_inj kx y (hd2 :: tl2) fb v v';
          rewrite (asn1_items_rel (dsnd y) (p +. p') a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ())) as (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb (p +. p') x v)
        } else {
          rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p' x v') as (pure False);
          unreachable ()
        }
      } else {
        rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p x v) as (pure False);
        unreachable ()
      }
    }
    Inr b -> {
      afb_cons_inr_eq kx y hd2 tl2 fb p b v;
      afb_cons_inr_eq kx y hd2 tl2 fb p' b v';
      afb_cons_inr_eq kx y hd2 tl2 fb (p +. p') b v;
      if (dfst v = key_of_lit key_k kx) {
        rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p x v) as (pure False);
        unreachable ()
      } else if (dfst v' = key_of_lit key_k kx) {
        rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p' x v') as (pure False);
        unreachable ()
      } else {
        rewrite (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p x v ** PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb p' x v')
          as (PA.afb_rel key_k (hd2 :: tl2) fb p b (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ()) ** PA.afb_rel key_k (hd2 :: tl2) fb p' b (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v' ()));
        gt b #p #(AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ()) #p' #(AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v' ());
        ady_fb_tail_inj kx y (hd2 :: tl2) fb v v';
        rewrite (PA.afb_rel key_k (hd2 :: tl2) fb (p +. p') b (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ())) as (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb (p +. p') x v)
      }
    }
  }
}
#pop-options

(* The shares of a whole schema *)

let rec share_content (k: asn1_content_k) (u: squash (wsupported_content k))
: Tot (share_t (asn1_content_rel k)) (decreases k)
= match k with
  | ASN1_TERMINAL k' ->
    content_terminal_equiv k';
    share_ext (asn1_terminal_rel k') (asn1_content_rel (ASN1_TERMINAL k')) () (share_terminal k')
  | ASN1_RESTRICTED_TERMINAL k' r -> share_restricted k' r (share_terminal k')
  | ASN1_PREFIXED k' ->
    content_prefixed_equiv k';
    share_ext (asn1_rel k') (asn1_content_rel (ASN1_PREFIXED k')) () (share_k k' ())
  | ASN1_SEQUENCE gitems ->
    content_sequence_equiv gitems;
    share_ext (asn1_items_rel (dsnd gitems)) (asn1_content_rel (ASN1_SEQUENCE gitems)) () (share_items (dsnd gitems) ())
  | ASN1_SET ids items pf ->
    content_set_equiv ids items pf;
    share_ext (asn1_items_rel items) (asn1_content_rel (ASN1_SET ids items pf)) () (share_items items ())
  | ASN1_SEQUENCE_OF ne k' -> share_seq_of ne k' (share_k k' ())
  | ASN1_SET_OF ne k' -> share_set_of ne k' (share_k k' ())
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      adb_none_equiv ipd prefix kid key_k ls pf pf';
      share_ext (asn1_items_any_rel prefix (asn1_adb_rel key_k ls)) (asn1_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf')) ()
        (share_items_any prefix () (asn1_adb_rel key_k ls) (share_adb key_k ls ()))
    | Some fb ->
      adb_some_equiv ipd prefix kid key_k ls fb pf pf';
      share_ext (asn1_items_any_rel prefix (PA.afb_rel key_k ls fb)) (asn1_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf')) ()
        (share_items_any prefix () (PA.afb_rel key_k ls fb) (share_afb key_k ls () fb (share_terminal key_k) (share_items (dsnd fb) ())))
    end

and share_adb (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u: squash (wsupported_ls ls))
: Tot (share_t (asn1_adb_rel key_k ls)) (decreases ls)
= match ls with
  | [] -> share_adb_nil key_k
  | [(kx, y)] -> share_adb_single kx y (share_items (dsnd y) ())
  | (kx, y) :: hd2 :: tl2 -> share_adb_cons kx y hd2 tl2 (share_items (dsnd y) ()) (share_adb key_k (hd2 :: tl2) ())

and share_afb (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u: squash (wsupported_ls ls)) (fb: asn1_gen_items_lk)
  (xk: share_t (asn1_terminal_rel key_k)) (xi: share_t (asn1_items_rel (dsnd fb)))
: Tot (share_t (PA.afb_rel key_k ls fb)) (decreases ls)
= match ls with
  | [] -> share_afb_nil key_k fb xk xi
  | [(kx, y)] -> share_afb_single kx y fb (share_items (dsnd y) ()) xk xi
  | (kx, y) :: hd2 :: tl2 -> share_afb_cons kx y hd2 tl2 fb (share_items (dsnd y) ()) (share_afb key_k (hd2 :: tl2) () fb xk xi)

and share_items_any (#i: _) (ls: asn1_gen_items_l i) (u: squash (wsupported_items ls)) (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs) (xs: share_t sfxr)
: Tot (share_t (asn1_items_any_rel ls sfxr)) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_any_nil_equiv sfxr;
    share_ext sfxr (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr) () xs
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_any_single_equiv dk sfxr;
    share_ext (prel_pair (asn1_decorated_rel dk) sfxr) (asn1_items_any_rel (PS.single dk) sfxr) ()
      (share_pair (asn1_decorated_rel dk) sfxr (share_dec dk ()) xs)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_any_cons_equiv dk dk2 tl2 sfxr;
    share_ext (prel_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr)) (asn1_items_any_rel (PS.cons2 dk dk2 tl2) sfxr) ()
      (share_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr) (share_dec dk ()) (share_items_any (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) () sfxr xs))

and share_lc (lc: list (asn1_id_t & asn1_content_k)) (u: squash (wsupported_lc lc))
: Tot (share_t (asn1_lc_rel lc)) (decreases lc)
= match lc with
  | [] -> share_lc_nil ()
  | [(id', c)] -> share_lc_single id' c (share_content c ())
  | (id', c) :: hd2 :: tl2 -> share_lc_cons id' c hd2 tl2 (share_content c ()) (share_lc (hd2 :: tl2) ())

and share_k (#s: _) (k: asn1_k s) (u: squash (wsupported_k k))
: Tot (share_t (asn1_rel k)) (decreases k)
= match k with
  | ASN1_ILC id k' ->
    rel_ilc_equiv id k';
    share_ext (asn1_content_rel k') (asn1_rel (ASN1_ILC id k')) () (share_content k' ())
  | ASN1_CHOICE_ILC lc pf ->
    rel_choice_equiv lc pf;
    share_ext (asn1_lc_rel lc) (asn1_rel (ASN1_CHOICE_ILC lc pf)) () (share_lc lc ())
  | ASN1_ANY_ILC ->
    rel_any_equiv ();
    share_ext (prel_slice_ser asn1_value_enc) (asn1_rel ASN1_ANY_ILC) () (share_any ())

and share_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (wsupported_dec dk))
: Tot (share_t (asn1_decorated_rel dk)) (decreases dk)
= match dk with
  | ASN1_PLAIN_ILC k ->
    dec_plain_equiv k;
    share_ext (asn1_rel k) (asn1_decorated_rel (ASN1_PLAIN_ILC k)) () (share_k k ())
  | ASN1_OPTION_ILC k ->
    dec_option_equiv k;
    share_ext (prel_option (asn1_rel k)) (asn1_decorated_rel (ASN1_OPTION_ILC k)) () (share_option (asn1_rel k) (share_k k ()))
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    dec_default_equiv id0 defv;
    share_ext (prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)) () (share_default (asn1_terminal_rel k) (key_of_lit k defv) (share_terminal k))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    dec_default_restricted_equiv id0 r defv;
    share_ext (prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)) () (share_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv) (share_restricted k r (share_terminal k)))

and share_items (#i: _) (ls: asn1_gen_items_l i) (u: squash (wsupported_items ls))
: Tot (share_t (asn1_items_rel ls)) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_nil_equiv ();
    share_ext (prel_emp unit unit) (asn1_items_rel ASN1_GEN_ITEMS_NIL) () (share_emp_unit ())
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_single_equiv dk;
    share_ext (asn1_decorated_rel dk) (asn1_items_rel (PS.single dk)) () (share_dec dk ())
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_cons_equiv dk dk2 tl2;
    share_ext (prel_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (asn1_items_rel (PS.cons2 dk dk2 tl2)) ()
      (share_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (share_dec dk ()) (share_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ()))

(* The gathers of a whole schema *)

let rec gather_content (k: asn1_content_k) (u: squash (wsupported_content k))
: Tot (gather_t (asn1_content_rel k)) (decreases k)
= match k with
  | ASN1_TERMINAL k' ->
    content_terminal_equiv k';
    gather_ext (asn1_terminal_rel k') (asn1_content_rel (ASN1_TERMINAL k')) () (gather_terminal k')
  | ASN1_RESTRICTED_TERMINAL k' r -> gather_restricted k' r (gather_terminal k')
  | ASN1_PREFIXED k' ->
    content_prefixed_equiv k';
    gather_ext (asn1_rel k') (asn1_content_rel (ASN1_PREFIXED k')) () (gather_k k' ())
  | ASN1_SEQUENCE gitems ->
    content_sequence_equiv gitems;
    gather_ext (asn1_items_rel (dsnd gitems)) (asn1_content_rel (ASN1_SEQUENCE gitems)) () (gather_items (dsnd gitems) ())
  | ASN1_SET ids items pf ->
    content_set_equiv ids items pf;
    gather_ext (asn1_items_rel items) (asn1_content_rel (ASN1_SET ids items pf)) () (gather_items items ())
  | ASN1_SEQUENCE_OF ne k' -> gather_seq_of ne k' (gather_k k' ())
  | ASN1_SET_OF ne k' -> gather_set_of ne k' (gather_k k' ())
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      adb_none_equiv ipd prefix kid key_k ls pf pf';
      gather_ext (asn1_items_any_rel prefix (asn1_adb_rel key_k ls)) (asn1_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf')) ()
        (gather_items_any prefix () (asn1_adb_rel key_k ls) (gather_adb key_k ls ()))
    | Some fb ->
      adb_some_equiv ipd prefix kid key_k ls fb pf pf';
      gather_ext (asn1_items_any_rel prefix (PA.afb_rel key_k ls fb)) (asn1_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf')) ()
        (gather_items_any prefix () (PA.afb_rel key_k ls fb) (gather_afb key_k ls () fb (gather_terminal key_k) (gather_items (dsnd fb) ())))
    end

and gather_adb (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u: squash (wsupported_ls ls))
: Tot (gather_t (asn1_adb_rel key_k ls)) (decreases ls)
= match ls with
  | [] -> gather_adb_nil key_k
  | [(kx, y)] -> gather_adb_single kx y (gather_items (dsnd y) ())
  | (kx, y) :: hd2 :: tl2 -> gather_adb_cons kx y hd2 tl2 (gather_items (dsnd y) ()) (gather_adb key_k (hd2 :: tl2) ())

and gather_afb (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u: squash (wsupported_ls ls)) (fb: asn1_gen_items_lk)
  (xk: gather_t (asn1_terminal_rel key_k)) (xi: gather_t (asn1_items_rel (dsnd fb)))
: Tot (gather_t (PA.afb_rel key_k ls fb)) (decreases ls)
= match ls with
  | [] -> gather_afb_nil key_k fb xk xi
  | [(kx, y)] -> gather_afb_single kx y fb (gather_items (dsnd y) ()) xk xi
  | (kx, y) :: hd2 :: tl2 -> gather_afb_cons kx y hd2 tl2 fb (gather_items (dsnd y) ()) (gather_afb key_k (hd2 :: tl2) () fb xk xi)

and gather_items_any (#i: _) (ls: asn1_gen_items_l i) (u: squash (wsupported_items ls)) (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs) (xs: gather_t sfxr)
: Tot (gather_t (asn1_items_any_rel ls sfxr)) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_any_nil_equiv sfxr;
    gather_ext sfxr (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr) () xs
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_any_single_equiv dk sfxr;
    gather_ext (prel_pair (asn1_decorated_rel dk) sfxr) (asn1_items_any_rel (PS.single dk) sfxr) ()
      (gather_pair (asn1_decorated_rel dk) sfxr (gather_dec dk ()) xs)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_any_cons_equiv dk dk2 tl2 sfxr;
    gather_ext (prel_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr)) (asn1_items_any_rel (PS.cons2 dk dk2 tl2) sfxr) ()
      (gather_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr) (gather_dec dk ()) (gather_items_any (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) () sfxr xs))

and gather_lc (lc: list (asn1_id_t & asn1_content_k)) (u: squash (wsupported_lc lc))
: Tot (gather_t (asn1_lc_rel lc)) (decreases lc)
= match lc with
  | [] -> gather_lc_nil ()
  | [(id', c)] -> gather_lc_single id' c (gather_content c ())
  | (id', c) :: hd2 :: tl2 -> gather_lc_cons id' c hd2 tl2 (gather_content c ()) (gather_lc (hd2 :: tl2) ())

and gather_k (#s: _) (k: asn1_k s) (u: squash (wsupported_k k))
: Tot (gather_t (asn1_rel k)) (decreases k)
= match k with
  | ASN1_ILC id k' ->
    rel_ilc_equiv id k';
    gather_ext (asn1_content_rel k') (asn1_rel (ASN1_ILC id k')) () (gather_content k' ())
  | ASN1_CHOICE_ILC lc pf ->
    rel_choice_equiv lc pf;
    gather_ext (asn1_lc_rel lc) (asn1_rel (ASN1_CHOICE_ILC lc pf)) () (gather_lc lc ())
  | ASN1_ANY_ILC ->
    rel_any_equiv ();
    gather_ext (prel_slice_ser asn1_value_enc) (asn1_rel ASN1_ANY_ILC) () (gather_any ())

and gather_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (wsupported_dec dk))
: Tot (gather_t (asn1_decorated_rel dk)) (decreases dk)
= match dk with
  | ASN1_PLAIN_ILC k ->
    dec_plain_equiv k;
    gather_ext (asn1_rel k) (asn1_decorated_rel (ASN1_PLAIN_ILC k)) () (gather_k k ())
  | ASN1_OPTION_ILC k ->
    dec_option_equiv k;
    gather_ext (prel_option (asn1_rel k)) (asn1_decorated_rel (ASN1_OPTION_ILC k)) () (gather_option (asn1_rel k) (gather_k k ()))
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    dec_default_equiv id0 defv;
    gather_ext (prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)) () (gather_default (asn1_terminal_rel k) (key_of_lit k defv) (gather_terminal k))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    dec_default_restricted_equiv id0 r defv;
    gather_ext (prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)) () (gather_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv) (gather_restricted k r (gather_terminal k)))

and gather_items (#i: _) (ls: asn1_gen_items_l i) (u: squash (wsupported_items ls))
: Tot (gather_t (asn1_items_rel ls)) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_nil_equiv ();
    gather_ext (prel_emp unit unit) (asn1_items_rel ASN1_GEN_ITEMS_NIL) () (gather_emp_unit ())
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_single_equiv dk;
    gather_ext (asn1_decorated_rel dk) (asn1_items_rel (PS.single dk)) () (gather_dec dk ())
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_cons_equiv dk dk2 tl2;
    gather_ext (prel_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (asn1_items_rel (PS.cons2 dk dk2 tl2)) ()
      (gather_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (gather_dec dk ()) (gather_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ()))

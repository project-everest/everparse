module CBOR.Pulse.Raw.EverParse.Access
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Type
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open CBOR.Pulse.Raw.EverParse.Match
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module U8 = FStar.UInt8
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module I = LowParse.PulseParse.Iterator

open CBOR.Pulse.Raw.EverParse.Read
open LowParse.Pulse.Base

(* Pure prop relating cbor_raw constructors to raw_data_item constructors *)
let cbor_raw_match_cases_prop (x: cbor_raw) (y: raw_data_item) : prop =
  match x, y with
  | CBOR_Case_Int v, Int64 m _ -> v.cbor_int_type == m
  | CBOR_Case_Simple _, Simple _ -> True
  | CBOR_Case_String v, String m _ _ -> v.cbor_string_type == m
  | CBOR_Case_Array _, Array _ _ -> True
  | CBOR_Case_Map _, Map _ _ -> True
  | CBOR_Case_Tagged _, Tagged _ _ -> True
  | CBOR_Case_Tagged_Serialized _, Tagged _ _ -> True
  | _, _ -> False

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

let cbor_raw_match_cases_prop_of_header
  (x: cbor_raw)
  (y: raw_data_item)
  (h: header)
  (_: squash (cbor_raw_get_header x == Some h))
  (_: squash (dfst (synth_raw_data_item_recip y) == h))
: Lemma (cbor_raw_match_cases_prop x y)
= ()

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_match_cases
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y
ensures cbor_raw_match pm x y ** pure (cbor_raw_match_cases_prop x y)
{
  // Unfold cbor_raw_match to cbor_raw_match_aux
  cbor_raw_match_unfold_aux x;
  // Unfold the chain of let-definitions to get the header pure fact
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  // Extract the header fact
  let the_prop = cbor_raw_get_header x ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
  let sq = elim_pure_explicit the_prop;
  // Prove cbor_raw_match_cases_prop
  cbor_raw_match_cases_prop_of_header x (Ghost.reveal y)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))) sq ();
  // Refold everything
  intro_pure the_prop sq;
  rewrite
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  // Refold cbor_raw_match
  cbor_raw_match_fold_aux x;
  ()
}
```

#pop-options

inline_for_extraction
let cbor_raw_major_type (xl: cbor_raw) : Tot (option major_type_t) =
  match xl with
  | CBOR_Case_Int v -> Some v.cbor_int_type
  | CBOR_Case_Simple _ -> Some cbor_major_type_simple_value
  | CBOR_Case_String v -> Some v.cbor_string_type
  | CBOR_Case_Array _ -> Some cbor_major_type_array
  | CBOR_Case_Map _ -> Some cbor_major_type_map
  | CBOR_Case_Tagged _ -> Some cbor_major_type_tagged
  | CBOR_Case_Tagged_Serialized _ -> Some cbor_major_type_tagged
  | CBOR_Case_Invalid -> None

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

let cbor_raw_major_type_correct_lemma
  (x: cbor_raw)
  (y: raw_data_item)
  (_: squash (cbor_raw_match_cases_prop x y))
: Lemma (cbor_raw_major_type x == Some (get_major_type y))
= ()

#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"

```pulse
fn cbor_raw_get_major_type
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y
returns res: major_type_t
ensures cbor_raw_match pm x y ** pure (res == get_major_type y)
{
  cbor_raw_match_cases pm x;
  cbor_raw_major_type_correct_lemma x (Ghost.reveal y) ();
  let res = Some?.v (cbor_raw_major_type x);
  res
}
```

#pop-options

(* ======== String accessor ======== *)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

let cbor_raw_match_cases_prop_string_elim
  (x: cbor_raw) (y: raw_data_item)
  (_: squash (cbor_raw_match_cases_prop x y))
  (_: squash (CBOR_Case_String? x \/ String? y))
: Lemma (CBOR_Case_String? x /\ String? y)
= ()

let synth_string_major_type
  (y: raw_data_item) (_: squash (String? y))
: Lemma (
    let b = dfst (dfst (synth_raw_data_item_recip y)) in
    (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) == true
  )
= ()

let content_string_value
  (y: raw_data_item) (_: squash (String? y))
: Lemma (
    let b = dfst (dfst (synth_raw_data_item_recip y)) in
    let la = dsnd (dfst (synth_raw_data_item_recip y)) in
    let c = dsnd (synth_raw_data_item_recip y) in
    content_as_seq_u8 b la c == (String?.v y <: Seq.seq U8.t)
  )
= ()

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_get_string_content
  (pm: perm) (h: header) (v: cbor_string) (c: content h)
  (_: squash (
    let b = dfst h in
    (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) == true
  ))
requires
  cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_String v) c
ensures exists* (pm': perm) (vs: Seq.seq U8.t).
  S.pts_to v.cbor_string_ptr #pm' vs **
  trade
    (S.pts_to v.cbor_string_ptr #pm' vs)
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_String v) c) **
  pure (pm' == pm *. v.cbor_string_perm /\ vs == content_as_seq_u8 (dfst h) (dsnd h) c)
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  cbor_raw_match_content_eq_string cbor_raw_match parse_raw_data_item pm b la v c;
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_String v) c)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_String v) c);
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_String v) c)
    as
    (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c));
  intro
    (trade
      (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c))
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_String v) c))
    #emp
    fn _ {
      cbor_raw_match_content_eq_string cbor_raw_match parse_raw_data_item pm b la v c;
      header_eta h;
      rewrite
        (S.pts_to v.cbor_string_ptr #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c))
        as
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_String v) c);
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_String v) c)
        as
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_String v) c);
    };
}
```

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_get_string_content_false
  (pm: perm) (h: header) (xl: cbor_raw) (c: content h)
  (_: squash (
    let b = dfst h in
    ((b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) == true) /\
    ~(CBOR_Case_String? xl)
  ))
requires
  cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h xl c
ensures pure False
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h xl c)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) xl c);
  match xl {
    CBOR_Case_String v -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (| b, la |) (CBOR_Case_String v) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Invalid -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (| b, la |) CBOR_Case_Invalid c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Int i -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (| b, la |) (CBOR_Case_Int i) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Simple sv -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (| b, la |) (CBOR_Case_Simple sv) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Array a -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (| b, la |) (CBOR_Case_Array a) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Map m -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (| b, la |) (CBOR_Case_Map m) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Tagged t -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (| b, la |) (CBOR_Case_Tagged t) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Tagged_Serialized ts -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (| b, la |) (CBOR_Case_Tagged_Serialized ts) c)
        as (pure False);
      unreachable ()
    }
  }
}
```

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
fn cbor_raw_get_string
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
  (_: squash (CBOR_Case_String? x \/ String? (Ghost.reveal y)))
requires cbor_raw_match pm x y
returns s: S.slice U8.t
ensures exists* (pm': perm) (v: Seq.seq U8.t).
  S.pts_to s #pm' v **
  Trade.trade (S.pts_to s #pm' v) (cbor_raw_match pm x y) **
  pure (String? (Ghost.reveal y) /\ v == (String?.v (Ghost.reveal y) <: Seq.seq U8.t))
{
  cbor_raw_match_cases pm x;
  cbor_raw_match_cases_prop_string_elim x (Ghost.reveal y) () ();

  // Unfold cbor_raw_match to content level
  cbor_raw_match_unfold_aux x;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));

  synth_string_major_type (Ghost.reveal y) ();
  content_string_value (Ghost.reveal y) ();

  match x {
    CBOR_Case_String v -> {
      cbor_raw_get_string_content pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();

      // Now have: S.pts_to v.cbor_string_ptr #pm' vs **
      //           trade (S.pts_to ...) (cbor_raw_match_content ... h (CBOR_Case_String v) c)
      // Need: trade (S.pts_to ...) (cbor_raw_match pm (CBOR_Case_String v) y)
      // Compose with a trade from content to cbor_raw_match

      // Set up trade from content to cbor_raw_match
      intro
        (trade
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_String v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
          (cbor_raw_match pm (CBOR_Case_String v) y))
        #(pure (cbor_raw_get_header (CBOR_Case_String v) ==
               Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
        fn _ {
          rewrite
            (pure (cbor_raw_get_header (CBOR_Case_String v) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
            as
            (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get (CBOR_Case_String v)) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
          fold (cbor_raw_match_header
            (cbor_raw_id_proj.pair_proj_get (CBOR_Case_String v))
            (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
          fold (vmatch_dep_pair_with_proj
            cbor_raw_match_header
            cbor_raw_id_proj
            (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
            (CBOR_Case_String v)
            (synth_raw_data_item_recip (Ghost.reveal y)));
          fold (vmatch_synth
            (vmatch_dep_pair_with_proj
               cbor_raw_match_header
               cbor_raw_id_proj
               (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
            synth_raw_data_item_recip
            (CBOR_Case_String v) (Ghost.reveal y));
          fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm
            (CBOR_Case_String v) (Ghost.reveal y));
          cbor_raw_match_fold_aux (CBOR_Case_String v);
        };

      // Bind the existentials from the helper
      let pm' = pm *. v.cbor_string_perm;
      with _pm' _vs . assert (S.pts_to v.cbor_string_ptr #_pm' _vs);
      with _pm'' _vs' . assert (trade (S.pts_to v.cbor_string_ptr #_pm'' _vs')
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
          (CBOR_Case_String v)
          (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))));
      rewrite
        (trade (S.pts_to v.cbor_string_ptr #_pm'' _vs')
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_String v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
        as
        (trade (S.pts_to v.cbor_string_ptr #_pm' _vs)
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_String v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))));

      // Compose the two trades
      Trade.trans
        (S.pts_to v.cbor_string_ptr #_pm' _vs)
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
          (CBOR_Case_String v)
          (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
        (cbor_raw_match pm (CBOR_Case_String v) y);

      rewrite
        (trade (S.pts_to v.cbor_string_ptr #_pm' _vs)
          (cbor_raw_match pm (CBOR_Case_String v) y))
        as
        (trade (S.pts_to v.cbor_string_ptr #_pm' _vs)
          (cbor_raw_match pm x y));

      v.cbor_string_ptr
    }
    CBOR_Case_Invalid -> {
      cbor_raw_get_string_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        CBOR_Case_Invalid
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Int i -> {
      cbor_raw_get_string_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Int i)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Simple sv -> {
      cbor_raw_get_string_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Simple sv)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Array a -> {
      cbor_raw_get_string_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Array a)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Map m -> {
      cbor_raw_get_string_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Map m)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged t -> {
      cbor_raw_get_string_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Tagged t)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged_Serialized ts -> {
      cbor_raw_get_string_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Tagged_Serialized ts)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
  }
}
```

#pop-options

(* ======== String unfold helper for constructors ======== *)

(* Ghost fn that unfolds cbor_raw_match for a known CBOR_Case_String value
   to S.pts_to on the string slice, with a trade back to cbor_raw_match.
   Used by cbor_mk_string to build the reverse trade. *)

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_match_string_elim
  (str: cbor_string)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match pm (CBOR_Case_String str) xh
ensures exists* v .
  S.pts_to str.cbor_string_ptr #(pm *. str.cbor_string_perm) v **
  trade
    (S.pts_to str.cbor_string_ptr #(pm *. str.cbor_string_perm) v)
    (cbor_raw_match pm (CBOR_Case_String str) xh)
{
  let x : cbor_raw = CBOR_Case_String str;
  rewrite (cbor_raw_match pm (CBOR_Case_String str) xh)
    as (cbor_raw_match pm x xh);

  cbor_raw_match_cases pm x;
  cbor_raw_match_cases_prop_string_elim x (Ghost.reveal xh) () ();

  cbor_raw_match_unfold_aux x;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal xh));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));

  rewrite
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (pure (cbor_raw_get_header (CBOR_Case_String str) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));

  synth_string_major_type (Ghost.reveal xh) ();
  content_string_value (Ghost.reveal xh) ();

  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
      (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
      x
      (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))))
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
      (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
      (CBOR_Case_String str)
      (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))));

  cbor_raw_get_string_content pm
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
    str
    (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
    ();

  // Set up trade from content to cbor_raw_match
  intro
    (trade
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_String str)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))))
      (cbor_raw_match pm (CBOR_Case_String str) xh))
    #(pure (cbor_raw_get_header (CBOR_Case_String str) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    fn _ {
      rewrite
        (pure (cbor_raw_get_header (CBOR_Case_String str) ==
               Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
        as
        (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get (CBOR_Case_String str)) ==
               Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
      fold (cbor_raw_match_header
        (cbor_raw_id_proj.pair_proj_get (CBOR_Case_String str))
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
      fold (vmatch_dep_pair_with_proj
        cbor_raw_match_header
        cbor_raw_id_proj
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
        (CBOR_Case_String str)
        (synth_raw_data_item_recip (Ghost.reveal xh)));
      fold (vmatch_synth
        (vmatch_dep_pair_with_proj
           cbor_raw_match_header
           cbor_raw_id_proj
           (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
        synth_raw_data_item_recip
        (CBOR_Case_String str) (Ghost.reveal xh));
      fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm
        (CBOR_Case_String str) (Ghost.reveal xh));
      cbor_raw_match_fold_aux (CBOR_Case_String str);
    };

  // Bind the existentials
  with _pm' _vs . assert (S.pts_to str.cbor_string_ptr #_pm' _vs);
  with _pm'' _vs' . assert (trade (S.pts_to str.cbor_string_ptr #_pm'' _vs')
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
      (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
      (CBOR_Case_String str)
      (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))));
  rewrite
    (trade (S.pts_to str.cbor_string_ptr #_pm'' _vs')
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_String str)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (trade (S.pts_to str.cbor_string_ptr #_pm' _vs)
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
        (CBOR_Case_String str)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))));

  // Compose the two trades
  Trade.trans
    (S.pts_to str.cbor_string_ptr #_pm' _vs)
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
      (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
      (CBOR_Case_String str)
      (dsnd (synth_raw_data_item_recip (Ghost.reveal xh))))
    (cbor_raw_match pm (CBOR_Case_String str) xh);
}
```

#pop-options


(* ======== Tagged accessor ======== *)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

let cbor_raw_match_cases_prop_tagged_elim
  (x: cbor_raw) (y: raw_data_item)
  (_: squash (cbor_raw_match_cases_prop x y))
  (_: squash (CBOR_Case_Tagged? x \/ CBOR_Case_Tagged_Serialized? x \/ Tagged? y))
: Lemma ((CBOR_Case_Tagged? x \/ CBOR_Case_Tagged_Serialized? x) /\ Tagged? y)
= ()

let synth_tagged_major_type
  (y: raw_data_item) (_: squash (Tagged? y))
: Lemma (
    let b = dfst (dfst (synth_raw_data_item_recip y)) in
    b.major_type = cbor_major_type_tagged
  )
= ()

let content_tagged_payload
  (y: raw_data_item) (_: squash (Tagged? y))
: Lemma (
    content_as_raw_data_item
      (dfst (dfst (synth_raw_data_item_recip y)))
      (dsnd (dfst (synth_raw_data_item_recip y)))
      (dsnd (synth_raw_data_item_recip y))
    == Tagged?.v y
  )
= ()

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_get_tagged_content_tagged
  (pm: perm) (h: header) (v: cbor_tagged cbor_raw) (c: content h)
  (_: squash (
    let b = dfst h in
    b.major_type = cbor_major_type_tagged
  ))
requires
  cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Tagged v) c
ensures exists* (vl: cbor_raw).
  R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
  cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item (dfst h) (dsnd h) c) **
  trade
    (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
     cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item (dfst h) (dsnd h) c))
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Tagged v) c)
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  cbor_raw_match_content_eq_tagged cbor_raw_match parse_raw_data_item pm b la v c;
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Tagged v) c)
    as
    (cbor_tagged_content_slprop cbor_raw_match pm v (content_as_raw_data_item b la c));
  unfold (cbor_tagged_content_slprop cbor_raw_match pm v (content_as_raw_data_item b la c));
  unfold (vmatch_ref
    (fun (vl: cbor_raw) (vh: raw_data_item) ->
      cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl vh)
    ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
    (content_as_raw_data_item b la c));
  with vl . assert (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl);
  intro
    (trade
      (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
       cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c))
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Tagged v) c))
    #emp
    fn _ {
      fold (vmatch_ref
        (fun (vl: cbor_raw) (vh: raw_data_item) ->
          cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl vh)
        ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
        (content_as_raw_data_item b la c));
      fold (cbor_tagged_content_slprop cbor_raw_match pm v (content_as_raw_data_item b la c));
      cbor_raw_match_content_eq_tagged cbor_raw_match parse_raw_data_item pm b la v c;
      rewrite
        (cbor_tagged_content_slprop cbor_raw_match pm v (content_as_raw_data_item b la c))
        as
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Tagged v) c)
    };
  rewrite
    (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
     cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c))
    as
    (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
     cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item (dfst h) (dsnd h) c));
  rewrite
    (trade
      (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
       cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c))
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Tagged v) c))
    as
    (trade
      (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
       cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item (dfst h) (dsnd h) c))
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Tagged v) c))
}
```

```pulse
ghost fn cbor_raw_get_tagged_content_false
  (pm: perm) (h: header) (xl: cbor_raw) (c: content h)
  (_: squash (
    let b = dfst h in
    b.major_type = cbor_major_type_tagged /\
    ~ (CBOR_Case_Tagged? xl) /\
    ~ (CBOR_Case_Tagged_Serialized? xl)
  ))
requires
  cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h xl c
ensures
  pure False
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h xl c)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) xl c);
  match xl {
    CBOR_Case_Invalid -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) CBOR_Case_Invalid c)
        as (pure False)
    }
    CBOR_Case_Int i -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Int i) c)
        as (pure False)
    }
    CBOR_Case_Simple sv -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Simple sv) c)
        as (pure False)
    }
    CBOR_Case_String s -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_String s) c)
        as (pure False)
    }
    CBOR_Case_Array a -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Array a) c)
        as (pure False)
    }
    CBOR_Case_Map m -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Map m) c)
        as (pure False)
    }
    CBOR_Case_Tagged t -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Tagged t) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Tagged_Serialized ts -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Tagged_Serialized ts) c)
        as (pure False);
      unreachable ()
    }
  }
}
```

#pop-options

#push-options "--z3rlimit 1024 --fuel 2 --ifuel 2"

```pulse
fn cbor_raw_get_tagged_payload
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item) (f64: squash SZ.fits_u64)
  (_: squash (CBOR_Case_Tagged? x \/ CBOR_Case_Tagged_Serialized? x \/ Tagged? (Ghost.reveal y)))
requires cbor_raw_match pm x y
returns res: cbor_raw
ensures exists* (pm': perm) (payload: Ghost.erased raw_data_item).
  cbor_raw_match pm' res payload **
  Trade.trade (cbor_raw_match pm' res payload) (cbor_raw_match pm x y) **
  pure (Tagged? (Ghost.reveal y) /\
        Ghost.reveal payload == Tagged?.v (Ghost.reveal y))
{
  cbor_raw_match_cases pm x;
  cbor_raw_match_cases_prop_tagged_elim x (Ghost.reveal y) () ();

  // Unfold cbor_raw_match to content level
  cbor_raw_match_unfold_aux x;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));

  synth_tagged_major_type (Ghost.reveal y) ();
  content_tagged_payload (Ghost.reveal y) ();

  match x {
    CBOR_Case_Tagged v -> {
      cbor_raw_get_tagged_content_tagged pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();

      with vl . assert (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl);
      let res = R.read v.cbor_tagged_ptr;

      // Set up trade from content to cbor_raw_match
      intro
        (trade
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_Tagged v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
          (cbor_raw_match pm (CBOR_Case_Tagged v) y))
        #(pure (cbor_raw_get_header (CBOR_Case_Tagged v) ==
               Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
        fn _ {
          rewrite
            (pure (cbor_raw_get_header (CBOR_Case_Tagged v) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
            as
            (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get (CBOR_Case_Tagged v)) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
          fold (cbor_raw_match_header
            (cbor_raw_id_proj.pair_proj_get (CBOR_Case_Tagged v))
            (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
          fold (vmatch_dep_pair_with_proj
            cbor_raw_match_header
            cbor_raw_id_proj
            (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
            (CBOR_Case_Tagged v)
            (synth_raw_data_item_recip (Ghost.reveal y)));
          fold (vmatch_synth
            (vmatch_dep_pair_with_proj
               cbor_raw_match_header
               cbor_raw_id_proj
               (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
            synth_raw_data_item_recip
            (CBOR_Case_Tagged v) (Ghost.reveal y));
          fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm
            (CBOR_Case_Tagged v) (Ghost.reveal y));
          cbor_raw_match_fold_aux (CBOR_Case_Tagged v);
        };

      // Compose: (R.pts_to ** cbor_raw_match) → content → cbor_raw_match
      Trade.trans
        (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
         cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl
           (content_as_raw_data_item
             (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
             (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
             (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
          (CBOR_Case_Tagged v)
          (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
        (cbor_raw_match pm (CBOR_Case_Tagged v) y);

      // Split off cbor_raw_match from the pair, absorbing R.pts_to into the trade
      intro
        (trade
          (cbor_raw_match (pm *. v.cbor_tagged_payload_perm) res
            (content_as_raw_data_item
              (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
              (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
              (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
          (cbor_raw_match pm (CBOR_Case_Tagged v) y))
        #(R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) res **
          trade
            (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
             cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl
               (content_as_raw_data_item
                 (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
                 (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
                 (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
            (cbor_raw_match pm (CBOR_Case_Tagged v) y))
        fn _ {
          rewrite
            (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) res)
            as
            (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl);
          Trade.elim
            (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
             cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl
               (content_as_raw_data_item
                 (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
                 (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
                 (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
            (cbor_raw_match pm (CBOR_Case_Tagged v) y)
        };

      rewrite
        (trade
          (cbor_raw_match (pm *. v.cbor_tagged_payload_perm) res
            (content_as_raw_data_item
              (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
              (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
              (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
          (cbor_raw_match pm (CBOR_Case_Tagged v) y))
        as
        (trade
          (cbor_raw_match (pm *. v.cbor_tagged_payload_perm) res
            (Tagged?.v (Ghost.reveal y)))
          (cbor_raw_match pm x y));

      rewrite
        (cbor_raw_match (pm *. v.cbor_tagged_payload_perm) res
          (content_as_raw_data_item
            (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
        as
        (cbor_raw_match (pm *. v.cbor_tagged_payload_perm) res
          (Tagged?.v (Ghost.reveal y)));

      res
    }
    CBOR_Case_Tagged_Serialized ts -> {
      cbor_raw_match_content_eq_tagged_serialized cbor_raw_match parse_raw_data_item pm
        (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
        (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
        ts
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)));
      header_eta (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
          (CBOR_Case_Tagged_Serialized ts)
          (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
        as
        (PPB.pts_to_parsed_strong_prefix parse_raw_data_item ts.cbor_tagged_serialized_ptr
          #(pm *. ts.cbor_tagged_serialized_slice_perm)
          (content_as_raw_data_item
            (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))));

      let res = cbor_raw_read pm f64
        ts.cbor_tagged_serialized_ptr
        #(pm *. ts.cbor_tagged_serialized_slice_perm)
        #(content_as_raw_data_item
            (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y))));

      // Set up trade: pts_to_parsed_strong_prefix → content → cbor_raw_match
      intro
        (trade
          (PPB.pts_to_parsed_strong_prefix parse_raw_data_item ts.cbor_tagged_serialized_ptr
            #(pm *. ts.cbor_tagged_serialized_slice_perm)
            (content_as_raw_data_item
              (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
              (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
              (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
          (cbor_raw_match pm (CBOR_Case_Tagged_Serialized ts) y))
        #(pure (cbor_raw_get_header (CBOR_Case_Tagged_Serialized ts) ==
               Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
        fn _ {
          cbor_raw_match_content_eq_tagged_serialized cbor_raw_match parse_raw_data_item pm
            (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            ts
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)));
          header_eta (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
          rewrite
            (PPB.pts_to_parsed_strong_prefix parse_raw_data_item ts.cbor_tagged_serialized_ptr
              #(pm *. ts.cbor_tagged_serialized_slice_perm)
              (content_as_raw_data_item
                (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
                (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
                (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
            as
            (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
              (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
              (CBOR_Case_Tagged_Serialized ts)
              (dsnd (synth_raw_data_item_recip (Ghost.reveal y))));
          rewrite
            (pure (cbor_raw_get_header (CBOR_Case_Tagged_Serialized ts) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
            as
            (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get (CBOR_Case_Tagged_Serialized ts)) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
          fold (cbor_raw_match_header
            (cbor_raw_id_proj.pair_proj_get (CBOR_Case_Tagged_Serialized ts))
            (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
          fold (vmatch_dep_pair_with_proj
            cbor_raw_match_header
            cbor_raw_id_proj
            (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
            (CBOR_Case_Tagged_Serialized ts)
            (synth_raw_data_item_recip (Ghost.reveal y)));
          fold (vmatch_synth
            (vmatch_dep_pair_with_proj
               cbor_raw_match_header
               cbor_raw_id_proj
               (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
            synth_raw_data_item_recip
            (CBOR_Case_Tagged_Serialized ts) (Ghost.reveal y));
          fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm
            (CBOR_Case_Tagged_Serialized ts) (Ghost.reveal y));
          cbor_raw_match_fold_aux (CBOR_Case_Tagged_Serialized ts);
        };

      // Compose: cbor_raw_match pm res _ → pts_to_parsed → cbor_raw_match pm x y
      Trade.trans
        (cbor_raw_match pm res
          (content_as_raw_data_item
            (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
        (PPB.pts_to_parsed_strong_prefix parse_raw_data_item ts.cbor_tagged_serialized_ptr
          #(pm *. ts.cbor_tagged_serialized_slice_perm)
          (content_as_raw_data_item
            (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
        (cbor_raw_match pm (CBOR_Case_Tagged_Serialized ts) y);

      rewrite
        (trade
          (cbor_raw_match pm res
            (content_as_raw_data_item
              (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
              (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
              (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
          (cbor_raw_match pm (CBOR_Case_Tagged_Serialized ts) y))
        as
        (trade
          (cbor_raw_match pm res
            (Tagged?.v (Ghost.reveal y)))
          (cbor_raw_match pm x y));

      rewrite
        (cbor_raw_match pm res
          (content_as_raw_data_item
            (dfst (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (dfst (synth_raw_data_item_recip (Ghost.reveal y))))
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
        as
        (cbor_raw_match pm res
          (Tagged?.v (Ghost.reveal y)));

      res
    }
    CBOR_Case_Invalid -> {
      cbor_raw_get_tagged_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        CBOR_Case_Invalid
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Int i -> {
      cbor_raw_get_tagged_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Int i)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Simple sv -> {
      cbor_raw_get_tagged_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Simple sv)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_String s -> {
      cbor_raw_get_tagged_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_String s)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Array a -> {
      cbor_raw_get_tagged_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Array a)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Map m -> {
      cbor_raw_get_tagged_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Map m)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
  }
}
```

#pop-options

(* ======== Array accessor ======== *)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

let cbor_raw_match_cases_prop_array_elim
  (x: cbor_raw) (y: raw_data_item)
  (_: squash (cbor_raw_match_cases_prop x y))
  (_: squash (CBOR_Case_Array? x \/ Array? y))
: Lemma (CBOR_Case_Array? x /\ Array? y)
= ()

let synth_array_major_type
  (y: raw_data_item) (_: squash (Array? y))
: Lemma (
    let b = dfst (dfst (synth_raw_data_item_recip y)) in
    b.major_type = cbor_major_type_array
  )
= ()

let content_array_list
  (y: raw_data_item) (_: squash (Array? y))
: Lemma (
    content_as_list_raw
      (dfst (dfst (synth_raw_data_item_recip y)))
      (dsnd (dfst (synth_raw_data_item_recip y)))
      (dsnd (synth_raw_data_item_recip y))
    == Array?.v y
  )
= ()

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_get_array_content
  (pm: perm) (h: header) (v: cbor_array cbor_raw) (c: content h)
  (_: squash (
    let b = dfst h in
    b.major_type = cbor_major_type_array
  ))
requires
  cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Array v) c
ensures exists* (pm': perm) (l: list raw_data_item).
  I.mixed_list_match
    cbor_raw_match
    parse_raw_data_item
    pm'
    v.cbor_array_ptr
    l **
  trade
    (I.mixed_list_match
      cbor_raw_match
      parse_raw_data_item
      pm'
      v.cbor_array_ptr
      l)
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Array v) c) **
  pure (pm' == pm *. v.cbor_array_slice_perm /\ l == content_as_list_raw (dfst h) (dsnd h) c)
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  cbor_raw_match_content_eq_array cbor_raw_match parse_raw_data_item pm b la v c;
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Array v) c)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Array v) c);
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Array v) c)
    as
    (I.mixed_list_match
      cbor_raw_match
      parse_raw_data_item
      (pm *. v.cbor_array_slice_perm)
      v.cbor_array_ptr
      (content_as_list_raw b la c));
  intro
    (trade
      (I.mixed_list_match
        cbor_raw_match
        parse_raw_data_item
        (pm *. v.cbor_array_slice_perm)
        v.cbor_array_ptr
        (content_as_list_raw b la c))
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Array v) c))
    #emp
    fn _ {
      cbor_raw_match_content_eq_array cbor_raw_match parse_raw_data_item pm b la v c;
      header_eta h;
      rewrite
        (I.mixed_list_match
          cbor_raw_match
          parse_raw_data_item
          (pm *. v.cbor_array_slice_perm)
          v.cbor_array_ptr
          (content_as_list_raw b la c))
        as
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Array v) c);
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Array v) c)
        as
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Array v) c);
    };
}
```

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_get_array_content_false
  (pm: perm) (h: header) (xl: cbor_raw) (c: content h)
  (_: squash (
    let b = dfst h in
    b.major_type = cbor_major_type_array /\
    ~ (CBOR_Case_Array? xl)
  ))
requires
  cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h xl c
ensures
  pure False
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h xl c)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) xl c);
  match xl {
    CBOR_Case_Invalid -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) CBOR_Case_Invalid c)
        as (pure False)
    }
    CBOR_Case_Int i -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Int i) c)
        as (pure False)
    }
    CBOR_Case_Simple sv -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Simple sv) c)
        as (pure False)
    }
    CBOR_Case_String s -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_String s) c)
        as (pure False)
    }
    CBOR_Case_Array a -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Array a) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Map m -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Map m) c)
        as (pure False)
    }
    CBOR_Case_Tagged t -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Tagged t) c)
        as (pure False)
    }
    CBOR_Case_Tagged_Serialized ts -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Tagged_Serialized ts) c)
        as (pure False)
    }
  }
}
```

#pop-options

#push-options "--z3rlimit 1024 --fuel 2 --ifuel 2"

```pulse
fn cbor_raw_get_array
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
  (_: squash (CBOR_Case_Array? x \/ Array? (Ghost.reveal y)))
requires cbor_raw_match pm x y
returns res: I.mixed_list cbor_raw
ensures exists* (pm': perm) (l: Ghost.erased (list raw_data_item)).
  I.mixed_list_match
    cbor_raw_match
    parse_raw_data_item
    pm'
    res
    l **
  Trade.trade
    (I.mixed_list_match
      cbor_raw_match
      parse_raw_data_item
      pm'
      res
      l)
    (cbor_raw_match pm x y) **
  pure (Array? (Ghost.reveal y) /\
        Ghost.reveal l == Array?.v (Ghost.reveal y))
{
  cbor_raw_match_cases pm x;
  cbor_raw_match_cases_prop_array_elim x (Ghost.reveal y) () ();

  cbor_raw_match_unfold_aux x;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));

  synth_array_major_type (Ghost.reveal y) ();
  content_array_list (Ghost.reveal y) ();

  match x {
    CBOR_Case_Array v -> {
      cbor_raw_get_array_content pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();

      // Set up trade from content to cbor_raw_match
      intro
        (trade
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_Array v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
          (cbor_raw_match pm (CBOR_Case_Array v) y))
        #(pure (cbor_raw_get_header (CBOR_Case_Array v) ==
               Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
        fn _ {
          rewrite
            (pure (cbor_raw_get_header (CBOR_Case_Array v) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
            as
            (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get (CBOR_Case_Array v)) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
          fold (cbor_raw_match_header
            (cbor_raw_id_proj.pair_proj_get (CBOR_Case_Array v))
            (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
          fold (vmatch_dep_pair_with_proj
            cbor_raw_match_header
            cbor_raw_id_proj
            (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
            (CBOR_Case_Array v)
            (synth_raw_data_item_recip (Ghost.reveal y)));
          fold (vmatch_synth
            (vmatch_dep_pair_with_proj
               cbor_raw_match_header
               cbor_raw_id_proj
               (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
            synth_raw_data_item_recip
            (CBOR_Case_Array v) (Ghost.reveal y));
          fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm
            (CBOR_Case_Array v) (Ghost.reveal y));
          cbor_raw_match_fold_aux (CBOR_Case_Array v);
        };

      // Bind the existentials from the helper
      with _pm' _l . assert (I.mixed_list_match
        cbor_raw_match
        parse_raw_data_item
        _pm'
        v.cbor_array_ptr
        _l);
      with _pm'' _l' . assert (trade
        (I.mixed_list_match
          cbor_raw_match
          parse_raw_data_item
          _pm''
          v.cbor_array_ptr
          _l')
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
          (CBOR_Case_Array v)
          (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))));
      rewrite
        (trade
          (I.mixed_list_match
            cbor_raw_match
            parse_raw_data_item
            _pm''
            v.cbor_array_ptr
            _l')
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_Array v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
        as
        (trade
          (I.mixed_list_match
            cbor_raw_match
            parse_raw_data_item
            _pm'
            v.cbor_array_ptr
            _l)
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_Array v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))));

      // Compose the two trades
      Trade.trans
        (I.mixed_list_match
          cbor_raw_match
          parse_raw_data_item
          _pm'
          v.cbor_array_ptr
          _l)
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
          (CBOR_Case_Array v)
          (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
        (cbor_raw_match pm (CBOR_Case_Array v) y);

      rewrite
        (trade
          (I.mixed_list_match
            cbor_raw_match
            parse_raw_data_item
            _pm'
            v.cbor_array_ptr
            _l)
          (cbor_raw_match pm (CBOR_Case_Array v) y))
        as
        (trade
          (I.mixed_list_match
            cbor_raw_match
            parse_raw_data_item
            _pm'
            v.cbor_array_ptr
            _l)
          (cbor_raw_match pm x y));

      v.cbor_array_ptr
    }
    CBOR_Case_Invalid -> {
      cbor_raw_get_array_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        CBOR_Case_Invalid
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Int i -> {
      cbor_raw_get_array_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Int i)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Simple sv -> {
      cbor_raw_get_array_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Simple sv)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_String s -> {
      cbor_raw_get_array_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_String s)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Map m -> {
      cbor_raw_get_array_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Map m)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged t -> {
      cbor_raw_get_array_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Tagged t)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged_Serialized ts -> {
      cbor_raw_get_array_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Tagged_Serialized ts)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
  }
}
```

#pop-options

(* ======== Map accessor ======== *)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

let cbor_raw_match_cases_prop_map_elim
  (x: cbor_raw) (y: raw_data_item)
  (_: squash (cbor_raw_match_cases_prop x y))
  (_: squash (CBOR_Case_Map? x \/ Map? y))
: Lemma (CBOR_Case_Map? x /\ Map? y)
= ()

let synth_map_major_type
  (y: raw_data_item) (_: squash (Map? y))
: Lemma (
    let b = dfst (dfst (synth_raw_data_item_recip y)) in
    b.major_type = cbor_major_type_map
  )
= ()

let content_map_list
  (y: raw_data_item) (_: squash (Map? y))
: Lemma (
    content_as_list_pair
      (dfst (dfst (synth_raw_data_item_recip y)))
      (dsnd (dfst (synth_raw_data_item_recip y)))
      (dsnd (synth_raw_data_item_recip y))
    == Map?.v y
  )
= ()

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_get_map_content
  (pm: perm) (h: header) (v: cbor_map cbor_raw) (c: content h)
  (_: squash (
    let b = dfst h in
    b.major_type = cbor_major_type_map
  ))
requires
  cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Map v) c
ensures exists* (pm': perm) (l: list (raw_data_item & raw_data_item)).
  I.mixed_list_match
    (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
      cbor_map_entry_match cbor_raw_match pm0 elem vi)
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm'
    v.cbor_map_ptr
    l **
  trade
    (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem vi)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm'
      v.cbor_map_ptr
      l)
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Map v) c) **
  pure (pm' == pm *. v.cbor_map_slice_perm /\ l == content_as_list_pair (dfst h) (dsnd h) c)
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  cbor_raw_match_content_eq_map cbor_raw_match parse_raw_data_item pm b la v c;
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Map v) c)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Map v) c);
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Map v) c)
    as
    (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem vi)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      (pm *. v.cbor_map_slice_perm)
      v.cbor_map_ptr
      (content_as_list_pair b la c));
  intro
    (trade
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match cbor_raw_match pm0 elem vi)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        (pm *. v.cbor_map_slice_perm)
        v.cbor_map_ptr
        (content_as_list_pair b la c))
      (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Map v) c))
    #emp
    fn _ {
      cbor_raw_match_content_eq_map cbor_raw_match parse_raw_data_item pm b la v c;
      header_eta h;
      rewrite
        (I.mixed_list_match
          (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm0 elem vi)
          (nondep_then parse_raw_data_item parse_raw_data_item)
          (pm *. v.cbor_map_slice_perm)
          v.cbor_map_ptr
          (content_as_list_pair b la c))
        as
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Map v) c);
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Map v) c)
        as
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h (CBOR_Case_Map v) c);
    };
}
```

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_get_map_content_false
  (pm: perm) (h: header) (xl: cbor_raw) (c: content h)
  (_: squash (
    let b = dfst h in
    b.major_type = cbor_major_type_map /\
    ~ (CBOR_Case_Map? xl)
  ))
requires
  cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h xl c
ensures
  pure False
{
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm h xl c)
    as
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) xl c);
  match xl {
    CBOR_Case_Invalid -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) CBOR_Case_Invalid c)
        as (pure False)
    }
    CBOR_Case_Int i -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Int i) c)
        as (pure False)
    }
    CBOR_Case_Simple sv -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Simple sv) c)
        as (pure False)
    }
    CBOR_Case_String s -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_String s) c)
        as (pure False)
    }
    CBOR_Case_Array a -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Array a) c)
        as (pure False)
    }
    CBOR_Case_Map m -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Map m) c)
        as (pure False);
      unreachable ()
    }
    CBOR_Case_Tagged t -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Tagged t) c)
        as (pure False)
    }
    CBOR_Case_Tagged_Serialized ts -> {
      rewrite
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm (| b, la |) (CBOR_Case_Tagged_Serialized ts) c)
        as (pure False)
    }
  }
}
```

#pop-options

#push-options "--z3rlimit 1024 --fuel 2 --ifuel 2"

```pulse
fn cbor_raw_get_map
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
  (_: squash (CBOR_Case_Map? x \/ Map? (Ghost.reveal y)))
requires cbor_raw_match pm x y
returns res: I.mixed_list (cbor_map_entry cbor_raw)
ensures exists* (pm': perm) (l: Ghost.erased (list (raw_data_item & raw_data_item))).
  I.mixed_list_match
    (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
      cbor_map_entry_match cbor_raw_match pm0 elem v)
    (nondep_then parse_raw_data_item parse_raw_data_item)
    pm'
    res
    l **
  Trade.trade
    (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match cbor_raw_match pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm'
      res
      l)
    (cbor_raw_match pm x y) **
  pure (Map? (Ghost.reveal y) /\
        Ghost.reveal l == Map?.v (Ghost.reveal y))
{
  cbor_raw_match_cases pm x;
  cbor_raw_match_cases_prop_map_elim x (Ghost.reveal y) () ();

  cbor_raw_match_unfold_aux x;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));

  synth_map_major_type (Ghost.reveal y) ();
  content_map_list (Ghost.reveal y) ();

  match x {
    CBOR_Case_Map v -> {
      cbor_raw_get_map_content pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        v
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();

      // Set up trade from content to cbor_raw_match
      intro
        (trade
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_Map v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
          (cbor_raw_match pm (CBOR_Case_Map v) y))
        #(pure (cbor_raw_get_header (CBOR_Case_Map v) ==
               Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
        fn _ {
          rewrite
            (pure (cbor_raw_get_header (CBOR_Case_Map v) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
            as
            (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get (CBOR_Case_Map v)) ==
                   Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
          fold (cbor_raw_match_header
            (cbor_raw_id_proj.pair_proj_get (CBOR_Case_Map v))
            (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
          fold (vmatch_dep_pair_with_proj
            cbor_raw_match_header
            cbor_raw_id_proj
            (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
            (CBOR_Case_Map v)
            (synth_raw_data_item_recip (Ghost.reveal y)));
          fold (vmatch_synth
            (vmatch_dep_pair_with_proj
               cbor_raw_match_header
               cbor_raw_id_proj
               (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
            synth_raw_data_item_recip
            (CBOR_Case_Map v) (Ghost.reveal y));
          fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm
            (CBOR_Case_Map v) (Ghost.reveal y));
          cbor_raw_match_fold_aux (CBOR_Case_Map v);
        };

      // Bind the existentials from the helper
      with _pm' _l . assert (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match cbor_raw_match pm0 elem vi)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        _pm'
        v.cbor_map_ptr
        _l);
      with _pm'' _l' . assert (trade
        (I.mixed_list_match
          (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm0 elem vi)
          (nondep_then parse_raw_data_item parse_raw_data_item)
          _pm''
          v.cbor_map_ptr
          _l')
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
          (CBOR_Case_Map v)
          (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))));
      rewrite
        (trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item)
            _pm''
            v.cbor_map_ptr
            _l')
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_Map v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))))
        as
        (trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item)
            _pm'
            v.cbor_map_ptr
            _l)
          (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
            (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
            (CBOR_Case_Map v)
            (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))));

      // Compose the two trades
      Trade.trans
        (I.mixed_list_match
          (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm0 elem vi)
          (nondep_then parse_raw_data_item parse_raw_data_item)
          _pm'
          v.cbor_map_ptr
          _l)
        (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm
          (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
          (CBOR_Case_Map v)
          (dsnd (synth_raw_data_item_recip (Ghost.reveal y))))
        (cbor_raw_match pm (CBOR_Case_Map v) y);

      rewrite
        (trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item)
            _pm'
            v.cbor_map_ptr
            _l)
          (cbor_raw_match pm (CBOR_Case_Map v) y))
        as
        (trade
          (I.mixed_list_match
            (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (vi: (raw_data_item & raw_data_item)) ->
              cbor_map_entry_match cbor_raw_match pm0 elem vi)
            (nondep_then parse_raw_data_item parse_raw_data_item)
            _pm'
            v.cbor_map_ptr
            _l)
          (cbor_raw_match pm x y));

      v.cbor_map_ptr
    }
    CBOR_Case_Invalid -> {
      cbor_raw_get_map_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        CBOR_Case_Invalid
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Int i -> {
      cbor_raw_get_map_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Int i)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Simple sv -> {
      cbor_raw_get_map_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Simple sv)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_String s -> {
      cbor_raw_get_map_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_String s)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Array a -> {
      cbor_raw_get_map_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Array a)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged t -> {
      cbor_raw_get_map_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Tagged t)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
    CBOR_Case_Tagged_Serialized ts -> {
      cbor_raw_get_map_content_false pm
        (dfst (synth_raw_data_item_recip (Ghost.reveal y)))
        (CBOR_Case_Tagged_Serialized ts)
        (dsnd (synth_raw_data_item_recip (Ghost.reveal y)))
        ();
      unreachable ()
    }
  }
}
```

#pop-options

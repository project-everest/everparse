module Golden

(* The schemas that everparse-asn1 generates from difftest/schemas are the
   hand translations in ASN1.DiffTest.* (up to normalization). Bounded
   INTEGER types are not compared: everparse-asn1 maps them to 64-bit
   integers, unlike the hand translations. *)

module T = FStar.Tactics
module C = ASN1.DiffTest.Constructed
module S = ASN1.DiffTest.Set
module R = ASN1.DiffTest.Constraints
module A = ASN1.DiffTest.Any

let tac () = T.norm [delta; zeta; iota; primops]; T.trefl ()

let _ = assert (DiffConstructed.k_Seq == C.seq) by (tac ())
let _ = assert (DiffConstructed.k_IntSeq == C.intSeq) by (tac ())
let _ = assert (DiffConstructed.k_OctetsSet == C.octetsSet) by (tac ())
let _ = assert (DiffConstructed.k_Choice == C.choice) by (tac ())
let _ = assert (DiffConstructed.k_App == C.app) by (tac ())
let _ = assert (DiffConstructed.k_PrivExp == C.privExp) by (tac ())
let _ = assert (DiffConstructed.k_HighCtx == C.highCtx) by (tac ())
let _ = assert (DiffConstructed.k_HighApp == C.highApp) by (tac ())
let _ = assert (DiffConstructed.k_Nested == C.nested) by (tac ())

let _ = assert (DiffSet.k_Set == S.set_) by (tac ())

let _ = assert (DiffConstraints.k_Sized == R.sized) by (tac ())
let _ = assert (DiffConstraints.k_NonEmptySeqOf == R.nonEmptySeqOf) by (tac ())
let _ = assert (DiffConstraints.k_NonEmptySetOf == R.nonEmptySetOf) by (tac ())

let _ = assert (DiffAny.k_AnyT == A.anyT) by (tac ())
let _ = assert (DiffAny.k_AlgId == A.algId) by (tac ())

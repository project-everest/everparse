module ASN1.Spec.Content.BOOLEAN.Test

open ASN1.Spec.Content.BOOLEAN

open FStar.Tactics

friend FStar.Seq.Base
friend LowParse.Spec.Base
friend LowParse.Spec.Combinators
friend LowParse.Spec.Int

let testNil : squash (parse_asn1_boolean (Seq.empty) == None) by (trefl (); qed ()) = ()

let testTrue : squash (parse_asn1_boolean (Seq.create 1 (0xFFuy)) == Some (true, 1) ) by (trefl (); qed ()) = ()

#set-options "--z3rlimit 64"

let testFalse : squash (parse_asn1_boolean (Seq.create 1 (0x00uy)) == Some (false, 1) ) by (trefl (); qed ()) = ()

let testFail : squash (parse_asn1_boolean (Seq.create 1 (0x01uy)) == None) by (trefl (); qed ()) = ()



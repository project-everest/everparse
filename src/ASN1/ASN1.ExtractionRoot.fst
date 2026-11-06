module ASN1.ExtractionRoot

(* Root of whole-program extraction (custard accepts a single root file):
   depends on every module that ocaml/ASN1_Parser.ml calls into. *)

noextract let crl = ASN1.CRL.parse_crl
noextract let settest = ASN1.SetTest.parse_settest
noextract let difftest = ASN1.DiffTest.parse
noextract let enc_cert = ASN1.RoundTrip.enc_cert
noextract let enc_crl = ASN1.RoundTrip.enc_crl

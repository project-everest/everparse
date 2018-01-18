These files are written by hand. They describe the expected
QuackyDucky output from the following RFC input:
https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.1.2

TLSParse.Spec.fst: pure specifications of parsers (and serializers,
		   upcoming). Imported from FStar commit
		   fd5e6b452801a5d6b1cb2d4b154a63742a3ed83a (branch
		   taramana_mitls_parsers_with_serializers),
		   examples/lowparse/TLSParse.Spec.fst

TLSParse.SLow.fst: pure implementations in "SuperLow*" (or SLow*)
	       	   (names coined by @msprotz) using
	       	   FStar.Bytes. Prospective.

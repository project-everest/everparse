1. DEPENDENCIES: EVERPARSE

This package depends on EverParse. To install EverParse, run
./install-everparse.sh and follow the instructions.

Alternatively, you can use the Dockerfile to have an environment with
EverParse already installed:
   docker build -t asn1star .
   docker run -i -t asn1star

2. HOW TO VERIFY, EXTRACT AND EVALUATE

To verify, extract the OCaml code and compile it, run:
   make -j

To run the evaluation experiments, run:
   make eval

The OCaml evaluation executable also re-encodes every successfully
parsed X.509 certificate and CRL with the spec serializer (see below)
and checks that the result equals the consumed bytes ("round trip
succeeded"; exit code 8 on mismatch).

3. SPEC SERIALIZERS

ASN1.Spec.Serializer defines, for any schema k:
- asn1_enc k x: total encoder, to_value (ASN1.Spec.ToValue) followed by
  the generic DER value encoder asn1_value_enc (ASN1.Spec.Value.Enc);
- encodable k x: the round-trip predicate (parsing asn1_enc k x gives x);
- serialize_asn1 k: a LowParse serializer for asn1_as_parser k
  restricted to encodable values.
Every value produced by the parser is encodable (parsed_encodable), and
encodable values conform to the schema (encodable_conforms). Soundness
of the encoding w.r.t. the parsers is proved in ASN1.Spec.ToValue.Sound,
ASN1.Spec.ToValue.Set (SET ordering) and ASN1.Spec.ToValue.Main.
Instances for X.509 and CRLs are in ASN1.Spec.Conformance.Examples.

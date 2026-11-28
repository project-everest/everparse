(* The constructed universal types EXTERNAL, EMBEDDED PDV and CHARACTER
   STRING, as ASN.1 types (named EXTERNAL, EMBEDDED-PDV and
   CHARACTER-STRING). They follow the encodings prescribed by X.690 (8.18,
   8.10, 8.24), via the associated SEQUENCE types of X.680 (36.5, 44.5),
   as in src/ASN1/ASN1.UniversalTypes.fst *)

let text = {|
EverParse-ASN1-Prelude DEFINITIONS EXPLICIT TAGS ::= BEGIN

EXTERNAL ::= [UNIVERSAL 8] IMPLICIT SEQUENCE {
  direct-reference      OBJECT IDENTIFIER OPTIONAL,
  indirect-reference    INTEGER OPTIONAL,
  data-value-descriptor ObjectDescriptor OPTIONAL,
  encoding CHOICE {
    single-ASN1-type [0] ANY,
    octet-aligned    [1] IMPLICIT OCTET STRING,
    arbitrary        [2] IMPLICIT BIT STRING
  }
}

-- The identification of EMBEDDED PDV and CHARACTER STRING
UNIVERSAL-Identification ::= CHOICE {
  syntaxes [0] IMPLICIT SEQUENCE {
    abstract [0] IMPLICIT OBJECT IDENTIFIER,
    transfer [1] IMPLICIT OBJECT IDENTIFIER
  },
  syntax                  [1] IMPLICIT OBJECT IDENTIFIER,
  presentation-context-id [2] IMPLICIT INTEGER,
  context-negotiation [3] IMPLICIT SEQUENCE {
    presentation-context-id [0] IMPLICIT INTEGER,
    transfer-syntax         [1] IMPLICIT OBJECT IDENTIFIER
  },
  transfer-syntax         [4] IMPLICIT OBJECT IDENTIFIER,
  fixed                   [5] IMPLICIT NULL
}

-- data-value-descriptor [1] is ABSENT (X.680 36.5)
EMBEDDED-PDV ::= [UNIVERSAL 11] IMPLICIT SEQUENCE {
  identification [0] EXPLICIT UNIVERSAL-Identification,
  data-value     [2] IMPLICIT OCTET STRING
}

-- data-value-descriptor [1] is ABSENT (X.680 44.5)
CHARACTER-STRING ::= [UNIVERSAL 29] IMPLICIT SEQUENCE {
  identification [0] EXPLICIT UNIVERSAL-Identification,
  string-value   [2] IMPLICIT OCTET STRING
}

END
|}


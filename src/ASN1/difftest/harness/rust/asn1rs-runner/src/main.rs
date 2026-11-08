//! asn1-rs runner for the ASN.1 DER differential tests; see difftest-common.
//!
//! asn1-rs has no ASN.1 compiler: every type of ../../../schemas/*.asn
//! is translated by hand below, with the asn1-rs types and derive macros,
//! as a user of the library would. The translations add no check of their
//! own: in particular, asn1-rs has no notion of constraints, so constrained
//! types are not translated (see ../../../capabilities/asn1-rs.json).

#![allow(dead_code)]
use asn1_rs::*;
use difftest_common::Outcome;

/// Generic driver: parse with `FromDer`, report bytes consumed.
fn run<'a, T: FromDer<'a, asn1_rs::Error>>(data: &'a [u8]) -> Outcome {
    outcome(data, T::from_der(data))
}

fn outcome<T>(data: &[u8], r: ParseResult<'_, T>) -> Outcome {
    match r {
        Ok((rem, _)) => Outcome::Consumed(data.len() - rem.len()),
        Err(e) => Outcome::Reject(e.to_string()),
    }
}

mod diff_smoke {
    use asn1_rs::*;

    // Smoke ::= SEQUENCE { a INTEGER, b BOOLEAN OPTIONAL, c OCTET STRING }
    #[derive(Debug, DerSequence)]
    pub struct Smoke<'a> {
        pub a: Integer<'a>,
        #[optional]
        pub b: Option<bool>,
        pub c: OctetString<'a>,
    }
}

mod diff_prim {
    use asn1_rs::*;

    // Enum ::= ENUMERATED { a(0), b(1), c(5) }
    #[derive(Debug)]
    pub enum Enum {
        A,
        B,
        C,
    }

    impl<'a> FromDer<'a> for Enum {
        fn from_der(bytes: &'a [u8]) -> ParseResult<'a, Self> {
            let (rem, e) = Enumerated::from_der(bytes)?;
            let v = match e.0 {
                0 => Enum::A,
                1 => Enum::B,
                5 => Enum::C,
                _ => return Err(nom::Err::Error(Error::InvalidValue { tag: Tag::Enumerated, msg: "not a value of Enum".into() })),
            };
            Ok((rem, v))
        }
    }

    // RelOid ::= RELATIVE-OID
    pub fn rel_oid(bytes: &[u8]) -> ParseResult<'_, Oid<'_>> {
        Oid::from_der_relative(bytes)
    }
}

mod diff_constructed {
    use asn1_rs::*;

    // Seq ::= SEQUENCE {
    //   a INTEGER,
    //   b BOOLEAN DEFAULT FALSE,
    //   c [0] IMPLICIT OCTET STRING OPTIONAL,
    //   d [1] EXPLICIT INTEGER OPTIONAL }
    #[derive(Debug, DerSequence)]
    pub struct Seq<'a> {
        pub a: Integer<'a>,
        #[default(false)]
        pub b: bool,
        #[tag_implicit(0)]
        #[optional]
        pub c: Option<OctetString<'a>>,
        #[tag_explicit(1)]
        #[optional]
        pub d: Option<Integer<'a>>,
    }

    // IntSeq ::= SEQUENCE OF INTEGER
    pub type IntSeq<'a> = Vec<Integer<'a>>;

    // OctetsSet ::= SET OF OCTET STRING
    pub type OctetsSet<'a> = SetOf<OctetString<'a>>;

    // Choice ::= CHOICE { i INTEGER, b BOOLEAN, o [0] IMPLICIT OCTET STRING }
    #[derive(Debug)]
    pub enum Choice<'a> {
        I(Integer<'a>),
        B(bool),
        O(OctetString<'a>),
    }

    impl<'a> FromDer<'a> for Choice<'a> {
        fn from_der(bytes: &'a [u8]) -> ParseResult<'a, Self> {
            let (_, header) = Header::from_der(bytes)?;
            match (header.class(), header.tag()) {
                (Class::Universal, Tag::Integer) => {
                    let (rem, v) = Integer::from_der(bytes)?;
                    Ok((rem, Choice::I(v)))
                }
                (Class::Universal, Tag::Boolean) => {
                    let (rem, v) = bool::from_der(bytes)?;
                    Ok((rem, Choice::B(v)))
                }
                (Class::ContextSpecific, Tag(0)) => {
                    let (rem, v) = TaggedImplicit::<OctetString, Error, 0>::from_der(bytes)?;
                    Ok((rem, Choice::O(v.into_inner())))
                }
                _ => Err(nom::Err::Error(Error::BerTypeError)),
            }
        }
    }

    // App ::= [APPLICATION 5] IMPLICIT INTEGER
    pub type App<'a> = ApplicationImplicit<Integer<'a>, Error, 5>;

    // PrivExp ::= [PRIVATE 3] EXPLICIT BOOLEAN
    pub type PrivExp = PrivateExplicit<bool, Error, 3>;

    // HighCtx ::= [100] IMPLICIT INTEGER
    pub type HighCtx<'a> = TaggedImplicit<Integer<'a>, Error, 100>;

    // HighApp ::= [APPLICATION 1000] EXPLICIT OCTET STRING
    pub type HighApp<'a> = ApplicationExplicit<OctetString<'a>, Error, 1000>;

    // Nested ::= SEQUENCE { s Seq, l IntSeq, ch Choice OPTIONAL }
    // (by hand, since the derive macros cannot make an untagged CHOICE
    // OPTIONAL)
    #[derive(Debug)]
    pub struct Nested<'a> {
        pub s: Seq<'a>,
        pub l: IntSeq<'a>,
        pub ch: Option<Choice<'a>>,
    }

    impl<'a> FromDer<'a> for Nested<'a> {
        fn from_der(bytes: &'a [u8]) -> ParseResult<'a, Self> {
            Sequence::from_der_and_then(bytes, |i| {
                let (i, s) = Seq::from_der(i)?;
                let (i, l) = IntSeq::from_der(i)?;
                let (i, ch) = if i.is_empty() {
                    (i, None)
                } else {
                    let (i, ch) = Choice::from_der(i)?;
                    (i, Some(ch))
                };
                // from_der_and_then ignores what the closure leaves over
                if !i.is_empty() {
                    return Err(nom::Err::Error(Error::BerValueError));
                }
                Ok((i, Nested { s, l, ch }))
            })
        }
    }
}

mod diff_set {
    use asn1_rs::*;

    // Set ::= SET {
    //   a [0] IMPLICIT INTEGER,
    //   b [1] IMPLICIT BOOLEAN OPTIONAL,
    //   c OCTET STRING }
    // The DerSet derive parses fields in declaration order, so they are
    // declared in DER canonical order (X.690 10.3: universal before context).
    #[derive(Debug, DerSet)]
    pub struct Set<'a> {
        pub c: OctetString<'a>,
        #[tag_implicit(0)]
        pub a: Integer<'a>,
        #[tag_implicit(1)]
        #[optional]
        pub b: Option<bool>,
    }
}

mod diff_any {
    use asn1_rs::*;

    // AlgId ::= SEQUENCE {
    //   algorithm OBJECT IDENTIFIER,
    //   parameters ANY DEFINED BY algorithm OPTIONAL }
    #[derive(Debug, DerSequence)]
    pub struct AlgId<'a> {
        pub algorithm: Oid<'a>,
        #[optional]
        pub parameters: Option<Any<'a>>,
    }
}

fn decode(ty: &str, data: &[u8]) -> Outcome {
    match ty {
        "DiffSmoke.Smoke" => run::<diff_smoke::Smoke>(data),
        "DiffPrim.Bool" => run::<bool>(data),
        "DiffPrim.Int" => run::<Integer>(data),
        "DiffPrim.Enum" => run::<diff_prim::Enum>(data),
        "DiffPrim.Bits" => run::<BitString>(data),
        "DiffPrim.Octets" => run::<OctetString>(data),
        "DiffPrim.Null" => run::<Null>(data),
        "DiffPrim.Oid" => run::<Oid>(data),
        "DiffRelOid.RelOid" => outcome(data, diff_prim::rel_oid(data)),
        "DiffDesc.Desc" => run::<ObjectDescriptor>(data),
        "DiffStrings.Utf8" => run::<Utf8String>(data),
        "DiffStrings.Numeric" => run::<NumericString>(data),
        "DiffStrings.Printable" => run::<PrintableString>(data),
        "DiffStrings.Ia5" => run::<Ia5String>(data),
        "DiffStrings.Visible" => run::<VisibleString>(data),
        "DiffStrings.Bmp" => run::<BmpString>(data),
        "DiffStrings.Universal" => run::<UniversalString>(data),
        "DiffStrings.Teletex" => run::<TeletexString>(data),
        "DiffVideotex.Videotex" => run::<VideotexString>(data),
        "DiffStrings2.Graphic" => run::<GraphicString>(data),
        "DiffStrings2.General" => run::<GeneralString>(data),
        "DiffTime.Utc" => run::<UtcTime>(data),
        "DiffTime.Gen" => run::<GeneralizedTime>(data),
        "DiffConstructed.Seq" => run::<diff_constructed::Seq>(data),
        "DiffConstructed.IntSeq" => run::<diff_constructed::IntSeq>(data),
        "DiffConstructed.OctetsSet" => run::<diff_constructed::OctetsSet>(data),
        "DiffConstructed.Choice" => run::<diff_constructed::Choice>(data),
        "DiffConstructed.App" => run::<diff_constructed::App>(data),
        "DiffConstructed.PrivExp" => run::<diff_constructed::PrivExp>(data),
        "DiffConstructed.HighCtx" => run::<diff_constructed::HighCtx>(data),
        "DiffConstructed.HighApp" => run::<diff_constructed::HighApp>(data),
        "DiffConstructed.Nested" => run::<diff_constructed::Nested>(data),
        "DiffSet.Set" => run::<diff_set::Set>(data),
        "DiffAny.AnyT" => run::<Any>(data),
        "DiffAny.AlgId" => run::<diff_any::AlgId>(data),
        "DiffPdv.Pdv" => run::<EmbeddedPdv>(data),
        _ => Outcome::Unsupported,
    }
}

fn main() {
    difftest_common::main("asn1-rs", decode)
}

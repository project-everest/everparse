//! rasn runner for the ASN.1 DER differential tests; see difftest-common.
//! Types are generated from ../../../schemas/*.asn by build.rs. Types that
//! rasn-compiler does not translate faithfully (EXTERNAL and EMBEDDED PDV
//! become an untagged ANY) are not dispatched; see
//! ../../../capabilities/rasn.json.

#![allow(clippy::all, non_camel_case_types, non_snake_case, unused)]
mod generated {
    include!(concat!(env!("OUT_DIR"), "/generated.rs"));
}

use difftest_common::Outcome;
use generated::*;

fn run<T: rasn::Decode>(data: &[u8]) -> Outcome {
    match rasn::der::decode_with_remainder::<T>(data) {
        Ok((_, rem)) => Outcome::Consumed(data.len() - rem.len()),
        Err(e) => Outcome::Reject(e.to_string()),
    }
}

fn decode(ty: &str, data: &[u8]) -> Outcome {
    match ty {
        "DiffSmoke.Smoke" => run::<diff_smoke::Smoke>(data),
        "DiffPrim.Bool" => run::<diff_prim::Bool>(data),
        "DiffPrim.Int" => run::<diff_prim::Int>(data),
        "DiffPrim.Enum" => run::<diff_prim::Enum>(data),
        "DiffPrim.Bits" => run::<diff_prim::Bits>(data),
        "DiffPrim.Octets" => run::<diff_prim::Octets>(data),
        "DiffPrim.Null" => run::<diff_prim::Null>(data),
        "DiffPrim.Oid" => run::<diff_prim::Oid>(data),
        "DiffRelOid.RelOid" => run::<diff_rel_oid::RelOid>(data),
        "DiffStrings.Utf8" => run::<diff_strings::Utf8>(data),
        "DiffStrings.Numeric" => run::<diff_strings::Numeric>(data),
        "DiffStrings.Printable" => run::<diff_strings::Printable>(data),
        "DiffStrings.Ia5" => run::<diff_strings::Ia5>(data),
        "DiffStrings.Visible" => run::<diff_strings::Visible>(data),
        "DiffStrings.Bmp" => run::<diff_strings::Bmp>(data),
        "DiffStrings.Universal" => run::<diff_strings::Universal>(data),
        "DiffStrings.Teletex" => run::<diff_strings::Teletex>(data),
        "DiffStrings2.Graphic" => run::<diff_strings2::Graphic>(data),
        "DiffStrings2.General" => run::<diff_strings2::General>(data),
        "DiffTime.Utc" => run::<diff_time::Utc>(data),
        "DiffTime.Gen" => run::<diff_time::Gen>(data),
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
        "DiffAny.AnyT" => run::<diff_any::AnyT>(data),
        "DiffAny.AlgId" => run::<diff_any::AlgId>(data),
        "DiffConstraints.Sized" => run::<diff_constraints::Sized>(data),
        "DiffConstraints.Byte" => run::<diff_constraints::Byte>(data),
        "DiffConstraints.NonEmptySeqOf" => run::<diff_constraints::NonEmptySeqOf>(data),
        "DiffConstraints.NonEmptySetOf" => run::<diff_constraints::NonEmptySetOf>(data),
        _ => Outcome::Unsupported,
    }
}

fn main() {
    difftest_common::main("rasn", decode)
}

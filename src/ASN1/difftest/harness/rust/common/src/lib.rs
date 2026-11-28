//! Shared driver for the Rust differential-testing runners.
//!
//! Usage of every runner: `RUNNER MANIFEST RESULTS`. Each manifest vector
//! (`"type"` is `"Module.Type"`) is decoded by the runner-specific `decode`
//! function, and one JSON object per line is written to RESULTS:
//! `{id, impl, verdict, consumed[, error]}`. The verdict is `accept` iff
//! decoding succeeds and consumes the whole input.

use serde::Deserialize;
use serde_json::{json, Value};
use std::io::Write;

#[derive(Deserialize)]
pub struct Vector {
    pub id: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub hex: String,
}

#[derive(Deserialize)]
struct Manifest {
    vectors: Vec<Vector>,
}

pub enum Outcome {
    /// The runner has no translation of this type.
    Unsupported,
    /// Decoding failed with this message.
    Reject(String),
    /// Decoding succeeded, consuming this many bytes.
    Consumed(usize),
}

fn from_hex(h: &str) -> Vec<u8> {
    let h: Vec<u8> = h.bytes().filter(|c| !c.is_ascii_whitespace()).collect();
    h.chunks(2)
        .map(|c| u8::from_str_radix(std::str::from_utf8(c).unwrap(), 16).unwrap())
        .collect()
}

pub fn main(impl_name: &str, decode: fn(&str, &[u8]) -> Outcome) {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: {} MANIFEST RESULTS", args[0]);
        std::process::exit(1);
    }
    let manifest: Manifest =
        serde_json::from_str(&std::fs::read_to_string(&args[1]).unwrap()).unwrap();
    let mut out = std::io::BufWriter::new(std::fs::File::create(&args[2]).unwrap());
    // Panics are reported as "error" verdicts, not printed
    std::panic::set_hook(Box::new(|_| {}));
    for v in &manifest.vectors {
        let data = from_hex(&v.hex);
        let outcome = std::panic::catch_unwind(|| decode(&v.ty, &data));
        let (verdict, consumed, error): (&str, Value, Option<String>) = match outcome {
            Err(e) => {
                let msg = e
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_default();
                ("error", Value::Null, Some(format!("panic: {msg}")))
            }
            Ok(Outcome::Unsupported) => ("unsupported", Value::Null, None),
            Ok(Outcome::Reject(e)) => ("reject", Value::Null, Some(e)),
            Ok(Outcome::Consumed(n)) => {
                (if n == data.len() { "accept" } else { "reject" }, json!(n), None)
            }
        };
        let mut r = json!({"id": v.id, "impl": impl_name, "verdict": verdict, "consumed": consumed});
        if let Some(e) = error {
            r["error"] = json!(e);
        }
        writeln!(out, "{r}").unwrap();
    }
}

// Compiles ../../../schemas/*.asn into Rust bindings for rasn, with
// rasn-compiler. Each module is compiled on its own, so that a module that
// rasn-compiler rejects only makes its own types unsupported.
use rasn_compiler::{prelude::*, OutputMode};
use std::path::PathBuf;

// Modules that rasn-compiler accepts, but whose generated Rust code does not
// build; see ../../../capabilities/rasn.json.
const SKIP: &[&str] = &["DiffDesc"];

fn main() {
    let schemas = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("../../../schemas");
    println!("cargo:rerun-if-changed={}", schemas.display());
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&schemas)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "asn"))
        .collect();
    paths.sort();
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let mut generated = String::new();
    for path in &paths {
        let stem = path.file_stem().unwrap().to_str().unwrap();
        if SKIP.contains(&stem) {
            continue;
        }
        let out = out_dir.join(format!("{stem}.rs"));
        match Compiler::<RasnBackend, _>::new()
            .add_asn_by_path(path)
            .set_output_mode(OutputMode::SingleFile(out.clone()))
            .compile()
        {
            Ok(warnings) => {
                for w in warnings {
                    println!("cargo:warning=rasn-compiler: {stem}: {w}");
                }
                generated.push_str(&std::fs::read_to_string(&out).unwrap());
                generated.push('\n');
            }
            Err(e) => println!("cargo:warning=rasn-compiler: {stem}: skipped: {e}"),
        }
    }
    std::fs::write(out_dir.join("generated.rs"), generated).unwrap();
}

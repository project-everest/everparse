"""Canonical tracked-source inventory and the existing corpus's build matrix."""

import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess


HERE = Path(__file__).resolve().parent
CORPUS = Path("share/everparse/tests/3d/lowstar")
APIS = ("legacy_lowstar", "lowstar")

# These are build recipes, not an allowlist of grammars. Every tracked grammar
# is assigned below, and every emitted public wrapper is discovered at run time.
SUITES = {
    "root": (".", ["batch-test", "batch-interpret-test", "elf-test",
                   "inplace-hash-test", "batch-cleanup-test", "z3-testgen-test"],
             ["out.batch-interpret", "out.elf"]),
    "check_complete": ("check_complete", ["all"], ["obj"]),
    "extern": ("extern", ["all"], ["obj"]),
    "static": ("static", ["all"], ["obj"]),
    "funptr": ("funptr", ["all"], ["obj"]),
    "exttype": ("exttype", ["all"], []),
    "goto_return": ("goto_return", ["all"], []),
    "ifdefs": ("ifdefs", ["all"], ["obj", "batch_obj"]),
    "iter/coarse": ("iter/coarse", ["all"], ["obj"]),
    "iter/fine": ("iter/fine", ["all"], ["obj"]),
    "modules": ("modules", ["all"], ["obj"]),
    "output_types": ("output_types", ["interpret"], ["interpret.out"]),
    "output_types/modules": ("output_types/modules", ["all"], ["obj"]),
    "output_types/modules_batch": ("output_types/modules_batch", ["all"], ["basic.out"]),
    "probe": ("probe", ["all"], ["obj"]),
    "probe/src": ("probe/src", ["all"], []),
    "probe_error_handler_macro": ("probe_error_handler_macro", ["all"], ["obj"]),
    "probe_error_handler_macro/src": ("probe_error_handler_macro/src", ["all"], []),
    "save_hashes": ("save_hashes", ["all"], ["obj"]),
    "specialize_test": ("specialize_test", ["all"], ["obj"]),
    "specialize_test2": ("specialize_test2", ["all"], ["obj"]),
    "specialize_test_error_handler_macro": (
        "specialize_test_error_handler_macro", ["all"], ["obj"]),
    "specialize_tagged_union_array": ("specialize_tagged_union_array", ["all"], ["obj"]),
    "tcpip": ("tcpip", ["all"], ["interpret.out", "extern.out"]),
    "use_error_handler_macro": ("use_error_handler_macro", ["all"], ["obj"]),
}

NEGATIVES = {
    "FAILAllBytesCompose.3d": ("verification", r"Error (12|19|189)\b"),
    "FAILAllBytesNotLast.3d": ("verification", r"Error (12|19|189)\b"),
    "FAILAllBytesType.3d": ("frontend", r"consume-all field returns UINT16"),
    "FAILArrayBitWidth.3d": ("frontend", r"cannot have a bit width"),
    "FAILArrayRefinement.3d": ("frontend", r"cannot be refined with constraints"),
    "FAILNoEntrypoint.3d": ("frontend", r"does not have an entry point"),
    "FAILProbe.3d": ("frontend", r"Probe init function not found"),
    "FAILSpecialize2.3d": ("frontend", r"Unexpected specialization types"),
    "FAILSpecializeDep1.3d": ("frontend", r"Cannot find probe function for Write UINT32"),
    "FAILSpecializeDep2.3d": ("frontend", r"Cannot find probe function for Write UINT32"),
}


class HarnessError(RuntimeError):
    pass


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_path(name):
    p = PurePosixPath(name)
    if p.is_absolute() or ".." in p.parts or str(p) != name:
        raise HarnessError(f"unsafe inventory path: {name!r}")
    return p


def excluded(name):
    p = source_path(name)
    return any(part in {"pulse-diff", "pulse-lowstar-diff-tests", "__pycache__"}
               or part in {"obj", "batch_obj"} or part.startswith(("out.", "obj."))
               or part.endswith(".out") for part in p.parts[:-1])


def classify(name):
    p = source_path(name)
    if p.name.startswith("FAIL") and p.suffix == ".3d":
        if name not in NEGATIVES:
            raise HarnessError(f"new negative needs an expected failure stage: {name}")
        return "negative", ["negative:" + name]
    if "snapshot" in p.parts:
        return "snapshot", ["goto_return"]
    owners = [s for s, (directory, _, _) in SUITES.items()
              if directory != "." and (name == directory or name.startswith(directory + "/"))]
    # probe/src has additional generation tests, but shares its parent grammar.
    if owners:
        deepest = max(owners, key=lambda s: len(SUITES[s][0]))
        owners = [deepest]
        if deepest in {"probe/src", "probe_error_handler_macro/src"}:
            owners.append(deepest.removesuffix("/src"))
    elif len(p.parts) == 1:
        owners = ["root"]
    elif p.parts[0] == "iter" and p.name == "Makefile":
        owners = ["iter/coarse", "iter/fine"]
    else:
        raise HarnessError(f"unassigned tracked corpus source: {name}")
    if p.suffix == ".3d":
        if owners == ["goto_return"]:
            return "snapshot-only-grammar", owners
        if owners == ["exttype"]:
            return "generation-only-grammar", owners
        return "runtime-grammar", owners
    if p.suffix in {".c", ".cpp"}:
        return "client-source", owners
    return "support", owners


def inventory(home, manifest=None):
    root = home / CORPUS
    if manifest is None:
        git = subprocess.run(["git", "-C", str(home), "ls-files", "-z", "--", str(CORPUS)],
                             capture_output=True)
        if git.returncode or not git.stdout:
            raise HarnessError("git inventory unavailable; supply --manifest exported by --inventory-only")
        names = [str(PurePosixPath(p).relative_to(CORPUS))
                 for p in git.stdout.decode().split("\0") if p]
    else:
        data = json.loads(Path(manifest).read_text())
        if data.get("version") != 1 or not isinstance(data.get("files"), list):
            raise HarnessError("invalid packaged inventory")
        names = [r["path"] for r in data["files"]]
        for r in data["files"]:
            source_path(r["path"])
            if digest(root / r["path"]) != r["sha256"]:
                raise HarnessError(f"packaged source checksum mismatch: {r['path']}")
        # A tarball must not silently omit newly added source grammars.
        extra = {p.relative_to(root).as_posix() for p in root.rglob("*.3d")
                 if not excluded(p.relative_to(root).as_posix())} - set(names)
        if extra:
            raise HarnessError(f"unlisted packaged grammars: {sorted(extra)}")
    if len(names) != len(set(names)):
        raise HarnessError("duplicate inventory paths")
    records = []
    for name in sorted(names):
        if excluded(name):
            continue
        kind, suites = classify(name)
        path = root / name
        if path.is_symlink() or not path.is_file():
            raise HarnessError(f"missing or symlinked corpus source: {name}")
        records.append(dict(path=name, category=kind, suites=suites, sha256=digest(path)))
    if not any(r["category"] == "runtime-grammar" for r in records):
        raise HarnessError("empty runtime corpus")
    return {"version": 1, "files": records,
            "scope": f"tracked {CORPUS} sources; hashchk implementation is outside this corpus"}


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

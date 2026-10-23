"""Extract the six runtime headers with Custard's direct C backend."""

import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RUNTIME = ROOT / "lib/everparse/3d"
PREFIX = "EverParse3d."
CONTRACT = json.loads((HERE / "runtime-contract.json").read_text())
PROFILES = {p["directory"]: p for p in CONTRACT["profiles"]}
COMPANION = "EverParseStreamPrimitives.h"


def c_name(name):
    return "EverParse" + "".join(word.capitalize() for word in name.split("_"))


def companion(profile):
    selected = PROFILES[profile]
    if selected["stream"] == "buffer":
        raise ValueError("This profile has no static client hooks: " + profile)
    hooks = PROFILES[("lowstar/" if selected["api"] == "lowstar" else "") + "static"]["static_hooks"]
    linkage = "static inline" if selected["stream"] == "static" else "extern"
    abi = json.loads((HERE / "runtime-abi.json").read_text())["profiles"][profile]
    lines = [
        "/* Generated from the runtime ABI contract. Client supplies the bodies. */",
        "#ifndef EVERPARSE_STREAM_PRIMITIVES_H",
        "#define EVERPARSE_STREAM_PRIMITIVES_H",
        "",
        "#include <stddef.h>",
        "#include <stdint.h>",
        '#include "EverParseEndianness.h"',
        "",
        "#ifdef __cplusplus",
        'extern "C" {',
        "#endif",
        "",
    ]
    for name in hooks:
        signature = abi["functions"][name]
        types = [signature["return"]] + signature["parameters"]
        if any("EVERPARSE_INPUT_BUFFER" in t or "EVERPARSE_ERROR_FRAME" in t
               for t in types):
            raise ValueError("Early static hook depends on a generated record: " + name)
        lines.append(linkage + " " + signature["return"] + " " + name
                     + "(" + ", ".join(signature["parameters"]) + ");")
    lines += ["", "#ifdef __cplusplus", "}", "#endif", "", "#endif", ""]
    return "\n".join(lines)


def publish(contents, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_name("." + destination.name + ".tmp")
    temporary.write_bytes(contents)
    os.replace(temporary, destination)


def native_path(path):
    if sys.platform == "cygwin":
        return subprocess.check_output(
            ["cygpath", "-m", str(path)], text=True
        ).strip()
    return str(path)


def profile_config(profile):
    p = PROFILES[profile]
    lowstar = p["api"] == "lowstar"
    extern = p["stream"] != "buffer"
    backend = ("Lowstar" if lowstar else "") + ("Extern" if extern else "Buffer")
    names = {
        "Actions.Common": {"app_ctxt": "EVERPARSE_APP_CTXT"},
        "Actions.ErrorHandler." + backend: {"error_handler": "EVERPARSE_ERROR_HANDLER"},
        "Prelude.StaticHeader": {
            "get_bitfield" + str(width) + suffix:
                "EverParseGetBitfield" + str(width) + ("MsbFirst" if suffix else "")
            for width in (8, 16, 32, 64) for suffix in ("", "_msb_first")
        },
    }
    preserved = {
        "Actions.Common": {"app_ctxt"},
        "Actions.ErrorHandler." + backend: {"error_handler"},
    }
    error_prefix = "EverParsePulseInternal" if lowstar else "EverParse"
    macro_prefix = "EVERPARSEPULSEINTERNAL_" if lowstar else "EVERPARSE_"
    error_names = {
        "validator_" + name: macro_prefix + "VALIDATOR_" + name.upper()
        for name in ("success", "error_action_failed", "error_not_enough_data",
                     "error_impossible", "error_list_size_not_multiple",
                     "error_constraint_failed", "error_unexpected_padding",
                     "error_probe_failed")
    }
    error_names["error_reason_of_result"] = error_prefix + "ErrorReasonOfResult"
    names["CAbi.ErrorCode" + ("Lowstar" if lowstar else "Pulse")] = error_names | {
        "error_code_is_range_okay": error_prefix + "IsRangeOkay",
    }
    names["CAbi.Public"] = {}
    foreign = {}
    external_types = {}
    include = "EverParseEndianness.h" if lowstar else "EverParsePulseEndianness.h"
    copy_module = "CopyBuffer." + backend
    external_types[("CopyBuffer.Buffer" if not lowstar else copy_module)
                   + ".copy_buffer_t"] = "EVERPARSE_COPY_BUFFER_T"
    if not extern or lowstar:
        copy_names = ("stream_of",) if extern else ("stream_of", "stream_len")
        if not lowstar:
            copy_names += ("stream_pos",)
        names[copy_module] = {name: c_name(name) for name in copy_names}
        foreign[copy_module] = set(copy_names)
        external_types[copy_module + ".copy_buffer_t"] = "EVERPARSE_COPY_BUFFER_T"
    if extern:
        types_module = "InputStream.LowstarExtern.Types" if lowstar else "InputStream.Extern.Types"
        external_types.update({
            types_module + ".input_stream_base": "EVERPARSE_INPUT_STREAM_BASE",
            types_module + ".extra_t": "EVERPARSE_EXTRA_T",
        })
        if lowstar:
            names["CAbi.Public"]["base_t"] = "EVERPARSE_BASE_T"
            preserved["CAbi.Public"] = {"base_t"}
            names["InputStream.LowstarExtern.Raw"] = {
                name: c_name(name) for name in ("has", "skip", "empty", "read", "peep")
            }
            foreign["InputStream.LowstarExtern.Raw"] = set(names["InputStream.LowstarExtern.Raw"])
            names[types_module] = {
                "input_buffer": "EVERPARSE_INPUT_BUFFER",
                "make_input_buffer": "EverParseMakeInputBuffer",
                "make_input_buffer_with_length": "EverParseMakeInputBufferWithLength",
            }
        else:
            names["InputStream.Extern"] = {
                name: c_name(name) for name in (
                    "stream_get_position", "stream_has", "stream_has_at",
                    "stream_read_bytes", "stream_skip", "stream_empty",
                    "field_ptr_after_impl",
                )
            }
            foreign["InputStream.Extern"] = set(names["InputStream.Extern"])
            names["InputStream.Extern"]["___PUINT8"] = "EVERPARSE____PUINT8"
            preserved["InputStream.Extern"] = {"___PUINT8"}
            names["InputStream.Extern.NullPtr"] = {"null_ptr": "EverParseNullPtr"}
            foreign["InputStream.Extern.NullPtr"] = {"null_ptr"}
    if lowstar:
        public_functions = (
            "set_validator_error_pos", "get_validator_error_pos",
            "set_validator_error_kind", "get_validator_error_kind",
            "error_reason_of_result",
        )
        names["Lowstar.Public"] = {name: c_name(name) for name in public_functions}
        names["Lowstar.Public"].update({
            "validator_" + name: "EVERPARSE_VALIDATOR_" + name.upper()
            for name in (
                "max_length", "error_generic", "error_not_enough_data", "error_impossible",
                "error_list_size_not_multiple", "error_action_failed",
                "error_constraint_failed", "error_unexpected_padding", "error_probe_failed",
            )
        })
        names["Lowstar.Public"]["error_frame"] = "EVERPARSE_ERROR_FRAME"
        names["CAbi.Public"].update({
            name: c_name(name)
            for name in ("is_error", "is_success", "is_range_okay", "check_constraint_ok")
        })
        support = "Lowstar.Support" + ("Extern" if extern else "Buffer")
        names[support] = {"default_error_handler": "EverParseDefaultErrorHandler"}
        if not extern:
            names[support]["input_buffer"] = "EVERPARSE_INPUT_BUFFER"
            preserved[support] = {"input_buffer"}
    return names, preserved, foreign, external_types, include


def extract(args):
    names, _, _, external_types, include = profile_config(args.profile)
    profile = PROFILES[args.profile]
    build = args.build_dir.resolve()
    source_dir = build / "src"
    source_dir.mkdir(parents=True, exist_ok=True)
    root = source_dir / "EverParse3d.CRuntime.Roots.fst"
    stream = "extern" if profile["api"] == "lowstar" and profile["stream"] == "static" else profile["stream"]
    backend = ("Lowstar" if profile["api"] == "lowstar" else "") + stream.capitalize()
    verification_modules = ["Interpreter", "ProbeActions", "InputStream." + backend,
                            "CopyBuffer.Buffer"]
    if profile["api"] == "lowstar":
        verification_modules.append(
            "Lowstar.BufferAdapter" if profile["stream"] == "buffer"
            else "Lowstar.ExternAdapter")
    root.write_text("module EverParse3d.CRuntime.Roots\n" + "".join(
        "module M" + str(i) + " = " + PREFIX + name + "\n"
        for i, name in enumerate(sorted(set(names) | set(verification_modules)))
    ))
    flags = shlex.split(args.fstar_options)
    flags += ["--cache_checked_modules", "--cache_dir", native_path(build),
              "--odir", native_path(build), "--include", native_path(source_dir),
              "--include", native_path(RUNTIME),
              "--include", native_path(ROOT / "lib/everparse/lowparse")]
    for path in (
        ROOT / "opt/FStar/pulse/lib/common",
        ROOT / "opt/FStar/pulse/lib/pulse",
        ROOT / "opt/FStar/pulse/build/lib.common.checked",
        ROOT / "opt/FStar/pulse/build/lib.pulse.checked",
    ):
        if path.is_dir():
            flags += ["--include", native_path(path)]
    flags += ["--already_cached", "PulseCore,Pulse,Prims,FStar,LowStar,LowParse,EverParse3d.*",
              "--warn_error", "@241@371-342"]
    command = [args.fstar] + flags
    subprocess.run(command + [native_path(root)], check=True)
    extraction = ["--codegen", "C", "--custard_unit", "EverParse",
                  "--custard_static_header",
                  "--custard_monomorphize_types", "true"]
    for module, declarations in names.items():
        for name in declarations:
            extraction += ["--custard_entry", PREFIX + module + "." + name]
    for name, target in external_types.items():
        extraction += ["--custard_extern_type", PREFIX + name + "=" + target + "@" + include]
    header = build / "EverParse.h"
    subprocess.run(command + extraction + [native_path(root), "-o", native_path(header)], check=True)
    if (build / "EverParse.c").exists():
        raise RuntimeError("Static-header extraction unexpectedly produced EverParse.c")
    publish(header.read_bytes(), args.output)
    publish((build / "EverParse.cui").read_bytes(), args.output.with_suffix(".cui"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=PROFILES, required=True)
    parser.add_argument("--build-dir", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--companion-only", action="store_true",
                        help="Generate static hook prototypes without invoking F*")
    parser.add_argument("--fstar", default=os.environ.get("FSTAR_EXE", "fstar.exe"))
    parser.add_argument("--fstar-options", default="")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.companion_only:
        if args.output.name != COMPANION:
            parser.error("The companion output must be named " + COMPANION)
        publish(companion(args.profile).encode(), args.output)
    else:
        if not args.build_dir:
            parser.error("Extraction requires --build-dir")
        extract(args)


if __name__ == "__main__":
    main()

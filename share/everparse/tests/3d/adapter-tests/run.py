"""Compile and execute focused ABI regressions without changing old fixtures."""

import argparse
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
TESTS = ROOT / "share/everparse/tests/3d/lowstar"
BUILD = HERE / "_build"
FSTAR = os.environ.get("FSTAR_EXE", str(ROOT / "opt/FStar/out/bin/fstar.exe"))
RUNTIME = ROOT / "lib/everparse/3d"
CC = shlex.split(os.environ.get("CC", "cc"))
SANITIZE = os.environ.get("SANITIZE", "0") == "1"


def run(args, out, echo=False):
    args = [str(arg) for arg in args]
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    with (out / "commands.log").open("a") as log:
        log.write("$ " + shlex.join(args) + "\n" + result.stdout)
    if result.returncode:
        print(result.stdout, file=sys.stderr)
        raise subprocess.CalledProcessError(result.returncode, args)
    if echo:
        print(result.stdout, end="")
    return result.stdout


def output(name):
    out = BUILD / name
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True, exist_ok=True)
    return out


def runtime_profile(api, stream):
    return RUNTIME / "runtime" / ("lowstar" if api == "lowstar" else "") / stream


def check_artifacts(out, modules, api, stream):
    for module in modules:
        for suffix in (".c", ".h", ".cui"):
            artifact = out / (module + suffix)
            if not artifact.is_file() or artifact.stat().st_size == 0:
                raise AssertionError(f"missing direct-C artifact: {artifact}")
    profile = runtime_profile(api, stream)
    for name in ("EverParse.h", "EverParseStreamPrimitives.h"):
        original = profile / name
        if original.is_file():
            copied = (out / name).read_bytes()
            if name == "EverParse.h" and copied.startswith(b"/*++\n"):
                copyright, marker, copied = copied.partition(b"--*/\n")
                if not marker or b"Copyright (c) Microsoft Corporation" not in copyright:
                    raise AssertionError(f"{out / name}: unexpected copyright header")
            if copied != original.read_bytes():
                raise AssertionError(f"{out / name}: runtime header body must be copied unchanged")
    for artifact in out.rglob("*"):
        if artifact.name in ("EverParse.c", "EverParse.cui",
                             "EverParsePulseInternal.h", "EverParsePrivate.h",
                             "EverParsePrivate.c", "SHOULDNOTBETHERE.h",
                             "SHOULDNOTBETHERE.c"):
            raise AssertionError(f"client extraction emitted a runtime-owned artifact: {artifact}")


def generate(name, grammar, api="lowstar", stream="buffer", extra_grammars=()):
    out = output(name)
    args = [ROOT / "bin/everparse-3d.exe", "--api", api, "--input_stream", stream,
            "--fstar", FSTAR, "--batch", "--odir", out]
    if os.environ.get("Z3_EXE"):
        args += ["--z3_executable", os.environ["Z3_EXE"]]
    if stream != "buffer":
        args += ["--input_stream_include", "EverParseStream.h"]
    run(args + [grammar] + list(extra_grammars), out)
    check_artifacts(out, [Path(path).stem for path in (grammar, *extra_grammars)],
                    api, stream)
    return out


def compile_run(out, sources, includes=(), flags=(), name="check", bits32=False):
    options = ["-std=c11", "-O1", "-g", "-Wall", "-Wextra", "-Werror",
               "-Wno-unused-parameter"]
    if SANITIZE and not bits32:
        options += ["-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
    if bits32:
        options += ["-m32", "-DREQUIRE_32BIT"]
    binary = out / name
    run(CC + options + ["-I" + str(out)]
        + ["-I" + str(path) for path in includes]
        + list(sources) + list(flags) + ["-o", binary], out)
    run([binary], out, echo=True)


def large(bits32=False):
    out = output("large")
    flags = shlex.split(os.environ.get("EVERPARSE_FSTAR_OPTIONS", ""))
    flags += ["--include", ROOT / "lib/everparse/lowparse",
             "--include", RUNTIME,
             "--include", HERE, "--include", out,
             "--cache_checked_modules", "--cache_dir", out,
             "--already_cached", "PulseCore,Pulse,Prims,FStar,LowStar,LowParse,EverParse3d.*",
             "--warn_error", "@241"]
    z3_version = os.environ.get("EVERPARSE_Z3_VERSION")
    if z3_version is not None:
        flags = ["--z3version", z3_version] + flags
    if os.environ.get("Z3_EXE"):
        flags = ["--smt", os.environ["Z3_EXE"]] + flags
    run([FSTAR] + flags + [HERE / "LargeExtern.fsti"], out)
    run([FSTAR] + flags + [HERE / "LargeExtern.fst"], out)
    profile = runtime_profile("lowstar", "extern")
    run([FSTAR] + flags + ["--codegen", "C",
                           "--custard_unit", "LargeExtern",
                           "--custard_link", profile / "EverParse.cui",
                           "--custard_monomorphize_types", "true",
                           "--custard_entry_module", "LargeExtern",
                           "--odir", out, HERE / "LargeExtern.fst",
                           "-o", out / "LargeExtern.c"], out)
    if (out / "EverParse.h").exists():
        raise AssertionError("client extraction emitted the runtime-owned EverParse.h")
    header = out / "LargeExtern.h"
    header.write_text('#include "EverParseStream.h"\n' + header.read_text())
    for header in [profile / "EverParse.h", RUNTIME / "EverParseEndianness.h"]:
        shutil.copy2(header, out)
    companion = profile / "EverParseStreamPrimitives.h"
    if companion.is_file():
        shutil.copy2(companion, out)
    check_artifacts(out, ["LargeExtern"], "lowstar", "extern")
    compile_run(out, [out / "LargeExtern.c", HERE / "large.c"],
                [TESTS / "extern/src"], name="check32" if bits32 else "check",
                bits32=bits32)


def client(stream):
    src = TESTS / stream / "src"
    out = generate(stream, src / "Test.3d", stream=stream)
    wrappers = (["-Wl,--wrap=EverParseRead", "-Wl,--wrap=EverParseSkip"]
                if stream == "extern" else ["-Wl,--wrap=_EverParsePeep"])
    compile_run(out, [out / "Test.c", src / "EverParseStream.c",
                      HERE / (stream + ".c")], [src], wrappers)


def probes():
    out = generate("probe-extern", HERE / "ExternProbe.3d", stream="extern")
    compile_run(out, [out / "ExternProbe.c", HERE / "probe-extern.c",
                      TESTS / "extern/src/EverParseStream.c"],
                [TESTS / "extern/src"])
    for api, clients in [
        ("pulse", ROOT / "share/everparse/tests/3d/probe/src"),
        ("lowstar", TESTS / "probe/src"),
    ]:
        out = generate("probe-" + api, TESTS / "probe/src/Probe.3d", api=api)
        compile_run(out, [out / "Probe.c", out / "ProbeWrapper.c",
                          clients / "main.c", clients / "error_handling.c"])
    native_tests = ROOT / "share/everparse/tests/3d"
    out = generate("probe-specialize-batch", native_tests / "Specialize6.3d",
                   api="pulse", extra_grammars=[native_tests / "Specialize5.3d"])
    for module in ("Specialize5", "Specialize6"):
        source = out / (module + ".c")
        if '#include "internal/' in source.read_text():
            raise AssertionError(f"{source}: unexpected shared callback tuple header")
        run(CC + ["-std=c11", "-Wall", "-Wextra", "-Werror", "-Wno-unused-parameter",
                  "-I" + str(out), "-c", source, "-o", out / (module + ".o")], out)
    print("native specialization batch: extraction, C compilation and header layout passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("test", choices=["all", "large", "large32", "extern",
                                        "static", "probes"])
    test = parser.parse_args().test
    if test in ("all", "large", "large32"):
        large(bits32=test == "large32")
    for stream in ("extern", "static"):
        if test in ("all", stream):
            client(stream)
    if test in ("all", "probes"):
        probes()
    print("adapter-tests: " + test + " passed")


if __name__ == "__main__":
    main()

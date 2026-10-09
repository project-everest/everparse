"""Compile and execute focused ABI regressions without changing old fixtures."""

import argparse
import os
import re
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
KRML = os.environ.get("KRML_EXE", str(ROOT / "opt/karamel/out/bin/krml"))
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
    out.mkdir(parents=True, exist_ok=True)
    return out


def check_no_runtime_header(log):
    headers = re.findall(r"KaRaMeL: wrote out \.h files for (.*)", log)
    if not headers or any("EverParse" in line.split(", ") for line in headers):
        raise AssertionError("lowstar extraction must not emit EverParse.h")
    if "EverParsePulseInternal.h" in log:
        raise AssertionError("lowstar extraction emitted an obsolete support header")


def generate(name, grammar, api="lowstar", stream="buffer", extra_grammars=()):
    out = output(name)
    args = [ROOT / "bin/3d.exe", "--api", api, "--input_stream", stream,
            "--fstar", FSTAR, "--batch", "--odir", out]
    if stream != "buffer":
        args += ["--input_stream_include", "EverParseStream.h"]
    log = run(args + [grammar] + list(extra_grammars), out)
    if api == "lowstar":
        check_no_runtime_header(log)
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
    flags = ["--z3version", "4.13.3", "--include", ROOT / "src/lowparse",
             "--include", ROOT / "src/lowparse/pulse",
             "--include", ROOT / "lib/everparse/3d", "--include", HERE,
             "--cache_checked_modules", "--cache_dir", out,
             "--already_cached", "PulseCore,Pulse,Prims,FStar,LowStar",
             "--warn_error", "@241"]
    run([FSTAR] + flags + [HERE / "LargeExtern.fsti"], out)
    run([FSTAR] + flags + [HERE / "LargeExtern.fst"], out)
    # Extract with Custard, not the old --codegen krml. This client is linked
    # against the Custard-extracted runtime (krml/extracted/Custard.krml), and
    # the two extractors disagree about erased arguments -- Custard drops them
    # outright, the old one passes units for KaRaMeL to remove later -- so
    # mixing them makes KaRaMeL reject the call sites on arity. See the comment
    # on fstar_extract_args in src/3d/ocaml/Batch.ml.
    run([FSTAR] + flags + ["--codegen", "Custard", "--custard_backend", "KrmlC",
                           "--custard_split",
                           "--custard_entry_module", "LargeExtern",
                           "--odir", out, HERE / "LargeExtern.fst",
                           "-o", out / "LargeExtern.krml"], out)
    api = ["EverParse3d.Actions.Common", "EverParse3d.Prelude.StaticHeader",
           "EverParse3d.ErrorCode", "EverParse3d.Lowstar.Public",
           "EverParse3d.Lowstar.SupportExtern",
           "EverParse3d.Actions.ErrorHandler.LowstarExtern",
           "EverParse3d.InputStream.LowstarExtern",
           "EverParse3d.InputStream.LowstarExtern.Types",
           "EverParse3d.InputStream.LowstarExtern.Raw",
           "EverParse3d.CopyBuffer.LowstarExtern"]
    log = run([KRML, "-skip-makefiles", "-skip-compilation", "-tmpdir", out,
         "-add-include", '"EverParseStream.h"',
         "-add-include", '"EverParse.h"',
         "-library", "Prims,LowParse.*,EverParse3d.*,Pulse.*",
         "-static-header", "Prims,LowParse.*,EverParse3d.*,Pulse.*",
         "-warn-error", "-9@4-20-26", "-fnoreturn-else", "-fparentheses",
         "-fcurly-braces", "-fmicrosoft", "-fno-shadow",
         "-header", ROOT / "src/3d/noheader.txt", "-minimal", "-fextern-c",
         "-finitialize-locals", "no", "-no-inline-type-abbrev",
         "EverParse3d.Actions.ErrorHandler.LowstarExtern.error_handler"]
        + sorted((ROOT / "lib/everparse/3d/krml/extracted").glob("*.krml"))
        + [out / "LargeExtern.krml",
           "-bundle", "Prims,FStar.*,LowStar.*[rename=SHOULDNOTBETHERE]",
           "-bundle", "+".join(api) + "=" + ",".join(api)
           + "[rename=EverParse,rename-prefix]",
           "-bundle", "EverParse3d.ErrorCode"
           "[rename=EverParsePulseInternal,rename-prefix]",
           "-bundle", "Prims,LowParse.*,EverParse3d.*,Pulse.*"
           "[rename=EverParsePrivate]"], out)
    check_no_runtime_header(log)
    for header in [ROOT / "lib/everparse/3d/krml/lowstar/extern/EverParse.h",
                   ROOT / "src/3d/EverParseEndianness.h"]:
        shutil.copy2(header, out)
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

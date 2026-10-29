"""Compile ABI/behavior consumers against every runtime header profile."""

import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess

from runtime_abi import canonical_type, check_headers
from runtime_headers import CONTRACT, HERE, RUNTIME


def prelude(profile):
    lines = [
        "#include <stdint.h>",
        "typedef void *EVERPARSE_INPUT_STREAM_BASE;",
        "typedef uintptr_t EVERPARSE_EXTRA_T;",
        '#include "EverParse.h"',
    ]
    if profile["static_hooks"]:
        lines.append('#include "static-hooks.h"')
    return lines


def consumers(profile, expected, output):
    prefix = prelude(profile)
    types = prefix + ["int check_types(void) {"]
    for index, (name, declaration) in enumerate(expected["functions"].items()):
        result = canonical_type(declaration["return"])
        parameters = ", ".join(map(canonical_type, declaration["parameters"])) or "void"
        types += [
            f"  {result} (*p{index})({parameters}) = {name};",
            f"  (void)p{index};",
        ]
    for name, declaration in expected["types"].items():
        if declaration["kind"] == "callback":
            result = canonical_type(declaration["return"])
            parameters = ", ".join(map(canonical_type, declaration["parameters"]))
            types += [
                f"  {result} (*callback)({parameters}) = ({name})0;",
                "  (void)callback;",
            ]
    types += ["  return 0;", "}", ""]
    (output / "types.c").write_text("\n".join(types))
    foreign = prefix + ["#include <string.h>"]
    for name, declaration in expected["functions"].items():
        if declaration["linkage"] != "extern":
            continue
        parameters = [t + " p" + str(i)
                      for i, t in enumerate(declaration["parameters"])]
        result = declaration["return"]
        foreign += [result + " " + name + "(" + ", ".join(parameters) + ") {"]
        foreign += ["  (void)p" + str(i) + ";" for i in range(len(parameters))]
        if result != "void":
            foreign += ["  " + result + " value;",
                        "  memset(&value, 0, sizeof(value));", "  return value;"]
        foreign += ["}"]
    for name, ty in expected["values"].items():
        foreign += [ty + " " + name + " = 0;"]
    foreign.append("")
    (output / "foreign.c").write_text("\n".join(foreign))


def check(args):
    check_headers(args.headers)
    reference = json.loads((HERE / "runtime-abi.json").read_text())["profiles"]
    for profile in CONTRACT["profiles"]:
        directory = profile["directory"]
        output = args.build_dir / directory
        output.mkdir(parents=True, exist_ok=True)
        header_dir = args.headers / directory
        shutil.copyfile(header_dir / "EverParse.h", output / "EverParse.h")
        if (header_dir / "EverParseStreamPrimitives.h").exists():
            shutil.copyfile(header_dir / "EverParseStreamPrimitives.h",
                            output / "EverParseStreamPrimitives.h")
        windows = os.name == "nt" or os.environ.get("OS") == "Windows_NT"
        endian = "EverParseEndianness_Windows_NT.h" if windows else "EverParseEndianness.h"
        shutil.copyfile(RUNTIME / endian, output / "EverParseEndianness.h")
        consumers(profile, reference[directory], output)
        flags = ["-D_DEFAULT_SOURCE", "-Wall", "-Wextra", "-Werror", "-O1",
                 "-I" + str(output), "-I" + str(HERE / "tests")]
        if profile["api"] == "lowstar":
            flags += ["-DLOWSTAR"]
            if profile["stream"] != "buffer":
                flags += ["-DEXTERN"]
        if profile["static_hooks"]:
            flags += ["-DSTATIC"]
        sources = [str(HERE / "tests/abi.c"), str(output / "types.c"),
                   str(output / "foreign.c")]
        for language, compiler in (("c", args.cc), ("c++", args.cxx)):
            for architecture in (("", "32") if args.test_32bit else ("",)):
                command = shlex.split(compiler) + [
                    "-x", language, "-std=" + ("c11" if language == "c" else "c++17"),
                ] + flags
                if architecture:
                    command += ["-m32"]
                if args.sanitize:
                    command += ["-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
                for order in range(2 if profile["static_hooks"] else 1):
                    binary = output / ("check-" + language.replace("+", "p")
                                       + architecture + str(order)
                                       + (".exe" if os.name == "nt" else ""))
                    subprocess.run(command + (["-DHOOKS_FIRST"] if order else [])
                                   + sources + ["-o", str(binary)], check=True)
                    subprocess.run([str(binary)], check=True)
        print(directory + ": ABI, behavior, C/C++ and multi-TU checks passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--headers", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--cc", default=os.environ.get("CC", "cc"))
    parser.add_argument("--cxx", default=os.environ.get("CXX", "c++"))
    parser.add_argument("--sanitize", action="store_true")
    parser.add_argument("--32bit", action="store_true", dest="test_32bit",
                        help="Also compile and execute real -m32 C and C++ consumers")
    check(parser.parse_args())


if __name__ == "__main__":
    main()

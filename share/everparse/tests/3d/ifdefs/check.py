"""Check preprocessing and runtime behavior for generated compile-time guards."""

import itertools
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile


def check(output):
    flags = ("ABOVE_DIAGONAL", "STRICT", "DIM3", "DIM4")
    configurations = [
        dict(zip(flags, values))
        for values in itertools.product((None, "0"), repeat=len(flags))
    ] + [dict.fromkeys(flags, ""), dict.fromkeys(flags, "1")]
    with tempfile.TemporaryDirectory(prefix="everparse-ifdef-") as temporary:
        directory = Path(temporary)
        for path in output.iterdir():
            if path.suffix in (".c", ".h"):
                shutil.copy2(path, directory / path.name)
        shutil.copy2(Path(__file__).with_suffix(".c"), directory / "check.c")
        for index, configuration in enumerate(configurations):
            (directory / "compile_time_flags.h").write_text(
                "".join(f"#define {flag} {value}\n"
                        for flag, value in configuration.items()
                        if value is not None)
            )
            for variable, default, standard in (
                ("CC", "cc", "c11"), ("CXX", "c++", "c++17")
            ):
                executable = directory / f"check-{index}-{standard}"
                subprocess.run(
                    shlex.split(os.environ.get(variable, default)) +
                    [f"-std={standard}", "-Wall", "-Wextra", "-Werror",
                     "-I" + str(directory), "-x",
                     "c" if standard == "c11" else "c++",
                     str(directory / "AnonNestedStructIfDefs.c"),
                     str(directory / "CompileTimeIf.c"),
                     str(directory / "check.c"), "-o", str(executable)],
                    check=True,
                )
                subprocess.run([str(executable)], check=True)
    print(f"{output}: C/C++ compile-time flag matrix passed")


for argument in sys.argv[1:]:
    check(Path(argument))

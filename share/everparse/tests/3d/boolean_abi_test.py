"""Execute both public Boolean ABIs, not just their generated spelling.

Mutable checks noncanonical Low* bytes, scalar/external Bool, in-place reads,
canonical writes after success/failure, and two parameters aliasing one cell.
Probes checks noncanonical callback results and failed refs, with each callback
independently rejecting validation. Including the validator headers in each C
client also makes a callback signature mismatch a compile error.
"""

import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile


def main():
    executable, fstar = sys.argv[1:]
    executable = str(Path(executable).resolve())
    here = Path(__file__).resolve().parent
    fixture = here / "boolean"
    compiler = shlex.split(os.environ.get("CC", "cc"))
    environment = dict(os.environ)

    def run(command):
        result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, env=environment)
        if result.returncode:
            raise AssertionError(f"{shlex.join(map(str, command))}\n{result.stdout}")

    # Keep intermediate artifacts under the test tree, never in system scratch.
    with tempfile.TemporaryDirectory(prefix="out.boolean-", dir=here) as directory:
        environment["TMPDIR"] = directory
        for api in ("lowstar", "pulse"):
            output = Path(directory) / api
            output.mkdir()
            command = [executable, "--api", api, "--odir", str(output),
                       "--batch", "--skip_c_makefiles"]
            if fstar:
                command += ["--fstar", fstar]
            run(command + [str(fixture / "Mutable.3d"), str(fixture / "Probes.3d")])
            for module, client in (("Mutable", "mutable.c"), ("Probes", "probes.c")):
                binary = output / module
                run(compiler + ["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror",
                                "-Wno-unused-parameter", "-Wno-ignored-qualifiers",
                                "-D_DEFAULT_SOURCE", "-I", str(output),
                                *(["-DTEST_LOWSTAR"] if api == "lowstar" else []),
                                str(fixture / client), str(output / f"{module}.c"),
                                str(output / f"{module}Wrapper.c"), "-o", str(binary)])
                run([str(binary)])
    print("Boolean scalar/ref aliasing, canonical writes and probe ABI: PASS")


if __name__ == "__main__":
    main()

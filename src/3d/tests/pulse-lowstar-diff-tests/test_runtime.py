"""Compare the public runtime header independently of generated validators."""

import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

from run import runtime_headers


class RuntimeTests(unittest.TestCase):
    def test_public_runtime_behavior_and_layout(self):
        here = Path(__file__).resolve().parent
        home = here.parents[3]
        with tempfile.TemporaryDirectory(prefix="runtime-", dir=here) as temporary:
            for backend in ("buffer", "extern", "static"):
                for compiler, language in ((os.environ.get("CC", "cc"), "c"),
                                           (os.environ.get("CXX", "c++"), "c++")):
                    outputs = []
                    for api in ("legacy_lowstar", "lowstar"):
                        with self.subTest(backend=backend, language=language, api=api):
                            headers = runtime_headers(home, api, backend)
                            header = (headers / "EverParse.h").read_text()
                            self.assertNotIn("EverParsePulseInternal.h", header)
                            self.assertNotIn("EVERPARSE_VIEW_OK", header)
                            self.assertEqual("EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS" in header,
                                             api == "lowstar")
                            if api == "lowstar":
                                self.assertEqual(sorted(p.name for p in headers.iterdir()), ["EverParse.h"])
                            binary = Path(temporary) / f"{backend}-{language}-{api}"
                            flags = ["-DTEST_EXTERN"] if backend != "buffer" else []
                            if backend == "static":
                                flags.append("-DTEST_STATIC")
                            if api == "lowstar":
                                flags.append("-DTEST_LOWSTAR")
                            result = subprocess.run(
                                [*shlex.split(compiler), "-x", language, "-Wall", "-Wextra", "-Werror",
                                 "-Wno-unused-function", f"-I{headers}", f"-I{home / 'src/3d'}",
                                 *flags, str(here / "runtime_regression.c"), "-o", str(binary)],
                                capture_output=True, text=True)
                            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                            outputs.append(subprocess.check_output([str(binary)], text=True))
                    if len(outputs) == 2:
                        self.assertEqual(outputs[0], outputs[1])


if __name__ == "__main__":
    unittest.main()

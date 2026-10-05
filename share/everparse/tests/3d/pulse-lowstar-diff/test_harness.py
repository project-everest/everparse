import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from check_api import check_api
import gen_seeds


HERE = Path(__file__).resolve().parent


class ApiTests(unittest.TestCase):
    def test_expected_apis_and_wrong_results(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            header = directory / "Example.h"
            for api, result, body in (
                    ("lowstar", "uint64_t", "EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS"),
                    ("pulse", "uint8_t", "")):
                header.write_text(f"{result}\nExampleValidateT(void);\n")
                (directory / "Example.c").write_text(body)
                check_api(api, directory)
                other = "pulse" if api == "lowstar" else "lowstar"
                with self.assertRaisesRegex(ValueError, "validator results"):
                    check_api(other, directory)

    def test_legacy_output_with_leftover_runtime_header_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory / "EverParsePulseInternal.h").write_text("/* stale runtime */")
            (directory / "Example.h").write_text("uint64_t ExampleValidateT(void);")
            with self.assertRaisesRegex(ValueError, "not generated with --api lowstar"):
                check_api("lowstar", directory)

    def test_missing_empty_and_mixed_outputs_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for path in (directory, directory / "missing"):
                with self.assertRaisesRegex(ValueError, "missing generated"):
                    check_api("pulse", path)
            (directory / "Example.h").write_text("uint8_t ExampleValidateT(void);")
            (directory / "Other.h").write_text("uint64_t OtherValidateT(void);")
            with self.assertRaisesRegex(ValueError, "validator results"):
                check_api("pulse", directory)

    def test_mixed_legacy_and_lowstar_implementations_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for name in ("Example", "Other"):
                (directory / f"{name}.h").write_text(f"uint64_t {name}ValidateT(void);")
            (directory / "Example.c").write_text("EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS")
            other = directory / "Other.c"
            other.write_text("EVERPARSE_VALIDATOR_ERROR_GENERIC")
            with self.assertRaisesRegex(ValueError, "Other.h: not generated"):
                check_api("lowstar", directory)
            other.write_text('#include "EverParsePulseInternal.h"\nEVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS')
            with self.assertRaisesRegex(ValueError, "obsolete separate"):
                check_api("lowstar", directory)

    def test_seed_generation_uses_relocated_lowstar_sources_and_explicit_api(self):
        output = "uint8_t witness0_0[1] = {42};\n// witness0[0].buf // ACCEPTED"
        with patch("gen_seeds.subprocess.run", return_value=subprocess.CompletedProcess(
                [], 0, output, "")) as run:
            self.assertEqual(gen_seeds.witnesses("/toolchain", "Arithmetic.3d", "Arithmetic._Check"),
                             [(42,)])
        argv = run.call_args.args[0]
        self.assertEqual(argv[argv.index("--api") + 1], "lowstar")
        self.assertIn(str(HERE.parent / "lowstar/Arithmetic.3d"), argv)


class BuildTests(unittest.TestCase):
    def test_direct_invocation_builds_both_corpora_and_prebuilt_avoids_rebuild(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Makefile").write_text(
                ".PHONY: 3d-unit-test 3d-pulse-test\n"
                "3d-unit-test 3d-pulse-test:\n\t@echo $@ >> built\n")
            env = dict(os.environ)
            for key in ("MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES"):
                env.pop(key, None)
            argv = ["make", "--no-print-directory", "-f", str(HERE / "Makefile"),
                    "prepare", f"EVERPARSE_HOME={root}"]
            subprocess.run(argv, cwd=root, env=env, check=True, capture_output=True)
            self.assertEqual((root / "built").read_text().splitlines(),
                             ["3d-unit-test", "3d-pulse-test"])
            (root / "built").unlink()
            subprocess.run([*argv, "DIFF_PREBUILT=1"], cwd=root, env=env,
                           check=True, capture_output=True)
            self.assertFalse((root / "built").exists())

    def test_missing_subdirectory_is_failure_not_skip(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = subprocess.run(
                [str(HERE / "run_subdir.sh"), "check_complete/obj", "1"],
                env=dict(os.environ, EVERPARSE_HOME=tmp), capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing output", result.stderr)
            self.assertNotIn("skipping", result.stderr)


if __name__ == "__main__":
    unittest.main()

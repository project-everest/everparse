"""Check API selection, generated command propagation, and hash separation."""

import os
import pathlib
import re
import shlex
import subprocess
import sys
import tempfile


def main():
    executable, fstar = sys.argv[1:]
    executable = str(pathlib.Path(executable).resolve())
    fstar_options = ["--fstar", fstar] if fstar else []

    def run(*args, succeeds=True):
        result = subprocess.run(
            [executable, *fstar_options, *map(str, args)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if (result.returncode == 0) != succeeds:
            raise AssertionError(
                f"{args}: unexpected exit {result.returncode}\n{result.stdout}"
            )
        return result.stdout

    help_text = run("--help")
    assert "--api" in help_text and "pulse|lowstar" in help_text
    assert "legacy_lowstar" not in help_text
    assert "--pulse" not in help_text
    for api in ["pulse", "lowstar"]:
        for option in ["goto_for_early_return", "blank_lines",
                       "line_comments"]:
            message = run("--api", api, f"--{option}", succeeds=False)
            assert f"--{option}: not implemented yet" in message
    # The legacy Low* backend is gone: lowstar is the default, and
    # legacy_lowstar is rejected like any other unknown backend because
    # Options.Base.valid_api no longer accepts it.
    for args in [("--pulse",), ("--no_pulse",), ("--api",),
                 ("--api", "invalid"), ("--api", "legacy_lowstar"),
                 ("--__micro_step", "copy_pulse_internal_h")]:
        run(*args, succeeds=False)

    with tempfile.TemporaryDirectory(
            prefix="out.api-", dir=pathlib.Path(__file__).resolve().parent) as directory:
        root = pathlib.Path(directory)
        source = root / "ApiChoice.3d"
        source.write_text(
            "entrypoint typedef struct _T { UINT8 x; } T;\n"
            "entrypoint typedef struct _T_core { UINT8 x; } T_core;\n",
            encoding="utf-8",
        )
        modes = {
            "default": [],
            "pulse": ["--api", "pulse"],
            "lowstar": ["--api", "lowstar"],
            "reset": ["--api", "lowstar", "--no_api"],
        }
        for name, options in modes.items():
            output = root / name
            output.mkdir()
            run(*options, "--odir", output, "--no_copy_everparse_h", source)

        # Omitting --api selects lowstar, and --no_api resets an earlier
        # --api back to that default, so all three must agree byte for byte.
        for extension in [".fst", ".fsti", "Wrapper.c", "Wrapper.h"]:
            expected = (root / "default" / f"ApiChoice{extension}").read_bytes()
            for name in ["lowstar", "reset"]:
                assert (root / name / f"ApiChoice{extension}").read_bytes() == expected
        # ... and must differ from --api pulse, so that an accidental flip of
        # the default is caught here rather than downstream in generated C.
        assert (root / "default" / "ApiChoice.fst").read_bytes() != (
            root / "pulse" / "ApiChoice.fst"
        ).read_bytes()
        assert "Pulse.Lib.Pervasives" in (
            root / "pulse" / "ApiChoice.fst"
        ).read_text()
        assert "_Static_assert(sizeof(size_t)" in (
            root / "pulse" / "ApiChoiceWrapper.c"
        ).read_text()
        # --api lowstar is Pulse-implemented too, but exposes the Low*-compatible
        # C ABI rather than the native Pulse one.
        assert "_Static_assert(sizeof(size_t)" not in (
            root / "lowstar" / "ApiChoiceWrapper.c"
        ).read_text()
        assert "Pulse.Lib.Pervasives" in (
            root / "lowstar" / "ApiChoice.fst"
        ).read_text()
        assert "EverParse3d.Lowstar.BufferAdapter" in (
            root / "lowstar" / "ApiChoice.fst"
        ).read_text()
        validators = re.findall(
            r"^\s*let (validate_\w+)\b",
            (root / "lowstar" / "ApiChoice.fst").read_text(),
            re.MULTILINE,
        )
        assert validators and len(validators) == len(set(validators))

        for name in ["pulse", "lowstar"]:
            options = modes[name]
            output = root / name
            run(*options, "--odir", output, "--makefile", "gmake", source)
            makefile = (output / "EverParse.Makefile").read_text()
            assert f"--api {options[1]}" in makefile
            assert "--pulse" not in makefile and "--no_pulse" not in makefile
            assert "ApiChoice.cui" in makefile
            assert "__produce_c_from_existing_checked" in makefile
            assert "__produce_c_from_existing_krml" not in makefile
            assert ".krml" not in makefile
            assert " &: " in makefile
            assert "EverParsePulseEndianness.h" not in makefile
            if name == "lowstar":
                assert "EverParsePulseInternal.h" not in makefile
            lines = makefile.splitlines()
            recipes = [
                index for index, line in enumerate(lines)
                if line.startswith("\t$(EVERPARSE_CMD)")
            ]
            assert recipes
            for index in recipes:
                assert f"--api {options[1]}" in lines[index]
                assert str(output / "EverParse.Makefile") in lines[index - 1]

            run(*options, "--odir", output, "--makefile", "nmake", source)
            nmake = (output / "EverParse.Makefile").read_text()
            assert " &: " not in nmake and ".krml" not in nmake
            unit_rule = next(line for line in nmake.splitlines()
                             if "ApiChoice.cui" in line and " : " in line)
            assert "ApiChoice.c " in unit_rule and "ApiChoice.h " in unit_rule
            assert "__produce_c_from_existing_checked" in nmake

        home = pathlib.Path(executable).parent.parent
        for backend in ["buffer", "extern", "static"]:
            output = root / f"lowstar-{backend}"
            output.mkdir()
            options = ["--api", "lowstar", "--input_stream", backend, "--odir", output]
            run(*options, "--makefile", "gmake", "--no_copy_everparse_h", source)
            makefile = (output / "EverParse.Makefile").read_text()
            assert f"lib/everparse/3d/runtime/lowstar/{backend}" in makefile
            assert "src/3d/prelude/" not in makefile
            assert "EverParsePulseInternal.h" not in makefile
            assert not (output / "EverParse.h").exists()
            run(*options, "--__micro_step", "copy_everparse_h", "--no_clang_format")
            expected = home / f"lib/everparse/3d/runtime/lowstar/{backend}/EverParse.h"
            assert (output / "EverParse.h").read_bytes() == expected.read_bytes()
            assert (output / "EverParseEndianness.h").is_file()
            assert not (output / "EverParsePulseInternal.h").exists()
            assert not (output / "EverParsePulse.h").exists()

        for api in ["pulse", "lowstar"]:
            for backend in ["extern", "static"]:
                output = root / f"{api}-{backend}-ownership"
                output.mkdir()
                options = ["--api", api, "--input_stream", backend, "--odir", output]
                run(*options, "--makefile", "gmake", source)
                makefile = (output / "EverParse.Makefile").read_text()
                companion = output / "EverParseStreamPrimitives.h"
                assert f"copy_everparse_h {companion.name}" in makefile
                header_set = next(line for line in makefile.splitlines()
                                  if line.startswith("EVERPARSE_ALL_H_FILES"))
                assert companion.name in header_set
                run(*options, "--__micro_step", "copy_everparse_h", companion.name,
                    "--no_clang_format")
                assert companion.is_file()
                assert not (output / "EverParse.h").exists()
                previous = companion.stat().st_mtime_ns
                run(*options, "--__micro_step", "copy_everparse_h", "EverParse.h",
                    "--no_clang_format")
                assert (output / "EverParse.h").is_file()
                assert companion.stat().st_mtime_ns == previous

        for api in ["pulse", "lowstar"]:
            outputs = {}
            for mode, flags in [
                    ("normal", ["--batch"]),
                    ("hoisted", ["--hoist_locals"]),
                    ("reset", ["--hoist_locals", "--no_hoist_locals", "--batch"])]:
                output = root / f"{api}-{mode}"
                output.mkdir()
                outputs[mode] = output
                log = run("--api", api, *flags, "--odir", output,
                          "--save_hashes", source)
                extraction_commands = [
                    line for line in log.splitlines()
                    if line.startswith("Running: ") and "--codegen C" in line
                ]
                assert extraction_commands, log
                assert all(("--custard_hoist_locals" in line) == (mode == "hoisted")
                           for line in extraction_commands), log
                verification_commands = [
                    line for line in log.splitlines()
                    if line.startswith("Running: ") and "--cache_checked_modules" in line
                ]
                assert verification_commands, log
                assert all("--custard_hoist_locals" not in line
                           for line in verification_commands), log

            for suffix in [".c", ".h", "Wrapper.c", "Wrapper.h"]:
                expected = (outputs["normal"] / f"ApiChoice{suffix}").read_bytes()
                assert (outputs["reset"] / f"ApiChoice{suffix}").read_bytes() == expected
            assert (outputs["normal"] / "ApiChoice.c").read_bytes() != (
                outputs["hoisted"] / "ApiChoice.c"
            ).read_bytes()
            if api == "lowstar":
                assert (outputs["normal"] / "ApiChoiceWrapper.c").read_bytes() != (
                    outputs["hoisted"] / "ApiChoiceWrapper.c"
                ).read_bytes()

            output = outputs["hoisted"]
            generated = (output / "ApiChoice.c").read_text()
            generated = re.sub(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"',
                               "", generated, flags=re.DOTALL)
            depth = 0
            declarations = 0
            for line in generated.splitlines():
                if depth and re.match(
                        r"\s*(?:u?int(?:8|16|32|64)_t|size_t|bool)\s+[*]?\s*\w+",
                        line):
                    assert depth == 1, line
                    declarations += 1
                depth += line.count("{") - line.count("}")
            assert declarations and depth == 0, generated
            for c_file in ["ApiChoice.c", "ApiChoiceWrapper.c"]:
                subprocess.run(
                    shlex.split(os.environ.get("CC", "cc")) +
                    ["-std=c11", "-Wall", "-Wextra", "-Werror", "-fsyntax-only",
                     "-I", str(output), str(output / c_file)],
                    check=True,
                )
            run("--api", api, "--hoist_locals", "--odir", output,
                "--check_hashes", "strong", source)
            for make in ["gmake", "nmake"]:
                run("--api", api, "--hoist_locals", "--odir", output,
                    "--makefile", make, source)
                makefile = (output / "EverParse.Makefile").read_text()
                recipes = [
                    line for line in makefile.splitlines()
                    if line.startswith("\t$(EVERPARSE_CMD)")
                ]
                assert recipes
                assert all("--hoist_locals" in line for line in recipes), makefile

        for api in ["pulse", "lowstar"]:
            outputs = {}
            for mode, flags, init in [
                    ("normal", ["--batch"], None),
                    ("c99", ["--init_locals", "c99", "--batch"], "c99"),
                    ("hoisted-c89", ["--hoist_locals", "--init_locals", "c89"], "c89"),
                    ("hoisted-c23", ["--hoist_locals", "--init_locals", "c23"], "c23"),
                    ("reset", ["--init_locals", "c99", "--no_init_locals", "--batch"], None)]:
                output = root / f"{api}-init-{mode}"
                output.mkdir()
                outputs[mode] = output
                log = run("--api", api, *flags, "--odir", output,
                          "--save_hashes", source)
                running = [line for line in log.splitlines()
                           if line.startswith("Running: ")]
                extraction_commands = [l for l in running if "--codegen C" in l]
                assert extraction_commands, log
                expected = f"--custard_init_locals {init}" if init else None
                assert all((expected in line) if expected
                           else "--custard_init_locals" not in line
                           for line in extraction_commands), log
                verification_commands = [
                    l for l in running if "--cache_checked_modules" in l]
                assert verification_commands, log
                assert all("--custard_init_locals" not in line
                           for line in verification_commands), log

            for suffix in [".c", ".h", "Wrapper.c", "Wrapper.h"]:
                expected = (outputs["normal"] / f"ApiChoice{suffix}").read_bytes()
                assert (outputs["reset"] / f"ApiChoice{suffix}").read_bytes() == expected

            # After hoisting, every function-level declaration is zeroed.
            for mode in ["hoisted-c89", "hoisted-c23"]:
                output = outputs[mode]
                generated = (output / "ApiChoice.c").read_text()
                generated = re.sub(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"',
                                   "", generated, flags=re.DOTALL)
                depth = 0
                declarations = 0
                for line in generated.splitlines():
                    if depth and re.match(
                            r"\s*(?:u?int(?:8|16|32|64)_t|size_t|bool)\s+[*]?\s*\w+",
                            line):
                        assert "=" in line, line
                        declarations += 1
                    depth += line.count("{") - line.count("}")
                assert declarations and depth == 0, generated
                standard = "c2x" if mode == "hoisted-c23" else "c11"
                for c_file in ["ApiChoice.c", "ApiChoiceWrapper.c"]:
                    subprocess.run(
                        shlex.split(os.environ.get("CC", "cc")) +
                        [f"-std={standard}", "-Wall", "-Wextra", "-Werror",
                         "-fsyntax-only", "-I", str(output), str(output / c_file)],
                        check=True,
                    )
            assert (outputs["normal"] / "ApiChoiceWrapper.c").read_bytes() != (
                outputs["c99"] / "ApiChoiceWrapper.c"
            ).read_bytes()

            output = outputs["hoisted-c89"]
            run("--api", api, "--hoist_locals", "--init_locals", "c89",
                "--odir", output, "--check_hashes", "strong", source)
            for make in ["gmake", "nmake"]:
                run("--api", api, "--hoist_locals", "--init_locals", "c89",
                    "--odir", output, "--makefile", make, source)
                makefile = (output / "EverParse.Makefile").read_text()
                recipes = [
                    line for line in makefile.splitlines()
                    if line.startswith("\t$(EVERPARSE_CMD)")
                ]
                assert recipes
                assert all("--hoist_locals --init_locals c89 " in line
                           for line in recipes), makefile

        # Weak hashes require no extraction, and must reject another API
        # even when its grammar and tool versions are identical.
        for name, options in modes.items():
            output = root / name
            for extension in [".h", ".c"]:
                (output / f"ApiChoice{extension}").write_text(
                    "/* Identical C fixture for API hash isolation. */\n",
                    encoding="utf-8",
                )
            run(*options, "--odir", output, "--__micro_step", "save_hashes", source)
            run(*options, "--odir", output, "--check_hashes", "weak", source)
        # Omitting --api selects lowstar, so the two must agree both ways.
        run("--api", "lowstar", "--odir", root / "default",
            "--check_hashes", "weak", source)
        run("--odir", root / "lowstar", "--check_hashes", "weak", source)
        for name in ["pulse", "lowstar"]:
            for other in ["pulse", "lowstar"]:
                if name != other:
                    run(*modes[name], "--odir", root / other,
                        "--check_hashes", "weak", source, succeeds=False)

    print("API selection, hoisting, local initialization, generated commands, and hash isolation: PASS")


if __name__ == "__main__":
    main()

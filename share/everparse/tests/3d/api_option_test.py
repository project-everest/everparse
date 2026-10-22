"""Check API selection, generated command propagation, and hash separation."""

import pathlib
import re
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
        for option in ["hoist_locals", "goto_for_early_return", "blank_lines",
                       "line_comments", "init_locals"]:
            arguments = [f"--{option}"] + (["c99"] if option == "init_locals" else [])
            message = run("--api", api, *arguments, succeeds=False)
            assert f"--{option}: not implemented yet" in message
    # The legacy Low* backend is gone: lowstar is the default, and
    # legacy_lowstar is rejected like any other unknown backend because
    # Options.Base.valid_api no longer accepts it.
    for args in [("--pulse",), ("--no_pulse",), ("--api",),
                 ("--api", "invalid"), ("--api", "legacy_lowstar"),
                 ("--__micro_step", "copy_pulse_internal_h")]:
        run(*args, succeeds=False)

    with tempfile.TemporaryDirectory(prefix="everparse-api-") as directory:
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
        assert "EverParsePulse.h" in (
            root / "pulse" / "ApiChoiceWrapper.c"
        ).read_text()
        # --api lowstar is Pulse-implemented too, but exposes the Low*-compatible
        # C ABI rather than the native Pulse one.
        assert "EverParsePulse.h" not in (
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
            if name == "lowstar":
                assert "EverParsePulseInternal.h" not in makefile
                assert "EverParsePulseEndianness.h" not in makefile
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
            assert f"lib/everparse/3d/krml/lowstar/{backend}" in makefile
            assert "src/3d/prelude/" not in makefile
            assert "EverParsePulseInternal.h" not in makefile
            assert not (output / "EverParse.h").exists()
            run(*options, "--__micro_step", "copy_everparse_h", "--no_clang_format")
            expected = home / f"lib/everparse/3d/krml/lowstar/{backend}/EverParse.h"
            assert (output / "EverParse.h").read_bytes() == expected.read_bytes()
            assert (output / "EverParseEndianness.h").is_file()
            assert not (output / "EverParsePulseInternal.h").exists()
            assert not (output / "EverParsePulse.h").exists()

        for api in ["pulse", "lowstar"]:
            output = root / f"{api}-static-ownership"
            output.mkdir()
            options = ["--api", api, "--input_stream", "static", "--odir", output]
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

    print("API selection, generated commands, and hash isolation: PASS")


if __name__ == "__main__":
    main()

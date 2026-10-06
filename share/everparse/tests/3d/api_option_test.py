"""Check API selection, generated command propagation, and hash separation."""

import pathlib
import re
import subprocess
import sys
import tempfile


def main():
    executable, fstar = sys.argv[1:]
    executable = str(pathlib.Path(executable).resolve())

    def run(*args, succeeds=True):
        result = subprocess.run(
            [executable, "--fstar", fstar, *map(str, args)],
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
    # The legacy Low* backend is gone: pulse is the default and
    # Options.Base.valid_api no longer accepts legacy_lowstar.
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

        # No --api, and --no_api after one, both select the default, pulse.
        for extension in [".fst", ".fsti", "Wrapper.c", "Wrapper.h"]:
            expected = (root / "pulse" / f"ApiChoice{extension}").read_bytes()
            for name in ["default", "reset"]:
                assert (root / name / f"ApiChoice{extension}").read_bytes() == expected
        assert "Pulse.Lib.Pervasives" in (
            root / "pulse" / "ApiChoice.fst"
        ).read_text()
        assert "EverParsePulse.h" in (
            root / "pulse" / "ApiChoiceWrapper.c"
        ).read_text()
        assert "Pulse.Lib.Pervasives" in (
            root / "lowstar" / "ApiChoice.fst"
        ).read_text()
        assert "EverParsePulse.h" not in (
            root / "lowstar" / "ApiChoiceWrapper.c"
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
        # The default is pulse, so its hashes are the pulse ones.
        run("--api", "pulse", "--odir", root / "default",
            "--check_hashes", "weak", source)
        run("--odir", root / "pulse", "--check_hashes", "weak", source)
        for name in ["pulse", "lowstar"]:
            for other in ["pulse", "lowstar"]:
                if name != other:
                    run(*modes[name], "--odir", root / other,
                        "--check_hashes", "weak", source, succeeds=False)

    print("API selection, generated commands, and hash isolation: PASS")


if __name__ == "__main__":
    main()

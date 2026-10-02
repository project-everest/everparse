"""Check API selection, generated command propagation, and hash separation."""

import pathlib
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
    assert "--api" in help_text and "legacy_lowstar|pulse" in help_text
    assert "--pulse" not in help_text
    for args in [("--pulse",), ("--no_pulse",), ("--api",),
                 ("--api", "invalid"), ("--api", "lowstar")]:
        run(*args, succeeds=False)

    with tempfile.TemporaryDirectory(prefix="everparse-api-") as directory:
        root = pathlib.Path(directory)
        source = root / "ApiChoice.3d"
        source.write_text(
            "entrypoint typedef struct _T { UINT8 x; } T;\n", encoding="utf-8"
        )
        modes = {
            "default": [],
            "legacy": ["--api", "legacy_lowstar"],
            "pulse": ["--api", "pulse"],
            "reset": ["--api", "pulse", "--no_api"],
        }
        for name, options in modes.items():
            output = root / name
            output.mkdir()
            run(*options, "--odir", output, "--no_copy_everparse_h", source)

        for extension in [".fst", ".fsti", "Wrapper.c", "Wrapper.h"]:
            expected = (root / "default" / f"ApiChoice{extension}").read_bytes()
            for name in ["legacy", "reset"]:
                assert (root / name / f"ApiChoice{extension}").read_bytes() == expected
        assert "Pulse.Lib.Pervasives" in (
            root / "pulse" / "ApiChoice.fst"
        ).read_text()
        assert "Pulse.Lib.Pervasives" not in (
            root / "default" / "ApiChoice.fst"
        ).read_text()
        assert "EverParsePulse.h" in (
            root / "pulse" / "ApiChoiceWrapper.c"
        ).read_text()
        assert "EverParsePulse.h" not in (
            root / "default" / "ApiChoiceWrapper.c"
        ).read_text()

        for name in ["legacy", "pulse"]:
            options = modes[name]
            output = root / name
            run(*options, "--odir", output, "--makefile", "gmake", source)
            makefile = (output / "EverParse.Makefile").read_text()
            assert f"--api {options[1]}" in makefile
            assert "--pulse" not in makefile and "--no_pulse" not in makefile
            lines = makefile.splitlines()
            recipes = [
                index for index, line in enumerate(lines)
                if line.startswith("\t$(EVERPARSE_CMD)")
            ]
            assert recipes
            for index in recipes:
                assert f"--api {options[1]}" in lines[index]
                assert str(output / "EverParse.Makefile") in lines[index - 1]

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
        run("--api", "legacy_lowstar", "--odir", root / "default",
            "--check_hashes", "weak", source)
        run("--odir", root / "legacy", "--check_hashes", "weak", source)
        run("--api", "pulse", "--odir", root / "legacy",
            "--check_hashes", "weak", source, succeeds=False)
        run("--api", "legacy_lowstar", "--odir", root / "pulse",
            "--check_hashes", "weak", source, succeeds=False)

    print("API selection, generated commands, and hash isolation: PASS")


if __name__ == "__main__":
    main()

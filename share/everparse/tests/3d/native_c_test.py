"""Check native CUI reuse, incremental builds, and grouped-output repair."""

import pathlib
import subprocess
import sys
import tempfile


def main():
    executable, fstar = sys.argv[1:]
    home = pathlib.Path(executable).resolve().parent.parent
    fixture = pathlib.Path(__file__).resolve().parent / "modules"

    with tempfile.TemporaryDirectory(prefix="everparse-native-") as directory:
        output = pathlib.Path(directory)
        command = [
            "make", "-s", "-j4", "-C", str(fixture), "world",
            f"EVERPARSE_HOME={home}", f"EVERPARSE_OUTPUT_DIR={output}",
            f"FSTAR_EXE={fstar}", "KRML_EXE=everparse-no-karamel",
        ]

        def build():
            result = subprocess.run(
                command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            if result.returncode:
                raise AssertionError(result.stdout)

        def snapshot():
            return {
                file.name: file.stat().st_mtime_ns
                for file in output.iterdir()
                if file.suffix in (".c", ".h", ".cui", ".fst", ".fsti", ".checked")
            }

        build()
        for name in ("Constants", "Point", "TPoint", "Test"):
            assert (output / f"{name}.cui").is_file()
        assert not list(output.glob("*.krml"))
        before = snapshot()
        build()
        assert before == snapshot(), "A no-op build rewrote generated artifacts"

        for missing in ("Point.cui", "Test.h", "Test.c"):
            before = snapshot()
            (output / missing).unlink()
            build()
            assert (output / missing).is_file(), f"Missing output not repaired: {missing}"
            after = snapshot()
            unrelated = ("Constants.",)
            if missing.startswith("Test."):
                unrelated += ("Point.", "TPoint.")
            for name in before:
                if name.startswith(unrelated):
                    assert before[name] == after[name], f"Unrelated output rewritten: {name}"

    print("Native CUI reuse, no-op builds, and grouped-output repair: PASS")


if __name__ == "__main__":
    main()

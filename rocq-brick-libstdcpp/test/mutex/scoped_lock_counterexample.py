#!/usr/bin/env python3
"""Compile and run the scoped_lock contract counterexample with libstdc++."""
import pathlib
import subprocess
import sys
import tempfile


def main() -> None:
    cxx, source = sys.argv[1:]
    with tempfile.TemporaryDirectory(prefix="scoped-lock-counterexample-") as tmp:
        executable = pathlib.Path(tmp) / "counterexample"
        subprocess.run(
            [cxx, "-std=c++17", "-stdlib=libstdc++", "-pthread", "-O1",
             source, "-o", str(executable)],
            check=True, timeout=60,
        )
        subprocess.run([str(executable)], check=True, timeout=20)


if __name__ == "__main__":
    main()

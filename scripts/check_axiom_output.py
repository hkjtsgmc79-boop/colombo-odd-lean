#!/usr/bin/env python3
"""Check that the release axiom audit has exactly the expected kernel output."""

from __future__ import annotations

from pathlib import Path
import sys


EXPECTED_SUFFIX = "depends on axioms: [propext, Classical.choice, Quot.sound]"
EXPECTED_COUNT = 5


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_axiom_output.py AXIOM_LOG")
        return 2

    lines = [
        line.strip()
        for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines()
        if "depends on axioms:" in line
    ]
    if len(lines) != EXPECTED_COUNT or any(
        not line.endswith(EXPECTED_SUFFIX) for line in lines
    ):
        print("Kernel axiom audit: FAIL")
        print("\n".join(lines) if lines else "no axiom lines found")
        return 1

    print(f"Kernel axiom audit: PASS ({EXPECTED_COUNT} theorems)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

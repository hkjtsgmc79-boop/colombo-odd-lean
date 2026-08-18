#!/usr/bin/env python3
"""Fail if production Lean sources contain placeholders or project axioms."""

from __future__ import annotations

from pathlib import Path
import re
import sys


PLACEHOLDER = re.compile(r"\b(?:sorry|admit|sorryAx)\b|by\?")
PROJECT_AXIOM = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|local)\s+)*(?:axiom|opaque)\b"
    r"|\bunsafe\b"
)


def production_files() -> list[Path]:
    return [Path("ColomboGeneralK2.lean"), *sorted(Path("ColomboGeneralK2").rglob("*.lean"))]


def main() -> int:
    failures: list[str] = []
    files = production_files()
    for path in files:
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if PLACEHOLDER.search(line) or PROJECT_AXIOM.search(line):
                failures.append(f"{path}:{number}:{line}")

    if failures:
        print("Production source audit: FAIL")
        print("\n".join(failures))
        return 1

    print(f"Production source audit: PASS ({len(files)} Lean files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

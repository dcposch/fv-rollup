#!/usr/bin/env python3
"""Check pinned dependency revisions and reject local changes."""
from pathlib import Path
import subprocess
from typing import NamedTuple

ROOT = Path(__file__).resolve().parent.parent


class Dependency(NamedTuple):
    name: str
    package: Path
    revision: str


DEPENDENCIES = (
    Dependency("EVMLean", ROOT / ".lake/packages/evmlean",
               "cdbd150780e6f41ebb989eaedc2248bf9ec16861"),
    Dependency("EquiVM", ROOT / ".lake/packages/EquiVM",
               "3db734e592aae8da5bc103db7eec61def39c27f5"),
)


def check_dependency(model):
    if not model.package.is_dir():
        raise SystemExit(f"Missing {model.name} dependency. Run lake update first.")
    def git(*args):
        return subprocess.check_output(["git", "-C", str(model.package), *args], text=True)
    if git("rev-parse", "HEAD").strip() != model.revision:
        raise SystemExit(f"Unexpected {model.name} revision.")
    if git("status", "--porcelain=v1", "--untracked-files=all"):
        raise SystemExit(f"Unexpected {model.name} local changes.")


def main():
    for model in DEPENDENCIES:
        check_dependency(model)
    print("Pinned dependencies are clean.")


if __name__ == "__main__":
    main()

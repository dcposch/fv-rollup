#!/usr/bin/env python3
"""Install or check the pinned semantic model patches."""
import argparse
from pathlib import Path
import subprocess
from typing import NamedTuple

ROOT = Path(__file__).resolve().parent.parent


class ModelPatch(NamedTuple):
    name: str
    package: Path
    payload: Path
    revision: str
    files: tuple


PATCHES = (
    ModelPatch("EVMLean", ROOT / ".lake/packages/evmlean", ROOT / "patches/keccak",
               "9a4001c549041b0f3bc700ed66af5a5ef599c64a", (
                   "Ethereum/FFI/ffi.lean",
                   "Ethereum/LeanCrypto/Wheels.lean",
                   "Ethereum/LeanCrypto/Keccak256.lean",
               )),
    ModelPatch("EquiVM", ROOT / ".lake/packages/EquiVM", ROOT / "patches/abi-signatures",
               "4b9fddcb353c69e740f7adf3eec1d5338d7073e4", ("ABI/Signature.lean",)),
)


def git(model, *args, check=True):
    return subprocess.run(["git", "-C", str(model.package), *args], check=check,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def preflight(model, check_only):
    if not model.package.is_dir():
        raise SystemExit(f"Missing {model.name} dependency. Run lake update first.")
    if git(model, "rev-parse", "HEAD").stdout.decode().strip() != model.revision:
        raise SystemExit(f"Unexpected {model.name} revision.")

    status = git(model, "status", "--porcelain=v1", "-z", "--untracked-files=all").stdout
    for entry in status.split(b"\0"):
        if entry and (entry[:2] not in (b" M", b"??") or entry[3:].decode() not in model.files):
            raise SystemExit(f"Unexpected {model.name} change: {entry.decode()}")

    changes = []
    for relative in model.files:
        destination = model.package / relative
        expected = (model.payload / relative).read_bytes()
        actual = destination.read_bytes() if destination.exists() else None
        if actual == expected:
            continue
        original = git(model, "show", f"{model.revision}:{relative}", check=False)
        pristine = original.stdout if original.returncode == 0 else None
        if actual != pristine:
            raise SystemExit(f"Unexpected {model.name} file contents: {relative}")
        if check_only:
            raise SystemExit(f"{model.name} patch is not installed: {relative}")
        changes.append((destination, expected))
    return changes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check without writing files.")
    args = parser.parse_args()
    # Check every package before making any write.
    changes = []
    for model in PATCHES:
        changes.extend(preflight(model, args.check))
    for destination, expected in changes:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(expected)
    print("Pinned semantic model patches match.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Check the import rules for the three Lean layers."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
LAYERS = ("semantics", "invariants", "proofs")
ALLOWED = {
    "semantics": {"semantics"},
    "invariants": {"semantics", "invariants"},
    "proofs": set(LAYERS),
}


def imports(source):
    """Read imports. Ignore line comments and nested block comments."""
    clean = []
    depth = 0
    offset = 0
    while offset < len(source):
        pair = source[offset:offset + 2]
        if pair == "/-":
            depth += 1
            clean.append(" ")
            offset += 2
        elif depth and pair == "-/":
            depth -= 1
            offset += 2
        elif not depth and pair == "--":
            end = source.find("\n", offset)
            offset = len(source) if end < 0 else end
        else:
            if not depth or source[offset] == "\n":
                clean.append(source[offset])
            offset += 1
    for line in "".join(clean).splitlines():
        match = re.fullmatch(
            r"\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.\s]+)",
            line,
        )
        if match:
            yield from match[1].split()


def check_layers(root):
    modules = {
        ".".join(path.relative_to(root).with_suffix("").parts): path
        for layer in LAYERS for path in (root / layer).rglob("*.lean")
    }
    errors = []
    for module, path in sorted(modules.items()):
        layer = module.split(".")[0]
        for dependency in imports(path.read_text()):
            target = dependency.split(".")[0]
            if target not in LAYERS:
                continue
            if target not in ALLOWED[layer]:
                errors.append(f"{module}: forbidden import {dependency}")
            if dependency not in modules:
                errors.append(f"{module}: missing module {dependency}")
    return errors


if __name__ == "__main__":
    errors = check_layers(ROOT)
    if errors:
        raise SystemExit("\n".join(errors))
    print("Lean layer imports pass.")

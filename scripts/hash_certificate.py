#!/usr/bin/env python3
"""Generate a kernel-checked upstream Keccak certificate for one input block."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ROUND_CONSTANTS = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
)


def array(values):
    return "#[" + ", ".join(map(str, values)) + "]"


def vector(values):
    return f"(⟨{array(values)}, by decide⟩ : State)"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name")
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", default="Rollup.EVM.HashCertificates")
    parser.add_argument("--alias")
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--text")
    source.add_argument("--hex")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z][a-z0-9_]*", args.name):
        parser.error("Use a lowercase Lean identifier for the name.")
    for identifier in [args.namespace, args.alias]:
        if identifier is not None and not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", identifier):
            parser.error("Use a qualified Lean identifier for namespaces and aliases.")
    if args.output.exists():
        parser.error("The output file already exists.")
    if args.text is not None:
        if any(ord(c) < 32 or ord(c) > 126 for c in args.text):
            parser.error("Use printable ASCII text, or use --hex.")
        payload = args.text.encode("ascii")
        expression = json.dumps(args.text) + ".toByteArray"
    else:
        payload = bytes.fromhex(args.hex.removeprefix("0x"))
        expression = f"(⟨{array(payload)}⟩ : ByteArray)"
    if len(payload) >= 136:
        parser.error("The input must contain fewer than 136 bytes.")

    padded = bytearray(payload) + bytearray(136 - len(payload))
    padded[len(payload)] = 0x01
    padded[-1] |= 0x80
    initial = [int.from_bytes(padded[i:i + 8], "little") for i in range(0, 136, 8)] + [0] * 8
    program = f'''import Ethereum.SpongeHash.Keccak256
import Lean
open Ethereum.Keccak256
#eval show IO Unit from do
  let input : ByteArray := {expression}
  let mut state : State := {vector(initial)}
  let mut states := #[state.toArray.map UInt64.toNat]
  for rc in ({array(ROUND_CONSTANTS)} : Array UInt64) do
    state := round state rc
    states := states.push (state.toArray.map UInt64.toNat)
  IO.println (Lean.Json.arr #[Lean.toJson states,
    Lean.toJson ((Ethereum.Keccak256.hash input).toList.map UInt8.toNat)]).compress
'''
    with tempfile.TemporaryDirectory() as directory:
        temporary = Path(directory).resolve()
        path = temporary / "HashInput.lean"
        path.write_text(program)
        result = subprocess.run(
            ["lake", "env", "lean", f"--root={temporary}", str(path)], cwd=ROOT,
            text=True, stdout=subprocess.PIPE)
        if result.returncode:
            raise SystemExit(result.stdout)
        states, digest = json.loads(result.stdout)
    reference = subprocess.check_output(
        ["cast", "keccak", "0x" + payload.hex()], cwd=ROOT, text=True).strip()
    if bytes(digest).hex() != reference.removeprefix("0x"):
        raise SystemExit("The upstream Lean model and cast hashes differ.")

    name = args.name
    lines = ["import Ethereum.SpongeHash.Keccak256", "",
             "set_option maxRecDepth 100000", "set_option maxHeartbeats 10000000", "",
             "open Ethereum.Keccak256", f"namespace {args.namespace}", ""]
    for r, rc in enumerate(ROUND_CONSTANTS):
        lines += [f"private theorem {name}_round_{r} :",
                  f"    round {vector(states[r])} {rc} =",
                  f"      {vector(states[r + 1])} := by", "  decide +kernel", ""]
    nested = vector(states[0])
    for rc in ROUND_CONSTANTS:
        nested = f"round ({nested}) {rc}"
    lines += [f"private theorem {name}_permutation :",
              f"    permute {vector(states[0])} = {vector(states[-1])} := by",
              f"  change {nested} = _",
              "  rw [" + ", ".join(f"{name}_round_{r}" for r in range(24)) + "]", "",
              "attribute [local irreducible] permute", "",
              f"theorem {name} : Ethereum.KEC {expression} = ⟨{array(digest)}⟩ := by",
              "  unfold Ethereum.KEC Ethereum.Keccak256.hash",
              "  conv =>",
              "    lhs",
              "    arg 1",
              "    change permute _",
              "    arg 1",
              "    tactic =>",
              f"      exact (show _ = {vector(states[0])} from by decide +kernel)",
              f"  rw [{name}_permutation]",
              "  decide +kernel", "", f"end {args.namespace}", ""]
    if args.alias:
        lines += [f"theorem {args.alias} : Ethereum.KEC {expression} = ⟨{array(digest)}⟩ :=",
                  f"  {args.namespace}.{name}", ""]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines))
    print(f"Wrote {args.output}. Compile and audit it before use.")


if __name__ == "__main__":
    main()

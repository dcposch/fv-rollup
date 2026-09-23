#!/usr/bin/env python3
"""Generate a kernel-checked Keccak certificate for one input block."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def array(values):
    return "#[" + ", ".join(map(str, values)) + "]"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name")
    parser.add_argument("output", type=Path)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--text")
    source.add_argument("--hex")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z][a-z0-9_]*", args.name):
        parser.error("Use a lowercase Lean identifier for the name.")
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

    program = f'''import Ethereum.LeanCrypto.Keccak256
import Lean
open LeanCrypto.HashFunctions
#eval show IO Unit from do
  let input : ByteArray := {expression}
  let padded := byteArrayOfSHA3SR (paddingKeccak 136 input)
  let words := Absorb.toBlocks padded
  let initial := (Array.replicate 25 (0 : UInt64)).mapIdx fun z _ =>
    if z / 5 + 5 * (z % 5) < 17 then words[z / 5 + 5 * (z % 5)]! else 0
  let mut states : Array (Array UInt64) := #[initial]
  let mut state : Array UInt64 := initial
  for r in [:24] do
    state := keccak_round r state
    states := states.push state
  IO.println (Lean.Json.arr #[Lean.toJson (padded.toList.map UInt8.toNat),
    Lean.toJson (words.map UInt64.toNat),
    Lean.toJson (states.map (fun s => s.map UInt64.toNat)),
    Lean.toJson ((keccak256 input).toList.map UInt8.toNat)]).compress
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
        output = result.stdout
    padded, words, states, digest = json.loads(output)
    reference = subprocess.check_output(
        ["cast", "keccak", "0x" + payload.hex()], cwd=ROOT, text=True).strip()
    if bytes(digest).hex() != reference.removeprefix("0x"):
        raise SystemExit("The Lean model and cast hashes differ.")

    name = args.name
    lines = ["import Ethereum.FFI.ffi", "import proofs.HashComputation", "",
             "set_option maxRecDepth 100000", "set_option maxHeartbeats 10000000", "",
             "open LeanCrypto.HashFunctions", "namespace Rollup.EVM.HashCertificates", ""]
    lines += [f"private theorem {name}_padding :",
              f"    byteArrayOfSHA3SR (paddingKeccak 136 {expression}) = ⟨{array(padded)}⟩ := by",
              "  decide +kernel", "",
              f"private theorem {name}_blocks :",
              f"    Absorb.toBlocks (byteArrayOfSHA3SR (paddingKeccak 136 {expression})) =",
              f"      {array(words)} := by", f"  rw [{name}_padding]", "  keccak_cbv", ""]
    for r in range(24):
        lines += [f"private theorem {name}_round_{r} :",
                  f"    keccak_round {r} {array(states[r])} =", f"      {array(states[r + 1])} := by",
                  "  decide +kernel", ""]
    nested = array(states[0])
    for r in range(24):
        nested = f"keccak_round {r} ({nested})"
    lines += [f"private theorem {name}_permutation :",
              f"    keccakF {array(states[0])} = {array(states[-1])} := by",
              f"  change {nested} = _",
              "  rw [" + ", ".join(f"{name}_round_{r}" for r in range(24)) + "]", "",
              f"theorem {name} : ffi.KEC {expression} = ⟨{array(digest)}⟩ := by",
              "  unfold ffi.KEC",
              "  simp only [keccak256, hashFunction, Function.comp_apply, Absorb.absorb]",
              f"  rw [{name}_blocks, Absorb.absorbBlock]",
              f"  change squeeze' 1088 (by decide) 32 (Absorb.absorbBlock 1088 (by decide) (keccakF {array(states[0])}) #[]) = _",
              "  rw [Absorb.absorbBlock]",
              f"  change squeeze' 1088 (by decide) 32 (keccakF {array(states[0])}) = _",
              f"  rw [{name}_permutation]",
              "  simp only [squeeze', squeeze'.stateToBytes, Function.comp_apply, Absorb.unfoldrN]",
              "  decide +kernel", "", "end Rollup.EVM.HashCertificates", ""]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines))
    print(f"Wrote {args.output}. Compile and audit it before use.")


if __name__ == "__main__":
    main()

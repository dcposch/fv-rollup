#!/usr/bin/env python3
"""Compare patched ABI formatting with the pinned upstream printer."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
REVISION = "4b9fddcb353c69e740f7adf3eec1d5338d7073e4"

original = subprocess.check_output(
    ["git", "-C", str(ROOT / ".lake/packages/EquiVM"), "show",
     f"{REVISION}:ABI/Signature.lean"], text=True)
original = original.replace("import ABI.Types", "import ABI.Signature")
original = original.replace("namespace ABI", "namespace ABI.Upstream")
original = original.replace("end ABI", "end ABI.Upstream")
program = original + '''
open ABI
private def compareType (ty : ABIType) : IO Unit := do
  unless ABI.abiToSigStr ty == ABI.Upstream.abiToSigStr ty do
    throw (IO.userError "ABI type formatting differs")
  unless ABI.printSignature ⟨"check", [ty]⟩ ==
      ABI.Upstream.printSignature ⟨"check", [ty]⟩ do
    throw (IO.userError "ABI signature formatting differs")

#eval show IO Unit from do
  for width in [:257] do
    if h : 0 < width ∧ width ≤ 256 ∧ width % 8 = 0 then
      compareType (.elem (.int (.uint ⟨width, h⟩)))
      compareType (.elem (.int (.sint ⟨width, h⟩)))
      for decimals in [:82] do
        if hd : 0 < decimals ∧ decimals ≤ 80 then
          compareType (.elem (.fixed (.ufixed ⟨width, h⟩ ⟨decimals, hd⟩)))
        if hd : 0 < decimals ∧ decimals ≤ 81 then
          compareType (.elem (.fixed (.fixed ⟨width, h⟩ ⟨decimals, hd⟩)))
  for width in [:32] do
    if h : width < 32 then compareType (.elem (.bytes ⟨width, h⟩))
  for size in [0, 1, 9, 10, 31, 32, 255, 256, 1000, 2 ^ 64, 2 ^ 256] do
    compareType (.array (.elem .address) size)
    compareType (.tuple [.array (.dynamicArray (.elem .bool)) size, .string])
  IO.println "ABI printer comparison passed."
'''
with tempfile.TemporaryDirectory() as directory:
    temporary = Path(directory).resolve()
    path = temporary / "SignatureComparison.lean"
    path.write_text(program)
    subprocess.run(["lake", "env", "lean", f"--root={temporary}", str(path)],
                   cwd=ROOT, check=True)

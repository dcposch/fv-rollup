import proofs.RuntimeBytes
import Ethereum.Semantics

open Ethereum Ethereum.EVM

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The decoder selects self-destruct only for byte 0xff. -/
theorem parse_selfdestruct_byte (byte : UInt8) (parsed : parseInstr byte = some .SELFDESTRUCT) :
    byte = 0xff := by
  have table : ∀ b : Fin 256,
      parseInstr (UInt8.ofNat b.val) = some .SELFDESTRUCT → UInt8.ofNat b.val = 0xff := by
    decide +kernel
  have result : parseInstr byte = some .SELFDESTRUCT → byte = 0xff := by
    simpa only [UInt8.ofNat_toNat] using table ⟨byte.toNat, UInt8.toNat_lt byte⟩
  exact result parsed

/-- At every program counter, runtime decoding excludes self-destruct. -/
theorem runtime_no_selfdestruct (pc : UInt256) :
    ((decode runtimeBytecode pc).getD (.STOP, none)).1 ≠ .SELFDESTRUCT := by
  have bytes : ∀ index (bounded : index < runtimeBytecode.data.size),
      runtimeBytecode.data[index] ≠ 0xff := by
    intro index bounded
    have checked := (Array.all_iff_forall.mp runtime_no_selfdestruct_byte)
      index bounded ⟨Nat.zero_le _, bounded⟩
    simpa using checked
  unfold decode ByteArray.get?
  split
  · rename_i bounded
    simp only [bind, Option.bind, Option.getD]
    cases parsed : parseInstr (runtimeBytecode.get pc.toNat bounded) with
    | none => simp
    | some operation =>
      simp only
      intro same
      subst operation
      exact bytes pc.toNat bounded (parse_selfdestruct_byte _ parsed)
  · simp

end Rollup.EVM

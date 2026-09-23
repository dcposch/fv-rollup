import semantics.ChildCreation
import proofs.RuntimeBytes
import proofs.CreationSite
import proofs.CallbackPrefix

open Ethereum Ethereum.EVM

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The pinned runtime contains neither creation opcode byte. -/
theorem runtime_no_creation_byte :
    runtimeBytecode.data.all (fun byte => byte != 0xf0 && byte != 0xf5) = true := by
  decide +kernel

/-- Creation decoding requires byte 0xf0 or 0xf5. -/
theorem parse_creation_byte (byte : UInt8) (op : Operation)
    (parsed : parseInstr byte = some op) (kind : op = .CREATE ∨ op = .CREATE2) :
    byte = 0xf0 ∨ byte = 0xf5 := by
  have table : ∀ b : Fin 256,
      (parseInstr (UInt8.ofNat b.val) = some .CREATE ∨
        parseInstr (UInt8.ofNat b.val) = some .CREATE2) →
      UInt8.ofNat b.val = 0xf0 ∨ UInt8.ofNat b.val = 0xf5 := by
    decide +kernel
  have result : (parseInstr byte = some .CREATE ∨ parseInstr byte = some .CREATE2) →
      byte = 0xf0 ∨ byte = 0xf5 := by
    simpa only [UInt8.ofNat_toNat] using table ⟨byte.toNat, UInt8.toNat_lt byte⟩
  apply result
  rcases kind with rfl | rfl
  · exact .inl parsed
  · exact .inr parsed

/-- No runtime program counter decodes to a creation instruction. -/
theorem runtime_no_creation (pc : UInt256) :
    ((decode runtimeBytecode pc).getD (.STOP, none)).1 ≠ .CREATE ∧
      ((decode runtimeBytecode pc).getD (.STOP, none)).1 ≠ .CREATE2 := by
  have bytes : ∀ index (bounded : index < runtimeBytecode.data.size),
      runtimeBytecode.data[index] ≠ 0xf0 ∧ runtimeBytecode.data[index] ≠ 0xf5 := by
    intro index bounded
    have checked := (Array.all_iff_forall.mp runtime_no_creation_byte)
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
      constructor <;> intro same
      all_goals
        have kind : operation = .CREATE ∨ operation = .CREATE2 := by simp [same]
        rcases parse_creation_byte _ operation parsed kind with first | second
        · exact (bytes pc.toNat bounded).1 first
        · exact (bytes pc.toNat bounded).2 second
  · simp

/-- Executing the pinned runtime cannot enter contract initialization. -/
theorem runtime_no_creation_child {before child : Ethereum.State} {jumps : Array UInt256}
    (code : before.executionEnv.code = runtimeBytecode)
    (entered : ChildCreationEntry jumps before child) : False := by
  cases entered with
  | @entered op arg checked cost site instruction precheck arguments bounded allowed =>
    have excluded := runtime_no_creation before.machineState.pc
    rw [← code, instruction] at excluded
    rcases creation_opcode_kind arguments with first | second
    · exact excluded.1 first
    · exact excluded.2 second

/-- A runtime prefix cannot descend into a creation frame. -/
theorem runtime_prefix_no_creation {start before child : Ethereum.State} {jumps : Array UInt256}
    (code : start.executionEnv.code = runtimeBytecode)
    (trace : ContinuingPrefix jumps start before)
    (entered : ChildCreationEntry jumps before child) : False := by
  apply runtime_no_creation_child (entered := entered)
  rw [continuing_prefix_environment trace]
  exact code

end Rollup.EVM

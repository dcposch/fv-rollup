import Reasoning.Initcode

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Check instruction boundaries through one jump destination. -/
def jumpScan (code : ByteArray) (target : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, pc =>
    match code.get? pc >>= parseInstr with
    | none => false
    | some op => if pc = target then decide (op = .JUMPDEST)
      else jumpScan code target fuel (N pc op)

theorem jumpScan_mem (code : ByteArray) (target fuel pc : Nat)
    (acc : Array UInt256) (checked : jumpScan code target fuel pc = true) :
    UInt256.ofNat target ∈ D_J_aux code pc acc := by
  induction fuel generalizing pc acc with
  | zero => simp [jumpScan] at checked
  | succ fuel ih =>
    simp only [jumpScan] at checked
    cases parsed : code.get? pc >>= parseInstr with
    | none => simp [parsed] at checked
    | some op =>
      simp only [parsed] at checked
      rw [D_J_aux_eq_some code pc acc op parsed]
      by_cases atTarget : pc = target
      · subst pc
        simp at checked
        subst op
        rw [D_J_aux_acc]
        simp
      · rw [if_neg atTarget] at checked
        exact ih _ _ checked

/-- A checked scan proves membership in the EVM jump table. -/
theorem jumpScan_valid (code : ByteArray) (target fuel : Nat)
    (checked : jumpScan code target fuel 0 = true) :
    (D_J code 0).contains (UInt256.ofNat target) = true := by
  rw [Array.contains_iff_mem]
  exact jumpScan_mem code target fuel 0 #[] checked

end Rollup.EVM

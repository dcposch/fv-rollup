import proofs.PrefixReach
import proofs.StaticStore

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- A storage write before the known child requires write permission. -/
theorem PCR.sstore_permission {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (reached : PCR code ee target child pc stack mem aw rdata acc)
    (decoded : decode code pc = some (.SSTORE, none)) : ee.perm = true := by
  by_contra denied
  have readonly : ee.perm = false := Bool.eq_false_iff.mpr denied
  apply prefix_cursor_stopped (op := .SSTORE) (arg := none) reached.2
    (by simp only [reached.1, decoded, Option.getD_some]) (by decide)
  intro before after matched run
  have actual : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) =
      (.SSTORE, none) := by
    simp only [matched.1, matched.2.1, reached.1, decoded, Option.getD_some]
  obtain ⟨checked, cost, _, precheck, _⟩ := instruction_state_step actual run
  exact static_sstore_precheck before _ (by rw [matched.1]; exact readonly) (checked, cost) precheck

end Rollup.EVM

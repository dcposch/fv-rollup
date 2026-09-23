import semantics.Boundary
import semantics.CreationCall
import Ethereum.Theory.GasLemmas

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A selected message returns no more gas than it receives. -/
theorem selected_message_gas_bound (call : MessageCall) :
    call.selectedRun.2.2.1.toNat ≤ call.gas.toNat := by
  exact Theta_gas_le

/-- Initialization errors, reverts, and code installation cannot increase returned gas. -/
theorem creation_gas_bound (call : CreationCall) :
    call.run.2.2.2.1.toNat ≤ call.gas.toNat := by
  unfold CreationCall.run Lambda
  simp only
  split
  · simp
  · rename_i execution
    have bound := Xi_gas_le execution
    simpa only [XiResultGas] using bound
  · rename_i created accounts gas substate output execution
    have bound := Xi_gas_le execution
    change gas.toNat ≤ call.gas.toNat at bound
    refine Nat.le_trans (Nat.mod_le _ _) ?_
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.le_trans (Nat.sub_le _ _) bound

/-- The one-fifth refund cap keeps total returned gas within the transaction gas limit. -/
theorem refund_gas_bound (limit remaining refund : Nat) (bounded : remaining ≤ limit) :
    remaining + min ((limit - remaining) / 5) refund ≤ limit := by
  omega

end Rollup.EVM

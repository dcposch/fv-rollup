import proofs.DepositLocked
import proofs.BatchEntry
import proofs.WithdrawalEntry
import proofs.RuntimeGetters
import proofs.RuntimeUnknownSelector

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- A successful call while locked is a getter and preserves every account. -/
theorem locked_runtime_xi_preserves_accounts {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (locked : solcSlotWord σ I ⟨6⟩ ≠ ⟨0⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ cA' = cA ∧ σ' = σ := by
  have notRejected (rejected : RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I)) : False := by
    rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  apply getter_xi_preserves_accounts code bounded ?_ success
  have known := runtime_success_selector code bounded success
  simp only [runtimeSelectors, List.mem_cons, List.not_mem_nil, or_false] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases known with seq | batch | root | number | withdrawal | backing | pending | deposit | claims
  · exact Or.inl seq
  · exact False.elim (notRejected (batch_locked_reject code bounded batch locked))
  · exact Or.inr (Or.inl root)
  · exact Or.inr (Or.inr (Or.inl number))
  · exact False.elim (notRejected (withdrawal_locked_reject code bounded withdrawal locked))
  · exact Or.inr (Or.inr (Or.inr (Or.inl backing)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl pending))))
  · exact False.elim (notRejected (deposit_locked_reject code bounded deposit locked))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr claims))))

end Rollup.EVM

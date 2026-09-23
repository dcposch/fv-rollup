import proofs.support.AccountSurvival
import proofs.CallEntry
import proofs.CreationCall
import proofs.WorldNonce
import proofs.AddressOrder

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A code-preserving account update keeps the lifecycle conditions. -/
theorem account_survives_code_frame {self : Address} {before after : AccountMap} {created substate}
    (initial : AccountSurvives self before created substate)
    (frame : accountCodeStateEq before after) : AccountSurvives self after created substate :=
  ⟨(frame self).symm.trans (AccountSurvives.pinned initial), (AccountSurvives.notCreated initial), (AccountSurvives.notDeleted initial)⟩

/-- A message entry preserves an existing account under any selected code. -/
theorem message_entry_survives (call : MessageCall) (code : ByteArray) {self : Address}
    (initial : AccountSurvives self call.accounts call.created call.substate) :
    StateSurvives self (call.codeEntry code) := by
  apply account_survives_code_frame initial
  exact sendEth_accountCodeStateEq call.receiver call.sender call.value true call.accounts

/-- A creation collision cannot add the rollup to the created-account set. -/
theorem creation_initial_set_excludes (call : CreationCall) {self : Address}
    (pinned : (call.accounts.findD self default).code = runtimeBytecode)
    (absent : self ∉ call.created) : self ∉ call.initialCreated := by
  unfold CreationCall.initialCreated
  cases collision : call.collision with
  | true => simpa only [if_true] using absent
  | false =>
    simp only [Bool.false_eq_true, if_false]
    have different := creation_fresh_foreign call pinned collision
    intro member
    rcases (Batteries.RBSet.mem_insert (t := call.created)).mp member with old | same
    · exact absent old
    · exact accountAddress_compare_ne_eq_of_ne different.symm same

/-- Creation transfer and collision checks preserve existing account code and lifecycle sets. -/
theorem creation_entry_survives (call : CreationCall) {self : Address}
    (initial : AccountSurvives self call.accounts call.created call.substate) :
    StateSurvives self call.entryState := by
  refine ⟨?_, creation_initial_set_excludes call (AccountSurvives.pinned initial) (AccountSurvives.notCreated initial), ?_⟩
  · have code := (sendEthCreate_static_state call.address call.sender call.value true call.accounts self).2.2
    exact code.symm.trans (AccountSurvives.pinned initial)
  · change self ∉ call.substate.selfDestructSet
    exact AccountSurvives.notDeleted initial

/-- The creator nonce update preserves the account survival conditions. -/
theorem nonce_survives {self sender : Address} {accounts : AccountMap} {created substate}
    (initial : AccountSurvives self accounts created substate) :
    AccountSurvives self (incrementNonce accounts sender) created substate := by
  refine ⟨?_, (AccountSurvives.notCreated initial), (AccountSurvives.notDeleted initial)⟩
  exact (incrementNonce_storage accounts sender self).2.2.symm.trans (AccountSurvives.pinned initial)

end Rollup.EVM

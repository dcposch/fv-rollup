import proofs.PaymentControl
import proofs.WithdrawalPrefixChecks
import proofs.WithdrawalPrefixPayment
import proofs.support.PaymentPrefix

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- An actual code call from the runtime has passed every withdrawal check. -/
theorem root_call_prefix_bound : RootCallPrefixBound := by
  intro created genesis blocks accounts original substate environment gas cursor child code bounded start trace entered
  have position := runtime_call_prefix_position
    (start := start) code rfl rfl trace entered
  have initial := PCR.initState code trace entered
  obtain ⟨entry, selector, dispatched⟩ := runtime_prefix_dispatch initial
  have withdrawal : entry = .withdrawal := by
    by_contra different
    obtain ⟨bytes, state, matched, remaining, _⟩ := dispatched
    have excluded := nonwithdraw_prefix_excludes_call entry different (runtimeEntrySelector entry)
      ((congrArg ExecutionEnv.code matched.1).trans bytes) matched.2.1 matched.2.2.1 remaining
    exact excluded position
  subst entry
  obtain ⟨checks, checked⟩ := withdrawal_prefix_checks (runtime_prefix_four initial) bounded dispatched
  have memorySize := twoWordHashMem_size_96 (calldataWord environment.calldata 4) ⟨5⟩ solcFreePtrMem_size
  have freePointer := twoWordHashMem_read64 (calldataWord environment.calldata 4) ⟨5⟩
    solcFreePtrMem_size solcFreePtrMem_read64
  obtain ⟨gasArg, setup⟩ := withdrawal_prefix_payment_setup
    (withdrawalClaimWord (sstoreAccountMap environment.codeOwner accounts ⟨6⟩ ⟨1⟩) environment)
    [⟨226⟩, ⟨0xbb3ef682⟩] (by decide) checks.canonical memorySize freePointer checked
  have matched := payment_prefix_target position setup
  refine ⟨checks, selector, ?_, matched.1, matched.2.1, gasArg, matched.2.2.1⟩
  exact congrArg Prod.snd matched.2.2.2.2.2.2

end Rollup.EVM

import proofs.FreshPaymentPrefix

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Actual runtime payment prefixes preserve custody throughout the active receiver tree. -/
theorem root_payment_prefix_safe {root cursor child current : Ethereum.State} {keys}
    (fresh : FreshFrame root) (bounded : root.executionEnv.calldata.size < UInt256.size)
    (code : OwnCode root) (world : WorldBounded root)
    (ready : StorageReady root root.executionEnv.codeOwner keys)
    (safe : Safe (project root root.executionEnv.codeOwner keys)) (covered : CalldataCovered root keys)
    (earlier : ContinuingPrefix (D_J runtimeBytecode 0) root cursor)
    (entered : ChildCallEntry (D_J runtimeBytecode 0) cursor child) (active : ActivePrefix child current) :
    ∃ owner : Address,
      UInt256.ofNat owner.val = calldataWord root.executionEnv.calldata 4 ∧
      Safe (inFlightProjection current root.executionEnv.codeOwner keys
        ⟨owner, (calldataWord root.executionEnv.calldata 36).toNat,
          (project root root.executionEnv.codeOwner keys).eth⟩) :=
  withdrawal_cursor_active_safe root cursor child current keys _ code world ready safe covered
    (fresh_root_payment_bound fresh code.1 bounded earlier entered) entered active

end Rollup.EVM

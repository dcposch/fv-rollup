import proofs.support.PaymentControl
import proofs.BlockedControlFrame
import proofs.PrefixReach

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The payment control row occurs in the checked runtime table. -/
theorem payment_control_member : paymentControlCursor ∈ controlPaths := by
  decide +kernel

/-- The exact payment stack satisfies the checked control row. -/
theorem payment_control_ready {state : Ethereum.State}
    {gas owner amount credit : UInt256}
    (code : state.executionEnv.code = runtimeBytecode) (counter : state.machineState.pc = ⟨935⟩)
    (stack : state.machineState.stack =
      [gas, owner, amount, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, amount, owner, ⟨0⟩,
        credit, amount, owner, ⟨226⟩, ⟨0xbb3ef682⟩]) : ControlFrameReady state := by
  refine ⟨code, paymentControlCursor, payment_control_member, counter, ?_⟩
  rw [stack]
  simp [paymentControlCursor, AbstractStackDenotes, AbstractWord.denotes]

/-- A represented payment cursor on a prefix to byte 935 is the target itself. -/
theorem payment_prefix_target {I : ExecutionEnv} {target child : Ethereum.State}
    {gas owner amount credit : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (position : target.machineState.pc = ⟨935⟩)
    (reached : PCR runtimeBytecode I target child ⟨935⟩
      [gas, owner, amount, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, amount, owner, ⟨0⟩,
        credit, amount, owner, ⟨226⟩, ⟨0xbb3ef682⟩] mem aw rdata acc) :
    CursorMatches I
      ⟨⟨935⟩, [gas, owner, amount, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, amount, owner, ⟨0⟩,
        credit, amount, owner, ⟨226⟩, ⟨0xbb3ef682⟩], mem, aw, rdata, acc⟩ target := by
  obtain ⟨code, before, matched, trace, _⟩ := reached
  have ready := payment_control_ready ((congrArg ExecutionEnv.code matched.1).trans code)
    matched.2.1 matched.2.2.1
  rcases continuing_prefix_head trace with same | ⟨after, run, rest⟩
  · exact same ▸ matched
  · exact False.elim (runtime_call_not_repeated ready matched.2.1 run rest position)

end Rollup.EVM

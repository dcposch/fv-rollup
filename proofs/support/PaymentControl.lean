import proofs.support.ControlFrame

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The control row for the runtime's payment CALL. -/
def paymentControlCursor : AbstractCursor :=
  ⟨⟨935⟩, [.any, .any, .any, .any, .any, .any, .exact ⟨0⟩,
    .any, .any, .any, .exact ⟨0⟩, .any, .any, .any, .exact ⟨226⟩, .any]⟩

end Rollup.EVM

import semantics.Deployment

open Ethereum Ethereum.EVM

namespace Rollup.EVM

noncomputable def deploymentCode (sequencer : Address) (root : Root) : ByteArray :=
  creationBytecode ++ ((UInt256.ofNat sequencer.val).toByteArray ++ (⟨root⟩ : UInt256).toByteArray)

end Rollup.EVM

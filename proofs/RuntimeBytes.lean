import semantics.Bytecode

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- No byte of the pinned runtime is the self-destruct opcode. -/
theorem runtime_no_selfdestruct_byte : runtimeBytecode.data.all (fun byte => byte != 0xff) = true := by
  decide +kernel

end Rollup.EVM

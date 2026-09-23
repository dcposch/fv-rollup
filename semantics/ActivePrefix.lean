import semantics.ChildCall
import semantics.ChildCreation

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Observe a frame or descend into a call or creation that is still executing. -/
inductive ActivePrefix : Ethereum.State → Ethereum.State → Prop where
  | within {start current} : InstructionPrefix (D_J start.executionEnv.code 0) start current →
      ActivePrefix start current
  | call {start before child current} :
      ContinuingPrefix (D_J start.executionEnv.code 0) start before →
      ChildCallEntry (D_J start.executionEnv.code 0) before child →
      ActivePrefix child current → ActivePrefix start current
  | creation {start before child current} :
      ContinuingPrefix (D_J start.executionEnv.code 0) start before →
      ChildCreationEntry (D_J start.executionEnv.code 0) before child →
      ActivePrefix child current → ActivePrefix start current

end Rollup.EVM

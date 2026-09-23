import semantics.PrefixCoverage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Follow actual foreign frames to an invocation of the pinned rollup code. -/
inductive RootEntryPath (self : Address) (root : Ethereum.State) : Ethereum.State → Prop where
  | here : root.executionEnv.codeOwner = self → root.executionEnv.code = runtimeBytecode →
      RootEntryPath self root root
  | call {start before child} : self ≠ start.executionEnv.codeOwner →
      ContinuingPrefix (D_J start.executionEnv.code 0) start before →
      ChildCallEntry (D_J start.executionEnv.code 0) before child →
      RootEntryPath self root child → RootEntryPath self root start
  | creation {start before child} : self ≠ start.executionEnv.codeOwner →
      ContinuingPrefix (D_J start.executionEnv.code 0) start before →
      ChildCreationEntry (D_J start.executionEnv.code 0) before child →
      RootEntryPath self root child → RootEntryPath self root start

/-- Cover the actual child records on the path and the root invocation's calldata. -/
inductive CoveredRootEntryPath (self : Address) (keys : AccessScope) (root : Ethereum.State) :
    Ethereum.State → Prop where
  | here : root.executionEnv.codeOwner = self → root.executionEnv.code = runtimeBytecode →
      CalldataCovered root keys → CoveredRootEntryPath self keys root root
  | call {start before child} : self ≠ start.executionEnv.codeOwner →
      CoveredPrefix self keys (D_J start.executionEnv.code 0) start before →
      ChildCallEntry (D_J start.executionEnv.code 0) before child →
      CoveredRootEntryPath self keys root child → CoveredRootEntryPath self keys root start
  | creation {start before child} : self ≠ start.executionEnv.codeOwner →
      CoveredPrefix self keys (D_J start.executionEnv.code 0) start before →
      ChildCreationEntry (D_J start.executionEnv.code 0) before child →
      CoveredRootEntryPath self keys root child → CoveredRootEntryPath self keys root start

end Rollup.EVM

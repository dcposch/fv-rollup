import Ethereum.Theory.AccountLocality

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The account keeps its code and both storage maps. -/
def CodeStorageFrame (self : AccountAddress) (before after : AccountMap) : Prop :=
  (before.findD self default).storage = (after.findD self default).storage ∧
  (before.findD self default).tstorage = (after.findD self default).tstorage ∧
  (before.findD self default).code = (after.findD self default).code

end Rollup.EVM

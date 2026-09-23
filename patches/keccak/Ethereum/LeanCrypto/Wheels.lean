/-
Adapted from NethermindEth/LeanCrypto, commit
cc4937cdcab1229fa375964fbcfae82b95576ed8. Apache-2.0.
See patches/keccak/LICENSE and README.md.
-/
namespace LeanCrypto

def rotateL (a : UInt64) (n : Nat) : UInt64 :=
  UInt64.ofNat (BitVec.ofNat 64 a.toNat |>.rotateLeft n).toNat

def complement (a : UInt64) : UInt64 :=
  UInt64.ofNat (Complement.complement <| BitVec.ofNat 64 a.toNat).toNat

end LeanCrypto

section Array

variable {α : Type}

namespace Array

section

variable [Inhabited α]

def foldl1 (f : α → α → α) (as : Array α) : α :=
  Array.foldl f (as[0]?.getD default) (as.drop 1)

def backpermute : Array α → Array Nat → Array α :=
  λ xs ↦ Array.map (xs[·]?.getD default)

def splitAt (n : Nat) (l : Array α) : Array α × Array α :=
  (l.extract 0 n, l.extract n l.size)

@[simp]
theorem size_snd_splitAt {α} {n : Nat} {l : Array α} :
  (splitAt n l).snd.size = l.size - n := by simp [splitAt]

end

end Array

end Array

section ByteArray

namespace ByteArray

def keccakExtract (a : ByteArray) (b e : Nat) : ByteArray :=
  if b < 2^64 && e < 2^64
  then a.extract b e -- NB only when `b` and `e` are sufficiently small
  else ⟨⟨a.toList.drop b |>.take (e - b)⟩⟩

end ByteArray

end ByteArray

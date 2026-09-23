/-
Adapted from NethermindEth/LeanCrypto, commit
cc4937cdcab1229fa375964fbcfae82b95576ed8. Apache-2.0.
See patches/keccak/LICENSE and README.md.
-/
import Ethereum.LeanCrypto.Wheels
import Init.Data.Rat.Basic

set_option maxRecDepth 10000

namespace LeanCrypto

namespace HashFunctions

abbrev SHA3SR : Type := Array UInt64

def Rounds : Nat := 24

def NumLanes : Nat := 25

def LaneWidth : Nat := 64

def RoundConstants : Array UInt64 :=
  #[ 0x0000000000000001, 0x0000000000008082, 0x800000000000808A
   , 0x8000000080008000, 0x000000000000808B, 0x0000000080000001
   , 0x8000000080008081, 0x8000000000008009, 0x000000000000008A
   , 0x0000000000000088, 0x0000000080008009, 0x000000008000000A
   , 0x000000008000808B, 0x800000000000008B, 0x8000000000008089
   , 0x8000000000008003, 0x8000000000008002, 0x8000000000000080
   , 0x000000000000800A, 0x800000008000000A, 0x8000000080008081
   , 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

def rotationConstants : Array Nat :=
  #[  0, 36,  3, 41, 18
   ,  1, 44, 10, 45,  2
   , 62,  6, 43, 15, 61
   , 28, 55, 25, 21, 56
   , 27, 20, 39,  8, 14 ]

def piConstants : Array Nat :=
  #[ 0, 15, 5, 20, 10
   , 6, 21, 11, 1, 16
   , 12, 2, 17, 7, 22
   , 18, 8, 23, 13, 3
   , 24, 14, 4, 19, 9 ]

def θ (state : SHA3SR) : SHA3SR :=
  let indexed := Array.zip (Array.range 25) d
  indexed.flatMap λ (i, e) ↦ Array.map (· ^^^ e) (state.extract (i * 5) (i * 5 + 5))
  where c : SHA3SR := Array.range 5 |>.map λ i ↦ (state.extract (i * 5) (i * 5 + 5)).foldl1 (·^^^·)
        d : SHA3SR := Array.range 5 |>.map λ i ↦ c[(Int.ofNat i - 1) % 5 |>.toNat]! ^^^
                                                 rotateL (c[(Int.ofNat i + 1) % 5 |>.toNat]!) 1

def ρ (state : SHA3SR) : SHA3SR := Array.zipWith (flip rotateL) rotationConstants state

def Array.backpermute {α} [Inhabited α] : Array α → Array Nat → Array α := λ xs ↦ Array.map (xs[·]!)

def π (state : SHA3SR) : SHA3SR := state.backpermute piConstants

def χ (b : SHA3SR) : SHA3SR := Array.mapIdx subChi b
  where subChi z el := el ^^^ (complement (b[(z + 5) % 25]!) &&& (b[(z + 10) % 25]!))

def ι (roundNumber : Nat) (state : SHA3SR) : SHA3SR :=
  state.setIfInBounds 0 (RoundConstants[roundNumber]! ^^^ (state[0]!))

def keccak_round (r : Nat) : SHA3SR → SHA3SR := ι r ∘ χ ∘ π ∘ ρ ∘ θ

def keccakF'' (s : SHA3SR) : SHA3SR :=
  let f : Nat × SHA3SR → Nat × SHA3SR := λ (r, s) => (.succ r, keccak_round r $ s)
  (List.foldl Function.comp id (List.replicate 24 f) (0, s)).2

set_option diagnostics true in
def keccakF (state : SHA3SR) : SHA3SR :=
  ((Array.mk (List.replicate Rounds f)).foldl1 (·∘·) (0, state)).2
  where f : Nat × SHA3SR → Nat × SHA3SR := λ (r, s) ↦ (r.succ, ι r ∘ χ ∘ π ∘ ρ <| θ s)

namespace Absorb

variable {α β : Type}

def unfoldr {α β : Type} [sz : SizeOf β]
            (f : (b : β) → Option (α × {b' : β // sizeOf b' < sizeOf b})) (b : β) : Array α :=
  match f b with
  | .none => #[]
  | .some (a, ⟨b', _⟩) => ⟨a :: (unfoldr f b').toList⟩

def unfoldrN {α β} (m : Nat) (f : β → Option (α × β)) (b0 : β) : Array α :=
  let build g := g List.cons []
  let res : List α :=
    build λ c n ↦
      let rec go b i := if i = 0 then n else
                        match f b with
                          | .some (a, new_b) => c a <| go new_b (i - 1)
                          | .none            => n
      go b0 m
  res.toArray

def ifoldl {α β : Type} (f : α → Nat → β → α) (init : α) (as : Array β) : α :=
  Array.range as.size |>.zip as |>.foldl (λ acc (i, elem) ↦ f acc i elem) init

def toBlocks : ByteArray → Array UInt64 :=
  unfoldr (sz := ⟨ByteArray.size⟩) toLane
    where toLane (input : ByteArray) :=
            if eq₁ : input.isEmpty then .none
            else match eq₂ : input.data.splitAt 8 with
                 | (h, t) =>
                 .some (ifoldl createWord64 0 h, ⟨⟨t⟩, by
                   change t.size < input.data.size
                   have ht : t = (input.data.splitAt 8).snd := by rw [eq₂]
                   rw [ht, Array.size_snd_splitAt]
                   have nonempty : input.data.size ≠ 0 := by
                     intro empty
                     apply eq₁
                     simp [ByteArray.isEmpty, ByteArray.size, empty]
                   omega⟩)
          createWord64 acc offset octet := acc ^^^ (octet.toUInt64 <<< (UInt64.ofNat offset * 8))

def absorbBlock (rate : Nat) (h : rate / 64 ≠ 0) (state : Array UInt64) (input : Array UInt64) : Array UInt64 :=
  if eq : input.size = 0 then state
  else have : input.size - rate / 64 < input.size := by
         omega
       absorbBlock rate h (keccakF state') (input.drop (rate / 64))
  termination_by input.size
  where state' : SHA3SR := Array.mapIdx (λ z el ↦ if z / 5 + 5 * (z % 5) < rate / 64
                                                  then el ^^^ (input[z / 5 + 5 * (z % 5)]!)
                                                  else el) state

def absorb (rate : Nat) (h : rate / 64 ≠ 0) (ba : ByteArray) : Array UInt64 :=
  absorbBlock rate h ⟨List.replicate 25 0⟩ ∘ toBlocks <| ba

end Absorb

def multiratePadding (bitrateBytes : Nat) (padByte : UInt8) (input : ByteArray) : ByteArray :=
  ByteArray.mk <| Array.range totalLength |>.map λ i ↦ process i
  where msglen := input.size
        padlen := bitrateBytes - (msglen % bitrateBytes)
        totalLength := padlen + msglen
        process x := if x < msglen then input[x]! else
                     if x == (totalLength - 1) && padlen == 1 then 0x80 ||| padByte else
                     if x == (totalLength - 1) then 0x80 else
                     if x == msglen then padByte
                     else 0x00

def byteArrayOfSHA3SR (arr : SHA3SR) : ByteArray :=
  arr.foldl (init := ByteArray.empty)
    λ acc word ↦
      acc.push (word >>> UInt64.ofNat 56).toUInt8
       |>.push (word >>> UInt64.ofNat 48).toUInt8
       |>.push (word >>> UInt64.ofNat 40).toUInt8
       |>.push (word >>> UInt64.ofNat 32).toUInt8
       |>.push (word >>> UInt64.ofNat 24).toUInt8
       |>.push (word >>> UInt64.ofNat 16).toUInt8
       |>.push (word >>> UInt64.ofNat 8).toUInt8
       |>.push (word >>> UInt64.ofNat 0).toUInt8

def SHA3SRofByteArray (arr : ByteArray) : SHA3SR :=
  let arr : ByteArray := ⟨Array.replicate ((8 - arr.size % 8) % 8) 0⟩ ++ arr
  (·.1) <| arr.foldl (init := (#[], 0, 7))
    λ (res, word, i) byte ↦
      let byteVal : UInt64 := (2^(8 * i)).toUInt64 * byte.toUInt64
      if i == 0
      then (res.push (word + byteVal), 0, 7)
      else (res, word + byteVal, i - 1)

def paddingKeccak (bitrateBytes : Nat) : ByteArray → SHA3SR :=
  SHA3SRofByteArray ∘ multiratePadding bitrateBytes 0x01

def squeeze' (rate : Nat) (h : rate / 64 ≠ 0) (l : Nat) (state : SHA3SR) : ByteArray :=
  ByteArray.keccakExtract (b := 0) (e := l) ∘ toLittleEndian <| stateToBytes state
  where lanesToExtract := Int.toNat ∘ Rat.ceil <| l / (64 / 8)
        extract (xXs : Nat × Array UInt64) :=
          if eq : xXs.1 < rate / 64
          then Option.some (xXs.2[xXs.1 / 5 + xXs.1 % 5 * 5]!, (xXs.1.succ, xXs.2))
          else have : 0 < xXs.fst := by omega
               extract (0, keccakF xXs.2)
        termination_by xXs.1
        stateToBytes (s : Array UInt64) : Array UInt64 := Absorb.unfoldrN lanesToExtract extract (0, s)
        toLittleEndian (arr : Array UInt64) : ByteArray :=
          arr.foldl (init := ByteArray.empty) λ acc elem ↦
            let res :=
            acc.push (elem >>> UInt64.ofNat 0).toUInt8
             |>.push (elem >>> UInt64.ofNat 8).toUInt8
             |>.push (elem >>> UInt64.ofNat 16).toUInt8
             |>.push (elem >>> UInt64.ofNat 24).toUInt8
             |>.push (elem >>> UInt64.ofNat 32).toUInt8
             |>.push (elem >>> UInt64.ofNat 40).toUInt8
             |>.push (elem >>> UInt64.ofNat 48).toUInt8
             |>.push (elem >>> UInt64.ofNat 56).toUInt8
            res

open Absorb

def hashFunction (paddingFunction : Nat → ByteArray → SHA3SR) (rate : Nat) (h : rate / 64 ≠ 0) (inp : ByteArray) : ByteArray :=
  squeeze' rate h outputBytes ∘ Absorb.absorb rate h ∘ byteArrayOfSHA3SR ∘ paddingFunction (rate / 8) $ inp
  where outputBytes := (1600 - rate) / 16

def keccak256 (data : ByteArray) : ByteArray :=
  hashFunction paddingKeccak 1088 (by decide) data

end HashFunctions

end LeanCrypto

import proofs.CreationBody

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

noncomputable def creationArgs (sequencer root : UInt256) : ByteArray :=
  sequencer.toByteArray ++ root.toByteArray

theorem creationArgs_size (sequencer root : UInt256) :
    (creationArgs sequencer root).size = 64 := by
  simp only [creationArgs, ByteArray.size_append, toByteArray_size]

/-- Copy an in-bounds source window after a gap in memory. -/
theorem write_from_gap (src mem : ByteArray) (source offset len : Nat)
    (positive : len ≠ 0) (bounds : source + len ≤ src.size) (afterMem : mem.size ≤ offset) :
    src.write source mem offset len =
      mem ++ ByteArray.zeroes (offset - mem.size) ++ src.extract source (source + len) := by
  have padded : (mem.data ++ (ByteArray.zeroes (offset - mem.size)).data).size = offset := by
    rw [Array.size_append, show (ByteArray.zeroes (offset - mem.size)).data.size =
      (ByteArray.zeroes (offset - mem.size)).size from rfl, ByteArray_zeroes_size]
    change mem.size + (offset - mem.size) = offset
    omega
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg positive, if_neg (show ¬ source ≥ src.size from by omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract]
  have srcSize : src.data.size = src.size := rfl
  rw [show min len (src.size - source) = len from by omega,
    show min mem.size (offset + len) - (offset + len) = 0 from by omega,
    show (ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
      rw [zeroes_zero (n := 0) rfl]; rfl,
    Array.append_empty]
  have tail : (mem.data ++ (ByteArray.zeroes (offset - mem.size)).data).extract
      (offset + len) = #[] := by
    apply Array.extract_eq_empty_of_le
    rw [padded]
    omega
  rw [Array.extract_eq_self_of_le (by rw [padded]),
    show min (len + 0) (src.data.size - source) = len from by omega,
    tail, Array.append_empty]
  simp only [Nat.add_zero]

noncomputable def creationCopiedMem (sequencer root : UInt256) : ByteArray :=
  (solcFreePtrMem ++ ByteArray.zeroes 32) ++ creationArgs sequencer root

noncomputable def creationArgMem (sequencer root : UInt256) : ByteArray :=
  (UInt256.toByteArray ⟨192⟩).write 0 (creationCopiedMem sequencer root) 64 32

theorem creation_codecopy (sequencer root : UInt256) :
    (creationBytecode ++ creationArgs sequencer root).write 1594 solcFreePtrMem 128 64 =
      creationCopiedMem sequencer root := by
  rw [write_from_gap _ _ _ _ _ (by decide)
    (by rw [ByteArray.size_append, creation_size, creationArgs_size])
    (by rw [solcFreePtrMem_size]; decide), solcFreePtrMem_size]
  rw [extract_append_right' _ _ _ _ creation_size.symm
    (by rw [creation_size, creationArgs_size])]
  rfl

theorem creationCopiedMem_size (sequencer root : UInt256) :
    (creationCopiedMem sequencer root).size = 192 := by
  simp only [creationCopiedMem, ByteArray.size_append, solcFreePtrMem_size,
    ByteArray_zeroes_size, creationArgs_size]

theorem creationArgMem_size (sequencer root : UInt256) :
    (creationArgMem sequencer root).size = 192 := by
  unfold creationArgMem
  exact toByteArray_write32_size_of_le _ _ 64 192 192 (creationCopiedMem_size sequencer root)
    (by rw [creationCopiedMem_size]; decide) (by decide)

theorem creationCopiedMem_read (sequencer root : UInt256) (offset : Nat)
    (inside : offset + 32 ≤ 64) :
    (creationCopiedMem sequencer root).readWithPadding (128 + offset) 32 =
      (creationArgs sequencer root).extract offset (offset + 32) := by
  rw [readWithPadding_eq_extract _ _ (by rw [creationCopiedMem_size]; omega)]
  unfold creationCopiedMem
  have padded : (solcFreePtrMem ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size]
  rw [extract_append_right_window _ _ _ _ (by rw [padded]; omega), padded]
  congr 1 <;> omega

theorem creationArgMem_read (sequencer root : UInt256) (offset : Nat)
    (inside : offset + 32 ≤ 64) :
    (creationArgMem sequencer root).readWithPadding (128 + offset) 32 =
      (creationArgs sequencer root).extract offset (offset + 32) := by
  unfold creationArgMem
  rw [write32_read_above _ _ _ _ (by rw [toByteArray_size])
    (by rw [creationCopiedMem_size]; decide) (by omega)
    (by rw [creationCopiedMem_size]; omega)]
  exact creationCopiedMem_read sequencer root offset inside

theorem creationArgMem_read128 (sequencer root : UInt256) :
    (creationArgMem sequencer root).readWithPadding 128 32 = sequencer.toByteArray := by
  change (creationArgMem sequencer root).readWithPadding (128 + 0) 32 = _
  rw [creationArgMem_read _ _ _ (by decide), creationArgs]
  rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
  exact toByteArray_extract_all sequencer

theorem creationArgMem_read160 (sequencer root : UInt256) :
    (creationArgMem sequencer root).readWithPadding 160 32 = root.toByteArray := by
  change (creationArgMem sequencer root).readWithPadding (128 + 32) 32 = _
  rw [creationArgMem_read _ _ _ (by decide), creationArgs]
  exact extract_append_right' _ _ 32 64 (by rw [toByteArray_size])
    (by simp only [toByteArray_size])

end Rollup.EVM

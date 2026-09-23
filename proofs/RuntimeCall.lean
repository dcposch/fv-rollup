import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

-- Adapted from EquiVM Reasoning/Reach. No return-data size bound is needed.
private theorem call_value_made {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target valueWord inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hperm : ee.perm = true)
    (hbalance : valueWord ≤ (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat ee.gasPrice) valueWord valueWord
          (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1) ee.header ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          (o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            outOffset.toNat outSize.toNat))
          o (cA', σ') k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
      (by unfold RD; exact Or.inl hoog)⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ valueWord ≠ { val := 0 }) = False := by
      rw [hperm']; exact eq_false (by simp)
    have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hbalT :
        (valueWord ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          True := by
      rw [hee, hσ]
      exact eq_true hbalance
    have hbalOpt :
        (valueWord ≤ Option.option ⟨0⟩ (fun x => x.balance)
            (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner)) = True := by
      rw [show Option.option ⟨0⟩ (fun x => x.balance)
          (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) =
          (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) by
        cases Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner <;> rfl]
      exact hbalT
    have hgtF :
        (valueWord > (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          False := by
      rw [hee, hσ]
      exact eq_false (by
        intro hlt
        have hLeNat :
            valueWord.val.val ≤
              ((σ.find? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val := hbalance
        have hGtNat :
            ((σ.find? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val <
              valueWord.val.val := hlt
        exact Nat.not_lt_of_ge hLeNat hGtNat)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbalOpt, hgtF, hdeqF,
      and_true, if_true, Bool.or_false] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    split at hXP
    · exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
        (by unfold RD; exact Or.inl hXP)⟩
    · rename_i hP
      set mc := memoryExpansionCost s Operation.CALL with hmc
      set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) valueWord
        gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hgc
      set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) valueWord
        gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hG
      set cg := UInt256.ofNat G with hcg
      set θs := Θ s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader s.blocks
        s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        cg (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
        s.executionEnv.header s.executionEnv.perm with hθs
      set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.2.1.toNat) with hgv
      have hw1 : s.σ₀ = s0.σ₀ := hworld.1
      have hw2 : s.genesisBlockHeader = s0.genesisBlockHeader := hworld.2.1
      have hw3 : s.blocks = s0.blocks := hworld.2.2
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hretle : θs.2.2.1.toNat ≤ cg.toNat := by
        rw [hθs]
        exact Theta_returnedGas_le s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader
          s.blocks s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
          (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
          cg (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
          s.executionEnv.header s.executionEnv.perm
      have hcgle : cg.toNat ≤ G := by
        have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
        rw [h]; exact Nat.mod_le _ _
      have hGltgc : G < gc := by
        rw [hG, hgc]
        exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target)
          (AccountAddress.ofUInt256 target) valueWord gasArg s.accountMap
          { pc := s.machineState.pc, stack := s.machineState.stack,
            execLength := s.machineState.execLength + 1,
            gasAvailable := s.machineState.gasAvailable.subNat mc,
            activeWords := s.machineState.activeWords, memory := s.machineState.memory,
            returnData := s.machineState.returnData, H_return := s.machineState.H_return }
          s.substate
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - θs.2.2.1.toNat) with hcallCharge
      have hcallChargePos : 1 ≤ callCharge := by
        rw [hcallCharge]
        omega
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - θs.2.2.1.toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨θs.1, θs.2.1, θs.2.2.2.2.1, θs.2.2.2.2.2,
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate, cg, k + 1,
        C + callCharge, ⟨θs.2.2.1, θs.2.2.2.1, ?_⟩, ?_⟩
      · rw [← hee, ← hcA, ← hσ, ← hmem, ← hw1, ← hw2, ← hw3, ← hθs]
      · unfold RD
        refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hcode
        · rw [hpc]
        · cases θs.2.2.2.2.1 <;> rfl
        · show gv = g.subNat (C + callCharge)
          exact hgvGas
        · show k + 1 ≤ C + callCharge
          omega
        · exact hCcallCharge
        · rw [hmem]
        · rw [haw]
        · rfl
        · rfl
        · exact hee
        · exact hworld

/-- An empty-input CALL gives its actual result without a return-data size assumption. -/
theorem runtime_call_value_made_empty {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target valueWord inOffset outOffset : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: valueWord :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hperm : ee.perm = true)
    (hbalance : valueWord ≤ (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat ee.gasPrice) valueWord valueWord
          ByteArray.empty (ee.depth + 1) ee.header ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          mem
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
            (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat))
          o (cA', σ') k' C' := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd⟩ :=
    call_value_made h hdec hperm hbalance hdepth hov
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : mem.readWithPadding inOffset.toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact byteArray_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
        s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
        (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
        callGas (UInt256.ofNat ee.gasPrice) valueWord valueWord
        ByteArray.empty (ee.depth + 1) ee.header ee.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  rw [hmin, byteArray_write_len_zero] at rd
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', rd⟩


end Rollup.EVM

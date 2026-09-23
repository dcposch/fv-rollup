import proofs.generated.ControlPaths
import proofs.generated.BlockedControlPaths
import proofs.support.ControlCallBoundary
import proofs.ArrayPredicate

open Ethereum Ethereum.EVM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Rollup.EVM

private def blockedCallChunks : List (List Nat) := [
  List.range' 0 32,
  List.range' 32 32,
  List.range' 64 32,
  List.range' 96 32,
  List.range' 128 32,
  List.range' 160 32,
  List.range' 192 32,
  List.range' 224 32,
  List.range' 256 32,
  List.range' 288 32,
  List.range' 320 32,
  List.range' 352 32,
  List.range' 384 32,
  List.range' 416 32,
  List.range' 448 32,
  List.range' 480 32,
  List.range' 512 32,
  List.range' 544 32,
  List.range' 576 32,
  List.range' 608 32,
  List.range' 640 32,
  List.range' 672 32,
  List.range' 704 32,
  List.range' 736 32,
  List.range' 768 32,
  List.range' 800 32,
  List.range' 832 32,
  List.range' 864 32,
  List.range' 896 32,
  List.range' 928 32,
  List.range' 960 32,
  List.range' 992 32,
  List.range' 1024 32,
  List.range' 1056 32,
  List.range' 1088 32,
  List.range' 1120 32,
  List.range' 1152 32,
  List.range' 1184 32,
  List.range' 1216 13
]

private theorem blockedCall_chunk_0 :
    (List.range' 0 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_1 :
    (List.range' 32 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_2 :
    (List.range' 64 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_3 :
    (List.range' 96 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_4 :
    (List.range' 128 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_5 :
    (List.range' 160 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_6 :
    (List.range' 192 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_7 :
    (List.range' 224 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_8 :
    (List.range' 256 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_9 :
    (List.range' 288 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_10 :
    (List.range' 320 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_11 :
    (List.range' 352 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_12 :
    (List.range' 384 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_13 :
    (List.range' 416 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_14 :
    (List.range' 448 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_15 :
    (List.range' 480 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_16 :
    (List.range' 512 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_17 :
    (List.range' 544 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_18 :
    (List.range' 576 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_19 :
    (List.range' 608 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_20 :
    (List.range' 640 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_21 :
    (List.range' 672 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_22 :
    (List.range' 704 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_23 :
    (List.range' 736 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_24 :
    (List.range' 768 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_25 :
    (List.range' 800 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_26 :
    (List.range' 832 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_27 :
    (List.range' 864 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_28 :
    (List.range' 896 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_29 :
    (List.range' 928 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_30 :
    (List.range' 960 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_31 :
    (List.range' 992 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_32 :
    (List.range' 1024 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_33 :
    (List.range' 1056 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_34 :
    (List.range' 1088 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_35 :
    (List.range' 1120 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_36 :
    (List.range' 1152 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_37 :
    (List.range' 1184 32).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

private theorem blockedCall_chunk_38 :
    (List.range' 1216 13).all (arrayPredicateAt blockedControlPaths (fun cursor => cursor.pc != ⟨935⟩)) = true := by
  decide +kernel

/-- Small kernel checks establish the predicate for every candidate row. -/
theorem blocked_call_certificate : blockedControlPaths.all (fun cursor => cursor.pc != ⟨935⟩) = true := by
  apply array_predicate_chunks_sound blockedCallChunks (by decide +kernel)
  simp only [blockedCallChunks, List.all_cons, List.all_nil, Bool.true_and,
    blockedCall_chunk_0, blockedCall_chunk_1, blockedCall_chunk_2, blockedCall_chunk_3,
    blockedCall_chunk_4, blockedCall_chunk_5, blockedCall_chunk_6, blockedCall_chunk_7,
    blockedCall_chunk_8, blockedCall_chunk_9, blockedCall_chunk_10, blockedCall_chunk_11,
    blockedCall_chunk_12, blockedCall_chunk_13, blockedCall_chunk_14, blockedCall_chunk_15,
    blockedCall_chunk_16, blockedCall_chunk_17, blockedCall_chunk_18, blockedCall_chunk_19,
    blockedCall_chunk_20, blockedCall_chunk_21, blockedCall_chunk_22, blockedCall_chunk_23,
    blockedCall_chunk_24, blockedCall_chunk_25, blockedCall_chunk_26, blockedCall_chunk_27,
    blockedCall_chunk_28, blockedCall_chunk_29, blockedCall_chunk_30, blockedCall_chunk_31,
    blockedCall_chunk_32, blockedCall_chunk_33, blockedCall_chunk_34, blockedCall_chunk_35,
    blockedCall_chunk_36, blockedCall_chunk_37, blockedCall_chunk_38]

end Rollup.EVM

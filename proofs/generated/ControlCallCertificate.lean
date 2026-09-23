import proofs.generated.ControlPaths
import proofs.generated.BlockedControlPaths
import proofs.support.ControlCallBoundary
import proofs.ArrayPredicate

open Ethereum Ethereum.EVM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Rollup.EVM

private def callBoundaryChunks : List (List Nat) := [
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
  List.range' 1216 32,
  List.range' 1248 32,
  List.range' 1280 32,
  List.range' 1312 32,
  List.range' 1344 32,
  List.range' 1376 2
]

private theorem callBoundary_chunk_0 :
    (List.range' 0 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_1 :
    (List.range' 32 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_2 :
    (List.range' 64 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_3 :
    (List.range' 96 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_4 :
    (List.range' 128 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_5 :
    (List.range' 160 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_6 :
    (List.range' 192 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_7 :
    (List.range' 224 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_8 :
    (List.range' 256 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_9 :
    (List.range' 288 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_10 :
    (List.range' 320 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_11 :
    (List.range' 352 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_12 :
    (List.range' 384 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_13 :
    (List.range' 416 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_14 :
    (List.range' 448 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_15 :
    (List.range' 480 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_16 :
    (List.range' 512 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_17 :
    (List.range' 544 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_18 :
    (List.range' 576 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_19 :
    (List.range' 608 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_20 :
    (List.range' 640 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_21 :
    (List.range' 672 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_22 :
    (List.range' 704 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_23 :
    (List.range' 736 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_24 :
    (List.range' 768 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_25 :
    (List.range' 800 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_26 :
    (List.range' 832 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_27 :
    (List.range' 864 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_28 :
    (List.range' 896 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_29 :
    (List.range' 928 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_30 :
    (List.range' 960 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_31 :
    (List.range' 992 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_32 :
    (List.range' 1024 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_33 :
    (List.range' 1056 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_34 :
    (List.range' 1088 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_35 :
    (List.range' 1120 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_36 :
    (List.range' 1152 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_37 :
    (List.range' 1184 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_38 :
    (List.range' 1216 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_39 :
    (List.range' 1248 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_40 :
    (List.range' 1280 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_41 :
    (List.range' 1312 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_42 :
    (List.range' 1344 32).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

private theorem callBoundary_chunk_43 :
    (List.range' 1376 2).all (arrayPredicateAt controlPaths (controlCallToTable runtimeBytecode blockedControlPaths)) = true := by
  decide +kernel

/-- Small kernel checks establish the predicate for every candidate row. -/
theorem control_call_certificate : controlPaths.all (controlCallToTable runtimeBytecode blockedControlPaths) = true := by
  apply array_predicate_chunks_sound callBoundaryChunks (by decide +kernel)
  simp only [callBoundaryChunks, List.all_cons, List.all_nil, Bool.true_and,
    callBoundary_chunk_0, callBoundary_chunk_1, callBoundary_chunk_2, callBoundary_chunk_3,
    callBoundary_chunk_4, callBoundary_chunk_5, callBoundary_chunk_6, callBoundary_chunk_7,
    callBoundary_chunk_8, callBoundary_chunk_9, callBoundary_chunk_10, callBoundary_chunk_11,
    callBoundary_chunk_12, callBoundary_chunk_13, callBoundary_chunk_14, callBoundary_chunk_15,
    callBoundary_chunk_16, callBoundary_chunk_17, callBoundary_chunk_18, callBoundary_chunk_19,
    callBoundary_chunk_20, callBoundary_chunk_21, callBoundary_chunk_22, callBoundary_chunk_23,
    callBoundary_chunk_24, callBoundary_chunk_25, callBoundary_chunk_26, callBoundary_chunk_27,
    callBoundary_chunk_28, callBoundary_chunk_29, callBoundary_chunk_30, callBoundary_chunk_31,
    callBoundary_chunk_32, callBoundary_chunk_33, callBoundary_chunk_34, callBoundary_chunk_35,
    callBoundary_chunk_36, callBoundary_chunk_37, callBoundary_chunk_38, callBoundary_chunk_39,
    callBoundary_chunk_40, callBoundary_chunk_41, callBoundary_chunk_42, callBoundary_chunk_43]

end Rollup.EVM

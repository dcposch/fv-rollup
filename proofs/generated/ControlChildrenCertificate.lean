import proofs.generated.ControlPaths
import proofs.generated.BlockedControlPaths
import proofs.support.ControlCallBoundary
import proofs.ArrayPredicate

open Ethereum Ethereum.EVM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Rollup.EVM

private def childrenChunks : List (List Nat) := [
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

private theorem children_chunk_0 :
    (List.range' 0 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_1 :
    (List.range' 32 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_2 :
    (List.range' 64 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_3 :
    (List.range' 96 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_4 :
    (List.range' 128 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_5 :
    (List.range' 160 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_6 :
    (List.range' 192 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_7 :
    (List.range' 224 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_8 :
    (List.range' 256 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_9 :
    (List.range' 288 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_10 :
    (List.range' 320 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_11 :
    (List.range' 352 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_12 :
    (List.range' 384 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_13 :
    (List.range' 416 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_14 :
    (List.range' 448 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_15 :
    (List.range' 480 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_16 :
    (List.range' 512 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_17 :
    (List.range' 544 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_18 :
    (List.range' 576 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_19 :
    (List.range' 608 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_20 :
    (List.range' 640 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_21 :
    (List.range' 672 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_22 :
    (List.range' 704 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_23 :
    (List.range' 736 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_24 :
    (List.range' 768 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_25 :
    (List.range' 800 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_26 :
    (List.range' 832 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_27 :
    (List.range' 864 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_28 :
    (List.range' 896 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_29 :
    (List.range' 928 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_30 :
    (List.range' 960 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_31 :
    (List.range' 992 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_32 :
    (List.range' 1024 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_33 :
    (List.range' 1056 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_34 :
    (List.range' 1088 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_35 :
    (List.range' 1120 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_36 :
    (List.range' 1152 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_37 :
    (List.range' 1184 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_38 :
    (List.range' 1216 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_39 :
    (List.range' 1248 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_40 :
    (List.range' 1280 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_41 :
    (List.range' 1312 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_42 :
    (List.range' 1344 32).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

private theorem children_chunk_43 :
    (List.range' 1376 2).all (arrayPredicateAt controlPaths (controlChildAt runtimeBytecode)) = true := by
  decide +kernel

/-- Small kernel checks establish the predicate for every candidate row. -/
theorem control_children_certificate : controlPaths.all (controlChildAt runtimeBytecode) = true := by
  apply array_predicate_chunks_sound childrenChunks (by decide +kernel)
  simp only [childrenChunks, List.all_cons, List.all_nil, Bool.true_and,
    children_chunk_0, children_chunk_1, children_chunk_2, children_chunk_3,
    children_chunk_4, children_chunk_5, children_chunk_6, children_chunk_7,
    children_chunk_8, children_chunk_9, children_chunk_10, children_chunk_11,
    children_chunk_12, children_chunk_13, children_chunk_14, children_chunk_15,
    children_chunk_16, children_chunk_17, children_chunk_18, children_chunk_19,
    children_chunk_20, children_chunk_21, children_chunk_22, children_chunk_23,
    children_chunk_24, children_chunk_25, children_chunk_26, children_chunk_27,
    children_chunk_28, children_chunk_29, children_chunk_30, children_chunk_31,
    children_chunk_32, children_chunk_33, children_chunk_34, children_chunk_35,
    children_chunk_36, children_chunk_37, children_chunk_38, children_chunk_39,
    children_chunk_40, children_chunk_41, children_chunk_42, children_chunk_43]

end Rollup.EVM

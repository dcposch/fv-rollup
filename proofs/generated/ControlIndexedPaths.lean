import proofs.generated.ControlEdges
import proofs.IndexedControl

open Ethereum Ethereum.EVM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Rollup.EVM

private def controlChunks : List (List Nat) := [
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

private theorem control_chunk_0 :
    (List.range' 0 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_1 :
    (List.range' 32 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_2 :
    (List.range' 64 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_3 :
    (List.range' 96 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_4 :
    (List.range' 128 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_5 :
    (List.range' 160 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_6 :
    (List.range' 192 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_7 :
    (List.range' 224 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_8 :
    (List.range' 256 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_9 :
    (List.range' 288 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_10 :
    (List.range' 320 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_11 :
    (List.range' 352 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_12 :
    (List.range' 384 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_13 :
    (List.range' 416 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_14 :
    (List.range' 448 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_15 :
    (List.range' 480 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_16 :
    (List.range' 512 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_17 :
    (List.range' 544 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_18 :
    (List.range' 576 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_19 :
    (List.range' 608 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_20 :
    (List.range' 640 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_21 :
    (List.range' 672 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_22 :
    (List.range' 704 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_23 :
    (List.range' 736 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_24 :
    (List.range' 768 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_25 :
    (List.range' 800 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_26 :
    (List.range' 832 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_27 :
    (List.range' 864 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_28 :
    (List.range' 896 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_29 :
    (List.range' 928 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_30 :
    (List.range' 960 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_31 :
    (List.range' 992 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_32 :
    (List.range' 1024 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_33 :
    (List.range' 1056 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_34 :
    (List.range' 1088 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_35 :
    (List.range' 1120 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_36 :
    (List.range' 1152 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_37 :
    (List.range' 1184 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_38 :
    (List.range' 1216 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_39 :
    (List.range' 1248 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_40 :
    (List.range' 1280 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_41 :
    (List.range' 1312 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_42 :
    (List.range' 1344 32).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

private theorem control_chunk_43 :
    (List.range' 1376 2).all (indexedControlAt runtimeBytecode controlPaths controlEdges) = true := by
  decide +kernel

/-- Small kernel checks certify every row of the control table. -/
theorem control_indexed_closed : indexedControlClosed runtimeBytecode controlPaths controlEdges = true := by
  apply indexed_control_chunks_sound controlChunks (by decide +kernel)
  simp only [controlChunks, List.all_cons, List.all_nil, Bool.true_and,
    control_chunk_0, control_chunk_1, control_chunk_2, control_chunk_3,
    control_chunk_4, control_chunk_5, control_chunk_6, control_chunk_7,
    control_chunk_8, control_chunk_9, control_chunk_10, control_chunk_11,
    control_chunk_12, control_chunk_13, control_chunk_14, control_chunk_15,
    control_chunk_16, control_chunk_17, control_chunk_18, control_chunk_19,
    control_chunk_20, control_chunk_21, control_chunk_22, control_chunk_23,
    control_chunk_24, control_chunk_25, control_chunk_26, control_chunk_27,
    control_chunk_28, control_chunk_29, control_chunk_30, control_chunk_31,
    control_chunk_32, control_chunk_33, control_chunk_34, control_chunk_35,
    control_chunk_36, control_chunk_37, control_chunk_38, control_chunk_39,
    control_chunk_40, control_chunk_41, control_chunk_42, control_chunk_43]

private def blockedControlChunks : List (List Nat) := [
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

private theorem blockedControl_chunk_0 :
    (List.range' 0 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_1 :
    (List.range' 32 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_2 :
    (List.range' 64 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_3 :
    (List.range' 96 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_4 :
    (List.range' 128 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_5 :
    (List.range' 160 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_6 :
    (List.range' 192 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_7 :
    (List.range' 224 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_8 :
    (List.range' 256 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_9 :
    (List.range' 288 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_10 :
    (List.range' 320 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_11 :
    (List.range' 352 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_12 :
    (List.range' 384 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_13 :
    (List.range' 416 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_14 :
    (List.range' 448 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_15 :
    (List.range' 480 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_16 :
    (List.range' 512 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_17 :
    (List.range' 544 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_18 :
    (List.range' 576 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_19 :
    (List.range' 608 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_20 :
    (List.range' 640 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_21 :
    (List.range' 672 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_22 :
    (List.range' 704 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_23 :
    (List.range' 736 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_24 :
    (List.range' 768 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_25 :
    (List.range' 800 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_26 :
    (List.range' 832 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_27 :
    (List.range' 864 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_28 :
    (List.range' 896 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_29 :
    (List.range' 928 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_30 :
    (List.range' 960 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_31 :
    (List.range' 992 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_32 :
    (List.range' 1024 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_33 :
    (List.range' 1056 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_34 :
    (List.range' 1088 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_35 :
    (List.range' 1120 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_36 :
    (List.range' 1152 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_37 :
    (List.range' 1184 32).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

private theorem blockedControl_chunk_38 :
    (List.range' 1216 13).all (indexedControlAt runtimeBytecode blockedControlPaths blockedControlEdges) = true := by
  decide +kernel

/-- Small kernel checks certify every row of the blockedControl table. -/
theorem blocked_control_indexed_closed : indexedControlClosed runtimeBytecode blockedControlPaths blockedControlEdges = true := by
  apply indexed_control_chunks_sound blockedControlChunks (by decide +kernel)
  simp only [blockedControlChunks, List.all_cons, List.all_nil, Bool.true_and,
    blockedControl_chunk_0, blockedControl_chunk_1, blockedControl_chunk_2, blockedControl_chunk_3,
    blockedControl_chunk_4, blockedControl_chunk_5, blockedControl_chunk_6, blockedControl_chunk_7,
    blockedControl_chunk_8, blockedControl_chunk_9, blockedControl_chunk_10, blockedControl_chunk_11,
    blockedControl_chunk_12, blockedControl_chunk_13, blockedControl_chunk_14, blockedControl_chunk_15,
    blockedControl_chunk_16, blockedControl_chunk_17, blockedControl_chunk_18, blockedControl_chunk_19,
    blockedControl_chunk_20, blockedControl_chunk_21, blockedControl_chunk_22, blockedControl_chunk_23,
    blockedControl_chunk_24, blockedControl_chunk_25, blockedControl_chunk_26, blockedControl_chunk_27,
    blockedControl_chunk_28, blockedControl_chunk_29, blockedControl_chunk_30, blockedControl_chunk_31,
    blockedControl_chunk_32, blockedControl_chunk_33, blockedControl_chunk_34, blockedControl_chunk_35,
    blockedControl_chunk_36, blockedControl_chunk_37, blockedControl_chunk_38]

end Rollup.EVM

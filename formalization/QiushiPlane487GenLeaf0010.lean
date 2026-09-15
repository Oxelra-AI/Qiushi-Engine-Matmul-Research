import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0010Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 83, .occ 87, .occ 94, .occ 97, .occ 105, .occ 118, .occ 119, .occ 204, .occ 205, .occ 216, .occ 217, .occ 240, .occ 246, .occ 269, .occ 279, .occ 303, .occ 312, .occ 313, .occ 315, .occ 333, .occ 347, .occ 377, .occ 380, .occ 386, .occ 390, .occ 394, .occ 399, .occ 468, .occ 475, .occ 501, .occ 523, .occ 524, .occ 611, .occ 639, .occ 648, .occ 651, .occ 652, .occ 653, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchGe 12 (1), .branchLe 3 (0), .branchLe 24 (0), .branchLe 36 (0), .branchLe 17 (0)]

def plane487GenLeaf0010Mult : Fin 49 → Nat := ![2272, 2724, 570, 412, 2440, 582, 4656, 2466, 3268, 3426, 692, 816, 564, 1630, 774, 1694, 730, 2200, 1854, 2106, 884, 3220, 2578, 3388, 1056, 1878, 916, 1678, 1146, 118, 96, 978, 1112, 1368, 2403, 1341, 921, 27, 1053, 10109, 9056, 4190, 8768, 1538, 21420, 7014, 6650, 5796, 6170]

theorem plane487GenLeaf0010 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0010Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0010Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 105
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 240
  · exact hroot.hOcc 246
  · exact hroot.hOcc 269
  · exact hroot.hOcc 279
  · exact hroot.hOcc 303
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 333
  · exact hroot.hOcc 347
  · exact hroot.hOcc 377
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 394
  · exact hroot.hOcc 399
  · exact hroot.hOcc 468
  · exact hroot.hOcc 475
  · exact hroot.hOcc 501
  · exact hroot.hOcc 523
  · exact hroot.hOcc 524
  · exact hroot.hOcc 611
  · exact hroot.hOcc 639
  · exact hroot.hOcc 648
  · exact hroot.hOcc 651
  · exact hroot.hOcc 652
  · exact hroot.hOcc 653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (17 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17

end QiushiMatmul

import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0070Refs : Fin 47 → RowRef 668 48 := ![.occ 80, .occ 87, .occ 93, .occ 95, .occ 125, .occ 190, .occ 203, .occ 209, .occ 211, .occ 216, .occ 217, .occ 223, .occ 231, .occ 241, .occ 260, .occ 294, .occ 299, .occ 315, .occ 343, .occ 353, .occ 379, .occ 390, .occ 391, .occ 399, .occ 539, .occ 546, .occ 563, .occ 566, .occ 590, .occ 608, .occ 628, .occ 639, .occ 644, .occ 645, .occ 648, .occ 649, .sumGe, .nonneg 31, .nonneg 45, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchGe 29 (1), .branchLe 10 (0), .branchLe 12 (0), .branchGe 16 (1)]

def plane487GenLeaf0070Mult : Fin 47 → Nat := ![2550, 794, 6304, 6504, 47338, 23984, 33112, 5618, 10226, 11730, 1278, 6252, 2968, 20404, 25574, 2618, 6000, 3996, 6538, 19038, 2142, 1072, 4488, 41354, 10504, 5928, 15612, 2686, 1938, 3686, 256, 7273, 17465, 3275, 15095, 2934, 59724, 27672, 11240, 57430, 31818, 56790, 44112, 105968, 14616, 28132, 176506]

theorem plane487GenLeaf0070 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0070Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0070Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0070Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0070Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 125
  · exact hroot.hOcc 190
  · exact hroot.hOcc 203
  · exact hroot.hOcc 209
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 223
  · exact hroot.hOcc 231
  · exact hroot.hOcc 241
  · exact hroot.hOcc 260
  · exact hroot.hOcc 294
  · exact hroot.hOcc 299
  · exact hroot.hOcc 315
  · exact hroot.hOcc 343
  · exact hroot.hOcc 353
  · exact hroot.hOcc 379
  · exact hroot.hOcc 390
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 539
  · exact hroot.hOcc 546
  · exact hroot.hOcc 563
  · exact hroot.hOcc 566
  · exact hroot.hOcc 590
  · exact hroot.hOcc 608
  · exact hroot.hOcc 628
  · exact hroot.hOcc 639
  · exact hroot.hOcc 644
  · exact hroot.hOcc 645
  · exact hroot.hOcc 648
  · exact hroot.hOcc 649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (45 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (16 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul

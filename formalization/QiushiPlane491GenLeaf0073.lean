import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0073Refs : Fin 50 → RowRef 726 49 := ![.occ 84, .occ 98, .occ 102, .occ 104, .occ 107, .occ 110, .occ 118, .occ 121, .occ 210, .occ 234, .occ 243, .occ 267, .occ 312, .occ 315, .occ 329, .occ 334, .occ 340, .occ 351, .occ 355, .occ 359, .occ 365, .occ 368, .occ 382, .occ 393, .occ 394, .occ 413, .occ 415, .occ 423, .occ 431, .occ 484, .occ 495, .occ 505, .occ 525, .occ 568, .occ 582, .occ 606, .occ 630, .occ 699, .occ 711, .occ 723, .sumGe, .nonneg 16, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchLe 22 (0), .branchLe 15 (0), .branchLe 12 (0), .branchLe 14 (0)]

def plane491GenLeaf0073Mult : Fin 50 → Nat := ![5829, 6869, 8237, 6042, 3007, 12459, 11112, 5058, 4160, 13921, 206, 1804, 5890, 6773, 5646, 10107, 1530, 3670, 7053, 1545, 5014, 6679, 2669, 14403, 2574, 1680, 1438, 11030, 2756, 3556, 1836, 2862, 8740, 1680, 9654, 12663, 4473, 848, 3932, 57, 34113, 11365, 90309, 30540, 28110, 20740, 31357, 30181, 20527, 29446]

theorem plane491GenLeaf0073 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0073Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0073Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0073Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0073Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 98
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 210
  · exact hroot.hOcc 234
  · exact hroot.hOcc 243
  · exact hroot.hOcc 267
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 329
  · exact hroot.hOcc 334
  · exact hroot.hOcc 340
  · exact hroot.hOcc 351
  · exact hroot.hOcc 355
  · exact hroot.hOcc 359
  · exact hroot.hOcc 365
  · exact hroot.hOcc 368
  · exact hroot.hOcc 382
  · exact hroot.hOcc 393
  · exact hroot.hOcc 394
  · exact hroot.hOcc 413
  · exact hroot.hOcc 415
  · exact hroot.hOcc 423
  · exact hroot.hOcc 431
  · exact hroot.hOcc 484
  · exact hroot.hOcc 495
  · exact hroot.hOcc 505
  · exact hroot.hOcc 525
  · exact hroot.hOcc 568
  · exact hroot.hOcc 582
  · exact hroot.hOcc 606
  · exact hroot.hOcc 630
  · exact hroot.hOcc 699
  · exact hroot.hOcc 711
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (12 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (14 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul

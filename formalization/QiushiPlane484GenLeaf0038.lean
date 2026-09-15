import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0038Refs : Fin 41 → RowRef 1665 43 := ![.occ 128, .occ 134, .occ 135, .occ 136, .occ 141, .occ 225, .occ 290, .occ 331, .occ 511, .occ 588, .occ 779, .occ 1168, .occ 1183, .occ 1194, .occ 1213, .occ 1280, .occ 1304, .occ 1313, .occ 1346, .occ 1357, .occ 1367, .occ 1500, .occ 1562, .occ 1606, .occ 1607, .occ 1608, .occ 1635, .occ 1647, .sumGe, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchGe 25 (1), .branchLe 33 (0), .branchGe 10 (1), .branchLe 6 (0)]

def plane484GenLeaf0038Mult : Fin 41 → Nat := ![328, 377, 212, 77, 3, 1, 54, 21, 23, 104, 159, 255, 60, 67, 119, 261, 89, 106, 30, 87, 208, 30, 30, 48, 86, 119, 32, 99, 652, 172, 90, 105, 652, 620, 590, 30, 623, 1615, 431, 903, 208]

theorem plane484GenLeaf0038 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0038Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0038Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0038Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0038Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 225
  · exact hroot.hOcc 290
  · exact hroot.hOcc 331
  · exact hroot.hOcc 511
  · exact hroot.hOcc 588
  · exact hroot.hOcc 779
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1194
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul

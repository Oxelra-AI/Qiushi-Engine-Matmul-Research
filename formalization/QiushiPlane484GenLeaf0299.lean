import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0299Refs : Fin 44 → RowRef 1665 43 := ![.occ 85, .occ 115, .occ 129, .occ 141, .occ 151, .occ 167, .occ 187, .occ 656, .occ 858, .occ 1100, .occ 1101, .occ 1109, .occ 1151, .occ 1160, .occ 1170, .occ 1208, .occ 1351, .occ 1481, .occ 1488, .occ 1492, .occ 1567, .occ 1601, .occ 1609, .occ 1610, .occ 1641, .occ 1644, .occ 1656, .sumGe, .nonneg 11, .nonneg 14, .nonneg 35, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchLe 36 (0), .branchLe 22 (0), .branchGe 32 (1), .branchGe 28 (1), .branchLe 10 (0), .branchLe 37 (0)]

def plane484GenLeaf0299Mult : Fin 44 → Nat := ![1850, 668, 687, 347, 382, 459, 952, 470, 79, 829, 334, 343, 1098, 408, 251, 541, 18, 594, 1154, 1442, 1878, 847, 54, 61, 1474, 810, 329, 4152, 95, 526, 1048, 2599, 3622, 287, 4152, 3476, 7187, 1918, 3305, 3342, 6839, 1824, 2349, 4037]

theorem plane484GenLeaf0299 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0299Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0299Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0299Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0299Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 115
  · exact hroot.hOcc 129
  · exact hroot.hOcc 141
  · exact hroot.hOcc 151
  · exact hroot.hOcc 167
  · exact hroot.hOcc 187
  · exact hroot.hOcc 656
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul

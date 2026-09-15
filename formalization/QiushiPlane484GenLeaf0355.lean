import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0355Refs : Fin 42 → RowRef 1665 43 := ![.occ 125, .occ 126, .occ 129, .occ 130, .occ 132, .occ 137, .occ 164, .occ 219, .occ 462, .occ 600, .occ 1147, .occ 1187, .occ 1188, .occ 1190, .occ 1200, .occ 1213, .occ 1264, .occ 1272, .occ 1408, .occ 1458, .occ 1459, .occ 1461, .occ 1463, .occ 1496, .occ 1507, .occ 1521, .occ 1567, .occ 1601, .occ 1602, .occ 1603, .sumGe, .nonneg 3, .nonneg 11, .nonneg 18, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 24 (0), .branchLe 19 (0), .branchGe 14 (1)]

def plane484GenLeaf0355Mult : Fin 42 → Nat := ![441, 445, 209, 879, 24, 1194, 126, 358, 730, 522, 126, 4, 34, 12, 170, 450, 80, 24, 234, 59, 59, 193, 563, 4, 286, 590, 94, 104, 2, 106, 1324, 126, 84, 94, 1120, 1200, 126, 3814, 790, 1300, 1214, 5210]

theorem plane484GenLeaf0355 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0355Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0355Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0355Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0355Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 164
  · exact hroot.hOcc 219
  · exact hroot.hOcc 462
  · exact hroot.hOcc 600
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1461
  · exact hroot.hOcc 1463
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1603
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul

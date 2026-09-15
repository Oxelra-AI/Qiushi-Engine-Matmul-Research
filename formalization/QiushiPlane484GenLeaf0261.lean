import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0261Refs : Fin 42 → RowRef 1665 43 := ![.occ 124, .occ 125, .occ 126, .occ 128, .occ 136, .occ 137, .occ 140, .occ 141, .occ 335, .occ 336, .occ 360, .occ 794, .occ 858, .occ 956, .occ 959, .occ 1003, .occ 1145, .occ 1154, .occ 1160, .occ 1170, .occ 1220, .occ 1307, .occ 1321, .occ 1414, .occ 1428, .occ 1472, .occ 1478, .occ 1492, .occ 1537, .occ 1558, .occ 1610, .sumGe, .nonneg 6, .nonneg 26, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 29 (0), .branchGe 17 (1), .branchGe 3 (1), .branchGe 20 (1)]

def plane484GenLeaf0261Mult : Fin 42 → Nat := ![22, 184, 568, 162, 282, 632, 350, 350, 282, 324, 150, 72, 162, 120, 182, 18, 108, 93, 249, 150, 12, 194, 198, 114, 254, 120, 189, 12, 162, 236, 153, 914, 8, 1896, 402, 1056, 324, 282, 324, 2976, 2362, 2934]

theorem plane484GenLeaf0261 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0261Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0261Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0261Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0261Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 335
  · exact hroot.hOcc 336
  · exact hroot.hOcc 360
  · exact hroot.hOcc 794
  · exact hroot.hOcc 858
  · exact hroot.hOcc 956
  · exact hroot.hOcc 959
  · exact hroot.hOcc 1003
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1610
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
